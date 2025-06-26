{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Symbolic differentiation
module Symbolic
  ( Expr
  , VarId
  , var
  , tag
  , lift
  , unlift
  , untag
  , eval
  , diff, diffVar
  , simplify
  , compile, compileOps, evalOps
  , toMaxima, toHaskell

  , showExprWithSharing
  , cse
  , interactivePrint
  ) where

import Control.DeepSeq
import Control.Monad
import Control.Monad.State.Strict qualified as S
import Data.Array
import Data.Array.Base (amap)
import Data.Bifunctor
import Data.Either
import Data.IntMap (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.List
import Data.Map (Map)
import Data.Map.Strict qualified as Map
import Data.Number.Erf
import Data.Ord
import Data.Traversable
import GHC.Generics (Generic)
import Number
import StructuralComparison
import Symbolic.Internal
import Unique

-- TODO: вынести Diff, Compile, Simplify в отдельные модули

-- | For use with `:set -interactive-print=Symbolic.interactivePrint`
class InteractivePrint a where
  interactivePrint :: a -> IO ()

  default interactivePrint :: Show a => a -> IO ()
  interactivePrint = print

instance InteractivePrint ()
instance InteractivePrint Double
instance Show a => InteractivePrint [a]
instance Show a => InteractivePrint (Maybe a)

instance N a => InteractivePrint (Expr a) where
  interactivePrint = putStrLn . toHaskell

data Cmp a = Cmp (Expr a) Ordering (Expr a)
  deriving (Generic, NFData)

-- | Remove 'tag' which opens a way to constant propagation
untag :: N a => Expr a -> Expr a
untag expr = S.evalState (go expr) IntMap.empty
  where
    go = \ case
      v@Var{} -> pure v
      Tag i _ _ e -> m i $ go e
      c@Const{} -> pure c
      If i c a b t e -> m i $ liftM4 (if_ c) (go a) (go b) (go t) (go e)
      BinOp i _ op a b -> m i $ liftM2 (foldBinOp op) (go a) (go b)
      UnOp i _ op e -> m i $ foldUnOp op <$> go e
      ExplicitD i _ v j h a -> m i $ mapMExplicitD explicitD go v j h a

------------------------------------------------------------------------------
-- Differentiation

diff :: N a => Expr a -> Expr a -> Expr a
diff e v =
  -- No longer necessary after adding constant propagation to binops
  -- and it's 100 times faster without simplify

  -- always use 'simplify' as we get a lot of 0s, and we might have
  -- an invalid computation multiplied by 0 and get NaN where we shouldn't.
  -- E.g.:
  --   (- x) ** 1
  -- gives
  --   (- x) ** 1 * (log (- x) * 0 + 1 * (- 1) * 1 / (- x))
  -- where log (-1) is NaN but it's multiplied by 0 and not used in
  -- final computation
  -- simplify $
  diffVar e $ case v of
    Var _ i   -> i
    Tag _ _ i _ -> i
    v -> error $ "Please use 'var' to differentiate instead of " <> show v

diffVar :: N a => Expr a -> VarId -> Expr a
diffVar expr by = S.evalState (d expr) IntMap.empty
  where
    d = \ case
      Var i vi -> m i $ pure $ if
        | vi == by  -> 1
        | otherwise -> 0
      Tag i _ vi e -> m i $ if
        | vi == by  -> pure 1
        | otherwise -> -- Tag i vi $
          d e -- is it correct at all? throw error?
      Const _ -> pure 0
      If i c a b t e -> m i $ liftM2 (if_ c a b) (d t) (d e)
      BinOp i _ op a b -> m i $ binOp op a b
      UnOp i _ op a -> m i $ do
        !a' <- d a
        pure $! dUnOp op a * a'
      ExplicitD i _ vars jacobian hessian _ -> m i $ do
        -- A separate variables list doesn't speed things up
        -- as we already cache evaluation and differentiation,
        -- but it helps with debugging as we can just check indices
        -- and don't look into repeated variables.
        -- It also simplifies usage a bit as we don't need to copy
        -- inputs everywhere.
        let vmes = arr [v - e v | v <- vars]
            e = toN . toD -- maybe (error "foo") (toN . toD) . evalMaybe
            arr xs = listArray (0, length vars-1) xs
        dvs <- arr <$> mapM d vars
        let a = sum [dv * dvs!v | (dv,v) <- jacobian]
            j = flip concatMap hessian $ \ (dv12,v1,v2) ->
               -- the inlined version of
               --   v' <- d ((v1-e v1)*(v2 - e v2))
               -- ==>
               --   v' = v1' * (v2 - e v2) + v2' * (v1 - e v1)
               let v' = dvs!v1 * vmes!v2 + dvs!v2 * vmes!v1
               in
                 if | isZero v' -> []
                    | otherwise -> [(dv12, v')]
        pure $ if null j then a else
          explicitD (map snd j) (zip (map fst j) [0..]) [] a
    binOp op a b = do
      !a' <- d a
      !b' <- d b
      pure $! case op of
        Plus     -> a' + b'
        Minus    -> a' - b'
        Multiply -> a' * b + a * b'
        Divide   -> (a' * b - a * b') / b^2
        Expt     -> a**b * (log a * b' + b * a' / a)
    dUnOp op x = case op of
      Negate -> -1
      Abs    -> nonDiff "abs"
      Signum -> nonDiff "signum"
      Exp    -> exp x
      Log    -> 1 / x
      Sqrt   -> 1 / (2 * sqrt x)
      Sin    -> cos x
      Cos    -> -sin x
      Tan    -> sec x ^ 2
      ASin   ->  1 / sqrt (1 - x^2)
      ACos   -> -1 / sqrt (1 - x^2)
      ATan   -> 1 / (x^2 + 1)
      Sinh   -> cosh x
      Cosh   -> sinh x
      Tanh   -> sech x ^ 2
      ASinh  -> 1 / sqrt (x^2 + 1)
      ACosh  -> 1 / sqrt (x^2 - 1)
      ATanh  -> 1 / (1 - x^2)
      Erf    ->  2 / sqrt pi * exp (-x^2)
      Erfc   -> -2 / sqrt pi * exp (-x^2)
      Normcdf -> recip (sqrt (2 * pi)) * exp (- x^2 / 2)
      Inverf  ->  sqrt pi / 2 * exp (inverf x^2)
      Inverfc -> -sqrt pi / 2 * exp (inverfc x^2)
      Invnormcdf -> sqrt (2 * pi) * exp (invnormcdf x^2 / 2)
      Step   -> k / (exp (k*x) + exp (-k*x) + 2)
    sec x = 1 / cos x
    sech x = 1 / cosh x
    nonDiff s = error $ "non-differentiable: " <> s

------------------------------------------------------------------------------
-- Compilation

-- | Create a faster evaluator for 'Expr'.
-- About 3x faster than 'eval' thanks to a faster shared
-- subexpressions handling.
-- It may worth to @'cse' . 'untag'@ the expression before to reduce
-- the number of nodes.
compile :: N a => Expr a -> (VarId -> a) -> a
compile expr = evalOps (compileOps expr)

{-# SPECIALIZE compile :: Expr Double -> (VarId -> Double) -> Double #-}

-- | Operation to evaluate the expression in a single array element.
-- Uses precomputed subexpressions from other array elements.
data Operation a
  = OVar VarId
  | OTag !I -- ^ redirect to another index
  | OConst !a
  | OIf !Ordering !I !I !I !I
  | OBinOp !BinOp !I !I
  | OUnOp !UnOp !I
  | OExplicitD
    [I]             -- ^ variables
    [(I, Int)]      -- ^ jacobian [(∂x/∂var, var)]
    [(I, Int, Int)] -- ^ hessian  [(∂x/(∂var1*∂var2), var1, var2)]
    !I
   deriving (Show, Generic, NFData)

evalOps :: N a => Array Int (Operation a) -> (VarId -> a) -> a
evalOps ops subst = r `deepseq` r!hi
  -- deepseq gives a 1.5x speedup on fem. The shallow seq on elements
  -- is not enough -- we need 'a' inside the 'Reverse' to be fully evaluated
  where
    (_, hi) = bounds r
    r = amap e ops
    e = \ case
      OVar v -> subst v
      OTag i -> r!i
      OConst x -> x
      OIf c a b t e -> if_ c (r!a) (r!b) (r!t) (r!e)
      OBinOp op a b -> binOp op (r!a) (r!b)
      OUnOp op a -> unOp op (r!a)
      OExplicitD v j h a ->
        mapExplicitD explicitD (r!) v j h a

-- | Create a sequence of operations to evaluate the expression.
-- Every next operation can use results of previous operations, so we
-- keep the sharing automatically without an additional 'State' and
-- 'IntMap'. The profiler shows a lot of allocations in 'm' and
-- 'IntMap.insert', we're removing these allocations with 'compile'.
compileOps :: N a => Expr a -> Array Int (Operation a)
compileOps expr = force $ listArray (0, nOps-1) $ reverse ops
  where
    CompileState _ _ ops nOps =
      S.execState (go expr) (CompileState IntMap.empty Map.empty [] 0)
    go :: N a => Expr a -> Compile a Int
    go = \ case
      Var i v -> o i $ pure $ OVar v
      Tag i (Just x) _ _ -> iconst i x
      Tag i _ _ e -> o i $ OTag <$> go e
      Const x -> lit x
      If i c a b t e -> o i $ liftM4 (OIf c) (go a) (go b) (go t) (go e)
      BinOp i (Just x) _ _ _ -> iconst i x
      BinOp i _ op a b -> o i $ liftM2 (OBinOp op) (go a) (go b)
      UnOp i (Just x) _ _ -> iconst i x
      UnOp i _ op a -> o i $ OUnOp op <$> go a
      ExplicitD i (Just x) _ _ _ _ -> iconst i x
      ExplicitD i _ v j h a -> o i $ mapMExplicitD OExplicitD go v j h a
    o :: I -> Compile a (Operation a) -> Compile a Int
    o i act = do
      im <- S.gets cIdToOperation
      case IntMap.lookup i im of
        Nothing -> do
          !op <- act
          S.state $ \ (CompileState m cs ops nOps) ->
            (nOps, CompileState (IntMap.insert i nOps m) cs (op:ops) (nOps+1))
        Just oi ->
          pure oi
    iconst i x = do
      im <- S.gets cIdToOperation
      case IntMap.lookup i im of
        Nothing -> do
          !oi <- lit x
          S.state $ \ (CompileState m cs ops nOps) ->
            (oi, CompileState (IntMap.insert i oi m) cs ops nOps)
        Just oi ->
          pure oi
    -- add a literal constant without the Expr id mapping
    lit :: StructuralOrd a => a -> Compile a Int
    lit c = S.state $ \ s@(CompileState m cs ops nOps) ->
      case Map.lookup (SCmp c) cs of
        Just n -> (n, s)
        Nothing ->
          (nOps, CompileState m (Map.insert (SCmp c) nOps cs) (OConst c:ops) (nOps+1))

type Compile e a = S.State (CompileState e) a
data CompileState a
  = CompileState
    { cIdToOperation   :: !(IntMap I) -- ^ Expr id to operation index map
    , cConstants       :: !(Map (SCmp a) I)
    , cOperations      :: ![Operation a]
    , cTotalOperations :: !Int
    }

------------------------------------------------------------------------------
-- Common subexpression elimination

type CSE e a = S.State (CSEState e) a
data CSEState a
  = CSEState
    { cseExprIdMap    :: !(IntMap (IndexedExpr a)) -- ^ Expr id to common expr
    , cseCExprMap     :: !(Map (CExpr a) (IndexedExpr a))
    , cseCurrentIndex :: !I
    }
  deriving Show
data IndexedExpr a
  = IE
    { ieIndex :: !I
    , ieExpr  :: Expr a
      -- Expr is still lazy as we might only need the index for comparisons
    }
  deriving Show

runCSE :: CSE e a -> a
runCSE act = S.evalState act (CSEState IntMap.empty Map.empty 0)

cse :: N a => Expr a -> Expr a
cse = ieExpr . runCSE . cse'

-- | Equality via CSE
-- More performant than a plain comparison as it handles sharing
cseEq :: N a => Expr a -> Expr a -> Bool
cseEq a b = runCSE $ do
  IE ia _ <- cse' a
  IE ib _ <- cse' b
  pure $ ia == ib

cse' :: N a => Expr a -> CSE a (IndexedExpr a)
cse' e = go e
  where
    go = \ case
      Var i v -> m i $
        get (CVar v) (var v)
      Tag i _ v e -> m i $ do
        IE ie se <- go e
        get (CTag v ie) (tag v se)
      c@(Const x) ->
        get (CConst $ SCmp x) c
      If i c a b t e -> m i $ do
        IE ia sa <- go a
        IE ib sb <- go b
        IE it st <- go t
        IE ie se <- go e
        get (CIf c ia ib it ie) (if_ c sa sb st se)
      BinOp i _ op a b -> m i $ do
        IE ia sa <- go a
        IE ib sb <- go b
        get (CBinOp op ia ib) (mkBinOp op sa sb)
      UnOp i _ op a -> m i $ do
        IE ia sa <- go a
        get (CUnOp op ia) (mkUnOp op sa)
      ExplicitD i _ v j h a -> m i $ do
        (iv, sv) <- unzip . map (\ (IE i e) -> (i,e)) <$> mapM go v
        IE ia sa <- go a
        (ij, sj) <- fmap unzip $ for j $ \ (d,v) -> do
          IE id sd <- go d
          pure ((id,v), (sd,v))
        (ih, sh) <- fmap unzip $ for h $ \ (d,v1,v2) -> do
          IE id sd <- go d
          pure ((id,v1,v2), (sd,v1,v2))
        get (CExplicitD iv ij ih ia) (explicitD sv sj sh sa)
    get :: StructuralOrd a => CExpr a -> Expr a -> CSE a (IndexedExpr a)
    get cexpr mkexpr = do
      em <- S.gets cseCExprMap
      case Map.lookup cexpr em of
        Nothing -> do
          S.state $ \ (CSEState im em idx) ->
            let r = IE idx mkexpr in
            (r, CSEState im (Map.insert cexpr r em) (succ idx))
        Just e -> pure e
    m :: I -> CSE a (IndexedExpr a) -> CSE a (IndexedExpr a)
    m i act = do
      im <- S.gets cseExprIdMap
      case IntMap.lookup i im of
        Nothing -> do
          r <- act
          S.state $ \ (CSEState im em idx) ->
            (r, CSEState (IntMap.insert i r im) em idx)
        Just r ->
          pure r

-- 'Expr' that can be used as a key for the common subexpression elimination
data CExpr a
  = CVar VarId
  | CTag VarId !I
  | CConst (SCmp a)
  | CIf Ordering !I !I !I !I
  | CBinOp BinOp !I !I
  | CUnOp UnOp !I
  | CExplicitD [I] [(I, Int)] [(I, Int, Int)] !I
  deriving (Eq, Ord, Show)

------------------------------------------------------------------------------
-- Simplification

simplify :: N a => Expr a -> Expr a
simplify = fexpand . fsimp . factor

fixedPoint :: Eq a => (a -> a) -> a -> a
fixedPoint f e
  | e' == e   = e
  | otherwise = fixedPoint f e'
  where
    e' = f e

data FExpr a
  = FVar VarId
  | FTag VarId (FExpr a)
  | FUnOp UnOp (FExpr a)
  | FIf Ordering (FExpr a) (FExpr a) (FExpr a) (FExpr a)
  | FExpt (FExpr a) (FExpr a)
  | FSum (SCmp a) (Map (FExpr a) (SCmp a))
    -- ^ c0 + expr1*c1 + expr2*c2 ...
  | FProduct (SCmp a) (Map (FExpr a) Integer)
    -- ^ c0 * expr1^c1 * expr2^c2 ...
  | FExplicitD [FExpr a] [(FExpr a, Int)] [(FExpr a, Int, Int)] (FExpr a)
  deriving (Eq, Ord)

fsimp :: (StructuralOrd a, N a) => FExpr a -> FExpr a
fsimp = fixedPoint $ \ case
  FSum 0 [(e,1)] -> e
  FSum 0 [(FProduct c0 e,c)] -> FProduct (c0*c) e
  FSum 0 [(FProduct p1 e1,1),(FProduct p2 e2,1)]
    | e1 == e2 -> FProduct (p1+p2) e1
  FSum c e -> uncurry FSum $ recurse (foldl' (+) c) flattenSum e
  FProduct 0 _ -> FProduct 0 mempty
  FProduct 1 [(e,1)] -> e
  FProduct c e -> uncurry FProduct $ recurse (foldl' (*) c) flattenProduct e
  FExpt a b
    | Just ca <- toConst a
    , Just cb <- toConst b
    , n <- truncate $ toD cb
    , cb == fromInteger n -> FSum (ca ^^ n) []
    | Just 1 <- toConst b -> a
    | Just 0 <- toConst b -> FSum 1 []
    | otherwise -> FExpt (fsimp a) (fsimp b)
  FUnOp Negate (FProduct c es) -> FProduct (-c) es
  FUnOp Negate (FSum c es) -> FSum (-c) $ Map.map negate es
  FUnOp Negate (FUnOp Negate e) -> e
  FUnOp Exp (toConst -> Just 0) -> FSum 1 []
  FUnOp Cos (FUnOp Negate x) -> FUnOp Cos x
  FUnOp Sin (FUnOp Negate x) -> FUnOp Negate (FUnOp Sin x)
  FUnOp op e -> FUnOp op (fsimp e)
  e@FVar{} -> e
  FTag i e -> FTag i (fsimp e)
  e@FExplicitD{} -> e -- TODO: recurse
  e@FIf{} -> e -- TODO: recurse
  where
    recurse
      :: (StructuralOrd a, N a, StructuralEq b, Num b)
      => ([SCmp a] -> SCmp a) -- ^ fold constants
      -> ((FExpr a, b) -> [Either (SCmp a) (FExpr a, b)])
         -- ^ constants or new expr
      -> Map (FExpr a) b -- ^ exprs of FSum or FProduct
      -> (SCmp a, Map (FExpr a) b) -- ^ new constant and exprs
    recurse fold flatten es = (fold consts, Map.fromListWith (+) nonConsts)
      where
        (consts, nonConsts)
          = partitionEithers $ concatMap flatten
          $ filter (not . (structuralEq 0) . snd)
          $ Map.toList
          $ Map.fromListWith (+) [(fsimp e, c) | (e,c) <- Map.toList es]
    flattenSum :: N a => (FExpr a, SCmp a) -> [Either (SCmp a) (FExpr a, SCmp a)]
    flattenSum = \ case
      (toConst -> Just x, c) -> [Left (x*c)]
      (FUnOp Negate x, c) -> [Right (x,-c)]
      (FProduct c0 [(x,1)], c) -> [Right (x,c0*c)]
      (FProduct c0 xs, c) | c0 /= 1 -> [Right (FProduct 1 xs,c0*c)]
      (FSum c0 es, c) ->
        Left (c0*c) : [Right (e, ce*c) | (e,ce) <- Map.toList es]
      e -> [Right e]
    flattenProduct :: N a => (FExpr a, Integer) -> [Either (SCmp a) (FExpr a, Integer)]
    flattenProduct = \ case
      (toConst -> Just x, c) -> [Left (x^^c)]
      (FUnOp Sqrt (toConst -> Just x), 2)  | x >= 0 -> [Left x]
      (FUnOp Sqrt (toConst -> Just x), -2) | x > 0  -> [Left (1/x)]
      (FUnOp Negate x, c)
        | odd c -> [Left (-1), Right (x,c)]
        | otherwise -> [Right (x,c)]
      (FSum 0 [(x,sc)], c) ->
        [Left (sc^^c), Right (x,c)]
      (FProduct c0 es, c) ->
        Left (c0^^c) : [Right (e, ce*c) | (e,ce) <- Map.toList es]
      e -> [Right e]
    toConst :: N a => FExpr a -> Maybe (SCmp a)
    toConst = \ case
      FSum c [] -> Just c
      FProduct c [] -> Just c
      _ -> Nothing

fexpand :: N a => FExpr a -> Expr a
fexpand = \ case
  FSum c0 ss -> case negativeLast ss of
    [] -> r c0
    (x:xs) -> mkSum c0 x xs
  FProduct c0 ps -> case negativeLast ps of
    [] -> r c0
    (x:xs) -> goProd (firstProd c0 x) xs
  FExpt a b -> e a ** e b
  FUnOp op x -> unOp op $ e x
  FVar i -> var i
  FTag i x -> tag i (e x)
  FExplicitD v j h x -> mapExplicitD explicitD e v j h x
  FIf c a b t e_ -> if_ c (e a) (e b) (e t) (e e_)
  where
    -- put negative constants last to have more a-b and a/b
    -- instead of -1*b+a and 1/b*a
    negativeLast x = map (first e)
      $ sortBy (comparing $ \ (e,c) -> (Down $ signum c, e)) $ Map.toList x
    -- replace 1/a*b*1/c with b/a/c
    firstProd 1  (e,c) = e ^^ c
    firstProd c0 p     = goProd (r c0) [p]
    goProd = foldl' prod
    prod acc (e,c)
      | c == 1    = acc * e
      | c == -1   = acc / e
      | c >= 0    = acc * (e ^^ c)
      | otherwise = acc / (e ^^ (-c))
    -- replace -1*b+a with a-b
    mkSum 0  (e,1) xs = goSum e xs
    mkSum 0  (e,c) xs = goSum (r c*e) xs
    mkSum c0 x     xs
      | c0 > 0    = goSum (r c0) (x:xs)
      | otherwise = mkSum 0 x (xs<>[(r (-c0), -1)])
    goSum = foldl' sum
    sum acc (e,c)
      | c == 1    = acc + e
      | c == -1   = acc - e
      | c >= 0    = acc + (r c*e)
      | otherwise = acc - (r (-c)*e)

    r :: SCmp a -> Expr a
    r = Const . unSCmp
    e :: N a => FExpr a -> Expr a
    e = fexpand

factor :: forall a . N a => Expr a -> FExpr a
factor = \ case
  Var _ i -> FVar i
  Tag _ _ i e -> FTag i $ factor e
  Const c -> FSum (SCmp c) Map.empty
  If _ c a b t e -> FIf c (factor a) (factor b) (factor t) (factor e)
  BinOp _ _ op a b ->
    let m :: Num b => b -> b -> Map (FExpr a) b
        m ca cb = Map.fromListWith (+) [(factor a, ca), (factor b, cb)]
    in
    case op of
      Plus      -> FSum 0 $ m 1 1
      Minus     -> FSum 0 $ m 1 (-1)
      Multiply  -> FProduct 1 $ m 1 1
      Divide    -> FProduct 1 $ m 1 (-1)
      Expt      -> FExpt (factor a) (factor b)
  UnOp _ _ op e -> FUnOp op $ factor e
  ExplicitD _ _ v j h e -> mapExplicitD FExplicitD factor v j h e

-- instance N a => Show (FExpr a) where
--   showsPrec d e = (showFExpr (d < 10) e <>)

showFExpr :: N a => Bool -> FExpr a -> String
showFExpr root = \ case
  FVar n -> n
  FTag n e -> n<>"@"<>showFExpr False e
  FSum c l ->
    parens "(Σ " ")" $ intercalate "+" $ showC c : showS (Map.toList l)
  FProduct c l ->
    parens "(Π " ")" $ intercalate "*" $ showC c : showP (Map.toList l)
  FUnOp op a -> parens "(" ")" $ unwords [show op, showFExpr False a]
  FExpt a b -> showFExpr False a <> "**" <> showFExpr False b
  FExplicitD{} -> "TODO FExplicitD"
  FIf{} -> "TODO FIf"
  where
    showC (SCmp x) = show x
    showS = map $ \ case
      (e,1) -> showFExpr False e
      (e,c) -> showC c <> "*" <> showFExpr False e
    showP = map $ \ case
      (e,1) -> showFExpr False e
      (e,c) -> showFExpr False e <> "^" <> show c
    isBinOp = \ case
      BinOp{} -> True
      _ -> False
    parens o c x
--      | root = x
      | otherwise = o <> x <> c
