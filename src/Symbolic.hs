{-# LANGUAGE OverloadedLists, DeriveAnyClass, TemplateHaskell, MultiWayIf #-}
{-# OPTIONS_GHC -Wincomplete-patterns -O2 #-}
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
  , diff
  , simplify
  , compile
  , toMaxima

  , testSymbolic
  , showExprWithSharing
  , cse
  ) where

import Control.Monad
import System.Exit
import Data.Number.Erf
import Data.Ord
import Data.Ratio
import Data.Array
import Data.Array.Base (amap)
import Data.Bifunctor
import Data.Either
import Data.Maybe
import Data.List
import Data.String
import Data.Map (Map)
import qualified Data.Map.Strict as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet

import Control.Applicative ((<|>))
import Text.Parsec ((<?>))
import qualified Text.Parsec as P
import qualified Text.Parsec.Expr as P
import qualified Text.Parsec.Token as P
import qualified Text.Parsec.Language as P

import Test.QuickCheck
import Number
import Unique
import StructuralComparison
import Data.Function
import Data.Traversable
import Control.DeepSeq
import GHC.Generics (Generic)
import Debug.Trace

import qualified Control.Monad.State.Strict as S

{- | Expression that can store values and variables.

It can be both evaluated numerically and differentiated symbolically.

If 'a' is an AD value, symbolically differentiated 'Expr' will have
correct sensitivities to market inputs.
-}
data Expr a
  = Var !I VarId
    -- | Named sub-expression that we can differentiate on.
    -- It can keep AD variables beneath.
  | Tag !I !(Maybe a) VarId (Expr a)
    -- | Lifted AD value.
  | Const a
  | BinOp !I !(Maybe a) !BinOp (Expr a) (Expr a)
  | UnOp !I !(Maybe a) !UnOp (Expr a)
  | ExplicitD !I !(Maybe a)
    [Expr a]             -- ^ variables
    [(Expr a, Int)]      -- ^ jacobian [(∂x/∂var, var)]
    [(Expr a, Int, Int)] -- ^ hessian  [(∂x/(∂var1*∂var2), var1, var2)]
    (Expr a)
  deriving (Generic, NFData)

var x = withNewId $ \ i -> Var i x
tag t e = withNewId $ \ i -> Tag i (evalMaybe e) t e
lift = Const
unlift e = unsafeEval "unlift" e
-- explicit = Explicit

type VarId = String

data BinOp
  = Plus
  | Minus
  | Multiply
  | Divide
  | Expt -- ^ a**b
--   | LogBase -- ^ logBase
  deriving (Eq, Ord, Enum, Bounded, Show, Generic, NFData)

data UnOp
  = Negate
  | Abs
  | Signum
  | Exp
  | Log
  | Sqrt
  | Sin
  | Cos
  | Tan
  | ASin
  | ACos
  | ATan
  | Sinh
  | Cosh
  | Tanh
  | ASinh
  | ACosh
  | ATanh
--     log1p x = log (1 + x)
--     expm1 x = exp x - 1
--     log1pexp x = log1p (exp x)
--     log1mexp x = log1p (negate (exp x))
  | Erf
  | Erfc
  | Step
  deriving (Eq, Ord, Enum, Bounded, Show, Generic, NFData)

evalMaybe :: Expr a -> Maybe a
evalMaybe = \ case
  Var {} -> Nothing
  Tag _ m _ _ -> m
  Const a -> Just a
  BinOp _ m _ _ _ -> m
  UnOp _ m _ _ -> m
  ExplicitD _ m _ _ _ _ -> m

-- | Remove 'tag' which opens a way to constant propagation
untag :: N a => Expr a -> Expr a
untag expr = S.evalState (go expr) IntMap.empty
  where
    go = \ case
      v@Var{} -> pure v
      Tag i _ _ e -> m i $ go e
      c@Const{} -> pure c
      BinOp i _ op a b -> m i $ liftM2 (foldBinOp op) (go a) (go b)
      UnOp i _ op e -> m i $ foldUnOp op <$> go e
      ExplicitD i _ v j h a -> m i $ mapMExplicitD explicitD go v j h a

eval :: N a => (VarId -> a) -> Expr a -> a
eval subst expr = S.evalState (go expr) IntMap.empty
  where
    go = \ case
      Var i v -> m i $ pure $ subst v
      Tag i (Just x) _ _ -> pure x
      Tag i _ _ e -> m i $ go e
      Const x -> pure x
      BinOp i (Just x) _ _ _ -> pure x
      BinOp i _ op a b -> m i $ liftM2 (binOp op) (go a) (go b)
      UnOp i (Just x) _ _ -> pure x
      UnOp i _ op a -> m i $ unOp op <$> go a
      ExplicitD i (Just x) _ _ _ _ -> pure x
      ExplicitD i _ v j h a -> m i $ mapMExplicitD explicitD go v j h a

m :: Int -> S.State (IntMap a) a -> S.State (IntMap a) a
m i act = do
  im <- S.get
  case IntMap.lookup i im of
    Nothing -> do
      !r <- act
      S.modify $ IntMap.insert i r
      pure r
    Just r ->
      pure r

binOp :: N a => BinOp -> (a -> a -> a)
binOp = \ case
  Plus      -> (+)
  Minus     -> (-)
  Multiply  -> (*)
  Divide    -> (/)
  Expt      -> (**)

unOp :: N a => UnOp -> (a -> a)
unOp = \ case
  Negate -> negate
  Abs    -> abs
  Signum -> signum
  Exp    -> exp
  Log    -> log
  Sqrt   -> sqrt
  Sin    -> sin
  Cos    -> cos
  Tan    -> tan
  ASin   -> asin
  ACos   -> acos
  ATan   -> atan
  Sinh   -> sinh
  Cosh   -> cosh
  Tanh   -> tanh
  ASinh  -> asinh
  ACosh  -> acosh
  ATanh  -> atanh
  Erf    -> erf
  Erfc   -> erfc
  Step   -> step

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
                 if | SCmp v' == 0 -> []
                    | otherwise    -> [(dv12, v')]
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
  | OConst a
  | OBinOp !(a -> a -> a) !I !I
  | OUnOp !(a -> a) !I
  | OExplicitD
    [I]             -- ^ variables
    [(I, Int)]      -- ^ jacobian [(∂x/∂var, var)]
    [(I, Int, Int)] -- ^ hessian  [(∂x/(∂var1*∂var2), var1, var2)]
    !I
--   deriving Show

evalOps :: N a => Array Int (Operation a) -> (VarId -> a) -> a
evalOps ops subst = r!hi
  where
    (lo, hi) = bounds r -- TODO: runST and evaluate the array sequentially
    r = amap e ops
    e = \ case
      OVar v -> subst v
      OTag i -> r!i
      OConst x -> x
      OBinOp f a b -> f (r!a) (r!b)
      OUnOp f a -> f (r!a)
      OExplicitD v j h a ->
        mapExplicitD explicitD (r!) v j h a

-- | Create a sequence of operations to evaluate the expression.
-- Every next operation can use results of previous operations, so we
-- keep the sharing automatically without an additional 'State' and
-- 'IntMap'. The profiler shows a lot of allocations in 'm' and
-- 'IntMap.insert', we're removing these allocations with 'compile'.
compileOps :: N a => Expr a -> Array Int (Operation a)
compileOps expr = listArray (0, nOps-1) $ reverse ops
  where
    CompileState _ ops nOps =
      S.execState (go expr) (CompileState IntMap.empty [] 0)
    go :: N a => Expr a -> Compile a Int
    go = \ case
      Var i v -> o i $ pure $ OVar v
      Tag i (Just x) _ _ -> iconst i x
      Tag i _ _ e -> o i $ OTag <$> go e
      Const x -> lit x
      BinOp i (Just x) _ _ _ -> iconst i x
      BinOp i _ op a b -> o i $ liftM2 (OBinOp $ binOp op) (go a) (go b)
      UnOp i (Just x) _ _ -> iconst i x
      UnOp i _ op a -> o i $ OUnOp (unOp op) <$> go a
      ExplicitD i (Just x) _ _ _ _ -> iconst i x
      ExplicitD i _ v j h a -> o i $ mapMExplicitD OExplicitD go v j h a
    o :: I -> Compile a (Operation a) -> Compile a Int
    o i act = do
      im <- S.gets cIdToOperation
      case IntMap.lookup i im of
        Nothing -> do
          !op <- act
          S.state $ \ (CompileState m ops nOps) ->
            (nOps, CompileState (IntMap.insert i nOps m) (op:ops) (nOps+1))
        Just oi ->
          pure oi
    iconst i x = o i $ pure $ OConst x
    -- add a literal constant without the Expr id mapping
    lit :: a -> Compile a Int
    lit c = S.state $ \ (CompileState m ops nOps) ->
      (nOps, CompileState m (OConst c:ops) (nOps+1))

type Compile e a = S.State (CompileState e) a
data CompileState a
  = CompileState
    { cIdToOperation   :: !(IntMap Int) -- ^ Expr id to operation index map
    , cOperations      :: ![Operation a]
    , cTotalOperations :: !Int
    }

------------------------------------------------------------------------------
-- Common subexpression elimination

cse :: (N a, StructuralOrd a) => Expr a -> Expr a
cse e = snd $ S.evalState (go e) (Map.empty, IntMap.empty)
  where
    go = \ case
      Var i v -> m i $
        get (CVar v) (var v)
      Tag i _ v e -> m i $ do
        (ce, se) <- go e
        get (CTag v ce) (tag v se)
      Const x ->
        get (CConst $ SCmp x) (Const x)
      BinOp i _ op a b -> m i $ do
        (ca, sa) <- go a
        (cb, sb) <- go b
        get (CBinOp op ca cb) (mkBinOp op sa sb)
      UnOp i _ op a -> m i $ do
        (ca, sa) <- go a
        get (CUnOp op ca) (mkUnOp op sa)
      ExplicitD i _ v j h a -> m i $ do
        (cv, sv) <- unzip <$> mapM go v
        (ca, sa) <- go a
        (cj, sj) <- fmap unzip $ for j $ \ (d,v) -> do
          (cd, sd) <- go d
          pure ((cd,v), (sd,v))
        (ch, sh) <- fmap unzip $ for h $ \ (d,v1,v2) -> do
          (cd, sd) <- go d
          pure ((cd,v1,v2), (sd,v1,v2))
        get (CExplicitD cv cj ch ca) (explicitD sv sj sh sa)
    get cexpr mkexpr = do
      (m,im) <- S.get
      case Map.lookup cexpr m of
        Nothing -> do
          S.put (Map.insert cexpr mkexpr m, im)
          pure (cexpr, mkexpr)
        Just e -> pure (cexpr, e)
    m i act = do
      (_,im) <- S.get
      case IntMap.lookup i im of
        Nothing -> do
          r <- act
          S.modify $ \ (m,im) -> (m, IntMap.insert i r im)
          pure r
        Just r ->
          pure r

-- 'Expr' that can be used as a key for the common subexpression elimination
data CExpr a
  = CVar VarId
  | CTag VarId (CExpr a)
  | CConst (SCmp a)
  | CBinOp BinOp (CExpr a) (CExpr a)
  | CUnOp UnOp (CExpr a)
  | CExplicitD [CExpr a] [(CExpr a, Int)] [(CExpr a, Int, Int)] (CExpr a)
  deriving (Eq, Ord, Show)

toCExpr = \ case
  Var _ v -> CVar v
  Tag _ _ v e -> CTag v $ toCExpr e
  Const c -> CConst $ SCmp c
  BinOp _ _ op a b -> CBinOp op (toCExpr a) (toCExpr b)
  UnOp _ _ op a -> CUnOp op (toCExpr a)
  ExplicitD _ _ v j h a -> mapExplicitD CExplicitD toCExpr v j h a

mapExplicitD c f v j h a = c
  (map f v)
  [(f d, v) | (d,v) <- j]
  [(f d, v1, v2) | (d,v1,v2) <- h]
  (f a)

mapMExplicitD c f v j h a = do
  ev <- for v f
  eh <- for h $ \ (d,v1,v2) -> (,v1,v2) <$> f d
  ej <- for j $ \ (d,v) -> (,v) <$> f d
  ea <- f a
  pure $ c ev ej eh ea

constToMaybe = \ case
  Const a -> Just a
  _ -> Nothing

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
  e@FExplicitD{} -> e
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
    e = fexpand

factor :: N a => Expr a -> FExpr a
factor = \ case
  Var _ i -> FVar i
  Tag _ _ i e -> FTag i $ factor e
  Const c -> FSum (SCmp c) Map.empty
  BinOp _ _ op a b ->
    let m ca cb = Map.fromListWith (+) [(factor a, ca), (factor b, cb)]
    in
    case op of
      Plus      -> FSum 0 $ m 1 1
      Minus     -> FSum 0 $ m 1 (-1)
      Multiply  -> FProduct 1 $ m 1 1
      Divide    -> FProduct 1 $ m 1 (-1)
      Expt      -> FExpt (factor a) (factor b)
  UnOp _ _ op e -> FUnOp op $ factor e
  ExplicitD _ _ v j h e -> mapExplicitD FExplicitD factor v j h e

------------------------------------------------------------------------------
-- Instances

-- That's ugly, we have a "symbolic" expression, yet it contains
-- 'Double's, lifted numbers and compared by converting to 'Double'
-- (that can fail if we don't have all variables).
--
-- OTOH we need to use @Expr (R.Reverse s Double)@ and don't care
-- about passing variable mappings (hence 'EmbeddedVar') and
-- converting 'Double' to 'Rational' and back may not only be slow but
-- also doesn't roundtrip with Infinity or NaN.
-- And comparing numeric result makes much more sense in Expr AD usage.
instance N a => Eq (Expr a) where
  a == b = toD a == toD b

instance N a => Ord (Expr a) where
  a `compare` b = toD a `compare` toD b

-- default 'Eq', could it be derived in some way?
instance StructuralEq a => StructuralEq (Expr a) where
  structuralEq a b = case (a, b) of
    (Var ia a, Var ib b) -> ia == ib || a == b
    (Tag ia _ ta ea, Tag ib _ tb eb) -> ia == ib || ta == tb && structuralEq ea eb
    (Const a, Const b) -> structuralEq a b -- but NaN /= NaN
    (BinOp ia _ oa a1 a2, BinOp ib _ ob b1 b2) -> ia == ib ||
      oa == ob && structuralEq a1 b1 && structuralEq a2 b2
    (UnOp ia _ oa a, UnOp ib _ ob b) -> ia == ib ||
      oa == ob && structuralEq a b
    (ExplicitD ia _ va ja ha a, ExplicitD ib _ vb jb hb b) -> ia == ib ||
      structuralEq va vb && structuralEq ja jb &&
      structuralEq ha hb && structuralEq a b
    -- to have a warning when new cases are added:
    (Var{}, _) -> False
    (Tag{}, _) -> False
    (Const{}, _) -> False
    (BinOp{}, _) -> False
    (UnOp{}, _) -> False
    (ExplicitD{}, _) -> False

instance N a => IsString (Expr a) where
  fromString = parseExpr

foldBinOp op (Const a) (Const b) = Const $ binOp op a b
foldBinOp op a b = mkBinOp op a b

mkBinOp op a b = withNewId $ \ i ->
  BinOp i (liftA2 (binOp op) (evalMaybe a) (evalMaybe b)) op a b

foldUnOp op (Const a) = Const $ unOp op a
foldUnOp op a = mkUnOp op a

mkUnOp op a = withNewId $ \ i -> UnOp i (unOp op <$> evalMaybe a) op a

instance N a => Num (Expr a) where
  a + b
   | SCmp a == 0 = b
   | SCmp b == 0 = a
   | otherwise   = foldBinOp Plus a b
  a - b
   | SCmp a == 0 = -b
   | SCmp b == 0 = a
   | otherwise   = foldBinOp Minus a b
  a * b
   | SCmp a == 0 = 0
   | SCmp b == 0 = 0
   | SCmp a == 1 = b
   | SCmp b == 1 = a
   | SCmp a == -1 = negate b
   | SCmp b == -1 = negate a
   | otherwise   = foldBinOp Multiply a b

  negate = foldUnOp Negate

  abs = foldUnOp Abs
  signum = foldUnOp Signum

  fromInteger = Const . fromInteger

instance N a => Fractional (Expr a) where
  a / b
--   | structuralEq a b = 1
   | SCmp b == 1 = a
--   | SCmp a == 0 && SCmp b /= 0 = 0
   | otherwise   = foldBinOp Divide a b

  fromRational = Const . fromRational

instance N a => Floating (Expr a) where
  pi    = Const pi
  exp   = foldUnOp Exp
  log   = foldUnOp Log
  sqrt  = foldUnOp Sqrt

  sin   = foldUnOp Sin
  cos   = foldUnOp Cos
  tan   = foldUnOp Tan
  asin  = foldUnOp ASin
  acos  = foldUnOp ACos
  atan  = foldUnOp ATan
  sinh  = foldUnOp Sinh
  cosh  = foldUnOp Cosh
  tanh  = foldUnOp Tanh
  asinh = foldUnOp ASinh
  acosh = foldUnOp ACosh
  atanh = foldUnOp ATanh

  a ** b
   | SCmp b == 0 = 1
   | otherwise   = foldBinOp Expt a b
--   logBase = foldBinOp LogBase

--     log1p x = log (1 + x)
--     expm1 x = exp x - 1
--     log1pexp x = log1p (exp x)
--     log1mexp x = log1p (negate (exp x))

instance N a => Erf (Expr a) where
  erf  = foldUnOp Erf
  erfc = foldUnOp Erfc

instance StructuralOrd a => StructuralOrd (Expr a) where
  structuralCompare = compare `on` toCExpr

instance N a => N (Expr a) where
  exprType _ = "Expr (" <> exprType (undefined :: a) <> ")"
  step = foldUnOp Step
  toN = Const . toN
  toD = toD . unsafeEval "toD"
  explicitD v j h e = maybe new Const folded
    where
      folded = mapMExplicitD explicitD constToMaybe v j h e
      new = withNewId $ \ i -> ExplicitD i m v j h e
      m = mapMExplicitD explicitD evalMaybe v j h e

  dLevel _ = DLAny

unsafeEval debugName =
  eval (\ v -> error $ "toD: undefined variable " <> show v)

------------------------------------------------------------------------------
-- Show

data ShowExprMode
  = SEM_Haskell -- ^ Haskell-style, no parens in functions
  | SEM_Maxima  -- ^ suitable for copy-pasting into Maxima
  deriving (Eq, Show)

instance N a => Show (Expr a) where
  showsPrec d e = (showExpr SEM_Haskell (False, P.AssocNone, d) e <>)

toMaxima :: N a => Expr a -> String
toMaxima = filter (/= ' ') . showExpr SEM_Maxima (False, P.AssocNone, 0)

showExprWithSharing :: N a => Expr a -> String
showExprWithSharing expr
  | null vars = toplevel
  | otherwise = unlines
    $ toplevel : mconcat ["where -- ", show (length vars), " subexpressions"]
    : [mconcat ["  ", idx i, " = ", c] | (i,c) <- vars]
  where
    (toplevel, (_, vars)) = S.runState (go expr) (IntSet.empty, [])
    idx i = "_" <> show i
    go = \ case
      Var _ n -> pure n
      Tag i _ n e -> add i ("_" <> n) $ go e
      Const a -> pure $ show a
      BinOp i _ op l r -> add i "" $ do
        sl <- go l
        sr <- go r
        pure $ unwords [sl, showBinOp op, sr]
      UnOp i _ op a -> add i "" $ do
        la <- go a
        pure $ unwords [showUnOp op, la]
      ExplicitD i _ v j h e -> add i "" $
        mapMExplicitD (\ v j h e -> unwords ["ExplicitD", show v, show j, show h, show e])
          go v j h e
    add i suffix action = do
      (m, vs) <- S.get
      when (IntSet.notMember i m) $ do
        S.put (IntSet.insert i m, vs)
        content <- action
        S.modify $ \ (m,vs) -> (m, (i,content):vs)
      pure $ idx i <> suffix

showExpr :: N a => ShowExprMode -> (Bool, P.Assoc, Int) -> Expr a -> String
showExpr m p@(pNegate, pa, pp) = \ case
  Var _ n -> parensIf argParens [n]
  Tag _ _ n e ->
    if m == SEM_Maxima then
      showExpr m p e
    else
      let (a, _aLeft, aRight, p) = tagFixity
      in
        parensIf (p < pp || (p == pp && diffAssoc a pa))
        [n,"@",showExpr m (False,aRight,p) e]
  Const a ->
    parensIf (a < 0 || argParens) [show a]
--     | n <- numerator a
--     , d <- denominator a
--     -> if d == 1 then parensIf (n < 0 || argParens) [show n]
--        else showExpr m (False,pa,pp) (fromInteger n / fromInteger d :: Expr ())
       -- show like a division -1%2 -> (-1)/2, not (-1/2) as the second
       -- one will be parsed as a division and not as a rational constant
  BinOp _ _ op l r ->
    let (a, aLeft, aRight, p) = fixity op
    in
      parensIf (p < pp || (p == pp && diffAssoc a pa))
        [showExpr m (False,aLeft ,p) l, showBinOp op
        ,showExpr m (False,aRight,p) r]
  UnOp _ _ op a ->
    let f@(_, _, p) = (op == Negate, P.AssocNone, 10)
    in
      parensIf (p <= pp || (op == Negate && pp > 0)) [showUnOp op, showExpr m f a]
  ExplicitD i _ v j h a ->
    unwords ["ExplicitD", show v, show j, show h, show a]
  where
    argParens = m == SEM_Maxima && pp == 10 && not pNegate

diffAssoc a b = case (a, b) of -- no Eq instance for Assoc
  (P.AssocLeft, P.AssocLeft) -> False
  (P.AssocRight, P.AssocRight) -> False
  _ -> True
parensIf :: Bool -> [String] -> String
parensIf needParens (unwords -> x)
  | needParens = "(" <> x <> ")"
  | otherwise  = x

debugShowExpr :: N a => Expr a -> String
debugShowExpr = \ case
  Var i n -> unwords ["Var", show i, show n]
  Tag i m t e -> unwords ["Tag", show i, sm m, show t, go e]
  Const a -> mconcat ["Const (", show a, ")"]
  BinOp i m op a b -> unwords ["BinOp", show i, sm m, show op, go a, go b]
  UnOp i m op a -> unwords ["UnOp", show i, sm m, show op, go a]
  ExplicitD i m v j h a -> unwords ["ExplicitD", show i, sm m, "TODO ExplicitD"] -- show op, go a]
  where
    go x = mconcat ["(", debugShowExpr x, ")"]
    sm x = showsPrec 10 x ""

showBinOp = \ case
  Plus      -> "+"
  Minus     -> "-"
  Multiply  -> "*"
  Divide    -> "/"
  Expt      -> "**"

showUnOp = \ case
  Negate -> "-"
  Abs    -> "abs"
  Signum -> "signum"
  Exp    -> "exp"
  Log    -> "log"
  Sqrt   -> "sqrt"
  Sin    -> "sin"
  Cos    -> "cos"
  Tan    -> "tan"
  ASin   -> "asin"
  ACos   -> "acos"
  ATan   -> "atan"
  Sinh   -> "sinh"
  Cosh   -> "cosh"
  Tanh   -> "tanh"
  ASinh  -> "asinh"
  ACosh  -> "acosh"
  ATanh  -> "atanh"
  Erf    -> "erf"
  Erfc   -> "erfc"
  Step   -> "step"

instance N a => Show (FExpr a) where
  showsPrec d e = (showFExpr (d < 10) e <>)

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

------------------------------------------------------------------------------
-- Parsing

fixity = \ case
            --  associativiy  left branch  right branch  precedence
  Plus      -> (P.AssocLeft , P.AssocLeft, P.AssocLeft , 6)
  Minus     -> (P.AssocLeft , P.AssocLeft, P.AssocNone , 6)
  Multiply  -> (P.AssocLeft , P.AssocLeft, P.AssocLeft , 7)
  Divide    -> (P.AssocLeft , P.AssocLeft, P.AssocNone , 7)
  Expt      -> (P.AssocRight, P.AssocNone, P.AssocRight, 8)

tagFixity =    (P.AssocRight, P.AssocNone, P.AssocRight, 0)

parseExpr :: N a => String -> Expr a
parseExpr s = either (error . show) id $ P.parse (expr <* P.eof) s s
  where
    expr = P.buildExpressionParser table term <?> "expression"

    term
      =   parens expr
      <|> constant
      <|> (var <$> identifier)
      <?> "simple expression"

    constant
      = either (Const . fromInteger) (Const . realToFrac) <$> naturalOrFloat

    table =
      [ [prefix "+" id] <>
        [prefix (showUnOp op) (mkUnOp op)
        |op <- sortBy (comparing $ Down . show) -- put "erfc" before "erf"
          [minBound..maxBound :: UnOp]]
      ]
      <> binops

    binops =
      reverse $ Map.elems $ Map.fromListWith (<>) $
      [ (prio, [binary (showBinOp op) (mkBinOp op) assoc])
      | op <- [minBound..maxBound]
      , let (assoc, _, _, prio) = fixity op ]
      <>
      [ let (assoc, _, _, prio) = tagFixity
        in
        (prio, [binary "@" tagged assoc]) ]
    tagged (Var _ vi) e = tag vi e
    tagged v _ = error "Expected a tag name before '@'"

    binary name fun assoc = P.Infix  (fun <$ reservedOp name) assoc
    prefix name fun       = P.Prefix (fun <$ reservedOp name)

    P.TokenParser{parens, identifier, naturalOrFloat, reservedOp, integer, decimal, lexeme}
      = P.makeTokenParser P.emptyDef
        { P.reservedOpNames = "@" : map show [minBound..maxBound :: BinOp] }

------------------------------------------------------------------------------
-- Tests

quickCheckBig p = quickCheckWith (stdArgs{maxSuccess=10000}) p

instance Arbitrary UnOp where
  arbitrary = chooseEnum (minBound, maxBound)
instance Arbitrary BinOp where
  arbitrary = chooseEnum (minBound, maxBound)
instance Arbitrary (Expr Double) where
  arbitrary = genExpr (const True) testVars

testVars :: Floating a => [(VarId, a)]
testVars = [("a",1),("b",-1.5),("c",pi),("x",exp 1)]
testEval x = eval (\ v -> fromJust $ lookup v testVars) x
substTest x = eval (\ v -> toN $ fromJust $ lookup v testVars) x

genExpr :: (Expr Double -> Bool) -> [(String, Double)] -> Gen (Expr Double)
genExpr goodExpr vars = g `suchThat` goodExpr
  where
    -- need to check every subexpression, otherwise we can build
    -- non-NaN from NaNs (1**NaN = 1), or build non-jittery computations
    -- from jittery ones and it will break differentiation
    g = (`suchThat` goodSimplifyExpr) $ oneof
      [var . fst <$> elements vars
      ,Const <$> arbitrary
      ,tag <$> elements ["i","j","k"] <*> g
      ,mkBinOp <$> arbitrary <*> g <*> g
      ,mkUnOp  <$> suchThat arbitrary diffUnOp <*> g
      -- don't generate explicitD at all?
      ]
    diffUnOp = \ case
      Abs -> False
      Signum -> False
      _ -> True

goodSimplifyExpr :: Expr Double -> Bool
goodSimplifyExpr expr = ok (e expr) && case expr of
  BinOp _ _ Expt _ (Const b) -> abs b < 1e3
  BinOp _ _ Expt _ b -> abs (e b) < 1e3
    && abs (e b - (fromInteger $ round $ e b)) > eps
  -- (-1)**30.000000001 = NaN, so we either check constant exponents
  -- that have no jitter or exponents that are far enough from integers
  BinOp _ _ Divide _ b -> abs (e b) > eps
  UnOp _ _ op x
    | op `elem` ([Sin, Cos, Tan] :: [UnOp]) ->
      -- trigonometric functions can have a huge difference
      -- when pi is on the level of floating point jitter
      -- so we cut the range here
      abs (e x) < 1e3
    | otherwise -> all (ok . unOp op . (e x +)) (l [eps, -eps])
      -- jitter can lead us out of the function domain
      -- 'tanh 0.99999' can be fine but 'tanh 1' is not
  _ -> True
  where
    l :: [a] -> [a]
    l = id
    e x = testEval x
    eps = 1e-5
    ok x = not $ isNaN x || isInfinite x || abs x > 1e5 || abs x < eps

newtype TestDiffExpr = TestDiffExpr (Expr Double) deriving Show
instance Arbitrary TestDiffExpr where
  arbitrary = TestDiffExpr <$>
    genExpr (\ e -> goodSimplifyExpr e && goodDiffExpr e) testVars

newtype TestSimplifyExpr = TestSimplifyExpr (Expr Double) deriving Show
instance Arbitrary TestSimplifyExpr where
  arbitrary = TestSimplifyExpr <$> genExpr goodSimplifyExpr testVars

-- | Can we get a more or less stable numerical derivative?
goodDiffExpr e =
  abs (numDiff e) > 1e-3 && abs (numDiff e) < 1e5
  && eq_eps 1e-4 (numDiff' defaultBump e) (numDiff' (defaultBump*10) e)

defaultBump = 0.00001
numDiff = numDiff' defaultBump
numDiff' bump e = (eb bump - eb (-bump)) / (2*bump)
  where
    eb b = eval (\ case "x" -> x+b; v -> fromJust $ lookup v testVars) e
    x = testEval "x"

prop_diff (TestDiffExpr e) = counterexample debug $ eq_eps 1e-1 n s
  where
    debug = unlines
      ["Debug Expr:"
      ,debugShowExpr e
      ,"Diff:"
      ,show d
      ,"Diff simplified:"
      ,show ds
      ,"numeric  = " <> show n
      ,"symbolic = " <> show s]
    d = diffVar e "x"
    ds = simplify d
    n = numDiff e
    s = testEval ds

prop_parse :: Expr Double -> Property
prop_parse x = counterexample debug $ e `structuralEq` parseExpr (show e)
  where
    debug = unlines
      ["Debug Expr:"
      ,debugShowExpr x]
    -- need to 'show' first to normalize associativity,
    -- otherwise 'a*(b*c)*d' will not roundtrip as it will be showed
    -- as 'a*b*c*d'
    e = parseExpr (show x) :: Expr Double

prop_simplify (TestSimplifyExpr x) = counterexample debug $ eq_eps 1e-6 l r
  where
    debug = unlines
      ["Debug Expr:"
      ,debugShowExpr x
      ,"Simplified:"
      ,show s
      ,"l = " <> show l
      ,"r = " <> show r]
    l = e x
    r = e s
    s = simplify x
    e = testEval

eq_eps eps a b = a == b
  || (b /= 0 && abs ((a-b)/b) < eps)
  || (b == 0 && abs a < eps)

return [] -- workaround to bring prop_* in scope
testSymbolic = do
  ok <- $forAllProperties $
    quickCheckWithResult (stdArgs {maxSuccess = 1_000_000})
  unless ok exitFailure
