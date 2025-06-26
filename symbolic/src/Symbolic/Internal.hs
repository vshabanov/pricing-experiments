{-# LANGUAGE DeriveAnyClass #-}
-- | Internal definitions of 'Expr' for use in tests
module Symbolic.Internal
  ( Expr(..)
  , UnOp(..)
  , BinOp(..)
  , VarId
  , var
  , tag
  , lift
  , unlift
  , eval

  , m
  , mapExplicitD, mapMExplicitD
  , unOp, mkUnOp, foldUnOp
  , binOp, mkBinOp, foldBinOp

  , toMaxima
  , toHaskell
  , showExprWithSharing
  )
  where

import Control.Applicative ((<|>))
import Control.DeepSeq
import Control.Monad
import Control.Monad.State.Strict qualified as S
import Data.IntMap (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.IntSet qualified as IntSet
import Data.List
import Data.Map.Strict qualified as Map
import Data.Number.Erf
import Data.Ord
import Data.String
import Data.Traversable
import GHC.Generics (Generic)
import Number
import StructuralComparison
import Text.Parsec ((<?>))
import Text.Parsec qualified as P
import Text.Parsec.Expr qualified as P
import Text.Parsec.Language qualified as P
import Text.Parsec.Token qualified as P
import Unique (I, withNewId)

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
  | If !I !Ordering (Expr a) (Expr a)
    (Expr a) -- ^ then branch
    (Expr a) -- ^ else branch
  | BinOp !I !(Maybe a) !BinOp (Expr a) (Expr a)
  | UnOp !I !(Maybe a) !UnOp (Expr a)
  | ExplicitD !I !(Maybe a)
    [Expr a]             -- ^ variables
    [(Expr a, Int)]      -- ^ jacobian [(∂x/∂var, var)]
    [(Expr a, Int, Int)] -- ^ hessian  [(∂x/(∂var1*∂var2), var1, var2)]
    (Expr a)
  deriving (Generic, Show, NFData)

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
  | Normcdf
  | Inverf
  | Inverfc
  | Invnormcdf
  | Step
  deriving (Eq, Ord, Enum, Bounded, Show, Generic, NFData)

var x = withNewId $ \ i -> Var i x
tag t e = withNewId $ \ i -> Tag i (evalMaybe e) t e
lift = Const
unlift e = unsafeEval "unlift" e
-- explicit = Explicit

evalMaybe :: Expr a -> Maybe a
evalMaybe = \ case
  Var{} -> Nothing
  Tag _ m _ _ -> m
  Const a -> Just a
  If{} -> Nothing
  BinOp _ m _ _ _ -> m
  UnOp _ m _ _ -> m
  ExplicitD _ m _ _ _ _ -> m

eval :: N a => (VarId -> a) -> Expr a -> a
eval subst expr = S.evalState (go expr) IntMap.empty
  where
    go = \ case
      Var i v -> m i $ pure $ subst v
      Tag i (Just x) _ _ -> pure x
      Tag i _ _ e -> m i $ go e
      Const x -> pure x
      If i c a b t e -> m i $ liftM4 (if_ c) (go a) (go b) (go t) (go e)
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
  Normcdf -> normcdf
  Inverf  -> inverf
  Inverfc -> inverfc
  Invnormcdf -> invnormcdf
  Step   -> step

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
-- Instances

-- It's ugly, we have a "symbolic" expression, yet it contains
-- 'Double's, lifted numbers and is compared by converting to a 'Double'
-- (the conversion can fail if we don't have all variables).
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
instance N a => StructuralEq (Expr a) where
  structuralEq a b = case (a, b) of
    (Var ia a, Var ib b) -> ia == ib || a == b
    (Tag ia _ ta ea, Tag ib _ tb eb) -> ia == ib || ta == tb && structuralEq ea eb
    (Const a, Const b) -> structuralEq a b -- but NaN /= NaN
    (If ia ca aa ba ta ea, If ib cb ab bb tb eb) ->
      ia == ib || ca == cb && structuralEq aa ab && structuralEq ba bb
      && structuralEq ta tb && structuralEq ea eb
    (UnOp ia _ oa a, UnOp ib _ ob b) -> ia == ib ||
      oa == ob && structuralEq a b
    (BinOp ia _ oa a1 a2, BinOp ib _ ob b1 b2) -> ia == ib ||
      oa == ob && structuralEq a1 b1 && structuralEq a2 b2
    (ExplicitD ia _ va ja ha a, ExplicitD ib _ vb jb hb b) -> ia == ib ||
      structuralEq va vb && structuralEq ja jb &&
      structuralEq ha hb && structuralEq a b
--     (BinOp ia _ oa _ _, BinOp ib _ ob _ _) -> ia == ib || oa == ob && cseEq a b
--     (ExplicitD ia _ _ _ _ _, ExplicitD ib _ _ _ _ _) -> ia == ib || cseEq a b
    -- cseEq is slightly slower in our case

    -- to have a warning when new cases are added:
    (Var{}, _) -> False
    (Tag{}, _) -> False
    (Const{}, _) -> False
    (BinOp{}, _) -> False
    (UnOp{}, _) -> False
    (ExplicitD{}, _) -> False
    (If{}, _) -> False

instance N a => IsString (Expr a) where
  fromString = parseExpr

foldBinOp op (Const a) (Const b) = Const $ binOp op a b
foldBinOp op a b = mkBinOp op a b

mkBinOp op a b = withNewId $ \ i ->
  BinOp i (liftA2 (binOp op) (evalMaybe a) (evalMaybe b)) op a b
--   BinOp i c op a b
--   where c = do
--           !ea <- evalMaybe a
--           !eb <- evalMaybe b
--           pure $! binOp op ea eb
-- slower, more allocations

foldUnOp op (Const a) = Const $ unOp op a
foldUnOp op a = mkUnOp op a

mkUnOp op a = withNewId $ \ i -> UnOp i (unOp op <$> evalMaybe a) op a
-- mkUnOp op a = withNewId $ \ i -> UnOp i c op a
--   where c = do
--           !ea <- evalMaybe a
--           pure $! unOp op ea


instance N a => Num (Expr a) where
  a + b
   | isZero a  = b
   | isZero b  = a
   | otherwise = foldBinOp Plus a b
  a - b
   | isZero a  = -b
   | isZero b  = a
   | otherwise = foldBinOp Minus a b
  a * b
   | isZero a  = 0
   | isZero b  = 0
   | isOne a   = b
   | isOne b   = a
   | otherwise = foldBinOp Multiply a b

  negate = foldUnOp Negate

  abs = foldUnOp Abs
  signum = foldUnOp Signum

  fromInteger = Const . fromInteger

instance N a => Fractional (Expr a) where
  a / b
   | isOne b   = a
--   | isZero a && SCmp b /= 0 = 0
   | otherwise = foldBinOp Divide a b

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
   | isZero b  = 1
   | otherwise = foldBinOp Expt a b
--   logBase = foldBinOp LogBase

--     log1p x = log (1 + x)
--     expm1 x = exp x - 1
--     log1pexp x = log1p (exp x)
--     log1mexp x = log1p (negate (exp x))

instance N a => Erf (Expr a) where
  erf     = foldUnOp Erf
  erfc    = foldUnOp Erfc
  normcdf = foldUnOp Normcdf

instance N a => InvErf (Expr a) where
  inverf     = foldUnOp Inverf
  inverfc    = foldUnOp Inverfc
  invnormcdf = foldUnOp Invnormcdf

instance N a => StructuralOrd (Expr a) where
  structuralCompare = error "StructuralOrd (Expr a) is not implemented"
  -- need some magic with CSE to make it fast (to take the sharing into account)

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
  isZero = \ case
    Const x -> isZero x
    _ -> False
  isOne = \ case
    Const x -> isOne x
    _ -> False
  if_ c ea eb t e = case (evalMaybe ea, evalMaybe eb) of
    (Just a, Just b)
      | compare a b == c -> t
      | otherwise -> e
    _ -> withNewId $ \ i -> If i c ea eb t e

unsafeEval debugName =
  eval (\ v -> error $ "toD: undefined variable " <> show v)

------------------------------------------------------------------------------
-- Show

data ShowExprMode
  = SEM_Haskell -- ^ Haskell-style, no parens in functions
  | SEM_Maxima  -- ^ suitable for copy-pasting into Maxima
  deriving (Eq, Show)

-- | Produce Haskell-style expression
toHaskell :: N a => Expr a -> String
toHaskell = showExpr SEM_Haskell (False, P.AssocNone, 0)

-- | Produce Maxima expression
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
      If i c a b t e -> add i "" $ do
        sa <- go a
        sb <- go b
        st <- go t
        se <- go e
        pure $ unwords ["if", show c, sa, sb, st, se]
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
  ExplicitD _ _ v j h a ->
    unwords ["ExplicitD", show v, show j, show h, show a]
  If _ c a b t e ->
    unwords ["if", show c, show a, show b, show t, show e]
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
  Normcdf -> "normcdf"
  Inverf  -> "inverf"
  Inverfc -> "inverfc"
  Invnormcdf -> "invnormcdf"
  Step   -> "step"

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
