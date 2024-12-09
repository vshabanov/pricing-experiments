{-# LANGUAGE OverloadedLists, DeriveAnyClass, TemplateHaskell #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}
-- | Symbolic differentiation
module Symbolic
  ( Expr
  , VarId
  , var
  , tag
  , lift
  , unlift
  , eval
  , diff
  , simplify
  , toMaxima

  , testSymbolic
  ) where

import Control.Monad
import System.Exit
import Data.Number.Erf
import Data.Ord
import Data.Ratio
import Data.Array
import Data.Bifunctor
import Data.Either
import Data.Maybe
import Data.List
import Data.String
import Data.Map (Map)
import qualified Data.Map.Strict as Map

import Control.Applicative ((<|>))
import Text.Parsec ((<?>))
import qualified Text.Parsec as P
import qualified Text.Parsec.Expr as P
import qualified Text.Parsec.Token as P
import qualified Text.Parsec.Language as P

import Test.QuickCheck
import Number
import Data.Function
import Control.DeepSeq
import GHC.Generics (Generic)
import Debug.Trace

test = do
  fix $ \ loop -> do
    l <- getLine
    unless (l == "ok") loop

{- | Expression that can store values and variables.

It can be both evaluated numerically and differentiated symbolically.

If 'a' is an AD value, symbolically differentiated 'Expr' will have
correct sensitivities to market inputs.
-}
data Expr a
  = Var VarId
    -- | Named sub-expression that we can differentiate on.
    -- It can keep AD variables beneath.
  | Tag VarId (Expr a)
    -- | Lifted AD value.
  | Const a
  | BinOp BinOp (Expr a) (Expr a)
  | UnOp UnOp (Expr a)
    -- | Non-differentiable
  | NonDiff String
  deriving (Generic, NFData)

var = Var
tag = Tag
lift = Const
unlift e = unsafeEval "unlift" e

type VarId = String

data BinOp
  = Plus
  | Minus
  | Multiply
  | Divide
  | Expt -- ^ a**b
  | ExplicitD -- ^ Explicit derivative to be used instead of an expression
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

eval :: N a => (VarId -> a) -> Expr a -> a
eval subst = \ case
  Var id -> subst id
  Tag _ x -> e x
  Const a -> a
  BinOp op a b -> binOp op (e a) (e b)
  UnOp op a -> unOp op (e a)
  NonDiff s -> error $ "non-differentiable: " <> s
  where
    e = eval subst

binOp :: N a => BinOp -> (a -> a -> a)
binOp = \ case
  Plus      -> (+)
  Minus     -> (-)
  Multiply  -> (*)
  Divide    -> (/)
  Expt      -> (**)
  ExplicitD -> error "ExplicitD" -- explicitD

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
    Var i   -> i
    Tag i _ -> i
    v -> error $ "Please use 'var' to differentiate instead of " <> show v

diffVar :: N a => Expr a -> VarId -> Expr a
diffVar e i = case e of
  Var vi
    | vi == i   -> 1
    | otherwise -> 0
  Tag vi e
    | vi == i   -> 1
    | otherwise -> Tag vi $ d e -- is it correct at all? throw error?
  Const _ -> 0
  BinOp op a b -> binOp op a b
  UnOp op a -> dUnOp op a * d a
  NonDiff s -> error $ "non-differentiable: " <> s
  where
    d x = diffVar x i
    binOp op a b = case op of
      Plus      -> d a + d b
      Minus     -> d a - d b
      Multiply  -> d a * b + a * d b
      Divide    -> (d a * b - a * d b) / b^2
      Expt      -> a**b * (log a * d b + b * d a / a)
      ExplicitD -> a * d b
    dUnOp op x = case op of
      Negate -> -1
      Abs    -> NonDiff "abs"
      Signum -> NonDiff "signum"
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
  | FExplicitD (FExpr a) (FExpr a)
  | FSum (SCmp a) (Map (FExpr a) (SCmp a))
    -- ^ c0 + expr1*c1 + expr2*c2 ...
  | FProduct (SCmp a) (Map (FExpr a) Integer)
    -- ^ c0 * expr1^c1 * expr2^c2 ...
  | FNonDiff String
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
  FExplicitD d e -> FExplicitD (fsimp d) (fsimp e)
  FUnOp Negate (FProduct c es) -> FProduct (-c) es
  FUnOp Negate (FSum c es) -> FSum (-c) $ Map.map negate es
  FUnOp Negate (FUnOp Negate e) -> e
  FUnOp Exp (toConst -> Just 0) -> FSum 1 []
  FUnOp Cos (FUnOp Negate x) -> FUnOp Cos x
  FUnOp Sin (FUnOp Negate x) -> FUnOp Negate (FUnOp Sin x)
  FUnOp op e -> FUnOp op (fsimp e)
  e@FVar{} -> e
  FTag i e -> FTag i (fsimp e)
  e@FNonDiff{} -> e
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
  FExplicitD a b -> error "explicitD" -- e a `explicitD` e b
  FUnOp op x -> unOp op $ e x
  FVar i -> var i
  FTag i x -> tag i (e x)
  FNonDiff s -> eval (error "var in NonDiff?") (NonDiff s)
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
  Var i -> FVar i
  Tag i e -> FTag i $ factor e
  Const c -> FSum (SCmp c) Map.empty
  BinOp op a b ->
    let m ca cb = Map.fromListWith (+) [(factor a, ca), (factor b, cb)]
    in
    case op of
      Plus      -> FSum 0 $ m 1 1
      Minus     -> FSum 0 $ m 1 (-1)
      Multiply  -> FProduct 1 $ m 1 1
      Divide    -> FProduct 1 $ m 1 (-1)
      Expt      -> FExpt (factor a) (factor b)
      ExplicitD -> FExplicitD (factor a) (factor b)
  UnOp op e -> FUnOp op $ factor e
  NonDiff s -> FNonDiff s

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
    (Var a, Var b) -> a == b
    (Tag ta ea, Tag tb eb) -> ta == tb && structuralEq ea eb
    (Const a, Const b) -> structuralEq a b -- but NaN /= NaN
    (BinOp ao a1 a2, BinOp bo b1 b2) ->
      ao == bo && structuralEq a1 b1 && structuralEq a2 b2
    (UnOp ao a, UnOp bo b) ->
      ao == bo && structuralEq a b
    (NonDiff a, NonDiff b) -> a == b
    -- to have a warning when new cases are added:
    (Var{}, _) -> False
    (Tag{}, _) -> False
    (Const _, _) -> False
    (BinOp{}, _) -> False
    (UnOp{}, _) -> False
    (NonDiff{}, _) -> False

instance Fractional a => IsString (Expr a) where
  fromString = parseExpr

foldBinOp op (Const a) (Const b) = Const $ binOp op a b
foldBinOp op a b = BinOp op a b

--foldUnOp op (Const a) = Const $ unOp op a
foldUnOp op a = UnOp op a

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

  (**) = foldBinOp Expt
--   logBase = foldBinOp LogBase


--     log1p x = log (1 + x)
--     expm1 x = exp x - 1
--     log1pexp x = log1p (exp x)
--     log1mexp x = log1p (negate (exp x))

instance N a => Erf (Expr a) where
  erf  = foldUnOp Erf
  erfc = foldUnOp Erfc

instance StructuralEq a => StructuralOrd (Expr a) where
  structuralCompare = error "StructuralOrd (Expr a) is not implemented"

instance N a => N (Expr a) where
  step = foldUnOp Step
--   explicitD a b
--     | SCmp a == 0 = 0
--     | otherwise   = foldBinOp ExplicitD a b
  toN = Const . toN
  toD = toD . unsafeEval "toD"

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

showExpr :: N a => ShowExprMode -> (Bool, P.Assoc, Int) -> Expr a -> String
showExpr m p@(pNegate, pa, pp) = \ case
  Var n -> parensIf argParens [n]
  Tag n e ->
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
  BinOp op l r ->
    let (a, aLeft, aRight, p) = fixity op
    in
      parensIf (p < pp || (p == pp && diffAssoc a pa))
        [showExpr m (False,aLeft ,p) l, showBinOp op
        ,showExpr m (False,aRight,p) r]
  UnOp op a ->
    let f@(_, _, p) = (op == Negate, P.AssocNone, 10)
    in
      parensIf (p <= pp || (op == Negate && pp > 0)) [showUnOp op, showExpr m f a]
  NonDiff s -> error $ "non-differentiable: " <> s
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
  Var n -> "Var " <> show n
  Tag t e -> mconcat ["Tag ", show t, " (", show e, ")"]
  Const a -> mconcat ["Const (", show a, ")"]
  BinOp op a b -> unwords ["BinOp", show op, go a, go b]
  UnOp op a -> unwords ["UnOp", show op, go a]
  NonDiff s -> "NonDiff " <> show s
  where
    go x = mconcat ["(", debugShowExpr x, ")"]

showBinOp = \ case
  Plus      -> "+"
  Minus     -> "-"
  Multiply  -> "*"
  Divide    -> "/"
  Expt      -> "**"
  ExplicitD -> "'"

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
  FNonDiff s -> show (NonDiff s :: Expr Double)
  FExpt a b -> showFExpr False a <> "**" <> showFExpr False b
  FExplicitD d e -> show d <> "'" <> showFExpr root e
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
  ExplicitD -> (P.AssocRight, P.AssocNone, P.AssocRight, 9)

tagFixity =    (P.AssocRight, P.AssocNone, P.AssocRight, 0)

parseExpr :: Fractional a => String -> Expr a
parseExpr s = either (error . show) id $ P.parse (expr <* P.eof) s s
  where
    expr = P.buildExpressionParser table term <?> "expression"

    term
      =   parens expr
      <|> constant
      <|> (Var <$> identifier)
      <?> "simple expression"

    constant
      = either (Const . fromInteger) (Const . realToFrac) <$> naturalOrFloat

    table =
      [ [prefix "+" id] <>
        [prefix (showUnOp op) (UnOp op)
        |op <- sortBy (comparing $ Down . show) -- put "erfc" before "erf"
          [minBound..maxBound :: UnOp]]
      ]
      <> binops

    binops =
      reverse $ Map.elems $ Map.fromListWith (<>) $
      [ (prio, [binary (showBinOp op) (BinOp op) assoc])
      | op <- [minBound..maxBound]
      , let (assoc, _, _, prio) = fixity op ]
      <>
      [ let (assoc, _, _, prio) = tagFixity
        in
        (prio, [binary "@" tag assoc]) ]
    tag (Var i) e = Tag i e
    tag v _ = error "Expected a tag name before '@'"

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
genExpr goodExpr vars = filterGen goodExpr $ oneof
  [Var <$> elements (map fst vars)
  ,Const <$> arbitrary
  ,Tag <$> elements ["i","j","k"] <*> g
  ,BinOp <$> arbitrary <*> g <*> g
  ,UnOp  <$> filterGen diffUnOp arbitrary <*> g
  ]
  where
    g = genExpr goodExpr vars
    diffUnOp = \ case
      Abs -> False
      Signum -> False
      _ -> True

filterGen :: Monad m => (a -> Bool) -> m a -> m a
filterGen pred gen = do
  r <- gen
  if pred r then pure r else filterGen pred gen

goodSimplifyExpr :: Expr Double -> Bool
goodSimplifyExpr expr = ok (e expr) && case expr of
  BinOp Expt _ (Const b) -> abs b < 1e3
  BinOp Expt _ b -> abs (e b) < 1e3
    && abs (e b - (fromInteger $ round $ e b)) > eps
  -- (-1)**30.000000001 = NaN, so we either check constant exponents
  -- that have no jitter or exponents that are far enough from integers
  BinOp Divide _ b -> abs (e b) > eps
  UnOp op x
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
    filterGen goodDiffExpr (genExpr goodSimplifyExpr testVars)

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
