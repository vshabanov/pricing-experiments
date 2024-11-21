{-# OPTIONS_GHC -Wincomplete-patterns #-}
-- | Symbolic differentiation
module Symbolic
  ( Expr
  , var
  , eval
  , diff
  , simplify
  ) where

import Data.Number.Erf
import Data.Ratio
import Data.Either
import Data.Maybe
import Data.List
import Data.String
import Data.Map (Map)
import qualified Data.Map.Strict as Map

data Expr
  = Var VarId
  | Const Rational
  | BinOp BinOp Expr Expr
  | UnOp UnOp Expr
  | NonDiff String -- ^ non-differentiable
  deriving (Eq, Ord)

-- | 'Expr' factored into
var = Var

type VarId = String

data BinOp
  = Plus
  | Minus
  | Multiply
  | Divide
  | Expt -- ^ a**b
  deriving (Eq, Ord)

data UnOp
  = Negate
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
  | Erf
  | Erfc
  deriving (Eq, Ord)

eval :: Erf a => [(VarId, a)] -> Expr -> a
eval subst = \ case
  Var id -> fromMaybe (error $ "variable " <> id <> " not found")
    $ lookup id subst
  Const a -> fromRational a
  BinOp op a b -> binOp op (e a) (e b)
  UnOp op a -> unOp op (e a)
  NonDiff s -> error $ "non-differentiable: " <> s
  where
    e = eval subst
    binOp = \ case
      Plus     -> (+)
      Minus    -> (-)
      Multiply -> (*)
      Divide   -> (/)
      Expt     -> (**)
    unOp = \ case
      Negate -> negate
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

diff :: Expr -> Expr -> Expr
diff e v@(Var i) = case e of
  Var vi
    | vi == i   -> 1
    | otherwise -> 0
  Const a -> 0
  BinOp op a b -> binOp op a b
  UnOp op a -> dUnOp op a * d a
  NonDiff s -> error $ "non-differentiable: " <> s
  where
    d x = diff x v
    binOp op a b = case op of
      Plus     -> d a + d b
      Minus    -> d a - d b
      Multiply -> d a * b + a * d b
      Divide   -> (d a * b - a * d b) / b^2
      Expt     -> a**b * (log a * d b + b * d a / a)
    dUnOp op x = case op of
      Negate -> -1
      Exp    -> exp x
      Log    -> log x
      Sqrt   -> 1 / (2 * sqrt x)
      Sin    -> cos x
      Cos    -> - sin x
      Tan    -> sec x ^ 2
      ASin   -> 1 / sqrt (1 - x^2)
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
    sec x = 1 / cos x
    sech x = 1 / cosh x
diff e v = error $ "Please use var to differentiate instead of " <> show v

------------------------------------------------------------------------------
-- Simplification

fixedPoint :: Eq a => (a -> a) -> a -> a
fixedPoint f e
  | e' == e   = e
  | otherwise = fixedPoint f e'
  where
    e' = f e

-- extremely inefficient, and probably wrong (needs QuickCheck)
-- may also loop somewhere
-- and of course incomplete
simplify :: Expr -> Expr
simplify = fixedPoint $ \ e -> case e of
  BinOp op a b
    | sa <- simplify a
    , sb <- simplify b
    , sa /= a || sb /= b -> BinOp op sa sb
  UnOp op a
    | sa <- simplify a
    , sa /= a -> UnOp op sa

  BinOp op (Const a) (Const b) -> case op of
    Plus     -> Const $ a + b
    Minus    -> Const $ a - b
    Multiply -> Const $ a * b
    Divide   -> Const $ a / b
    Expt
      | denominator b == 1 -> Const $ a ^ numerator b
      | otherwise          -> e

  BinOp Plus a b@Const{} -> b + a
  BinOp Plus 0 a -> a
  BinOp Plus (UnOp Negate a) (UnOp Negate b) -> - (a + b)
  BinOp Plus (UnOp Negate a) b -> b - a
  BinOp Plus a (UnOp Negate b) -> a - b
  BinOp Plus (BinOp Multiply a1 a2) (BinOp Multiply b1 b2)
    | a2 == b2 -> (a1+b1) * a2
  BinOp Plus (BinOp Multiply x a) b | a == b -> (x+1) * a
  BinOp Plus a@Const{} (BinOp Plus b@Const{} c) -> (a+b)*c
  BinOp Plus a (BinOp Plus b@Const{} c) -> b+(a+c)
  BinOp Plus (BinOp Plus a b) c -> a + (b + c)
  BinOp Plus a b | a == b -> BinOp Multiply 2 a

  BinOp Minus 0 a -> UnOp Negate a
  BinOp Minus a 0 -> a
  BinOp Minus (UnOp Negate a) (UnOp Negate b) -> b - a
  BinOp Minus (UnOp Negate a) b -> - (a + b)
  BinOp Minus a (UnOp Negate b) -> a + b
  BinOp Minus a b | a == b -> 0

  BinOp Multiply a b@Const{} -> b * a
  BinOp Multiply 0 _ -> 0
  BinOp Multiply 1 a -> a
  BinOp Multiply a@Const{} (BinOp Multiply b@Const{} c) -> (a*b)*c
  BinOp Multiply (BinOp Multiply a b) c -> a * (b * c)
  BinOp Multiply a (BinOp Multiply c@Const{} b) -> c * (a * b)
  BinOp Multiply a (BinOp Divide c@Const{} b) -> c * (a / b)
  BinOp Multiply (UnOp Negate a) (UnOp Negate b) -> a * b
  BinOp Multiply (UnOp Negate a) b -> - (a * b)
  BinOp Multiply a (UnOp Negate b) -> - (a * b)
  BinOp Multiply (BinOp Expt a x) (BinOp Expt b y) | a == b -> a ** (x+y)
  BinOp Multiply (BinOp Expt a x) b | a == b -> a ** (x+1)
  BinOp Multiply a (BinOp Expt b x) | a == b -> a ** (x+1)
  BinOp Multiply (UnOp Exp a) (UnOp Exp b) -> exp (a+b)
  BinOp Multiply a b | a == b -> BinOp Expt a 2

  BinOp Divide 0 _ -> 0
  BinOp Divide a 1 -> a
  BinOp Divide a (Const b) -> Const (1/b) * a
  BinOp Divide (BinOp Expt a x) b | a == b -> a ** (x-1)

  BinOp Expt a 0 -> 1
  BinOp Expt a 1 -> a
  BinOp Expt (BinOp Expt a b) c -> BinOp Expt a (b+c)
  BinOp Expt (UnOp Exp x) y -> exp (x*y)
  BinOp Expt (UnOp Sqrt x) 2 -> x

  UnOp Negate (UnOp Negate x) -> x
  UnOp Exp 0 -> 1
  UnOp Cos (UnOp Negate x) -> cos x
  UnOp Sin (UnOp Negate x) -> - sin x
  a -> a

data FactoredExpr
  = FVar VarId
  | FUnOp UnOp FactoredExpr
  | FExpr FactoredExpr FactoredExpr
  | Sum Rational (Map FactoredExpr Rational)
    -- ^ c0 + expr1*c1 + expr2*c2 ...
  | Product Rational (Map FactoredExpr Rational)
    -- ^ c0 * expr1^c1 * expr2^c2 ...
  | FNonDiff String
  deriving (Eq, Ord)

fsimp = fixedPoint $ \ case
  Sum 0 [(e,1)] -> e
  Sum 0 [(Product c0 e,c)] -> Product (c0*c) e
  Sum c e -> uncurry Sum $ recurse (foldl' (+) c) sumConst e
  Product 0 _ -> Product 0 mempty
  Product 1 [(e,1)] -> e
  Product c e -> uncurry Product $ recurse (foldl' (*) c) productConst e
  FExpr a b
    | Just ca <- toConst a
    , Just cb <- toConst b
    , denominator cb == 1 -> Sum (ca ^^ numerator cb) []
    | otherwise -> FExpr (fsimp a) (fsimp b)
  FUnOp Negate (Product c es) -> Product (-c) es
  FUnOp Negate (Sum c es) -> Sum (-c) $ Map.map negate es
  FUnOp Negate (FUnOp Negate e) -> e
  FUnOp op e -> FUnOp op (fsimp e)
  e@FVar{} -> e
  e@FNonDiff{} -> e
  where
    recurse fold getConst es = (fold consts, Map.fromListWith (+) nonConsts)
      where
        (consts, nonConsts)
          = partitionEithers $ concatMap getConst
          $ filter ((/= 0) . snd)
          $ Map.toList
          $ Map.fromListWith (+) [(fsimp e, c) | (e,c) <- Map.toList es]
    sumConst = \ case
      (toConst -> Just x, c) -> [Left (x*c)]
      (Sum c0 es, c) ->
        Left (c0*c) : [Right (e, ce*c) | (e,ce) <- Map.toList es]
      e -> [Right e]
    productConst = \ case
      (toConst -> Just x, c) | denominator c == 1 -> [Left (x^^numerator c)]
      (FUnOp Sqrt (toConst -> Just x), 2) -> [Left x]
      (FUnOp Sqrt (toConst -> Just x), -2) -> [Left (1/x)]
      (Product c0 es, c) | denominator c == 1 ->
        Left (c0^^numerator c) : [Right (e, ce*c) | (e,ce) <- Map.toList es]
      (Product 1 es, c) -> [Right (e, ce*c) | (e,ce) <- Map.toList es]
      e -> [Right e]
    toConst = \ case
      Sum c [] -> Just c
      Product c [] -> Just c
      _ -> Nothing

factor = \ case
  Var i -> FVar i
  Const c -> Sum c Map.empty
  BinOp op a b ->
    let m ca cb = Map.fromListWith (+) [(factor a,ca), (factor b,cb)] in
    case op of
      Plus     -> Sum 0 $ m 1 1
      Minus    -> Sum 0 $ m 1 (-1)
      Multiply -> Product 1 $ m 1 1
      Divide   -> Product 1 $ m 1 (-1)
      Expt
        | Const y <- b -> expt a y
        | otherwise    -> FExpr (factor a) (factor b)
  UnOp op e -> FUnOp op $ factor e
  NonDiff s -> FNonDiff s
  where
    expt x y = Product 1 $ Map.singleton (factor x) y

------------------------------------------------------------------------------
-- Instances

instance IsString Expr where
  fromString = Var

instance Num Expr where
  a + b = BinOp Plus a b
  a - b = BinOp Minus a b
  a * b = BinOp Multiply a b

  negate = UnOp Negate

  abs _ = NonDiff "abs"
  signum _ = NonDiff "signum"

  fromInteger = Const . fromInteger

instance Fractional Expr where
  a / b = BinOp Divide a b

  fromRational = Const

instance Floating Expr where
  pi    = Const $ toRational pi
  exp   = UnOp Exp
  log   = UnOp Log
  sqrt  = UnOp Sqrt

  a ** b = BinOp Expt a b

  -- logBase x y  = log y / log x
  sin   = UnOp Sin
  cos   = UnOp Cos
  tan   = UnOp Tan
  asin  = UnOp ASin
  acos  = UnOp ACos
  atan  = UnOp ATan
  sinh  = UnOp Sinh
  cosh  = UnOp Cosh
  tanh  = UnOp Tanh
  asinh = UnOp ASinh
  acosh = UnOp ACosh
  atanh = UnOp ATanh

instance Erf Expr where
  erf  = UnOp Erf
  erfc = UnOp Erfc

instance Show Expr where
  showsPrec d e = (showExpr (d < 10) e <>)

showExpr :: Bool -> Expr -> String
showExpr root = \ case
  Var n -> n
  Const a
    | a == toRational pi -> "pi"
    | denominator a == 1 -> show $ numerator a
    | otherwise          -> show a
  BinOp op a b -> parens [operand a, show op, operand b]
  UnOp op a -> parens [show op, showExpr False a]
  NonDiff s -> error $ "non-differentiable: " <> s
  where
    isBinOp = \ case
      BinOp{} -> True
      _ -> False
    operand x = showExpr (not $ isBinOp x) x
    parens (unwords -> x)
      | root = x
      | otherwise = "(" <> x <> ")"

instance Show BinOp where
  show = \ case
    Plus     -> "+"
    Minus    -> "-"
    Multiply -> "*"
    Divide   -> "/"
    Expt     -> "**"

instance Show UnOp where
  show = \ case
    Negate -> "-"
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

-- deriving instance Show FactoredExpr
instance Show FactoredExpr where
  showsPrec d e = (showFExpr (d < 10) e <>)

showFExpr :: Bool -> FactoredExpr -> String
showFExpr root = \ case
  FVar n -> n
  Sum c l ->
    parens "(Σ " ")" $ intercalate "+" $ showC c : showS (Map.toList l)
  Product c l ->
    parens "(Π " ")" $ intercalate "*" $ showC c : showP (Map.toList l)
  FUnOp op a -> parens "(" ")" $ unwords [show op, showFExpr False a]
  FNonDiff s -> showExpr root (NonDiff s)
  FExpr a b -> showFExpr False a <> "**" <> showFExpr False b
  where
    showC x = showExpr root (Const x)
    showS = map $ \ case
      (e,1) -> showFExpr False e
      (e,c) -> showC c <> "*" <> showFExpr False e
    showP = map $ \ case
      (e,1) -> showFExpr False e
      (e,c) -> showFExpr False e <> "^" <> showC c
    isBinOp = \ case
      BinOp{} -> True
      _ -> False
    operand x = showExpr (not $ isBinOp x) x
    parens o c x
--      | root = x
      | otherwise = o <> x <> c

test =
  simplify $ diff (sin x ** cos (x)) x
x = Var "x"
