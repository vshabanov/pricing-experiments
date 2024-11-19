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
import Data.Maybe
import Data.String

data Expr
  = Var VarId
  | Const Rational
  | BinOp BinOp Expr Expr
  | UnOp UnOp Expr
  | NonDiff String -- ^ non-differentiable
  deriving (Eq, Ord)

var = Var

type VarId = String

data BinOp
  = Plus
  | Minus
  | Multiply
  | Divide
  | Expt -- ^ a**b
  deriving (Eq, Ord, Show)

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
  deriving (Eq, Ord, Show)

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

fixedPoint :: (Expr -> Expr) -> Expr -> Expr
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

  BinOp Divide a 1 -> a
  BinOp Divide (BinOp Expt a x) b | a == b -> a ** (x-1)

  BinOp Expt a 0 -> 1
  BinOp Expt a 1 -> a
  BinOp Expt (BinOp Expt a b) c -> BinOp Expt a (b+c)
  BinOp Expt (UnOp Exp x) y -> exp (x*y)

  UnOp Negate (UnOp Negate x) -> x
  UnOp Exp 0 -> 1
  UnOp Cos (UnOp Negate x) -> cos x
  UnOp Sin (UnOp Negate x) -> - sin x
  a -> a

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
    | denominator a == 1 -> show $ numerator a
    | otherwise          -> show a
  BinOp op a b -> parens [operand a, binOp op, operand b]
  UnOp op a -> parens [unOp op, showExpr False a]
  NonDiff s -> error $ "non-differentiable: " <> s
  where
    isBinOp = \ case
      BinOp{} -> True
      _ -> False
    operand x = showExpr (not $ isBinOp x) x
    parens (unwords -> x)
      | root = x
      | otherwise = "(" <> x <> ")"
    binOp = \ case
      Plus     -> "+"
      Minus    -> "-"
      Multiply -> "*"
      Divide   -> "/"
      Expt     -> "**"
    unOp = \ case
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

test =
  simplify $ diff (sin x ** cos (x)) x
x = Var "x"
