-- | Symbolic differentiation
module Symbolic
  ( Expr
  , eval
  , var
  , diff
  , simplify
  ) where

data Expr a
  = Var String a -- ^ id
  | Const a
  | BinOp BinOp (Expr a) (Expr a)
  | UnOp UnOp (Expr a)
  | NonDiff String -- ^ non-differentiable
  deriving (Eq, Ord)

var = Var

instance Show a => Show (Expr a) where
  showsPrec d e = (showExpr (d < 10) e <>)

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
  deriving (Eq, Ord, Show)

eval :: (Num a, Fractional a, Floating a) => Expr a -> a
eval = \ case
  Var _ a -> a
  Const a -> a
  BinOp op a b -> binOp op (eval a) (eval b)
  UnOp op a -> unOp op (eval a)
  NonDiff s -> error $ "non-differentiable: " <> s
  where
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

showExpr :: Show a => Bool -> Expr a -> String
showExpr root = \ case
  Var n a -> n -- <> "[=" <> show a <> "]"
  Const a -> show a
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

sec x = 1 / cos x
sech x = 1 / cosh x

simplify :: (Num a, Eq a) => Expr a -> Expr a
simplify = \ case
  BinOp Plus a (Const 0) -> simplify a
  BinOp Plus (Const 0) a -> simplify a
  BinOp Multiply _ (Const 0) -> Const 0
  BinOp Multiply (Const 0) _ -> Const 0
  BinOp Multiply a (Const 1) -> simplify a
  BinOp Multiply (Const 1) a -> simplify a
  BinOp Multiply (UnOp Negate a) b ->
    simplify $ UnOp Negate $ BinOp Multiply a b
  BinOp Multiply a (UnOp Negate b) ->
    simplify $ UnOp Negate $ BinOp Multiply a b
  BinOp Multiply (Const (-1)) b -> simplify $ UnOp Negate b
  BinOp Multiply a (Const (-1)) -> simplify $ UnOp Negate a
  BinOp op a b ->
    let sa = simplify a -- should be trySimplify to remove equality checks
        sb = simplify b
    in
      if sa == a && sb == b then BinOp op a b
      else simplify $ BinOp op sa sb
  UnOp Negate (UnOp Negate x) -> simplify x
  UnOp Cos (UnOp Negate x) -> simplify $ UnOp Cos x
  UnOp Sin (UnOp Negate x) -> simplify $ UnOp Negate (UnOp Sin x)
  UnOp op a ->
    let sa = simplify a
    in
      if sa == a then UnOp op a else simplify (UnOp op sa)
  a -> a


diff :: (Num a, Fractional a, Floating a) => Expr a -> Expr a -> Expr a
diff e v@(Var i _) = case e of
  Var vi _
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

instance Num a => Num (Expr a) where
  a + b = BinOp Plus a b
  a - b = BinOp Minus a b
  a * b = BinOp Multiply a b

  negate = UnOp Negate

  abs _ = NonDiff "abs"
  signum _ = NonDiff "signum"

  fromInteger = Const . fromInteger

instance Fractional a => Fractional (Expr a) where
  a / b = BinOp Divide a b

  fromRational = Const . fromRational

instance Floating a => Floating (Expr a) where
  pi        = Const pi
  exp a     = UnOp Exp a
  log a     = UnOp Log a
  sqrt a    = UnOp Sqrt a

  a ** b    = BinOp Expt a b

  -- logBase x y  = log y / log x
  sin a     = UnOp Sin a
  cos a     = UnOp Cos a
  tan a     = UnOp Tan a
  asin a    = UnOp ASin a
  acos a    = UnOp ACos a
  atan a    = UnOp ATan a
  sinh a    = UnOp Sinh a
  cosh a    = UnOp Cosh a
  tanh a    = UnOp Tanh a
  asinh a   = UnOp ASinh a
  acosh a   = UnOp ACosh a
  atanh a   = UnOp ATanh a

test =
  simplify $ diff (sin x ** cos (x)) x
x = Var "x" 1.0
