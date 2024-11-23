{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}
-- | Symbolic differentiation
module Symbolic
  ( Expr
  , var
  , eval
  , diff
  , simplify
  , fsimplify
  , toMaxima
  ) where

import Data.Number.Erf
import Data.Ord
import Data.Ratio
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

data Expr
  = Var VarId
  | Const Rational
  | Pi
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
--   | LogBase -- ^ logBase
  deriving (Eq, Ord, Enum, Bounded)

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
--     log1p x = log (1 + x)
--     expm1 x = exp x - 1
--     log1pexp x = log1p (exp x)
--     log1mexp x = log1p (negate (exp x))
  | Erf
  | Erfc
  deriving (Eq, Ord, Enum, Bounded)

eval :: Erf a => (VarId -> a) -> Expr -> a
eval subst = \ case
  Var id -> subst id
--     fromMaybe (error $ "variable " <> id <> " not found")
--     $ lookup id subst
  Const a -> fromRational a
  Pi -> pi
  BinOp op a b -> binOp op (e a) (e b)
  UnOp op a -> unOp op (e a)
  NonDiff s -> error $ "non-differentiable: " <> s
  where
    e = eval subst

binOp :: Erf a => BinOp -> (a -> a -> a)
binOp = \ case
  Plus     -> (+)
  Minus    -> (-)
  Multiply -> (*)
  Divide   -> (/)
  Expt     -> (**)

unOp :: Erf a => UnOp -> (a -> a)
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
  Pi -> 0
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
      Log    -> 1 / x
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
      | denominator b == 1 -> Const $ a ^^ numerator b
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
  | FExpt FactoredExpr FactoredExpr
  | Sum Rational (Map FactoredExpr Rational)
    -- ^ c0 + expr1*c1 + expr2*c2 ...
  | Product Rational (Map FactoredExpr Rational)
    -- ^ c0 * expr1^c1 * expr2^c2 ...
  | FNonDiff String
  | FPi
  deriving (Eq, Ord)

fsimp = fixedPoint $ \ case
  Sum 0 [(e,1)] -> e
  Sum 0 [(Product c0 e,c)] -> Product (c0*c) e
  Sum 0 [(Product p1 e1,1),(Product p2 e2,1)]
    | e1 == e2 -> Product (p1+p2) e1
  Sum c e -> uncurry Sum $ recurse (foldl' (+) c) sumConst e
  Product 0 _ -> Product 0 mempty
  Product 1 [(e,1)] -> e
  Product c e -> uncurry Product $ recurse (foldl' (*) c) productConst e
  FExpt a b
    | Just ca <- toConst a
    , Just cb <- toConst b
    , denominator cb == 1 -> Sum (ca ^^ numerator cb) []
    | otherwise -> FExpt (fsimp a) (fsimp b)
  FUnOp Negate (Product c es) -> Product (-c) es
  FUnOp Negate (Sum c es) -> Sum (-c) $ Map.map negate es
  FUnOp Negate (FUnOp Negate e) -> e
  FUnOp op e -> FUnOp op (fsimp e)
  e@FVar{} -> e
  e@FNonDiff{} -> e
  e@FPi -> e
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
      (FUnOp Negate x, c) -> [Right (x,-c)]
      (Product c0 [(x,1)], c) -> [Right (x,c0*c)]
      (Product c0 xs, c) | c0 /= 1 -> [Right (Product 1 xs,c0*c)]
      (Sum c0 es, c) ->
        Left (c0*c) : [Right (e, ce*c) | (e,ce) <- Map.toList es]
      e -> [Right e]
    productConst = \ case
      (toConst -> Just x, c) | denominator c == 1 -> [Left (x^^numerator c)]
      (FUnOp Sqrt (toConst -> Just x), 2) -> [Left x]
      (FUnOp Sqrt (toConst -> Just x), -2) -> [Left (1/x)]
      (FUnOp Negate x, 1) -> [Left (-1), Right (x,1)]
      (Sum 0 [(x,sc)], c) | denominator c == 1 ->
        [Left (sc^^numerator c), Right (x,c)]
      (Product c0 es, c) | denominator c == 1 ->
        Left (c0^^numerator c) : [Right (e, ce*c) | (e,ce) <- Map.toList es]
      (Product 1 es, c) -> [Right (e, ce*c) | (e,ce) <- Map.toList es]
      e -> [Right e]
    toConst = \ case
      Sum c [] -> Just c
      Product c [] -> Just c
      _ -> Nothing

fsimplify = feval Var . fsimp . factor

feval :: Erf a => (VarId -> a) -> FactoredExpr -> a
feval v = \ case
  Sum c0 [] -> r c0
--   Sum 0 [(a,1),(b,-1)] -> e a - e b
--   Sum 0 [(a,-1),(b,1)] -> e b - e a
  Sum c0 xs -> foldr1 (+) $ (if c0 /= 0 then (r c0:) else id)
    [(if c /= 1 then (r c*) else id) $ e x | (x,c) <- Map.toList xs]
  Product c0 [] -> r c0
--   Product 1 [(a,1),(b,-1)] -> e a / e b
--   Product 1 [(a,-1),(b,1)] -> e b / e a
  Product c0 xs -> foldr1 (*) $ (if c0 /= 1 then (r c0:) else id)
    [(if c /= 1 then (** r c) else id) $ e x | (x,c) <- Map.toList xs]
  FExpt a b -> e a ** e b
  FUnOp op x -> unOp op $ e x
  FVar i -> v i
  FPi -> pi
  FNonDiff s -> eval (error "var in NonDiff?") (NonDiff s)
  where
    r = fromRational
    e = feval v

factor = \ case
  Var i -> FVar i
  Const c -> Sum c Map.empty
  Pi -> FPi
  BinOp op a b ->
    let m ca cb = Map.fromListWith (+) [(factor a,ca), (factor b,cb)] in
    case op of
      Plus     -> Sum 0 $ m 1 1
      Minus    -> Sum 0 $ m 1 (-1)
      Multiply -> Product 1 $ m 1 1
      Divide   -> Product 1 $ m 1 (-1)
      Expt
        | Const y <- b -> expt a y
        | otherwise    -> FExpt (factor a) (factor b)
  UnOp op e -> FUnOp op $ factor e
  NonDiff s -> FNonDiff s
  where
    expt x y = Product 1 $ Map.singleton (factor x) y

------------------------------------------------------------------------------
-- Instances

instance IsString Expr where
  fromString = parseExpr

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
  pi    = Pi
  exp   = UnOp Exp
  log   = UnOp Log
  sqrt  = UnOp Sqrt

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

  (**) = BinOp Expt
--   logBase = BinOp LogBase


--     log1p x = log (1 + x)
--     expm1 x = exp x - 1
--     log1pexp x = log1p (exp x)
--     log1mexp x = log1p (negate (exp x))

instance Erf Expr where
  erf  = UnOp Erf
  erfc = UnOp Erfc

------------------------------------------------------------------------------
-- Show

data ShowExprMode
  = SEM_Haskell -- ^ Haskell-style, no parens in functions
  | SEM_Maxima  -- ^ suitable for copy-pasting into Maxima
  deriving (Eq, Show)

instance Show Expr where
  showsPrec d e = (showExpr SEM_Haskell (False, P.AssocNone, d) e <>)

toMaxima = filter (/= ' ') . showExpr SEM_Maxima (False, P.AssocNone, 0)

showExpr :: ShowExprMode -> (Bool, P.Assoc, Int) -> Expr -> String
showExpr m (pNegate, pa, pp) = \ case
  Var n -> parensIf argParens [n]
  Const a
    | n <- numerator a
    , d <- denominator a
    -> if d == 1 then parensIf (n < 0 || argParens) [show n]
       else showExpr m (False,pa,pp) (fromInteger n / fromInteger d)
       -- show like a division -1%2 -> (-1)/2, not (-1/2) as the second
       -- one will be parsed as a division and not as a rational constant
  Pi -> parensIf argParens [if m == SEM_Maxima then "%pi" else "pi"]
  BinOp op l r ->
    let (a, aLeft, aRight, p) = fixity op
    in
      parensIf (p < pp || (p == pp && diffAssoc a pa))
        [showExpr m (False,aLeft,p) l, show op, showExpr m (False,aRight,p) r]
  UnOp op a ->
    let f@(_, _, p) = (op == Negate, P.AssocNone, 10)
    in
      parensIf (p <= pp || (op == Negate && pp > 0)) [show op, showExpr m f a]
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

debugShowExpr :: Expr -> String
debugShowExpr = \ case
  Var n -> "Var " <> show n
  Const a -> mconcat ["Const (", show a, ")"]
  Pi -> "Pi"
  BinOp op a b -> unwords ["BinOp", show op, go a, go b]
  UnOp op a -> unwords ["UnOp", show op, go a]
  NonDiff s -> "NonDiff " <> show s
  where
    go x = mconcat ["(", debugShowExpr x, ")"]

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
  FNonDiff s -> show (NonDiff s)
  FExpt a b -> showFExpr False a <> "**" <> showFExpr False b
  FPi -> "pi"
  where
    showC x = show (Const x)
    showS = map $ \ case
      (e,1) -> showFExpr False e
      (e,c) -> showC c <> "*" <> showFExpr False e
    showP = map $ \ case
      (e,1) -> showFExpr False e
      (e,c) -> showFExpr False e <> "^" <> showC c
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
  Plus     -> (P.AssocLeft , P.AssocLeft, P.AssocLeft , 6)
  Minus    -> (P.AssocLeft , P.AssocLeft, P.AssocNone , 6)
  Multiply -> (P.AssocLeft , P.AssocLeft, P.AssocLeft , 7)
  Divide   -> (P.AssocLeft , P.AssocLeft, P.AssocNone , 7)
  Expt     -> (P.AssocRight, P.AssocNone, P.AssocRight, 8)

parseExpr s = either (error . show) id $ P.parse (expr <* P.eof) s s
  where
    expr = P.buildExpressionParser table term <?> "expression"

    term
      =   parens expr
      <|> constant
      <|> (Var <$> identifier)
      <?> "simple expression"

    constant
      = either (Const . fromInteger) (Const . toRational) <$> naturalOrFloat

    table =
      [ [prefix "+" id] <>
        [prefix (show op) (UnOp op)
        |op <- sortBy (comparing $ Down . show) -- put "erfc" before "erf"
          [minBound..maxBound :: UnOp]]
      ]
      <> binops

    binops =
      reverse $ Map.elems $ Map.fromListWith (<>)
      [ (prio, [binary (show op) (BinOp op) assoc])
      | op <- [minBound..maxBound]
      , let (assoc, _, _, prio) = fixity op ]

    binary name fun assoc = P.Infix (reservedOp name >> pure fun) assoc
    prefix name fun       = P.Prefix (reservedOp name >> pure fun)

    P.TokenParser{parens, identifier, naturalOrFloat, reservedOp, integer, decimal, lexeme}
      = P.makeTokenParser P.emptyDef
        { P.reservedOpNames = map show [minBound..maxBound :: BinOp] }

test =
  simplify $ diff (sin x ** cos (x)) x
x = Var "x"


------------------------------------------------------------------------------
-- Tests

instance Arbitrary UnOp where
  arbitrary = chooseEnum (minBound, maxBound)
instance Arbitrary BinOp where
  arbitrary = chooseEnum (minBound, maxBound)
instance Arbitrary Expr where
  arbitrary = genExpr testVars

testVars = ["a","b","c","x"]

genExpr :: [String] -> Gen Expr
genExpr vars = oneof
  [Var <$> elements vars
  ,Const <$> arbitrary --  . fromInteger <$> choose (0,100)
  ,pure Pi
  ,BinOp <$> arbitrary <*> genExpr vars <*> genExpr vars
  ,UnOp  <$> arbitrary <*> genExpr vars
  ]

quickCheckBig p = quickCheckWith (stdArgs{maxSuccess=10000}) p

prop_parse :: Expr -> Bool
prop_parse x = e == parseExpr (show e)
  where
    -- need to 'show' first to normalize associativity,
    -- otherwise 'a*(b*c)*d' will not roundtrip as it will be showed
    -- as 'a*b*c*d'
    e = parseExpr (show x)

prop_fsimp x = e x `eq` e (fsimplify x)
  where
    e = eval (const (1::Double))
    eq a b
      | isNaN a = isNaN b
      | isInfinite a = isInfinite b
      | otherwise = a == b
        || (b /= 0 && abs (a-b)/b < 1e-10)
        || (b == 0 && abs a < 1e-10)
{-
check the same with diff and AD
λ> let e = BinOp Expt (BinOp Expt (UnOp ACos (Const (0 % 1))) (Const ((-3) % 2))) (Var "a")
λ> eval (const 1) $ fsimplify e
0.5079490874739278
λ> eval (const 1) $ simplify e
0.7978845608028654
λ> eval (const 1) $ e
0.5079490874739278

filter:
* sin of large numbers
* neg sqrt, expt
* div by zero
UnOp Sin (BinOp Expt (BinOp Minus (Const ((-61) % 8)) (Const ((-221) % 18))) (Const (17 % 1)))
-}
