{-# LANGUAGE OverloadedLists #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}
-- | Symbolic differentiation
module Symbolic
  ( Expr
  , VarId
  , var
  , tag
  , lift
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
import qualified Control.Monad.State.Strict as S

import Control.Applicative ((<|>))
import Text.Parsec ((<?>))
import qualified Text.Parsec as P
import qualified Text.Parsec.Expr as P
import qualified Text.Parsec.Token as P
import qualified Text.Parsec.Language as P

import Test.QuickCheck
import N

data Expr a
  = Var VarId
    -- | Same as 'Var' but doesn't require lookup in 'eval'.
    -- It should simplify the connection of 'Expr' with AD variables.
    -- No need to invent variable names and maintain name-value mappings.
    -- We can then differentiate subexpressions symbolically while keeping
    -- AD value to have sensitivies to market inputs from the end results.
  | EmbeddedVar a
    -- | Named sub-expression that we can differentiate on.
    -- It can keep AD variables beneath.
  | Tag VarId (Expr a)
  | Const Rational
  | Pi
  | BinOp BinOp (Expr a) (Expr a)
  | UnOp UnOp (Expr a)
    -- | Non-differentiable
  | NonDiff String
  deriving (Eq, Ord)

var = Var
tag = Tag
lift = EmbeddedVar

type VarId = String

data BinOp
  = Plus
  | Minus
  | Multiply
  | Divide
  | Expt -- ^ a**b
--   | LogBase -- ^ logBase
  deriving (Eq, Ord, Enum, Bounded, Show)

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
  deriving (Eq, Ord, Enum, Bounded, Show)

eval :: Erf a => (VarId -> a) -> Expr a -> a
eval subst = \ case
  Var id -> subst id
  EmbeddedVar a -> a
  Tag _ x -> e x
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

diff :: Show a => Expr a -> Expr a -> Expr a
diff e v =
  -- always use 'simplify' as we get a lot of 0s, and we might have
  -- an invalid computation multiplied by 0 and get NaN where we shouldn't.
  -- E.g.:
  --   (- x) ** 1
  -- gives
  --   (- x) ** 1 * (log (- x) * 0 + 1 * (- 1) * 1 / (- x))
  -- where log (-1) is NaN but it's multiplied by 0 and not used in
  -- final computation
  simplify $ diffVar e $ case v of
    Var i   -> i
    Tag i _ -> i
    v -> error $ "Please use 'var' to differentiate instead of " <> show v

diffVar :: Expr a -> VarId -> Expr a
diffVar e i = case e of
  Var vi
    | vi == i   -> 1
    | otherwise -> 0
  EmbeddedVar _ -> 0
  Tag vi e
    | vi == i   -> 1
    | otherwise -> d e
  Const _ -> 0
  Pi -> 0
  BinOp op a b -> binOp op a b
  UnOp op a -> dUnOp op a * d a
  NonDiff s -> error $ "non-differentiable: " <> s
  where
    d x = diffVar x i
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
    sec x = 1 / cos x
    sech x = 1 / cosh x

------------------------------------------------------------------------------
-- Simplification

simplify :: Expr a -> Expr a
simplify e = feval Var (EmbeddedVar . (evars!)) Tag $ fsimp fe
  where
    (fe, evars) = factor e

fixedPoint :: Eq a => (a -> a) -> a -> a
fixedPoint f e
  | e' == e   = e
  | otherwise = fixedPoint f e'
  where
    e' = f e

data FExpr
  = FVar VarId
  | FEmbeddedVar Int
  | FTag VarId FExpr
  | FUnOp UnOp FExpr
  | FExpt FExpr FExpr
  | FSum Rational (Map FExpr Rational)
    -- ^ c0 + expr1*c1 + expr2*c2 ...
  | FProduct Rational (Map FExpr Integer)
    -- ^ c0 * expr1^c1 * expr2^c2 ...
  | FNonDiff String
  | FPi
  deriving (Eq, Ord)

fsimp = fixedPoint $ \ case
  FSum 0 [(e,1)] -> e
  FSum 0 [(FProduct c0 e,c)] -> FProduct (c0*toRational c) e
  FSum 0 [(FProduct p1 e1,1),(FProduct p2 e2,1)]
    | e1 == e2 -> FProduct (p1+p2) e1
  FSum c e -> uncurry FSum $ recurse (foldl' (+) c) flattenSum e
  FProduct 0 _ -> FProduct 0 mempty
  FProduct 1 [(e,1)] -> e
  FProduct c e -> uncurry FProduct $ recurse (foldl' (*) c) flattenProduct e
  FExpt a b
    | Just ca <- toConst a
    , Just cb <- toConst b
    , denominator cb == 1 -> FSum (ca ^^ numerator cb) []
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
  e@FEmbeddedVar{} -> e
  FTag i e -> FTag i (fsimp e)
  e@FNonDiff{} -> e
  e@FPi -> e
  where
    recurse
      :: (Eq a, Num a)
      => ([Rational] -> Rational) -- ^ fold constants
      -> ((FExpr, a) -> [Either Rational (FExpr, a)]) -- ^ constants or new expr
      -> Map FExpr a -- ^ exprs of FSum or FProduct
      -> (Rational, Map FExpr a) -- ^ new constant and exprs
    recurse fold flatten es = (fold consts, Map.fromListWith (+) nonConsts)
      where
        (consts, nonConsts)
          = partitionEithers $ concatMap flatten
          $ filter ((/= 0) . snd)
          $ Map.toList
          $ Map.fromListWith (+) [(fsimp e, c) | (e,c) <- Map.toList es]
    flattenSum :: (FExpr, Rational) -> [Either Rational (FExpr, Rational)]
    flattenSum = \ case
      (toConst -> Just x, c) -> [Left (x*c)]
      (FUnOp Negate x, c) -> [Right (x,-c)]
      (FProduct c0 [(x,1)], c) -> [Right (x,c0*c)]
      (FProduct c0 xs, c) | c0 /= 1 -> [Right (FProduct 1 xs,c0*c)]
      (FSum c0 es, c) ->
        Left (c0*c) : [Right (e, ce*c) | (e,ce) <- Map.toList es]
      e -> [Right e]
    flattenProduct :: (FExpr, Integer) -> [Either Rational (FExpr, Integer)]
    flattenProduct = \ case
      (toConst -> Just x, c) -> [Left (x^^c)]
      (FUnOp Sqrt (toConst -> Just x), 2)  | x >= 0 -> [Left x]
      (FUnOp Sqrt (toConst -> Just x), -2) | x > 0  -> [Left (1/x)]
      (FUnOp Sqrt FPi,  2) -> [Right (FPi, 1)]
      (FUnOp Sqrt FPi, -2) -> [Right (FPi,-1)]
      (FUnOp Negate x, c)
        | odd c -> [Left (-1), Right (x,c)]
        | otherwise -> [Right (x,c)]
      (FSum 0 [(x,sc)], c) ->
        [Left (sc^^c), Right (x,c)]
      (FProduct c0 es, c) ->
        Left (c0^^c) : [Right (e, ce*c) | (e,ce) <- Map.toList es]
      e -> [Right e]
    toConst = \ case
      FSum c [] -> Just c
      FProduct c [] -> Just c
      _ -> Nothing

feval
  :: Erf a
  => (VarId -> a) -- ^ 'FVar' to 'Var'
  -> (Int -> a)   -- ^ 'FEmbeddedVar' to 'EmbeddedVar'
  -> (VarId -> a -> a)  -- ^ 'FTag' to 'Tag'
  -> FExpr
  -> a
feval var embeddedVar tag = \ case
  FSum c0 ss -> case negativeLast ss of
    [] -> r c0
    (x:xs) -> mkSum c0 x xs
  FProduct c0 ps -> case negativeLast ps of
    [] -> r c0
    (x:xs) -> goProd (firstProd c0 x) xs
  FExpt a b -> e a ** e b
  FUnOp op x -> unOp op $ e x
  FVar i -> var i
  FEmbeddedVar i -> embeddedVar i
  FTag i x -> tag i (e x)
  FPi -> pi
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

    r :: Fractional a => Rational -> a
    r = fromRational
    e = feval var embeddedVar tag

factor :: Expr a -> (FExpr, Array Int a)
factor e = (fe, listArray (0,n-1) $ reverse embeddedVars)
  where
    (fe, (n, embeddedVars)) = S.runState (factorS e) (0, [])

factorS :: Expr a -> S.State (Int, [a]) FExpr
factorS = \ case
  Var i -> p $ FVar i
  EmbeddedVar e -> do
    (n, vs) <- S.get
    S.put (n+1, e:vs)
    p $ FEmbeddedVar n
  Tag i e -> FTag i <$> factorS e
  Const c -> p $ FSum c Map.empty
  Pi -> p FPi
  BinOp op a b -> do
    let m ca cb = do
          fa <- factorS a
          fb <- factorS b
          p $ Map.fromListWith (+) [(fa,ca), (fb,cb)]
    case op of
      Plus     -> FSum 0 <$> m 1 1
      Minus    -> FSum 0 <$> m 1 (-1)
      Multiply -> FProduct 1 <$> m 1 1
      Divide   -> FProduct 1 <$> m 1 (-1)
      Expt     -> liftM2 FExpt (factorS a) (factorS b)
  UnOp op e -> FUnOp op <$> factorS e
  NonDiff s -> p $ FNonDiff s
  where
    p = pure

------------------------------------------------------------------------------
-- Instances

instance IsString (Expr a) where
  fromString = parseExpr

instance Num (Expr a) where
  a + b = BinOp Plus a b
  a - b = BinOp Minus a b
  a * b = BinOp Multiply a b

  negate = UnOp Negate

  abs _ = NonDiff "abs"
  signum _ = NonDiff "signum"

  fromInteger = Const . fromInteger

instance Fractional (Expr a) where
  a / b = BinOp Divide a b

  fromRational = Const

instance Floating (Expr a) where
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

instance Erf (Expr a) where
  erf  = UnOp Erf
  erfc = UnOp Erfc

------------------------------------------------------------------------------
-- Show

data ShowExprMode
  = SEM_Haskell -- ^ Haskell-style, no parens in functions
  | SEM_Maxima  -- ^ suitable for copy-pasting into Maxima
  deriving (Eq, Show)

instance Show a => Show (Expr a) where
  showsPrec d e = (showExpr SEM_Haskell (False, P.AssocNone, d) e <>)

toMaxima :: Show a => Expr a -> String
toMaxima = filter (/= ' ') . showExpr SEM_Maxima (False, P.AssocNone, 0)

showExpr :: Show a => ShowExprMode -> (Bool, P.Assoc, Int) -> Expr a -> String
showExpr m p@(pNegate, pa, pp) = \ case
  Var n -> parensIf argParens [n]
  EmbeddedVar e -> parensIf argParens [show e]
  Tag n e ->
    if m == SEM_Maxima then
      showExpr m p e
    else
      let (a, p) = (P.AssocRight, 0)
      in
        parensIf (p < pp || (p == pp && diffAssoc a pa))
        [n,"@",showExpr m (False,a,p) e]
  Const a
    | n <- numerator a
    , d <- denominator a
    -> if d == 1 then parensIf (n < 0 || argParens) [show n]
       else showExpr m (False,pa,pp) (fromInteger n / fromInteger d :: Expr ())
       -- show like a division -1%2 -> (-1)/2, not (-1/2) as the second
       -- one will be parsed as a division and not as a rational constant
  Pi -> parensIf argParens [if m == SEM_Maxima then "%pi" else "pi"]
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

debugShowExpr :: Show a => Expr a -> String
debugShowExpr = \ case
  Var n -> "Var " <> show n
  EmbeddedVar v -> "EmbeddedVar " <> show v
  Tag t e -> mconcat ["Tag ", show t, " (", show e, ")"]
  Const a -> mconcat ["Const (", show a, ")"]
  Pi -> "Pi"
  BinOp op a b -> unwords ["BinOp", show op, go a, go b]
  UnOp op a -> unwords ["UnOp", show op, go a]
  NonDiff s -> "NonDiff " <> show s
  where
    go x = mconcat ["(", debugShowExpr x, ")"]

showBinOp = \ case
  Plus     -> "+"
  Minus    -> "-"
  Multiply -> "*"
  Divide   -> "/"
  Expt     -> "**"

showUnOp = \ case
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

instance Show FExpr where
  showsPrec d e = (showFExpr (d < 10) e <>)

showFExpr :: Bool -> FExpr -> String
showFExpr root = \ case
  FVar n -> n
  FEmbeddedVar i -> "EV" <> show i
  FTag n e -> n<>"@"<>showFExpr False e
  FSum c l ->
    parens "(Σ " ")" $ intercalate "+" $ showC c : showS (Map.toList l)
  FProduct c l ->
    parens "(Π " ")" $ intercalate "*" $ showC c : showP (Map.toList l)
  FUnOp op a -> parens "(" ")" $ unwords [show op, showFExpr False a]
  FNonDiff s -> show (NonDiff s :: Expr ())
  FExpt a b -> showFExpr False a <> "**" <> showFExpr False b
  FPi -> "pi"
  where
    showC x = show (Const x :: Expr ())
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
      <|> (Pi <$ reservedOp "pi")
      <|> (Var <$> identifier)
      <?> "simple expression"

    constant
      = either (Const . fromInteger) (Const . toRational) <$> naturalOrFloat

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
      [ (0, [binary "@" tag P.AssocRight]) ]
    tag (Var i) e = Tag i e
    tag v _ = error "Expected tag name before '@'"

    binary name fun assoc = P.Infix  (fun <$ reservedOp name) assoc
    prefix name fun       = P.Prefix (fun <$ reservedOp name)

    P.TokenParser{parens, identifier, naturalOrFloat, reservedOp, integer, decimal, lexeme}
      = P.makeTokenParser P.emptyDef
        { P.reservedOpNames =
            "pi" : "@" : map show [minBound..maxBound :: BinOp] }

------------------------------------------------------------------------------
-- Tests

testSymbolic = do
  r <- quickCheckWithResult (stdArgs{maxSuccess=5000000}) prop_diff
  unless (isSuccess r) exitFailure

quickCheckBig p = quickCheckWith (stdArgs{maxSuccess=10000}) p

instance Arbitrary UnOp where
  arbitrary = chooseEnum (minBound, maxBound)
instance Arbitrary BinOp where
  arbitrary = chooseEnum (minBound, maxBound)
instance Arbitrary (Expr Double) where
  arbitrary = genExpr testVars

testVars :: Floating a => [(VarId, a)]
testVars = [("a",1),("b",-1.5),("c",pi),("x",exp 1)]
testEval x = eval (\ v -> fromJust $ lookup v testVars) x
substTest x = eval (\ v -> Const $ toRational $ fromJust $ lookup v testVars) x

genExpr :: [(String, Double)] -> Gen (Expr Double)
genExpr vars = filterGen goodTestExpr $ oneof
  [Var <$> elements (map fst vars)
  ,EmbeddedVar <$> arbitrary
  ,Const <$> arbitrary
  ,pure Pi
  ,BinOp <$> arbitrary <*> genExpr vars <*> genExpr vars
  ,UnOp  <$> arbitrary <*> genExpr vars
  ]

filterGen :: Monad m => (a -> Bool) -> m a -> m a
filterGen pred gen = do
  r <- gen
  if pred r then pure r else filterGen pred gen

goodTestExpr :: Expr Double -> Bool
goodTestExpr expr = ok (e expr) && case expr of
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

newtype TestDiffExpr = TestDiffExpr (Expr Double)
instance Show TestDiffExpr where show (TestDiffExpr e) = show e
instance IsString TestDiffExpr where fromString = TestDiffExpr . fromString

instance Arbitrary TestDiffExpr where
  arbitrary = TestDiffExpr <$> filterGen goodDiffExpr arbitrary

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

prop_parse :: Expr () -> Bool
prop_parse x = e == parseExpr (show e)
  where
    -- need to 'show' first to normalize associativity,
    -- otherwise 'a*(b*c)*d' will not roundtrip as it will be showed
    -- as 'a*b*c*d'
    e = parseExpr (show x) :: Expr ()

prop_simplify x = counterexample debug $ eq_eps 1e-6 l r
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
