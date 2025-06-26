{-# LANGUAGE TemplateHaskell #-}
module Main (main) where

import Control.Monad
import Data.Maybe
import Data.String
import Number
import StructuralComparison
import Symbolic
import Symbolic.Internal
import System.Exit
import Test.QuickCheck

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

prop_diff (TestDiffExpr e) = counterexample debug $ eq_eps 1e-4 n s
  where
    debug = unlines
      ["Expr:"
      ,toHaskell e
      ,"Diff:"
      ,toHaskell d
      ,"Diff simplified:"
      ,toHaskell ds
      ,"numeric  = " <> show n
      ,"symbolic = " <> show s]
    d = diffVar e "x"
    ds = simplify d
    n = numDiff e
    s = testEval ds

prop_parse :: Expr Double -> Property
prop_parse x = counterexample debug $ e `structuralEq` fromString (toHaskell e)
  where
    debug = unlines
      ["Debug Expr:"
      ,show x]
    -- need 'toHaskell' first to normalize associativity,
    -- otherwise 'a*(b*c)*d' will not roundtrip as it will be showed
    -- as 'a*b*c*d'
    e = fromString (toHaskell x) :: Expr Double

prop_simplify (TestSimplifyExpr x) = counterexample debug $ eq_eps 1e-6 l r
  where
    debug = unlines
      ["Expr:"
      ,show x
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

main = do
  ok <- $forAllProperties $
    quickCheckWithResult (stdArgs {maxSuccess = 1_000_000})
  when (not ok) exitFailure
