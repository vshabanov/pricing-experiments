{-# LANGUAGE UndecidableInstances #-}
--  ^ for Reifies s RD.Tape => N (RD.ReverseDouble s)
{-# OPTIONS_GHC -Wincomplete-patterns -O2 #-}
module Number where

import Data.Array
import Control.DeepSeq
import Data.Number.Erf
import Data.Reflection
import qualified Numeric.AD.Mode as R
import qualified Numeric.AD.Mode.Reverse as R
import qualified Numeric.AD.Mode.Reverse.Double as RD
import qualified Numeric.AD.Internal.Reverse.Double as RD
import qualified Numeric.AD.Internal.Reverse as R
import qualified Numeric.AD.Jacobian as J
import GHC.TypeError
import StructuralComparison

instance NFData (R.Reverse s a) where
  rnf a = seq a ()

deriving instance N a => N (SCmp a)

-- | extended Num functions
class (NFData a, Show a, Erf a, InvErf a, Ord a, StructuralOrd a) => N a where
  exprType :: a -> String

  step :: a -> a
--   step = (\x -> if x > 0 then 1 else 0)
  step x = 1 / (1 + exp (-k*x))
--   step x = k*x / sqrt (1+(k*x)^2) / 2 + 0.5 -- w=0.3 still bad
-- step x = if x > 0 then 1 else 0 -- по-сути, обнуляет производные
-- step x = if x > 0 then 1 else 0
-- step :: (R.Jacobian t, Ord (AD.Scalar t)) => t -> t
-- step x = R.lift1 (\ x -> if x > 0 then 1 else 0) (const 0) x
-- step x = (x + abs x) / (2*x)
-- step x = R.diff (max 0) x -- derivative of the ramp function

  partials :: a -> [Double]
  partials _ = []

  toD :: a -> Double
  toN :: Double -> a

  explicitD
    :: [a]             -- ^ variables
    -> [(a, Int)]      -- ^ jacobian [(∂x/∂var, var)]
    -> [(a, Int, Int)] -- ^ hessian  [(∂x/(∂var1*∂var2), var1, var2)]
    -> a               -- ^ value
    -> a

  dLevel :: a -> DLevel

  isZero :: a -> Bool
--   isZero = structuralEq 0
  isOne :: a -> Bool
--   isOne = structuralEq 1

  -- | @if_ LT a b then else@
  if_ :: Ordering -> a -> a -> a -> a -> a

data DLevel
  = DLNone  -- ^ can't be differentiated, 'explicitD' is no-op
  | DL1st   -- ^ can have 1st order derivative, 'explicitD' only honors jacobian
  | DLAny   -- ^ can have derivatives of any order
  deriving (Eq, Ord, Show)

intToN :: N a => Int -> a
intToN = toN . toEnum

width = 0.0001 -- NaN with 0.01, larger error with 0.1 or 1
                -- but for 'integrated' 0.1 gives good result
--     width = 0.000001  -- gives 0.00004 = 1 (half pip)
                      --      -0.00004 ~ 4e-18
    -- k=10 дает плавный переход от -0.5 до 0.5?
k, width :: Erf a => a
k = 1/width -- steepness

instance N Double where
  exprType _ = "Double"
  toN = id
  toD = id
  partials _ = []
  explicitD _ _ _ = id
  dLevel _ = DLNone
  isZero = (== 0)
  isOne  = (== 1)
  if_ o a b t e
    | compare a b == o = t
    | otherwise        = e
instance (Reifies s R.Tape, N a) => N (R.Reverse s a) where
  exprType _ = "R.Reverse s (" <> exprType (undefined :: a) <> ")"
  step = J.lift1 step
  -- Dirac delta is not much better
--     (\ x -> 1 / realToFrac (abs a * sqrt pi) * exp (-(x / realToFrac a)^2))
--     where a = 0.1 -- lower values lead to bigger error until it breaks at ~0.001
    (\ x -> k / (exp (k*x) + exp (-k*x) + 2))
  -- no NaN this way, but error grows for width<0.1, and breaks at 0.0003
-- 1000 / (exp 1000 + exp (-1000) + 2)
  explicitD vars jacobian _hessian base =
    base
    +
    sum [J.lift1 (const 0) (const $ R.auto (R.primal d)) (va ! var)
        | (d, var) <- jacobian]
    where
      va = listArray (0, length vars-1) vars
  partials = map toD . R.partials
  toN = R.auto . toN
  toD = toD . R.primal
  dLevel _ = DL1st

  isZero = \ case
    R.Zero -> True
    R.Lift x -> isZero x
    R.Reverse{} -> False
  isOne = \ case
    R.Zero -> False
    R.Lift x -> isOne x
    R.Reverse{} -> False
  if_ o a b t e
    | compare (R.primal a) (R.primal b) == o = t
    | otherwise = e

instance NFData (RD.ReverseDouble s) where
  rnf !a = ()

instance (Reifies s RD.Tape) => N (RD.ReverseDouble s) where
  exprType _ = "RD.ReverseDouble s"
  step = J.lift1 step
    (\ x -> k / (exp (k*x) + exp (-k*x) + 2))
  explicitD vars jacobian _hessian base =
    base
    +
    sum [J.lift1 (const 0) (const $ RD.auto (RD.primal d)) (va ! var)
        | (d, var) <- jacobian]
    where
      va = listArray (0, length vars-1) vars
  partials = RD.partials
  toN = RD.auto . toN
  toD = RD.primal
  dLevel _ = DL1st

  isZero = \ case
    RD.Zero -> True
    RD.Lift x -> isZero x
    RD.ReverseDouble{} -> False
  isOne = \ case
    RD.Zero -> False
    RD.Lift x -> isOne x
    RD.ReverseDouble{} -> False
  if_ o a b t e
    | compare (RD.primal a) (RD.primal b) == o = t
    | otherwise = e
