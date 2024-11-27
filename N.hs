module N where

import Control.DeepSeq
import Data.Number.Erf
import Data.Reflection
import qualified Numeric.AD.Mode.Reverse as R
import qualified Numeric.AD.Internal.Reverse as R
import qualified Numeric.AD.Jacobian as J

toD :: N a => a -> Double
toD = realToFrac

toN :: N a => Double -> a
toN = realToFrac

instance NFData (R.Reverse s a) where
  rnf a = seq a ()

-- | extended Num functions
class (NFData a, Show a, Enum a, Ord a, Real a, Erf a) => N a where
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

  -- | Specify an explicit derivative to a variable
  explicitD :: Double -> a -> a
  explicitD _ _ = 0

  partials :: a -> [Double]
  partials _ = []

width = 0.0001 -- NaN with 0.01, larger error with 0.1 or 1
                -- but for 'integrated' 0.1 gives good result
--     width = 0.000001  -- gives 0.00004 = 1 (half pip)
                      --      -0.00004 ~ 4e-18
    -- k=10 дает плавный переход от -0.5 до 0.5?
k, width :: Erf a => a
k = 1/width -- steepness

instance N Double
instance (Reifies s R.Tape, Ord a, Erf a, N a) => N (R.Reverse s a) where
  step = J.lift1 step
  -- Dirac delta is not much better
--     (\ x -> 1 / realToFrac (abs a * sqrt pi) * exp (-(x / realToFrac a)^2))
--     where a = 0.1 -- lower values lead to bigger error until it breaks at ~0.001
    (\ x -> k / (exp (k*x) + exp (-k*x) + 2))
  -- no NaN this way, but error grows for width<0.1, and breaks at 0.0003
-- 1000 / (exp 1000 + exp (-1000) + 2)
  explicitD d = J.lift1 (const 0) (const $ realToFrac d)
  partials = map toD . R.partials
