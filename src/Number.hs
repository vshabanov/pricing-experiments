{-# OPTIONS_GHC -Wincomplete-patterns -O2 #-}
module Number where

import Data.Array
import Control.DeepSeq
import Data.Number.Erf
import Data.Reflection
import qualified Numeric.AD.Mode as R
import qualified Numeric.AD.Mode.Reverse as R
import qualified Numeric.AD.Internal.Reverse as R
import qualified Numeric.AD.Jacobian as J
import GHC.TypeError

instance NFData (R.Reverse s a) where
  rnf a = seq a ()

-- | extended Num functions
class (NFData a, Show a, Erf a, Ord a, StructuralOrd a) => N a where
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

-- | Structural equality.
-- @x == x^2@ for some @x@-es, but their derivatives are different
class StructuralEq a where
  structuralEq :: a -> a -> Bool

class StructuralEq a => StructuralOrd a where
  structuralCompare :: a -> a -> Ordering

-- | Wrapper to make 'Eq' and 'Ord' instances use 'StructuralEq' and 'StructuralOrd'.
newtype SCmp a = SCmp { unSCmp :: a }
  deriving
    (Show, Num, Fractional, Floating, Erf, NFData
    ,StructuralEq, StructuralOrd, N)

instance StructuralEq a => Eq (SCmp a) where
  SCmp a == SCmp b = structuralEq a b
instance StructuralOrd a => Ord (SCmp a) where
  SCmp a `compare` SCmp b = structuralCompare a b

instance StructuralEq Integer where
  structuralEq = (==)
instance StructuralOrd Integer where
  structuralCompare = compare
instance StructuralEq Int where
  structuralEq = (==)
instance StructuralOrd Int where
  structuralCompare = compare
instance StructuralEq Double where
  structuralEq = (==)
instance StructuralOrd Double where
  structuralCompare = compare
instance StructuralEq a => StructuralEq [a] where
  structuralEq a b = map SCmp a == map SCmp b
instance (StructuralEq a, StructuralEq b) => StructuralEq (a,b) where
  structuralEq (a1,a2) (b1,b2) = structuralEq a1 b1 && structuralEq a2 b2
instance (StructuralEq a, StructuralEq b, StructuralEq c) => StructuralEq (a,b,c) where
  structuralEq (a1,a2,a3) (b1,b2,b3) =
    structuralEq a1 b1 && structuralEq a2 b2 && structuralEq a3 b3

instance StructuralEq a => StructuralEq (R.Reverse s a) where
  structuralEq a b = case (a, b) of
    (R.Zero, R.Zero) -> True
    (R.Zero, _) -> False
    (R.Lift a, R.Lift b) -> structuralEq a b
    (R.Lift _, _) -> False
    (R.Reverse a _, R.Reverse b _) -> a == b
    (R.Reverse _ _, _) -> False

instance StructuralOrd a => StructuralOrd (R.Reverse s a) where
  structuralCompare = \ case
    R.Zero -> \ case
      R.Zero -> EQ
      _ -> LT
    R.Lift a -> \ case
      R.Zero -> GT
      R.Lift b -> structuralCompare a b
      R.Reverse{} -> LT
    R.Reverse a _ -> \ case
      R.Reverse b _ -> compare a b
      _ -> GT
