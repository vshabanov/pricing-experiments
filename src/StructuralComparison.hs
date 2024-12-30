module StructuralComparison where

import Control.DeepSeq
import Data.Number.Erf
import qualified Numeric.AD.Internal.Reverse as R

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
    ,StructuralEq, StructuralOrd)

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
