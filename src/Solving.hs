module Solving
  ( newton
  , brent
  )
  where

import Debug.Trace
import Number
import Numeric.AD.Mode.Reverse qualified as R
import Numeric.GSL.Root

newton
  :: N a
  => (forall a . N a => [a] -> a -> a) -- inputs guess -> result
  -> [a] -- ^ inputs
  -> a   -- ^ guess
  -> Either String (a, [a], a) -- ^ (result, [df_i\/dInput_i], dGuess)
newton f inputs x0 = go 0 x0
  where
    go iter x
      | iter > 50 = Left ("too many iterations, last guess " <> show x)
      | (fx, (dx:dis)) <- R.grad' (\ (x:is) -> f is x) (x:inputs) =
        trace (show (x, fx, dx, fx / dx)) $
        if abs fx < 1e-10 then
          Right (x, dis, dx)
        else
          go (succ iter) (x - fx / dx)

-- | Bisection solver
bisectionSolve f min max = go 0 min max
  where
    go iter a b
       | iter > 50 = Left "too many iterations"
       | abs (f mid) < 1e-10 = Right (mid, iter)
       | f mid > 0 && f a < 0 = go (succ iter) a mid
       | f mid > 0 && f b < 0 = go (succ iter) mid b
       | f mid < 0 && f a > 0 = go (succ iter) a mid
       | f mid < 0 && f b > 0 = go (succ iter) mid b
       | otherwise = Left $ concat
         ["bracket doesn't contain root f(", show a, ")=", show (f a)
         ,", f(", show b, ")=", show (f b)]
       where mid = (a+b)/2

-- fails if can't solve
-- need to add implicit function theorem
-- as a quick hack we can just call fitSystem with 'r'
brent f min max = r
  where
    r = uniRoot Brent 0x1p-28 100 f min max

-- brent (\ x -> let s = SABR {f0 = 1.3465, t = 2.7397260273972603e-3, σ0 = 8.091763568780608e-2, ν = 8.276827983108886, ρ = -0.5158156659150436} in bs (Delta SpotPips) (BS {k = x, d = Call, t = 2.7397260273972603e-3, s = 1.3465, σ = smileVol s x, rf = 3.46e-2, rd = 2.94e-2}) - 0.25) 1 2
