module Solving
  ( newton
  , solve
  )
  where

import qualified Numeric.AD.Mode.Reverse as R
import Number

newton
  :: N a
  => (forall a . N a => [a] -> a -> a) -- inputs guess -> result
  -> [a] -- ^ inputs
  -> a   -- ^ guess
  -> Either String (a, [a], a) -- ^ (result, [df_i\/dInput_i], dGuess)
newton f inputs x0 = go 0 x0
  where
    go iter x
      | iter > 50 = Left "too many iterations"
      | (fx, (dx:dis)) <- R.grad' (\ (x:is) -> f is x) (x:inputs) =
        if abs fx < 1e-15 then
          Right (x, dis, dx)
        else
          go (succ iter) (x - fx / dx)

-- | Bisection solver
solve f = go 0 (-10) 10
  where
    go iter a b
       | iter > 50 = Left "too many iterations"
       | abs (f mid) < 1e-9 = Right mid
       | f mid > 0 && f a < 0 = go (succ iter) a mid
       | f mid > 0 && f b < 0 = go (succ iter) mid b
       | f mid < 0 && f a > 0 = go (succ iter) a mid
       | f mid < 0 && f b > 0 = go (succ iter) mid b
       | otherwise = Left $ concat
         ["bracket doesn't contain root f(", show a, ")=", show (f a)
         ,", f(", show b, ")=", show (f b)]
       where mid = (a+b)/2
