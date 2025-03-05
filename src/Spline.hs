{-# LANGUAGE NoFieldSelectors, DuplicateRecordFields, DerivingStrategies, DeriveAnyClass #-}
module Spline where

import Control.DeepSeq
import GHC.Generics (Generic)
import Data.Array
import Tridiag
import NLFitting
import Traversables
import Number

-- | Cubic spline coefficients for interpolation (first derivatives)
data CubicSplineK a = CubicSplineK
  { xs :: Array Int a  -- ^ x coordinates
  , ys :: Array Int a  -- ^ y coordinates
  , ks :: Array Int a  -- ^ first derivatives at knot points
  }
  deriving (Show, Functor, Foldable, Traversable, Generic, NFData)

-- | Cubic spline coefficients for interpolation (second derivatives)
data CubicSpline a = CubicSpline
  { xs :: Array Int a  -- ^ x coordinates
  , ys :: Array Int a  -- ^ y coordinates
  , ms :: Array Int a  -- ^ second derivatives at knot points
  }
  deriving (Show, Functor, Foldable, Traversable, Generic, NFData)

-- | Solve cubic spline coefficients for interpolation
--
-- <https://en.wikipedia.org/wiki/Spline_interpolation>
solveCubicSplineK
  :: N a
  => [a]  -- ^ x coordinates (knot points)
  -> [a]  -- ^ y coordinates (values at knots)
  -> CubicSplineK a
solveCubicSplineK xs@(_:txs@(_:_)) ys@(y0:tys@(y1:_)) =
  CubicSplineK
  { xs = listArray (0,n-1) xs
  , ys = listArray (0,n-1) ys
  , ks = listArray (0,n-1) (solveTridiagTDMA t d)
  }
  where
    n = length xs
    h  = zipWith (-) txs xs
    dy = zipWith (-) tys ys

    -- Build tridiagonal system
    t = tridiagFromLists n a b a
    a  = map (1/) h
    b0 = map (2/) h
    b = zipWith (+) (b0 <> [0]) (0:b0)

    -- Right hand side with boundary conditions
    d0 = zipWith (\ y h -> 3*y/h^2) dy h
    d  = zipWith (+) (d0 <> [0]) (0:d0)

-- | Interpolate value at given point using cubic spline
interpolateCubicSplineK
  :: (Fractional a, Ord a)
  => CubicSplineK a -- ^ Precomputed spline coefficients
  -> a              -- ^ x value to interpolate at
  -> a              -- ^ Interpolated y value
interpolateCubicSplineK CubicSplineK{xs,ys,ks} x
  | x <= xmin = (x - xmin) * ks!lo + ys!lo
  | x >= xmax = (x - xmax) * ks!hi + ys!hi
  | otherwise =
--   error $ show (i)
   (1-t)*y0 + t*y1 + t*(1-t)*(a*(1-t) + b*t)
  where
    (lo,hi) = bounds xs
    xmin = xs!lo
    xmax = xs!hi
    -- Find interval containing x
    i = length (takeWhile (<=x) $ elems xs) - 1

    -- Get interval bounds
    x0 = xs!i
    x1 = xs!(i+1)
    h = x1 - x0

    -- Get y values and coefficients
    y0 = ys!i
    y1 = ys!(i+1)
    k0 = ks!i
    k1 = ks!(i+1)

    -- Interpolation parameters
    t = (x - x0) / h
    a =  k0*h - (y1-y0)
    b = -k1*h + (y1-y0)

-- https://lemesurierb.people.charleston.edu/introduction-to-numerical-methods-and-analysis-julia/docs/piecewise-polynomial-approximation-and-splines.html
solveCubicSpline
  :: N a
  => [(a,a)]  -- ^ x-y coordinates (knot points and values at knots)
  -> CubicSpline a
solveCubicSpline points =
  CubicSpline
  { xs = listArray (0,n-1) xs
  , ys = listArray (0,n-1) ys
  , ms = listArray (0,n-1) (0 : solveTridiagTDMA t d <> [0])
  }
  where
    (xs@(_:txs@(_:_)), ys@(y0:tys@(y1:_))) = unzip points
    n = length xs
    h  = zipWith (-) txs xs
    dy = zipWith (-) tys ys

    t = tridiagFromLists (n-2) (drop 1 h) b (drop 1 h)
    b = zipWith (\ a b -> 2*(a+b)) h (drop 1 h)

    d0 = zipWith (/) dy h
    d  = zipWith (\ a b -> 6*(a-b)) (drop 1 d0) d0

solveCubicSplineClamped
  :: N a
  => [(a,a)]  -- ^ x-y coordinates (knot points and values at knots)
  -> a    -- ^ d0
  -> a    -- ^ dn-1
  -> CubicSpline a
solveCubicSplineClamped points d0 dnm1 =
  CubicSpline
  { xs = listArray (0,n-1) xs
  , ys = listArray (0,n-1) ys
  , ms = listArray (0,n-1) (solveTridiagTDMA t rhs)
  }
  where
    (xs@(_:txs@(_:_)), ys@(y0:tys@(y1:_))) = unzip points
    n = length xs
    h  = zipWith (-) txs xs
    dy = zipWith (-) tys ys

    t = tridiagFromLists n h b h
    b = zipWith (\ a b -> 2*(a+b)) (0:h) (h<>[0])

    r = zipWith (/) dy h
    rhs = zipWith (\ a b -> 6*(a-b)) (r<>[dnm1]) (d0:r)

-- | Interpolate value at given point using cubic spline
interpolateCubicSpline
  :: N a
  => CubicSpline a  -- ^ Precomputed spline coefficients
  -> a       -- ^ x value to interpolate at
  -> a       -- ^ Interpolated y value
interpolateCubicSpline CubicSpline{xs,ys,ms=zs} x = go (-1) $ elems xs
  where
    (lo,hi) = bounds xs
    xmin = xs!lo
    xmax = xs!hi
    h0 = xs!(lo+1) - xs!lo
    hnm1 = xs!hi - xs!(hi-1)
    k0 = -h0/3*zs!lo -h0/6*zs!(lo+1) - ys!lo/h0 + ys!(lo+1)/h0
    knm1 = hnm1/6*zs!(hi-1) +hnm1/3*zs!hi - ys!(hi-1)/hnm1 + ys!hi/hnm1

    -- Find interval containing x
    go _ [] = (x - xmax) * knm1 + ys!hi
    go i (e:es) = if_ GT x e (go (i+1) es) $
      if i < 0 then
        (x - xmin) * k0 + ys!lo
      else
        ( z0/(6*h)*(x1-x)^3
        + z1/(6*h)*(x-x0)^3
        + (y0/h - z0*h/6)*(x1-x)
        + (y1/h - z1*h/6)*(x-x0))
      where
        -- Get interval bounds
        x0 = xs!i
        x1 = xs!(i+1)
        h = x1 - x0

        -- Get y values and coefficients
        y0 = ys!i
        y1 = ys!(i+1)
        z0 = zs!i
        z1 = zs!(i+1)

data GaussianKernel a = GaussianKernel
  { αs :: [a]  -- ^ α_k
  , xs :: [a]  -- ^ x_k
  , λ  :: a
  }
  deriving (Show, Functor, Foldable, Traversable)

interpolateGK GaussianKernel{αs,xs,λ} x =
    sum [αk * ψλ (x-xk) | (αk,xk) <- zip αs xs]
  / sum [     ψλ (x-xk) | xk <- xs]
  where
    ψλ u = 1/(λ*sqrt (2*pi)) * exp(-u^2/(2*λ^2))

fitGK λ xys =
  GaussianKernel
  { αs =
    fitSystemThrow (T λ (TT xs ys)) (map (const 1) xys)
               $ \ (T λ (TT xs ys)) αs ->
      [interpolateGK GaussianKernel{αs,xs,λ} x - y
      |(x,y) <- zip xs ys]
  , xs = xs
  , λ  = λ
  }
  where
    (xs,ys) = unzip xys
