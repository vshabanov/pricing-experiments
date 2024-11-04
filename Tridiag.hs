{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wno-x-partial #-}
module Tridiag
  ( (.+), (.-), (.*), (#>)
  , Tridiag, tridiag
  , solveTridiagTDMA
  , solveTridiagLATridiag
  , solveTridiagLAGeneric
  , laTridiag
  )
where

import Data.Array
import Control.Monad
import Control.Monad.ST
import qualified Data.Vector.Mutable as M
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U

import qualified Numeric.LinearAlgebra as LA
import Test.QuickCheck

infixl 6 .+, .- -- same as (+)
infixl 7 .*, #> -- same as (*)

-- scale .* mat = realToFrac scale * mat

t@(Tridiag sa l d u) #> vec
  | length vec /= sa
  = err ["Matrix size /= vector size, ", show t, " ", show vec]
  | otherwise
  = case vec of
      []  -> []
      [x] -> [d*x]
      _   ->
           [               d * v!0 + u * v!1]
        <> [l * v!(i-1)  + d * v!i + u * v!(i+1) | i <- [1..sa-2]]
        <> [l * v!(sa-2) + d * v!(sa-1)]
  where
    v = listArray (0,sa-1) vec

(.*) :: Num a => a -> Tridiag a -> Tridiag a
scale .* Tridiag s l d u = Tridiag s (scale*l) (scale*d) (scale*u)

liftTridiag2 :: Show a => (a -> a -> a) -> Tridiag a -> Tridiag a -> Tridiag a
liftTridiag2 f a@(Tridiag sa la da ua) b@(Tridiag sb lb db ub)
  | sa /= sb
  = err ["Mismatch in tridiag sizes ", show a, ", ", show b]
  | otherwise
  = Tridiag sa (f la lb) (f da db) (f ua ub)
a .+ b = liftTridiag2 (+) a b
a .- b = liftTridiag2 (-) a b

tridiag = Tridiag

data Tridiag a
  = Tridiag
    { tridiagSize :: Int
    , tridiagL :: a
    , tridiagD :: a
    , tridiagU :: a
    }
  deriving Show

tridiagVectors (Tridiag s l d u) =
  (replicate (s-1) l
  ,replicate  s    d
  ,replicate (s-1) u)

err x = error $ mconcat x

solveTridiagTDMA :: (Fractional a, Ord a, Show a) => Tridiag a -> [a] -> [a]
solveTridiagTDMA t@(Tridiag _ l d u)
  | d < l + u
  = err ["solveTridiagTDMA: matrix ", show t, " is not diagonally dominant"]
    -- can produce wildly different results from solveTridiagLAGeneric
    -- for non-diagonally dominant matrices
  | otherwise
  = tdmaSolver ([0] <> ll) ld (lu <> [0])
  where
    (ll, ld, lu) = tridiagVectors t

solveTridiagLATridiag t vec =
  LA.toList $ head $ LA.toColumns
    $ LA.triDiagSolve (LA.fromList ll) (LA.fromList ld) (LA.fromList lu)
    $ LA.fromColumns [LA.fromList vec]
  where
    (ll, ld, lu) = tridiagVectors t

solveTridiagLAGeneric (Tridiag s l d u) vec =
  LA.toList $ laTridiag s l d u LA.<\> LA.fromList vec


laTridiag size l d u =
  (LA.dropRows 1 (diag u) LA.=== zeroRow)
  +
  diag d
  +
  (zeroRow LA.=== LA.subMatrix (0,0) (size-1,size) (diag l))
  where
    diag x = LA.diagl $ replicate size x
    zeroRow = LA.row $ replicate size 0


data SolveTridiagInputs a
  = SolveTridiagInputs
    { stiTridiag :: Tridiag a
    , stiVector :: [a]
    }
  deriving Show

instance Arbitrary (SolveTridiagInputs Double) where
  arbitrary = do
    tridiagSize <- chooseInt (5, 50)
    let e = choose (1,10)
        v s = vectorOf s e
    tridiagL <- e
    tridiagU <- e
    let m = tridiagL + tridiagU
    tridiagD <- choose (m, 2*m) -- diagonally dominant
    stiVector <- vectorOf tridiagSize e
    pure $ SolveTridiagInputs{stiTridiag=Tridiag{..}, ..}

prop_solveTridiag SolveTridiagInputs{..} =
  and $ zipWith (epsEq 1e-11)
    (solveTridiagTDMA stiTridiag stiVector)
--     (solveTridiagLAGeneric stiTridiag stiVector)
    (solveTridiagLATridiag stiTridiag stiVector)

data TestTridiagInputs a
  = TestTridiagInputs
    { ttiA :: [a]
    , ttiB :: [a]
    , ttiC :: [a]
    , ttiD :: [a]
    }
  deriving Show

instance Arbitrary (TestTridiagInputs Double) where
  arbitrary = do
    size <- chooseInt (5, 50)
    let v s = vectorOf s $ choose (1,10)
    ttiA <- v (size-1)
    ttiB <- v size
    ttiC <- v (size - 1)
    ttiD <- v size
    pure $ TestTridiagInputs{..}

prop_tridiag TestTridiagInputs{..} = and $ zipWith (epsEq 5e-12) qf la
  where
    qf = tdmaSolver ([0]<>ttiA) ttiB (ttiC<>[0]) ttiD
    la = LA.toList $ head $ LA.toColumns
      $ LA.triDiagSolve (LA.fromList ttiA) (LA.fromList ttiB) (LA.fromList ttiC)
      $ LA.fromColumns [LA.fromList ttiD]

epsEq e a b = eps a b < e
eps a b = abs (a-b) / max (abs a) (abs b)

-- https://hackage.haskell.org/package/quantfin-0.2.0.0/docs/src/Quant-Math-Utilities.html#tdmaSolver
-- | Tridiagonal matrix solver.  Pretty simple.
tdmaSolver :: (Fractional a, Ord a) => [a] -> [a] -> [a] -> [a] -> [a]
tdmaSolver aL bL cL dL = V.toList $
    let [a,b,c,d] = map V.fromList [aL,bL,cL,dL] in
        runST $ do
            c' <- V.thaw c
            M.write c' 0 (V.head c / V.head b)
            forM_ [1..V.length c-1] $ \x -> do
                let ai = a V.! x
                    bi = b V.! x
                    ci = c V.! x
                ci1' <- M.read c' (x-1)
                M.write c' x $ ci / (bi-ai*ci1')
            cf <- V.unsafeFreeze c'
            d' <- V.thaw d
            M.write d' 0 (V.head d / V.head b)
            forM_ [1..V.length d-1] $ \x -> do
                let ai  = a  V.! x
                    bi  = b  V.! x
                    di  = d  V.! x
                    ci1 = cf V.! (x-1)
                di1' <- M.read d' (x-1)
                M.write d' x $ (di-ai*di1') / (bi-ai*ci1)
            df <- V.unsafeFreeze d'
            xn <- M.new $ V.length d
            M.write xn (V.length d-1) $ V.last df
            forM_ (reverse [0..V.length df-2]) $ \ x-> do
                let ci = cf V.! x
                    di = df V.! x
                xi1 <- M.read xn $ x+1
                M.write xn x $ di - ci*xi1
            V.unsafeFreeze xn
{-# INLINE tdmaSolver #-}
