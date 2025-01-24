{-# LANGUAGE MagicHash, ViewPatterns #-}

module Random
  ( gaussianQuasiRandom
  , gaussian
  , chunkedGaussian
  , chunkedGaussian'
  , chunkedGaussianQuasi
  , splitMixSplits
  , gaussianSM
  )
  where

import qualified System.Random.SplitMix as SplitMix
import qualified Control.Monad.State.Strict as State.Strict
import Control.Monad.Identity
import System.Random.Stateful (StatefulGen(..))
import Data.List
import Data.List.Split
import Data.Number.Erf
import Data.Monoid

import GHC.Word
import GHC.Float
import GHC.Num.Primitives (wordReverseBits#)
import GHC.Prim (word2Double#, (*##))

import qualified System.Random.MWC as MWC
import qualified System.Random.MWC.Distributions as MWC

import qualified Data.Vector.Unboxed as U

import Gnuplot

{-# INLINE gaussianQuasiRandom #-}
{-# INLINE gaussian #-}
{-# INLINE chunkedGaussian #-}
{-# INLINE chunkedGaussian' #-}

splitMixSplits n = take n $ split [SplitMix.mkSMGen 1337]
  where
    split gs = ss <> split ss
      where ss = concat [[a,b] | g <- gs, let (a,b) = SplitMix.splitSMGen g]

-- | low-disrepancy Gaussian distribution based on 'corput2'
gaussianQuasiRandom n =
  map (invnormcdf . corput2) [1..toEnum n]

gaussianSM n =
--  runIdentity . State.Strict.evalStateT (replicateM n $ MWC.standard $ DummyGen ())
--   U.unfoldrExactN n
--   (\ g -> let (x, g') = SplitMix.nextDouble g in (invnormcdf x, g'))
 take n . map invnormcdf . unfoldr (Just . SplitMix.nextDouble)

chunkedGaussian chunk n = chunkedGaussian' chunk n defaultSM
chunkedGaussian' chunk n = chunksOf chunk . gaussianSM (chunk * n)

chunkedGaussianQuasi chunk n = chunksOf chunk $ gaussianQuasiRandom (chunk * n)

-- chunkedGaussian chunk n = go n $ gaussian (chunk * n)
--   where
--     go 0 _ = []
--     go n v = let (x,xs) = U.splitAt chunk v in x : go (n-1) xs

defaultSM = SplitMix.mkSMGen 1337

gaussian :: Int -> [Double]
gaussian n
 =  gaussianSM n defaultSM
    -- nextDouble [0..1), а нам нужно [0..1]
--    runIdentity $ State.Strict.evalStateT (replicateM n $ MWC.standard $ DummyGen ()) (SplitMix.mkSMGen 1337)
    --   1k      10k    100k     1mio    10mio
    --  0.18%   0.39    0.31     0.084   -0.007

--     runST $ replicateM n . MWC.standard =<< MWC.create
    --   1k      10k    100k     1mio    10mio (goes up as LAPACK)
    -- -5.37%  -0.88   -0.13    0.014   -0.059
--    take n $ map invnormcdf $ randomRs (0.0,1.0) (mkStdGen 137)
    -- about 2x bigger difference than with LAPACK on average
    -- 2M error is bigger than 1M error!
    -- while LAPACK is slowly decreasing (but 10M error is bigger again
    -- 0.064% -> 0.0512% -> 0.07834%
  -- = LV.toList $ LV.random LV.Normal (Shape.Range 1 n) (toEnum 137)
--   = LA.toList $ LA.randomVector 137 LA.Gaussian n
--     ^^ seems to be not thread-safe and doesn't look good on small sample size

-- | https://en.wikipedia.org/wiki/Van_der_Corput_sequence
corput :: Int -> Int -> Double
corput base n = go n rBase 0.0
  where
    rBase = recip $ toEnum base
    go !n !bk !q
      | n > 0 = go (n `div` base) (bk * rBase) (q + toEnum (n `mod` base)*bk)
      | otherwise = q

-- | Optimized @'corput' 2@
-- https://www.pbr-book.org/3ed-2018/Sampling_and_Reconstruction/The_Halton_Sampler
corput2 :: Word -> Double
corput2 (W# w) = (D# (word2Double# (wordReverseBits# w))) * 0x1p-64
-- λ> and [corput2 i == corput 2 (fromEnum i) | i <- [1..1000000]]
-- True


newtype DummyGen = DummyGen ()

instance StatefulGen DummyGen (State.Strict.State SplitMix.SMGen) where
   uniformWord64 _ = State.Strict.StateT $ Identity . SplitMix.nextWord64
   uniformWord32 _ = State.Strict.StateT $ Identity . SplitMix.nextWord32
   uniformShortByteString = error "uniformShortByteString SMGen is not implemented" -- added to remve MonadIO constraint from the default implementation

-- replicateM is 10-20% faster in GHCi and slightly faster in -O2 microbenchmark
replicateAcc n act = go n []
  where
    go 0 acc = pure $ reverse acc
    go n acc = do
      !x <- act
      go (n-1) (x:acc)

-- doesn't look to approach 1, more like jumping around 0.2-0.7
lawOfIteratedLogarithm = sum (take n $ map (\x -> (toEnum . fromEnum) x*2-1) $ unfoldr (Just . SplitMix.bitmaskWithRejection64' 1) (SplitMix.mkSMGen 1337))
  / sqrt (2*n * log (log n))
  where
    n :: Num a => a
    n = 5000000

plotg = plotGraphs
  [defaultStyle $ histogramPlot 0.001
--   $ map (\ e -> spotAtT mkt e 0.5)
   $ gaussian 50000]

--    1
--   1 1
--  1 2 1
-- 1 3 3 1
pascalTriangleRow n
  | n <= 1 = [1]
  | otherwise = let p = pascalTriangleRow (n-1) in
      zipWith (+) ([0]<>p) (p<>[0])

plotp = plotGraphs
  [defaultStyle [(toEnum i, fromRational $ x / sum p) | (i,x) <- zip [start..end] (drop start p)]]
  where
    p :: [Rational]
    p = pascalTriangleRow n -- sum [Double] overlows at 1100
    n = 2000
    plotN = 101
    start = (n-plotN)`div`2
    end = start + plotN - 1


mean [] = error "mean: empty list"
mean x  = sum x / toEnum (length x)

-- https://mathworld.wolfram.com/RandomWalk1-Dimensional.html
--   proportional to sqrt (2N/pi)
-- https://mathworld.wolfram.com/RandomWalk2-Dimensional.html
--   proportional to sqrt N
brownianDistance = mean distances / sqrt n -- usually around 0.9, not 1.0
  where
    n :: Num a => a
    n = 1000
    nPaths = 10000
--     dist path = sqrt $ x^2 + y^2 + z^2
--       where
--         (Sum x, Sum y, Sum z) =
--           mconcat
--           [(Sum $ sin θ * cos φ, Sum $ sin θ * sin φ, Sum $ cos θ)
--            | [(pi*) -> θ, (2*pi*) -> φ] <- chunksOf 2 path]
    dist path = sqrt $ x^2 + y^2
      where
        (Sum x, Sum y) =
          mconcat
          [(Sum $ sin φ, Sum $ cos φ)
           | [(pi*) -> θ, (2*pi*) -> φ] <- chunksOf 2 path]
    distances =
      map dist $ take nPaths $ chunksOf (2*n)
      $ unfoldr (Just . SplitMix.nextDouble) (SplitMix.mkSMGen 133711)
