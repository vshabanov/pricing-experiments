{-# LANGUAGE LambdaCase, BangPatterns, ViewPatterns, MagicHash, RecordWildCards, ScopedTypeVariables #-}
{-# OPTIONS_GHC -O2 -Wno-x-partial #-}
--module ZeroDeltaTest (main) where

import Data.Number.Erf

import Data.Array
import Debug.Trace
import Data.Monoid
import Data.List.Split
import Test.QuickCheck
import Criterion.Main
import Graphics.Gnuplot.Simple

import qualified Graphics.Gnuplot.Advanced as GP
import qualified Graphics.Gnuplot.MultiPlot as MultiPlot

import qualified Graphics.Gnuplot.Graph as Graph

import qualified Graphics.Gnuplot.Plot.TwoDimensional as Plot2D
import qualified Graphics.Gnuplot.Graph.TwoDimensional as Graph2D
import Graphics.Gnuplot.Plot.TwoDimensional (linearScale, )

import qualified Graphics.Gnuplot.LineSpecification as LineSpec
import Graphics.Gnuplot.Value.Tuple (Label(Label))


import Data.Maybe
import System.Random
import qualified Data.IntMap as IntMap
import Data.Bifunctor
-- import qualified Numeric.LAPACK.Vector as LV
import qualified Data.Array.Comfort.Shape as Shape
import qualified Numeric.LinearAlgebra as LA
import qualified System.Random.MWC as MWC
import qualified System.Random.MWC.Distributions as MWC
import Control.Monad.ST
import Control.Monad
import Data.List
import qualified System.Random.SplitMix as SplitMix
import qualified Control.Monad.State.Strict as State.Strict
import Control.Monad.Identity
import System.Random.Stateful (StatefulGen(..))
import Control.Concurrent
import Control.Concurrent.Async
import System.IO.Unsafe
import Text.Printf

import Data.Reflection
import qualified Numeric.AD.Mode as AD
import qualified Numeric.AD.Mode.Reverse as R
import qualified Numeric.AD.Internal.Reverse as R
import qualified Numeric.AD.Jacobian as J

import GHC.Word
import GHC.Float
import GHC.Num.Primitives (wordReverseBits#)
import GHC.Prim (word2Double#, (*##))

import Control.Monad.ST
import qualified Data.Vector.Mutable as M
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U


data Greek
  = PV
  | RhoFor
  | RhoDom
  | Delta
  | Gamma
  | Vega
  | Vanna
  | Theta
  deriving Show

data Input
  = Spot
  | Vol
  | RateDom
  | RateFor
  | PricingDate
  deriving (Show, Eq)

data OptionDirection
  = Call
  | Put
  deriving Show

data Option a
  = Option
    { oStrike :: a
    , oMaturityInYears :: a
    , oDirection :: OptionDirection
    }
data Forward a
  = Forward
    { fStrike :: Strike a
    , fMaturityInYears :: MaturityInYears a
    }
newtype Strike a = Strike { strike :: a }
  deriving (Num, Fractional, Floating, Erf)
newtype MaturityInYears a = MaturityInYears { maturityInYears :: a }
  deriving (Num, Fractional, Floating, Erf)

forwardRate :: Erf a => Market a -> MaturityInYears a -> a
forwardRate market (MaturityInYears τ) = x * exp ((rd-rf)*τ)
  where
    x = market Spot
    rd = market RateDom
    rf = market RateFor

digiPricer :: Erf a => Option a -> (Input -> a) -> Greek -> a
digiPricer o market what = case what of
  PV ->
    φ * exp (-rd*τ) * nc (φ*dm) -- digi
  where
    k = oStrike o
    τ = oMaturityInYears o - market PricingDate
    φ = oφ o
    x = market Spot
    σ = market Vol
    rd = market RateDom
    rf = market RateFor
    nc = normcdf
    f = x * exp ((rd-rf)*τ)
    dm = (log (f/k) - σ^2/2*τ) / (σ*sqrt τ)

blackSholesPricer :: Erf a => Option a -> (Input -> a) -> Greek -> a
blackSholesPricer o market what = case what of
  PV ->
--    φ * exp (-rd*τ) * nc (φ*dm) -- digi
    φ * exp (-rd*τ) * (f * nc (φ*dp) - k * nc (φ*dm))
  RhoDom ->
    φ * k * τ * exp (-rd*τ) * nc (φ*dm)
  RhoFor ->
    -φ * x * τ * exp (-rf*τ) * nc (φ*dp)
  Delta ->
    φ * exp (-rf*τ) * nc (φ*dp)
  Gamma ->
    exp (-rf*τ) * n dp / (x*σ*sqrt τ)
  Vega ->
    x * exp (-rf*τ) * sqrt τ * n dp
  Vanna ->
    - exp (-rf*τ) * n dp * dm / σ
  Theta ->
    - exp (-rf*τ) * n dp * x * σ / (2*sqrt τ)
    + φ * (rf*x*exp (-rf*τ) * nc (φ*dp) - rd*k*exp (-rd*τ) * nc (φ*dm))
  where
    k = oStrike o
    τ = oMaturityInYears o - market PricingDate
    x = market Spot
    σ = market Vol
    rd = market RateDom
    rf = market RateFor
    φ = oφ o
    nc = normcdf
    n = normdf
    f = x * exp ((rd-rf)*τ)
    dp = (log (f/k) + σ^2/2*τ) / (σ*sqrt τ)
    dm = (log (f/k) - σ^2/2*τ) / (σ*sqrt τ)

oφ o = case oDirection o of
  Call ->  1
  Put  -> -1

normdf t = exp (- t^2/2) / sqrt (2*pi)

forwardPricer :: Floating a => Forward a -> (Input -> a) -> Greek -> a
forwardPricer f market what = case what of
  PV ->
    x * exp ((-rf)*τ) - k * exp ((-rd)*τ)
  where
    Strike k = fStrike f
    MaturityInYears m = fMaturityInYears f
    τ = m - market PricingDate
    x = market Spot
    rd = market RateDom
    rf = market RateFor

-- | ϵ -- a sample from a normal distribution with mean=0 and stddev=1
spotAtT market ϵ τ =
  s0 * exp ((μ̂ - σ^2/2)*τ + σ*ϵ*sqrt τ)
  where
    μ̂ = rd - rf
    s0 = market Spot
    σ = market Vol
    rd = market RateDom
    rf = market RateFor

optionPv :: N a => Option a -> (Input -> a) -> (a -> a) -> a
optionPv o market spotAt =
  exp (-rd*τ) * -- log1pexp (payoff * scale) / scale
  step payoff * payoff
  -- max payoff 0
  where
    scale = 1e10 -- better with 100, but doesn't break with 1e10
    payoff = φ * (spotAt τ - k)
    k = oStrike o
    τ = oMaturityInYears o - market PricingDate
    φ = oφ o
    rd = market RateDom

toDouble :: N a => a -> Double
toDouble = realToFrac

-- | extended Num functions
class (Show a, Enum a, Ord a, Real a, Erf a) => N a where
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

digiOptionPv o market spotAt =
  exp (-rd*τ) * step (φ * (spotAt τ - k))
  where
    k = oStrike o
    τ = oMaturityInYears o - market PricingDate
    φ = oφ o
    rd = market RateDom

combine a b market what = a market what + b market what
scale s f market what = s * f market what

-- мало что меняет, видимо маленьких значений нет
treeSum l = case splitSum l of -- $ sort l of
  [] -> 0
  [x] -> x
  xs -> treeSum xs
  where
    splitSum [] = []
    splitSum [x] = [x]
    splitSum (x:y:xs) = x+y : splitSum xs

type Market a = Input -> a

monteCarlo :: N a => Market a -> a
monteCarlo mkt =
  treeSum [getPv mkt (spotAtT mkt (realToFrac ϵ)) | ϵ <- gaussian n] / toEnum n
--   unsafePerformIO $
--   fmap sum $ forConcurrently (splitMixSplits threads) $ \ sm ->
--     pure $! treeSum [getPv mkt (spotAtT mkt (realToFrac ϵ)) | ϵ <- gaussianSM tn sm] / fromRational n
  where
    threads = 1 -- 1 thread gives better greeks?
    --   1k      10k    100k     1mio    10mio
    --  0.18%   0.39    0.31     0.084   -0.007
    --
    --   10mio   10k    100k
    -- 1 0.007%
    -- 4 0.05%  0.04    0.4      0.019
    -- 8 0.032%
    tn = n `div` threads
    n :: Num a => a
    n = 10000

_integrated :: N a => Market a -> a
_integrated mkt =
  treeSum [getPv mkt (spotAtT mkt (realToFrac $ x+step/2)) *
       realToFrac (normcdf (x+step) - normcdf x) | x <- [from, from+step .. to]]
  -- мы можем просто провести интеграцию
  where
    n = 100/width
    -- 0.32% with n=100, better than monteCarlo with n=100_000
    -- 5e-9% with n=1M
    -- у digital погрешность гораздо больше
    -- 4e-4% with n=1M
    step = (to-from)/n :: Double
    (from, to) = (-5,5) -- best greeks 0-0.014% for vanilla
--     (from, to) = (-39,9) -- best PV, 0.001%
--     (from, to) = (-10,10) -- map normcdf [-39,9] == [0,1]

-- здесь точность хуже, это по-сути тот же Monte-Carlo только с равномерным
-- распределением, но с width=0.001 (n=100k) становится точнее

integrated :: N a => Market a -> a
integrated = integrated' $ truncate (10/width :: Double)

-- doesn't help
{-# SPECIALIZE integrated' :: Int -> Market Double -> Double #-}
{-# SPECIALIZE fem' :: Int -> Int -> Market Double -> Double #-}

integrated' :: N a => Int -> Market a -> a
integrated' n mkt = realToFrac step * treeSum
  [getPv mkt (spotAtT mkt (realToFrac mid))
  | x <- [0..n-1]
  , let mid = invnormcdf (toEnum x * step + step/2)
  ]
  where
    step = 1/toEnum n :: Double

o :: Erf a => Option a
o = Option
  { oStrike =
    1
--    forwardRate mkt (oMaturityInYears o)
  , oMaturityInYears = 1 -- 0.1/365
  , oDirection = Call }

f :: Erf a => Forward a
f = Forward { fStrike = oStrike o, fMaturityInYears = oMaturityInYears o }

p :: N a => Market a -> Greek -> a
getPv :: N a => Market a -> (a -> a) -> a
-- p     = digiPricer o
-- getPv = digiOptionPv o
p     = blackSholesPricer o
getPv = optionPv o

greeksBump = map (\ i -> dvdx PV i 0.00001) [Spot, Vol, RateDom, RateFor, PricingDate]
greeksBumpIntegrated = map (\ i -> dvdx' (const . integrated) mkt () i 0.00001) [Spot, Vol, RateDom, RateFor, PricingDate]
greeksBumpMonteCarlo = map (\ i -> dvdx' (const . monteCarlo) mkt () i 0.00001) [Spot, Vol, RateDom, RateFor, PricingDate]
greeksAnalytic = map (p mkt) [Delta, Vega, RhoDom, RhoFor, Theta, Gamma, Vanna] :: [Double]

newtype Percent = Percent Double
instance Show Percent where show (Percent p) = printf "%.5f%%" p
pct a b = Percent ((a / b - 1) * 100)

pv :: Double
[(pv,greeks)] =
  R.jacobian' (\ [s,v,rd,rf,pd] ->
    [ --fem
-- σ=0.3, rd=0.05, rf=0.03, nx=500, nt=500, spot=[0.050..20.086], h=0.011976
-- [0.00076%,-0.06512%,-0.01311%,0.01374%,-0.06819%]
      integrated
-- λ> zipWith pct greeks greeksBump
-- [-0.000%,0.014%,0.002%,-0.000%,0.013%] -- vanilla
-- [-0.015%,0.008%,-0.021%,-0.015%,0.039%] -- digi
     --monteCarlo
-- λ> zipWith pct greeks greeksBump
-- [-0.779%,1.087%,-1.034%,-0.779%,0.779%] -- vanilla
-- [-2.703%,-2.258%,-3.307%,-2.703%,-0.790%] -- digi
     -- digiPricer o
     -- [3.6661059215952516e-2,-0.2291316200997029,0.6795758158561364,-0.9165264803988129,3.744296366024975e-2] ~= greeksBump
     -- blackSholesPricer o
     -- [0.5644849344925212,13.74789720598219,11.847533227133829,-14.112123362313032,-4.744637550015519] epsEq greeksAnalytic
      (\ case
        Spot -> s
        Vol -> v
        RateDom -> rd
        RateFor -> rf
        PricingDate -> pd)
--       PV
    ])
    [mkt Spot, mkt Vol, mkt RateDom, mkt RateFor, mkt PricingDate]

--     `combine`
--     scale (-0.5)
--     (forwardPricer Forward { fStrike = 1.2, fMaturityInYears = 3/12 })
mkt :: Fractional a => Input -> a
mkt = \ case
    Spot -> 1
    Vol -> 0.3
    RateDom -> 0.05
    RateFor -> 0.03
    PricingDate -> 0
-- p = blackSholesPricer
--     $ Option { oStrike = 300, oMaturityInYears = 0.001, oDirection = Call }
-- mkt = \ case
--     Spot -> 300
--     Vol -> 0.21058845741208643
--     RateDom -> 0.03
--     RateFor -> 0.01
--     PricingDate -> 0
modify input f m i
  | i == input = f $ m i
  | otherwise = m i
m input f = modify input f mkt

test' what rd = p (modify RateDom (const rd) mkt) what

solvePriceToVol price = solve (\ x -> p (m Vol (const x)) PV - price)

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

-- symd f x bump = (f (x+bump) - f (x-bump)) / (2*bump)
symd f x part bump = (f (x+part*bump) - f (x-part*bump)) / (2*bump)

dvdx'
  :: (Market Double -> a -> Double)
     -> Market Double -> a -> Input -> Double -> Double
dvdx' p mkt what x (bump :: Double)
--     | mkt x > bump =
--         (p (modify x (* (1+bump)) mkt) what -
--          p (modify x (* (1-bump)) mkt) what) / (2*bump*mkt x)
    | otherwise =
        (p (modify x (+bump) mkt) what -
         p (modify x (+ (-bump)) mkt) what) / (2*bump)
dvdx = dvdx' p mkt
dvdx2 what x bump = dvdx' (\ m w -> dvdx' p m w x bump) mkt what x bump
dvdd what x1 x2 bump = dvdx' (\ m w -> dvdx' p m w x2 bump) mkt what x1 bump

-- Достаточно близко в обоих случаях
-- λ> test' Rho 0.03 / symd (test' PV) 0.03 1 1e-4
-- 1.0000001694839284
-- λ> test' Rho 0.03 / sum [symd (test' PV) 0.03 x 0.0001 | x <- [0.3,0.7]]
-- 1.0000000627094483

-- λ> dvdx PV RateDom 0.000001
-- 806.7514432212874
-- λ> p mkt Rho
-- 806.7514432362166

mcError, integratedError :: N a => a
mcError = (1 - monteCarlo mkt / p mkt PV) * 100
integratedError = (1 - integrated mkt / p mkt PV) * 100

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

gaussianSM n =
--  runIdentity . State.Strict.evalStateT (replicateM n $ MWC.standard $ DummyGen ())
  take n . map invnormcdf . unfoldr (Just . SplitMix.nextDouble)
splitMixSplits n = take n $ split [SplitMix.mkSMGen 1337]
  where
    split gs = ss <> split ss
      where ss = concat [[a,b] | g <- gs, let (a,b) = SplitMix.splitSMGen g]

-- doesn't look to approach 1, more like jumping around 0.2-0.7
lawOfIteratedLogarithm = sum (take n $ map (\x -> (toEnum . fromEnum) x*2-1) $ unfoldr (Just . SplitMix.bitmaskWithRejection64' 1) (SplitMix.mkSMGen 1337))
  / sqrt (2*n * log (log n))
  where
    n :: Num a => a
    n = 5000000

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

gaussian :: Int -> [Double]
gaussian n
 =
    map (invnormcdf . corput2) [1..toEnum n]
--     take n $ map invnormcdf $ unfoldr (Just . SplitMix.nextDouble) (SplitMix.mkSMGen 1337)
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

--    1
--   1 1
--  1 2 1
-- 1 3 3 1
pascalTriangleRow n
  | n <= 1 = [1]
  | otherwise = let p = pascalTriangleRow (n-1) in
      zipWith (+) ([0]<>p) (p<>[0])

plot = void $ GP.plotDefault $
  Plot2D.function Graph2D.lines
  (linearScale 1000 (oStrike o - 1, oStrike o + 1::Double))
  (\x ->
--     blackSholesPricer
--       Option { oStrike = x, oMaturityInYears = 12/12, oDirection = Call } mkt PV
--    p (m Spot (const x)) PV
--    p (m RateDom (const x)) PV
--      R.diff
--      step (x - oStrike o)
--   getPv mkt (const x)
   dvdx' p (m Spot (const x)) PV Spot 0.0001
--    dvdx' p (m RateDom (const x)) PV RateDom 0.0001
  )
  `mappend`
  Plot2D.list Graph2D.boxes
  [(spotAtT mkt x (oMaturityInYears o), 0.5::Double)
  |x <- [-0.2,-0.199..0.2::Double]]

plotp = plotListStyle [] defaultStyle
  [(toEnum i :: Double, x / sum p) | (i,x) <- zip [start..end] (drop start p)]
  where
    p :: [Rational]
    p = pascalTriangleRow n -- sum [Double] overlows at 1100
    n = 2000
    plotN = 101
    start = (n-plotN)`div`2
    end = start + plotN - 1

plotg = plotListStyle [] defaultStyle-- {plotType = HiSteps}
  (hist 0.001
--   $ map (\ e -> spotAtT mkt e 0.5)
   $ gaussian 500000)
hist :: Double -> [Double] -> [(Double, Double)]
hist bucket l =
  map (\ (b,c) -> (toEnum b * bucket, toEnum c / toEnum (length l))) $
  IntMap.toList $ IntMap.fromListWith (+)
  [(floor (x / bucket) :: Int, 1::Int) | x <- l]

plot3d = plotFunc3d [] [] [0.5,0.51..1.5::Double] [0,0.1..1::Double]
  (\s mat ->
    blackSholesPricer
      Option { oStrike = s, oMaturityInYears = mat, oDirection = Call } (m Spot (const 1)) PV
  )

linInterpolate x (g:gs) = go g gs
  where
    go p@(px,py) (c@(cx,cy):cs)
      | x >= px && x <= cx = -- (p,c,head cs)
        ((x - px)/(cx-px))*(cy-py) + py
      | otherwise = go c cs

-- почему-то digital лучше чем vanilla?
-- и увеличение nx не увеличивает точность (хотя с exp(-3..3) vanilla уже
-- как в книжке, но digital по-прежнему лучше)
-- попробовать с triDiagSolve и большим nx

fem :: forall a . N a => Market a -> a
fem = fem' 500 500

fem' :: forall a . N a => Int -> Int -> Market a -> a
fem' nx nt market =
--  trace (printf "σ=%f, rd=%f, rf=%f, nx=%d, nt=%d, spot=[%.3f..%.3f], h=%.6f" (toDouble σ) (toDouble rd) (toDouble rf) nx nt (toDouble minSpot) (toDouble maxSpot) (toDouble h) :: String) $
--    plotListStyle [] defaultStyle $ map (first exp) $
--   take 50 $
  linInterpolate (log $ market Spot) $
  zipWith (,) (map iToLogSpot [1..nx]) (fst $ last iterations)
  -- LA.disp 1 $ LA.fromRows iterations
  where
    iterations = take (nt+1) (iterate ump1 (u0,0))
    τ = oMaturityInYears o - market PricingDate
    σ = market Vol
    rd = market RateDom
    rf = market RateFor
--    r = rd-rf -- так получается d rf = - d rd
    θ = 1 -- 1=implicit, 0=explicit -- oscilates, even with 0.5

    ump1 :: ([a], Int) -> ([a], Int)
    ump1 (um,i) =
      (solveTridiagTDMA
      (m .+ k i*θ .* a_bs) ((m .- k i*(1-θ) .* a_bs) #> um), succ i)
--       (_i .+ k i*θ .* g_bs) ((_i .- k i*(1-θ) .* g_bs) #> um), succ i)
--     nx = 500 :: Int
--     nt = 500 :: Int
    maxSpot, minSpot, h :: a
    maxSpot = exp 3    -- с вот этими уже как в книжке
    minSpot = exp (-3)
--     maxSpot = oStrike o * 3 / 2
--     minSpot = oStrike o     / 2
--     maxSpot = max s0 $ spotAtT market 8 τ
--     minSpot = min s0 $ spotAtT market (-1) τ
    s0 = market Spot
    k, iToT :: Int -> a
    k i = iToT (i+1) - iToT i
    iToT i = realToFrac ((toEnum i / toEnum nt)**β) * τ
    β = 1 -- market Vol / 2 -- ???
--    k = τ / (toEnum nt-1) -- time step
    h = (log maxSpot - log minSpot) / (toEnum nx+1) -- log spot step
    iToLogSpot i = toEnum i * h + log minSpot

    u0 :: [a]
    u0 = [getPv market (const $ realToFrac $ exp $ iToLogSpot x) / exp (-rd*τ) | x <- [1..nx]]

    s, b, m, a_bs :: Tridiag a
    a_bs = (σ^2/2) .* s .+ (σ^2/2-rd+rf) .* b .+ rd .* m
    s = (1/h) .* tridiag nx (-1) 2 (-1)
    b = (1/2) .* tridiag nx (-1) 0   1
    m = (h/6) .* tridiag nx   1  4   1

    g_bs = (σ^2/2) .* _r .+ (σ^2/2-rd+rf) .* _c .+ rd .* _i
    _i = tridiag nx 0 1 0
    _r = (1/h) .* s
    _c = (1/h) .* b

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

liftTridiag2 :: N a => (a -> a -> a) -> Tridiag a -> Tridiag a -> Tridiag a
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

solveTridiagTDMA :: N a => Tridiag a -> [a] -> [a]
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

-- integrated 100k ~ fem 500x100 ~ 15ms
main = defaultMain
  [ bgroup "fem" (map benchFem [(100,100), (100,500), (500,100), (500,500)])
  , bgroup "integrated" (map benchIntegrated [1000, 10000, 100000, 1000000])
  , bgroup "gaussian" (map benchGaussian [1000, 10000, 100000])
--   , bgroup "gaussianAcc" (map benchGaussianAcc [1000, 10000, 100000])
  , bgroup "tridiag" (map benchTridiag [128, 256, 512, 1024, 2048, 4096])
  , bgroup "generic" (map benchGeneric [128, 256, 512])
  ]
  -- triDiagSolve is linear for vector, but we use matrix
  -- triDiagSolve is O(n^2)   generic is O(n^3)
  --   128   0.2ms                5ms
  --   256   1ms                120ms >> 5*2^3=40, cache miss?
  --   512   4ms               1375ms  > 120*8=960
  -- x - x0 :: LA.Matrix Double
  where
    benchFem size = bench (show size) $ whnf (\(nx,nt) -> fem' nx nt mkt :: Double) size
    benchIntegrated size = bench (show size) $ whnf (\ s -> integrated' s mkt :: Double) size
    benchGaussian size = bench (show size) $ whnf (sum . gaussian) size
--    benchGaussianAcc size = bench (show size) $ whnf (sum . gaussianAcc) size
    benchTridiag size =
      bench (show size)
      $ whnf (\ (a,b,c,d) -> LA.triDiagSolve a b c d :: LA.Matrix Double) (dL,d,dU,i)
     where
      cvec s c = LA.fromList $ replicate s c
      !dL = cvec (size-1)   3.0
      !d  = cvec size      10.0
      !dU = cvec (size-1)   4.0
      !i  = LA.ident size
    benchGeneric size =
      bench (show size) $ whnf (uncurry (LA.<\>)) (m,i)
     where
      !m = laTridiag size 3 10 4 :: LA.Matrix Double
      !i = LA.ident size
    size = 250
    --         default                  +openblas
    --        <\>   triDiagSolve         <\>         triDiagSolve
    --   500  0.22  0.05                 0.33
    --  1000  1.3s  0.08                 1.7
    --  2000 17.8s  0.19                19.7           0.18
    -- 10000        3.8   -- not linear                4
--    x = x0 -- tridiag size 3 1 4 LA.<\> LA.ident size
--     b = (9 LA.>< 3)
--         [
--           1.0,   1.0,   1.0,
--           1.0,  -1.0,   2.0,
--           1.0,   1.0,   3.0,
--           1.0,  -1.0,   4.0,
--           1.0,   1.0,   5.0,
--           1.0,  -1.0,   6.0,
--           1.0,   1.0,   7.0,
--           1.0,  -1.0,   8.0,
--           1.0,   1.0,   9.0
--         ]
--    x0 = LA.triDiagSolve dL d dU (LA.ident size) -- b

{-
pkg load statistics;
pkg load financial;
r=0.05; sig=0.2; T=1; S0=110; K=100;
N = 1:1000000;
U = rand(1,max(N)); % uniform random variable
Y = norminv(U); % inverts Normal cum. fn.
S = S0*exp((r-sig^2/2)*T + sig*sqrt(T)*Y);
F = exp(-r*T)*max(0,S-K);
sum1 = cumsum(F); % cumulative summation of
sum2 = cumsum(F.^2); % payoff and its square
val = sum1./N;
rms = sqrt(sum2./N - val.^2);

[Call, Put] = blsprice (S0, K, r, T, sig)
% err = european_call(r,sig,T,S0,K,'value') - val;
err = Call - val;
plot(N,err, ...
N,err-3*rms./sqrt(N), ...
N,err+3*rms./sqrt(N))
axis([0 length(N) -1 1])
xlabel('N'); ylabel('Error')
legend('MC error','lower bound','upper bound')
-}

-- https://en.wikipedia.org/wiki/Van_der_Corput_sequence
corput :: Int -> Int -> Double
corput base n = go n rBase 0.0
  where
    rBase = recip $ toEnum base
    go !n !bk !q
      | n > 0 = go (n `div` base) (bk * rBase) (q + toEnum (n `mod` base)*bk)
      | otherwise = q

-- https://www.pbr-book.org/3ed-2018/Sampling_and_Reconstruction/The_Halton_Sampler
corput2 :: Word -> Double
corput2 (W# w) = (D# (word2Double# (wordReverseBits# w))) * 0x1p-64
-- λ> and [corput2 i == corput 2 (fromEnum i) | i <- [1..1000000]]
-- True

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
