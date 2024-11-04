{-# LANGUAGE LambdaCase, BangPatterns, ViewPatterns, MagicHash, RecordWildCards, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-x-partial #-}

module Main (module Main) where

import Control.DeepSeq
import Data.Number.Erf

import Data.Array
import Debug.Trace
import Data.Monoid
import Data.List.Split
import Criterion.Main
import Graphics.Gnuplot.Simple

import qualified Graphics.Gnuplot.Frame as Frame
import qualified Graphics.Gnuplot.Frame.Option as Opt
import qualified Graphics.Gnuplot.Frame.OptionSet as Opts
import qualified Graphics.Gnuplot.Advanced as GP
import qualified Graphics.Gnuplot.MultiPlot as MultiPlot

import qualified Graphics.Gnuplot.Graph as Graph

import qualified Graphics.Gnuplot.Plot.TwoDimensional as Plot2D
import qualified Graphics.Gnuplot.Plot.ThreeDimensional as Plot3D
import qualified Graphics.Gnuplot.Graph.TwoDimensional as Graph2D
import qualified Graphics.Gnuplot.Graph.ThreeDimensional as Graph3D
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
import Control.Monad.ST
import Control.Monad
import Data.List
import Control.Concurrent
import Control.Concurrent.Async
import System.IO.Unsafe
import Text.Printf

import Data.Reflection
import qualified Numeric.AD.Mode as AD
import qualified Numeric.AD.Mode.Reverse as R
import qualified Numeric.AD.Internal.Reverse as R
import qualified Numeric.AD.Jacobian as J

import qualified Data.Vector.Unboxed as U

import System.Process

import Random
import Tridiag
import Control.Concurrent.Chan
import Control.Concurrent.Async

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

data BarrierPosition
  = Upper
  | Lower
  deriving Show

data PayOn
  = PayOnTouch    -- ^ rebate paid at hit
  | PayOnEnd      -- ^ rebate paid at end
  deriving Show

data Option a
  = Option
    { oStrike :: a
    , oMaturityInYears :: a
    , oDirection :: OptionDirection
    }
data OneTouch a
  = OneTouch
    { otBarrier :: a
    , otBarrierPosition :: BarrierPosition
    , otPayOn :: PayOn
    , otMaturityInYears :: a
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

digiPricer :: Erf a => Option a -> Market a -> Greek -> a
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

blackScholesPricer :: Erf a => Option a -> Market a -> Greek -> a
blackScholesPricer o market what = case what of
  PV ->
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

pay1Pricer :: Erf a => OneTouch a -> Market a -> Greek -> a
pay1Pricer ot market PV = exp (-rd*τ)
  where
    τ = otMaturityInYears ot - market PricingDate
    rd = market RateDom

noTouchPricer :: Erf a => OneTouch a -> Market a -> Greek -> a
noTouchPricer ot market what =
  pay1Pricer ot market what - oneTouchPricer ot market what

oneTouchPricer :: Erf a => OneTouch a -> Market a -> Greek -> a
oneTouchPricer ot market PV =
  exp (-ω*rd*τ) *
  (  (b/x)**((θm+𝜗m)/σ) * nc (-η*ep)
   + (b/x)**((θm-𝜗m)/σ) * nc ( η*em))
  where
    b = otBarrier ot
    τ = otMaturityInYears ot - market PricingDate
    η = otη ot
    ω = otω ot
    x = market Spot
    σ = market Vol
    rd = market RateDom
    rf = market RateFor
    θp = (rd-rf)/σ + σ/2
    θm = (rd-rf)/σ - σ/2
    𝜗m = sqrt (θm^2 + 2*(1-ω)*rd)
    ep = ( log (x/b) - σ*𝜗m*τ) / (σ*sqrt τ)
    em = (-log (x/b) - σ*𝜗m*τ) / (σ*sqrt τ)
    nc = normcdf
    n = normdf

oφ o = case oDirection o of
  Call ->  1
  Put  -> -1

otη ot = case otBarrierPosition ot of
  Upper -> -1
  Lower ->  1

otω ot = case otPayOn ot of
  PayOnTouch -> 0
  PayOnEnd   -> 1

normdf t = exp (- t^2/2) / sqrt (2*pi)

forwardPricer :: Floating a => Forward a -> Market a -> Greek -> a
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

spotPath market dτ es =
  map ((s0 *) . exp) $
  scanl' (+) 0 [(μ̂ - σ^2/2)*dτ + σ*ϵ*sqrt dτ | ϵ <- es]
  where
    μ̂ = rd - rf
    s0 = market Spot
    σ = market Vol
    rd = market RateDom
    rf = market RateFor

pay1Pv :: N a => Option a -> Market a -> (a -> a) -> a
pay1Pv o market _ =
  exp (-rd*τ)
  where
    rd = market RateDom
    τ = oMaturityInYears o - market PricingDate

optionPv :: N a => Option a -> Market a -> (a -> a) -> a
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

digiOptionPv o market spotAt =
  exp (-rd*τ) * step (φ * (spotAt τ - k))
  where
    k = oStrike o
    τ = oMaturityInYears o - market PricingDate
    φ = oφ o
    rd = market RateDom

combine a b market what = a market what + b market what
scale s f market what = s * f market what


toDouble :: N a => a -> Double
toDouble = realToFrac

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

parMap :: (NFData a, NFData b) => Int -> (a -> b) -> [a] -> [b]
parMap nThreads f xs = unsafePerformIO $ do
  c <- newChan
  let grain = 100
      writer = do
        forM_ (chunksOf grain xs) $ \ chunk ->
          chunk `deepseq` writeChan c (Just chunk)
        forM_ [1..nThreads] $ const $ writeChan c Nothing
      reader acc = do
        chunk <- readChan c
        case chunk of
          Nothing -> return $ concat acc
          Just c ->
            let r = map f c in r `deepseq` reader (r:acc)
  fmap concat $ withAsync writer $ const $
    forConcurrently [1..nThreads] $ const $ reader []
-- map works faster than parMap :)
-- looks like a lot of fusion is lost, and more pressure on ram is added

monteCarlo :: N a => Market a -> a
monteCarlo mkt =
--   unsafePerformIO $
--  fmap sum $ forConcurrently (splitMixSplits threads) $ seqpure .
    (/ toEnum n) . treeSum . map (pv . spotPath mkt dt . map realToFrac)
    $ chunkedGaussian nt (n `div` threads)
  where
    seqpure a = a `seq` pure a
    pv xs = product [step (otBarrier ot - x) | x <- xs]
      * getPv mkt (const $ last xs)
    threads = 1
    nt = 500
    n = 5000
    τ = oMaturityInYears o - mkt PricingDate
    dt = τ / toEnum nt
    s0 = mkt Spot

_monteCarlo :: N a => Market a -> a
_monteCarlo mkt =
  treeSum [getPv mkt (spotAtT mkt (realToFrac ϵ)) | ϵ <- gaussianQuasiRandom n] / toEnum n
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
    n = 1000000

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
{-# SPECIALIZE monteCarlo :: Market Double -> Double #-}
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
ot :: Erf a => OneTouch a
ot = OneTouch
  { otBarrier = 1.1
  , otBarrierPosition = Upper
  , otPayOn = PayOnEnd
  , otMaturityInYears = oMaturityInYears o
  }
f :: Erf a => Forward a
f = Forward { fStrike = oStrike o, fMaturityInYears = oMaturityInYears o }

p :: N a => Market a -> Greek -> a
getPv :: N a => Market a -> (a -> a) -> a
-- p     = digiPricer o
-- getPv = digiOptionPv o
-- p     = blackScholesPricer o
-- getPv = optionPv o
p     = noTouchPricer ot
getPv = pay1Pv o

greeksBump = map (\ i -> dvdx PV i 0.00001) [Spot, Vol, RateDom, RateFor, PricingDate]
greeksBumpIntegrated = map (\ i -> dvdx' (const . integrated) mkt () i 0.00001) [Spot, Vol, RateDom, RateFor, PricingDate]
greeksBumpMonteCarlo = map (\ i -> dvdx' (const . monteCarlo) mkt () i 0.00001) [Spot, Vol, RateDom, RateFor, PricingDate]
greeksAnalytic = map (p mkt) [Delta, Vega, RhoDom, RhoFor, Theta, Gamma, Vanna] :: [Double]
greeksAD = snd $ jacobianPvGreeks (flip p PV)
greeksADMonteCarlo = snd $ jacobianPvGreeks monteCarlo

newtype Percent = Percent Double
instance Show Percent where show (Percent p) = printf "%.5f%%" p
pct a b
  | a == b = Percent 0
  | otherwise = Percent ((a / b - 1) * 100)

pv :: Double
(pv,greeks) = jacobianPvGreeks
  fem
-- σ=0.3, rd=0.05, rf=0.03, nx=500, nt=500, spot=[0.050..20.086], h=0.011976
-- [0.00076%,-0.06512%,-0.01311%,0.01374%,-0.06819%]
--       integrated
-- λ> zipWith pct greeks greeksBump
-- [-0.000%,0.014%,0.002%,-0.000%,0.013%] -- vanilla
-- [-0.015%,0.008%,-0.021%,-0.015%,0.039%] -- digi
     --monteCarlo
-- λ> zipWith pct greeks greeksBump
-- [-0.779%,1.087%,-1.034%,-0.779%,0.779%] -- vanilla
-- [-2.703%,-2.258%,-3.307%,-2.703%,-0.790%] -- digi
     -- digiPricer o
     -- [3.6661059215952516e-2,-0.2291316200997029,0.6795758158561364,-0.9165264803988129,3.744296366024975e-2] ~= greeksBump
     -- blackScholesPricer o
     -- [0.5644849344925212,13.74789720598219,11.847533227133829,-14.112123362313032,-4.744637550015519] epsEq greeksAnalytic

jacobianPvGreeks :: (forall a . N a => Market a -> a) -> (Double, [Double])
jacobianPvGreeks pricer =
  head $ R.jacobian' (\ [s,v,rd,rf,pd] ->
    [ pricer
      (\ case
        Spot -> s
        Vol -> v
        RateDom -> rd
        RateFor -> rf
        PricingDate -> pd)
    ])
    [mkt Spot, mkt Vol, mkt RateDom, mkt RateFor, mkt PricingDate]

--     `combine`
--     scale (-0.5)
--     (forwardPricer Forward { fStrike = 1.2, fMaturityInYears = 3/12 })
mkt :: Fractional a => Input -> a
mkt = \ case
    Spot -> 1
    Vol -> 0.1
    RateDom -> 0.05
    RateFor -> 0.02
    PricingDate -> 0
-- p = blackScholesPricer
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

plot = void $ GP.plotDefault $
  Plot2D.function Graph2D.lines
  (linearScale 1000 (oStrike o - 1, oStrike o + 1::Double))
  (\x ->
--     blackScholesPricer
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

plot3d = -- plotFunc3d [Custom "data" ["lines"],
--                      Custom "surface" [], Custom "hidden3d" []] [Plot3dType Surface]
  plotMeshFun
         [0.5,0.51..1.5::Double] [0,0.1..1::Double]
  (\s pd ->
    blackScholesPricer o (modify PricingDate (const pd) $ m Spot (const s)) PV
  )

plotMeshFun xs ys f = plotMesh [[(x, y, f x y) | x <- xs] | y <- ys]

plotMesh :: [[(Double, Double, Double)]] -> IO ()
plotMesh rows = do
  let dat = "mesh.dat"
      script = "script.plot"
  writeFile dat $ unlines [unlines [unwords $ map show [y,x,v] | (x,y,v) <- r] | r <- rows]
  writeFile script $ unlines $
    ["set view 60, 60"
--     "set view 90, 90"
    ,"set key off"
    ,"unset colorbox"
--     ,"set contour both"
    ,"set pm3d depthorder border lc 'black' lw 0.33"
    ,concat ["splot \"", dat, "\" ",
      -- "with lines palette lw 0.33"
      "with pm3d"
     ]
    ]
  void $ spawnCommand $ "gnuplot " <> script

linInterpolate x (g:gs) = go g gs
  where
    go p@(px,py) (c@(cx,cy):cs)
      | x >= px && x <= cx = -- (p,c,head cs)
        ((x - px)/(cx-px))*(cy-py) + py
      | otherwise = go c cs

-- почему-то digital лучше чем vanilla?
-- увеличение nx желательно сопровождать увеличением nt

fem :: forall a . N a => Market a -> a
fem = fem' 100 100

fem' :: forall a . N a => Int -> Int -> Market a -> a
fem' nx nt market =
--  trace (printf "σ=%f, rd=%f, rf=%f, nx=%d, nt=%d, spot=[%.3f..%.3f], h=%.6f" (toDouble σ) (toDouble rd) (toDouble rf) nx nt (iToSpot 0) (iToSpot (nx+1)) (toDouble h) :: String) $
  linInterpolate (log $ market Spot) $
  (\ prices -> unsafePerformIO $ do
      let toGraph = map (\(logSpot, v) -> (toDouble $ exp logSpot, toDouble v))
      -- plotListStyle [] defaultStyle $ toGraph prices
--       GP.plotDefault
--         $ Frame.cons
--           (Opts.grid True $
--            Opts.viewMap $
-- --            Opts.view 10 10 1 1 $
--            Opts.key False $
--            Opts.add (Opt.custom "hidden3d" "") [] $
--            Opts.deflt)
--         $ -- Graph3D.lineSpec (LineSpec.title "" LineSpec.deflt) <$>
--           Plot3D.mesh
      plotMesh
          [map (\(x,v) -> (x, toDouble $ iToT t, v)) $ toGraph $ addLogSpot l
          |(l,t) <- iterations]
--         foldMap
--         (noTitle .
--           Plot2D.list Graph2D.lines . toGraph . addLogSpot . fst) iterations
--         <>
--         noTitle (Plot2D.list Graph2D.dots [(iToSpot i, 1.05) | i <- [0..nx]])
      pure prices)
  $ addLogSpot (fst $ last iterations)
  -- LA.disp 1 $ LA.fromRows iterations
  where
    noTitle x = fmap (Graph2D.lineSpec (LineSpec.title "" LineSpec.deflt)) x
    addLogSpot iteration =
         [(iToLogSpot 0, 0)]
      <> zipWith (,) (map iToLogSpot [1..nx]) iteration
      <> [(iToLogSpot (nx+1), 0)]
    iterations = take (nt+1) (iterate ump1 (u0,0))
    τ = oMaturityInYears o - market PricingDate
    σ = market Vol
    rd = market RateDom
    rf = market RateFor
--    r = rd-rf -- так получается d rf = - d rd
    θ = 1 -- 1=implicit, 0=explicit -- oscilates, even with 0.5

    ump1 :: ([a], Int) -> ([a], Int)
    ump1 (um,mi) =
      (solveTridiagTDMA
      (m .+ k mi*θ .* a_bs) ((m .- k mi*(1-θ) .* a_bs) #> um), succ mi)
--       (i .+ k mi*θ .* g_bs) ((i .- k mi*(1-θ) .* g_bs) #> um), succ mi)
--     nx = 500 :: Int
--     nt = 500 :: Int
    (minSpot, maxSpot) = (exp (-3), otBarrier ot)
--     (minSpot, maxSpot) = (otBarrier ot, exp 3)
--     (minSpot, maxSpot) = (exp (-3), exp 3) -- так уже как в книжке
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
    iToSpot = toDouble . exp . iToLogSpot
    iToLogSpot i = toEnum i * h + log minSpot

    u0 :: [a]
    u0 = [getPv market (const $ realToFrac $ exp $ iToLogSpot x) / exp (-rd*τ) | x <- [1..nx]]

    s, b, m, a_bs :: Tridiag a
    -- FEM
    a_bs = (σ^2/2) .* s .+ (σ^2/2-rd+rf) .* b .+ rd .* m
    s = (1/h) .* tridiag nx (-1) 2 (-1)
    b = (1/2) .* tridiag nx (-1) 0   1
    m = (h/6) .* tridiag nx   1  4   1

    -- FDM
    g_bs = (σ^2/2) .* r .+ (σ^2/2-rd+rf) .* c .+ rd .* i
    r = (1/h) .* s
    c = (1/h) .* b
    i = tridiag nx 0 1 0

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
