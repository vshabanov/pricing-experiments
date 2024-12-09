{-# LANGUAGE MagicHash, ScopedTypeVariables, CPP #-}
{-# OPTIONS_GHC -Wno-gadt-mono-local-binds -Wno-ambiguous-fields #-}

module Main (module Main) where

import qualified Control.Exception as E
import Data.Char
import Control.DeepSeq
import Data.Number.Erf

import GHC.Generics
import qualified Control.Monad.State.Strict as S
import qualified Data.Map.Strict as Map
import Data.Array
import Debug.Trace
import Data.Monoid
import Data.List.Split
import Data.Foldable
import Data.Functor.Identity
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
import qualified Numeric.AD as AD
import qualified Numeric.AD.Mode as AD
import qualified Numeric.AD.Mode.Reverse as R
import qualified Numeric.AD.Internal.Reverse as R
import qualified Numeric.AD.Jacobian as J

import qualified Data.Vector.Unboxed as U
import Control.Concurrent.Chan
import Control.Concurrent.Async
import Numeric.GSL.Fitting
import Control.Comonad.Cofree

import System.Process

import Random
import Tridiag
import Market
import Tenor
import Analytic
import Symbolic
import Number

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

rates :: Market a -> Rates a
rates m = Rates{s = get Spot m, rf = get RateFor m, rd = get RateDom m}

digiPricer :: Erf a => Option a -> Market a -> Greek -> a
digiPricer o market what = case what of
  PV ->
    φ * exp (-rd*τ) * nc (φ*dm) -- digi
  where
    k = oStrike o
    τ = oMaturityInYears o - m PricingDate
    φ = directionφ $ oDirection o
    x = m Spot
    σ = impliedVol market τ k
    rd = m RateDom
    rf = m RateFor
    nc = normcdf
    f = x * exp ((rd-rf)*τ)
    dm = (log (f/k) - σ^2/2*τ) / (σ*sqrt τ)
    m i = get i market

blackScholesPricer :: Erf a => Option a -> Market a -> Greek -> a
blackScholesPricer o market greek = bs greek BS{..}
  where
    k = oStrike o
    d = oDirection o
    t = oMaturityInYears o - m PricingDate
    s = m Spot
    σ = impliedVol market t k
    rf = m RateFor
    rd = m RateDom
    m i = get i market

pay1Pricer :: Erf a => OneTouch a -> Market a -> Greek -> a
pay1Pricer ot market PV = exp (-rd*τ)
  where
    τ = otMaturityInYears ot - m PricingDate
    rd = m RateDom
    m i = get i market

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
    τ = otMaturityInYears ot - m PricingDate
    η = barrierPositionη $ otBarrierPosition ot
    ω = payOnω $ otPayOn ot
    x = m Spot
    σ = impliedVol market τ b
    rd = m RateDom
    rf = m RateFor
    θp = (rd-rf)/σ + σ/2
    θm = (rd-rf)/σ - σ/2
    𝜗m = sqrt (θm^2 + 2*(1-ω)*rd)
    ep = ( log (x/b) - σ*𝜗m*τ) / (σ*sqrt τ)
    em = (-log (x/b) - σ*𝜗m*τ) / (σ*sqrt τ)
    nc = normcdf
    n = normdf
    m i = get i market

forwardPricer :: Floating a => Forward a -> Market a -> Greek -> a
forwardPricer f market what = case what of
  PV ->
    x * exp ((-rf)*τ) - k * exp ((-rd)*τ)
  where
    Strike k = fStrike f
    MaturityInYears mat = fMaturityInYears f
    τ = mat - m PricingDate
    x = m Spot
    rd = m RateDom
    rf = m RateFor
    m i = get i market

-- | ϵ -- a sample from a normal distribution with mean=0 and stddev=1
spotAtT market ϵ τ =
  s0 * exp ((μ̂ - σ^2/2)*τ + σ*ϵ*sqrt τ)
  where
    μ̂ = rd - rf
    s0 = m Spot
    σ = impliedVol market τ (oStrike o)
    rd = m RateDom
    rf = m RateFor
    m i = get i market

spotPath market dτ es =
  map ((s0 *) . exp) $
  scanl' (+) 0 [(μ̂ - σ^2/2)*dτ + σ*ϵ*sqrt dτ | ϵ <- es]
  where
    μ̂ = rd - rf
    s0 = m Spot
    σ = impliedVol market (dτ * intToN (length es)) (oStrike o)
    rd = m RateDom
    rf = m RateFor
    m i = get i market

pay1Pv :: N a => Option a -> Market a -> (a -> a) -> a
pay1Pv o market _ =
  exp (-rd*τ)
  where
    rd = m RateDom
    τ = oMaturityInYears o - m PricingDate
    m i = get i market

optionPv :: N a => Option a -> Market a -> (a -> a) -> a
optionPv o market spotAt =
  exp (-rd*τ) * -- log1pexp (payoff * scale) / scale
  step payoff * payoff
  -- max payoff 0
  where
    scale = 1e10 -- better with 100, but doesn't break with 1e10
    payoff = φ * (spotAt τ - k)
    k = oStrike o
    τ = oMaturityInYears o - m PricingDate
    φ = directionφ $ oDirection o
    rd = m RateDom
    m i = get i market

digiOptionPv o market spotAt =
  exp (-rd*τ) * step (φ * (spotAt τ - k))
  where
    k = oStrike o
    τ = oMaturityInYears o - m PricingDate
    φ = directionφ $ oDirection o
    rd = m RateDom
    m i = get i market

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

parMapSum :: (Num b, NFData a, NFData b) => Int -> (a -> b) -> [a] -> b
parMapSum nThreads f xs = unsafePerformIO $ do
  c <- newChan
  let grain = 100
      writer = do
        forM_ (chunksOf grain xs) $ \ chunk ->
          chunk `deepseq` writeChan c (Just chunk)
        forM_ [1..nThreads] $ const $ writeChan c Nothing
      reader acc = do
        chunk <- readChan c
        case chunk of
          Nothing -> return $! treeSum acc
          Just c ->
            let r = treeSum $ map f c in r `deepseq` reader (r:acc)
  fmap sum $ withAsync writer $ const $
    forConcurrently [1..nThreads] $ const $ reader []
-- in GHCi map works faster than parMap or forConcurrently :)
-- despite they use more CPU
-- ByteCode thing?
-- parMap лучше чем forConcurrently, но возможно из-за неравномерной загрузки

monteCarlo :: N a => Market a -> a
monteCarlo market =
--   unsafePerformIO $
--   fmap sum $ forConcurrently (splitMixSplits threads) $ seqpure .
  -- Jacobian похоже тоже надо внутри нитки делать
  -- зависает в каких-то блокировках
    (/ n) . parMapSum 8 (pv . spotPath market dt . map realToFrac)
    $ chunkedGaussian nt (n `div` threads)
  where
    seqpure a = a `seq` pure a
    pv xs = product [step (otBarrier ot - x) | x <- xs]
      * getPv mkt (const $ last xs)
    threads = 1
    nt, n :: Num a => a
    nt = 500
    n = 50000
    τ = oMaturityInYears o - m PricingDate
    dt = τ / nt
    s0 = m Spot
    m i = get i market

_monteCarlo :: N a => Market a -> a
_monteCarlo mkt =
  treeSum [getPv mkt (spotAtT mkt (realToFrac ϵ)) | ϵ <- gaussianQuasiRandom n] / n
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
    1.3
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
p     = blackScholesPricer o
getPv = optionPv o
-- p     = noTouchPricer ot
-- getPv = pay1Pv o

mapInputs f = -- zip is $
  map f is :: [Double]
  where
    is = map fst $ inputs mkt
greeksBumpImpliedVol = mapInputs (\ i -> dvdx' (\m -> impliedVol m (1.1 + get PricingDate m)) mkt 1 i 0.00001)
greeksADImpliedVol = snd $ jacobianPvGreeks (\m -> impliedVol m (1.1 + get PricingDate m) 1)
greeksBumpLocalVol = mapInputs (\ i -> dvdx' (\m -> localVol m (1.1 + get PricingDate m)) mkt 1 i 0.00001)
greeksADLocalVol = snd $ jacobianPvGreeks (\m -> localVol m (1.1 + get PricingDate m) 1)
greeksBump = mapInputs (\ i -> dvdx PV i 0.00001)
greeksBumpIntegrated = mapInputs (\ i -> dvdx' (const . integrated) mkt () i 0.00001)
greeksBumpMonteCarlo = mapInputs (\ i -> dvdx' (const . monteCarlo) mkt () i 0.00001)
greeksAnalytic = map (p mkt) [Delta, Vega, RhoDom, RhoFor, Theta-- , Gamma, Vanna
                             ] :: [Double]
compareToAnalytic !g =
  map (\(g,is) -> p mkt g `pct` sum (mapMaybe (flip lookup gs) is)) mapping
  where
    gs = zip (map fst $ inputs (mkt :: Market Double)) g
    mapping =
      [(Delta, [Spot])
      ,(Vega, [i | (i@(Vol _ ATMVol),_) <- gs])
      ,(RhoDom, [RateDom])
      ,(RhoFor, [RateFor])
      ,(Theta, [PricingDate])]
greeksAD = snd $ jacobianPvGreeks (flip p PV)
greeksADMonteCarlo = snd $ jacobianPvGreeks monteCarlo

newtype Percent = Percent { unPercent :: Double }
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
  R.grad' (\ xs ->
    pricer $ modifyList (zip (map (coerceGet . fst) is) (map const xs)) mkt)
    (map snd is)
  where
    is = inputs mkt

--     `combine`
--     scale (-0.5)
--     (forwardPricer Forward { fStrike = 1.2, fMaturityInYears = 3/12 })
mkt :: N a => Market a
mkt = buildMarket $ do
--   s <- input Spot 1
--   rf <- input RateFor 0.03
--   rd <- input RateDom 0.05
  s <- input Spot 1.3465
  rf <- input RateFor 0.0346 -- discount 0.966001?  exp (-0.0346) = 0.965992
  rd <- input RateDom 0.0294 -- discount 0.971049?  exp (-0.0294) = 0.971028
  pd <- input PricingDate 0

--   let flatRow tenor x = do
--         i <- input (Vol tenor ATMVol) x
--         pure $ (\ i -> VolTableRow tenor i 0 0 0 0) <$> i
--   v1 <- flatRow  "11M" 0.1
--   v2 <- flatRow "13M" 0.2
--   node ImpliedVol $ atmVol <$> sequenceA [v1, v2]
  let flatRow tenor x = do
        i <- input (Vol tenor ATMVol) x
        pure $ (\ i -> VolTableRow tenor i 0 0 0 0) <$> i
  let rowNode VolTableRow{t=t,..} = do
        inputs <- sequence
          [input (Vol t ATMVol) σatm
          ,input (Vol t RR25)   σrr25
          ,input (Vol t BF25)   σbf25
          ,input (Vol t RR10)   σrr10
          ,input (Vol t BF10)   σbf10]
        pure $ (\ [σatm, σrr25, σbf25, σrr10, σbf10] -> VolTableRow{..})
          <$> sequenceA inputs
  surf <- mapM rowNode testSurface
  node Smile $ smileAtT <$> sequenceA surf <*> (Rates <$> s <*> rf <*> rd)

instance (Show t, N a) => Show (VolTableRow t a) where
  show (VolTableRow {..}) =
    printf "%3s %7.3f %7.3f %7.3f %7.3f %7.3f"
      (show t) (toD σatm) (toD σrr25) (toD σbf25)
      (toD σrr10) (toD σbf10)

g = forM_ [0.5] -- [0.01,0.02..2]
  $ \ t -> do
  print t
  volSens (\ mkt -> impliedVol mkt (toN t) 1.3)
    `E.catch` \ (e :: E.SomeException) -> print e

volSens :: (forall a . N a => Market a -> a) -> IO ()
volSens f = putStrLn $ unlines
  [printf "%-15s %12.6g %12.6g %15s" (show v) x d (show $ d `pct` x)
  |((v@Vol {},_), x) <- zip (inputs mkt) $ snd $ jacobianPvGreeks f, x /= 0
  ,let d = dvdx' (\ m () -> f m) mkt () v 0.000001
  ]

smile :: N a => VolTableRow (Expr a) (Expr a) -> Rates a -> Smile a
smile v@VolTableRow{t,σatm,σbf25,σrr25} (fmap lift -> rates@Rates{s,rf,rd}) =
--   trace (unlines $
--       [ printf "%-12s %.8f  %.5f%%" n (toD k) (toD $ solvedS k * 100)
--       | (n::String,k) <-
--         [("k25-d-P"   , k25dp)
--         ,("k25-d-P-MS", k25dpMS)
--         ,("kDNS"      , kDNS)
--         ,("k25-d-C"   , k25dc)
--         ,("k25-d-C-MS", k25dcMS)]]
--       <>
--       [ printf "%-12s %10.7f" n (toD p) -- (show p)
--       | (n::String,p) <-
--         [("σatm", σatm)
--         ,("σbf25", σbf25)
--         ,("σrr25", σrr25)
--         ,("σ25dSS", σ25dSS)
--         ,("σ25dSS via smile", 1/2*(solvedS k25dc + solvedS k25dp) - solvedS kDNS)
--         ,("t", t)
--         ,("f", f)
--         ,("v25dMS", v25dMS)
-- --         ,("vMS", vStrangle env k25dpMS (solvedS k25dpMS) k25dcMS (solvedS k25dcMS))
-- --         ,("vSS", vStrangle env k25dp   (solvedS k25dp)   k25dc   (solvedS k25dc))
--         ,("c0", c0)
--         ,("c1", c1)
--         ,("c2", c2)
--         ]]) $
--  trace (show ("partials", f, c0, partials c0))
  Smile_
  { smileImpliedVol = unlift . solvedS . lift
  , smileLocalVol = \ k ->
      -- diff solvedS t -- 79k(118k not simplified)
--      (trace $ show $ length $ show $ diff (solvedS $ lift k) t) $
      unlift $ (diff (solvedS $ lift k) t)
  }
{-
λ> bumpDiff (\ t -> localVol mkt (1.1+t) 1) 0 0.0001
2.2016559180458584e-3
λ> AD.grad (\ [t] -> localVol mkt (1.1+t) 1) [0]
[-0.23278584935191213]
λ> localVol mkt 1.1 1
-5.815826767965754e-3
λ> bumpDiff (\ t -> impliedVol mkt (1.1+t) 1) 0 0.0001
-5.815826784605349e-3
λ> AD.grad (\ [t] -> impliedVol mkt (1.1+t) 1) [0]
[-5.815826767967286e-3]
-}
  -- d/dt
--   -5.815826767965754e-3 -- symbolic
--   -5.81582676796051e-3  -- ad impliedVol
--   -5.81582671188574e-3  -- bump impliedVol
  -- d2/dt2 is wrong
--   -0.23278584935191496  -- ad of symbolic d/dt
--   -0.23278584935190863  -- symbolic
--    2.1988660892091616e-3 <<< bump, a close to correct one
--  we need explicitD tower, having explicitD a b -> a * d b
--  is not enough, need to play with newton to get a second derivative
  where
    pi n k s = printf "%-12s %.4f  %.5f%% (table %.5f%%)" n (toD k) (toD $ solvedS k * 100) (toD $ s*100)
    f = forwardRate rates t -- F_0,T
    kDNS = f * exp (1/2 * σatm^2 * t) -- K_DNS;pips
    solvedS = -- trace (show $ toD kDNS)
      polynomialInDeltaExpC0 f t [c0,c1,c2]
    ϕRR :: Num a => a
    ϕRR = 1 -- convention, could be -1

    -- input variables passed between solvers
    #define env (T11 f s rf rd t σatm σrr25 kDNS k25dpMS k25dcMS v25dMS)

    T5 c0 c1 c2 k25dp k25dc = fitSS env σ25dSS

    [σ25dSS] = -- [σbf25]
      fitSystemThrow env [σbf25] $ \ env [σ25dSS] ->
      let T5 c0 c1 c2 _k25dp _k25dc = fitSS env σ25dSS
          sm = polynomialInDeltaExpC0 f t [c0,c1,c2]
      in
        [vStrangle env k25dpMS (sm k25dpMS) k25dcMS (sm k25dcMS) === v25dMS]
    fitSS env σ25dSS =
      fitSystemThrow (T σ25dSS env) (T5 (-2) (-0.1) 0.1 k25dpMS k25dcMS)
                 $ \ (T σ25dSS env) (T5 c0 c1 c2 k25dp k25dc) ->
      let sm = polynomialInDeltaExpC0 f t [c0,c1,c2]
          delta d k = bs Delta BS{k,d,σ=sm k,s,rf,rd,t}
          -- PipsForwardDelta
      in
      -- Converges on the vol table, and on BF=RR=0
      -- but fails on BF=1% and RR=0 or some other number
      -- seems that polynomialInDeltaExpC0 is not flexible enough
      -- for pure symmetric smiles.
      [ sm kDNS === σatm
--       , ϕRR*(sm k25dc - sm k25dp) === σrr25
--       , 1/2*(sm k25dc + sm k25dp) - sm kDNS === σ25dSS
      , sm k25dc === sm k25dp + σrr25
      , 1/2*(sm k25dc + sm k25dp) === sm kDNS + σ25dSS
        --  ^ reordered to use division in (===) for better error estimates
      , delta Put  k25dp === -0.25 -- smile 25D, not Black-Scholes
      , delta Call k25dc ===  0.25
      ]
    v25dMS = vStrangle env k25dpMS (σatm+σbf25) k25dcMS (σatm+σbf25)
    vStrangle env kp σp kc σc =
        bs PV BS{k=kp,d=Put ,σ=σp,s,rf,rd,t}
      + bs PV BS{k=kc,d=Call,σ=σc,s,rf,rd,t}

    #undef env

    #define env (T6 σatm σbf25 t s rf rd)

    T2 k25dpMS k25dcMS =
      fitSystemThrow env (T2 kDNS kDNS) $ \ env (T2 kp kc) ->
        let delta d k = bs Delta BS{k,d,t,s,rf,rd,σ=σatm+σbf25} in
        [delta Put  kp === -0.25
        ,delta Call kc ===  0.25]

-- | Traversable cons @T var traversable@
data T t a = T a (t a)
  deriving (Show, Functor, Foldable, Traversable)
data T1 a  = T1 { unT1 :: a }
  deriving (Show, Functor, Foldable, Traversable)
data T2 a  = T2 a a
  deriving (Show, Functor, Foldable, Traversable)
data T3 a  = T3 a a a
  deriving (Show, Functor, Foldable, Traversable)
data T4 a  = T4 a a a a
  deriving (Show, Functor, Foldable, Traversable)
data T5 a  = T5 a a a a a
  deriving (Show, Functor, Foldable, Traversable)
data T6 a  = T6 a a a a a a
  deriving (Show, Functor, Foldable, Traversable)
data T7 a  = T7 a a a a a a a
  deriving (Show, Functor, Foldable, Traversable)
data T8 a  = T8 a a a a a a a a
  deriving (Show, Functor, Foldable, Traversable)
data T9 a  = T9 a a a a a a a a a
  deriving (Show, Functor, Foldable, Traversable)
data T10 a = T10 a a a a a a a a a a
  deriving (Show, Functor, Foldable, Traversable)
data T11 a = T11 a a a a a a a a a a a
  deriving (Show, Functor, Foldable, Traversable)

iainsTable3_5 :: Fractional a => (String -> a -> a -> b) -> [b]
iainsTable3_5 f0 =
  [f "k25-d-P"    1.2034 19.50
  ,f "k25-d-P-MS" 1.2050 19.48
  ,f "kATM"       1.3620 18.25
  ,f "k25-d-C"    1.5410 18.90
  ,f "k25-d-C-MS" 1.5449 18.92]
  where f n k s = f0 n k (s/100)

iainsDiff = mapM_ putStrLn $ iainsTable3_5 $ \ n k s ->
  printf "%-12s %.4f  %.2f%% (table %.2f%%, %9s)" n k (iains k * 100) (s*100)
  (show $ iains k `pct` s)
iains x = polynomialInDeltaExpC0 1.3395163731662 1
--  [-1.701005, 0.050131, 0.800801]
--  ^ example in the book is wrong, values don't match iainsTable3_5
  [-1.4606627150883185,-1.0877333376976042,1.2259367762563833]
  --  ^ these have 0.034% error (0.024% max)
  x
iainsCS :: [Double] =
  fitSystemThrow [] [-2,-0.1,0.1]
             $ \ [] [c0,c1,c2] ->
    iainsTable3_5 $ \ _ k σ ->
      polynomialInDeltaExpC0 1.3395163731662 1 [c0,c1,c2] k === σ
      -- doesn't converge, 1e-5 error

polynomialInDelta f t [c0,c1,c2,c3] k = exp $ fun $ log (f / k)
  where
    fun x = c0 + c1*δ x + c2*δ x^2 -- + c3*d x^3
    -- can't fit c3, maybe it'll work with rr10/bf10
    σ0 = c3
    δ x = normcdf (x / (σ0 * sqrt t))
    -- normcdf of standartized moneyness

testDiff = writeFile "test.maxima" $ unlines $
  [def "p" p]
  <>
  foldMap (\ v ->
    [def ("p"<>v)      $ simplify $       diff p (var v)
    ,def ("p"<>v<>"2") $ simplify $ diff (diff p (var v)) (var v)
    ,printf "mp%s:diff(p,%s)$" v v
    ,printf "mp%s2:diff(p,%s,2)$" v v
    ,printf "print(\"d%s  is the same: \", is(equal(p%s,mp%s)));" v v v
    ,printf "print(\"d%s2 is the same: \", is(equal(p%s2,mp%s2)));" v v v
    ])
    ["x", "f", "t", "c0", "c1", "c2", "x"]
--   <>
--   ["subst([x=1,f=1,t=1],mpx);" -- /=0
--   ,"subst([x=1,f=1,t=1],px);"  --  =0
--   ]
  where
    def n e = mconcat [n, ":", toMaxima e, "$"]
    p = polynomialInDeltaExpC0 "f" "t" ["c0","c1","c2"] "x" :: Expr Double


polynomialInDeltaExpC0 f t [c0,c1,c2] k =
--  c0 + c1*(f/k) + c2*(f/k)^2
--  ^ fits very nice, but has huge negative numbers on range ends
  exp $ fun $ log (f / k)
  where
    fun x = c0 + c1*δ x + c2*δ x^2
    σ0 = exp c0
    δ x = normcdf (x / (σ0 * sqrt t))

-- -- | df(x0..xn-1, t) / dt
-- deriv :: N a => (forall a . N a => [a] a -> a) -> [a] -> a -> a

infix 4 === -- same as ==

x === y = (x - y)/y  -- /y may cause division by zero

smileAtT :: N a => [VolTableRow Tenor a] -> Rates a -> a -> Smile a
smileAtT surface rates = flip smile rates . volTableRow surface

-- | variable for 't'
tagVolT = tag "volT"

volTableRow :: N a => [VolTableRow Tenor a] -> a -> VolTableRow (Expr a) (Expr a)
volTableRow surface = \ (tagVolT . lift -> t) -> case Map.splitLookup (toD t) rows of
  (_, Just r, _) -> r { Analytic.t = t }
    -- FIXME: interpolate both upper and lower sections with two
    --        crossing step functions to make on-pillar AD Theta
    --        closer to the bump Theta?
  (l, _, r) -> case (Map.lookupMax l, Map.lookupMin r) of
    (Just (t1, r1), Just (t2, r2)) ->
      let i w f = interp t t1 t2 w (f r1) (f r2) in
        VolTableRow
        { t = t
        , σatm  = i "ATM" $ \VolTableRow{σatm} -> σatm
        , σrr25 = - i "RR25" (\VolTableRow{σrr25} -> abs σrr25)
          -- TODO: it makes no sense to interpolate difference between volatilities
          -- we should first calibrate two smiles, get kATM/P25/C25,
          -- their vols, interpolate strikes and vols
          -- and calibrate new smile.
          -- interpolate like all delta conventions are the same
        , σbf25 = i "BF25" $ \VolTableRow{σbf25} -> σbf25
        , σrr10 = i "RR10" $ \VolTableRow{σrr10} -> σrr10
        , σbf10 = i "BF10" $ \VolTableRow{σbf10} -> σbf10
        }
    (Just (_,  r1), _            ) -> r1 { Analytic.t = t }
    (_            , Just (t2, r2)) -> r2 { Analytic.t = t }
    _ -> error "volTableRow: empty vol surface"
  where
    rows = Map.fromList
      [(tenorToYear t, lift <$> r) | r@VolTableRow{..} <- surface]
    interp t (toN -> t1) (toN -> t2) (what::String) v1 v2 =
      -- Iain Clark, p65, Flat forward interpolation
      let v12 = (v2^2*t2 - v1^2*t1) / (t2 - t1) in
      if toD v12 < 0 then
        error $ printf "volTableRow: negative %s forward variance v12 = %.8f, t1=%f, v1=%f, t2=%f, v2=%f"
          what (toD v12) (toD t1) (toD v1) (toD t2) (toD v2)
      else
        sqrt $ (v1^2*t1 + v12 * (t - t1)) / t

testSurface :: N a => [VolTableRow Tenor a]
testSurface =
  -- Copied from Iain Clark, p64, EURUSD
  --             ATM
  --  Exp     Bid     Ask    25D RR   25D BF   10D RR   10D BF
  [r  "1D"   7.556   8.778  (-0.636)   0.084  (-1.251)  0.299
  ,r  "1W"  11.550  12.350  (-1.432)   0.270  (-2.540)  0.840
  ,r  "2W"  11.650  12.300  (-1.510)   0.257  (-2.750)  0.808
  ,r  "3W"  11.490  12.030  (-1.558)   0.265  (-2.857)  0.823
  ,r  "1M"  11.540  12.040  (-1.660)   0.260  (-3.042)  0.795
  ,r  "2M"  11.605  12.006  (-1.667)   0.315  (-3.075)  0.990
  ,r  "3M"  11.795  12.195  (-1.677)   0.365  (-3.103)  1.165
--   ,r  "6M"  12.340  12.690  (0)   0  (-3.132)  1.460
  ,r  "6M"  12.340  12.690  (-1.680)   0.445  (-3.132)  1.460
--   ,r  "1Y"  18.25  18.25  (-0.6)   0.95  (-1.359)  3.806 -- Table 3.3 p50
  ,r  "1Y"  12.590  12.915  (-1.683)   0.520  (-3.158)  1.743
  ,r "18M"  12.420  12.750  (-1.577)   0.525  (-3.000)  1.735
  ,r  "2Y"  12.315  12.665  (-1.520)   0.495  (-2.872)  1.665
  ,r  "3Y"  11.915  12.310  (-1.407)   0.457  (-2.683)  1.572
  ,r  "5Y"  11.075  11.520  (-1.183)   0.417  (-2.217)  1.363
  ,r  "7Y"  11.144  10.626  (-1.205)   0.353  (-2.382)  1.157
  ]
  where
    r tenor bid ask rr25 bf25 rr10 bf10 =
      VolTableRow tenor (p (bid+ask) / 2) (p rr25) (p bf25) (p rr10) (p bf10)
    p x = x / 100

-- p = blackScholesPricer
--     $ Option { oStrike = 300, oMaturityInYears = 0.001, oDirection = Call }
-- mkt = \ case
--     Spot -> 300
--     Vol -> 0.21058845741208643
--     RateDom -> 0.03
--     RateFor -> 0.01
--     PricingDate -> 0

test' what rd = p (modify RateDom (const rd) mkt) what

m inp f = modify inp f mkt

--solvePriceToVol price = solve (\ x -> p (modify ImpliedVol (const $ const x) mkt) PV - price)

--fitTest :: [(Double, [Double])]
fitTest :: N a => (a, [[a]], [a])
fitTest = (d2xda2Bump, R.jacobian system is, system is)
  where
    d2xda2Bump = bumpDiff2 (\ x -> head $ system [a+x]) 0 0.0001
    is@[a] = [1]
    system inputs =
      (\ [a] -> fitSystemThrow [a] [1] $ \ [a] [x] ->
      [  a*x^2 - 4
      ]) inputs
--     d2xda2Bump = bumpDiff (\ x -> head $ system [a+x,b,c]) 0 0.0001
--     is@[a,b,c] = [1,1,1]
--     system inputs =
--       (\ [a,b,c] -> fitSystemThrow [a,b,c] [0.5, 0.5, 0.5] $ \ [a,b,c] [x,y,z] ->
--       [  x^2 + b*y^3 - 9
--       ,a*x^2 -   y      - c
--       ,  y - x - z^2
--       ]) inputs
--       попробовать с "системой" из одного уравнения x^2 - 4
--       первая производная 2x = 4
--       вторая производная 2

-- | Replace elements of 'Traversable'
-- @replace t (toList t) = t@
replace :: Traversable t => [a] -> t b -> t a
replace l t = S.evalState (mapM (const $ S.state (\ (x:xs) -> (x,xs))) t) l

fitSystemThrow1
  :: (Traversable i, N a)
  => i a -- ^ n inputs
  -> a -- ^ guess
  -> (forall a . N a => i a -> a -> a) -- ^ n inputs -> guess -> error
  -> a -- ^ result with derivatives to inputs
fitSystemThrow1 i g f = unT1 $ fitSystemThrow i (T1 g) (\ i (T1 g) -> [f i g])

fitSystemThrow
  :: (Traversable i, Traversable r, N a, Show (r a))
  => i a -- ^ n inputs
  -> r a -- ^ m guesses
  -> (forall a . N a => i a -> r a -> [a]) -- ^ n inputs -> m guesses -> me errors
  -> r a -- ^ results with derivatives to inputs
fitSystemThrow i g f = either error id $ fitSystem i g f

-- | Solve a system of non-linear equations for a set of inputs.
--
-- Uses Levenberg-Marquardt fitting from GSL with jacobians computed
-- using AD.
--
-- Results have derivatives to inputs computed via the implicit
-- function theorem.
--
-- Can be used to plug a model parameters calibration
-- (m parameters -> m equations = 0) into an AD framework.
fitSystem
  :: (Traversable i, Functor i, Traversable r, Functor r, N a, Show (r a))
  => i a -- ^ n inputs
  -> r a -- ^ m guesses
  -> (forall a . N a => i a -> r a -> [a]) -- ^ n inputs -> m guesses -> me errors
  -> Either String (r a) -- ^ results with derivatives to inputs
fitSystem inputs guesses system0
  | me < m = error $ mconcat ["Can’t fit ", show m, " variables with "
    , show me, " equations"]
  | err > 1e-10 = -- Sum of squared residuals (sum . map (^2))
    -- if there's a big error, there's a big chance that
    --  * LA.inv will fail with a singular matrix
    --  * LA.inv will not fail, but derivatives will be incorrect
    --    (either completely missing out some of the dependencies,
    --    or be off)
    Left $ printf
      ("Didn't converge after %.0f iterations:\n" <>
      "  error           %10.3g\n" <>
      "%s" <>
      "  inputs          %s\n" <>
      "  initial guesses %s\n" <>
      "  last guesses    %s\n" <>
      "  difference      %s")
    nIterations err
    (unlines $
     zipWith (\ i e -> printf "    %2d %10.7f%%" (i::Int) (e*100))
       [0..] $ system inputsD lastGuesses)
    (showDL inputsD) (showDL guessesD) (showDL lastGuesses)
    (unwords $ map fmtP $ zipWith pct lastGuesses guessesD)
  | otherwise =
--   trace (show path) $
--   map realToFrac results
  Right $ flip replace guesses $ zipWith
    (\ r dis ->
      realToFrac r + sum (zipWith (\ d i -> explicitD (toN d) i (toD i)) (LA.toList dis) inputsL))
    results (
      trace (
          unlines $
          zipWith (\ n _g -> printf "depends(g%d,[%s]);" (n::Int)
             (intercalate "," (map show $ vars "i" inputs)) :: String)
            [0..] (toList guesses)
          <>
          zipWith (\ n e -> printf "e%d:%s;" (n::Int) (toMaxima e) :: String)
            [0..] (system (vars "i" inputs) (vars "g" guesses))
{-
it's easy to have a derivative of the implicit function in a symbolic form
(expressions get massive for 5x5 matrix, but it works)

matrix([-invert(jacobian([x^2+y^2-1],[y]))]) . jacobian([x^2+y^2-1],[x]);

depends([f,g,h,i,j],[x,y,z,w,v]);

(-invert(jacobian([f,g],[x,y])) . jacobian([f,g],[w]));

/* d2x/dy2 */
diff(matrix([-invert(jacobian([f],[x]))]) . jacobian([f],[y]), y);

diff((-invert(jacobian([f,g,h],[x,y,z])) . jacobian([f,g,h],[w,v]))[1,1], w);
-}
-- # solve([diff(e0)=0], diff(g0,i0));
--           <>
-- solve([diff(e2)=0], diff(g0,i8)); -- very long
--           map (\ n -> printf "solve([diff(e0, i0) = 0], diff(g0,i0));
      ) $
--       trace (show (jr results, "inv", LA.inv (jr results), guesses, inputsD, results, ji inputsD, jResultsInputs)) $
      LA.toRows jResultsInputs)
  where
    fmtP (Percent p)
      | abs p < 5 && abs p > 0.0001 = printf "%9.5f%%" p
      | otherwise = printf "%10.3e" (p/100)
    fmtD = printf "%10.3g" -- 1.123e-197 is 10 characters
    showDL = unwords . map fmtD
    (nIterations:err:lastGuesses) = LA.toList $ last $ LA.toRows path
    me = length $ system0 inputs guesses -- determine the number of equations
    system is gs
      | length es /= me = error $ "system returned " <> show (length es)
        <> " equations instead of " <> show me
      | otherwise = es
      where es = system0 (replace is inputs) (replace gs guesses)
    -- Jacobian of results to inputs via the implicit function theorem
    -- https://en.wikipedia.org/wiki/Implicit_function_theorem#Statement_of_the_theorem
    jResultsInputs = (- (LA.inv $ jr results)) <> ji inputsD
--     jr2 = matrix m  m . j2
    jr  = matrix m  m . R.jacobian (\ r -> system (map (toN.toD) inputsL) r)
    jrg = matrix me m . R.jacobian (\ r -> system (map (toN.toD) inputsL) r)
    ji  = matrix m  n . R.jacobian (\ i -> system i (map toN results))
    j2 r =
      map (\ e -> [unlift $ diff (diff e i) i | i <- tagged "r" r])
      $ system (map (toN.toD) inputsL) (tagged "r" r)
    tagged prefix is =
      zipWith (\ n v -> tag (prefix <> show n) $ lift v) [0..] is
    vars prefix xs = zipWith (\i _ -> var $ prefix <> show i :: Expr Double) [0..] (toList xs)
    systemD1 (a:as) r =
      map (\ e -> unlift $ diff e "a") $
      system (tag "a" (lift a) : map lift as) (map lift r)
    combine s = foldl1 (zipWith (+))
      $ chunksOf m (s + replicate (m - (me `mod` m)) 0)
      -- TODO: ^ is this a nonesense? check with curve fitting
    matrix m n = (LA.><) m n . concat -- == LA.fromLists
    (LA.toList -> results, path) =
      nlFitting LevenbergMarquardtScaled
      1e-10 -- error
      1e-10 -- per-iteration change in the error to stop if the
            -- fitting error can no longer be improved
      100 -- max iterations
      (\ (LA.toList -> x) -> LA.fromList $ system inputsD x)
      (\ (LA.toList -> x) -> jrg x)
      (LA.fromList guessesD)
    inputsL = toList inputs
    inputsD = map toD inputsL
    guessesD = map toD $ toList guesses
    m = length guesses
    n = length inputs

test = (x :: Double, dgda `pct` dgdaBump, dgdb `pct` dgdbBump
       , dgda `pct` fdgda, dgdb `pct` fdgdb
       , d2gda2Bump
       )
  where
    [fdgda, fdgdb] = R.grad (\ as -> fitSystemThrow1 as 0.5 f) [ia,ib]
    dgda = - (1/dx) * dfda
    dgdb = - (1/dx) * dfdb
    d2gda2Bump = bumpDiff (\ a -> bumpDiff (\ a -> nx a ib) a 0.00001) ia 0.00001
    dgdaBump = bumpDiff (\ a -> nx a ib) ia 0.00001
    dgdbBump = bumpDiff (\ b -> nx ia b) ib 0.00001
    Right (x, [dfda, dfdb], dx) = n ia ib
--    _ :< [_ :< d2fda2,d2fdb2]:_) = AD.grads (\ (x:is) -> f is x) [x,ia,ib]
    ia = 1
    ib = 2
    n a b = newton (\ as x -> f as x) [a, b] 0.5
    nx a b = let Right (x,_,_) = n a b in x
    f [a,b] x = a * cos x - b * x^3

trimCofree :: Int -> Cofree [] a -> Cofree [] a
trimCofree 0 (x :< _)  = x :< []
trimCofree n (x :< xs) = x :< map (trimCofree (n-1)) xs

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

-- symd f x bump = (f (x+bump) - f (x-bump)) / (2*bump)
symd f x part bump = (f (x+part*bump) - f (x-part*bump)) / (2*bump)

bumpDiff f x bump = (f (x+bump) - f (x-bump)) / (2*bump)
bumpDiff2 f x bump = bumpDiff (\ x -> bumpDiff f x bump) x bump
dvdxUp :: N n => (Market n -> a -> n) -> Market n -> a -> Get n n -> n -> n
dvdxUp p mkt what x (bump :: n) =
  (p (modify x (+bump) mkt) what - p mkt what) / bump
dvdx' :: N n => (Market n -> a -> n) -> Market n -> a -> Get n n -> n -> n
dvdx' p mkt what x (bump :: n) =
  (p (modify x (+   bump ) mkt) what -
   p (modify x (+ (-bump)) mkt) what) / (2*bump)
dvdx = dvdx' p mkt
dvdx2' p mkt what x bump = dvdx' (\ m w -> dvdx' p m w x bump) mkt what x bump
dvdx2 w = dvdx2' p mkt w
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

plotf :: Double -> Double -> (Double -> Double) -> IO ()
plotf a b f = void $ GP.plotDefault $
  Plot2D.function Graph2D.lines (linearScale 1000 (a, b)) f

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
--   dvdx' p (m Spot (const x)) PV Spot 0.0001
--    dvdx' p (m RateDom (const x)) PV RateDom 0.0001
     impliedVol mkt 5 x
  )
--   `mappend`
--   Plot2D.list Graph2D.boxes
--   [(spotAtT mkt x (oMaturityInYears o), 0.5::Double)
--   |x <- [-0.2,-0.199..0.2::Double]]

plot3d = -- plotFunc3d [Custom "data" ["lines"],
--                      Custom "surface" [], Custom "hidden3d" []] [Plot3dType Surface]
  plotMeshFun
         [0.5,0.51..1.5::Double] [0,0.1..1::Double]
  (\s pd ->
    blackScholesPricer o (modify PricingDate (const pd) $ m Spot (const s)) PV
  )

plotVolSurf = plotMeshFun [0.1,0.11..2] [0.5,0.51..2::Double]
  $ impliedVol mkt

plotMeshFun xs ys f =
  plotMesh $ sort [[(x, y, f' y) | y <- ys] | x <- xs, let !f' = f x]

plotMesh :: [[(Double, Double, Double)]] -> IO ()
plotMesh rows = do
  let dat = "mesh.dat"
      script = "script.plot"
  writeFile dat $ unlines [unlines [unwords $ map show [y,x,v] | (x,y,v) <- r] | r <- rows]
  writeFile script $ unlines $
    ["set view 60, 60"
     -- "set view 90, 90"
    ,"set key off"
    ,"unset colorbox"
--     ,"set contour both"
    ,"set hidden3d"
    ,"set pm3d depthorder border lc 'black' lw 0.33"
--     ,concat ["splot [0:1] [0:20] [-0.1:1.1] \"", dat, "\" ",
    ,concat ["splot \"", dat, "\" ",
      -- "with lines palette lw 0.33"
      "with pm3d"
     ]
    ]
  void $ spawnCommand $ "gnuplot " <> script

linInterpolate x (g:gs) = go g gs
  where
    go p@(px,py) (c@(cx,cy):cs)
      | toD x >= toD px && toD x <= toD cx = -- (p,c,head cs)
        ((x - px)/(cx-px))*(cy-py) + py
      | otherwise = go c cs

-- почему-то digital лучше чем vanilla?
-- увеличение nx желательно сопровождать увеличением nt

fem :: forall a . N a => Market a -> a
fem = fem' 200 100

fem' :: forall a . N a => Int -> Int -> Market a -> a
fem' nx nt market =
  trace (printf "σ=%f, rd=%f, rf=%f, nx=%d, nt=%d, spot=[%.3f..%.3f], h=%.6f" (toD σ) (toD rd) (toD rf) nx nt (toD $ iToSpot 0) (toD $ iToSpot (nx+1)) (toD (h 3)) :: String) $
  linInterpolate (log $ get Spot market) $
  (\ prices -> unsafePerformIO $ do
--       let toGraph = map (\(logSpot, v) -> (toD $ exp logSpot, toD v))
--       plotMesh
--           [map (\(x,v) -> (x, toD $ iToT t, v)) $ toGraph $ addLogSpot l
--           |(l,t) <- iterations]

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
--          [(iToLogSpot 0, 0)]
      zipWith (,) (map iToLogSpot [0..nx+1]) iteration
--       <> [(iToLogSpot (nx+1), 0)]
    iterations = take (nt+1) (iterate ump1 (u0,0))
    τ = oMaturityInYears o - get PricingDate market
    σ = impliedVol market τ (oStrike o)
    rd = get RateDom market
    rf = get RateFor market
--    r = rd-rf -- так получается d rf = - d rd
    θ = 1 -- 1=implicit, 0=explicit -- oscilates, even with 0.5

    ump1 :: ([a], Int) -> ([a], Int)
    ump1 (um,mi) =
      (trimSolve 0 0 -- (if mi > 30 && mi < 40 then 45 else 0)
      (m .+ k mi*θ .* a_bs) ((m .- k mi*(1-θ) .* a_bs) #> um), succ mi)
--       (i .+ k mi*θ .* g_bs) ((i .- k mi*(1-θ) .* g_bs) #> um), succ mi)
--     nx = 500 :: Int
--     nt = 500 :: Int
--     (minSpot, maxSpot) = (exp (-3), otBarrier ot)
--     (minSpot, maxSpot) = (otBarrier ot, exp 3)
--     (minSpot, maxSpot) = (exp (-3), exp 3) -- так уже как в книжке
--     maxSpot = oStrike o * 3 / 2
--     minSpot = oStrike o     / 2
    maxSpot = realToFrac $ toD $ max s0 $ spotAtT market   5 τ
    minSpot = realToFrac $ toD $ min s0 $ spotAtT market (-5) τ
    -- need 0.1*s0 for σ=0.003, rd=0.2, rf=0.01 to have diagonally
    -- dominant matrix; σ=0.03 is fine
    s0 = get Spot market
    k, iToT :: Int -> a
    k i = iToT (i+1) - iToT i
    iToT i = realToFrac ((toEnum i / toEnum nt)**β) * τ
    β = 1 -- market Vol / 2 -- ???
--    k = τ / (toEnum nt-1) -- time step
--     h = (log maxSpot - log minSpot) / (toEnum nx+1) -- log spot step
--     iToLogSpot i = toEnum i * h + log minSpot
    h i = iToLogSpot i - iToLogSpot (i-1)
    iToLogSpot i =
      gradeSpot (intToN i / (intToN nx+1)) * (log maxSpot - log minSpot)
      + log minSpot
    iToSpot = toD . exp . iToLogSpot

    u0 :: [a]
    u0 = [getPv market (const $ exp $ iToLogSpot x) / exp (-rd*τ) | x <- [0..nx+1]]

    s, b, m, a_bs :: Tridiag a
    -- FEM
    a_bs = (σ^2/2) .* s .+ (σ^2/2-rd+rf) .* b .+ rd .* m
--     s = (1/h) .* tridiag nx (-1) 2 (-1)
--     b = (1/2) .* tridiag nx (-1) 0   1
--     m = (h/6) .* tridiag nx   1  4   1
    s = assemble $ \ h -> scale (1/h) ( 1,-1
                                      ,-1, 1)
    b = assemble $ \ h -> scale (1/2) (-1, 1
                                      ,-1, 1)
    m = assemble $ \ h -> scale (h/6) ( 2, 1
                                      , 1, 2)
    bcm = tridiagFromLists (nx+2)
      (repeat 0) ([-1] <> replicate (nx+1) 0) (repeat 0)
    bc = replicate (nx+1) 0 <> [1]
    assemble elt = -- trimTridiag 1 1 $
      tridiagFrom2x2Elements
      [elt (h i) | i <- [1..nx+1]]
    scale x (a,b,c,d) = (x*a,x*b,x*c,x*d)
    trimSolve t b m v =
         replicate t 0
      <> solveTridiagTDMA (trimTridiag t b m) (take (nx+2-t-b) $ drop t v)
      <> replicate b 0

    -- FDM
--     g_bs = (σ^2/2) .* r .+ (σ^2/2-rd+rf) .* c .+ rd .* i
--     r = (1/h) .* s
--     c = (1/h) .* b
--     i = tridiag nx 0 1 0

gradeSpot x
  = x
--   = x**0.5
--   | x < 0.5   =     2*x^2
--   | otherwise = 1 - 2*(1-x)^2

-- integrated 100k ~ fem 500x100 ~ 15ms
main = g
_main = defaultMain
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
      !m = laTridiag (tridiag size 3 10 4) :: LA.Matrix Double
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
