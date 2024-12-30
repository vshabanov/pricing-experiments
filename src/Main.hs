{-# LANGUAGE MagicHash, ScopedTypeVariables, CPP, MultilineStrings #-}
{-# OPTIONS_GHC -Wno-gadt-mono-local-binds -Wno-ambiguous-fields #-}

module Main (module Main) where

import qualified Control.Exception as E
import Control.DeepSeq
import Data.Number.Erf
import qualified Data.Map.Strict as Map
import Debug.Trace
import Data.List.Split
import Data.Foldable
import Criterion.Main
import Graphics.Gnuplot.Simple
import qualified Graphics.Gnuplot.Advanced as GP
import qualified Graphics.Gnuplot.Plot.TwoDimensional as Plot2D
import qualified Graphics.Gnuplot.Graph.TwoDimensional as Graph2D
import qualified Graphics.Gnuplot.LineSpecification as LineSpec
import Data.Maybe
import qualified Numeric.LinearAlgebra as LA
import Control.Monad
import Data.List
import Control.Concurrent
import Control.Concurrent.Async
import System.IO.Unsafe
import Text.Printf
import qualified Numeric.AD.Mode.Reverse as R
import Control.Comonad.Cofree
import System.Process
import Data.MemoUgly

import Random
import Tridiag
import Market
import Tenor
import Analytic
import Symbolic
import Number
import Bump
import NLFitting
import Traversables
import Percent

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
    (/ n) . parMapSum 8 (pv . spotPath o market dt . map realToFrac)
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
  treeSum [getPv mkt (spotAtT o mkt (realToFrac ϵ)) | ϵ <- gaussianQuasiRandom n] / n
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
  treeSum [getPv mkt (spotAtT o mkt (realToFrac $ x+step/2)) *
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
  [getPv mkt (spotAtT o mkt (realToFrac mid))
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
greeksBumpLocalVol = mapInputs (\ i -> dvdx' (\m -> localVol m (1.1 + get PricingDate m)) mkt 1 i 0.000001)
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

smileAtT :: N a => [VolTableRow Tenor a] -> Rates a -> a -> Smile a
smileAtT surface rates =
  memo (\ t -> -- trace (exprType t) $
         flip smile rates $ volTableRow surface t)
-- bumping works, but it's only 6-7 times faster than the full AD version.
-- smileAtT surface rates t =
-- --  trace (printf "smileAtT %f" (toD t)) $
--   s0 { smileLocalVol = \ s ->
--          (smileImpliedVol sUp s - smileImpliedVol sDown s)/(2*h) }
--   where
--     sm tx = smile (mapTenor unlift $ fmap unlift $ volTableRow surface tx) rates
--     s0 = sm t
--     sDown = sm (t-h)
--     sUp   = sm (t+h)
--     h = 0.0001

mapTenor :: (a -> b) -> VolTableRow a c -> VolTableRow b c
mapTenor f v@VolTableRow{t} = v { t = f t }

-- smile :: N a => VolTableRow a a -> Rates a -> Smile a
-- smile v@VolTableRow{t,σatm,σbf25,σrr25} rates@Rates{s,rf,rd} =
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
      -- (trace $ take 1000 $ showExprWithSharing dSolvedSdt) $
      eval (const k) dSolvedSdt
--      (trace $ take 100 $ showExprWithSharing $ diff (solvedS $ lift k) t) $
--       unlift $ diff (solvedS $ lift k) t
  }
{-
λ> bumpDiff (\ t -> localVol mkt (1.1+t) 1) 0 0.0001
2.201655918713727e-3
λ> R.grad (\ [t] -> localVol mkt (1.1+t) 1) [0]
[2.201655812057629e-3]
λ> localVol mkt 1.1 1
-5.815826767965226e-3
λ> bumpDiff (\ t -> impliedVol mkt (1.1+t) 1) 0 0.0001
-5.815826784605349e-3
λ> R.grad (\ [t] -> impliedVol mkt (1.1+t) 1) [0]
[-5.815826767966395e-3]
-}
  where
    pi n k s = printf "%-12s %.4f  %.5f%% (table %.5f%%)" n (toD k) (toD $ solvedS k * 100) (toD $ s*100)
    f = forwardRate rates t -- F_0,T
    kDNS = f * exp (1/2 * σatm^2 * t) -- K_DNS;pips
    dSolvedSdt = cse $ untag $ diff (solvedS "k") t
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
--      trace (show ("fitSS", toD σ25dSS)) $
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
      , 1/2*(sm k25dc + sm k25dp) === σatm + σ25dSS
        -- Using σatm instead sm kDNS gives a better match between
        -- bump and AD greeks. Better convergence?
      , delta Put  k25dp === -0.25 -- smile 25D, not Black-Scholes
      , delta Call k25dc ===  0.25
        --  ^ reordered to use division in (===) for better error estimates
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
        , σrr25 = -i "RR25" (\VolTableRow{σrr25} -> -σrr25)
          -- TODO: it makes no sense to interpolate difference between volatilities
          -- we should first calibrate two smiles, get kATM/P25/C25,
          -- their vols, interpolate strikes and vols
          -- and calibrate the new smile.
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
  map toRow $ filter (not . isPrefixOf "--") $ lines
  """
-- Copied from Iain Clark, p64, EURUSD
--           ATM
-- Exp   Bid     Ask    RR25   BF25    RR10   BF10
   1D   7.556   8.778  -0.636  0.084  -1.251  0.299
   1W  11.550  12.350  -1.432  0.270  -2.540  0.840
   2W  11.650  12.300  -1.510  0.257  -2.750  0.808
   3W  11.490  12.030  -1.558  0.265  -2.857  0.823
   1M  11.540  12.040  -1.660  0.260  -3.042  0.795
   2M  11.605  12.006  -1.667  0.315  -3.075  0.990
   3M  11.795  12.195  -1.677  0.365  -3.103  1.165
--    6M  12.340  12.690   0      0      -3.132  1.460
   6M  12.340  12.690  -1.680  0.445  -3.132  1.460
--    1Y  18.25   18.25   -0.6    0.95   -1.359  3.806 -- Table 3.3 p50
   1Y  12.590  12.915  -1.683  0.520  -3.158  1.743
  18M  12.420  12.750  -1.577  0.525  -3.000  1.735
   2Y  12.315  12.665  -1.520  0.495  -2.872  1.665
   3Y  11.915  12.310  -1.407  0.457  -2.683  1.572
   5Y  11.075  11.520  -1.183  0.417  -2.217  1.363
   7Y  11.144  10.626  -1.205  0.353  -2.382  1.157
  """
  where
    toRow (words -> [tenor, bid, ask, rr25, bf25, rr10, bf10]) =
      VolTableRow (read tenor)
        ((p bid + p ask) / 2) (p rr25) (p bf25) (p rr10) (p bf10)
    p x = toN (read x) / 100

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

trimCofree :: Int -> Cofree [] a -> Cofree [] a
trimCofree 0 (x :< _)  = x :< []
trimCofree n (x :< xs) = x :< map (trimCofree (n-1)) xs

dvdx = dvdx' p mkt
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
--    ,"set term aqua enhanced 4"
--     ,"set term pdfcairo linewidth 0.01"
--     ,"set output \"output.pdf\""
    ,"set pm3d depthorder border lc 'black' lw 0.2"
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
fem = fem' 100 100

fem' :: forall a . N a => Int -> Int -> Market a -> a
fem' nx nt market =
  trace (printf "σ=%f, rd=%f, rf=%f, nx=%d, nt=%d, spot=[%.3f..%.3f], h=%.6f" (toD σ) (toD rd) (toD rf) nx nt (toD $ iToSpot 0) (toD $ iToSpot (nx+1)) (toD (h 3)) :: String) $
  linInterpolate (log $ get Spot market) $
  (\ prices -> unsafePerformIO $ do
      let toGraph = map (\(logSpot, v) -> (toD $ exp logSpot, toD v))
      plotMesh
          [map (\(x,v) -> (x, toD $ iToT t, v)) $ toGraph $ addLogSpot l
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
    maxSpot = realToFrac $ toD $ max s0 $ spotAtT o market   5 τ
    minSpot = realToFrac $ toD $ min s0 $ spotAtT o market (-5) τ
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
main =
  print $ zipWith pct greeksBumpLocalVol greeksADLocalVol
--  print (localVol mkt 1.1 1 :: Double)
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
