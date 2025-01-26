{-# LANGUAGE MagicHash, ScopedTypeVariables, CPP, MultilineStrings, TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-gadt-mono-local-binds -Wno-ambiguous-fields #-}

module Main (module Main) where

import qualified Control.Exception as E
import Control.DeepSeq
import Data.Number.Erf
import qualified Data.Map.Strict as Map
import Debug.Trace
import Data.List.Split
import Data.Foldable
import Data.Array
import Criterion.Main
import Data.Maybe
import Data.Tuple.Extra
import qualified Numeric.LinearAlgebra as LA
import Control.Monad
import Data.List
import Control.Concurrent
import Control.Concurrent.Async
import System.IO.Unsafe
import Text.Printf
import qualified Numeric.AD.Mode.Reverse.Double as RD
import Control.Comonad.Cofree
import Data.MemoUgly
import GHC.Conc

import Random
import Tridiag
import Market
import Gnuplot
import Tenor
import Analytic
import StructuralComparison
import Symbolic
import Number
import Bump
import NLFitting
import Traversables
import Percent
import VolSurface
import FreeVars

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
  -- В AD было примечание, что tape плохо работает в параллельных
  -- вычислениях
    (/ n) . sum . map -- parMapSum 1
    (pv . spotPathLocalVol market dt . map realToFrac)
    $ chunkedGaussian nt (n `div` threads)
  where
    seqpure a = a `seq` pure a
    pv xs = -- product [step (otBarrier ot - x) | x <- xs]
      -- *
      getPv mkt (const $ last xs)
    threads = 1
    nt, n :: Num a => a
    nt = 100
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
    n = 10000

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
    1.35045280 -- kDNS, vol=12.75250%, pv=0.061223760477414985
  --    forwardRate mkt (oMaturityInYears o)
  , oMaturityInYears = 1.1 -- 0.1/365
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
-- p     = digitalPricer o
-- getPv = digitalOptionPv o
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
greeksBumpFem = mapInputs (\ i -> dvdx' (const . fem) mkt () i 0.00001)
greeksBumpIntegrated = mapInputs (\ i -> dvdx' (const . integrated) mkt () i 0.00001)
greeksBumpMonteCarlo = mapInputs (\ i -> dvdx' (const . monteCarlo) mkt () i 0.00001)
greeksAnalytic = map (p mkt) [Delta SpotPips, Vega, RhoDom, RhoFor, Theta-- , Gamma, Vanna
                             ] :: [Double]
compareToAnalytic !g =
  map (\(g,is) -> p mkt g `pct` sum (mapMaybe (flip lookup gs) is)) mapping
  where
    gs = zip (map fst $ inputs (mkt :: Market Double)) g
    mapping =
      [(Delta SpotPips, [Spot])
      ,(Vega, [i | (i@(Vol _ ATMVol),_) <- gs])
      ,(RhoDom, [RateDom])
      ,(RhoFor, [RateFor])
      ,(Theta, [PricingDate])]
greeksAD = snd $ jacobianPvGreeks (flip p PV)
greeksADMonteCarlo = snd $ jacobianPvGreeks monteCarlo

pv :: Double
greeks :: [Double]
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
     -- digitalPricer o
     -- [3.6661059215952516e-2,-0.2291316200997029,0.6795758158561364,-0.9165264803988129,3.744296366024975e-2] ~= greeksBump
     -- blackScholesPricer o
     -- [0.5644849344925212,13.74789720598219,11.847533227133829,-14.112123362313032,-4.744637550015519] epsEq greeksAnalytic

jacobianPvGreeks :: (forall a . N a => Market a -> a) -> (Double, [Double])
jacobianPvGreeks pricer =
  RD.grad' (\ xs ->
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
  node VolSurface $ mkVolSurface <$> sequenceA surf <*> (Rates <$> s <*> rf <*> rd)

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

mkVolSurface :: N a => [VolTableRow Tenor a] -> Rates a -> VolSurface a
mkVolSurface volSurfaceMarks rates = VolSurface_{..}
  where
    volSurfaceSmiles =
      map (flip volTableRowSmile rates . mapTenor tenorToYear) volSurfaceMarks
    volSurfaceSmileAt = Memo $ smileAtT volSurfaceSmiles rates

smileAtT :: N a => [FittedSmile a] -> Rates a -> a -> Smile a
smileAtT smiles rates =
  memo (\ (tagVolT . lift -> t) -> -- trace (exprType t) $
         smile (getSmiles t) (lift <$> rates) t)
  where
    getSmiles = smileInterpolator $ map (lift <$>) smiles
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

smile :: N a => (FittedSmile (Expr a), FittedSmile (Expr a), Expr a -> Expr a -> Expr a) -> Rates (Expr a) -> Expr a -> Smile a
smile (sa, sb, interp) rates@Rates{..} t =
--   trace (unlines $
--       [printf "t=%f" (toD t)] -- , show sa, show sb]
--       <>
--       [ printf "%-7s %.5f %.5f%%  %.5f %.5f%%  %.5f %.5f%%" n
--         (toD $ fst $ f sa) (toD $ snd $ f sa)
--         (toD k) (toD $ 100*s)
--         (toD $ fst $ f sb) (toD $ snd $ f sb)
--       | (n::String,k,s,f) <-
--         [("25dp"   , k25dp, σ25dp, fs25dpkσ)
--         ,("atm"    , katm , σatm , fsATMkσ)
--         ,("25dc"   , k25dc, σ25dc, fs25dckσ)
--         ]]) $
  Smile_
  { smileImpliedVol   = toFun $ impliedVol k
  , smileImpliedVol'k = toFun $ diff (impliedVol k) k
  , smileLocalVol     = toFun $ localVol k
  , smileLocalVol's   = toFun $ diff (localVol k) k
  }
  where
    toFun e =
--      trace (show $ bounds c) $
      c `seq` memo (evalOps c . const . unSCmp) . SCmp
      where c = compileOps $ cse $ untag e

    impliedVol k =
--       interp (smileVol (fsSmileFun sa) k) (smileVol (fsSmileFun sb) k)
--       === -- difference is not that big, ~0.01% on extreme strikes
      smile f s t cs k
      -- surprisingly, it's faster than a simple interpolation from the above
    smile f s t cs k = smileVol (smileFun f s t cs) k
    f = forwardRate rates t -- F_0,T
    cs = $(fitSystemQ [| smileFunGuess |] [| \ cs ->
      let sm = id smile f s t cs
      in
      [ sm katm === σatm
      , sm k25dp === σ25dp
      , sm k25dc === σ25dc
      ] |])

    i f = interp (snd $ f sa) (snd $ f sb)
    σatm = i fsATMkσ
    σ25dp = i fs25dpkσ
    σ25dc = i fs25dckσ
    katm = atmStrike defaultAtmConv ATMBS{s,t,rf,rd,σ=σatm}
    k25dp = ds Put  (-0.25) σ25dp
    k25dc = ds Call   0.25  σ25dc
    ds d delta σ = strikeFromDelta defaultDeltaConv DeltaBS{d,delta,t,s,σ,rf,rd}

    localVol k =
--  σ(K,T) = sqrt (2*(∂C/∂T + (rd-rf) K ∂C/∂K + rf C)/(K² ∂²C/∂K²))
      sqrt (2*(diff c t + (rd-rf)*k*dcdk + rf*c)/(k^2 * d²cdk²))
      where
        dcdk = diff c k
        d²cdk² = diff dcdk k
        c = bs PV BS{k=k,d=Call,σ=impliedVol k,s,rf,rd,t}
    k = "k"

mapTenor :: (a -> b) -> VolTableRow a c -> VolTableRow b c
mapTenor f v@VolTableRow{t} = v { t = f t }

volTableRowSmile :: N a => VolTableRow a a -> Rates a -> FittedSmile a
volTableRowSmile v@VolTableRow{t,σatm,σbf25,σrr25,σbf10,σrr10} (rates@Rates{s,rf,rd})
--   | SCmp t == 0 =
  =
--   trace (unlines $
--       [printf "t=%f" (toD t)]
--       <>
--       [ printf "%-12s %.4f  %.3f%%  %.6f %.6f" n (toD k) (toD $ impliedVol k * 100)
--         (toD $ bs PV BS{k=k,d=Put ,σ=impliedVol k,s,rf,rd,t})
--         (toD $ bs PV BS{k=k,d=Call,σ=impliedVol k,s,rf,rd,t})
--       | (n::String,k) <-
--         [
-- --          ("k10-d-P"   , k10dp)
-- --         ,("k10-d-P-MS", k10dpMS)
--          ("k25-d-P"   , k25dp)
--         ,("k25-d-Pn"  , k25dpn)
-- --         ,("k25-d-P'"   , k25dp')
--         ,("k25-d-P-MS", k25dpMS)
--         ,("kATM"      , kATM)
--         ,("kATMn"     , kATMn)
-- --         ,("kATMsolved", kATMsolved)
--         ,("k25-d-C"   , k25dc)
--         ,("k25-d-Cn"  , k25dcn)
-- --         ,("k25-d-C'"   , k25dc')
--         ,("k25-d-C-MS", k25dcMS)
-- --         ,("k10-d-C"   , k10dc)
--         ,("k10-d-C-MS", k10dcMS)
--         ]]
--       <>
--       [ printf "%-12s %10.7f" n (toD p)
--         -- printf "%-12s %s" n (take 100 $ show p)
--       | (n::String,p) <-
--         [("σatm", σatm)
--         ,("σbf25", σbf25)
-- --         ,("σ25dSS", σ25dSS)
--         ,("σrr25", σrr25)
-- --         ,("σrr25actual", impliedVol k25dcMS - impliedVol k25dpMS)
-- --         ,("σbf25actual", (impliedVol k25dcMS + impliedVol k25dpMS)/2 - σatm)
--         ,("σbf10", σbf10)
-- --         ,("σ10dSS", σ10dSS)
--         ,("σrr10", σrr10)
--         ,("t", t)
--         ,("f", f)
-- --         ,("v25dMSrr", v25dMSrr)
--         ,("v25dMS", v25dMS)
--         ,("v10dMS", v10dMS)
--         ,("vMS", vStrangle k25dpMS (impliedVol k25dpMS) k25dcMS (impliedVol k25dcMS))
--         ,("vSS", vStrangle k25dp   (impliedVol k25dp)   k25dc   (impliedVol k25dc))
--         ,("σatm error", impliedVol kATM === σatm)
--         ,("σrr25 error", impliedVol k25dc === impliedVol k25dp + σrr25)
-- --         ,("σrr10 error", impliedVol k10dc === impliedVol k10dp + σrr10)
--         ,("v25MS error", vStrangle k25dpMS (impliedVol k25dpMS) k25dcMS (impliedVol k25dcMS) === v25dMS)
--         ,("v10MS error", vStrangle k10dpMS (impliedVol k10dpMS) k10dcMS (impliedVol k10dcMS) === v10dMS)
--         ,("c0 (or σ0)", c0)
--         ,("c1 (or ρ) ", c1)
--         ,("c2 (or ν) ", c2)
--         ]]) $
--   traceShow (unlift f) $ -- to check the AD tape size
--   force -- only keep compiled expressions and GC everything else
        -- no longer speeds things up with ad +ffi
        -- but uses much less memory when a lot of smiles are cached
--   traceShow (liftA2 pct (toD <$> cs) (toD <$> csRefit)) $
  FittedSmile
  { fsSmileFun = smileFun f s t cs
  , fsATMkσ  = (kATMn , impliedVol kATMn)
  , fs25dpkσ = (k25dpn, impliedVol k25dpn)
  , fs25dckσ = (k25dcn, impliedVol k25dcn)
  }
--   , smileFittingPoints = map (both unlift)
--     [(kATM, σatm)
--     ,(k25dpMS, σatm + σbf25 - σrr25/2)
--     ,(k25dcMS, σatm + σbf25 + σrr25/2)
-- --     ,(k10dpMS, σatm + σbf10 - σrr10/2)
-- --     ,(k10dcMS, σatm + σbf10 + σrr10/2)
--     ,(k25dp, σatm + σ25dSS - σrr25/2)
--     ,(k25dc, σatm + σ25dSS + σrr25/2)
-- --     ,(k10dp, σatm + σ10dSS - σrr10/2)
-- --     ,(k10dc, σatm + σ10dSS + σrr10/2)
--     ]
  where
    pi n k s = printf "%-12s %.4f  %.5f%% (table %.5f%%)" n (toD k) (toD $ impliedVol k * 100) (toD $ s*100)
    f = forwardRate rates t -- F_0,T
    kATM = atmStrike atmConv ATMBS{s,t,rf,rd,σ=σatm}

    impliedVol k = smile f s t cs k
    smile f s t cs k = smileVol (smileFun f s t cs) k
    ϕRR :: Num a => a
    ϕRR = 1 -- convention, could be -1

    -- TODO: fit 25d and 10d separately, then combine
    --       for SABR we might be able to interpolate c1 c2 between 25d and 10d
    kATMn  = normalizeATMK kATM
    k25dpn = normalizeDK Put  (-0.25) k25dp
    k25dcn = normalizeDK Call   0.25  k25dc
    TT cs@(T3 c0 c1 c2) (T2 k25dp k25dc) =
      $(fitSystemQ [| TT smileFunGuess (T2 k25dpMS k25dcMS) |] [|
                   \ (TT cs (T2 k25dp k25dc)) ->
--       traceShow (cs, σatm, σ25dSS) $
      let sm = id smile f s t cs
          delta d k = bs (Delta $ id deltaConv) BS{k,d,σ=sm k,s,rf,rd,t}
      in
      [ sm kATM === σatm
      , sm k25dc === sm k25dp + ϕRR*σrr25
      , delta Put  k25dp === -0.25 -- smile 25D, not Black-Scholes
      , delta Call k25dc ===  0.25
        -- Despite k25dp/c are functions of 'cs' we can't solve them
        -- during the search for 'cs' as there might be no solution,
        -- so we add them here.
      , id vStrangle_ RatesT{..}
          k25dpMS (sm k25dpMS) k25dcMS (sm k25dcMS) === v25dMS
      ]
      |])

    (k25dpMS, k25dcMS, v25dMS) = ms 0.25 (σatm+σbf25)
    (k10dpMS, k10dcMS, v10dMS) = ms 0.10 (σatm+σbf10)
    -- simple bf-+rr/2 strangle doesn't produce the same price
    -- we need to fit smile strangle instead
--     v25dMSrr = vStrangle k25dpMS (σatm + σbf25 - σrr25/2)
--                          k25dcMS (σatm + σbf25 + σrr25/2)

    ms delta vol = (p, c, vStrangle p vol c vol)
      where (p,c) = (kForDelta Put (-delta) vol, kForDelta Call delta vol)
    kForDelta direction delta vol =
      strikeFromDelta deltaConv DeltaBS{d=direction,t,s,rf,rd,σ=vol,delta}

    vStrangle = vStrangle_ RatesT{..}
    vStrangle_ RatesT{s,rf,rd,t} kp σp kc σc =
        bs PV BS{k=kp,d=Put ,σ=σp,s,rf,rd,t}
      + bs PV BS{k=kc,d=Call,σ=σc,s,rf,rd,t}

    normalizeDK d delta k
      | deltaConv == defaultDeltaConv = k
      | otherwise =
        $(fitSystemQ1 [| k |] [| \ k -> let sm = id smile f s t (T3 c0 c1 c2) in
          bs (Delta defaultDeltaConv) BS{k,d=id d,σ=sm k,s,rf,rd,t} - delta |])
    normalizeATMK k
      | atmConv == defaultAtmConv = k
      | otherwise =
        $(fitSystemQ1 [| k |] [| \ k -> let sm = id smile f s t (T3 c0 c1 c2) in
          atmStrike defaultAtmConv ATMBS{s,t,rf,rd,σ=sm k} - k |])

    deltaConv
      | t <= 1 = SpotPips -- EURUSD convention
      | otherwise = defaultDeltaConv
    atmConv = ATMDeltaNeutral deltaConv

smileFunGuess :: N a => T3 a
-- smileFunGuess = T3 (-2) (-0.1) 0.1
-- smileFun f _s t (T3 c0 c1 c2) = PolynomialInDelta{f,t,c0,c1,c2}
-- Converges on the vol table, and on BF=RR=0
-- but fails on BF=1% and RR=0 or some other number
-- seems that polynomialInDelta is not flexible enough
-- for pure symmetric smiles.
smileFunGuess = T3 0.1 0.1 0.1
smileFun _f f0 t (T3 σ0 ρ ν) = SABR{f0,t,σ0,ρ,ν}
-- with β=1
-- Handles BF=RR=0 with error ~1e-7..1e-9 (bigger than polynomialInDelta)
-- shows almost flat line with numerical noise
-- Handles BF=1% RR=0 and other RRs well
-- smile doesn't have flat wings
-- About 2.2x times slower than polynomialInDelta
-- with β=0 errors <1e-10 and about 1.8x slower
-- BF=RR=0 is not flat at wings but looks flat in -25D..25D range
-- Huge volatility in wings in smaller tenors,
-- can't run Monte-Carlo as it starts with k=f0 or can cross it during
-- the simulation
{-
λ> RD.grad (\ [t] -> (\m -> traceShowId $ localVol m t 1 + localVol m t 1) mkt) [1.1]
λ> bumpDiff (\ t -> localVol mkt t 1) 1.1 0.0001
2.201655918713727e-3
λ> RD.grad (\ [t] -> localVol mkt t 1) [1.1]
[2.201655812057629e-3]
-}


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
iains x = polynomialInDelta 1.3395163731662 1
--  [-1.701005, 0.050131, 0.800801]
--  ^ example in the book is wrong, values don't match iainsTable3_5
--    but for SABR we're pretty close
  (-1.4606627150883185) (-1.0877333376976042) 1.2259367762563833
  --  ^ these have 0.034% error (0.024% max)
  x
iainsCS :: [Double] =
  fitSystemThrow [] [-2,-0.1,0.1]
             $ \ [] [c0,c1,c2] ->
    iainsTable3_5 $ \ _ k σ ->
      polynomialInDelta 1.3395163731662 1 c0 c1 c2 k === σ
      -- doesn't converge, 1e-5 error

polynomialInDelta4 f t [c0,c1,c2,c3] k = exp $ fun $ log (f / k)
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
    p = polynomialInDelta "f" "t" "c0" "c1" "c2" "x" :: Expr Double

infix 4 === -- same as ==

x === y = (x - y)/y  -- /y may cause division by zero

-- | variable for 't'
tagVolT = tag "volT"

smileInterpolator
  :: N a
  => [FittedSmile a]  -- ^ list of smiles fitted for [VolTableRow a]
  -> a             -- ^ time
  -> (FittedSmile a, FittedSmile a, a -> a -> a) -- ^ (smileA, smileB, vol -> vol -> vol)
smileInterpolator smiles = \ t -> case Map.splitLookup (toD t) rows of
  (_, Just r, _) -> (r, r, const id)
    -- FIXME: interpolate both upper and lower sections with two
    --        crossing step functions to make on-pillar AD Theta
    --        closer to the bump Theta?
  (l, _, r) -> case (Map.lookupMax l, Map.lookupMin r) of
    (Just (t1, s1), Just (t2, s2)) -> (s1, s2, interp t t1 t2)
    (Just (_ , s1), _            ) -> (s1, s1, const id)
    (_            , Just (_ , s2)) -> (s2, s2, const id)
    _ -> error "smileInterpolator: empty vol surface"
  where
    rows = Map.fromList [(toD $ smileFunT $ fsSmileFun s, s) | s <- smiles]
    interp t (toN -> t1) (toN -> t2) v1 v2 =
      -- Iain Clark, p65, Flat forward interpolation
      let v12 = (v2^2*t2 - v1^2*t1) / (t2 - t1) in
      if toD v12 < 0 then
        error $ printf "smileInterpolator: negative forward variance v12 = %.8f, t1=%f, v1=%f, t2=%f, v2=%f"
          (toD v12) (toD t1) (toD v1) (toD t2) (toD v2)
      else
        sqrt $ (v1^2*t1 + v12 * (t - t1)) / t

testSurface :: N a => [VolTableRow Tenor a]
testSurface =
  map toRow $ filter (not . null) $ map stripComment $ lines
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
--    2Y  17.677  17.677  -0.562  0.85   -1.208  3.208 -- Table 3.3 p50
--    1Y   12.590  12.915   0  0.01 -3.158  1.743
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
    stripComment = \ case
      '-':'-':_ -> []
      [] -> []
      (x:xs) -> x : stripComment xs

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

-- bad, ignores the fact that probabilities are not independent
-- hitProbabilityDownAndOut mkt barrier n =
--   1-product [1 - volSmileCDF mkt (i/n) barrier | i <- [1..n]]

volSmileCDF mkt t s =
  digitalUndiscPricer (Option{oStrike=s,oDirection=Put,oMaturityInYears=t}) mkt PV
volSmileCDF_BS mkt t s =
  bsDigitalUndiscPricer (Option{oStrike=s,oDirection=Put,oMaturityInYears=t}) mkt PV

volSmileCDF_LocalVol mkt t =
  cdfPlot
  $ map (last . spotPathLocalVol mkt dt . map realToFrac)
  $ chunkedGaussian nt n
  where
    -- same as 'volSmileCDF' with n=100k nt=100, but takes a lot of time
    -- n=400k nt=400 is even closer
    n = 100000
    nt = 100
    dt = t / fromIntegral nt

plot mkt = plotGraphs
--   $ map smileVariance $ drop 5 $ volSurfaceSmiles $ get VolSurface mkt
--   $ map variance [0.51,0.511..0.55]
--   $ map (p . volSmileCDF mkt) [0.1,0.15..1]
--   [
--    p $ volSmileCDF mkt t
-- --   ,volSmileCDF_LocalVol mkt t
-- --   ,p (impliedVol mkt 0)
-- --   ,p (impliedVol mkt 0.0001)
-- --   ,p (impliedVol mkt 0.001)
-- --   ,p (impliedVol mkt 0.01)
--   ,p (impliedVol mkt t)
-- --   ,pointsStyle $ smileFittingPoints $ get Smile mkt t
--   ]
--   [defaultStyle $ functionPlot 0.01 1 $ \ t -> impliedVol mkt t 1.3 ^ 2 * t]
  where
    smileVariance (fsSmileFun -> s) =
      p $ (\ v -> v^2 * smileFunT s) . smileVol s
    variance t = let v2 = var (t+0.00001); v1 = var t in p $ \ x ->
      v1 x
--       signum $ v2 x - v1 x
    var t = (\ v -> v^2 * t) . impliedVol mkt t
    t = 1
    p = defaultStyle . functionPlot
--         1.3 1.5
        0.5 (oStrike o + 1)
        -- (oStrike o - 0.1) (oStrike o + 0.1)

plot3d =
  plotMeshFun
         [0.5,0.51..1.5::Double] [0,0.1..1::Double]
  (\s pd ->
    blackScholesPricer o (modify PricingDate (const pd) $ m Spot (const s)) PV
  )

plotVolSurf mkt = plotMeshFun [0.1,0.11..1.2] [1,1.01..2::Double]
  $ impliedVol mkt

linInterpolate x (g:gs) = go g gs
  where
    go p@(px,py) (c@(cx,cy):cs)
      | toD x >= toD px && toD x <= toD cx = -- (p,c,head cs)
        ((x - px)/(cx-px))*(cy-py) + py
      | otherwise = go c cs

-- почему-то digital лучше чем vanilla?
-- увеличение nx желательно сопровождать увеличением nt

fem :: forall a . N a => Market a -> a
fem = fem' 100 50

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
    addLogSpot iteration =
--          [(iToLogSpot 0, 0)]
      zipWith (,) (map iToLogSpot [0..nx+1]) iteration
--       <> [(iToLogSpot (nx+1), 0)]
    iterations = take (nt+1) (iterate' ump1 (u0,0))
    τ = oMaturityInYears o - get PricingDate market
    σ = impliedVol market τ (oStrike o)
    σ̃loc t x = localVol market t (exp x)
    -- no need to handle the t=0 case as the 'nt' step uses the 'nt-1' time.
    σ̃loc' t x = localVol's market t (exp x) * exp x
    rd = get RateDom market
    rf = get RateFor market
--    r = rd-rf -- так получается d rf = - d rd
    θ = 1 -- 1=implicit, 0=explicit -- oscilates, even with 0.5

    ump1 :: ([a], Int) -> ([a], Int)
    ump1 (um,mi) =
      (trimSolve 0 0 -- (if mi > 30 && mi < 40 then 45 else 0)
      (m .+ k mi*θ .* a) ((m .- k mi*(1-θ) .* a) #> um), succ mi)
      where a = a_bs mi
--       (i .+ k mi*θ .* g_bs) ((i .- k mi*(1-θ) .* g_bs) #> um), succ mi)
--     nx = 500 :: Int
--     nt = 500 :: Int
--     (minSpot, maxSpot) = (exp (-3), otBarrier ot)
--     (minSpot, maxSpot) = (otBarrier ot, exp 3)
--     (minSpot, maxSpot) = (exp (-3), exp 3) -- так уже как в книжке
--     maxSpot = oStrike o * 3 / 2
--     minSpot = oStrike o     / 2
    maxSpot = 2.584 -- realToFrac $ toD $ max s0 $ spotAtT o market   5 τ
    minSpot = 0.681 -- realToFrac $ toD $ min s0 $ spotAtT o market (-5) τ
      -- makes a big difference between AD and Bump
    -- need 0.1*s0 for σ=0.003, rd=0.2, rf=0.01 to have diagonally
    -- dominant matrix; σ=0.03 is fine
    s0 = get Spot market
    k, iToT :: Int -> a
    k i = iToT (i+1) - iToT i
    iToT i = realToFrac ((toEnum i / toEnum nt)**bβ) * τ
    bβ = 1 -- market Vol / 2 -- ???
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

    -- FEM
--     -- Flat vol
--     α _ _ = σ^2/2
--     β _ _ = σ^2/2-rd+rf
    -- Local vol
    α t x = σ̃loc t x^2/2
    β t x = σ̃loc t x*σ̃loc' t x + σ̃loc t x^2/2-rd+rf
    -- the AD tape size:
    -- imp=24
    -- loc=579 loc'=1738
    -- one row (579+1738)*2*100 = 463400  -- 2 for quadrature
    -- an actual number is 655075  (177513 without loc')
    -- (slightly more due to the tridiag solving and vol smile hessian)
    -- ~32M for nx=100 nt=50, which somehow uses 4G of RAM?
    -- 128 bytes (16 words) overhead?
    -- with ReverseDouble 4G -> 1.3G
    -- 40 bytes (5 words) overhead -- looks fine
    -- but it's heap values, so the total RAM usage is 3.5G and GC takes a lot
    -- ad +ffi, makes 1G _total_ RAM, ~10MB Haskell heap
    -- 32 bytes (4 words) overhead and nothing else
    γ _ = rd

    a_bs :: Int -> Tridiag a
    a_bs i = -- trimTridiag 1 1 $
--       trace (printf "a_bs i=%3d t=%.4f iToT i=%.4f" i (toD t) (toD $ iToT i)) $
      tridiagFrom2x2Elements
      [s + b + m
      |i <- [1..nx+1]
      ,let (s,b,m) = elements (iToLogSpot (i-1)) (iToLogSpot i) (α t) (β t) γ
      ]
      where t = τ - iToT i
    m =
      tridiagFrom2x2Elements
      [(h i/6 *) <$> T4 2 1 1 2 | i <- [1..nx+1]]
--     a_bs = (σ^2/2) .* s .+ (σ^2/2-rd+rf) .* b .+ rd .* m
--     s = (1/h) .* tridiag nx (-1) 2 (-1)
--     b = (1/2) .* tridiag nx (-1) 0   1
--     m = (h/6) .* tridiag nx   1  4   1
--     s = assemble $ \ h -> scale (1/h) ( 1,-1
--                                       ,-1, 1)
--     b = assemble $ \ h -> scale (1/2) (-1, 1
--                                       ,-1, 1)
--     m = assemble $ \ h -> scale (h/6) ( 2, 1
--                                       , 1, 2)
    bcm = tridiagFromLists (nx+2)
      (repeat 0) ([-1] <> replicate (nx+1) 0) (repeat 0)
    bc = replicate (nx+1) 0 <> [1]

    trimSolve t b m v =
         replicate t 0
      <> solveTridiagTDMA (trimTridiag t b m) (take (nx+2-t-b) $ drop t v)
      <> replicate b 0

    -- FDM
--     g_bs = (σ^2/2) .* r .+ (σ^2/2-rd+rf) .* c .+ rd .* i
--     r = (1/h) .* s
--     c = (1/h) .* b
--     i = tridiag nx 0 1 0

elements x_lm1 x_l α β γ = (s, b, m)
  where
    s = (2/h_l *) <$> element Diff   Diff   α
    b =               element Diff   Normal β
    m = (h_l/2 *) <$> element Normal Normal γ
    n1 Normal ξ = (1-ξ)/2
    n1 Diff   _ = -1/2
    n2 Normal ξ = (1+ξ)/2
    n2 Diff   _ = 1/2
    fkl ξ = (x_l + x_lm1)/2 + ξ*h_l/2
    h_l = x_l - x_lm1
    element mj mi f =
      quadrature 2 <$>  -- 1 point is not enough for 'm'
      t4 (m n1 n1, m n1 n2
         ,m n2 n1, m n2 n2)
      where
        m φi φj x = f (fkl x) * φj mj x * φi mi x

data Shape = Normal | Diff

-- | <https://en.wikipedia.org/wiki/Gaussian_quadrature>
quadrature :: Floating a => Int -> (a -> a) -> a
quadrature points f = case points of
  1 -> 2 * f 0
  2 -> f (-1/sqrt 3) + f (1/sqrt 3)
  3 -> 8/9*f 0 + 5/9*(f (-sqrt(3/5)) + f (sqrt(3/5)))
  n -> error $ printf "quadrature for %d points is not implemented" n

gradeSpot x
  = x
--   = x**0.5
--   | x < 0.5   =     2*x^2
--   | otherwise = 1 - 2*(1-x)^2

-- integrated 100k ~ fem 500x100 ~ 15ms
main = do
-- --  printf "Analytic PV = %f, MC PV = %f, %s\n" a m (show $ pct a m)
-- --  plot mkt
-- --  print $ fem mkt
  let (adDelta:_) = greeksAD
      femBumpDelta = dvdx' (\ m () -> fem m) mkt () Spot 0.0001
  printf "femBumpDelta = %f, adDelta = %f, %s\n" femBumpDelta adDelta (show $ pct femBumpDelta adDelta)
  let analyticPV = p mkt PV
      femPV = pv
  printf "femPV = %f, analyticPV = %f, %s\n" femPV analyticPV (show $ pct femPV analyticPV)
  print greeks
  print $ compareToAnalytic greeks
  print greeksAD
  print $ compareToAnalytic greeksAD
  print $ zipWith pct greeks greeksAD
--   where
--     a = p mkt PV
--     m = monteCarlo mkt
--   print $ force $ zipWith pct greeksBumpFem greeks
--   print $ zipWith pct greeksBumpLocalVol greeksADLocalVol
--   print (localVol mkt 1.1 1 :: Double)
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
