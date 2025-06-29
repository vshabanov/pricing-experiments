-- | Market-based analytic pricers
module Analytic.Market where

import Analytic.Pure
import Control.DeepSeq
import Data.List
import Data.Number.Erf
import Market
import Number
import StructuralComparison

data Option a
  = Option
    { oStrike :: a
    , oMaturityInYears :: a
    , oDirection :: OptionDirection
    }
  deriving Show
data OneTouch a
  = OneTouch
    { otBarrier :: a
    , otBarrierPosition :: BarrierPosition
    , otPayOn :: PayOn
    , otMaturityInYears :: a
    }
  deriving Show
data Forward a
  = Forward
    { fStrike :: Strike a
    , fMaturityInYears :: MaturityInYears a
    }
  deriving Show
newtype Strike a = Strike { strike :: a }
  deriving (Num, Fractional, Floating, Erf, Show, NFData, InvErf, Ord, Eq, StructuralOrd, StructuralEq, N)
newtype MaturityInYears a = MaturityInYears { maturityInYears :: a }
  deriving (Num, Fractional, Floating, Erf, Show)

rates :: Market a -> Rates a
rates m = Rates{s = get Spot m, rf = get RateFor m, rd = get RateDom m}

bsDigitalPricer :: N a => Option a -> Market a -> Greek -> a
bsDigitalPricer o market greek =
  bsDigital greek $ marketBS o market

bsDigitalUndiscPricer :: N a => Option a -> Market a -> Greek -> a
bsDigitalUndiscPricer o market greek =
  bsDigitalUndisc greek $ marketBS o market

digitalPricer :: N a => Option a -> Market a -> Greek -> a
digitalPricer o market greek =
  uncurry (digital greek) $ marketBS_impliedVol'k o market

digitalUndiscPricer :: N a => Option a -> Market a -> Greek -> a
digitalUndiscPricer o market greek =
  uncurry (digitalUndisc greek) $ marketBS_impliedVol'k o market

blackScholesPricer :: N a => Option a -> Market a -> Greek -> a
blackScholesPricer o market greek = bs greek $ marketBS o market

marketBS_impliedVol'k :: N a => Option a -> Market a -> (BS a, a)
marketBS_impliedVol'k o market = (b, impliedVol'k market t k)
  where b@BS{t,k} = marketBS o market

marketBS :: N a => Option a -> Market a -> BS a
marketBS o market = BS{..}
  where
    k = oStrike o
    d = oDirection o
    t = oMaturityInYears o - m PricingDate
    s = m Spot
    σ = impliedVol market t k
    rf = m RateFor
    rd = m RateDom
    m i = get i market

marketRatesT :: Erf a => a -> Market a -> RatesT a
marketRatesT t market = RatesT{..}
  where
    s = m Spot
    rf = m RateFor
    rd = m RateDom
    m i = get i market

pay1Pricer :: Erf a => OneTouch a -> Market a -> Greek -> a
pay1Pricer ot market PV = exp (-rd*τ)
  where
    τ = otMaturityInYears ot - m PricingDate
    rd = m RateDom
    m i = get i market

noTouchPricer :: N a => OneTouch a -> Market a -> Greek -> a
noTouchPricer ot market what =
  pay1Pricer ot market what - oneTouchPricer ot market what

oneTouchPricer :: N a => OneTouch a -> Market a -> Greek -> a
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
spotAtT o market ϵ τ =
  s0 * exp ((μ̂ - σ^2/2)*τ + σ*ϵ*sqrt τ)
  where
    μ̂ = rd - rf
    s0 = m Spot
    σ = impliedVol market τ (oStrike o)
    rd = m RateDom
    rf = m RateFor
    m i = get i market

spotPath o market dτ es =
  map ((s0 *) . exp) $
  scanl' (+) 0 [(μ̂ - σ^2/2)*dτ + σ*ϵ*sqrt dτ | ϵ <- es]
  where
    μ̂ = rd - rf
    s0 = m Spot
    σ = impliedVol market (dτ * intToN (length es)) (oStrike o)
    rd = m RateDom
    rf = m RateFor
    m i = get i market

spotPathLocalVol market dτ es =
  scanl' (\ s (i,ϵ) ->
            let vol = σ i s in
--            trace (printf "σ %d %f = %f" i s vol) $
            s * exp ((μ̂ - vol^2/2)*dτ + vol*ϵ*sqrt dτ))
    s0 (zip [0..] es)
  where
    μ̂ = rd - rf
    s0 = m Spot -- + 1e-5
    -- as vol is undefined (NaN) at t=0 we use the implied vol in the
    -- first step and then local vol
    -- TODO: We use impliedVol for strike=spot, the correct way would
    --       be to use the smile CDF, so we can generate the spot
    --       distribution corresponding to the smile. We will need to
    --       solve the smile CDF for normcdf ϵ
    σ 0 s = impliedVol market dτ s
    σ i s = localVol market (dτ * intToN i) s
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

digitalOptionPv o market spotAt =
  exp (-rd*τ) * step (φ * (spotAt τ - k))
  where
    k = oStrike o
    τ = oMaturityInYears o - m PricingDate
    φ = directionφ $ oDirection o
    rd = m RateDom
    m i = get i market

combine a b market what = a market what + b market what
scale s f market what = s * f market what
