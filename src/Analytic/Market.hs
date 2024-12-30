-- | Market-based analytic pricers
module Analytic.Market where

import Data.Number.Erf
import Data.List
import Number
import Market
import Analytic.Pure

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
