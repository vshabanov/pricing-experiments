{-# LANGUAGE NoFieldSelectors, DuplicateRecordFields #-}
-- | Pure analytic pricers, no market dependencies
module Analytic.Pure where

import Debug.Trace
import Data.Number.Erf
import Text.Printf

import Number
import StructuralComparison

data Greek
  = PV
  | FV
  | RhoFor
  | RhoDom
  | Delta
  | DualDelta -- ^ dv/dk
  | PipsForwardDelta
  | Gamma
  | Vega
  | Vanna
  | Theta
  deriving Show

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

directionφ :: Num a => OptionDirection -> a
directionφ = \ case
  Call ->  1
  Put  -> -1

barrierPositionη :: Num a => BarrierPosition -> a
barrierPositionη = \ case
  Upper -> -1
  Lower ->  1

payOnω :: Num a => PayOn -> a
payOnω = \ case
  PayOnTouch -> 0
  PayOnEnd   -> 1

-- | 'forwardRate'
data Rates a
  = Rates
    { s  :: a -- ^ spot
    , rf :: a -- ^ foreign rate
    , rd :: a -- ^ domestic rate
    }
  deriving (Show, Functor, Foldable, Traversable)

data RatesT a
  = RatesT
    { s  :: a -- ^ spot
    , rf :: a -- ^ foreign rate
    , rd :: a -- ^ domestic rate
    , t  :: a -- ^
    }
  deriving (Show, Functor, Foldable, Traversable)

forwardRate :: Floating a => Rates a -> a -> a
forwardRate Rates{s,rf,rd} t = s * exp ((rd-rf)*t)

-- | 'bs' arguments
data BS a
  = BS
    { k  :: a -- ^ strike
    , d  :: OptionDirection
    , t  :: a -- ^ maturity in years
    , s  :: a -- ^ spot
    , σ  :: a -- ^ implied volatility
    , rf :: a -- ^ foreign rate
    , rd :: a -- ^ domestic rate
    }
  deriving (Show, Functor, Foldable, Traversable)

-- | 'fbs' arguments
data FBS a
  = FBS
    { k  :: a -- ^ strike
    , d  :: OptionDirection
    , t  :: a -- ^ maturity in years
    , f  :: a -- ^ forward
    , σ  :: a -- ^ implied volatility
    }
  deriving (Show, Functor, Foldable, Traversable)

-- | Forward greeks that do not requre separate foreign and domestic rates
fbs :: Erf a => Greek -> FBS a -> a
fbs greek FBS{k,d,t,f,σ} = case greek of
  FV -> b
  PipsForwardDelta -> b
  where
    b = bs greek BS{k,d,t,s=f,σ,rf=0,rd=0}

-- | Black-Scholes greeks for vanilla options
bs :: Erf a => Greek -> BS a -> a
bs greek BS{k,d,t=τ,s=x,σ,rf,rd} = case greek of
  PV ->
    φ * exp (-rd*τ) * (f * nc (φ*dp) - k * nc (φ*dm))
  FV ->
    φ * (f * nc (φ*dp) - k * nc (φ*dm))
  RhoDom ->
    φ * k * τ * exp (-rd*τ) * nc (φ*dm)
  RhoFor ->
    -φ * x * τ * exp (-rf*τ) * nc (φ*dp)
  Delta -> -- pips spot delta
    φ * exp (-rf*τ) * nc (φ*dp)
  DualDelta ->
    -φ * exp (-rd*τ) * nc (φ*dm)
  PipsForwardDelta ->
    φ * nc (φ*dp)
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
    φ = directionφ d
    f = x * exp ((rd-rf)*τ)
    dp = (log (f/k) + σ^2/2*τ) / (σ*sqrt τ)
    dm = (log (f/k) - σ^2/2*τ) / (σ*sqrt τ)

-- | Vanilla (flat vol) digital (dual delta), ignores smile effect.
bsDigital :: Erf a => Greek -> BS a -> a
bsDigital greek b@BS{d} = case greek of
  PV ->
    - φ * bs DualDelta b
  where
    φ = directionφ d

-- | Pure bs probability of having spot above/below the strike.
bsDigitalUndisc :: Erf a => Greek -> BS a -> a
bsDigitalUndisc greek b@BS{t=τ,rd} = case greek of
  PV ->
    bsDigital greek b / exp (-rd*τ)

{- | digital option PV with a smile effect.
Needs ∂σ\/∂k.

The digital call option replication via the call spread

digital(k) = lim (h->0) (vanilla(k-h) - vanilla(k+h))\/2h
           = - ∂\/∂k vanilla(k)

since vanilla(k) with a smile is vanilla(k,σ(k)) we get

digital(k) = - vanilla_k(k,σ(k)) - vanilla_σ(k,σ(k)) * σ'(k)
           = - dualDelta         - vega              * σ'(k)

The digital put replication via the put spread
digital(k) = lim (h->0) (vanilla(k+h) - vanilla(k-h))\/2h
           = ∂\/∂k vanilla(k) = -digital_call(k)
-}
digital :: Erf a => Greek -> BS a -> a -> a
digital greek b@BS{d} dσdk = case greek of
  PV ->
    φ * (- bs DualDelta b - bs Vega b * dσdk)
  where
    φ = directionφ d

-- | Probability of having spot above\/below the strike with a smile effect.
-- Needs ∂σ\/∂k.
digitalUndisc :: Erf a => Greek -> BS a -> a -> a
digitalUndisc greek b@BS{t=τ,rd} dσdk = case greek of
  PV ->
    digital greek b dσdk / exp (-rd*τ)

nc :: Erf a => a -> a
nc = normcdf

n :: Floating a => a -> a
n = normdf

normdf t = exp (- t^2/2) / sqrt (2*pi)

------------------------------------------------------------------------------
-- Smiles

data VolTableRow t a
  = VolTableRow
    { t :: t
    , σatm :: a
    , σrr25 :: a
    , σbf25 :: a
    , σrr10 :: a
    , σbf10 :: a
    }
  deriving (Functor, Foldable, Traversable)

instance (Show t, N a) => Show (VolTableRow t a) where
  show (VolTableRow {..}) =
    printf "%3s %7.3f %7.3f %7.3f %7.3f %7.3f"
      (show t) (toD σatm) (toD σrr25) (toD σbf25)
      (toD σrr10) (toD σbf10)

smileFunT = \ case
  SABR{t} -> t
  PolynomialInDelta{t} -> t

data SmileFun a
  = SABR
    { f0 :: a -- ^ initial forward
    , t  :: a
    , σ0 :: a -- ^ initial volatility
    , ν  :: a -- ^ volatility of volatility
    , ρ  :: a -- ^ correlation between spot and volatility
    }
  | PolynomialInDelta
    { f  :: a -- ^ forward at t
    , t  :: a
    , c0 :: a
    , c1 :: a
    , c2 :: a
    }
  deriving (Show, Functor)

smileVol :: Erf a => SmileFun a -> a -> a
smileVol s k = case s of
  SABR{f0,t,σ0,ρ,ν} -> sabr f0 t σ0 ρ ν k
  PolynomialInDelta{f,t,c0,c1,c2} -> polynomialInDelta f t c0 c1 c2 k

-- | SABR model, Hull p648, Iain p60 (same formula, but no f0=k case)
-- f0 -- initial forward
-- σ0 -- initial volatility
-- ν  -- volatility of volatility
-- ρ  -- correlation between spot and volatility
sabr f0 t σ0 ρ ν k
--  | SCmp f0 == SCmp k = σ0*b/f0**(1-β)
    -- the default formula is undefined when f0=k, this can break AD
    -- Comparison here doesn't help as we have a differentiated version
    -- and no longer run this function at all.
  | otherwise =
--     trace (show (f0,k)) $
    a * b * ϕ / χ
  where
    x = (f0*k)**((1-β)/2)
    y = (1-β)*log(f0/k)
    a = σ0/(x*(1 + y^2/24 + y^4/1920))
    b = 1 + ((1-β)^2*σ0^2/(24*x^2) + ρ*β*ν*σ0/(4*x) + (2-3*ρ^2)/24*ν^2)*t
    ϕ = ν*x/σ0*log(f0/k)
    χ = log((sqrt(1 - 2*ρ*ϕ + ϕ^2) + ϕ - ρ) / (1-ρ))
    β = 1
    -- 0 stochastic normal (Hull recommends this,
    --   it's 1.2x faster than β=1, and fits BF=0 with smaller errors)
    -- 1 stochastic lognormal (Iain recommends this)

polynomialInDelta f t c0 c1 c2 k =
--  c0 + c1*(f/k) + c2*(f/k)^2
--  ^ fits very nice, but has huge negative numbers on range ends
  exp $ fun $ log (f / k)
  where
    fun x = c0 + c1*δ x + c2*δ x^2
    σ0 = exp c0
    δ x = normcdf (x / (σ0 * sqrt t))
