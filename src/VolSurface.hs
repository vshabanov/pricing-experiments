{-# LANGUAGE DerivingStrategies, DeriveAnyClass #-}
module VolSurface where

import Data.Ord
import Data.Maybe
import Data.List
import Control.DeepSeq
import GHC.Generics (Generic)

import Analytic.Pure
import Tenor
import Number

data VolSurface a
  = VolSurface_
    { volSurfaceMarks :: [VolTableRow Tenor a]
    , volSurfaceSmiles :: [FittedSmile a] -- ^ fitted smiles for marks
    , volSurfaceSmileAt :: Memo a (Smile a) -- ^ smile at time t
    }
  deriving Show

data FittedSmile a
  = FittedSmile
    { fsRatesT :: RatesT a
    , fsSmileFun :: SmileFun a
    , fsSmileFun10 :: SmileFun a
      -- in theory, we can do some solving to get ATM and xD strikes and vols,
      -- but let's just cache them
    , fsConventions :: Conventions
    , fsATMkσ  :: (a, a) -- ^ in 'fsAtmConv'
    , fs25dpkσ :: (a, a) -- ^ in 'fsDeltaConv'
    , fs25dckσ :: (a, a)
    , fs10dpkσ :: (a, a)
    , fs10dckσ :: (a, a)
    }
  deriving (Show, Functor, Foldable, Traversable)

fsF :: Floating a => FittedSmile a -> a
fsF = forwardRateT . fsRatesT

fsT :: FittedSmile a -> a
fsT (fsRatesT -> RatesT{t}) = t

data Smile a
  = Smile_
    { smileImpliedVol   :: SmileFun a
        -- a -> a -- ^ strike -> implied vol
    , smileImpliedVol'k :: a -> a -- ^ strike -> d implied vol / dk
    , smileLocalVol     :: a -> a -- ^ strike -> local vol
    , smileLocalVol's   :: a -> a -- ^ strike -> d local vol / ds
--    , smileFittingPoints :: [(a,a)] -- ^ [(strike, vol)] points
    }
  deriving Generic
  deriving anyclass NFData

newtype Memo a b = Memo { unMemo :: a -> b }
instance Show (Memo a b) where show _ = "Memo"

data VolInput
  = ATMVol
  | RR25
  | BF25
  | RR10
  | BF10
  deriving (Show, Eq, Ord)
