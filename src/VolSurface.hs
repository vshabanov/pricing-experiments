{-# LANGUAGE DerivingStrategies, DeriveAnyClass #-}
module VolSurface where

import Control.DeepSeq
import GHC.Generics (Generic)

import Analytic.Pure
import Tenor
import Number

data VolSurface a
  = VolSurface_
    { volSurfaceMarks :: [VolTableRow Tenor a]
    , volSurfaceSmiles :: [SmileFun a] -- ^ fitted smiles for marks
    , volSurfaceSmileAt :: Memo a (Smile a) -- ^ smile at time t
    }
  deriving Show

data Smile a
  = Smile_
    { smileImpliedVol   :: a -> a -- ^ strike -> implied vol
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
