module Tenor where

import Data.Char
import Data.String

data Tenor
  = D Int
  | W Int
  | M Int
  | Y Int
  deriving (Eq, Ord)

instance Show Tenor where
  showsPrec _ t = (<>) $ case t of
    D x -> show x <> "D"
    W x -> show x <> "W"
    M x -> show x <> "M"
    Y x -> show x <> "Y"

instance Read Tenor where
  readsPrec p s =
    [(t x, r)
    |(x::Int, (unit:r)) <- readsPrec p s
    ,t <- fromUnit (toUpper unit)]
    where
      fromUnit = \ case
        'D' -> [D]
        'W' -> [W]
        'M' -> [M]
        'Y' -> [Y]
        _ -> []

instance IsString Tenor where
  fromString s = case reads s of
    [(t, "")] -> t
    _ -> error $ "Bad tenor " <> show s

-- | dumb tenor to 365 days year conversion, no calendar/spot rules
tenorToYear = \ case
  D x ->   fromIntegral x*d
  W x -> 7*fromIntegral x*d
  M x ->   fromIntegral x/12
  Y x ->   fromIntegral x
  where
    d = 1/365
