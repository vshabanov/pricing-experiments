module Percent where

import Control.DeepSeq
import Text.Printf

newtype Percent = Percent { unPercent :: Double }
  deriving NFData
instance Show Percent where show (Percent p) = printf "%.5f%%" p
pct a b
  | a == b = Percent 0
  | otherwise = Percent ((a / b - 1) * 100)
