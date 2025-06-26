{-# LANGUAGE MultilineStrings #-}
module TestData where

import Analytic
import Market
import Number
import Tenor

data TestData
  = EURUSD
  | USDJPY
  | DummyData
  deriving (Eq, Show)

testData = EURUSD

testRates :: Fractional a => Recipe a (Node a (Rates a))
testRates = do
  let (s,rf,rd) = case testData of
        DummyData -> (1     , 0.03  , 0.05)
        EURUSD    -> (1.3465, 0.0346, 0.0294)
        -- discount 0.966001?  exp (-0.0346) = 0.965992
        -- discount 0.971049?  exp (-0.0294) = 0.971028
        USDJPY    -> (90.72 , 0.0294, 0.0171)
  s  <- input Spot s
  rf <- input RateFor rf
  rd <- input RateDom rd
  pure (Rates <$> s <*> rf <*> rd)

premiumConvention = case testData of
  DummyData -> Pips
  EURUSD -> Pips
  USDJPY -> Percent

convs = case testData of
  DummyData -> INil (ForwardDelta pc, ATMDeltaNeutral $ ForwardDelta pc)
  EURUSD -> oecd
  USDJPY -> oecd
  where
    pc = premiumConvention
    -- [Wystup2010] "If the currency pair contains only currencies from
    -- the OECD economies (USD, EUR, JPY, GBP, AUD, NZD, CAD, CHF,
    -- NOK, SEK, DKK), and does not include ISK, TRY, MXN, CZK, KRW,
    -- HUF, PLN, ZAR or SGD, then spot deltas are used out to and
    -- including 1Y. For all longer dated tenors forward deltas are
    -- used."
    oecd = ICons
      (SpotDelta pc, ATMDeltaNeutral $ SpotDelta pc)
      (Including (Y 1))
      (INil (ForwardDelta pc, ATMDeltaNeutral $ ForwardDelta pc))


testSurface :: N a => [VolTableRow Tenor a]
testSurface =
  map toRow $ filter (not . null) $ map stripComment $ lines $ case testData of
  DummyData ->
    """
--   Exp   Bid     Ask    RR25   BF25    RR10   BF10
    10Y   10      10     0      0       0      0
    """
  EURUSD ->
    """
-- Copied from Iain Clark, p64, EURUSD
--             ATM
--   Exp   Bid     Ask    RR25   BF25    RR10   BF10
     1D   7.556   8.778  -0.636  0.084  -1.251  0.299
     1W  11.550  12.350  -1.432  0.270  -2.540  0.840
     2W  11.650  12.300  -1.510  0.257  -2.750  0.808
     3W  11.490  12.030  -1.558  0.265  -2.857  0.823
     1M  11.540  12.040  -1.660  0.260  -3.042  0.795
     2M  11.605  12.006  -1.667  0.315  -3.075  0.990
     3M  11.795  12.195  -1.677  0.365  -3.103  1.165
--      6M  12.340  12.690   0      0      -3.132  1.460
     6M  12.340  12.690  -1.680  0.445  -3.132  1.460
--      1Y  18.25   18.25   -0.6    0.95   -1.359  3.806 -- Table 3.3 p50
--      2Y  17.677  17.677  -0.562  0.85   -1.208  3.208 -- Table 3.3 p50
--      1Y   12.590  12.915   0  0.01 -3.158  1.743
     1Y  12.590  12.915  -1.683  0.520  -3.158  1.743
    18M  12.420  12.750  -1.577  0.525  -3.000  1.735
     2Y  12.315  12.665  -1.520  0.495  -2.872  1.665
     3Y  11.915  12.310  -1.407  0.457  -2.683  1.572
     5Y  11.075  11.520  -1.183  0.417  -2.217  1.363
     7Y  11.144  10.626  -1.205  0.353  -2.382  1.157
    """
  USDJPY ->
    """
-- Copied from Iain Clark, p64, USDJPY
--             ATM
--   Exp   Bid     Ask    RR25   BF25    RR10   BF10
     1D   6.871   8.780   0.014  0.077   0.031  0.278
     1W  10.830  12.080   0.060  0.245   0.010  0.840
     2W  11.205  12.005  -0.285  0.265  -0.523  0.843
     3W  11.390  12.000  -0.475  0.293  -0.865  0.913
     1M  11.435  11.910  -0.585  0.287  -1.100  0.907
     2M  11.720  12.120  -0.985  0.305  -1.843  1.060
     3M  12.085  12.500  -1.292  0.328  -2.452  1.207
     6M  13.045  13.375  -1.813  0.345  -3.503  1.415
     1Y  13.710  14.020  -2.383  0.390  -4.678  1.680
    18M  14.045  14.425  -2.687  0.370  -5.245  1.712
     2Y  14.245  14.645  -2.910  0.305  -5.705  1.685
     3Y  14.430  14.930  -3.475  0.290  -6.783  1.745
     5Y  14.995  15.695  -4.550  0.240  -8.937  1.905
     7Y  16.800  17.538  -5.425  0.413 -11.062  3.090
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
