{-# LANGUAGE MultilineStrings #-}

-- | Simplified interface to gnuplot.
-- It's much easier to configure gnuplot directly in the gnuplot's script
-- than is to find corresponding functions in the 'gnuplot' package
-- (and there are no functions to customize graphs the way I like)
module Gnuplot where

import Control.Monad (void)
import Data.List (intercalate, sort)
import qualified Data.IntMap.Strict as IntMap
import System.Process (spawnCommand)
import Text.Printf (printf)

plotf :: Double -> Double -> (Double -> Double) -> IO ()
plotf a b f = plotGraphs [defaultStyle $ functionPlot a b f]

functionPlot :: Double -> Double -> (Double -> Double) -> [(Double, Double)]
functionPlot from to f = [(x, f x) | x <- linearScale 1000 from to]

linearScale :: Fractional a => Integer -> a -> a -> [a]
linearScale n from to =
  map (\m -> from + (to-from) * fromIntegral m / fromIntegral n) [0..n]


type Style = String

defaultStyle = ("lines",)
pointsStyle = ("points",)
-- circlesStyle = ("circles fs solid 0.25",)

plotGraphs :: [(Style, [(Double, Double)])] -> IO ()
plotGraphs graphs = do
  let script = "script.plot"
  writeFile script $ unlines $
    ["""
    set terminal aqua size 2000,1400 title "Graphs" font "Helvetica,20" \\
        linewidth 2.5
        # 2000 is the maximum width
    set grid

    plot """
    <>
    intercalate ", "
    [printf "'-' using 1:2 title 'graph %d' with %s" i s
    |(i,(s,_)) <- zip [0..] graphs]]
    <>
    -- specify data inline in the same script
    [unlines [unwords $ map show [x,y] | (x,y) <- g] <> "e\n"
    |(_,g) <- graphs]
  void $ spawnCommand $ "gnuplot " <> script

plotMeshFun xs ys f =
  plotMesh $ sort [[(x, y, f' y) | y <- ys] | x <- xs, let !f' = f x]

plotMesh :: [[(Double, Double, Double)]] -> IO ()
plotMesh rows = do
  let script = "script.plot"
  writeFile script $ unlines $
    ["""
     set view 60, 60
     #set view 90, 90
     set key off
     unset colorbox
     #set contour both
     set hidden3d
     set terminal aqua size 2000,1400 title "Graphs" font "Helvetica,20" \\
         linewidth 2
     #set term pdfcairo linewidth 0.01
     #set output 'output.pdf'
     set pm3d depthorder border lc 'black' lw 0.2
     #splot [0:1] [0:20] [-0.1:1.1]
     splot '-' using 1:2:3 with pm3d
     #with lines palette lw 0.33
     """
     ]
    <>
    [unlines [unlines [unwords $ map show [y,x,v] | (x,y,v) <- r] | r <- rows]
    ,"e"]
  void $ spawnCommand $ "gnuplot " <> script

cdfPlot :: [Double] -> [(Double, Double)]
cdfPlot l = go 1 $ sort l
  where
    go !i = \ case
      [] -> []
      (x:xs) -> (x,i/n) : go (i+1) xs
    n = fromIntegral $ length l

histogramPlot :: Double -> [Double] -> [(Double, Double)]
histogramPlot bucket l =
  map (\ (b,c) -> (toEnum b * bucket, toEnum c / toEnum (length l))) $
  IntMap.toList $ IntMap.fromListWith (+)
  [(floor (x / bucket) :: Int, 1::Int) | x <- l]
