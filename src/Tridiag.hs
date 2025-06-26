{-# OPTIONS_GHC -Wno-x-partial #-}
module Tridiag
  ( (.+), (.-), (.*), (#>)
  , Tridiag, tridiag
  , solveTridiagTDMA
  , solveTridiagLATridiag
  , solveTridiagLAGeneric
  , laTridiag
  , tridiagFromLists
  , trimTridiag, tridiagFrom2x2Elements
  )
where

import Control.Monad
import Control.Monad.ST
import Data.Array
import Data.Vector qualified as V
import Data.Vector.Mutable qualified as M
import Number
import Numeric.LinearAlgebra qualified as LA
import Test.QuickCheck
import Text.Printf
import Traversables

infixl 6 .+, .- -- same as (+)
infixl 7 .*, #> -- same as (*)

-- scale .* mat = realToFrac scale * mat

(#>) :: (Show a, Num a) => Tridiag a -> [a] -> [a]
t@(Tridiag sa l d u) #> vec
  | length vec /= sa
  = err ["Matrix size /= vector size, ", show sa, " /= ", show (length vec)]
  | otherwise
  = case vec of
      []  -> [1]
      [x] -> [d!0 * x]
      _   ->
           [                d!i * v!i + u!i * v!(i+1) | i <- [0]]
        <> [l!i * v!(i-1) + d!i * v!i + u!i * v!(i+1) | i <- [1..sa-2]]
        <> [l!i * v!(i-1) + d!i * v!i                 | i <-    [sa-1]]
  where
    v = listArray (0,sa-1) vec

(.*) :: Num a => a -> Tridiag a -> Tridiag a
scale .* Tridiag size l d u = Tridiag size (s l) (s d) (s u)
  where
    s = fmap (scale *)

liftTridiag2 :: Show a => (a -> a -> a) -> Tridiag a -> Tridiag a -> Tridiag a
liftTridiag2 f a@(Tridiag sa la da ua) b@(Tridiag sb lb db ub)
  | sa /= sb
  = err ["Mismatch in tridiag sizes ", show a, ", ", show b]
  | otherwise
  = Tridiag sa (z la lb) (z da db) (z ua ub)
  where
    z a b = accum f a (assocs b)
a .+ b = liftTridiag2 (+) a b
a .- b = liftTridiag2 (-) a b

tridiag :: Int -> a -> a -> a -> Tridiag a
tridiag s l d u = tridiagFromLists s (repeat l) (repeat d) (repeat u)

tridiagFromLists s l d u = Tridiag s
  (listArray (1,s-1) l) -- no first row
  (listArray (0,s-1) d)
  (listArray (0,s-2) u) -- no last row

trimTridiag :: Num a => Int -> Int -> Tridiag a -> Tridiag a
trimTridiag top bottom (Tridiag s l d u)
  | newSize < 0 = error $
    printf "trimTridiag %d %d [matrix of size %d]: can't trim more than the size of the matrix" top bottom s
  | newSize == 0 = tridiag 0 0 0 0
  | otherwise = tridiagFromLists newSize
    (drop top $ elems l)
    (drop top $ elems d)
    (drop top $ elems u)
  where
    newSize = s - top - bottom

-- | N+1 tridiagonal matrix from N 2x2 elements
--   a0    b0
--   c0    d0+a1  b1
--         c1     d1+a2 b2
--                c2    d2
tridiagFrom2x2Elements :: Num a => [T4 a] -> Tridiag a
tridiagFrom2x2Elements es = tridiagFromLists (length es+1)
  cs
  (zipWith (+) (as <> [0]) ([0] <> ds))
  bs
  where
    as = [a | T4 a _ _ _ <- es]
    bs = [b | T4 _ b _ _ <- es]
    cs = [c | T4 _ _ c _ <- es]
    ds = [d | T4 _ _ _ d <- es]

data Tridiag a
  = Tridiag
    { tridiagSize :: Int
    , tridiagL :: Array Int a
    , tridiagD :: Array Int a
    , tridiagU :: Array Int a
    }
  deriving Show

err x = error $ mconcat x

solveTridiagTDMA :: N a => Tridiag a -> [a] -> [a]
solveTridiagTDMA t@(Tridiag s l d u)
  | Just e <- nonDiagonallyDominant t
  = err ["solveTridiagTDMA: matrix is not diagonally dominant, " <> e]
    -- can produce wildly different results from solveTridiagLAGeneric
    -- for non-diagonally dominant matrices
  | s == 0 = const []
  | otherwise = tdmaSolver ([0] <> elems l) (elems d) (elems u <> [0])

-- https://en.wikipedia.org/wiki/Diagonally_dominant_matrix
nonDiagonallyDominant (Tridiag s _l _d _u)
  | s <= 1 = Nothing
  | otherwise =
      check d u 0
    $ check d l (s-1)
    $ foldr (\ i n -> check d u i $ check d l i n) Nothing [1..s-2]
  where
    l = (_l, "l"); d = (_d, "d"); u = (_u, "u")
    check (a,na) (b,nb) i next
      | not $ abs (a!i) >= abs (b!i) -- do not use <, to check for NaNs as well
      = Just $ printf "abs (%s!%d) < abs (%s!%d); abs (%f) < abs (%f)"
        na i nb i (toD $ a!i) (toD $ b!i)
      | otherwise = next

solveTridiagLATridiag (Tridiag _ l d u) vec =
  LA.toList $ head $ LA.toColumns
    $ LA.triDiagSolve (v l) (v d) (v u)
    $ LA.fromColumns [LA.fromList vec]
  where
    v = LA.fromList . elems

solveTridiagLAGeneric t vec =
  LA.toList $ laTridiag t LA.<\> LA.fromList vec

laTridiag (Tridiag size l d u) =
  ((zeroCol LA.||| diag u)
            LA.=== zeroRow)
  +
  diag d
  +
  (zeroRow LA.===
   (diag l LA.||| zeroCol))
  where
    diag = LA.diagl . elems
    zeroRow = LA.row $ replicate  size    0
    zeroCol = LA.col $ replicate (size-1) 0


data SolveTridiagInputs a
  = SolveTridiagInputs
    { stiTridiag :: Tridiag a
    , stiVector :: [a]
    }
  deriving Show

instance Arbitrary (SolveTridiagInputs Double) where
  arbitrary = do
    size <- chooseInt (5, 50)
    let e = choose (1,10)
    l <- e
    u <- e
    let m = l + u
    d <- choose (m, 2*m) -- diagonally dominant
    stiVector <- vectorOf size e
    pure $ SolveTridiagInputs{stiTridiag=tridiag size l d u, ..}

prop_solveTridiag SolveTridiagInputs{..} =
  and $ zipWith (epsEq 1e-11)
    (solveTridiagTDMA stiTridiag stiVector)
--     (solveTridiagLAGeneric stiTridiag stiVector)
    (solveTridiagLATridiag stiTridiag stiVector)

data TestTridiagInputs a
  = TestTridiagInputs
    { ttiA :: [a]
    , ttiB :: [a]
    , ttiC :: [a]
    , ttiD :: [a]
    }
  deriving Show

instance Arbitrary (TestTridiagInputs Double) where
  arbitrary = do
    size <- chooseInt (5, 50)
    let v s = vectorOf s $ choose (1,10)
    ttiA <- v (size-1)
    ttiB <- v size
    ttiC <- v (size - 1)
    ttiD <- v size
    pure $ TestTridiagInputs{..}

prop_tridiag TestTridiagInputs{..} = and $ zipWith (epsEq 5e-12) qf la
  where
    qf = tdmaSolver ([0]<>ttiA) ttiB (ttiC<>[0]) ttiD
    la = LA.toList $ head $ LA.toColumns
      $ LA.triDiagSolve (LA.fromList ttiA) (LA.fromList ttiB) (LA.fromList ttiC)
      $ LA.fromColumns [LA.fromList ttiD]

epsEq e a b = eps a b < e
eps a b = abs (a-b) / max (abs a) (abs b)

-- https://hackage.haskell.org/package/quantfin-0.2.0.0/docs/src/Quant-Math-Utilities.html#tdmaSolver
-- | Tridiagonal matrix solver.  Pretty simple.
tdmaSolver :: Fractional a => [a] -> [a] -> [a] -> [a] -> [a]
tdmaSolver aL bL cL dL = V.toList $
    let [a,b,c,d] = map V.fromList [aL,bL,cL,dL] in
        runST $ do
            c' <- V.thaw c
            M.write c' 0 $! V.head c / V.head b
            forM_ [1..V.length c-1] $ \x -> do
                let ai = a V.! x
                    bi = b V.! x
                    ci = c V.! x
                ci1' <- M.read c' (x-1)
                M.write c' x $! ci / (bi-ai*ci1')
            cf <- V.unsafeFreeze c'
            d' <- V.thaw d
            M.write d' 0 $! V.head d / V.head b
            forM_ [1..V.length d-1] $ \x -> do
                let ai  = a  V.! x
                    bi  = b  V.! x
                    di  = d  V.! x
                    ci1 = cf V.! (x-1)
                di1' <- M.read d' (x-1)
                M.write d' x $! (di-ai*di1') / (bi-ai*ci1)
            df <- V.unsafeFreeze d'
            xn <- M.new $ V.length d
            M.write xn (V.length d-1) $! V.last df
            forM_ (reverse [0..V.length df-2]) $ \ x-> do
                let ci = cf V.! x
                    di = df V.! x
                xi1 <- M.read xn $ x+1
                M.write xn x $! di - ci*xi1
            V.unsafeFreeze xn
{-# INLINE tdmaSolver #-}
