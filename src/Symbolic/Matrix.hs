{-# OPTIONS_GHC -Wincomplete-patterns #-}
-- | Symbolic matrix
module Symbolic.Matrix
  ( M, (!)
  ) where

import Data.Array
import Data.List (intercalate)
import Text.Printf
import Symbolic

newtype M a = M (Array (Int, Int) a)

instance Show a => Show (M a) where
  show (M a)
    | sum widths + 2*(n - 1) <= 80 = unlines
      [intercalate "  " [center w (s ! (r,c)) | (w,c) <- zip widths [0..n-1]]
      |r <- [0..m-1]]
    | otherwise = unlines
      [printf "[%2d,%2d]  %s" r c (s ! (r,c)) | c <- [0..n-1], r <- [0..m-1]]
    where
      center w s = replicate padLeft ' ' <> s <> replicate (w - l - padLeft) ' '
        where
          l = length s
          padLeft = (w - l) `div` 2
      s = show <$> a
      (m,n) = msize (M a)

      widths = [maximum [length (s ! (r,c)) | r <- [0..m-1]] | c <- [0..n-1]]

msize (M a) = (m+1,n+1)
  where
    ((0,0), (m,n)) = bounds a

matrix :: Int -> Int -> [[a]] -> M a
matrix m n l
  | length l /= m =
    error $ printf "matrix %d %d: %d rows provided" m n (length l)
  | (bad:_) <- filter ((/= n) . length) l =
    error $ printf "matrix %d %d: row of size %d provided %s" m n (length bad)
  | otherwise =
    M $ listArray ((0,0), (m-1,n-1)) $ concat l

test :: M (Expr Double)
test =
  matrix 2 2 [["a","b"],["c","d"]]
--   matrix 3 3 [["a","b","c"],["d","e","f"],["g","h","i"]]
--   matrix 4 4 [["a","b","c","d"],["e","f","g","h"],["i","j","k","l"],["m","n","o","p"]]
--  matrix 3 2 [["a","b"],["c",diff "ddddd*exp(x/log x)" "x"],["f","g"]]

determinant mat
  | m /= n = error $ printf
    "determinant: matrix must be square; found %d rows, %d columns" m n
  | m == 1 = mat!.(0,0)
  | otherwise =
    -- https://en.wikipedia.org/wiki/Laplace_expansion
    sum [mat!.(0,c) * cofactor 0 c mat | c <- [0..n-1]]
  where
    (m,n) = msize mat

infixl 9 !. -- as !
M a !. i = a ! i

cofactor r c mat = (if (-1)^(r+c) == 1 then id else negate) $ minor r c mat

invert :: Fractional a => M a -> M a
invert m = mapi (\ _ _ x -> x / determinant m) $ adjoint m

adjoint :: Num a => M a -> M a
adjoint = transpose . comatrix

comatrix :: Num a => M a -> M a
comatrix m = mapi (\ r c _ -> cofactor r c m) m

mapi f mat = matrix m n
    [[f mr mc (mat!.(mr,mc)) | mc <- [0..n-1]] | mr <- [0..m-1]]
  where
    (m,n) = msize mat

minor r c m = determinant $ strikeOut r c m

transpose mat = matrix n m
    [[mat!.(mr,mc) | mr <- [0..m-1]] | mc <- [0..n-1]]
  where
    (m,n) = msize mat

strikeOut r c mat
  | r < 0 || c < 0 =
    error $ printf "submatrix %d %d: row or column can't be negative"
  | r >= m || c >= n =
    error $ printf "submatrix %d %d: matrix (%d x %d) is too small"
  | otherwise = matrix (m-1) (n-1) $
    [[mat!.(mr,mc) | mc <- [0..n-1], mc /= c] | mr <- [0..m-1], mr /= r]
  where
    (m,n) = msize mat
