module Bump where

import Market
import Number

-- symd f x bump = (f (x+bump) - f (x-bump)) / (2*bump)
symd f x part bump = (f (x+part*bump) - f (x-part*bump)) / (2*bump)

bumpDiff f x bump = (f (x+bump) - f (x-bump)) / (2*bump)
bumpDiff2 f x bump = bumpDiff (\ x -> bumpDiff f x bump) x bump
bumpDiffMixed f x y h =
  bumpDiff (\ x -> bumpDiff (\ y -> f x y) y h) x h
dvdxUp :: N n => (Market n -> a -> n) -> Market n -> a -> Get n n -> n -> n
dvdxUp p mkt what x (bump :: n) =
  (p (modify x (+bump) mkt) what - p mkt what) / bump
dvdx' :: N n => (Market n -> a -> n) -> Market n -> a -> Get n n -> n -> n
dvdx' p mkt what x (bump :: n) =
  (p (modify x (+   bump ) mkt) what -
   p (modify x (+ (-bump)) mkt) what) / (2*bump)
dvdx2' p mkt what x bump = dvdx' (\ m w -> dvdx' p m w x bump) mkt what x bump
