module Bump.Pure where

-- symd f x bump = (f (x+bump) - f (x-bump)) / (2*bump)
symd f x part bump = (f (x+part*bump) - f (x-part*bump)) / (2*bump)

bumpDiff f x bump = (f (x+bump) - f (x-bump)) / (2*bump)
bumpDiff2 f x bump = bumpDiff (\ x -> bumpDiff f x bump) x bump
bumpDiffMixed f x y h =
  bumpDiff (\ x -> bumpDiff (\ y -> f x y) y h) x h
