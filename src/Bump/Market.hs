module Bump.Market where

import Market
import Number

dvdxUp :: N n => (Market n -> a -> n) -> Market n -> a -> Get n n -> n -> n
dvdxUp p mkt what x (bump :: n) =
  (p (modify x (+bump) mkt) what - p mkt what) / bump
dvdx' :: N n => (Market n -> a -> n) -> Market n -> a -> Get n n -> n -> n
dvdx' p mkt what x (bump :: n) =
  (p (modify x (+   bump ) mkt) what -
   p (modify x (+ (-bump)) mkt) what) / (2*bump)
dvdx2' p mkt what x bump = dvdx' (\ m w -> dvdx' p m w x bump) mkt what x bump
