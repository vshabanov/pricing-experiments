{-# LANGUAGE DerivingVia #-}
module Traversables where

import Data.Kind

class Traversable t => FromList (t :: Type -> Type) where
  fromList :: [a] -> t a

instance FromList n => FromList (T n) where
  fromList (a : n) = T a (fromList n)
instance FromList T1 where
  fromList [a] = T1 a
instance FromList T2 where
  fromList [a,b] = T2 a b
instance FromList T3 where
  fromList [a,b,c] = T3 a b c
instance FromList T4 where
  fromList [a,b,c,d] = T4 a b c d
instance FromList T5 where
  fromList [a,b,c,d,e] = T5 a b c d e
instance FromList T6 where
  fromList [a,b,c,d,e,f] = T6 a b c d e f
instance FromList T7 where
  fromList [a,b,c,d,e,f,g] = T7 a b c d e f g
instance FromList T8 where
  fromList [a,b,c,d,e,f,g,h] = T8 a b c d e f g h
instance FromList T9 where
  fromList [a,b,c,d,e,f,g,h,i] = T9 a b c d e f g h i
instance FromList T10 where
  fromList [a,b,c,d,e,f,g,h,i,j] = T10 a b c d e f g h i j
instance FromList T11 where
  fromList [a,b,c,d,e,f,g,h,i,j,k] = T11 a b c d e f g h i j k

-- | Traversable cons @T var traversable@
data T t a = T a (t a)
  deriving (Show, Functor, Foldable, Traversable)
data T1 a  = T1 { unT1 :: a }
  deriving (Show, Functor, Foldable, Traversable)
data T2 a  = T2 a a
  deriving (Show, Functor, Foldable, Traversable)
data T3 a  = T3 a a a
  deriving (Show, Functor, Foldable, Traversable)
data T4 a  = T4 a a a a
  deriving (Show, Functor, Foldable, Traversable)
data T5 a  = T5 a a a a a
  deriving (Show, Functor, Foldable, Traversable)
data T6 a  = T6 a a a a a a
  deriving (Show, Functor, Foldable, Traversable)
data T7 a  = T7 a a a a a a a
  deriving (Show, Functor, Foldable, Traversable)
data T8 a  = T8 a a a a a a a a
  deriving (Show, Functor, Foldable, Traversable)
data T9 a  = T9 a a a a a a a a a
  deriving (Show, Functor, Foldable, Traversable)
data T10 a = T10 a a a a a a a a a a
  deriving (Show, Functor, Foldable, Traversable)
data T11 a = T11 a a a a a a a a a a a
  deriving (Show, Functor, Foldable, Traversable)

newtype AppNum a = AppNum a

instance (Applicative t, Num a) => Num (AppNum (t a)) where
  AppNum x + AppNum y = AppNum $ liftA2 (+) x y
  AppNum x * AppNum y = AppNum $ liftA2 (*) x y
  abs (AppNum x) = AppNum $ abs <$> x
  signum (AppNum x) = AppNum $ signum <$> x
  fromInteger n = AppNum $ pure $ fromInteger n
  negate (AppNum x) = AppNum $ negate <$> x

deriving via AppNum (T t a) instance (Applicative t, Num a) => Num (T t a)
deriving via AppNum (T1 a)  instance Num a => Num (T1 a)
deriving via AppNum (T2 a)  instance Num a => Num (T2 a)
deriving via AppNum (T3 a)  instance Num a => Num (T3 a)
deriving via AppNum (T4 a)  instance Num a => Num (T4 a)
deriving via AppNum (T5 a)  instance Num a => Num (T5 a)
deriving via AppNum (T6 a)  instance Num a => Num (T6 a)
deriving via AppNum (T7 a)  instance Num a => Num (T7 a)
deriving via AppNum (T8 a)  instance Num a => Num (T8 a)
deriving via AppNum (T9 a)  instance Num a => Num (T9 a)
deriving via AppNum (T10 a) instance Num a => Num (T10 a)
deriving via AppNum (T11 a) instance Num a => Num (T11 a)

t2 (a,b) = T2 a b
t3 (a,b,c) = T3 a b c
t4 (a,b,c,d) = T4 a b c d
t5 (a,b,c,d,e) = T5 a b c d e
t6 (a,b,c,d,e,f) = T6 a b c d e f
t7 (a,b,c,d,e,f,g) = T7 a b c d e f g
t8 (a,b,c,d,e,f,g,h) = T8 a b c d e f g h
t9 (a,b,c,d,e,f,g,h,i) = T9 a b c d e f g h i
t10 (a,b,c,d,e,f,g,h,i,j) = T10 a b c d e f g h i j
t11 (a,b,c,d,e,f,g,h,i,j,k) = T11 a b c d e f g h i j k

instance Applicative t => Applicative (T t) where
  pure a = T a (pure a)
  liftA2 f (T a ta) (T b tb) = T (f a b) (liftA2 f ta tb)

------------------------------------------------------------------------------
-- Applicative instances generated by GitHub Copilot

instance Applicative T1 where
  pure a = T1 a
  liftA2 f (T1 a) (T1 b) = T1 (f a b)

instance Applicative T2 where
  pure a = T2 a a
  liftA2 f (T2 a0 a1) (T2 b0 b1) = T2 (f a0 b0) (f a1 b1)

instance Applicative T3 where
  pure a = T3 a a a
  liftA2 f (T3 a0 a1 a2) (T3 b0 b1 b2) = T3 (f a0 b0) (f a1 b1) (f a2 b2)

instance Applicative T4 where
  pure a = T4 a a a a
  liftA2 f (T4 a0 a1 a2 a3) (T4 b0 b1 b2 b3) = T4 (f a0 b0) (f a1 b1) (f a2 b2) (f a3 b3)

instance Applicative T5 where
  pure a = T5 a a a a a
  liftA2 f (T5 a0 a1 a2 a3 a4) (T5 b0 b1 b2 b3 b4) = T5 (f a0 b0) (f a1 b1) (f a2 b2) (f a3 b3) (f a4 b4)

instance Applicative T6 where
  pure a = T6 a a a a a a
  liftA2 f (T6 a0 a1 a2 a3 a4 a5) (T6 b0 b1 b2 b3 b4 b5) = T6 (f a0 b0) (f a1 b1) (f a2 b2) (f a3 b3) (f a4 b4) (f a5 b5)

instance Applicative T7 where
  pure a = T7 a a a a a a a
  liftA2 f (T7 a0 a1 a2 a3 a4 a5 a6) (T7 b0 b1 b2 b3 b4 b5 b6) = T7 (f a0 b0) (f a1 b1) (f a2 b2) (f a3 b3) (f a4 b4) (f a5 b5) (f a6 b6)

instance Applicative T8 where
  pure a = T8 a a a a a a a a
  liftA2 f (T8 a0 a1 a2 a3 a4 a5 a6 a7) (T8 b0 b1 b2 b3 b4 b5 b6 b7) = T8 (f a0 b0) (f a1 b1) (f a2 b2) (f a3 b3) (f a4 b4) (f a5 b5) (f a6 b6) (f a7 b7)

instance Applicative T9 where
  pure a = T9 a a a a a a a a a
  liftA2 f (T9 a0 a1 a2 a3 a4 a5 a6 a7 a8) (T9 b0 b1 b2 b3 b4 b5 b6 b7 b8) = T9 (f a0 b0) (f a1 b1) (f a2 b2) (f a3 b3) (f a4 b4) (f a5 b5) (f a6 b6) (f a7 b7) (f a8 b8)

instance Applicative T10 where
  pure a = T10 a a a a a a a a a a
  liftA2 f (T10 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) (T10 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) = T10 (f a0 b0) (f a1 b1) (f a2 b2) (f a3 b3) (f a4 b4) (f a5 b5) (f a6 b6) (f a7 b7) (f a8 b8) (f a9 b9)

instance Applicative T11 where
  pure a = T11 a a a a a a a a a a a
  liftA2 f (T11 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) (T11 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10) = T11 (f a0 b0) (f a1 b1) (f a2 b2) (f a3 b3) (f a4 b4) (f a5 b5) (f a6 b6) (f a7 b7) (f a8 b8) (f a9 b9) (f a10 b10)
