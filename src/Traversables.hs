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
