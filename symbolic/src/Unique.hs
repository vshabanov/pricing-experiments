module Unique
  (I, withNewId)
  where

import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

withNewId :: (I -> a) -> a
withNewId f = unsafePerformIO $ newId >>= pure . f

-- | Unique subexpression id to help with sharing
type I = Int

-- 2^63/1e9/86400/365 = 292 years, should be enough.
-- And 1Gz atomic increment is barely possible (more like 200MHz).
idSource :: IORef Int
idSource = unsafePerformIO (newIORef 0)
{-# NOINLINE idSource #-}

newId :: IO Int
newId = atomicModifyIORef' idSource $ \x -> let z = x+1 in (z,z)
