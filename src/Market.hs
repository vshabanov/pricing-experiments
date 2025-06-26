{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

{- | Quick and dirty way to build computations based on modifiable inputs.

After 'buildMarket' you can get 'inputs' list and run the AD jacobian
to get derivatives for all those inputs

@
mkt = buildMarket $ do
  input Spot 1
  input RateDom 0.1
  v1d <- input (Vol "1D" ATMVol) 0.1
  v1y <- input (Vol "1Y" ATMVol) 0.2
  node GetATMVol $ (\ v1 v2 t -> v1*v2*t) <$> v1d <*> v1y

...
get GetATMVol (modify Spot (+1) mkt) 1
@
-}
module Market
  ( -- * Market and its inputs
    Market
  , Get(..)
  , impliedVol, localVol, impliedVol'k, localVol's, smileAt
    -- TODO: separate the market and inputs
    -- * Building a new market
  , buildMarket, input, node, Recipe, Node
    -- * Changing inputs
  , modify
  , modifyList
    -- * Querying a market
  , get
  , inputs
    -- * Utils
  , coerceGet
  ) where

import Analytic.Pure
import Control.Monad.State.Strict qualified as S
import Data.Bifunctor
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.MemoUgly
import Tenor
import Unique
import Unsafe.Coerce
import VolSurface

-- | @Get n a@ some data from the @Market n@ with type @a@
data Get n a where
  -- inputs (usually), not a separate type to make 'get' work uniformly
  -- with inputs and nodes
  Spot :: Get a a
  Vol  :: Tenor -> VolInput -> Get a a
  RateDom :: Get a a
  RateFor :: Get a a
  PricingDate :: Get a a

  -- nodes
  VolSurface :: Get a (VolSurface a)

smileAt :: a -> Market a -> Smile a
smileAt t mkt = (unMemo $ volSurfaceSmileAt $ get VolSurface mkt) t

impliedVol'k mkt = smileImpliedVol'k . flip smileAt mkt
impliedVol   mkt = smileVol
                 . smileImpliedVol   . flip smileAt mkt
localVol     mkt = smileLocalVol     . flip smileAt mkt
localVol's   mkt = smileLocalVol's   . flip smileAt mkt

deriving instance Eq (Get n a)
deriving instance Ord (Get n a)
deriving instance Show (Get n a)

newtype AnyGet = AnyGet (Get () ())
  deriving (Eq, Ord, Show)

toAnyGet :: Get n a -> AnyGet
toAnyGet = AnyGet . unsafeCoerce

newtype AnyNode = AnyNode (Node () ())
  deriving (Show)

toAnyNode :: Node n a -> AnyNode
toAnyNode = AnyNode . unsafeCoerce

unsafeFromAnyNode :: AnyNode -> Node n a
unsafeFromAnyNode (AnyNode n) = unsafeCoerce n

data CmpFirst a b = CmpFirst a b
instance Eq a => Eq (CmpFirst a b) where
  CmpFirst a _ == CmpFirst b _ = a == b
instance Ord a => Ord (CmpFirst a b) where
  CmpFirst a _ `compare` CmpFirst b _ = compare a b

data Node n a where
  InputNode :: Get a a -> Node a a
  Pure :: !I -> a -> Node n a
  Ap   :: !(CmpFirst (I,I) b -> (I,b)) -- ^ memoization function
       -> Node n (a -> b) -> Node n a -> Node n b

instance Show (Node n a) where
  showsPrec d n
    | d > 10 = ('(':) . showsPrec 0 n . (')':)
    | otherwise = case n of
      InputNode n -> ("InputNode " <>) . showsPrec 11 n
      Pure _ _ -> ("Pure ?" <>)
      Ap _ f x -> showsPrec d f . (" " <>) .
        showsPrec 11 x

instance Functor (Node a) where
  fmap f x = pure f <*> x

instance Applicative (Node a) where
  pure x = withNewId $ \ i -> Pure i x
  (<*>) f = Ap (memo $ \ (CmpFirst _ b) -> withNewId (,b)) f

evalNode :: Node n a -> Market n -> (I, a)
evalNode n m = case n of
  InputNode i ->
    fromMaybe (error $ "Input not found " <> show i) $ Map.lookup i (mInputs m)
  Pure i x -> (i,x)
  Ap memofx f x ->
    let (fi, fe) = evalNode f m
        (xi, xe) = evalNode x m
        r@(ri,_) = memofx $ CmpFirst (fi,xi) (fe xe)
    in
--      trace (show (fi,xi,ri)) $
      fi `seq`
      -- For some unbeknown reason we need this not to get <<loop>>
      -- in compiled version. For GHCi it's enough to make (<*>) f = Ap .. f
      r

data Market n
  = Market
    { mInputs :: Map (Get n n) (I,n)
    , mNodes :: Map AnyGet AnyNode
    }
  deriving Show

newtype Recipe n a = Recipe { runRecipe :: S.State (Market n) a }
  deriving newtype (Functor, Applicative, Monad)

buildMarket r = S.execState (runRecipe r) $
  Market { mInputs = Map.empty, mNodes = Map.empty }

input :: Get n n -> n -> Recipe n (Node n n)
input g x = Recipe $ do
  withNewId $ \ i -> S.modify $ \ m ->
    m { mInputs = Map.insert g (i,x) $ mInputs m }
  runRecipe $ node g $ InputNode g

node :: Get n a -> Node n a -> Recipe n (Node n a)
node get n = Recipe $ do
  S.modify $ \ m ->
    m { mNodes = Map.insert (toAnyGet get) (toAnyNode n) $ mNodes m }
  pure n

get :: Get n a -> Market n -> a
get g m = case Map.lookup (toAnyGet g) (mNodes m) of
  Nothing -> error $ "Node not found " <> show g
  Just n -> snd $ evalNode (unsafeFromAnyNode n) m

inputs :: Market a -> [(Get a a, a)]
inputs = map (second snd) . Map.toList . mInputs

modify :: Get a a -> (a -> a) -> Market a -> Market a
modify i f = modifyList [(i, f)]

modifyList :: [(Get a a, (a -> a))] -> Market a -> Market a
modifyList l m = m {
  -- FIXME: we can modify nodes as well
  -- FIXME: test that the node exists
  mInputs = Map.differenceWith
    (\ (_,x) f -> withNewId $ \ i -> Just (i, f x)) (mInputs m) (Map.fromList l)
  }

coerceGet :: Get a a -> Get b b
coerceGet = unsafeCoerce

mkt = buildMarket $ do
  input Market.Spot 1
  input RateDom 0.1
  v1d <- input (Vol "1D" ATMVol) 0.1
  v1y <- input (Vol "1Y" ATMVol) 0.2
  pure ()
--  node Smile $ (\ v1 v2 t -> Smile_ (*(v1*v2*t)) (*t) (*t) (*t) []) <$> v1d <*> v1y
