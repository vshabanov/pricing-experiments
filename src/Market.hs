{-# LANGUAGE GADTs #-}

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
  , VolInput(..)
  , Smile(..), impliedVol, localVol -- TODO: separate the market and inputs
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

import Data.Maybe
import qualified Control.Monad.State.Strict as S
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Unsafe.Coerce

import Tenor

-- | @Get n a@ some data from the @Market n@ with type @a@
data Get n a where
  -- inputs (usually), not a separate type to make 'get' work uniformly
  -- with inputs and nodes
  Spot :: Get a a
  Vol :: Tenor -> VolInput -> Get a a
  RateDom :: Get a a
  RateFor :: Get a a
  PricingDate :: Get a a

  -- nodes
  Smile :: Get a (a -> Smile a) -- ^ time -> smile

data Smile a
  = Smile_
    { smileImpliedVol :: a -> a -- ^ strike -> implied vol
    , smileLocalVol   :: a -> a -- ^ strike -> local vol
    }

impliedVol mkt τ k = smileImpliedVol (get Smile mkt τ) k
localVol   mkt τ k = smileLocalVol   (get Smile mkt τ) k


deriving instance Eq (Get n a)
deriving instance Ord (Get n a)
deriving instance Show (Get n a)

data VolInput
  = ATMVol
  | RR25
  | BF25
  | RR10
  | BF10
  deriving (Show, Eq, Ord)

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

data Node n a where
  InputNode :: Get a a -> Node a a
  Pure :: a -> Node n a
  Ap   :: Node n (a -> b) -> Node n a -> Node n b

instance Show (Node n a) where
  showsPrec d n
    | d > 10 = ('(':) . showsPrec 0 n . (')':)
    | otherwise = case n of
      InputNode n -> ("InputNode " <>) . showsPrec 11 n
      Pure _ -> ("Pure ?" <>)
      Ap f x -> showsPrec d f . (" " <>) .
        showsPrec 11 x

instance Functor (Node a) where
  fmap f x = pure f <*> x

instance Applicative (Node a) where
  pure  = Pure
  (<*>) = Ap

evalNode :: Node n a -> Market n -> a
evalNode n m = case n of
  InputNode i ->
    fromMaybe (error $ "Input not found " <> show i) $ Map.lookup i (mInputs m)
  Pure x -> x
  Ap f x -> evalNode f m $ evalNode x m

data Market n
  = Market
    { mInputs :: Map (Get n n) n
    , mNodes :: Map AnyGet AnyNode
    }
  deriving Show

newtype Recipe n a = Recipe { runRecipe :: S.State (Market n) a }
  deriving (Functor, Applicative, Monad)

buildMarket r = S.execState (runRecipe r) $
  Market { mInputs = Map.empty, mNodes = Map.empty }

input :: Get n n -> n -> Recipe n (Node n n)
input i x = Recipe $ do
  S.modify (\ m -> m { mInputs = Map.insert i x $ mInputs m })
  runRecipe $ node i $ InputNode i

node :: Get n a -> Node n a -> Recipe n (Node n a)
node get n = Recipe $ do
  S.modify (\ m -> m { mNodes = Map.insert (toAnyGet get) (toAnyNode n) $ mNodes m })
  pure n

get :: Get n a -> Market n -> a
get g m = case Map.lookup (toAnyGet g) (mNodes m) of
  Nothing -> error $ "Node not found " <> show g
  Just n -> evalNode (unsafeFromAnyNode n) m

inputs :: Market a -> [(Get a a, a)]
inputs = Map.toList . mInputs

modify :: Get a a -> (a -> a) -> Market a -> Market a
modify i f = modifyList [(i, f)]

modifyList :: [(Get a a, (a -> a))] -> Market a -> Market a
modifyList l m = m {
  -- FIXME: we can modify nodes as well
  -- FIXME: test that the node exists
  mInputs = Map.differenceWith
    (\ x f -> Just $ f x) (mInputs m) (Map.fromList l)
  }

coerceGet :: Get a a -> Get b b
coerceGet = unsafeCoerce

mkt = buildMarket $ do
  input Spot 1
  input RateDom 0.1
  v1d <- input (Vol "1D" ATMVol) 0.1
  v1y <- input (Vol "1Y" ATMVol) 0.2
  node Smile $ (\ v1 v2 t -> Smile_ (*(v1*v2*t)) (*t)) <$> v1d <*> v1y
