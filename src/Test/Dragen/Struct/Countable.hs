{-# LANGUAGE KindSignatures  #-}
{-# LANGUAGE DefaultSignatures  #-}

module Test.Dragen.Struct.Countable where

import GHC.Generics
import Data.Kind

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- | A map that associates constructors names and the times each one appears
-- within a value.
type ConsCount = Map String Int
type ConsAvg   = Map String Double

(+++) :: ConsCount -> ConsCount -> ConsCount
(+++) = Map.unionWith (+)

combine :: [ConsCount] -> ConsCount
combine = Map.unionsWith (+)

empty :: ConsCount
empty = Map.empty

singleton :: String -> ConsCount
singleton = flip Map.singleton 1

consAvg :: [ConsCount] -> ConsAvg
consAvg counts = norm <$> combine counts
  where norm c = fromIntegral c / fromIntegral (length counts)

--------------------------------------------------------------------------------

defaultCount :: (Generic a, GCountable (Rep a)) => a -> ConsCount
defaultCount a = gcount (from a)

instance (GCountable (Rep a), Generic a) => Countable a
instance (GCountable1 (Rep1 f), Generic1 f) => Countable1 f

--------------------------------------------------------------------------------

class Countable (a :: Type) where
    count :: a -> ConsCount
    default count :: (Generic a, GCountable (Rep a)) => a -> ConsCount
    count = gcount . from


class GCountable f where
    gcount :: f a -> ConsCount


instance GCountable (URec a) where
    gcount _ = empty

instance GCountable V1 where
    gcount _ = empty

instance GCountable U1 where
    gcount U1 = empty

instance Countable a => GCountable (K1 i a) where
    gcount (K1 x) = count x

instance (GCountable f, GCountable g) => GCountable (f :*: g) where
    gcount (f :*: g)  = gcount f +++ gcount g

instance (GCountable f, GCountable g) => GCountable (f :+: g) where
    gcount (L1 x) = gcount x
    gcount (R1 x) = gcount x

instance (Constructor c, GCountable f) => GCountable (C1 c f) where
    gcount c@(M1 inner) = singleton (conName c) +++ gcount inner

instance GCountable f => GCountable (D1 c f) where
    gcount (M1 x) = gcount x

instance GCountable f => GCountable (S1 c f) where
    gcount (M1 x) = gcount x

--------------------------------------------------------------------------------

class Countable1 (f :: Type -> Type) where
    count1 :: f a -> ConsCount
    default count1 :: (Generic1 f, GCountable1 (Rep1 f)) => f a -> ConsCount
    count1 = gcount1 . from1


class GCountable1 f where
    gcount1 :: f a -> ConsCount


instance GCountable1 V1 where
    gcount1 _ = empty

instance GCountable1 U1 where
    gcount1 U1 = empty

instance GCountable1 Par1 where
    gcount1 (Par1 _) = empty

instance (Countable1 f) => GCountable1 (Rec1 f) where
    gcount1 (Rec1 a) = count1 a

instance (GCountable1 f, GCountable1 g) => GCountable1 (f :*: g) where
    gcount1 (f :*: g)  = gcount1 f +++ gcount1 g

instance (GCountable1 f, GCountable1 g) => GCountable1 (f :+: g) where
    gcount1 (L1 x) = gcount1 x
    gcount1 (R1 x) = gcount1 x

instance (Constructor c, GCountable1 f) => GCountable1 (C1 c f) where
    gcount1 con@(M1 inner) = singleton (conName con) +++ gcount1 inner

instance GCountable1 f => GCountable1 (D1 c f) where
    gcount1 (M1 x) = gcount1 x

instance GCountable1 f => GCountable1 (S1 c f) where
    gcount1 (M1 x) = gcount1 x
