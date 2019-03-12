{-# OPTIONS_GHC -fno-warn-unticked-promoted-constructors #-}
module Test.Dragen.Struct.TypeLevel where

import Data.Kind
import Data.Proxy
import Data.Reflection

import GHC.TypeLits

----------------------------------------
-- | Useful type families

type family
  Length (xs :: [k]) :: Nat where
  Length '[]      = 0
  Length (_ : xs) = 1 + Length xs

type family
  Lookup (map :: [(k, v)]) (key :: k) :: v where
  Lookup ('(k, v) : m) k = v
  Lookup (_       : m) k = Lookup m k
  Lookup '[]           k
    = TypeError (Text "Lookup: key not found" :<>: ShowType k)

type family
  Ix (map :: [(k, v)]) (key :: k) :: Nat where
  Ix ('(k,  _) : m) k = 0
  Ix ('(k', _) : m) k = 1 + Ix m k
  Ix '[]            k = TypeError (Text "Ix: key not found" :<>: ShowType k)

type family
  Keys (map :: [(k, v)]) :: [k] where
  Keys '[] = '[]
  Keys ('(k, _) : kvs) = k : Keys kvs

type family
  Values (map :: [(k, v)]) :: [v] where
  Values '[] = '[]
  Values ('(_, v) : kvs) = v : Values kvs

type family
  (++) (f :: [k]) (g :: [k]) :: [k] where
  (++) '[]      g = g
  (++) (f : fs) g = f : (fs ++ g)

type family
  (==) (f :: k) (g :: k) :: Bool where
  (==) t t = True
  (==) _ _ = False

type family
  FailWhen (n :: Bool) (f :: Type -> Type) (msg :: Symbol) :: Constraint where
  FailWhen True f msg = TypeError (ShowType f :<>: Text ":" :<>: Text msg)
  FailWhen _    _ _   = ()

----------------------------------------
-- | Reflection utilities

-- | Reflect a type level Nat as a Num
numVal :: forall n a. (KnownNat n, Reifies n Integer, Num a) => a
numVal = fromIntegral (reflect (Proxy @n))

-- | Reflect the lenght of a type level list as a Num
lengthVal :: forall xs n a. (Length xs ~ n, KnownNat n, Num a) => a
lengthVal = numVal @n


-- | Reflect a list of Nats
class KnownNats (ns :: [Nat]) where
  natVals  :: Proxy ns -> [Integer]

instance KnownNats '[] where
  natVals  _ = []

instance (KnownNat n, KnownNats ns) => KnownNats (n : ns) where
  natVals  _ = natVal  (Proxy @n) : natVals (Proxy @ns)

-- | Reflect a list of list of Nats
class KnownNatss (ns :: [[Nat]]) where
  natValss :: Proxy ns -> [[Integer]]

instance KnownNatss '[] where
  natValss  _ = []

instance (KnownNats n, KnownNatss ns) => KnownNatss (n : ns) where
  natValss _ = natVals  (Proxy @n) : natValss (Proxy @ns)
