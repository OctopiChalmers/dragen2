{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FunctionalDependencies #-}

module Test.QuickCheck.Patterns.Rep where

import GHC.TypeLits (Nat, Symbol, KnownNat)
import qualified GHC.TypeLits as TL

import Data.Kind
import Data.Proxy
import Data.Reflection

import Test.QuickCheck

import Debug.Trace

----------------------------------------
-- | Fix point of a functor
data Fix (f :: Type -> Type)
  = Fix (f (Fix f))

unFix :: Fix f ->  f (Fix f)
unFix (Fix f) = f

deriving instance (Show (f (Fix f)) => Show (Fix f))

-- | Catamorphisms, a.k.a generic foldings over fix points
cata :: Functor f => (f a -> a) -> Fix f -> a
cata f = f . fmap (cata f) . unFix

-- | Evaluation morphism
eval :: Algebra f a => Fix f -> a
eval = cata alg

step :: (Algebra f a, Algebra g a) => f (Fix g) -> a
step = alg . fmap eval

----------------------------------------
-- | Types tagged with an explicit generation frequency

newtype (f @> (n :: Nat)) a
  = Tag (f a)
  deriving (Functor, Show)

infix 6 @>

----------------------------------------
-- | Extensible sum types.

-- | Generic sum type
data (f + g) a
  = InL (f a)
  | InR (g a)
  deriving Functor

infixr 5 +

deriving instance (Show (f a), Show (g a)) => Show ((f + g) a)

-- | Generic random choice sum type
-- This type is isomorphic to (:+:), but it's useful to distinguish them when
-- generating random values, since we can perform different generation schemas.
data (f ? g) a
  = Rnd (f a)
  | Pat (g a)
  deriving (Functor)

infixr 4 ?

deriving instance (Show (f a), Show (g a)) => Show ((f ? g) a)

-- Smart injections into sum types
class (Functor sub, Functor sup) => sub < sup where
  inj :: sub a -> sup a

infixr 3 <

instance Functor f => f < f where
  inj = id

instance Functor f => f < f @> n where
  inj = Tag

instance (Functor f, Functor g) => f < f + g where
  inj = InL

instance (Functor f, Functor g, Functor h, f < g) => f < h + g where
  inj = InR . inj

instance (Functor f, Functor g) => f < f ? g where
  inj = Rnd

instance (Functor f, Functor g, Functor h, f < g) => f < h ? g where
  inj = Pat . inj

inject :: f < g => f (Fix g) -> Fix g
inject = Fix . inj

----------------------------------------
-- | Some type families to reduce the noise

-- | Associate each type to its (isomorphic) canonical functor.
type family Rep (t :: Type) :: Type -> Type

-- | Associate each function name to its pattern-matching functor.
type family Pat (f :: Symbol) :: Type -> Type

-- | Build a sum type composed of a list of function names.
type family Sum (ps :: [Type -> Type]) :: Type -> Type where
  Sum '[f]      = f
  Sum (f ': fs) = f + Sum fs

-- | Calculate the sum of the frequencies in a sum type.
-- Defaults to 1 if no frequency tag is provided.
type family Frequency (f :: Type -> Type) :: Nat where
  Frequency (f + g) = Frequency f TL.+ Frequency g
  Frequency (f ? g) = Frequency f TL.+ Frequency g
  Frequency (_ @> n) = n
  Frequency t = 1

-- | Type level frequency equality constraint
type t @@> freq = (KnownNat freq, Frequency t ~ freq)

-- | Get the value of a type level frequency tag.
-- We need to use TypeApplications to break the ambiguity!
freqVal :: forall n. (KnownNat n, Reifies n Integer) => Int
freqVal = fromInteger (reflect (Proxy @n))

----------------------------------------
-- | F-algebras over functors

class Functor f => Algebra f a | f -> a where
  alg :: f a -> a

instance Algebra f a => Algebra (f @> n) a where
  alg (Tag f) = alg f

instance (Algebra f a, Algebra g a) => Algebra (f + g) a where
  alg (InL f) = alg f
  alg (InR g) = alg g

instance (Algebra f a, Algebra g a) => Algebra (f ? g) a where
  alg (Rnd f) = alg f
  alg (Pat g) = alg g

----------------------------------------
-- | Arbitrary and Arbitrary1 instances

{- |
class Arbitrary1 f where
  liftArbitrary :: Gen a -> Gen (f a)
  liftShrink    :: (a -> [a]) -> f a -> [f a]

arbitrary1 :: (Arbitrary1 f, Arbitrary a) => Gen (f a)
arbitrary1 = liftArbitrary arbitrary

-- Sadly, Arbitary1 is too general for us, since we need to tranform our f's
-- into their target type while generating patterns in order to avoid generating
-- pattern overlapped values.

-- | Arbitrary plumbing for fixpoints
instance Arbitrary1 f => Arbitrary (Fix f) where
  arbitrary = Fix <$> arbitrary1

-- | Arbitrary plumbing for tagged values
instance Arbitrary1 f => Arbitrary1 (f @> n) where
  liftArbitrary gen = Tag <$> liftArbitrary gen

-- | Random generation of sum types, following the type level frequencies
instance (Arbitrary1 f, Arbitrary1 g, f @@> freq_f, g @@> freq_g)
    => Arbitrary1 (f + g) where
    liftArbitrary gen
      = frequency
      [(freqVal @freq_f, InL <$> liftArbitrary gen)
      ,(freqVal @freq_g, InR <$> liftArbitrary gen)]

-- | Generation of random choice types, following the type level frequencies
instance (Arbitrary1 f, Arbitrary1 g, f @@> freq_f, g @@> freq_g)
    => Arbitrary1 (Choice f g) where
    liftArbitrary gen = sized $ \n ->
      if n == 0 then Rnd <$> liftArbitrary gen
      else frequency
           [(freqVal @freq_f, Rnd <$> liftArbitrary gen)
           ,(freqVal @freq_g, Pat <$> liftArbitrary gen)]

-}

class Algebra f a => FixArbitrary f a where
  liftFix :: Algebra g a => Gen (Fix g) -> Gen (f (Fix g))

  fixGen :: Gen a
  fixGen = eval <$> (arbitrary :: Gen (Fix f))

-- | Arbitrary plumbing for tagged values
instance FixArbitrary f a => FixArbitrary (f @> n) a where
  liftFix gen = Tag <$> liftFix gen

-- | Random generation of sum types, following the type level frequencies
instance (FixArbitrary f a, FixArbitrary g a,
          f @@> freq_f, g @@> freq_g)
    => FixArbitrary (f + g) a where
    liftFix gen
      = frequency
        [(freqVal @freq_f, InL <$> liftFix gen)
        ,(freqVal @freq_g, InR <$> liftFix gen)]

-- | Random generation of choice types, following the type level frequencies
instance (FixArbitrary f a, FixArbitrary g a,
          f @@> freq_f, g @@> freq_g)
    => FixArbitrary (f ? g) a where
    liftFix gen = sized $ \n ->
      if n == 0 then Rnd <$> liftFix gen
      else frequency
        [(freqVal @freq_f, Rnd <$> liftFix gen)
        ,(freqVal @freq_g, Pat <$> liftFix gen)]

instance FixArbitrary f a => Arbitrary (Fix f) where
  arbitrary = Fix <$> liftFix arbitrary


-- Some generators utilities
smaller :: Gen a -> Gen a
smaller g = sized $ \size -> resize (max (size - 1) 0) g

reduce :: Int -> Gen a -> Gen a
reduce n g = sized $ \size -> resize (max (size - n) 0) g

satisfy :: String -> Gen a -> (a -> Bool) -> Gen a
satisfy nm gen p = do
  v <- gen
  case p v of
    True -> return v
    False -> trace ("\n[RETRYING: " ++ nm ++ "]") $ satisfy nm gen p

----------------------------------------
-- | Top-level representations

type Interleave (t :: Type) (tf :: Nat) (pats :: [Type -> Type])
  = Rep t @> tf ? Sum pats
