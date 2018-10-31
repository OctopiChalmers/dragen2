{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Test.QuickCheck.Patterns.Rep where

import GHC.TypeLits
import Data.Kind
import Data.Proxy
import Data.Reflection

import Test.QuickCheck

----------------------------------------
-- | Fix point of a functor
data Fix (f :: Type -> Type)
  = Fix { unFix :: (f (Fix f)) }

deriving instance (Show (f (Fix f)) => Show (Fix f))

-- | Catamorphisms, a.k.a generic foldings over fix points
cata :: Functor f => (f a -> a) -> Fix f -> a
cata f = f . fmap (cata f) . unFix

-- | Evaluation morphism
eval :: (Functor f, Algebra f a) => Fix f -> a
eval = cata alg

----------------------------------------
-- | Types tagged with an explicit generation frequency

newtype (f :> (n :: Nat)) a
  = Tag (f a)
  deriving (Functor, Show)

infix 6 :>

----------------------------------------
-- | Extensible sum types.

-- | Generic sum type
data (f :+: g) a
  = InL (f a)
  | InR (g a)
  deriving Functor

infixr 5 :+:

deriving instance (Show (f a), Show (g a)) => Show ((f :+: g) a)

-- | Generic random choice sum type
-- This type is isomorphic to (:+:), but it's useful to distinguish them when
-- generating random values, since we can perform different generation schemas.
data (f :?: g) a
  = Rnd (f a)
  | Pat (g a)
  deriving (Functor)

infixr 4 :?:

deriving instance (Show (f a), Show (g a)) => Show ((f :?: g) a)

----------------------------------------
-- | Some type families to reduce the noise

-- | Associate each type to its (isomorphic) pattern functor.
type family PF (t :: Type) :: Type -> Type

-- | Associate each function to its pattern-matching functor.
type family Pat (f :: Symbol) :: Type -> Type

-- | Build a sum type composed of a list of function names.
type family Sum (ps :: [Type -> Type]) :: Type -> Type where
  Sum '[f]      = f
  Sum (f ': fs) = f :+: Sum fs

-- | Calculate the sum of the frequencies in a sum type.
-- Defaults to 1 if no frequency tag is provided.
type family Frequency (f :: Type -> Type) :: Nat where
  Frequency (f :+: g) = Frequency f + Frequency g
  Frequency (_ :> n) = n
  Frequency t = 1

-- | Type level frequency equality constraint
type t ::> freq = (KnownNat freq, Frequency t ~ freq)

-- | Get the value of a type level frequency tag.
-- We need to use TypeApplications to break the ambiguity!
freqVal :: forall n. (KnownNat n, Reifies n Integer) => Int
freqVal = fromInteger (reflect (Proxy @n))

----------------------------------------
-- | F-algebras over functors

class Algebra f a where
  alg :: f a -> a

instance Algebra f a => Algebra (f :> n) a where
  alg (Tag f) = alg f

instance (Algebra f a, Algebra g a) => Algebra (f :+: g) a where
  alg (InL f) = alg f
  alg (InR g) = alg g

instance (Algebra f a, Algebra g a) => Algebra (f :?: g) a where
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

shrink1 :: (Arbitrary1 f, Arbitrary a) => f a -> [f a]
shrink1 = liftShrink shrink
-}

-- | Arbitrary plumbing for fixpoints
instance Arbitrary1 f => Arbitrary (Fix f) where
  arbitrary = Fix <$> arbitrary1

-- | Arbitrary plumbing for tagged values
instance Arbitrary1 f => Arbitrary1 (f :> n) where
  liftArbitrary gen = Tag <$> liftArbitrary gen

-- | Random generation of sum types, following the type level frequencies
instance (Arbitrary1 f, Arbitrary1 g, f ::> freq_f, g ::> freq_g)
    => Arbitrary1 (f :+: g) where
    liftArbitrary gen
      = frequency
      [(freqVal @freq_f, InL <$> liftArbitrary gen)
      ,(freqVal @freq_g, InR <$> liftArbitrary gen)]

-- | Generation of random choice types, following the type level frequencies
instance (Arbitrary1 f, Arbitrary1 g, f ::> freq_f, g ::> freq_g)
    => Arbitrary1 (f :?: g) where
    liftArbitrary gen = sized $ \n ->
      if n == 0 then Rnd <$> liftArbitrary gen
      else frequency
           [(freqVal @freq_f, Rnd <$> liftArbitrary gen)
           ,(freqVal @freq_g, Pat <$> liftArbitrary gen)]

----------------------------------------
-- | Top-level representations

type Interleave (t :: Type) (ps :: [Type -> Type]) = Fix (PF t :?: Sum ps)
