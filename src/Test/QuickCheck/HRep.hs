{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Test.QuickCheck.HRep where

import Data.Kind
import Data.Proxy
import Data.Reflection

import GHC.TypeLits
import GHC.Generics

import Test.QuickCheck
import Test.QuickCheck.Branching

----------------------------------------
-- | Type level combinators

-- | Fix point of a functor
data Fix (f :: Type -> Type)
  = Fix (f (Fix f))

unFix :: Fix f ->  f (Fix f)
unFix (Fix f) = f

-- | Types tagged with an explicit generation frequency
newtype Freq f (n :: Nat) a
  = Tag (f a)
  deriving (Functor)

-- | Generic sum type
data Sum f g a
  = InL (f a)
  | InR (g a)
  deriving Functor

-- | Generic sum type with tagged terminals
data SizedSum f g a
  = Size0 (f a)
  | SizeN (g a)
  deriving (Functor)

deriving instance (Show (f (Fix f)))       => Show (Fix f)
deriving instance (Show (f a))             => Show (Freq f n a)
deriving instance (Show (f a), Show (g a)) => Show (Sum f g a)
deriving instance (Show (f a), Show (g a)) => Show (SizedSum f g a)

deriving instance (Generic (f (Fix f)))          => Generic (Fix f)
deriving instance (Generic (f a))                => Generic (Freq f n a)
deriving instance (Generic (f a), Generic (g a)) => Generic (Sum f g a)
deriving instance (Generic (f a), Generic (g a)) => Generic (SizedSum f g a)

----------------------------------------
-- | F-algebras over functors

class Functor f => Algebra f a | f -> a where
  alg :: f a -> a

-- | Catamorphisms, a.k.a generic foldings over fix points
cata :: Functor f => (f a -> a) -> Fix f -> a
cata f = f . fmap (cata f) . unFix

-- | Evaluation morphism
eval :: Algebra f a => Fix f -> a
eval = cata alg

-- | Single step morphism
step :: (Algebra f a, Algebra g a) => f (Fix g) -> a
step = alg . fmap eval

instance Algebra f a => Algebra (Freq f n) a where
  alg (Tag f) = alg f

instance (Algebra f a, Algebra g a) => Algebra (Sum f g) a where
  alg (InL f) = alg f
  alg (InR g) = alg g

instance (Algebra f a, Algebra g a) => Algebra (SizedSum f g) a where
  alg (Size0 f) = alg f
  alg (SizeN g) = alg g


----------------------------------------
-- | FixArbitrary class and instances

class Algebra f a => FixArbitrary f a where

  liftFix :: Algebra g a => Gen (Fix g) -> Gen (f (Fix g))

  genFix :: Gen (Fix f)
  genFix = arbitrary @(Fix f)

  genEval :: Gen a
  genEval = eval <$> genFix @f


-- | Calculate the sum of the frequencies in a composite type.
-- Defaults to 1 if no frequency tag is provided.
type family Frequency (f :: Type -> Type) :: Nat where
  Frequency (Freq _ n) = n
  Frequency (Sum f g) = Frequency f + Frequency g
  Frequency (SizedSum f g) = Frequency f + Frequency g
  Frequency _ = 1

-- | Type level frequency equality constraint
type t *> freq = (KnownNat freq, Frequency t ~ freq)

-- | Get the value of a type level frequency tag.
freqVal :: forall n. (KnownNat n, Reifies n Integer) => Int
freqVal = fromInteger (reflect (Proxy @n))


instance FixArbitrary f a => Arbitrary (Fix f) where
  arbitrary = Fix <$> liftFix arbitrary

instance FixArbitrary f a => FixArbitrary (Freq f n) a where
  liftFix gen = Tag <$> liftFix gen

instance (FixArbitrary f a, FixArbitrary g a, f *> ff, g *> fg)
    => FixArbitrary (Sum f g) a where
    liftFix gen = frequency
      [ (freqVal @ff, InL <$> liftFix gen)
      , (freqVal @fg, InR <$> liftFix gen) ]

instance (FixArbitrary f a, FixArbitrary g a, f *> ff, g *> fg)
    => FixArbitrary (SizedSum f g) a where
    liftFix gen = sized $ \n ->
      if n == 0
      then Size0 <$> liftFix gen
      else frequency
        [ (freqVal @ff, Size0 <$> liftFix gen)
        , (freqVal @fg, SizeN <$> liftFix gen) ]

----------------------------------------
-- | Branching instances

instance Branching f => Branching (Freq f n) where
  alias = alias @f
  terminals = terminals @f
  probs = probs @f
  beta = beta @f
  sigma = sigma @f

instance (Branching f, Branching g, f *> ff, g *> fg)
  => Branching (Sum f g) where
  alias = alias @f <> alias @g
  terminals = terminals @f <> terminals @g
  probs = probs @f <> probs @g
  beta = beta @f <> beta @g
  sigma = fmap (* (ff/tot)) (sigma @f) <> fmap (* (fg/tot)) (sigma @g)
    where ff = fromIntegral (freqVal @ff)
          fg = fromIntegral (freqVal @fg)
          tot = ff + fg

instance (Branching f, Branching g, f *> ff, g *> fg)
  => Branching (SizedSum f g) where
  alias = alias @f <> alias @g
  terminals = terminals @f <> terminals @g
  probs = probs @f <> probs @g
  beta = beta @f <> beta @g
  sigma = fmap (* (ff/tot)) (sigma @f) <> fmap (* (fg/tot)) (sigma @g)
    where ff = fromIntegral (freqVal @ff)
          fg = fromIntegral (freqVal @fg)
          tot = ff + fg

----------------------------------------
-- | Type families to reduce the noise

-- | A higher-order representation
type family HRep (t :: k) :: Type -> Type

-- | The higher-order representation of a single constructor
type family Con (c :: k) :: Type -> Type

-- | The higher order representation of a single pattern matching of a function
type family Pat (p :: Symbol) :: Type -> Type

-- | The higher-order representation of a function combinator
type family Fun (f :: Symbol) :: Type -> Type

-- | The higher-order representation of a given pattern matching of a function
type family Hash (f :: Symbol) (n :: Nat) :: Symbol


-- | Existential data types hiding type parameters
data Some1 (f :: Type -> Type -> Type) (r :: Type)
  = forall (a :: Type)
  . Some1 (f a r)
data Some2 (f :: Type -> Type -> Type -> Type) (r :: Type)
  = forall (b :: Type) (a :: Type)
  . Some2 (f a b r)
data Some3 (f :: Type -> Type -> Type -> Type -> Type) (r :: Type)
  = forall (c :: Type) (b :: Type) (a :: Type)
  . Some3 (f a b c r)
data Some4 (f :: Type -> Type -> Type -> Type -> Type -> Type) (r :: Type)
  = forall (d :: Type) (c :: Type) (b :: Type) (a :: Type)
  . Some4 (f a b c d r)
data Some5 (f :: Type -> Type -> Type -> Type -> Type -> Type -> Type) (r :: Type)
  = forall (e :: Type) (d :: Type) (c :: Type) (b :: Type) (a :: Type)
  . Some5 (f a b c d e r)

-- | Apply a data type to a type parameter hidden by an existential type
type family Apply (a :: Type) (t :: Type -> Type) where
  Apply a (Freq t n) = Freq (Apply a t) n
  Apply a (Sum l r) = Sum (Apply a l) (Apply a r)
  Apply a (SizedSum l r) = SizedSum (Apply a l) (Apply a r)
  Apply a (Some1 t) = t a
  Apply a (Some2 t) = Some1 (t a)
  Apply a (Some3 t) = Some2 (t a)
  Apply a (Some4 t) = Some3 (t a)
  Apply a (Some5 t) = Some4 (t a)
  Apply a t = t
