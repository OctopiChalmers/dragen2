{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
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

----------------------------------------
-- | Type level combinators

-- | Fix point of a functor
data Fix (f :: Type -> Type)
  = Fix (f (Fix f))

unFix :: Fix f ->  f (Fix f)
unFix (Fix f) = f

-- | Empty type
data Void :: Type -> Type

-- | Types tagged with an explicit generation frequency
newtype Freq f (n :: Nat) a
  = FreqTag (f a)
  deriving Functor

-- | Types tagged to represent terminal constructors
data Term f a
  = TermTag (f a)
  deriving Functor

-- | Generic sum type
data Sum f g a
  = InL (f a)
  | InR (g a)
  deriving Functor


deriving instance (Show (f (Fix f)))       => Show (Fix f)
deriving instance (Show (f a))             => Show (Freq f n a)
deriving instance (Show (f a))             => Show (Term f a)
deriving instance (Show (f a), Show (g a)) => Show (Sum f g a)

deriving instance (Generic (f (Fix f)))          => Generic (Fix f)
deriving instance (Generic (f a))                => Generic (Freq f n a)
deriving instance (Generic (f a))                => Generic (Term f a)
deriving instance (Generic (f a), Generic (g a)) => Generic (Sum f g a)

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
  alg (FreqTag f) = alg f

instance Algebra f a => Algebra (Term f) a where
  alg (TermTag f) = alg f

instance (Algebra f a, Algebra g a) => Algebra (Sum f g) a where
  alg (InL f) = alg f
  alg (InR g) = alg g

----------------------------------------
-- | FixArbitrary class and instances

-- | Branching frequencies in a sum type.
-- Defaults to 1 if no frequency tag is provided.
type family Frequency (f :: Type -> Type) :: Nat where
  Frequency (Freq f n) = n * Frequency f
  Frequency (Term f) = Frequency f
  Frequency (Sum f g) = Frequency f + Frequency g
  Frequency _ = 1

-- | Terminal frequencies in a sum type.
-- Defaults to 1 if no frequency tag is provided.
type family Frequency' (f :: Type -> Type) :: Nat where
  Frequency' (Freq f n) = n * Frequency' f
  Frequency' (Term f) = Frequency f
  Frequency' (Sum f g) = Frequency' f + Frequency' g
  Frequency' _ = 0

-- | Get the value of a type level frequency tag.
numVal :: forall n a. (KnownNat n, Reifies n Integer, Num a) => a
numVal = fromIntegral (reflect (Proxy @n))

type family HasTerminals (f :: Type -> Type) :: Constraint where
  HasTerminals f = ErrorIfZero (Frequency' f) f

type family ErrorIfZero (n :: Nat) (f :: Type -> Type) :: Constraint where
  ErrorIfZero 0 f = TypeError
    ('Text "the type representation: " ':<>: 'ShowType f
      ':<>: 'Text " has no terminal constructions")
  ErrorIfZero _ _ = ()


-- | Type level frequency equality constraint
type t #> freq = (KnownNat freq, Frequency  t ~ freq)
type t @> freq = (KnownNat freq, Frequency' t ~ freq)

type HasFixArbitrary hrep target
  = (FixArbitrary hrep target, HasTerminals hrep)

class Algebra f a => FixArbitrary f a where

  liftFix :: Algebra g a => Gen (Fix g) -> Gen (f (Fix g))

  genFix :: HasTerminals f => Gen (Fix f)
  genFix = arbitrary @(Fix f)

  genEval :: HasTerminals f => Gen a
  genEval = eval <$> genFix @f


instance FixArbitrary f a => Arbitrary (Fix f) where
  arbitrary = Fix <$> liftFix arbitrary

instance FixArbitrary f a => FixArbitrary (Freq f n) a where
  liftFix gen = FreqTag <$> liftFix gen

instance FixArbitrary f a => FixArbitrary (Term f) a where
  liftFix gen = TermTag <$> liftFix gen

instance ( FixArbitrary f a, f #> ff, f @> ff0
         , FixArbitrary g a, g #> gg, g @> gg0
         ) => FixArbitrary (Sum f g) a where
    liftFix gen = sized $ \n ->
      if n == 0
      then case (numVal @ff0, numVal @gg0) of
        (0, 0) -> error "liftFix: the impossible happened"
        (_, 0) -> InL <$> liftFix gen
        (0, _) -> InR <$> liftFix gen
        (ff0, gg0) -> frequency
           [ (ff0, InL <$> liftFix gen)
           , (gg0, InR <$> liftFix gen) ]
      else frequency
           [ (numVal @ff, InL <$> liftFix gen)
           , (numVal @gg, InR <$> liftFix gen) ]


----------------------------------------
-- | Type families to hide TH unique names

-- | Whole types, functions or modules
type family HRep (t :: Symbol) :: Type -> Type

-- | A single constructor
type family Con (c :: k) :: Type -> Type

-- | A single pattern matchings
type family Pat (p :: Symbol) (n :: Nat) :: Type -> Type

-- | A single function in a module
type family Fun (t :: Symbol) :: Type -> Type


----------------------------------------
-- | Existential types to hide type parameters

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

type family Apply (a :: Type) (t :: Type -> Type) where
  Apply a (Freq t n) = Freq (Apply a t) n
  Apply a (Term t) = Term (Apply a t)
  Apply a (Sum l r) = Sum (Apply a l) (Apply a r)
  Apply a (Some1 t) = t a
  Apply a (Some2 t) = Some1 (t a)
  Apply a (Some3 t) = Some2 (t a)
  Apply a (Some4 t) = Some3 (t a)
  Apply a (Some5 t) = Some4 (t a)
  Apply a t = t
