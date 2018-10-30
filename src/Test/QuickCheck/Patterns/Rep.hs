{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module Test.QuickCheck.Patterns.Rep where

import GHC.TypeLits
import Data.Kind
import Data.Proxy

--import Test.QuickCheck
import Test.QuickCheck.FreqArbitrary

----------------------------------------

-- | Fix point of a functor.
data Fix (f :: Type -> Type)
  = Fix { unFix :: (f (Fix f)) }

deriving instance (Show (f (Fix f)) => Show (Fix f))

-- | Arbitrary plumbing for fixpoints
instance FreqArbitrary1 f => FreqArbitrary (Fix f) where
  freqArbitrary freq = Fix <$> liftFreqArbitrary freq (freqArbitrary freq)

-- instance Arbitrary1 f => Arbitrary (f (Fix f)) where
--   arbitrary = liftArbitrary arbitrary
--   shrink = liftShrink shrink

-- | Catamorphisms, a.k.a generic foldings over fix points.
cata :: Functor f => (f a -> a) -> Fix f -> a
cata f = f . fmap (cata f) . unFix

----------------------------------------
-- | Extensible sum types using "data types a la carte" approach.

-- | Generic sum type
data (f :+: g) a
  = InL (f a)
  | InR (g a)
  deriving (Functor)

infixr 8 :+:

deriving instance (Show (f a), Show (g a)) => Show ((f :+: g) a)

-- instance (Arbitrary1 f, Arbitrary1 g) => Arbitrary1 (f :+: g) where
--   liftArbitrary arb = oneof
--     [ InL <$> liftArbitrary arb
--     , InR <$> liftArbitrary arb ]
--   liftShrink shrinker (InL f) = InL <$> liftShrink shrinker f
--   liftShrink shrinker (InR g) = InR <$> liftShrink shrinker g

instance (FreqArbitrary1 f, FreqArbitrary1 g) => FreqArbitrary1 (f :+: g) where
  liftFreqArbitrary f gen
    = withFrequency f
    [ ('InL, InL <$> gen @! f)
    , ('InR, InR <$> gen @! f)
    ]

-- | Generic random choice sum type
-- This is isomorphic to (:+:), but it's useful to distinguish them when
-- generating random values
data (f :?: g) a
  = Rnd (f a)
  | Pat (g a)
  deriving (Functor)

infixr 7 :?:

deriving instance (Show (f a), Show (g a)) => Show ((f :?: g) a)

-- instance (Arbitrary1 f, Arbitrary1 g) => Arbitrary1 (f :?: g) where
--   liftArbitrary arb = oneof
--     [ Rnd <$> liftArbitrary arb
--     , Pat <$> liftArbitrary arb ]
--   liftShrink shrinker (Rnd f) = Rnd <$> liftShrink shrinker f
--   liftShrink shrinker (Pat g) = Pat <$> liftShrink shrinker g

instance (FreqArbitrary1 f, FreqArbitrary1 g) => FreqArbitrary1 (f :?: g) where
  liftFreqArbitrary f gen
    = withFrequency f
    [ ('Rnd, Rnd <$> gen @! f)
    , ('Pat, Pat <$> gen @! f)
    ]

----------------------------------------
-- | Some type families to reduce the noise

-- | Associate each type to its (isomorphic) pattern functor.
type family PF (t  :: Type) :: Type -> Type

-- | Associate each function to its pattern-matching functor.
type family Pattern  (f  :: Symbol)   :: Type -> Type

-- | Build a sum type composed of a list of function names.
type family Patterns (fs :: [Symbol]) :: Type -> Type where
  Patterns '[f]       = Pattern f
  Patterns (f ': fs)  = Pattern f :+: Patterns fs

----------------------------------------
-- | F-algebras over functors

class Algebra f a where
  alg :: f a -> a

-- class Coalgebra f a where
--   coalg :: a -> f a

instance (Algebra f a, Algebra g a) => Algebra (f :+: g) a where
  alg (InL f) = alg f
  alg (InR g) = alg g

instance (Algebra f a, Algebra g a) => Algebra (f :?: g) a where
  alg (Rnd f) = alg f
  alg (Pat g) = alg g

----------------------------------------
-- | Functor representations

-- | This is a type class constraint synonym!
type Rep f a = (Functor f, Algebra f a)

-- eval :: (Rep f a, Rep g a) => f (Fix g) -> a
-- eval = alg . fmap foldRep

eval :: Rep f a => Fix f -> a
eval = cata alg

-- type f |:?:| g = Fix (f :?: g)

type Interleave (t :: Type) (fs :: [Symbol]) = Fix (PF t :?: Patterns fs)




----------------------------------------
-- | Some type level trickery again

rnd :: rnd (Fix (rnd :?: pats)) -> Fix (rnd :?: pats)
rnd = Fix . Rnd

pat1 :: f1 (Fix (rnd :?: f1 :+: rest)) -> Fix (rnd :?: f1 :+: rest)
pat1 = Fix . Pat . InL

pat2 :: f2 (Fix (rnd :?: f1 :+: f2 :+: rest))
     -> Fix (rnd :?: f1 :+: f2 :+: rest)
pat2 = Fix . Pat . InR . InL

pat3 :: f3 (Fix (rnd :?: f1 :+: f2 :+: f3 :+: rest))
     -> Fix (rnd :?: (f1 :+: f2 :+: f3 :+: rest))
pat3 = Fix . Pat . InR . InR . InL

type family Index (x :: Symbol) (xs :: [Symbol]) :: Nat where
  Index x (x ': xs) = 0
  Index x (y ': xs) = 1 + (Index x xs)
  Index x '[] = TypeError ('Text "Function "
                           ':<>: 'ShowType x
                           ':<>: 'Text " is not in the list")

printNat :: KnownNat n => proxy n -> IO ()
printNat = print . natVal

-- printNat (Proxy @(Index "bar" '["foo", "bar", "baz"]))
-- 1

funIndex :: Index f pats ~ n => Integer
funIndex = natVal (Proxy @4)
