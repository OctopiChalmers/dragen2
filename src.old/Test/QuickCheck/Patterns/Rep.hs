{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}

module Test.QuickCheck.Patterns.Rep where

import GHC.TypeLits
import Data.Kind

----------------------------------------

-- | Fix point of a data type. Just for illustration.
data Fix (f :: Type -> Type) = Fix (f (Fix f))

-- | Fix point of a pair of data types.
-- If we have two pattern functors representing the same data type in different
-- ways, we can interleave them by selecting either FixL or FixR accordingly.
data Bifix (f :: Type -> Type) (g :: Type -> Type)
  = FixL (f (Bifix f g))
  | FixR (g (Bifix f g))

----------------------------------------

-- | We say that an interleaved pattern functor `f` can be translated to our
-- original type `a`, provided that we know how to translate any other
-- internally interleaved pattern functor.
class f ===> a where
  translate :: (g ===> a, g' ===> a) => f (Bifix g g') -> a

----------------------------------------

-- | A type that represents values of type `t` that are built using either its
-- pattern functor (PF t) for completely random subexpressions, or a pattern
-- satisfying subexpression from a list of functions-patterns-encoding functors.
type Interleave (t :: Type) (fs :: [Symbol]) = Bifix (PF t) (Pats fs)

-- | If we know how to translate both pattern functors from an interleaved
-- value, we can translate it to our original data type `a` by "uninterleaving" the
-- interleaved structure.
uninterleave :: (f ===> a, g ===> a) => Bifix f g -> a
uninterleave (FixL f) = translate f
uninterleave (FixR g) = translate g

----------------------------------------

-- | Extensible sum types using "data types a la carte" approach.

-- | Empty type
data Empty a

-- | Generic sum type
data (f :+: g) t = InL (f t) | InR (g t)

instance (f ===> a, g ===> a) => (f :+: g) ===> a where
  translate (InL f) = translate f
  translate (InR g) = translate g

----------------------------------------

-- | Some type families to reduce the noise
-- | Associate each type to its correspondent pattern functor.
type family PF   (t  :: Type)     :: Type -> Type

-- | Associate each pattern type to its corresponding function.
type family Pat  (f  :: Symbol)   :: Type -> Type
type family Pats (fs :: [Symbol]) :: Type -> Type

type instance Pats '[]       = Empty
type instance Pats (f ': fs) = Pat f :+: Pats fs
