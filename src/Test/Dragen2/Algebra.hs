module Test.Dragen2.Algebra where

import Data.Kind
import GHC.Generics

----------------------------------------
-- | Fixed point of a data type

newtype Fix  (f :: Type -> Type) = Fix {unFix :: (f (Fix f)) }

deriving instance (Show    (f (Fix f))) => Show    (Fix f)
deriving instance (Generic (f (Fix f))) => Generic (Fix f)

----------------------------------------
-- | F-algebras over functors

class Functor f => Algebra f a | f -> a where
  alg :: f a -> a

cata :: Functor f => (f a -> a) -> Fix f -> a
cata f = f . fmap (cata f) . unFix

eval :: Algebra f a => Fix f -> a
eval = cata alg
