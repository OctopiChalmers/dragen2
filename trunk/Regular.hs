{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeOperators #-}

module Test.QuickCheck.Patterns.Regular where

import GHC.TypeLits
import Data.Kind

-- | Let's try first with a regular data type

data Expr
  = EConst Int
  | EAdd Expr Expr
  | EMul Expr Expr
  | EVar String
  deriving Show

foo :: Expr -> Expr
foo (EAdd (EConst 0) (EConst _)) = undefined
foo (EMul (EConst 1) _)          = undefined
foo (EMul (EConst 0) _)          = undefined
foo _                            = undefined

bar :: Expr -> Expr
bar (EMul (EAdd _ _) _)          = undefined
bar (EAdd _ (EAdd _ (EConst _))) = undefined
bar _                            = undefined

----------------------------------------
-- The standard machinery

-- | Fix point of a data type. Just for illustration.
data Fix (f :: Type -> Type) = Fix (f (Fix f))

-- | Fix point of a pair of data types.
-- If we have two pattern functors representing the same data type in different
-- ways, we can interleave them by selecting either FixL or FixR accordingly.
data Bifix (f :: Type -> Type) (g :: Type -> Type)
  = FixL (f (Bifix f g))
  | FixR (g (Bifix f g))

-- | We say that an interleaved pattern functor `f` can be translated to our
-- original type `a`, provided that we know how to translate any other
-- internally interleaved pattern functor.
class f ===> a where
  translate :: (g ===> a, g' ===> a) => f (Bifix g g') -> a

-- | If we know how to translate both pattern functors from an interleaved
-- value, we can translate it to our original data type `a` by "forgetting" the
-- interleaved structure.
forget :: (f ===> a, g ===> a) => Bifix f g -> a
forget (FixL f) = translate f
forget (FixR g) = translate g


-- | Extensible sum types using "data types a la carte" approach.
-- | Empty type
data Empty a

instance Empty ===> Expr where
  translate = error "impossible happened"

-- | Generic sum type
data (f :+: g) t = InL (f t) | InR (g t)

instance (f ===> a, g ===> a) => (f :+: g) ===> a where
  translate (InL f) = translate f
  translate (InR g) = translate g


-- | Some type families to reduce the noise
-- | Associate each type to its correspondent pattern functor.
type family PF   (t  :: Type)     :: Type -> Type

-- | Associate each pattern type to its corresponding function.
type family Pat  (f  :: Symbol)   :: Type -> Type
type family Pats (fs :: [Symbol]) :: Type -> Type

type instance Pats '[]       = Empty
type instance Pats (f ': fs) = Pat f :+: Pats fs


-- | A type that represents values of type `t` that are built using either its
-- pattern functor (PF t) for completely random subexpressions, or a pattern
-- satisfying subexpression from a list of functions-patterns-encoding functors.
type Interleave (t :: Type) (fs :: [Symbol]) = Bifix (PF t) (Pats fs)

----------------------------------------
-- Code that should be generated automatically

data ExprF r
  = EConstF Int
  | EAddF r r
  | EMulF r r
  | EVarF String
  deriving Functor

type Expr' = Fix ExprF

type instance PF Expr = ExprF

data Pat_foo t
  = Pat_foo_1 Int
  | Pat_foo_2 t
  | Pat_foo_3 t
  deriving Functor

type instance Pat "foo" = Pat_foo

data Pat_bar t
  = Pat_bar_1 t t t
  | Pat_bar_2 t t Int
  deriving Functor

type instance Pat "bar" = Pat_bar

instance ExprF ===> Expr where
  translate (EConstF n)   = EConst n
  translate (EAddF e1 e2) = EAdd (forget e1) (forget e2)
  translate (EMulF e1 e2) = EMul (forget e1) (forget e2)
  translate (EVarF v)     = EVar v

instance Pat_foo ===> Expr where
  translate (Pat_foo_1 n) = (EAdd (EConst 0) (EConst n))
  translate (Pat_foo_2 e) = (EMul (EConst 1) (forget e))
  translate (Pat_foo_3 e) = (EMul (EConst 0) (forget e))

instance Pat_bar ===> Expr where
  translate (Pat_bar_1 e1 e2 e3) = EMul (EAdd (forget e1) (forget e2)) (forget e3)
  translate (Pat_bar_2 e1 e2 n)  = EAdd (forget e1) (EAdd (forget e2) (EConst n))

----------------------------------------
-- Code to tell our tool how to behave

type Expr_foo_bar = Interleave Expr '["foo", "bar"]

x :: Expr_foo_bar
x = FixL $ EAddF                  -- Arbitrarly Add expression
    (FixR $ InL $ Pat_foo_2       --  |-> Expression sat. foo 2nd pattern
      (FixL $ EConstF 42))        --  |    \-> Arbitrarly expression 42
    (FixR $ InR $ InL $ Pat_bar_2 --  \-> Expression sat. bar 2nd pattern
      (FixL $ EConstF 20)         --       |-> Arbitrarly expression 20
      (FixL $ EConstF 100)        --       |-> Arbitrarly expression 100
      24)                         --       \-> Arbitrarly value 24


x' :: Expr
x' = forget x

----------------------------------------
