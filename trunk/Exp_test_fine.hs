{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}

module Exp_test_fine where

import Test.QuickCheck.Patterns.Rep
import Test.QuickCheck.Patterns.TH

data Exp
  = Val Int
  | Add Exp Exp
  deriving (Show)

foo :: Exp -> a
foo (Add (Add _ _) _) = undefined
foo (Add (Val 0) _)   = undefined
foo _ = undefined

bar :: Exp -> a
bar (Add (Val _) (Val 0)) = undefined
bar (Add _ _)   = undefined
bar _ = undefined

data ValF r = ValF Int deriving (Show, Functor)
data AddF r = AddF r r deriving (Show, Functor)

data Pat_foo_1 r = Pat_foo_1 r r r deriving (Show, Functor)
data Pat_foo_2 r = Pat_foo_2 Int r deriving (Show, Functor)

data Val
data Add

-- type instance (Exp a).Val = ValF
type instance Con Exp Add = AddF

type instance Rep "foo#1" = Pat_foo_1
type instance Rep "foo#2" = Pat_foo_2

-- type instance Rep Exp   = ValF + AddF
-- type instance Rep "foo" = Pat_foo_1 + Pat_foo_2

type instance Rep Exp = Val .~ Exp
                     <+ Add .~ Exp

type instance Rep "foo" = Rep "foo#1" .* 2
                       .+ Rep "foo#2" .* 3

-- data AddEq e = AddEq e deriving Functor

-- instance Algebra AddEq Exp where
--   alg (AddEq e) = Add e e

-- type Exp_pat = ExpR + Pats + AddEq

-- twice :: IExp -> IExp
-- twice e = Add e e

-- thrice :: IExp -> IExp
-- thrice e = Add e (twice e)

-- weird :: IExp -> IExp -> IExp -> IExp
-- weird x y z = If (And (LEq x y) (LEq y z)) (Add x y) (Add y z)

-- equals :: IExp -> IExp -> BExp
-- equals x y = And (LEq x y) (LEq y x)

-- and3 :: BExp -> BExp -> BExp -> BExp
-- and3 x y z = And x (And y z)
