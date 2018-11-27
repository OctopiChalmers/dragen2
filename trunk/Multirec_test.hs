{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}

module Multirec_test where

import Data.Kind
import GHC.Generics
import Generics.MultiRec.TH

data Exp
  = Val Int
  | Add Exp Exp
  deriving (Generic, Show)

foo :: Exp -> a
foo (Add (Add _ _) _) = undefined
foo (Add (Val 0) _)   = undefined
foo _ = undefined

bar :: Exp -> a
bar (Add (Val _) (Val 0)) = undefined
bar (Add _ _)   = undefined
bar _ = undefined

data Pat_foo
  = Pat_foo_1 Exp Exp Exp
  | Pat_foo_2 Exp
  deriving Show

data AST :: Type -> Type where
  Exp :: AST Exp
  Pat_foo :: AST Pat_foo

deriveAll ''AST
