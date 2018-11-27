{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}

module Exp where

import Test.QuickCheck.HRep
import Test.QuickCheck.HRep.TH

----------------------------------------

data Exp v a
  = Val a
  | Var v
  | Add (Exp v a) (Exp v a)
  | Mul (Exp v a) (Exp v a)
  deriving Show

foo :: Exp v a -> a
foo (Add (Add _ _) _) = undefined
foo (Add (Val _) _)   = undefined
foo _                 = undefined

type ExpString = Exp String

bar :: ExpString a -> a
bar (Add (Var "very rare var") (Val _)) = undefined
bar (Add _ _)                           = undefined
bar _                                   = undefined

twice :: ExpString a -> ExpString a
twice e = Add e e

pow :: Exp v Int -> Int -> Exp v Int
pow e n = foldr Mul (Val 1) (replicate n e)

zero :: Exp v Int
zero = Val 0

fortyTwo :: Exp v Int
fortyTwo = Add (Mul (Val 5) (Val 4)) (Val 22)

----------------------------------------

derive typeRep    { type_ = ''Exp }
derive funPatsRep { fun   = 'foo  }
derive funPatsRep { fun   = 'bar  }
derive modIntRep  { type_ = ''Exp , alias = "my module" }
