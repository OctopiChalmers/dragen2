{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Pred_test where

import Prelude hiding (zipWith)

import Test.QuickCheck (Arbitrary, arbitrary)
import Test.QuickCheck.HRep
import Test.QuickCheck.HRep.Infix
import Test.QuickCheck.HRep.TH

import GHC.Generics
import GHC.Generics.Countable

----------------------------------------
-- Module contents

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
twice exp = Add exp exp

pow :: Exp v Int -> Int -> Exp v Int
pow exp n = foldr Mul (Val 1) (replicate n exp)

zero :: Exp v Int
zero = Val 0

fortyTwo :: Exp v Int
fortyTwo = Add (Mul (Val 5) (Val 4)) (Val 22)

derive typeRep    { type_ = ''Exp }
derive funPatsRep { fun   = 'foo  }
derive funPatsRep { fun   = 'bar  }
derive modIntRep  { type_ = ''Exp , alias = "my module" }

----------------------------------------

type Exp'
  -- Constructors
   = Con  Val
  :< Con  Add        :* 2
  :| Con  Mul        :* 2
  -- Function patters
  :| Pat ("foo" :#1)
  :| Pat ("bar" :#2)
  -- Combinators
  :| Fun "pow"
  :| Fun "twice"     :* 3
  :| Fun "zero"

type Exp''
  = HRep Exp
 :| HRep "foo"
 :| HRep "bar"
 :| HRep "my module"

instance Arbitrary (Exp String Int) where
  arbitrary = genEval @(Exp'' :@ String :@ Int)

-- -- | Maybe this is a good automation!
-- -- deriveArbitrary
--   -- [| Exp String a |]
--   -- [t| Con Val
--    -- +| Con Var          :* 2
--    -- <| Con Add
--    -- +| Pat "foo"        :* 3
--    -- +| Pat ("bar" :# 2) :* 3
--    -- |]
-- -- =====>
-- instance Arbitrary a => Arbitrary (Exp String a) where
--   arbitrary = genEval @( Con Val
--                       :| Con Var          :* 2
--                       :< Con Add
--                       :| Pat "foo"        :* 3
--                       :| Pat ("bar" :# 1) :* 3
--                       :@ String
--                       :@ a)


deriving instance Generic Int
deriving instance Generic Char
