{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

module Exp_test where

import Test.QuickCheck (Gen)
import Test.QuickCheck.HRep
import Test.QuickCheck.HRep.Infix

import Exp


-- | A fine grained specification
type Exp'
  -- Constructors
   = Con 'Val
  :< Con 'Add        :* 2
  :| Con 'Mul        :* 2
  -- Function patters
  :| Pat ("foo" :#1)
  :| Pat ("bar" :#2)
  -- Combinators
  :| Fun "pow"
  :| Fun "twice"     :* 3
  :| Fun "zero"

-- | A coarse grained specification
type Exp''
  = HRep Exp
 :| HRep "foo"
 :| HRep "bar"
 :| HRep "my module"


genExp :: Gen (Exp String Int)
genExp = genEval @(Exp'' :@String :@Int)

-- instance Arbitrary (Exp String Int) where
--   arbitrary = genEval @(Exp'' :@ String :@ Int)
