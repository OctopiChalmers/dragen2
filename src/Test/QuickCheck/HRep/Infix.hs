{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}

module Test.QuickCheck.HRep.Infix where

import Test.QuickCheck.HRep
import Test.QuickCheck.Branching

-- | Infix representation of operators
-- type (f # n) = Pat f n
-- infix 7 #

type (:*) = Freq
infixl 6 :*

type (:|) = Sum
infixl 5 :|

type (spec # k) = Lookup spec k
infix 4 #

type (t :@ a) = Apply a t
infixl 3 :@

type (spec :@@ a) = ApplySpec a spec
infixl 3 :@@

type (k := v) = '(k, v)
infix 2 :=
