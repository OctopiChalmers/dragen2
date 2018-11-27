{-# LANGUAGE TypeOperators #-}

module Test.QuickCheck.HRep.Infix where

import Test.QuickCheck.HRep

-- | Infix representation of operators
type (f :# n) = Hash f n
infix 7 :#

type (:*) = Freq
infixl 6 :*

type (:|) = Sum
infixl 5 :|

type (:<) = SizedSum
infix 4 :<

type (t :@ a) = Apply a t
infixl 3 :@
