module Test.Dragen.Struct.Infix where

import Test.Dragen.Struct.Rep
import Test.Dragen.Struct.TypeLevel

-- | Infix representation of operators

type (:*) = Freq
infixl 6 :*

type (:+) = Sum
infixl 5 :+

type (m :> k) = Lookup m k
infix 4 :>

type (t :$ a) = Apply a t
infixl 3 :$

type ((k :: kk) := (v :: vv)) = '(k, v)
infix 2 :=
