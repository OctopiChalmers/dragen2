module Test.Dragen2.Infix where

import Test.Dragen2.Rep
import Test.Dragen2.TypeLevel

-- | Infix representation of operators

type (:*) = Freq
infixl 6 :*

type (:+) = Sum
infixr 5 :+

type (m :! k) = Lookup m k
infix 4 :!

type (t <| a) = Apply a t
infixl 3 <|

type ((k :: kk) := (v :: vv)) = '(k, v)
infix 2 :=

(.=>) :: a -> b -> (b, a)
(.=>) = flip (,)
infix 2 .=>
