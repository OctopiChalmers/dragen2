module RE.RE where

import Control.Monad(liftM, liftM2)

import GHC.Generics hiding (Rep, R, L)
import Control.DeepSeq
import Test.Dragen2 hiding ((.+.))
import Test.QuickCheck hiding ((.&.), Fun)


infix  5 ~~
infixl 7 .+.
infixl 8 .>.

--------------------------------------------------------------------------------
-- regular expressions with intersection

data R a
  = Nil
  | Eps
  | Atom a
  | R a :+: R a
  | R a :&: R a
  | R a :>: R a
  | Star (R a)
 deriving (Eq, Ord, Show, Generic)

instance NFData a => NFData (R a)

(.&.) :: R a -> R a -> R a
Nil .&.  _   = Nil
_   .&.  Nil = Nil
p   .&.  q   = p :&: q

(.+.) :: R a -> R a -> R a
Nil .+. q   = q
p   .+. Nil = p
p   .+. q   = p :+: q

(.>.) :: R a -> R a -> R a
Nil .>. _   = Nil
_   .>. Nil = Nil
Eps .>. q   = q
p   .>. Eps = p
p   .>. q   = p :>: q

--------------------------------------------------------------------------------
-- can the RE parse the empty string?

eps :: R a -> Bool
eps Eps       = True
eps (p :+: q) = eps p || eps q
eps (p :&: q) = eps p && eps q
eps (p :>: q) = eps p && eps q
eps (Star _)  = True
eps _         = False

epsR :: R a  -> R a
epsR p | eps p     = Eps
       | otherwise = Nil

--------------------------------------------------------------------------------
-- small step operational semantics, Brzozowsky-style

step :: Eq a => R a -> a -> R a
step (Atom a)  x
  | a == x    = Eps
  | otherwise = Nil
step (p :+: q) x = step p x .+. step q x
step (p :&: q) x = step p x .&. step q x
step (p :>: q) x = (step p x .>. q) .+. if eps p then step q x else Nil
step (Star p)  x = step p x .>. Star p
step _         _ = Nil

rec :: Eq a => R a -> [a] -> Bool
rec p []     = eps p
rec p (x:xs) = rec (step p x) xs

-- --------------------------------------------------------------------------------
-- -- properties, all falsifiable

prop_SeqComm :: R L -> R L -> [L] -> Bool
prop_SeqComm p q = p .>. q ~~ q .>. p

prop_StarPlus :: R L -> R L -> [L] -> Bool
prop_StarPlus p q = Star (p .+. q) ~~ Star p .+. Star q

prop_StarSeq :: R L -> R L -> [L] -> Bool
prop_StarSeq p q = Star (p .>. q) ~~ Star p .>. Star q

prop_SomeAnd :: R L -> R L -> [L] -> Bool
prop_SomeAnd p q = some p .&. some q ~~ some (p .&. q)
  where some p' = p' .>. (p' .+. Eps)

-- ~~

-- {-
-- (~~) :: R L -> R L -> [L] -> Property
-- p ~~ q = \s -> rec p s === rec q s
-- -}

(~~) :: R L -> R L -> [L] -> Bool
(~~) _ _ [] = True
(~~) p q (x:xs)
  | eps p /= eps q               = False
  | size p > 100 || size q > 100 = True
  | otherwise                    = (step p x ~~ step q x) xs

-- the size is there to avoid explosion when evaluating
size :: R a -> Int
size (p :+: q) = 1 + size p + size q
size (p :>: q) = 1 + size p + size q
size (p :&: q) = 1 + size p + size q
size (Star p)  = 1 + size p
size _         = 1

--------------------------------------------------------------------------------
-- Koen generator

data L = A | B | C deriving ( Eq, Ord, Show, Read, Enum )

instance Arbitrary L where
  arbitrary = elements [A ..]

koenGen :: Arbitrary a => Gen (R a)
koenGen = sized go
    where
      go s = frequency
        [(1,return Nil)
        ,(1,return Eps)
        ,(3,Atom `fmap` arbitrary)
        ,(s,liftM2 (:+:) (go s2) (go s2))
        ,(s,liftM2 (:&:) (go s2) (go s2))
        ,(s,liftM2 (:>:) (go s2) (go s2))
        ,(s,liftM  Star  (go s1))
        ]
        where
         s2 = s`div`2
         s1 = pred s

----------------------------------------
-- Manual generator

genR :: Arbitrary a => BoundedGen (R a)
genR depth = go depth
  where
    go 0 = frequency
      [ (1, pure Eps)
      , (1, pure Nil)
      , (1, Atom <$> arbitrary)
      ]
    go n = frequency
      -- Con' "Eps"
      [ (1, pure Eps)
      -- Con' "Nil"
      , (1, pure Nil)
      -- Con' "Atom"
      , (1, Atom <$> arbitrary)
      -- Con  ":+:"
      , (1, (:+:) <$> go (n-1) <*> go (n-1))
      -- Con  ":&:"
      , (1, (:&:) <$> go (n-1) <*> go (n-1))
      -- Con  ":>:"
      , (1, (:>:) <$> go (n-1) <*> go (n-1))
      -- Con  "Star"
      , (1, Star <$> go (n-1))
      -- Fun  ".+."
      , (1, (.+.) <$> go (n-1) <*> go (n-1))
      -- Fun  ".&."
      , (1, (.&.) <$> go (n-1) <*> go (n-1))
      -- Fun  ".>."
      , (1, (.>.) <$> go (n-1) <*> go (n-1))
      -- Fun  "epsR"
      , (1, epsR <$> go (n-1))
      ]

----------------------------------------
-- Dragen2

derive [''R]
  [ constructors ''R
  , interface    ''R
  ]

type R_Spec
  =  Con "Nil"
  :+ Con "Eps"
  :+ Con "Atom"
  :+ Con ":+:"
  :+ Con ":&:"
  :+ Con ":>:"
  :+ Con "Star"
  :+ Fun ".&."
  :+ Fun ".+."
  :+ Fun ".>."
  :+ Fun "epsR"

genR' :: forall a. (Ord a, Arbitrary a) => BoundedGen (R a)
genR' = genRep @(R_Spec <| a)
