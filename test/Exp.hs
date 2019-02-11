{-# OPTIONS_GHC -fdefer-type-errors #-}
module Exp where

import GHC.Generics
import Test.QuickCheck hiding (Fun)
import Dragen.Struct


deriving instance Generic Int

----------------------------------------

-- | Given the following mutually recursive data types

data IExp
  = Val Int
  | Add IExp IExp
  | If  BExp IExp IExp
  deriving (Show, Generic)

data BExp
  = Bool Bool
  | And  BExp BExp
  | LEq  IExp IExp
  deriving (Show, Generic)

ieval :: IExp -> Int
ieval (Val n) = n
ieval (Add x y) = ieval x + ieval y
ieval (If b x y) = if beval b then ieval x else ieval y

beval :: BExp -> Bool
beval (Bool b) = b
beval (And x y) = beval x && beval y
beval (LEq x y) = ieval x <= ieval y

-- | The following functions defined using pattern matching on them

foo :: IExp -> a
foo (Add (Add (Val _)   _) _) = undefined
foo (Add (If _ (Val 10) _) _) = undefined
foo _                         = undefined

bar :: BExp -> a
bar (LEq (Val _) _)              = undefined
bar (And (Bool False) (LEq _ _)) = undefined
bar _                            = undefined


-- | And the following abstract abstract interface for creating expressions:

zero :: IExp
zero = Val 0

twice :: IExp -> IExp
twice x = Add x x

eq :: IExp -> IExp -> BExp
eq x y = And (LEq x y) (LEq y x)

----------------------------------------

-- | First, we write a "generation specification"
type ExpS =
  '[ "IExp"
       := HRep "IExp"
       :+ HRep "foo"
       :+ HRep "[IExp]"
   , "BExp"
       := HRep "BExp"
       :+ HRep "bar"
       :+ HRep "[BExp]"
   ]

type ExpS_fine =
  '[ "IExp"
       := Term (Con 'Val)  :* 1
       :+ Con 'Add         :* 2
       :+ Con 'If          :* 3
       :+ Pat "foo" 1      :* 4
       :+ Pat "foo" 2      :* 5
       :+ Fun "zero"       :* 6
       :+ Fun "twice"      :* 7
   , "BExp"
       := Term (Con 'Bool) :* 1
       :+ Con 'LEq         :* 2
       :+ Pat "bar" 1      :* 3
       :+ Pat "bar" 2      :* 4
       :+ Fun "eq"         :* 5
   ]

deriveAll
  -- | Mutually recursive family of types
  [ ''IExp, ''BExp ]
  -- | Targets
  [ patterns   'foo
  , patterns   'bar
  , interface ''IExp
  , interface ''BExp
  ] ''ExpS


pred :: Hist
pred = predictRep @ExpS @"IExp" 15

hist :: IO Hist
hist = confirmRep @ExpS @"IExp" 15

freqs :: [[Integer]]
freqs = optimize @ExpS @"IExp" 15 uniform

pred' :: Hist
pred' = predictRepWith @ExpS @"IExp" freqs 15


genExp :: IO IExp
genExp = do
  x <- generate $ resize 15 $ genFix @(ExpS ~> "IExp")
  putStrLn $ "Fix point value:\n" ++ show x ++ "\n--------------"
  return (eval x)
