module TestExp where

import GHC.Generics

import Test.QuickCheck
import Dragen.Struct

----------------------------------------

deriving instance Generic Int

-- Given the following mutually recursive data types

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

-- And the following functions defined using pattern matching on them

foo :: IExp -> a
foo (Add (Add (Val _)   _) _) = undefined
foo (Add (If _ (Val _) _) _)  = undefined
foo _                         = undefined

bar :: BExp -> a
bar (LEq (Val _) _)          = undefined
bar (And (Bool _) (LEq _ _)) = undefined
bar _                        = undefined


-- We can write a "generation specification"
type ExpS =
  '[ "IExp" := HRep "IExp"
            :+ HRep "foo"
   , "BExp" := HRep "BExp"
            :+ HRep "bar"
   ]

-- Which is equivalent to the following "fine grained" specification
type ExpS_fine =
  '[ "IExp" := Term (Con 'Val)  :* 1
            :+ Con 'Add         :* 1
            :+ Con 'If          :* 1
            :+ Pat "foo" 1      :* 1
            :+ Pat "foo" 2      :* 1
   , "BExp" := Term (Con 'Bool) :* 1
            :+ Con 'LEq         :* 1
            :+ Pat "bar" 1      :* 1
            :+ Pat "bar" 2      :* 1
   ]

-- And derive all the require machinery for it
-- NOTE: load this file in ghci with the flag -ddump-splices to see the generated code!
deriveHRep
  [''IExp, ''BExp]  -- Family of types
  [ patterns_ 'foo  -- Targets
  , patterns_ 'bar
  ]


{-
With the representation and the prediction mechanism in place, we can optimize
the frequencies in the same way as we did before.

NOTE: not really, Haskell stage restriction forbids to use the type "ExpS" as a
parameter of a TH function because it was generated in a splice within the same
module. There are some ways to "jailbreak" this restriction but I need to find
how to make them work here :(

So, I have optimized the following frequencies using ghci and pasted them here for now.
-}

-- freqs :: [[Integer]]
-- freqs = optimizeFreqs
--         @ExpS @"IExp"
--         Rep
--         10
--         (weighted [("Add", 2), ("foo#1", 3)])
--         [ [1, 1, 1, 1, 1]
--         , [1, 1, 1, 1, 1] ]
-- ===>
-- [[11,9,1,14,1],[10,12,8,1,1]]

type ExpS_Opt = SetSpecFreqs (MkSpec ExpS) '[ '[11,9,1,14,1], '[10,12,8,1,1]]

{-  which is equivalent to:
ghci> :kind!' ExpS_Opt
===>
[ '("IExp",
       Sum
         (Freq (Term HRep_Con_Val) 11)
         (Sum
            (Freq HRep_Con_Add 9)
            (Sum
               (Freq HRep_Con_If 1)
               (Sum (Freq HRep_Pat_foo_1 14) (Freq HRep_Pat_foo_2 1))))),
     '("BExp",
       Sum
         (Freq (Term HRep_Con_Bool) 10)
         (Sum
            (Freq HRep_Con_And 12)
            (Sum
               (Freq HRep_Con_LEq 8)
               (Sum (Freq HRep_Pat_bar_1 1) (Freq HRep_Pat_bar_2 1)))))]
-}


instance Arbitrary IExp where arbitrary = genEval @(ExpS_Opt ~> "IExp")
instance Arbitrary BExp where arbitrary = genEval @(ExpS_Opt ~> "BExp")

{-
We can predict the distribution and confirm it generating actual data:

It's difficult to see if the distribution follows the "desired" one because the
all the representation cosntructors are gone.

ghci> predict @ExpS_Opt  @"IExp" 10
fromList [("Add",82.696734010464),("And",2.4670719614784673),("Bool",4.921783983563986),("If",4.3524596847612615),("LEq",1.897747662675744),("Val",91.84468902057674)]

confirm @ExpS_Opt  @"IExp" 10
fromList [("Add",82.66198),("And",2.48682),("Bool",4.93628),("False",2.46942),("I#",91.8424),("If",4.35978),("LEq",1.91032),("True",2.46686),("Val",91.8424)]

On the other hand, if we predict and confirm over the distribution, we obtain
some nicer numbers (remember that we optimized the frequencies to follow:
(2*size*Add) and (3*size*foo#1)):

ghci> predictRep @ExpS_Opt @"IExp" 10

fromList [("Add",19.58606858142568),("And",2.277297195210893),("Bool",4.732009217296412),("If",2.1762298423806308),("LEq",1.5181981301405951),("Val",59.01146661859969),("bar#1",0.1897747662675744),("bar#2",0.1897747662675744),("foo#1",30.46721779332884),("foo#2",2.1762298423806308)]

However, confirming this distribution over the representation results in a lot of noise:

ghci> confirmRep @ExpS_Opt  @"IExp" 10
fromList [("Add",12.84046),("And",2.43924),("Bool",4.87554),("Con_Add",16.4112),("Con_If",1.82454),("Con_Val",46.6112),("False",2.4404),("Fix",92.2224),("FreqTag",92.2224),("I#",91.28438),("If",0.67398),("InL",90.39298),("InR",104.01608),("LEq",1.89164),("Pat_foo_1",25.54604),("Pat_foo_2",1.82942),("TermTag",46.6112),("True",2.43514),("Val",17.29772)]

-}
