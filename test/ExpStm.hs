{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module ExpStm where

import GHC.Generics
import GHC.Generics.Countable

import Test.QuickCheck
import Test.QuickCheck.Branching hiding (alias)
import Test.QuickCheck.HRep
import Test.QuickCheck.HRep.Infix
import Test.QuickCheck.HRep.TH

import Data.Map.Strict (Map)
import Data.Matrix (Matrix, (!), (<->))
import qualified Data.Map.Strict as Map
import qualified Data.Matrix as Matrix

----------------------------------------

type Var = Char

data IExp
  = Val Int
  | Add IExp IExp
  | If  BExp IExp IExp
  deriving Show

data BExp
  = Bool Bool
  | LEq  IExp IExp
  deriving Show

foo :: IExp -> IExp
foo (Add (Val 42)             _i2) = undefined
foo (Add (If _b (Val 42) _i1) _i2) = undefined
foo _                              = undefined

bar :: BExp -> BExp
bar (LEq (Val 42) _i2) = Bool True
bar b                  = b

derive typeRep    { type_ = ''IExp }
derive typeRep    { type_ = ''BExp }
derive funPatsRep { fun   = 'foo  }
derive funPatsRep { fun   = 'bar  }

type IExp'
  = Con 'Val
 :< Con 'Add
 :| Con 'If
 :| Pat ("foo" :#1)
 :| Pat ("foo" :#2)

type BExp'
  = Con 'Bool
 :< Con 'LEq

instance Arbitrary IExp where arbitrary = genEval @IExp'
instance Arbitrary BExp where arbitrary = genEval @BExp'

deriving instance Generic Int
deriving instance Generic Char
deriving instance Generic IExp
deriving instance Generic BExp

----------------------------------------

-- | Branching probabilities
pVal, pAdd, pIf, pBool, pLEq, pfoo1, pfoo2 :: Double
pVal  = 1/5
pAdd  = 1/5
pIf   = 1/5
pfoo1 = 1/5
pfoo2 = 1/5

pBool = 1/2
pLEq  = 1/2

-- | ORDERING:
-- Val, Add, If, Bool, LEq

mC :: Matrix Double
mC = Matrix.fromLists
             {-  Val  |   Add  |   If   |  Bool  |  LEq      |    foo#1  |  foo#2 -}
{-  Val  -} [[   0    ,   0    ,   0    ,   0    ,   0    ,{-|-}    0    ,    0    ]
{-  Add  -} ,[ 2*pVal , 2*pAdd , 2*pIf  ,   0    ,   0    ,{-|-} 2*pfoo1 , 2*pfoo2 ]
{-  If   -} ,[ 2*pVal , 2*pAdd , 2*pIf  , pBool  ,  pLEq  ,{-|-} 2*pfoo1 , 2*pfoo2 ]
{-  Bool -} ,[   0    ,   0    ,   0    ,   0    ,   0    ,{-|-}    0    ,    0    ]
{-  LEq  -} ,[ 2*pVal , 2*pAdd , 2*pIf  ,   0    ,   0    ,{-|-} 2*pfoo1 , 2*pfoo2 ]
             {-----------------------------------------------|---------------------}
{- foo#1 -} ,[  pVal  ,  pAdd  ,  pIf   ,   0    ,   0    ,{-|-}  pfoo1  ,  pfoo2  ]
{- foo#2 -} ,[ 2*pVal , 2*pAdd , 2*pIf  , pBool  ,  pLEq  ,{-|-} 2*pfoo1 , 2*pfoo2 ]]

expand :: Matrix Double
expand = Matrix.identity 5
     <-> -----------------
               p2c

p2c :: Matrix Double
p2c = Matrix.fromLists
             {-  Val   |  Add   |   If   |  Bool  |  LEq  -}
 {- foo#1 -} [[   1    ,   1    ,   0    ,   0    ,   0    ]
 {- foo#2 -} ,[   1    ,   1    ,   1    ,   0    ,   0    ]]


e0 :: Matrix Double
e0 = Matrix.fromList 1 7 [pVal, pAdd, pIf, 0, 0, pfoo1, pfoo2]

level :: Int -> Matrix Double
level 0 = e0
level k = e0 * (mC ^ k)

-- | Predict the distribution using the previous stuff
predict :: Int -> Map String Double
predict n = Map.fromList $ zip
  ["Val", "Add", "If", "Bool", "LEq"]
  (Matrix.toList ((firstLevels + lastLevel) * expand))
  where
    firstLevels = foldr1 (+) (level <$> [0..n-1])
    lastLevel   = Matrix.fromList 1 7 [llVal, 0, 0, llBool, 0, 0, 0]

    llVal  = 2 * (prevLvl!(1,2)) -- Two vals for each Add
           + 2 * (prevLvl!(1,3)) -- Two vals for each If
           + 2 * (prevLvl!(1,5)) -- Two vals for each LEq
           + 1 * (prevLvl!(1,6)) -- Two vals for each foo#1
           + 2 * (prevLvl!(1,6)) -- Two vals for each foo#2

    llBool = 1 * (prevLvl!(1,3)) -- One Bool for each If
           + 1 * (prevLvl!(1,7)) -- One Bool for each foo#2

    prevLvl = level (n-1)
