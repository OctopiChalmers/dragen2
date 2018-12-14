{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ExistentialQuantification #-}

module PredMutRec where

import Unsafe.Coerce
import Data.Kind
import Data.Proxy
import Data.Reflection

import GHC.TypeLits (KnownNat)
import GHC.Generics
import GHC.Generics.Countable

import Test.QuickCheck
import Test.QuickCheck.Branching
import Test.QuickCheck.HRep
import Test.QuickCheck.HRep.Infix
import Test.QuickCheck.HRep.TH

import Data.Map.Strict (Map)
import Data.Vector (Vector, (!))
import Data.Matrix (Matrix, (<->), (<|>))
import qualified Data.Map.Strict as Map
import qualified Data.Vector as Vector
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
foo (Add (Add (Val 42)   _i1) _i2) = undefined
foo (Add (If _b (Val 42) _i1) _i2) = undefined
foo _                              = undefined

bar :: BExp -> BExp
bar (LEq (Val 42) _i2) = Bool True
bar b                  = b

deriveWithFam [''IExp, ''BExp]
  [ typeRep ''IExp
  , typeRep ''BExp
  , patsRep 'foo
  , patsRep 'bar
  ]

-- derive TypeRep    { ty  = ''IExp, fam = [''IExp, ''BExp] }
-- derive TypeRep    { ty  = ''BExp, fam = [''IExp, ''BExp] }
-- derive FunPatsRep { fun = 'foo  , fam = [''IExp, ''BExp], arg = 1 }
-- derive FunPatsRep { fun = 'bar  , fam = [''IExp, ''BExp], arg = 1 }

type IExp'
  = Term (Con 'Val) .* 2
  + Con 'Add
  + Con 'If .* 3
  + "foo" #1
  + "foo" #2


type BExp'
  = Term (Con 'Bool)
  + Con 'LEq
  + "bar" #1 .* 2

type ExpFam = Fam '[IExp', BExp']

instance Arbitrary IExp where arbitrary = genEval @IExp'
instance Arbitrary BExp where arbitrary = genEval @BExp'

-- type IExp'' = HRep IExp + HRep "foo"
-- type IExp'' = HRep IExp + HRep "foo" + HRep IExp
-- type BExp'' = HRep BExp + HRep "bar"

-- instance Arbitrary IExp where arbitrary = genEval @IExp'
-- instance Arbitrary BExp where arbitrary = genEval @BExp'

deriving instance Generic Int
deriving instance Generic Char
deriving instance Generic IExp
deriving instance Generic BExp

----------------------------------------

-- -- | Pattern expansion matrices
-- expIExp'2IExp :: Matrix Double
-- expIExp'2IExp = Matrix.fromLists
--             {-   Val   |  Add   |   If   -}
-- {-  Val  -} [[    1    ,   0    ,    0    ]
-- {-  Add  -} ,[    0    ,   1    ,    0    ]
-- {-  If   -} ,[    0    ,   0    ,    1    ]
-- {- foo#1 -} ,[    1    ,   2    ,    0    ]
-- {- foo#2 -} ,[    1    ,   1    ,    1    ]]

-- expBExp'2IExp :: Matrix Double
-- expBExp'2IExp = Matrix.fromLists
--             {-   Val   |  Add   |   If   -}
-- {-  Bool -} [[    0    ,   0    ,    0    ]
-- {-  LEq  -} ,[    0    ,   0    ,    0    ]
-- {- pbar1 -} ,[    1    ,   0    ,    0    ]]

-- -- | Pattern expansion matrices
-- expIExp'2BExp :: Matrix Double
-- expIExp'2BExp = Matrix.fromLists
--             {-   Bool  |  LEq   -}
-- {-  Val  -} [[    0    ,   0     ]
-- {-  Add  -} ,[    0    ,   0     ]
-- {-  If   -} ,[    0    ,   0     ]
-- {- foo#1 -} ,[    0    ,   0     ]
-- {- foo#2 -} ,[    0    ,   0     ]]

-- expBExp'2BExp :: Matrix Double
-- expBExp'2BExp = Matrix.fromLists
--             {-   Bool  |   LEq  -}
-- {-  Bool -} [[    1    ,    0    ]
-- {-  LEq  -} ,[    0    ,    1    ]
-- {- pbar1 -} ,[    0    ,    1    ]]

-- expand' :: Matrix Double
-- expand' = (expIExp'2IExp <|> expIExp'2BExp)
--      <-> (expBExp'2IExp <|> expBExp'2BExp)

----------------------------------------

-- -- | Branching probabilities
-- pVal, pAdd, pIf, pfoo1, pfoo2 :: Double
-- pVal: pAdd: pIf: pfoo1: pfoo2:_ = Vector.toList $ (probs @IExp') ! 0

-- pBool, pLEq, pbar1 :: Double
-- pBool: pLEq: pbar1:_ = Vector.toList $ (probs @BExp') ! 0

-- -- -- | ORDERING:
-- -- -- IExp, BExp

-- -- | Branching processes matrices
-- m11 :: Matrix Double
-- m11 = col (beta' @ExpFam 0 0) * row (probs' @ExpFam 0)

-- -- m11 :: Matrix Double
-- -- m11 = Matrix.fromLists
-- --              {-  Val  |   Add   |   If   |  foo#1  |  foo#2 -}
-- -- {-  Val  -} [[   0    ,   0     ,   0    ,    0    ,    0    ]
-- -- {-  Add  -} ,[ 2*pVal , 2*pAdd  , 2*pIf  , 2*pfoo1 , 2*pfoo2 ]
-- -- {-  If   -} ,[ 2*pVal , 2*pAdd  , 2*pIf  , 2*pfoo1 , 2*pfoo2 ]
-- -- {- foo#1 -} ,[  pVal  ,  pAdd   ,  pIf   ,  pfoo1  ,  pfoo2  ]
-- -- {- foo#2 -} ,[ 2*pVal , 2*pAdd  , 2*pIf  , 2*pfoo1 , 2*pfoo2 ]]

-- m12 :: Matrix Double
-- m12 = col (beta' @ExpFam 0 1) * row (probs' @ExpFam 1)

-- -- m12 :: Matrix Double
-- -- m12 = Matrix.fromLists
-- --              {-  Bool  |  LEq   |  bar#1 -}
-- -- {-  Val  -} [[    0    ,   0    ,    0    ]
-- -- {-  Add  -} ,[    0    ,   0    ,    0    ]
-- -- {-  If   -} ,[  pBool  ,  pLEq  ,  pbar1  ]
-- -- {- foo#1 -} ,[    0    ,   0    ,    0    ]
-- -- {- foo#2 -} ,[  pBool  ,  pLEq  ,  pbar1  ]]

-- m21 :: Matrix Double
-- m21 = col (beta' @ExpFam 1 0) * row (probs' @ExpFam 0)

-- -- m21 :: Matrix Double
-- -- m21 = Matrix.fromLists
-- --              {-  Val  |   Add  |   If  |  foo#1  |  foo#2 -}
-- -- {-  Bool -} [[   0    ,   0    ,   0   ,    0    ,    0    ]
-- -- {-  LEq  -} ,[ 2*pVal , 2*pAdd , 2*pIf , 2*pfoo1 , 2*pfoo2 ]
-- -- {- pbar1 -} ,[  pVal  ,  pAdd  ,  pIf  ,  pfoo1  ,  pfoo2  ]]

-- m22 :: Matrix Double
-- m22 = col (beta' @ExpFam 1 1) * row (probs' @ExpFam 1)

-- -- -- m22 :: Matrix Double
-- -- -- m22 = Matrix.fromLists
-- -- --             {-  Bool  |  LEq   |  bar#1 -}
-- -- -- {-  Bool -} [[   0    ,   0    ,    0    ]
-- -- -- {-  LEq  -} ,[   0    ,   0    ,    0    ]
-- -- -- {- pbar1 -} ,[   0    ,   0    ,    0    ]]

-- mC :: Matrix Double
-- mC =  (m11 <|> m12)
--   <-> (m21 <|> m22)
