{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module PredList where

import GHC.Generics

import Test.QuickCheck
import Test.QuickCheck.Branching
import Test.QuickCheck.HRep
import Test.QuickCheck.HRep.Infix
import Test.QuickCheck.HRep.TH


data T1 = A | B [T1] | C [T2] deriving (Show, Generic)
data T2 = D | E [T1]          deriving (Show, Generic)

f1 :: [T2] -> T1
f1 = C

f2 :: [T1] -> T2
f2 = E

type T_S = '[ "T1" := HRep "T1" :+ HRep "<T1>"
            , "T2" := HRep "T2" :+ HRep "<T2>" ]
deriveAll [''T1, ''T2] [module_ ''T1, module_ ''T2] ''T_S
