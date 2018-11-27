{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

module Expr_test where

import Test.QuickCheck
import Test.QuickCheck.Patterns.Rep

import Expr

type Expr_Int_foo_bar_baz
  = Rep (Expr Int) @> 10
  ? Pat "foo"      @> 5
  + Pat "bar"      @> 2
  + Pat "baz"      @> 1

genExpr :: Gen (Expr Int)
genExpr = genEval @Expr_Int_foo_bar_baz

genExpr' :: Gen (Expr Int)
genExpr' = genEval @(Rep (Expr Int) @> 50
                   ? Pat "foo"      @> 2
                   + Pat "baz"      @> 1)

genExpr'' :: Gen (Expr Int)
genExpr'' = genEval @(Interleave
                     (Expr Int) 5
                     [ Pat "foo"
                     , Pat "bar"])
