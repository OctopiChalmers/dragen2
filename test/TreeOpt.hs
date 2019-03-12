module TreeOpt where

import Test.Dragen2

import Tree

type TreeOptSpec = TreeSpec <<< $(optimize @TreeSpec @"Tree" uniform 10)

deriveBoundedArbitrary [''Tree, ''Rose] ''TreeOptSpec
