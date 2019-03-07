module TreeOpt where

import Test.Dragen.Struct

import Tree

type TreeOptSpec = TreeSpec <<< $(optimize @TreeSpec @"Tree" uniform 10)

deriveBoundedArbitrary [''Tree, ''Rose] ''TreeOptSpec
