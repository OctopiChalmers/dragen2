module TestTree where

import Tree

import Test.Dragen.Struct
import Test.Dragen.Struct.Spec

type OptSpec = GenSpec <<< $(optimize @GenSpec @"Tree" uniform 10)

deriveBoundedArbitrary [''Tree, ''Rose] ''OptSpec
