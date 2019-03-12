module Main where

import qualified Data.Vector as Vector

import Test.Dragen2

import TreeOpt
import Tree


main :: IO ()
main = do
  testTree


testTree :: IO ()
testTree = do

  putStrLn $ "\n-------------------------------------"
  let treeNames = famNames          @(Values TreeSpec)

  putStrLn $ "Branching factors of TreeSpec:"
  let treeBfs   = famBeta           @(Values TreeSpec)
  print $ Vector.zipWith Vector.zip treeNames treeBfs

  putStrLn $ "Generation probabilities of TreeSpec:"
  let treeProbs = famBranchingProbs @(Values TreeSpec)
  print $ Vector.zipWith Vector.zip treeNames treeProbs

  putStrLn $ "Generation probabilities of TreeOptSpec:"
  let treeOptProbs = famBranchingProbs @(Values TreeOptSpec)
  print $ Vector.zipWith Vector.zip treeNames treeOptProbs

  putStrLn $ "Prediction with uniform frequencies:"
  let treePred = predictSpec @TreeSpec @"Tree" 10
  print $ treePred

  putStrLn $ "Prediction with optimized frequencies:"
  let treeOptPred = predictSpec @TreeOptSpec @"Tree" 10
  print $ treeOptPred
