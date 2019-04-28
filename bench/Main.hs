module Main where

import Criterion
import Criterion.Main

import Test.Dragen2
import Test.QuickCheck

import qualified RBT
import qualified RE
import qualified Html

samples :: Int
samples = 1000

size :: Int
size = 30

depth :: Int
depth = 5

genSamples :: Show a => BoundedGen a -> IO [a]
genSamples gen
  = sequence
  . replicate samples
  . generate
  . resize size
  $ gen depth

main :: IO ()
main = defaultMain
  [ bench "RBT/Dragen"  $ nfIO (genSamples (RBT.genTree' @Int))
  , bench "RBT/Manual"  $ nfIO (genSamples (RBT.genTree  @Int))
  , bench "RE/Dragen"   $ nfIO (genSamples (RE.genR'     @Char))
  , bench "RE/Manual"   $ nfIO (genSamples (RE.genR      @Char))
  , bench "Html/Dragen" $ nfIO (genSamples (Html.genHtml'))
  , bench "RE/Manual"   $ nfIO (genSamples (Html.genHtml ))
  ]
