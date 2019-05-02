module Main where

import Criterion
import Criterion.Main
import Criterion.Types

import Test.Dragen2
import Test.QuickCheck

import qualified RBT.RBT        as RBT
import qualified RE.RE          as RE
-- import qualified Html.Html     as Html
import qualified Html.HtmlUnbal as Html
import qualified Lisp.Lisp      as Lisp

samples :: Int
samples = 10000

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
main = defaultMainWith (defaultConfig { verbosity = Verbose })
  [
  --   bench "RBT/Manual"          $ nfIO (genSamples (RBT.genTree   @Int))
  -- , bench "RBT/Dragen/Linear"   $ nfIO (genSamples (RBT.genTree'  @Int))
  -- , bench "RBT/Dragen/Autobal"  $ nfIO (genSamples (RBT.genTree'' @Int))
  -- , bench "Lisp/Manual"         $ nfIO (genSamples (Lisp.genSExpr))
  -- , bench "Lisp/Dragen/Linear"  $ nfIO (genSamples (Lisp.genSExpr'))
  -- , bench "Lisp/Dragen/Autobal" $ nfIO (genSamples (Lisp.genSExpr''))
  -- , bench "Html/Manual"         $ nfIO (genSamples (Html.genHtml ))
  -- , bench "Html/Dragen/Linear"  $ nfIO (genSamples (HtmlU.genHtml'))
    bench "Html/Dragen/Autobal" $ nfIO (genSamples (Html.genHtml''))
  -- , bench "RE/Manual"       $ nfIO (genSamples (RE.genR       @Char))
  -- , bench "RE/Dragen"       $ nfIO (genSamples (RE.genR'      @Char))
  -- , bench "RE/Dragen/Bal"   $ nfIO (genSamples (RE.genR''     @Char))
  ]
