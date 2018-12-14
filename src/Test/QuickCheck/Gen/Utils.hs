module Test.QuickCheck.Gen.Utils where

import Test.QuickCheck
import Debug.Trace

smaller :: Gen a -> Gen a
smaller g = sized $ \size -> resize (max (size - 1) 0) g

reduce :: Int -> Gen a -> Gen a
reduce n g = sized $ \size -> resize (max (size - n) 0) g

satisfy :: String -> (a -> Bool) -> Gen a -> Gen a
satisfy msg p gen = satisfy' (10 :: Int)
  where
    satisfy' 0 = gen
    satisfy' n = gen >>= \v ->
      if (p v)
      then return v
      else trace ("\n*** RETRYING: " ++ msg) (satisfy' (n-1))
