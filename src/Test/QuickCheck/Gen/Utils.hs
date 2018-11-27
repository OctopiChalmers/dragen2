module Test.QuickCheck.Gen.Utils where

import Test.QuickCheck
import Debug.Trace

smaller :: Gen a -> Gen a
smaller g = sized $ \size -> resize (max (size - 1) 0) g

reduce :: Int -> Gen a -> Gen a
reduce n g = sized $ \size -> resize (max (size - n) 0) g

satisfy :: String -> (a -> Bool) -> Gen a -> Gen a
satisfy msg p gen = do
  v <- gen
  case p v of
    True -> return v
    False -> trace ("\n*** RETRYING: " ++ msg) (satisfy msg p gen)
