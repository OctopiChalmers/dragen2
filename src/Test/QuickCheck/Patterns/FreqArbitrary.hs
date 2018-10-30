{-# LANGUAGE TemplateHaskell #-}

module Test.QuickCheck.FreqArbitrary where

import Test.QuickCheck
import Language.Haskell.TH (Name)

type Size = Int
type Freq  = Int

class FreqArbitrary a where
  freqArbitrary :: (Name -> Size -> Freq) -> Gen a

class FreqArbitrary1 f where
  liftFreqArbitrary :: (Name -> Size -> Freq) -> Gen a -> Gen (f a)

instance FreqArbitrary1 Maybe where
  liftFreqArbitrary freq gen = sized $ \n ->
    frequency
    [ (freq 'Nothing n, pure Nothing)
    , (freq 'Just    n, Just <$> resize (n-1) gen)
    ]

instance FreqArbitrary1 [] where
  liftFreqArbitrary freq gen = sized $ \n ->
    frequency
    [ (freq '[]  n, pure [])
    , (freq '(:) n, (:) <$> resize (n-1) gen <*> undefined)
    ]
