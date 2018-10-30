{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}

module Test.QuickCheck.FreqArbitrary where

import Test.QuickCheck
import Language.Haskell.TH (Name)

type Size = Int
type Freq  = Int

class FreqArbitrary a where
  freqArbitrary :: (Name -> Size -> Maybe Freq) -> Gen a

class FreqArbitrary1 f where
  liftFreqArbitrary :: (Name -> Size -> Maybe Freq) -> Gen a -> Gen (f a)

at :: (Size -> Maybe Freq) -> Size -> Freq
at f n = maybe 1 id (f n)

withFrequency :: (Name -> Size -> Maybe Freq) -> [(Name, Gen a)] -> Gen a
withFrequency freq gens = sized $ \n -> frequency (map (getFreq n) gens)
  where getFreq n (name, gen) = (freq name `at` n, gen)

constFreq :: Name -> Size -> Maybe Freq
constFreq = const (const (Just 1))

smaller :: Gen a -> Gen a
smaller gen = sized $ \n -> resize (max 0 (n-1)) gen

modify, (%) :: Gen a -> (Int -> Int) -> Gen a
modify gen f = sized $ \n -> resize (f n) gen
(%) = modify

(@!) :: FreqArbitrary1 f => Gen a -> (Name -> Size -> Maybe Freq) -> Gen (f a)
(@!) = flip liftFreqArbitrary

infixl @!


instance FreqArbitrary Int where freqArbitrary _ = arbitrary
instance FreqArbitrary String where freqArbitrary _ = arbitrary

-- instance FreqArbitrary a => FreqArbitrary (Maybe a) where
--   freqArbitrary f
--     = withFrequency f
--     [ ('Nothing, pure Nothing)
--     , ('Just, Just <$> smaller (freqArbitrary f))
--     ]

-- instance FreqArbitrary a => FreqArbitrary [a] where
--   freqArbitrary f
--     = withFrequency f
--     [ ('[], pure [])
--     , ('(:), (:) <$> smaller (freqArbitrary f) <*> smaller (freqArbitrary f))
--     ]

instance FreqArbitrary1 Maybe where
  liftFreqArbitrary f gen
    = withFrequency f
    [ ('Nothing, pure Nothing)
    , ('Just, Just <$> smaller gen)
    ]

instance FreqArbitrary1 [] where
  liftFreqArbitrary f gen
    = withFrequency f
    [ ('[], pure [])
    , ('(:), (:) <$> smaller gen <*> smaller (gen @! f))
    ]
