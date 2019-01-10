{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}

module RBT where

import Control.Monad
import Test.QuickCheck
import Data.Maybe as Maybe

data Color
  = Red
  | Black
  deriving (Eq, Show)

data RBT a
  = Leaf
  | Node Color (RBT a) a (RBT a)
  deriving (Eq, Show)

color :: RBT a -> Color
color Leaf = Black
color (Node c _ _ _) = c

empty :: RBT a
empty = Leaf

member :: Ord a => a -> RBT a -> Bool
member _ Leaf = False
member x (Node _ a y b)
  | x < y     = member x a
  | x > y     = member x b
  | otherwise = True

elements :: Ord a => RBT a -> [a]
elements t = aux t [] where
  aux Leaf xs = xs
  aux (Node _ a y b) xs = aux a (y : aux b xs)

insert :: Ord a => a -> RBT a -> RBT a
insert x t = blacken (ins t)
  where
    ins Leaf = Node Red Leaf x Leaf
    ins s@(Node c a y b)
      | x < y     = balance (Node c (ins a) y b)
      | x > y     = balance (Node c a y (ins b))
      | otherwise = s

blacken :: RBT a -> RBT a
blacken (Node _ a e b) = (Node Black a e b)
blacken Leaf = error "insert never returns empty tree"

balance :: Ord a => RBT a -> RBT a
balance (Node Black (Node Red (Node Red a x b) y c) z d)
  = (Node Red (Node Black a x b) y (Node Black c z d))
balance (Node Black (Node Red a x (Node Red b y c)) z d)
  = (Node Red (Node Black a x b) y (Node Black c z d))
balance (Node Black a x (Node Red (Node Red b y c) z d))
  = (Node Red (Node Black a x b) y (Node Black c z d))
balance (Node Black a x (Node Red b y (Node Red c z d)))
  = (Node Red (Node Black a x b) y (Node Black c z d))
balance t = t

----------------------------------------
-- Arbitrary instances

instance Arbitrary (RBT Int)  where
   arbitrary = do
     xs <- arbitrary :: Gen [Int]
     return (foldr insert empty xs)

----------------------------------------
-- Properties

prop_insert_1 :: Int -> RBT Int -> Bool
prop_insert_1 x t = member x (insert x t)

prop_insert_2 :: Int -> RBT Int -> Bool
prop_insert_2 x t = all (\y -> member y (insert x t)) (elems t)
  where
   elems Leaf = []
   elems (Node _ l e r) = elems l ++ [e] ++ elems r

prop_RBT_1 :: RBT Int -> Bool
prop_RBT_1 t = color t == Black

prop_RBT_2 :: RBT Int -> Bool
prop_RBT_2 t = Maybe.isJust (aux t)
  where
   aux Leaf = Just 1 :: Maybe Int
   aux (Node c l _ r) = do
     bh1 <- aux l
     bh2 <- aux r
     guard (bh1 == bh2)
     return (case c of { Red -> bh1; Black -> bh1 + 1 })

prop_RBT_3 :: RBT Int -> Bool
prop_RBT_3 Leaf = True
prop_RBT_3 (Node Red l _ r)
  = prop_RBT_3 l && prop_RBT_3 r
  && color l == Black
  && color r == Black
prop_RBT_3 (Node Black l _ r)
  = prop_RBT_3 l
  && prop_RBT_3 r


prop_BST :: RBT Int -> Bool
prop_BST Leaf = True
prop_BST (Node _ l x r)
  = prop_BST l && prop_BST r
  && maybe True (x >) (tmax l)
  && maybe True (x <) (tmin r)

tmin :: RBT Int -> Maybe Int
tmin Leaf = Nothing
tmin (Node _ l x r)
  = case (tmin l, tmin r) of
  (Just lmin, Just rmin) -> Just (min x (min lmin rmin))
  (Just lmin, Nothing)   -> Just (min x lmin)
  (Nothing,   Just rmin) -> Just (min x rmin)
  (Nothing,   Nothing)   -> Just x

tmax :: RBT Int -> Maybe Int
tmax Leaf = Nothing
tmax (Node _ l x r)
  = case (tmax l, tmax r) of
  (Just lmax, Just rmax) -> Just (max x (max lmax rmax))
  (Just lmax, Nothing)   -> Just (max x lmax)
  (Nothing,   Just rmax) -> Just (max x rmax)
  (Nothing,   Nothing)   -> Just x


----------------------------------------
-- QuickCheck runner

return []

runTests :: IO Bool
runTests = $quickCheckAll
