module RBT.RBT where

import GHC.Generics hiding (Rep)
import Control.DeepSeq

import Test.QuickCheck hiding (Fun)
import Test.Dragen2    hiding (empty)


data Color = R | B deriving (Show, Generic)

data Tree a = E | T Color (Tree a) a (Tree a) deriving (Show, Generic)

instance NFData Color
instance NFData a => NFData (Tree a)


-- Invariants
-- 1. No red node has a red parent
-- 2. Every path from the root node to an empty node contains the same number of
-- black nodes
-- 3. The root and leaves of the tree are black


-- | Simple Tree operations
empty :: Tree a
empty = E

member :: (Ord a) => a -> Tree a -> Bool
member _ E    = False
member x (T _ a y b)
  | x < y     = member x a
  | x == y    = True
  | otherwise = member x b

-- | Insertion
insert :: (Ord a) => a -> Tree a -> Tree a
insert x s = makeBlack $ ins s
  where ins E  = T R E x E
        ins (T color a y b)
          | x < y  = balance color (ins a) y b
          | x == y = T color a y b
          | x > y  = balance color a y (ins b)
        makeBlack (T _ a y b) = T B a y b

balance :: Color -> Tree a -> a -> Tree a -> Tree a
balance B (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
balance B (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
balance B a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
balance B a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
balance color a x b = T color a x b

-- This is simple helper to reduce typing
balance' :: Tree a -> Tree a
balance' (T color left value right) = balance color left value right
balance' x = x

-- | Deletion
delete :: (Ord a) => a -> Tree a -> Tree a
delete x t = makeBlack $ del x t
  where makeBlack (T _ a y b) = T B a y b
        makeBlack E           = E

-- Delete with consecutive red nodes at the top which is rectified in delete
del :: (Ord a) => a -> Tree a -> Tree a
del _ E = E
del x t@(T _ l y r)
  | x < y = delL x t
  | x > y = delR x t
  | otherwise = fuse l r

-- We are in the current node and about to traverse in the left child
-- We have 2 options
-- 1. If it(the ccurent node i.e t) is black delelte from t1 and then balance.
-- 2. If it is red delete from t1 and no need to balance because there are no cases
delL :: Ord a => a -> Tree a -> Tree a
delL x (T _ t1@(T B _ _ _) y t2) = balL $ T B (del x t1) y t2
delL x (T _ t1 y t2) = T R (del x t1) y t2
delL _ x = x

balL :: Tree a -> Tree a
balL (T B (T R t1 x t2) y t3) = T R (T B t1 x t2) y t3
balL (T B t1 y (T B t2 z t3)) = balance' (T B t1 y (T R t2 z t3))
-- t1 root is black in both the last cases because red is handled at the top
balL (T B t1 y (T R (T B t2 u t3) z t4@(T B l value r))) =
  T R (T B t1 y t2) u (balance' (T B t3 z (T R l value r)))
balL x = x


-- We are in the current node and about to traverse in the right child
-- We have 2 options
-- 1. If it(the ccurent node i.e t) is black delelte from t2 and then balance.
-- 2. If it is red delete from t2 and no need to balance because there are no cases
delR :: Ord a => a -> Tree a -> Tree a
delR x (T _ t1 y t2@(T B _ _ _)) = balR $ T B t1 y (del x t2)
delR x (T _ t1 y t2) = T R t1 y (del x t2)
delR _ x = x

balR :: Tree a -> Tree a
balR (T B t1 y (T R t2 x t3)) = T R t1 y (T B t2 x t3)
balR (T B (T B t1 z t2) y t3) = balance' (T B (T R t1 z t2) y t3)
-- t3 root is black in both the last cases because red is handled at the top
balR (T B (T R (T B l value r) z (T B t2 u t3)) y t4) =
  T R (balance' (T B (T R l value r) z t2)) u (T B t3 y t4)
balR x = x


fuse :: Tree a -> Tree a -> Tree a
fuse E t = t
fuse t E = t
fuse t1@(T B _ _ _) (T R t3 y t4) = T R (fuse t1 t3) y t4
fuse (T R t1 x t2) t3@(T B _ _ _) = T R t1 x (fuse t2 t3)
fuse (T R t1 x t2) (T R t3 y t4)  =
  let s = fuse t2 t3
  in case s of
       (T R s1 z s2) -> (T R (T R t1 x s1) z (T R s2 y t4))
       (T B _ _ _)   -> (T R t1 x (T R s y t4))
       x -> x
fuse (T B t1 x t2) (T B t3 y t4)  =
  let s = fuse t2 t3
  in case s of
       (T R s1 z s2) -> (T R (T B t1 x s1) z (T B s2 y t4)) -- consfusing case
       (T B s1 z s2) -> balL (T B t1 x (T B s y t4))
       x -> x


----------------------------------------
-- Tree size

treeSize :: Tree a -> Int
treeSize E = 1
treeSize (T _ l _ r) = 2 + treeSize l + treeSize r

----------------------------------------
-- Manual generator

genTree :: (Arbitrary a, Ord a) => BoundedGen (Tree a)
genTree depth = go depth
  where
    go 0 = frequency
      [ (1, pure E)
      , (1, pure empty)
      ]
    go n = frequency
      [ -- Con "E"
        (1, pure E)
        -- Con "T"
      , (1, T <$> arbitrary <*> go (n-1) <*> arbitrary <*> go (n-1))
        -- Fun' "empty"
      , (1, pure empty)
        -- Fun  "insert"
      , (1, insert <$> arbitrary <*> go (n-1))
        -- Fun  "balance'"
      , (1, balance' <$> go (n-1))
        -- Fun  "delete"
      , (1, delete <$> arbitrary <*> go (n-1))
        -- Fun  "fuse"
      , (1, fuse <$> go (n-1) <*> go (n-1))
        -- Pat  "balL" 1
      , (1, do t1 <- go (n-1)
               x <- arbitrary
               t2 <- go (n-1)
               y <- arbitrary
               t3 <- go (n-1)
               return (T B (T R t1 x t2) y t3)
        )
        -- Pat  "balL" 2
      , (1, do t1 <- go (n-1)
               y <- arbitrary
               t2 <- go (n-1)
               z <- arbitrary
               t3 <- go (n-1)
               return (T B t1 y (T B t2 z t3))
        )
        -- Pat  "balL" 3
      , (1, do t1 <- go (n-1)
               y <- arbitrary
               t2 <- go (n-1)
               u  <- arbitrary
               t3 <- go (n-1)
               z <- arbitrary
               l <- go (n-1)
               value <- arbitrary
               r <- go (n-1)
               return (T B t1 y (T R (T B t2 u t3) z (T B l value r)))
        )
        -- Pat  "balR" 1
      , (1, do t1 <- go (n-1)
               y <- arbitrary
               t2 <- go (n-1)
               x <- arbitrary
               t3 <- go (n-1)
               return (T B t1 y (T R t2 x t3))
        )
        -- Pat  "balR" 2
      , (1, do t1 <- go (n-1)
               z <- arbitrary
               t2 <- go (n-1)
               y <- arbitrary
               t3 <- go (n-1)
               return (T B (T B t1 z t2) y t3)
        )
        -- Pat  "balR" 3
      , (1, do l <- go (n-1)
               value <- arbitrary
               r <- go (n-1)
               z <- arbitrary
               t2 <- go (n-1)
               u  <- arbitrary
               t3 <- go (n-1)
               y <- arbitrary
               t4 <- go (n-1)
               return (T B (T R (T B l value r) z (T B t2 u t3)) y t4)
        )
      ]



----------------------------------------
-- Dragen2

instance Arbitrary Color where
  arbitrary = elements [R, B]

derive [''Tree]
  [ constructors ''Tree
  , interface    ''Tree |> blacklist ['balance]
  , patterns     'balL
  , patterns     'balR
  ]

type RBT_Spec
  =  Con "E"
  :+ Con "T"
  :+ Fun "empty"
  :+ Fun "insert"
  :+ Fun "balance'"
  :+ Fun "delete"
  :+ Fun "fuse"
  :+ Pat "balL" 1
  :+ Pat "balL" 2
  :+ Pat "balL" 3
  :+ Pat "balR" 1
  :+ Pat "balR" 2
  :+ Pat "balR" 3


genTree' :: forall a. (Ord a, Arbitrary a) => BoundedGen (Tree a)
genTree' = genRep @(RBT_Spec <| a)
