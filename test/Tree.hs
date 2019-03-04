module Tree where

import Test.Dragen.Struct
import Test.Dragen.Struct.TH.Util

import Test.QuickCheck hiding (Fun)


data Tree a
  = Leaf   a
  | Node   (Tree a) (Tree a)
  | Tuple  (Tree a, Tree a)
  | Forest (Rose a)
  deriving Show

data Rose a
  = Rose [Tree a]
  deriving Show


leaf :: a -> Tree a
leaf = Leaf

merge :: Tree a -> Tree a -> Tree a
merge t1 t2 = Tuple (t1, t2)

node :: Tree a -> Tree a -> Tree a
node t1 t2 = Node t1 t2


foo _ (Node (Forest xs) (Leaf _))      = undefined
foo _ (Forest (Rose [Leaf _, Leaf _])) = undefined



derive
  [''Tree, ''Rose]
  [ constructors ''Tree
    |> blacklist ['Tuple]
  , interface ''Tree
    |> alias "Tree interface"
    |> blacklist ['merge]
  , patterns 'foo
    |> argNum 2
  , constructors ''Rose
  ]


type GenSpec =
  '[ "Tree"
       := Con' "Leaf" :* 2
       :+ Con  "Node"
       :+ Fun  "node"
       :+ Pat  "foo" 1
   , "Rose"
       := Con' "Rose"
   ]
