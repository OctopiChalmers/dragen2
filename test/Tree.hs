module Tree where

import Test.Dragen.Struct


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


foo :: something -> Tree a -> somethingElse
foo _ (Node (Forest _) (Leaf _))       = undefined
foo _ (Forest (Rose [Leaf _, Leaf _])) = undefined
foo _ _                                = undefined


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

type TreeSpec =
  '[ "Tree"
       := Con' "Leaf" :* 2
       :+ Con  "Node"
       :+ Fun  "node"
       :+ Pat  "foo" 1
       :+ Pat  "foo" 2
   , "Rose"
       := Con' "Rose"
   ]
