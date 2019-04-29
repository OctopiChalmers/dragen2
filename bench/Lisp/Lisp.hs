module Lisp.Lisp where

import GHC.Generics hiding (Rep)
import Control.DeepSeq
import Test.Dragen2
import Test.QuickCheck hiding ((.&.), Fun)

newtype Symbol = Symbol String
  deriving (Show, Eq, Generic)

data SExpr
  = Cons SExpr SExpr  -- ^ Appending list and list
  | Null               -- ^ A representation of empty list
  | AtomInt Int       -- ^ A pattern of the atom for `Int`
  | AtomBool Bool     -- ^ A pattern of the atom for `Bool`
  | AtomSymbol Symbol -- ^ A pattern of the atom for `MaruSymbol`
  | Quote SExpr       -- ^ Delays the evaluation of a 'SExpr'
  deriving (Show, Eq, Generic)

instance NFData Symbol
instance NFData SExpr

execute :: SExpr -> ()
execute (Cons (AtomSymbol (Symbol "let"))
         (Cons (Cons (AtomSymbol var) (Cons val Null))
          (Cons body Null))) = ()
execute (Cons (AtomSymbol (Symbol "if"))
          (Cons cond (Cons x (Cons y Null)))) = ()
execute (Cons (Cons (AtomSymbol (Symbol "defun")) (Cons params (Cons body Null))) args) = ()
execute (Cons (AtomSymbol (Symbol "print")) s) = ()
execute (Cons (AtomSymbol (Symbol "list")) s) = ()

constantFold :: SExpr -> ()
constantFold (AtomSymbol (Symbol "+")) = ()
constantFold (AtomSymbol (Symbol "-")) = ()
constantFold (AtomSymbol (Symbol "*")) = ()
constantFold (AtomSymbol (Symbol "/")) = ()

----------------------------------------
-- Size

lispSize :: SExpr -> Int
lispSize Null = 1
lispSize (AtomInt _) = 1
lispSize (AtomBool _) = 2
lispSize (AtomSymbol _) = 2
lispSize (Quote x) = 1 + lispSize x
lispSize (Cons x y) = 1 + lispSize x + lispSize y

----------------------------------------
-- Manual generator

genSExpr :: BoundedGen SExpr
genSExpr d = go d
  where
    go 0 = frequency
      [ (1, pure Null)
      , (1, AtomInt <$> arbitrary)
      , (1, AtomBool <$> arbitrary)
      , (1, AtomSymbol <$> arbitrary)
      , (1, pure (AtomSymbol (Symbol "+")))
      , (1, pure (AtomSymbol (Symbol "-")))
      , (1, pure (AtomSymbol (Symbol "*")))
      , (1, pure (AtomSymbol (Symbol "/")))
      ]
    go depth = frequency
      [ (1, pure Null)
      , (1, AtomInt <$> arbitrary)
      , (1, AtomBool <$> arbitrary)
      , (1, AtomSymbol <$> arbitrary)
      , (1, Quote <$> go (depth-1))
      , (1, Cons <$> go (depth-1) <*> go (depth-1))
      , (1, do var <- arbitrary
               val <- go (depth-1)
               body <- go (depth-1)
               return (Cons (AtomSymbol (Symbol "let"))
                        (Cons (Cons (AtomSymbol var) (Cons val Null))
                          (Cons body Null))))
      , (1, do cond <- go (depth-1)
               x <- go (depth-1)
               y <- go (depth-1)
               return (Cons (AtomSymbol (Symbol "if"))
                        (Cons cond (Cons x (Cons y Null)))))
      , (1, do params <- go (depth-1)
               body <- go (depth-1)
               args <- go (depth-1)
               return (Cons (Cons (AtomSymbol (Symbol "defun"))
                             (Cons params (Cons body Null))) args))
      , (1, do s <- go (depth-1)
               return (Cons (AtomSymbol (Symbol "print")) s))
      , (1, do s <- go (depth-1)
               return (Cons (AtomSymbol (Symbol "list")) s))
      , (1, pure (AtomSymbol (Symbol "+")))
      , (1, pure (AtomSymbol (Symbol "-")))
      , (1, pure (AtomSymbol (Symbol "*")))
      , (1, pure (AtomSymbol (Symbol "/")))
      ]

----------------------------------------
-- Dragen2

instance Arbitrary Symbol where
  arbitrary = Symbol <$> arbitrary

derive [''SExpr]
  [ constructors ''SExpr
  , patterns     'execute
  , patterns     'constantFold
  ]

type SExprS
   = Con' "Null"
   :+ Con' "AtomInt"
   :+ Con' "AtomBool"
   :+ Con' "AtomSymbol"
   :+ Con  "Quote"
   :+ Con  "Cons"
   :+ Pat  "execute" 1
   :+ Pat  "execute" 2
   :+ Pat  "execute" 3
   :+ Pat  "execute" 4
   :+ Pat  "execute" 5
   :+ Pat' "constantFold" 1
   :+ Pat' "constantFold" 2
   :+ Pat' "constantFold" 3
   :+ Pat' "constantFold" 4

type SExprSBal
   =  (((Con' "Null"
   :+ Con' "AtomInt")
   :+ (Con' "AtomBool"
   :+ Con' "AtomSymbol"))
   :+ ((Con  "Quote"
   :+ Con  "Cons")
   :+ (Pat  "execute" 1
   :+ Pat  "execute" 2)))
   :+ (((Pat  "execute" 3
   :+ Pat  "execute" 4)
   :+ (Pat  "execute" 5
   :+ Pat' "constantFold" 1))
   :+ ((Pat' "constantFold" 2
   :+ Pat' "constantFold" 3)
   :+ Pat' "constantFold" 4))

genSExpr' :: BoundedGen SExpr
genSExpr' = genEval @SExprS

genSExpr'' :: BoundedGen SExpr
genSExpr'' = genEval @SExprSBal
