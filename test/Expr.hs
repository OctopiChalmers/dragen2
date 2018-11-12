{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module Expr where

-- import Test.QuickCheck
-- import Test.QuickCheck.Patterns.Rep
import Test.QuickCheck.Patterns.TH

data Expr a
  = ELit a
  | EAdd (Expr a) (Expr a)
  | EMul (Expr a) (Expr a)
  | EMbE (Maybe (Maybe (Expr a)))
  | ELst [Expr a]
  | EVar String
  deriving Show

foo :: Expr Int -> Bool
foo (EMul (EAdd _ _) _)         = undefined
foo (EAdd _ (EAdd _ (ELit 42))) = undefined
foo _                           = undefined

bar :: Int -> Expr Int -> Int -> a
bar 1 (EAdd (EVar "foo") (ELit _)) = undefined
bar 2 (EMul (ELit 5) _)            = undefined
bar 3 (EMul (ELit _) _)            = undefined
bar _ _                            = undefined

baz :: Expr a -> Bool
baz (EMul (EAdd _ (EAdd _ _)) (EVar "baz")) = undefined
baz (EAdd _ (EAdd _ (ELit _)))            = undefined
baz (EAdd _ _)                            = undefined
baz (EMbE (Just _))                       = undefined
baz (EMbE _)                              = undefined
baz _                                     = undefined

-- deriveAll ''Expr [''Int] [('foo, 2), ('bar, 1), ('baz, 1)]

derive typeRep { typ = ''Expr }
derive patsRep { fun = 'foo }
derive patsRep { fun = 'bar, arg = 2 }
derive patsRep { fun = 'baz, tvs = [''Int] }

main :: IO ()
main = return ()
