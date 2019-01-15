module Exp where

data Exp  =  Val  Int
          |  Add  Exp  Exp
          |  Mul  Exp  Exp
          |  If   Exp  Exp  Exp
          deriving Show

eval :: Exp -> Int
eval (Val n) = n
eval (Add x y) = eval x + eval y
eval (Mul x y) = eval x * eval y
eval (If b x y) = if (eval b /= 0) then eval x else eval y

-- genExp :: Gen Exp
-- genExp = sized gen
--   where
--     gen 0 = Val <$> genInt
--     gen n = oneof
--       [  Val  <$> arbitrary
--       ,  Add  <$> gen pred   <*> gen pred
--       ,  Mul  <$> gen pred   <*> gen pred
--       ,  If   <$> arbitrary  <*> gen pred <*> gen pred ]


-- foo :: Exp -> Exp
-- foo (Mul (Add x (Val 42)) (Mul (Val 0) y))  = ...
-- foo (Add (Add x y) (Val z))                 = ...
-- foo (Add (Val 42)  (Val 24))                = ...
-- foo x                                       = ...

(.+) = Add
(.*) = Mul
val = Val

square :: Exp -> Exp
square x = Mul x x

neg :: Exp -> Exp
neg x = Mul x (Val (-1))

minus :: Exp -> Exp -> Exp
minus x y = Add x (neg y)

pow :: Exp -> Exp -> Exp
pow b e = If e (Mul b (pow b (minus e (Val 1)))) (Val 1)
