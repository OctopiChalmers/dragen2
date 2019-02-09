module Test where

type Var = String

data RE
  = Empty
  | Lit   Char
  | Or    RE   RE
  | Seq   RE   RE
  | Star  RE
  deriving Show

-- simpl :: RE -> RE
-- simpl (Star (Star re)) = Star (opt re)
-- simpl (Seq re Empty)   = opt re   
-- simpl (Seq Empty re)   = opt re   
-- simpl x                = x

-- try :: RE -> RE -> RE
-- try f g = (f `Or` Empty) g

-- plus :: RE -> RE
-- plus re = re `Seq` (Star re)

-- digit :: RE
-- digit = '0' `Or` '1' `Or` ... `Or` 9

-- lower :: RE
-- lower = 'a' `Or` 'b' `Or` ... `Or` 'z'

