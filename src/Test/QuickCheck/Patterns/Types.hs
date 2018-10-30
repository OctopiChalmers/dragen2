module Test.QuickCheck.Patterns.Types where

import Data.List
import Data.Maybe
import Data.Function

import Language.Haskell.TH (Name)

-- | Type environment
type TyEnv = [TyDec]

-- | Type declaration (data, newtype, etc)
data TyDec
  = TyDec
  { tsig   :: Ty    -- ^ Left hand side of the type declaration.
  , tcons  :: [Con] -- ^ Data constructors constructors
  , isPrim :: Bool  -- ^ Is this data type primitive? (e.g. Int, Bool)
  } deriving Show

-- | Data constructors
data Con
  = Con
  { cname :: Name -- ^ Constructor name
  , cargs :: [Ty] -- ^ Constructor args
  , isRec :: Bool -- ^ Is this constructor recursive?
  } deriving Show

-- | Type signatures
data Ty
  = TC Name      -- ^ Base type name (e.g. Int, Maybe, Either)
  | TV Name      -- ^ Type variables (e.g. a, b)
  | Ty :@  Ty    -- ^ Type application (e.g. Maybe Int)
  | Ty :-> Ty    -- ^ Function application (e.g Int -> Bool)
  deriving (Show, Eq, Ord)


infixr :@
infixr :->

-- -- | Function match clauses
-- data FunDef
--   = FunDef Name Ty [[DPat]]
--   deriving (Show, Eq)

data ClausePat
  = ClausePat [Pattern]
  deriving (Show, Eq)

-- | Patterns
data Pattern
  = AnyP                -- ^ Variable or wildcard patterns
  | LitP LitP           -- ^ Literal patterns
  | ConP Name [Pattern] -- ^ Constructors applied to patterns
  | ParenP Pattern      -- ^ A pattern between parens
  deriving (Show, Eq)

-- | Literal patterns
data LitP
  = IntL Integer
  | CharL Char
  | StringL String
  | FloatL Rational
  deriving (Show, Eq)

instance Eq TyDec where
    (==) = (==) `on` tsig

instance Eq Con where
    (==) = (==) `on` cname


apply :: Name -> [Ty] -> Ty
apply = foldl (:@) . TC

unapply :: Ty -> (Name, [Ty])
unapply (TC name) = (name, [])
unapply (TV name) = (name, [])
unapply (l :@ r) = (name, l' ++ [r])
  where (name, l') = unapply l
unapply (l :-> r) = error $ "unapply: cannot unapply function type "
                    ++ show (l :-> r)

tyDecName :: TyDec -> Name
tyDecName = fst . unapply . tsig

tyDecArgs :: TyDec -> [Ty]
tyDecArgs = snd . unapply . tsig

flatten :: Ty -> [Name]
flatten (TC name) = [name]
flatten (TV name) = [name]
flatten (l :@ r) = flatten l ++ flatten r
flatten (l :-> r) = flatten l ++ flatten r

isSubtype :: Ty -> Ty -> Bool
isSubtype t t' | t == t' = True
isSubtype t (l :@ r) = t `isSubtype` l || t `isSubtype` r
isSubtype t (l :-> r) = t `isSubtype` l || t `isSubtype` r
isSubtype _ _ = False

occurrences :: Ty -> Con -> Int
occurrences ts con = countSat (==ts) (cargs con)

countSat :: (a -> Bool) -> [a] -> Int
countSat p = length . filter p

-- Extract type signatures from a type env.
envTySigs :: TyEnv -> [Ty]
envTySigs = map tsig

-- Extract the list of type constructor names from a type env.
envCons :: TyEnv -> [Name]
envCons = nub . map cname . concatMap tcons

-- Split constructors into recursive and terminals.
envConsByRole :: TyEnv -> ([Con], [Con])
envConsByRole = partition isRec . concatMap tcons

envRecCons :: TyEnv -> [Con]
envRecCons = fst . envConsByRole

envTermCons :: TyEnv -> [Con]
envTermCons = snd . envConsByRole

-- Is this constructor terminal?
isTerminal :: TyEnv -> Name -> Bool
isTerminal env cn = cn `elem` map cname (envTermCons env)

-- Extracts type parameters of every type constructor.
involvedWith :: TyDec -> [Ty]
involvedWith = nub . concatMap cargs . tcons

-- Given a type constructor name, returns its siblings (including itself).
envSiblingCons :: Name -> TyEnv -> [Con]
envSiblingCons cn env = tcons (conTySig env cn)

-- Is a type constructor sibling with another?
envIsSiblingCon :: TyEnv -> Name -> Name -> Bool
envIsSiblingCon env = (==) `on` conTySig env

-- Extracts a type constructor from a given type.
getCon :: Name -> TyDec -> Con
getCon cn t = fromMaybe
    (error $ "getCon: looking for " ++ show cn ++ " in " ++ show (tsig t))
    (find ((cn==) . cname) (tcons t))

-- Finds a type declaration from the environment
findTyDec :: Name -> TyEnv -> TyDec
findTyDec tname env = fromMaybe
  (error $ "findTyDec: " ++ show tname ++ " not found in " ++ show env)
  (find (\td -> tyDecName td == tname) env)

-- Given a type constructor name, finds its associated type.
conTySig :: TyEnv -> Name -> TyDec
conTySig env cn = fromMaybe
    (error $ "conTySig: " ++ show cn ++ " not found in " ++ show env)
    (find (any ((cn==) . cname) . tcons) env)

-- | Usefull unsupported messages
unsupported :: Show a => String -> a -> any
unsupported fname val = error $ fname ++ ": not yet supported " ++ show val
