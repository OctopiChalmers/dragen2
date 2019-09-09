{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE CPP #-}

module Test.Dragen2.TH.Util where

import System.FilePath
import System.Directory
import Data.List
import Control.Arrow
import Control.Monad.Extra
import Control.Monad.IO.Class
import System.Console.ANSI

import Test.Dragen2.TH.Ppr
import Language.Haskell.TH hiding (Ppr, ppr, pprint)
import Language.Haskell.TH.Desugar

import qualified Data.Vector as Vector
import qualified GHC.Generics as Generics
import qualified Test.QuickCheck as QC
import qualified Test.Dragen2.Rep as Rep
import qualified Test.Dragen2.BoundedArbitrary as BoundedArb


-- | Derive "syntactic" equivalence relations for DTypes
deriving instance Eq DTyVarBndr
deriving instance Eq DPred
deriving instance Eq DType
deriving instance Eq DCon
deriving instance Eq DConFields

instance Ppr DType      where ppr = ppr . typeToTH
instance Ppr DCon       where ppr = ppr . conToTH
instance Ppr DExp       where ppr = ppr . expToTH
instance Ppr DTyVarBndr where ppr = ppr . tvbToTH
instance Ppr DDec       where ppr = ppr . decToTH
instance Ppr DPred      where ppr = ppr . predToTH

----------------------------------------
-- | Reification utilities

-- | Reify the full path of the module calling this splice
currentFile :: Q FilePath
currentFile = do
  dir  <- liftIO getCurrentDirectory
  file <- location
  return (dir </> loc_filename file)

-- | Reify a name or die gracefully
reifyName :: Name -> Q DInfo
reifyName name = do
  mbInfo <- dsReify name
  case mbInfo of
    Just info -> return info
    Nothing -> dragenError "could not reify name" [name]

-- | Retrieve a function type signature
reifyFunSig :: Name -> Q ([DTyVarBndr], [DPred], [DType], DType)
reifyFunSig funName = do
  DVarI _ funTy _ <- reifyName funName
  -- let funSig = splitSignature funTy
  -- return (init funSig, last funSig)
  return (unravel funTy)

-- | Reify the constructors of a given type name
getDCons :: Name -> Q [DCon]
getDCons typeName = do
  (vs, cons) <- getDataD (nameBase typeName) typeName
  tyVars <- mapM desugar vs
  let ty = simplifyDType (typeName <<* tyVars)
  concatMapM (dsCon tyVars ty) cons

getDConNames :: Name -> Q [Name]
getDConNames typeName = fmap dConName <$> getDCons typeName

getFamDConNames :: [Name] -> Q [[Name]]
getFamDConNames = mapM getDConNames

-- | Collect the pattern variables and depth of a pattern in from left to right.
-- Since the function defining the pattern can be using an instantiated type, we
-- need to carry it around to make the proper substitutions.
collectPatVarsDepthsTypes :: DType -> DPat -> Q [(Integer, DType)]
collectPatVarsDepthsTypes = collect 0
  where
    collect _ _ (DLitPa _) = return []
    collect d t (DVarPa _) = return [(d, t)]
    collect d t (DTildePa p) = collect d t p
    collect d t (DBangPa p) = collect d t p
    collect d t DWildPa = return [(d, t)]
    collect d t (DConPa conName conFieldsPats)
      = collectCon (d+1) t conName conFieldsPats
    collect _ _ p = unsupported 'collectPatVarsDepthsTypes (show p)

    -- | Calculate the instatiated types of each field and call recursively.
    collectCon d t conName conFieldsPats = do
      conFieldsTys <- getConFieldTypes conName t
      let conFieldsTysPats = zip conFieldsTys conFieldsPats
      concatMapM (uncurry (collect d)) conFieldsTysPats


-- | Get the field types of a constructor, instantiated against a concrete type
getConFieldTypes :: Name -> DType -> Q [DType]
getConFieldTypes conName insTy = do
  -- | Obtain the original data definition where conName is declared
  ogTyName <- dataConNameToDataName conName
  (vs, _) <- getDataD mempty ogTyName
  ogVars <- mapM desugar vs
  -- | Calculate variable substitutions with the concrete type
  let ogTy = ogTyName <<* ogVars
      Just subst = matchTy YesIgnore ogTy (simplifyDType insTy)
  -- | Get the original types of the fields definitions (maybe parametric)
  con <- dataConNameToCon conName
  DCon _ _ _ conFields _ <- head <$> dsCon ogVars ogTy con
  let conFieldsTys = dConFieldsTypes conFields
  -- | Return the field types instantiated with the concrete type
  mapM (substTy subst) conFieldsTys

----------------------------------------
-- | Observations over DTypes

-- | Simplify a DType removing foralls and signatures
simplifyDType :: DType -> DType
simplifyDType (DForallT _ _ t) = simplifyDType t
simplifyDType (DSigT t _)      = simplifyDType t
simplifyDType (DAppT l r)      = DAppT (simplifyDType l) (simplifyDType r)
simplifyDType t                = t

-- | Compare DTypes for equality
(.==.) :: DType -> DType -> Bool
t1 .==. t2 = simplifyDType t1 == simplifyDType t2

-- | Split a function type into its parameters and return type
splitSignature :: DType -> [DType]
splitSignature (DArrowT `DAppT` l `DAppT` r) = l : splitSignature r
splitSignature (DForallT _ _ t)              = splitSignature t
splitSignature (DSigT t _)                   = splitSignature t
splitSignature t                             = [t]

returnType :: DType -> DType
returnType = last . splitSignature

argTypes :: DType -> [DType]
argTypes = init . splitSignature

-- | Split a type on a head constructor and its parameters
unapply :: DType -> (Name, [DType])
unapply (DConT name) = (name, [])
unapply (DVarT name) = (name, [])
unapply (DForallT _ _ t) = unapply t
unapply (DSigT t _) = unapply t
unapply (DAppT l r) = (name, l' ++ [r])
  where (name, l') = unapply l
unapply t = unsupported 'unapply t

typeHead :: DType -> Name
typeHead = fst . unapply

typeArgs :: DType -> [DType]
typeArgs = snd . unapply

-- | How many times a type occurs within another
occurrences :: Name -> DType -> Int
occurrences t t' | t == typeHead t' = 1
occurrences t (DAppT t1 t2)     = occurrences t t1 + occurrences t t2
occurrences t (DSigT t' _)      = occurrences t t'
occurrences t (DForallT _ _ t') = occurrences t t'
occurrences _ _                 = 0

-- | Is this type a list of things?
isListOf :: DType -> Maybe DType
isListOf (DConT f `DAppT` a) | f == ''[] = Just a
isListOf _                               = Nothing

-- | Is this the String type?
isStringType :: DType -> Bool
isStringType ty = ty .==. (DConT ''[] `DAppT` DConT ''Char)


----------------------------------------
-- | Observations over DCons

dConName :: DCon -> Name
dConName (DCon _ _ name _ _) = name

dConFields :: DCon -> DConFields
dConFields (DCon _ _ _ conFields _) = conFields

dConFieldsTypes :: DConFields -> [DType]
dConFieldsTypes (DNormalC _ bts) = map snd bts
dConFieldsTypes (DRecC bts)      = map (\(_,_,t) -> t) bts

dConFieldsNum :: DConFields -> Int
dConFieldsNum (DNormalC _ bts) = length bts
dConFieldsNum (DRecC bts)      = length bts

-- | Is a construction terminal?
-- We assume that if it contains a field naming any type from the mutually
-- recursive family of types, then it is not.
isTerminal :: [Name] -> [DType] -> Bool
isTerminal typeFam types
  -- = not (any ((`nameOccursIn` types)) typeFam)
  = sum (branchingFactor typeFam types) == 0


-- | The branching factor of a list of types to members of a mutually recursive
-- family of types. Some special cases happen here. You have been warned!
branchingFactor :: [Name] -> [DType] -> [Int]
branchingFactor typeFam types
  = branches types <$> typeFam
  where
    branches fields target = sum (factor target <$> fields)

    factor target (DAppT (DConT f) t)
      | f == ''[]
      = listBF * (factor target t)
    factor target ty
      | typeHead ty == target = 1
      | otherwise             = 0

----------------------------------------
-- | Observations over DPats

-- | Collect the constructors frequencies of a pattern
collectPatCons :: DPat -> [(Name, Int)]
collectPatCons = fmap (head &&& length) . group . sort . go
  where
    go (DConPa cn pats) = cn : concatMap go pats
    go (DTildePa p)     = go p
    go (DBangPa p)      = go p
    go (DSigPa p _)     = go p
    go _                = []

----------------------------------------
-- | Transformations

-- | Replace a given type with a type var within a type
replaceTyForTV :: DType -> DTyVarBndr -> DType -> DType
replaceTyForTV target tv ty | ty .==. target
  = dTyVarBndrToDType tv
replaceTyForTV target tv (DAppT l r)
  = DAppT (replaceTyForTV target tv l) (replaceTyForTV target tv r)
replaceTyForTV target tv (DSigT ty kind)
  = DSigT (replaceTyForTV target tv ty) kind
replaceTyForTV _  _ fa@(DForallT _ _ _)
  = unsupported 'replaceTyForTV (show fa)
replaceTyForTV _  _  ty = ty

-- | Drop every pattern that is a wildcard, a variable, or is after one of those
dropTrivialPats :: [DPat] -> [DPat]
dropTrivialPats [] = []
dropTrivialPats (DVarPa _ : _) = []
dropTrivialPats (DWildPa  : _) = []
dropTrivialPats (p : ps) = p : dropTrivialPats ps

-- | Transform a pattern into an expression using a list of variables names for
-- the pattern variables
dPatToDExpWithVars :: [Name] -> DPat -> DExp
dPatToDExpWithVars vars = fst . go vars
  where
    go vs (DLitPa l) = (DLitE l, vs)
    go vs (DVarPa _) = (DVarE (head vs), tail vs)
    go vs (DConPa cn pats) = (applyDExp (DConE cn) pats', vs')
      where (pats', vs') = mapListDPatsToDExp (pats, vs)
    go vs (DTildePa pat) = go vs pat
    go vs (DBangPa pat) = go vs pat
    go vs (DSigPa pat kind) = (DSigE pat' kind, vs')
      where (pat', vs') = go vs pat
    go vs DWildPa = (DVarE (head vs), tail vs)

    mapListDPatsToDExp :: ([DPat], [Name]) -> ([DExp], [Name])
    mapListDPatsToDExp ([], vs) = ([], vs)
    mapListDPatsToDExp (p:ps, vs) = (p':ps', vs'')
      where (p', vs') = go vs p
            (ps', vs'') = mapListDPatsToDExp (ps, vs')


----------------------------------------
-- | Pure builders

-- | Apply a list of types to a head type constructor
applyDTypes, (<<#) :: Name -> [DType] -> DType
applyDTypes tn ts = DConT tn `applyDType` ts
(<<#) = applyDTypes

-- | Apply a list of type vars to a head constructor
applyTVs, (<<*) :: Name -> [DTyVarBndr] -> DType
applyTVs tn vs = applyDTypes tn (map dTyVarBndrToDType vs)
(<<*) = applyTVs

-- | Build an applicative expression by chaining `<*>`
thApplicativeExp :: Name -> [DExp] -> DExp
thApplicativeExp headName exps = foldl appExp pureCon exps
  where pureCon = DVarE 'pure `DAppE` DConE headName
        appExp l r = DVarE '(<*>) `DAppE` l `DAppE` r

-- | Build a list expression by chaining `(:)`
thListExp :: [DExp] -> DExp
thListExp exps = foldr consExp nilExp exps
  where nilExp = DConE '[]
        consExp l r = DConE '(:) `DAppE` l `DAppE` r


thStrTyLit :: String -> DType
thStrTyLit = DLitT . StrTyLit

thNumTyLit :: Int -> DType
thNumTyLit = DLitT . NumTyLit . fromIntegral

thNameTyLit :: Name -> DType
thNameTyLit = thStrTyLit . nameBase

----------------------------------------
-- | Impure builders (over Q)

-- | Create a new recursive variable
newRecVar :: Q DTyVarBndr
newRecVar = DPlainTV <$> newName "r"

-- | Create an infinite source of variable names
newPatVars :: Int -> Q [Name]
newPatVars n = replicateM n (newName "v")

-- | Create a pattern variable which doesn't emit an unused warning
newName_ :: String -> Q Name
newName_ str = newName ("_" ++ str)

-- | Create the appropriate generator for a constructor field based on its type
-- and the instances in the current environment
mkBoundedGen :: [Name] -> DType -> Name -> Name -> DType -> Q DExp
mkBoundedGen typeFam target gen_ depth_ fieldType
  = dsExp =<< mkGen fieldType
  where
    mkGen ty
      -- The field is self recursive:
      -- We use the reference to the recursive generator
      | ty .==. target
      = [e| $(varE gen_) (max 0 ($(varE depth_) - 1)) |]

      -- The field is mutually recursive:
      -- We call to its BoundedArbitrary instance
      | typeHead ty `elem` typeFam
      = [e| BoundedArb.boundedArbitrary (max 0 ($(varE depth_) - 1)) |]

      -- Some special cases in between:
      -- ^ Strings
      | isStringType ty
      = [e| genString |]

      | Just a <- isListOf ty
      = [e| genList $(mkGen a) |]

      -- ^ Types of kind `* -> *`
      | (DConT f `DAppT` a) <- ty
      = ifM (isInstance ''QC.Arbitrary1 [ConT f])
        [e| QC.liftArbitrary $(mkGen a) |]
        [e| QC.arbitrary |]

      -- ^ Types of kind `* -> * -> *`
      | (DConT f `DAppT` t1 `DAppT` t2) <- ty
      = ifM (isInstance ''QC.Arbitrary2 [ConT f])
        [e| QC.liftArbitrary2 $(mkGen t1) $(mkGen t2) |]
        [e| QC.arbitrary |]

      -- The field type is something else:
      -- Hope for it having an Arbitrary instance
      | otherwise
      = [e| QC.arbitrary |]


listBF :: Int
listBF = 5

genString :: QC.Gen String
genString = QC.resize (listBF * 5) (QC.listOf1 chars)
  where chars = QC.elements [' ' .. '~']

genList :: QC.Gen a -> QC.Gen [a]
genList = customListGen (listBF * 2)
  where
    customListGen n gen = do
      n' <- QC.choose (0, n)
      QC.vectorOf n' gen


----------------------------------------
-- Construct TH stuff using borrowed names

thSome :: Int -> DType -> DType
thSome n = DAppT (DConT (mkName ("Some" ++ show n)))

thSum :: DType -> DType -> DType
thSum t1 t2 = ''Rep.Sum <<# [t1, t2]

thCon :: DType -> DType
thCon = DAppT (DConT ''Rep.Con)

thFun :: DType -> DType
thFun = DAppT (DConT ''Rep.Fun)

thPat :: DType -> Integer -> DType
thPat p n = DAppT (DAppT (DConT ''Rep.Pat) p) (DLitT (NumTyLit n))

thTerm :: DType -> DType
thTerm = DAppT (DConT ''Rep.Term)

thSingleton :: DExp -> DExp
thSingleton = DAppE (DVarE 'Vector.singleton)

thVector :: [DExp] -> DExp
thVector xs = DVarE 'Vector.fromList `DAppE` thListExp xs

thVector2 :: [[DExp]] -> DExp
thVector2 xss = DVarE 'Vector.fromList `DAppE` thListExp (thVector <$> xss)

thString :: String -> DExp
thString = DLitE . StringL

thRational :: Rational -> DExp
thRational n = DLitE (RationalL n)

thTrue, thFalse :: DExp
thTrue = DConE 'True
thFalse = DConE 'False

derivingClauses :: Bool -> [DDerivClause]
derivingClauses branching
  = [ DDerivClause Nothing $
      (if branching then [DConPr ''Generics.Generic] else [])
      ++ [ DConPr ''Show, DConPr ''Functor ]
    ]

----------------------------------------
-- Name manipulations

toValidIdent :: String -> String -> String
toValidIdent prefix str = prefix ++ "_" ++ foldr translate [] str
  where
    translate c rest = maybe [c] ('_':) (lookup c table) ++ rest
    table =
      [ ('!', "bang")
      , ('#', "hash")
      , ('$', "dollar")
      , ('%', "percent")
      , ('&', "amp")
      , ('*', "ast")
      , ('+', "plus")
      , ('.', "dot")
      , ('/', "slash")
      , ('<', "langle")
      , ('=', "equal")
      , ('>', "rangle")
      , ('?', "question")
      , ('@', "as")
      , ('^', "caret")
      , ('|', "pipe")
      , ('-', "dash")
      , ('~', "tilde")
      , (':', "colon")
      , ('\\', "backslash")
      ]

----------------------------------------
-- | Other utilities

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

(<$$>):: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
(<$$>) f xss = fmap f <$> xss
infix 8 <$$>

----------------------------------------
-- | Error and warning messages

-- | Internal errors
unsupported :: Show a => Name -> a -> b
unsupported funName input
  = error $ "[DRAGEN]" ++ show funName ++ ": unsupported input:\n" ++ show input


instance {-# OVERLAPPING #-} Ppr String where
  ppr = pprString

dump :: Ppr a => a -> String
dump = pprint

withColor :: Color -> IO () -> IO ()
withColor color io
  = setSGR [SetColor Foreground Vivid color] >> io >> setSGR [Reset]

dragenLog :: String -> IO ()
dragenLog str = putStrLn $ "[DRAGEN] " ++ str

dragenLog' :: String -> IO ()
dragenLog' str = putStrLn str

dragenMsg :: Ppr a => String -> [a] -> Q ()
dragenMsg msg inputs = runIO $ do
#ifdef DEBUG
  withColor Green $ do
    dragenLog msg
  forM_ inputs $ \i -> do
    mapM_ dragenLog' (lines (dump i))
#else
  return ()
#endif

dragenMsg' :: String -> Q ()
dragenMsg' msg = dragenMsg msg ([] :: [String])

dragenWarning :: Ppr a => String -> [a] -> Q ()
dragenWarning msg inputs = runIO $ do
  withColor Yellow $ do
    dragenLog msg
    forM_ inputs $ \i -> do
      mapM_ dragenLog' (lines (dump i))

dragenError :: Show a => String -> [a] -> Q b
dragenError msg inputs = runIO $ do
  withColor Red $ do
    dragenLog "an error happened:"
    dragenLog msg
    dragenLog "input was:"
    forM_ inputs $ \i -> do
      mapM_ dragenLog' (lines (show i))

  error "DRAGEN derivation error"

dragenHeader :: Name -> Q ()
dragenHeader method = do
  dragenMsg' "-----------------------------"
  dragenMsg' "DRAGEN 0.1.0.0"
  dragenMsg' ("method: " ++ pprint method)

dragenFooter :: Q ()
dragenFooter = do
  dragenMsg' "done!"
  dragenMsg' "-----------------------------"

dragen :: Name -> Q a -> Q a
dragen method action = do
  dragenHeader method
  a <- action
  dragenFooter
  return a
