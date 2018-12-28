{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}

module Test.QuickCheck.HRep.TH.Common where

import Data.Char
import Data.List

import System.Directory
import System.FilePath

import Control.Arrow
import Control.Monad.IO.Class
import Control.Monad.Extra

import Language.Haskell.TH
import Language.Haskell.TH.Desugar

import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Gen.Utils as QC
import qualified Test.QuickCheck.HRep as HRep
import qualified Test.QuickCheck.Branching as Branching

import qualified GHC.Generics as Generics
import qualified Data.Vector as Vector


-- | Derive "syntactic" equivalence relations for DTypes
deriving instance Eq DTyVarBndr
deriving instance Eq DPred
deriving instance Eq DType
deriving instance Eq DCon
deriving instance Eq DConFields

----------------------------------------
-- | Derive a generator for a possibly composite type.
-- Use Arbitrary1 and Arbitrary2 instancies to lift it
-- whenever possible.
deriveGen :: DExp -> DType -> DType -> Q DExp
deriveGen gen target ty = mkGen ty
  where mkGen t | t == target
          = pure (smallerTH gen)
        mkGen (DAppT (DAppT (DConT f) t1) t2)
          = ifM (isInstance ''QC.Arbitrary2 [ConT f])
                   (liftArbitrary2TH
                    <$> (smallerTH <$> mkGen t1)
                    <*> (smallerTH <$> mkGen t2))
            (pure (smallerTH arbitraryTH))
        mkGen (DAppT (DConT f) t)
          = ifM (isInstance ''QC.Arbitrary1 [ConT f])
            (liftArbitraryTH
             <$> (smallerTH <$> mkGen t))
            (pure (smallerTH arbitraryTH))
        mkGen _ = pure (smallerTH arbitraryTH)

-- | Compare DTypes for equality
(.==.) :: DType -> DType -> Bool
t1 .==. t2 = simplifyDType t1 == simplifyDType t2

simplifyDType :: DType -> DType
simplifyDType (DForallT _ _ t) = simplifyDType t
simplifyDType (DSigT t _) = simplifyDType t
simplifyDType (DAppT l r) = DAppT (simplifyDType l) (simplifyDType r)
simplifyDType t = t

-- | How many times a type occurs within another
occurrences :: DType -> DType -> Integer
occurrences t t' | t == t' = 1
occurrences t (DAppT t1 t2) = occurrences t t1 + occurrences t t2
occurrences t (DSigT t' _) = occurrences t t'
occurrences t (DForallT _ _ t') = occurrences t t'
occurrences _ _ = 0

occursIn :: DType -> DType -> Bool
occursIn ty ty' = occurrences ty ty' > 0

occursInTypes :: DType -> [DType] -> Bool
occursInTypes ty tys = any ((0 <) . occurrences ty) tys

occursInFields :: DType -> DConFields -> Bool
occursInFields ty conFields = ty `occursInTypes` dConFieldsTypes conFields

isTerminalDCon :: [Name] -> DCon -> Bool
isTerminalDCon tyFam (DCon _ _ _ conFields _)
  = not (any ((`nameOccursIn` conFields)) tyFam)

branchesToFam :: [Name] -> DCon -> Int
branchesToFam tyFam (DCon _ _ _ conFields _)
  = sum (branches . tyHead <$> dConFieldsTypes conFields)
  where branches cn | any (cn ==) tyFam = 1
                    | otherwise         = 0



-- | Extract information from constructors
dConName :: DCon -> Name
dConName (DCon _ _ n _ _) = n

dConFieldsTypes :: DConFields -> [DType]
dConFieldsTypes (DNormalC _ bts) = map snd bts
dConFieldsTypes (DRecC bts)      = map (\(_,_,t) -> t) bts

dConFieldsNr :: DConFields -> Int
dConFieldsNr (DNormalC _ bts) = length bts
dConFieldsNr (DRecC bts)      = length bts

-- | Transform a pattern into an expression using 'patVars for variable patterns
dPatToDExpWithVars :: DPat -> DExp
dPatToDExpWithVars = fst . go varNames
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

-- | Drop every pattern that is a wildcard, a variable, or is after one of those
dropTrivialPats :: [DPat] -> [DPat]
dropTrivialPats [] = []
dropTrivialPats (DVarPa _ : _) = []
dropTrivialPats (DWildPa  : _) = []
dropTrivialPats (p : ps) = p : dropTrivialPats ps

-- | Collect the constructors frequencies of a pattern
collectPatCons :: DPat -> [(Name, Int)]
collectPatCons = fmap (head &&& length) . group . sort . go
  where
    go (DConPa cn pats) = cn : concatMap go pats
    go (DTildePa p)     = go p
    go (DBangPa p)      = go p
    go (DSigPa p _)     = go p
    go _                = []

-- | Build an applicative expression by chaining `<*>`
mkAppExp :: Name -> [DExp] -> DExp
mkAppExp conName conFields = foldl appExp pureCon conFields
  where pureCon = DVarE 'pure .: DConE conName
        appExp l r = DVarE '(<*>) .: l .: r

-- | Build an applicative expression by chaining `<*>`
mkListExp :: [DExp] -> DExp
mkListExp exps = foldr consExp nilExp exps
  where nilExp = DConE '[]
        consExp l r = DConE '(:) .: l .: r

-- | An infinite source of variable names
varNames :: [Name]
varNames = mkName . ("v"++) . show <$> [1 :: Integer ..]

mkRecVar :: Q DTyVarBndr
mkRecVar = DPlainTV <$> newName "self"

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

-- | Split a type on a head constructor and its parameters
unapply :: DType -> (Name, [DType])
unapply (DConT name) = (name, [])
unapply (DVarT name) = (name, [])
unapply (DForallT _ _ t) = unapply t
unapply (DSigT t _) = unapply t
unapply (DAppT l r) = (name, l' ++ [r])
  where (name, l') = unapply l
unapply t = unsupported 'unapply t

tyHead :: DType -> Name
tyHead = fst . unapply

tyArgs :: DType -> [DType]
tyArgs = snd . unapply

-- | Split a function type into its parameters and return type
splitSignature :: DType -> [DType]
splitSignature (DAppT (DAppT DArrowT l) r) = l : splitSignature r
splitSignature (DForallT _ _ t) = splitSignature t
splitSignature (DSigT t _) = splitSignature t
splitSignature t = [t]

retType :: DType -> DType
retType = last . splitSignature


-- | Apply a list of types to a head constructor
apply, (<<|) :: Name -> [DType] -> DType
apply tn ts = DConT tn `applyDType` ts
(<<|) = apply

-- | Apply a list of type vars to a head constructor
applyWithTVs, (<<*) :: Name -> [DTyVarBndr] -> DType
applyWithTVs tn vs = apply tn (map dTyVarBndrToDType vs)
(<<*) = applyWithTVs

-- | Infix alias for DAppE
(.:) :: DExp -> DExp -> DExp
(.:) = DAppE

infixl .:

----------------------------------------

getConNames :: Name -> Q [Name]
getConNames tyName = do
  (vs, cons) <- getDataD mempty tyName
  tyVars <- mapM desugar vs
  let ty = simplifyDType (tyName <<* tyVars)
  ogCons <- concatMapM (dsCon tyVars ty) cons
  let projName (DCon _ _ cn _ _) = cn
  return (projName <$> ogCons)

getFamConNames :: [Name] -> Q [[Name]]
getFamConNames tyFam = mapM getConNames tyFam

currentFile :: Q FilePath
currentFile = do
  dir  <- liftIO getCurrentDirectory
  file <- location
  return (dir </> loc_filename file)

reifyOrFail :: Name -> Q DInfo
reifyOrFail n = dsReify n >>= maybe err expand
  where err = error ("dsReify: error while reifiying " ++ show n)

putStrLnQ :: String -> Q ()
putStrLnQ = liftIO . putStrLn

unsupported :: Show t => Name -> t -> a
unsupported funName input
  = error $ show funName ++ ": unsupported input\n" ++ show input

debugQ :: Show a => a -> Q ()
debugQ v = do
  putStrLnQ "\n=== Debug ==="
  putStrLnQ (show v)
  putStrLnQ "=== Debug ==="

qq :: Show a => Q a -> Q Exp
qq a = a >>= return . sweeten . DLitE . StringL . show

dumpTHInfo :: Name -> Q [Dec]
dumpTHInfo nm = dsReify nm >>=
  \(Just (DTyConI (DTySynD _ _ ty) _)) -> expandType ty >>=
  \dsTy -> [d| infoTH_ = $(stringE (show dsTy)) |]

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

toIdentStr :: String -> String
toIdentStr = fmap (\c -> if isAlphaNum c then c else '_')

----------------------------------------
-- | Borrowed names

someTH :: Int -> DType -> DType
someTH n = DAppT (DConT (mkName ("Some" ++ show n)))

smallerTH :: DExp -> DExp
smallerTH = DAppE (DVarE 'QC.smaller)

reduceTH :: Integer -> DExp -> DExp
reduceTH n = DAppE (DAppE (DVarE 'QC.reduce) (DLitE (IntegerL n)))

liftArbitraryTH :: DExp -> DExp
liftArbitraryTH = DAppE (DVarE 'QC.liftArbitrary)

liftArbitrary2TH :: DExp -> DExp -> DExp
liftArbitrary2TH e1 e2 = DVarE 'QC.liftArbitrary2 .: e1 .: e2

mkSumType :: DType -> DType -> DType
mkSumType t1 t2 = ''HRep.Sum <<| [t1, t2]

arbitraryTH :: DExp
arbitraryTH = DVarE 'QC.arbitrary

satisfyTH :: String -> DExp
satisfyTH str = DVarE 'QC.satisfy .: DLitE (StringL str)

stepTH :: DExp
stepTH = DVarE 'HRep.step

singletonTH :: DExp -> DExp
singletonTH = DAppE (DVarE 'Vector.singleton)

vectorTH :: [DExp] -> DExp
vectorTH xs = DVarE 'Vector.fromList .: mkListExp xs

vector2TH :: [[DExp]] -> DExp
vector2TH xxs = DVarE 'Vector.fromList .: mkListExp (vectorTH <$> xxs)

stringLit :: String -> DExp
stringLit = DLitE . StringL

intLit :: Int -> DExp
intLit = DLitE . IntegerL . fromIntegral

branchingFunNames :: [Name]
branchingFunNames = [ 'Branching.typeNames
                    , 'Branching.typeAtomic
                    , 'Branching.typeProbs
                    , 'Branching.typeProbs'
                    , 'Branching.typeBeta
                    , 'Branching.typeEta
                    ]

derivingClauses :: [DDerivClause]
derivingClauses = [DDerivClause Nothing
                    [ DConPr ''Functor
                    , DConPr ''Show
                    , DConPr ''Generics.Generic
                    ]]
