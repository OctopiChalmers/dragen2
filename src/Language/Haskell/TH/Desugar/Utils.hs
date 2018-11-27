{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}

module Language.Haskell.TH.Desugar.Utils where

import Data.Char

import Control.Monad.IO.Class

import Language.Haskell.TH
import Language.Haskell.TH.Desugar

import System.Directory
import System.FilePath


-- | Derive "syntactic" equivalence relations for DTypes
deriving instance Eq DTyVarBndr
deriving instance Eq DPred
deriving instance Eq DType

-- | Compare DTypes for equality
(.==.) :: DType -> DType -> Bool
t1 .==. t2 = simplifyDType t1 == simplifyDType t2

simplifyDType :: DType -> DType
simplifyDType (DForallT _ _ t) = simplifyDType t
simplifyDType (DSigT t _) = simplifyDType t
simplifyDType (DAppT l r) = DAppT (simplifyDType l) (simplifyDType r)
simplifyDType t = t

-- | How many times a type occurs within another
branchFactor :: DType -> DType -> Integer
branchFactor t t' | t == t' = 1
branchFactor t (DAppT t1 t2) = branchFactor t t1 + branchFactor t t2
branchFactor t (DSigT t' _) = branchFactor t t'
branchFactor t (DForallT _ _ t') = branchFactor t t'
branchFactor _ _ = 0

occursIn :: DType -> DType -> Bool
occursIn ty ty' = branchFactor ty ty' > 0

occursInTypes :: DType -> [DType] -> Bool
occursInTypes ty tys = any ((0 <) . branchFactor ty) tys

occursInFields :: DType -> DConFields -> Bool
occursInFields ty conFields = ty `occursInTypes` dConFieldsTypes conFields

isTerminalDCon :: DType -> DCon -> Bool
isTerminalDCon ty (DCon _ _ _ conFields _) = ty `occursInFields` conFields

-- | Extract information from constructors
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

-- | Build an applicative expression by chaining `<*>`
mkAppExp :: Name -> [DExp] -> DExp
mkAppExp conName conFields = foldl app_exp pure_con conFields
  where pure_con = DVarE 'pure .: DConE conName
        app_exp l r = DVarE '(<*>) .: l .: r

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

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

toIdentStr :: String -> String
toIdentStr = fmap (\c -> if isAlphaNum c then c else '_')
