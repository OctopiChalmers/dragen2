{-# LANGUAGE LambdaCase #-}
module Test.QuickCheck.Patterns.Extract where

import Language.Haskell.TH (Name, nameBase, mkName)
import Language.Haskell.Exts hiding (Name)

import Test.QuickCheck.Patterns.Types

exts :: [Extension]
exts = [ EnableExtension DeriveFunctor
       , EnableExtension TypeOperators
       , EnableExtension TypeFamilies
       , EnableExtension DataKinds
       , EnableExtension MultiParamTypeClasses
       ]

extractFunMatchs :: FilePath -> Name -> IO [ClausePat]
extractFunMatchs path fun = parseFileWithExts exts path >>= \case
  ParseOk (Module _ _ _ _ decs) -> do
    let srcDefs = concat (foldr extractFunBinds [] decs)
        funDefs = filter matchName srcDefs

        extractFunBinds (FunBind _ ms) = (ms:)
        extractFunBinds _ = id

        matchName (Match      _ n _ _ _)   = prettyPrint n == nameBase fun
        matchName (InfixMatch _ _ n _ _ _) = prettyPrint n == nameBase fun

    return (map toClausePat funDefs)

  err -> error $ "extractFunMatchs: unable to parse module "
         ++ show path ++ "\n"
         ++ show err


toClausePat :: Match l -> ClausePat
toClausePat (Match _ _ pats _ _) = ClausePat (map toPattern pats)
toClausePat (InfixMatch _ p _ ps _ _) = ClausePat (toPattern p : map toPattern ps)

toTHName :: Pretty a => a -> Name
toTHName = mkName . prettyPrint

toPattern :: Pat l -> Pattern
toPattern (PVar _ _) = AnyP
toPattern (PWildCard _) = AnyP
toPattern (PLit _ sign l) = LitP (fromLiteral l sign)
toPattern (PApp _ qn ps) = ConP (toTHName qn) (map toPattern ps)
toPattern (PParen _ pat) = ParenP (toPattern pat)
toPattern p = unsupported "toPattern" (prettyPrint p)

fromLiteral :: Literal l -> Sign l -> LitP
fromLiteral (Char _ c _)     _            = CharL c
fromLiteral (String _ str _) _            = StringL str
fromLiteral (Int _ n _)      (Negative _) = IntL (-n)
fromLiteral (Int _ n _)      _            = IntL n
fromLiteral (Frac _ f _)     (Negative _) = FloatL (-f)
fromLiteral (Frac _ f _)     _            = FloatL f
fromLiteral l _ = unsupported "fromLiteral" (prettyPrint l)
