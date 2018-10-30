{-# LANGUAGE TemplateHaskell #-}
module Test.QuickCheck.Patterns.TH where

import System.Directory
import System.FilePath
import Control.Monad.IO.Class
import Language.Haskell.TH hiding (Con)

import Test.QuickCheck.Patterns.Types
import Test.QuickCheck.Patterns.Reify
import Test.QuickCheck.Patterns.Extract


runTH :: Name -> [Name] -> DecsQ
runTH tname fnames = decorate $ do

  path <- current_file
  putStrLnQ $ "\n*** Current file:"
  putStrLnQ $ path

  env <- reifyNameEnv tname
  putStrLnQ $ "*** Type environment:"
  mapM_ (putStrLnQ . ("--- "++) . show) env

  fsigs <- mapM reifyFunc fnames
  fpats <- liftIO $ mapM (extractFunMatchs path) fnames
  let mkFunDef (fn, ft) pats = FunDef fn ft pats
      fdefs = zipWith mkFunDef fsigs fpats
  putStrLnQ $ "\n*** Function definitions:"
  mapM_ (putStrLnQ . ("--- "++) . show) fdefs

  pf <- derivePF env tname

  return [pf]


derivePF :: TyEnv -> Name -> DecQ
derivePF env tname = do
  let tdec = findTyDec tname env
  tv <- newName "t"
  dataD
    (cxt [])
    (mkPFName tname)
    [plainTV tv]
    Nothing
    (map (derivePFCon env tname) (tcons tdec))
    -- [derivClause Nothing [conT ''Functor]]
    []

derivePFCon :: TyEnv -> Name -> Con -> ConQ
derivePFCon env tname con = normalC (mkPFName (cname con)) []


current_file :: Q FilePath
current_file = do
  dir <- runIO getCurrentDirectory
  file <- loc_filename <$> location
  return (dir </> file)

putStrLnQ :: String -> Q ()
putStrLnQ = liftIO . putStrLn

qq :: Name -> ExpQ
qq n = reify n >>= stringE . show

decorate :: Q a -> Q a
decorate action = do
  putStrLnQ "\n=== Template Haskell begin ==="
  res <- action
  putStrLnQ "===  Template Haskell end  ===\n"
  return res

mkPFName tn = mkName (nameBase tn ++ "F")
