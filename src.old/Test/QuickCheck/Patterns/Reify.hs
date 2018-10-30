{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}

module Test.QuickCheck.Patterns.Reify where

import Data.List
import Control.Monad.Extra

import Language.Haskell.TH hiding (Con)
import qualified Language.Haskell.TH as TH

import Test.QuickCheck.Patterns.Types


-- Given a type name, extracts its information and the information of the types
-- involved with it from the compiling environment. This functions performs a
-- reachability analysis, looking for mutually recursive type definitions, and
-- marks the _rec_ field of each type constructor accordingly.
-- IMPORTANT: This function should be called with non-parametric (kind ~ *)
-- type names, since we can not resolve the implicit type vars. To reify fully
-- instantiated parametric types, first define a non-parametric type synonym of
-- the target (e.g. type MaybeInt = Maybe Int), or use _reifyTyEnv_ instead.
reifyNameEnv :: Name -> Q TyEnv
reifyNameEnv = reifyName >=> reifyInvolvedTyDecs

-- Similar to _reifyTyEnv_, but allows us to reify parametric type
-- definitions without needing to define an ad-hoc non-parametric type synonym.
-- E.g. reifyNameEnv ''MaybeInt == reifyTyEnv (Base ''Maybe `App` Base ''Int)
reifyTyEnv :: Ty -> Q TyEnv
reifyTyEnv = reifyTy >=> reifyInvolvedTyDecs



-- Given a type name, extracts its information from the compiling environment.
-- Note this function does not mark the type constructors as mutually recursive
-- if they are mutually recursive with any other type.
-- IMPORTANT: This function should be called with non-parametric (kind ~ *)
--            type names, since we cannot resolve implicit type vars.
reifyName :: Name -> Q TyDec
reifyName = reifyTy . TC


-- Given a type, reifies the leftmost type constructor, and instantiates its
-- type vars with the types applied to the original type.
-- E.g.  reifyTy (Base ''Maybe `App` Base ''Int)
--       ===>
--       TyDec { tsig = App (Base ''Maybe) (Base ''Int)
--             , tcons = [ Con { cname = 'Nothing, ... }
--                       , Con { cname = 'Just, cargs = [Base ''Int], ...} ]
--             , ... }
reifyTy :: Ty -> Q TyDec
reifyTy this = do

  let isPrimTy PrimTyConI {} = True
      isPrimTy _ = False

  let (name, args) = unapply this
  reify name >>= \case

    {- data T {...} = C1 {...} | C2 {...} | ... -}
    TyConI (DataD _ _ vars _ cons _) -> do
      let vars' = map extractTVar vars
          binds = zip vars' args
          cons' = map (extractCon binds this) cons
          fields = concatMap (concatMap flatten . cargs) cons'
          emptyCon = Con { cname = name, cargs = [], isRec = False }

      ifM (any isPrimTy <$> mapM reify fields)
        (pure TyDec { tsig = apply name [], tcons = [emptyCon], isPrim = True })
        (pure TyDec { tsig = this, tcons = cons', isPrim = False })

    {- newtype T {...} = Con T' -}
    TyConI (NewtypeD _ _ vars _ con _ ) -> do
      let vars' = map extractTVar vars
          binds = zip vars' args
          con' = extractCon binds this con
          fields = concatMap flatten (cargs con')
          emptyCon = Con { cname = name, cargs = [], isRec = False }

      ifM (any isPrimTy <$> mapM reify fields)
        (pure TyDec { tsig = apply name [], tcons = [emptyCon], isPrim = True })
        (pure TyDec { tsig = this, tcons = [con'], isPrim = False })

    {- type T {...} = U {...} -}
    TyConI (TySynD _ vars ty) -> do
      let vars'  = map extractTVar vars
          binds  = zip vars' args
          realTy = instantiate binds (extractTy ty)
      realDef <- reifyTy realTy
      return realDef { tsig = this }

    {- Int#, Bool#, ...  -}
    PrimTyConI {} -> return
        TyDec { tsig = apply name [], tcons = [], isPrim = True }

    {- Not supported yet. -}
    x -> unsupported "reifyTy" x


extractTVar :: TyVarBndr -> Name
extractTVar (PlainTV tv) = tv
extractTVar (KindedTV tv _) = tv

extractCon :: [(Name, Ty)] -> Ty -> TH.Con -> Con
extractCon binds this (NormalC cn cas)
  = Con { cname = cn, cargs = args, isRec = this `elem` args }
  where args = map (instantiate binds . extractTy . snd) cas
extractCon binds this (InfixC lt op rt)
  = Con { cname = op, cargs = args, isRec = this `elem` args }
  where args = map (instantiate binds . extractTy . snd) [lt,rt]
extractCon binds this (RecC cn vbts)
  = Con { cname = cn, cargs = args, isRec = this `elem` args }
  where args = map (instantiate binds . extractTy . (\(_,_,x) -> x)) vbts
extractCon _ _ x = unsupported "extractCon" x

extractTy :: TH.Type -> Ty
extractTy (ForallT _ [] ty) = extractTy ty
extractTy (AppT (AppT ArrowT a) b) = extractTy a :-> extractTy b
extractTy (AppT t1 t2) = extractTy t1 :@ extractTy t2
extractTy (ConT nm) = TC nm
extractTy (VarT nm) = TV nm
extractTy (TupleT s) = TC (TH.tupleTypeName s)
extractTy ListT = TC ''[]
extractTy x = unsupported "extractTy" x

instantiate :: [(Name, Ty)] -> Ty -> Ty
instantiate _     (TC name) = TC name
instantiate binds (TV v) = maybe (TV v) id (lookup v binds)
instantiate binds (l :@ r) = instantiate binds l :@ instantiate binds r
instantiate binds (l :-> r) = instantiate binds l :-> instantiate binds r


-- Traverse a data type definition, extracting recursively every data type
-- reachable from the root data type. This function also calculates mutually
-- recursive dependencies in type constructors and updates its `rec` field
-- accordingly.
reifyInvolvedTyDecs :: TyDec -> Q TyEnv
reifyInvolvedTyDecs root = addMutRecLoops <$> reifyInvolvedTys' [root] root
  where
    reifyInvolvedTys' _ this | isPrim this = return [this]
    reifyInvolvedTys' visited this = do
      let newTys = involvedWith this \\ map tsig visited
      newTyDecs <- mapM reifyTy newTys
      newReached <- mapM (reifyInvolvedTys' (this:visited)) newTyDecs
      return (nub (this : concat newReached))


-- Calculate if any type constructor is mutually recursive and update the
-- `isRec` field accordingly.
addMutRecLoops :: TyEnv -> TyEnv
addMutRecLoops env = map (addMutRecLoop env) env
  where
    addMutRecLoop env' this
      = this { tcons = map (setIsRecursive env' (tsig this)) (tcons this) }

    setIsRecursive env' this con
      | isRec con = con
      | reachableFrom env' this con = con { isRec = True }
      | otherwise = con

    reachableFrom env' this con = any (reachableFrom' env' this []) (cargs con)

    reachableFrom' env' this visited arg
      | this `isSubtype` arg  = True
      | any (this `isSubtype`) argImmDefs = True
      | otherwise = any (reachableFrom' env' this (arg:visited)) nextArgs
      where
        argDef = find ((==arg) . tsig) env'
        argImmDefs = maybe [] involvedWith argDef
        nextArgs = maybe [] (\def -> involvedWith def \\ visited) argDef
        -- ToDo: look why some definitions are not in the env sometimes.
        -- Just nextArgs = involvedWith argDef \\ visited


reifyFunc :: Name -> Q (Name, Ty)
reifyFunc f = reify f >>= \case
  VarI fname ftype _ -> return (fname, extractTy ftype)
  _ -> error $ "reifyFunc: name " ++ show f
       ++ " does not correspond to a valid function identifier"
