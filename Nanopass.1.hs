{-# LANGUAGE TemplateHaskell, LambdaCase, TupleSections, ParallelListComp #-}
module Nanopass where

import Control.Applicative
import Data.Maybe (fromJust)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax hiding (lift)

import Control.Monad.State
import qualified Data.Map as M

import Debug.Trace
import Data.List
import Data.Maybe

trd3 (_, _, x) = x

conName :: Con -> Name
conName (NormalC n _) = n
conName (RecC n _) = n
conName (InfixC _ n _) = n
conName (ForallC _ _ c) = conName c

-- TODO: copy the fixity of constructors?

removeCons :: [Name] -> Name -> Maybe Name
removeCons ns n | n `elem` ns = Nothing
                | otherwise = Just n

data RedefineType =
  RedefineType { oldType :: Q Type,
                 forwardFunction :: String,
                 backwardFunction :: String,
                 nameMangler :: Name -> Maybe Name,
                 newType :: Q [Dec] }

type TypeSubst = [(Name, Type)]
type ConMap = [(Maybe Con, Maybe Con)]
type TypeMap = [(Name, [TyVarBndr], Name, [Type])] -- Map[new -> old]

{-
getCons :: Name -> [Type] -> Q [(Con, Maybe Con)]
getCons typeName typeArgs = do
  (DataD _cxt _typeName tyVarBndr newCons _deriving, oldCons, omittedCons) <- reify' typeName
  typeSubst <- mkTypeSubst tyVarBndr typeArgs
  oldCons' <- map (applyTypeSubstCon typeSubst) oldCons
  newCons' <- map (applyTypeSubstCon typeSubst) newCons
  return (zip oldCons' newCons')
-}

data Data = Data {
  dTypeInfo :: [(Name, TypeInfo)],
  dFunctionNames :: [(Type, Name)],
  dApplicative :: Type,
  dDecs :: [Dec]
}

type M a = StateT Data Q a

type TypeInfo = (Dec, Maybe ([Name]{-old con names-}, [Name]{-omitted con names-}))

errorE = VarE (mkName "error")

reify' :: Name -> M TypeInfo
reify' name = do
  info <- gets dTypeInfo
  case lookup name info of
    Nothing -> do TyConI i <- lift $ reify name; return (i, Nothing)
    Just i -> return i

splitType :: Type -> (Name, [Type])
splitType t = go t [] where
  go (ConT name) args = (name, args)
  go (AppT t1 t2) args = go t1 (t2 : args)
  go t args = error $ "splitType: " ++ show (t, args)

splitCon :: Con -> (Name, [Type])
splitCon (NormalC n ts) = (n, map snd ts)
splitCon (RecC n ts) = (n, map trd3 ts)
splitCon (InfixC t1 n t2) = (n, [snd t1, snd t2])
splitCon (ForallC _ _ c) = splitCon c

-- TODO: translateType

substType subst (VarT t) = maybe (VarT t) id $ lookup t subst
substType subst (ConT t) = ConT t
substType subst (AppT t1 t2) = AppT (substType subst t1) (substType subst t2)

substCon subst con =
  case con of
    (NormalC name ts) -> NormalC name [(s, substType subst t) | (s, t) <- ts]
-- TODO:    (RecC ..)

redefineTypes :: [RedefineType] -> Q [Dec]
redefineTypes defs = do
{-
  oldTypes <- mapM oldType defs
  oldTypeDefs <- mapM (reify . typeName) oldTypes
-}



  a <- newName "a"
  typeInfo <- mapM mkTypeInfo defs
  let newTypes = [foldl (\x y -> x `AppT` VarT (tyVarBndrVar y)) (ConT typeName) tyVarBndrs | (_, (DataD _cxt typeName tyVarBndrs _cons _deriving, _)) <- typeInfo]
  args <- mapM (const $ newName "_f") newTypes
  d <- execStateT (mapM (translateFun True) newTypes) Data {
    dTypeInfo = typeInfo,
    dFunctionNames = zip newTypes args,
    dApplicative = VarT a,
    dDecs = []
  }
  let inType = foldr
               (\inT outT -> ArrowT `AppT` inT `AppT` outT)
               outType
               [ArrowT `AppT` t `AppT` (VarT a `AppT` t) | t <- newTypes]
      outType = foldl AppT (TupleT (length newTypes)) [ArrowT `AppT` t `AppT` (VarT a `AppT` t) | t <- newTypes]
      body = TupE [VarE $ fromJust $ lookup t (reverse $ dFunctionNames d) | t <- newTypes]
  name <- newName "transform"
  return [SigD name (ForallT [PlainTV a] [ClassP ''Applicative [VarT a]] inType),
          FunD name [Clause (map VarP args) (NormalB body) (dDecs d)]]
          -- forall a. (Applicative a) => (new -> a old) -> new -> a old


translateFun :: Bool -> Type -> M Name
translateFun force newType = do
  fns <- gets dFunctionNames
  case lookup newType fns of
    Just f | not force -> return f
    _ -> do
      name <- lift $ newName "go"
      modify (\d -> d { dFunctionNames = dFunctionNames d ++ [(newType, name)] })
      let (newTypeName, newArgTypes) = splitType newType
      clauses <- translateFun' newTypeName newArgTypes
      a <- gets dApplicative
      oldType <- return newType -- TODO: translateType newType
      modify (\d -> d { dDecs = dDecs d ++ [SigD name (ArrowT `AppT` oldType `AppT` (a `AppT` newType)),
                                            FunD name clauses] })
      return name

tyVarBndrVar (PlainTV n) = n
tyVarBndrVar (KindedTV n _) = n
-- TODO: check for extra or missing args
mkTypeSubst tyVarBndrs newArgTypes = [(tyVarBndrVar x, t) | x <- tyVarBndrs | t <- newArgTypes]

translateFun' :: Name{-new-} -> [Type] -> M [Clause]
translateFun' newTypeName newArgTypes = do
  reify' newTypeName >>= \case
    (DataD _cxt _typeName _tyVarBndr cons _deriving, Just (oldConNames, omittedConNames)) -> do
      -- Note that we do not instantiate the type arguments and instead we keep them general
      clauses <- sequence [translateCon oldConName (Just $ con) | con <- cons | oldConName <- oldConNames]
      clauses' <- sequence [translateCon omittedConName Nothing | omittedConName <- omittedConNames]
      return (clauses ++ clauses')
    (DataD _cxt _typeName tyVarBndrs cons _deriving, Nothing) -> do
      -- TODO: what happens when wrong number of arguments
      let subst = mkTypeSubst tyVarBndrs newArgTypes
      trace ("tf' "++ show (subst, cons)) $ return ()
      clauses <- sequence [translateCon (conName con) (Just $ substCon subst con) | con <- cons]
      return clauses

-- Expects the types of the new args to be the actual ones
translateCon :: Name {-old-} -> Maybe Con {-new-} -> M Clause
translateCon oldConName Nothing =
  return $ Clause [RecP oldConName []] (NormalB (errorE `AppE` LitE (StringL "translation error"))) []
translateCon oldConName (Just newCon) = do
  let (newConName, newConArgTypes) = splitCon newCon
  args <- sequence [do f <- translateFun False t
                       a <- lift $ newName "_arg"
                       return (VarP a, AppE (VarE f) (VarE a))
                   | t <- newConArgTypes]
  let body = foldl app (VarE 'pure `AppE` ConE newConName) (map snd args)
      app l r = InfixE (Just l) (VarE '(<*>)) (Just r)
  return $ Clause [ConP oldConName (map fst args)] (NormalB body) []


--------------

mangleCon :: (Name -> Maybe Name) -> Con -> Maybe Con
mangleCon mangle (NormalC n ts) | Just n' <- mangle n = Just (NormalC n' ts)
mangleCon _ _ = Nothing

mkTypeInfo :: RedefineType -> Q (Name, TypeInfo)
mkTypeInfo rt = do
  let mangle = nameMangler rt
  (oldTypeName, oldTypeArgs) <- liftM splitType (oldType rt)
  TyConI (DataD _oldCxt _oldTypeName oldTyVarBndr oldCons _oldDeriving) <- reify oldTypeName
-- TODO: translate types in oldCons into newCons
  let oldTypeSubst = mkTypeSubst oldTyVarBndr oldTypeArgs -- TODO: check compatibility with each other
  [(DataD newCxt newTypeName newTyVarBndr newCons newDeriving)] <- newType rt
  let newCons = [c | Just c <- map (mangleCon mangle . substCon oldTypeSubst) oldCons]
      (oldCons', omitted) = partition (isJust . mangle) (map conName oldCons)
  return (newTypeName, (DataD newCxt newTypeName newTyVarBndr newCons newDeriving, Just (oldCons', omitted)))

{-
reify' :: Name -> Q (Dec, [Maybe Con])

-- TODO: copy constructor fixity?
getCons :: Name -> [Type] -> Q [(Con, Maybe Con)]
getCons typeName typeArgs = do
  (DataD _cxt _typeName tyVarBndr oldCons _deriving, newCons) <- reify' typeName
  typeSubst <- mkTypeSubst tyVarBndr typeArgs
  oldCons' <- map (applyTypeSubstCon typeSubst) oldCons
  newCons' <- map (applyTypeSubstCon typeSubst) newCons
  return (zip oldCons' newCons')
-}

{-
mkTranslate :: Q Type
mkTranslate newSubType = do x where
  go oldTypeName oldTypeArgs = do
    cons <- getCons oldTypename oldTypeArgs
    



  fns <- gets dFunctionNames
  trace ("tf " ++ show (oldType, fns)) $ return ()
  case lookup oldType fns of
    Just f | not force -> return f
    _ -> do
      name <- lift $ newName "go"
      modify (\d -> d { dFunctionNames = (dFunctionNames d) ++ [(oldType, name)] })
      d <- get
      TyConI (DataD _oldCxt oldTypeName oldTyVarBndr cons _oldDeriving) <- lift $ dReify d (tyName oldType)
      clauses <- mapM (translateCon (mkTypeSub oldTyVarBndr oldType)) cons
      a <- gets dApplicative
      modify (\d -> d { dDecls = [SigD name (ArrowT `AppT` oldType `AppT` (a `AppT` (dRenameType d oldType))),
                                  FunD name clauses] ++
                        dDecls d })
      return name

  

main = do
  (typeSubst, conMap, oldTypeName, oldTypeArgs, newTypeDec) <- foo oldType newType
  return newTypeDec*


foo oldType newType = do
  (oldTypeName, oldTypeArgs) <- liftM splitType oldType
  TyConI (DataD _oldCxt _oldTypeName oldTyVarBndr oldCons _oldDeriving) <- reify oldTypeName
  oldTypeSubst = zip oldTyVarBndr oldTypeArgs -- TODO: check compatibility with each other
  [(DataD newCxt newTypeName newTyVarBndr newCons newDeriving)] = newType
  consMap = [(oldCon, mangle oldCon) | oldCon <- map (applyTypeSubst oldTypeSubst) oldCons] ++
            [(Nothing, newCon) | newCon <- newCons]
  return (consMap, oldTypeName, oldTypeArgs, DataD newCxt newTypeName newTyVarBndr [c | (_, Just c) <- consMap] newDeriving)

mkFun = do
  


Type DataD
 -> (DataD, Type{-old-}, [(Maybe Con, Maybe Con)])


instantiate oldtypes with vars and args from newtype
this makes a new DataD and a mapping from old Con to new Con

on a function: instantiate old type and old con with vars





new types

reify

type mapping

con subst

swap (x, y) = (y, x)

mkRenameCons mangle oldType newType =
  [(Just (conName oldCon), mangle (conName oldCon)) | oldCon <- oldCons] ++
  [(Nothing, Just (conName newCon)) | newCon <- newCons] where
  TyConI (DataD _oldCxt _oldTypeName _oldTyVarBndr oldCons _oldDeriving) = oldType
  [(DataD newCxt newTypeName newTyVarBndr newCons newDeriving)] = newType

mkRenameType oldType newType = (oldTypeName, newTypeName) where
  TyConI (DataD _oldCxt oldTypeName _oldTyVarBndr oldCons _oldDeriving) = oldType
  [(DataD newCxt newTypeName newTyVarBndr addedCons newDeriving)] = newType

typeName (TyConI (DataD _oldCxt oldTypeName _oldTyVarBndr oldCons _oldDeriving)) = oldTypeName
typeName' ([(DataD newCxt newTypeName newTyVarBndr newCons newDeriving)]) = newTypeName

mangleCon mangler tySub (NormalC n ts) | Just n' <- mangler n = Just (NormalC n' (map (\(s,t) -> (s, applyTypeSub tySub t)) ts))
                                       | otherwise = Nothing

redefineTypes :: [RedefineType] -> Q [Dec]
redefineTypes rts = do
  rts' <- sequence [do o <- reify (oldType rt); n <- newType rt; return (rt, o, n) | rt <- rts]
  let conSubst = concat [mkRenameCons (nameMangler rt) o n | (rt, o, n) <- rts']
      conSubstLookup :: [(Maybe Name, Maybe Name)] -> Con -> Maybe Name
      conSubstLookup subst c | Just c' <- lookup (Just $ conName c) subst = c'
                             | otherwise = Just (conName c)
      tySubst = [mkRenameType o n | (_, o, n) <- rts']
      newTypes' = [(newTypeName,
                   DataD newCxt newTypeName newTyVarBndr ([c | Just c <- map (mangleCon (nameMangler rt) [(x,ConT y) | (x,y) <- tySubst]) oldCons] ++ addedCons) newDeriving)
                   | (rt,
                     TyConI (DataD _oldCxt _oldTypeName _oldTyVarBndr oldCons _oldDeriving),
                      [DataD newCxt newTypeName newTyVarBndr addedCons newDeriving]) <- rts']
      reify' name | Just i <- lookup name newTypes' = return (TyConI i)
                  | otherwise = reify name
  transF <- sequence [translate (renameType tySubst) (conSubstLookup conSubst) reify'
                                  (mkName $ forwardFunction rt) [ConT (typeName o)] | (rt, o, _) <- rts']
  transB <- sequence [translate (renameType (map swap tySubst)) (conSubstLookup (map swap conSubst)) reify'
                                  (mkName $ backwardFunction rt) [ConT (typeName' n)] | (rt, _, n) <- rts']
{-
  transB <- translate (renameType tySubst) (l backwardCons) r
            (mkName $ backwardFunction td) [ConT newTypeName]
-}
  return $ {-[DataD newCxt newTypeName newTyVarBndr (map fst backwardCons) newDeriving] ++-} concat transF ++ concat transB


{-

  let newTypes = map trd3 rts'
{-
  renamings <- [
   | (rt, o, n) <- rts,
     TyConI (DataD _oldCxt oldTypeName _oldTyVarBndr oldCons _oldDeriving) <- [o],
     [(DataD newCxt newTypeName newTyVarBndr addedCons newDeriving)] = n ]
sequence
      [do TyConI (DataD _oldCxt oldTypeName _oldTyVarBndr oldCons _oldDeriving) <- reify (oldType rt)
          let [(DataD newCxt newTypeName newTyVarBndr addedCons newDeriving)] = newType td
          return [(oldTypeName, newTypeName)]
       | (rt, nt) <- rts]
-}
  let newTypes' = [(newTypeName, d) | d@(DataD _newCxt newTypeName _newTyVarBndr _addedCons _newDeriving) <- newTypes]
      reify' name | Just i <- lookup name newTypes' = return (TyConI i)
                  | otherwise = reify name
      return (oldTypeName, 
  renameType :: Type -> Type
  renameType = renameType renamings
  [ | (oldType, newType) <- renamings]
  renameCon = if con `in` explicitTypes && rename else id
-- TODO: text mutual rec

redefineTypes :: [RedefineType] -> Q [Dec]
redefineTypes [td] = do
  TyConI (DataD _oldCxt oldTypeName _oldTyVarBndr oldCons _oldDeriving) <- reify (oldType td)
  [(DataD newCxt newTypeName newTyVarBndr addedCons newDeriving)] <- newType td
  let -- maps old Con to what its new name is
      forwardCons :: [(Con, Maybe Name)]
      forwardCons = [(oldCon, nameMangler td (conName oldCon)) | oldCon <- oldCons]
      -- maps new Con to what is old name was
      backwardCons :: [(Con, Maybe Name)]
      backwardCons = [(renameArgs oldTypeName newTypeName newCon, Just (conName oldCon)) |
                      oldCon <- oldCons,
                      Just newCon <- [renameCon (nameMangler td) oldCon]] ++
                     [(addedCon, Nothing) | addedCon <- addedCons]
      nt = DataD newCxt newTypeName newTyVarBndr (map fst backwardCons) newDeriving
      r name = if name == newTypeName then return (TyConI nt) else reify name
      l cs c | Just x <- lookup c cs = x
             | otherwise = Just (conName c)
  trace ("names " ++ show (oldTypeName, newTypeName)) $ return ()
  transF <- translate (renameType oldTypeName newTypeName) (l forwardCons) r
            (mkName $ forwardFunction td) [ConT oldTypeName]
  transB <- translate (renameType newTypeName oldTypeName) (l backwardCons) r
            (mkName $ backwardFunction td) [ConT newTypeName]
  return $ [DataD newCxt newTypeName newTyVarBndr (map fst backwardCons) newDeriving] ++ transF ++ transB
{-
  a <- newName "a"
  return [DataD newCxt newTypeName newTyVarBndr (map fst backwardCons) newDeriving,
          -- forall a. (Applicative a) => (old -> a new) -> old -> a new
          SigD (mkName (forwardFunction td))
               (ForallT [PlainTV a] [ClassP ''Applicative [VarT a]]
                          (ArrowT `AppT` (ArrowT `AppT` ConT oldTypeName `AppT` (VarT a `AppT` ConT newTypeName))
                                  `AppT` (ArrowT `AppT` ConT oldTypeName `AppT` (VarT a `AppT` ConT newTypeName)))),
          FunD (mkName (forwardFunction td)) (translateFun oldTypeName forwardCons),
          -- forall a. (Applicative a) => (new -> a old) -> new -> a old
          SigD (mkName (backwardFunction td))
               (ForallT [PlainTV a] [ClassP ''Applicative [VarT a]]
                          (ArrowT `AppT` (ArrowT `AppT` ConT newTypeName `AppT` (VarT a `AppT` ConT oldTypeName))
                                  `AppT` (ArrowT `AppT` ConT newTypeName `AppT` (VarT a `AppT` ConT oldTypeName)))),
          FunD (mkName (backwardFunction td)) (translateFun newTypeName backwardCons)]
-}
-}

conName :: Con -> Name
conName (NormalC n _) = n
conName (RecC n _) = n
conName (InfixC _ n _) = n
conName (ForallC _ _ c) = conName c

tyName :: Type -> Name
tyName (ConT name) = name
tyName (AppT t _) = tyName t
tyName t = error $ "tyName:" ++ show t

renameArgs :: [(Name, Name)] -> Con -> Con
renameArgs ns = go where
  go (NormalC n ts) = NormalC n (map (renameStrictType ns) ts)
  go (RecC n ts) = RecC n (map (renameNameStrictType ns) ts)
  go (InfixC t1 n t2) = InfixC (renameStrictType ns t1) n (renameStrictType ns t2)
  go (ForallC xs c con) = ForallC xs (renameCxt ns c) (go con)

renameNameStrictType :: [(Name, Name)] -> VarStrictType -> VarStrictType
renameNameStrictType ns (n, s, t) = (n, s, renameType ns t)

renameStrictType :: [(Name, Name)] -> StrictType -> StrictType
renameStrictType ns (s, t) = (s, renameType ns t)

renameType :: [(Name, Name)] -> Type -> Type
renameType ns = go where
  go (ConT n) | Just n' <- lookup n ns = ConT n'
              | otherwise = ConT n
  go (ForallT tvbs c t) = ForallT tvbs (renameCxt ns c) (go t)
  go (AppT t1 t2) = AppT (go t1) (go t2)
  go (SigT t k) = SigT (go t) k
  go t = t

renameCxt :: [(Name, Name)] -> Cxt -> Cxt
renameCxt ns x = map (renamePred ns) x

renamePred :: [(Name, Name)] -> Pred -> Pred
renamePred ns (ClassP c ts) = ClassP c (map (renameType ns) ts)
renamePred ns (EqualP t1 t2) = EqualP (renameType ns t1) (renameType ns t2)

renameCon :: (Name -> Maybe Name) -> Con -> Maybe Con
renameCon f con = case f (conName con) of
                    Nothing -> Nothing
                    Just n -> Just (go con) where
                      go (NormalC _ ts) = NormalC n ts
                      go (RecC _ ts) = RecC n ts
                      go (InfixC t1 _ t2) = InfixC t1 n t2
                      go (ForallC xs c con') = ForallC xs c (go con')

{-
-- Implements the forward and backward translation functions
translateFun :: Name -> [(Con, Maybe Name)] -> [Clause]
translateFun oldTypeName cons = [Clause [VarP fName, VarP x] (NormalB (AppE (VarE go) (VarE x))) [FunD go (map (translate f) cons)]] where
  f t' | ConT oldTypeName == t' = Just fName
       | otherwise = Nothing
  fName = mkName "f"
  x = mkName "x"
  go = mkName "go"

translate :: (Type -> Maybe Name) -> (Con, Maybe Name) -> Clause
translate f (NormalC n ts, n') = Clause [ConP n (map (VarP . fst) args)] (NormalB body) [] where
  args = [g t i | (_, t) <- ts | i <- [(1 :: Integer) ..]]
  g t i | Just h <- f t = let name = mkName ("_arg" ++ show i) in (name, AppE (VarE h) (VarE name))
        | otherwise = let name = mkName ("_arg" ++ show i) in (name, VarE name)
  body | Just n'' <- n' = foldl (\l r -> InfixE (Just l) (VarE '(<*>)) (Just r)) (VarE 'pure `AppE` ConE n'') (map snd args)
       | otherwise = VarE (mkName "error") `AppE` LitE (StringL "translation error")
translate f (RecC n ts, n') = translate f (NormalC n (map (\(_, x, y) -> (x, y)) ts), n')
translate f (InfixC t1 n t2, n') = translate f (NormalC n [t1, t2], n')
translate f (ForallC _xs _c con, n') = translate f (con, n')
-}

------

data D = D {
  dApplicative :: Type,
  dRenameType :: Type -> Type,
  dRenameCon :: Con -> Maybe Name,
  dReify :: Name -> Q Info,
  dFunctionNames :: [(Type, Name)],
  dDecls :: [Dec]
  }
type M a = StateT D Q a

translate :: (Type -> Type) -> (Con -> Maybe Name) -> (Name -> Q Info) -> Name -> [Type] -> Q [Dec]
translate renameType renameCon reify name types = do
  a <- newName "a"
  args <- mapM (const $ newName "_f") types
  d <- execStateT (mapM (translateFun True) types)
             (D { dApplicative = VarT a,
                  dRenameType = renameType,
                  dRenameCon = renameCon,
                  dReify = reify,
                  dFunctionNames = zip types args,
                  dDecls = [] })
  let inType = foldr
               (\inT outT -> ArrowT `AppT` inT `AppT` outT)
               outType
               [ArrowT `AppT` t `AppT` (VarT a `AppT` renameType t) | t <- types]
      outType = foldl AppT (TupleT (length types)) [ArrowT `AppT` t `AppT` (VarT a `AppT` renameType t) | t <- types]
      body = TupE [VarE $ fromJust $ lookup t (reverse $ dFunctionNames d) | t <- types]
  return [SigD name (ForallT [PlainTV a] [ClassP ''Applicative [VarT a]] inType),
          FunD name [Clause (map VarP args) (NormalB body) (dDecls d)]]
          -- forall a. (Applicative a) => (new -> a old) -> new -> a old

mkTypeSub :: [TyVarBndr] -> Type -> [(Name, Type)]
mkTypeSub [] _ = []
mkTypeSub bs (AppT l r) = (tyVarBndrName (last bs), r) : mkTypeSub (init bs) l

tyVarBndrName (PlainTV n) = n
tyVarBndrName (KindedTV n _) = n

applyTypeSub :: [(Name, Type)] -> Type -> Type
applyTypeSub ts (ConT n) = ConT n
applyTypeSub ts (ArrowT) = ArrowT
applyTypeSub ts (VarT t) | Just t' <- lookup t ts = t'
                         | otherwise = VarT t
applyTypeSub ts (AppT t1 t2) = AppT (applyTypeSub ts t1) (applyTypeSub ts t2)

-- Implements the translation functions
translateFun :: Bool -> Type -> M Name
translateFun force oldType = do
  fns <- gets dFunctionNames
  trace ("tf " ++ show (oldType, fns)) $ return ()
  case lookup oldType fns of
    Just f | not force -> return f
    _ -> do
      name <- lift $ newName "go"
      modify (\d -> d { dFunctionNames = (dFunctionNames d) ++ [(oldType, name)] })
      d <- get
      TyConI (DataD _oldCxt oldTypeName oldTyVarBndr cons _oldDeriving) <- lift $ dReify d (tyName oldType)
      clauses <- mapM (translateCon (mkTypeSub oldTyVarBndr oldType)) cons
      a <- gets dApplicative
      modify (\d -> d { dDecls = [SigD name (ArrowT `AppT` oldType `AppT` (a `AppT` (dRenameType d oldType))),
                                  FunD name clauses] ++
                        dDecls d })
      return name

errorE = VarE (mkName "error")

translateCon :: [(Name, Type)] -> Con -> M Clause
translateCon tySub c@(NormalC n ts) = do
  trace ("tc " ++ show (c, tySub)) $ return ()
  gets (flip dRenameCon c) >>= \case
   Nothing -> return $ Clause [RecP n []] (NormalB (errorE `AppE` LitE (StringL "translation error"))) []
   Just n' -> do
     args <- sequence [do f <- translateFun False (applyTypeSub tySub t)
                          a <- lift $ newName "_arg"
                          return (VarP a, AppE (VarE f) (VarE a))
                       | (_, t) <- ts]
     let body = foldl (\l r -> InfixE (Just l) (VarE '(<*>)) (Just r)) (VarE 'pure `AppE` ConE n') (map snd args)
     return $ Clause [ConP n (map fst args)] (NormalB body) []

{-

translateCon :: (Type -> Maybe Name) -> (Con, Maybe Name) -> Clause
translateCon f (NormalC n ts, n') = Clause [ConP n (map (VarP . fst) args)] (NormalB body) [] where
  args = [g t i | (_, t) <- ts | i <- [(1 :: Integer) ..]]
  g t i | Just h <- f t = let name = mkName ("_arg" ++ show i) in (name, AppE (VarE h) (VarE name))
        | otherwise     = let name = mkName ("_arg" ++ show i) in (name, VarE name)
  body | Just n'' <- n' = foldl (\l r -> InfixE (Just l) (VarE '(<*>)) (Just r)) (VarE 'pure `AppE` ConE n'') (map snd args)
       | otherwise = VarE (mkName "error") `AppE` LitE (StringL "translation error")
translateCon f (RecC n ts, n') = translateCon f (NormalC n (map (\(_, x, y) -> (x, y)) ts), n')
translateCon f (InfixC t1 n t2, n') = translateCon f (NormalC n [t1, t2], n')
translateCon f (ForallC _xs _c con, n') = translateCon f (con, n')
-}
-}
