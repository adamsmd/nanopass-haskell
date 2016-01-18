{-# LANGUAGE TemplateHaskell, GADTs, ScopedTypeVariables #-}
module Nanopass where

-- TODO: implement "backwards"
-- TODO: copy the fixity of constructors

import Control.Applicative
import Control.Monad.RWS
import Control.Monad.State
import Data.Maybe
import Data.Monoid
import Language.Haskell.TH
import Language.Haskell.TH.Syntax hiding (lift)

import qualified Data.Map as Map

import TestTypes

import Debug.Trace

--------
-- User level syntax
--------

type ConFun = (Con, [Type]) -> Maybe (Con, [Type])

data Delta where
  (:->:) :: Q Type -> ConFun -> Q Dec -> Delta

--------
-- Internal data types
--------

type M a = RWST R W S Q a

data R = R {
  -- Names for functions that the user supplies to "forward"
  userFunctionsR :: Map.Map (Type{-srcType-}, Type{-dstType-}) Name,
  
  -- Names for generated functions where the user specifies the name
  namedFunctionsR :: Map.Map (Type{-srcType-}, Type{-dstType-}) Name,
  
  -- Mappings between constructors
  consR :: [(Type, Type, [(Maybe Con, Maybe Con)])]
  }
  
data W = W {
  generatedImplementationsW :: [Dec]
  }

instance Monoid W where
  mempty = W mempty
  mappend (W x) (W y) = W (x <> y)

data S = S {
  worklistS :: [(Name, Type{-srcType-}, Type{-dstType-})],
  -- Names and implementations for functions that we generated
  generatedNamesS :: Map.Map (Type{-srcType-}, Type{-dstType-}) Name
  }

popWorklist :: M (Maybe (Name, Type, Type))
popWorklist = do
  s <- get
  case worklistS s of
    [] -> return Nothing
    x:xs -> do put (s { worklistS = xs })
               return (Just x)

addWorklist :: Name -> Type -> Type -> M ()
addWorklist name srcType dstType =
  modify (\s -> s { worklistS = (name, srcType, dstType) : (worklistS s) })

addImplementation :: Dec -> M ()
addImplementation impl = tell (W [impl])

-- returns the names of the functions that
-- are supplied to 'forward' by the user
getUserFun :: Type -> Type -> M (Maybe Name)
getUserFun srcType dstType =
  asks (Map.lookup (srcType, dstType) . userFunctionsR)

{-
addFun :: Name -> Type -> Type -> Dec -> M ()


-- TODO: this function might go away, and I'm not sure about its specification
-- Construct a function naming function based on the input.
-- This is so we can implement the special cases for 'Map' and 'Set'
getName :: Type -> Type -> M Name
getName = error "nameFor not implemented"
  -- lookup name in 'funlistS'
  -- return if found; otherwise, generate a new name, put it in namesS, call  and return that
-}

-- main entry point for user API
typeDeltas :: [Delta] -> Q [Dec]
typeDeltas deltas = do
  -- put user written functions (u1, u2, u3) in the 'userFunctionsR' list
  --  i.e., addFun u1 u1SrcType u1DstType, etc.
  
  -- put user specified names for generated functions in generatedNamesS
  -- TODO

  -- put entry point functions (e1, e2, e3) in the worklist
  --  i.e., addWorklist e1 e1SrcType e1DstType, etc.  
  
  -- run the worklist to create the generated functions
  -- We call generateFun in a worklist style algorithm.
  -- The initial functions to generate in that worklist
  -- are based on the entry points.
  
--  let oldType = [d| data ListInt = Cons Int ListInt | Nil |]
--  let newType = [d| data ListInt' = Cons' Int ListInt | Nil' |]
  let name = mkName "function"
  listInt <- [t|ListInt|]
  listInt' <- [t|ListInt'|]
  int <- [t|Int|]
  
  let userFunctions = Map.fromList [((listInt, listInt'), mkName "u1")]
      exportedFunctions = [mkName "u1"]

  -- The worklist contains functions that should be generated.
  let loop = do r <- popWorklist
                case r of
                  Nothing -> return ()
                  Just (name, srcType, dstType) ->
                    generateFun name srcType dstType >> loop
      initialReader = R {
        userFunctionsR = userFunctions,
        namedFunctionsR = Map.empty,
        consR = [(listInt, listInt', [(Just $ NormalC 'Cons [{-(NotStrict, int),-} (NotStrict, listInt)], Just $ NormalC 'Cons' [{-(NotStrict, int),-} (NotStrict, listInt')])])]
        }

      initialState = S {
        worklistS = [(mkName "go_ListInt_ListInt'", listInt, listInt')],
        generatedNamesS = Map.empty
       }
  ((), finalState, finalImpls) <- runRWST loop initialReader initialState

  -- return function that looks like:
  --   forward u1 u2 u3 = (e1, e2, e3) where
  --     ... results from calling generateFun ...
  -- 
  return $ [ValD (VarP name)
    (NormalB
      (LamE (map VarP (Map.elems userFunctions))
        (LetE (generatedImplementationsW finalImpls)
          (TupE (map VarE exportedFunctions))))) []]

-- 'getFun' checks if there is already a user supplied
-- function and if so, does not put anything in the worklist.
getFun :: Type -> Type -> M Name
getFun srcType dstType = do
  userFun <- getUserFun srcType dstType
  case userFun of -- would prefer 'case<-'
    Just name -> return name
    Nothing -> getFunNoUser srcType dstType

-- 'getFunNoUser' checks if there is already a generated
-- function and if so, does not put anything in the worklist.
getFunNoUser :: Type -> Type -> M Name
getFunNoUser srcType dstType = do
  s <- get
  let names = generatedNamesS s
  case Map.lookup (srcType, dstType) names of
    Just name -> return name
    Nothing -> do
      name <- getNewName srcType dstType
      -- Record the name before starting processing so we properly handle recursion
      -- Puts (name, error "Impossible in ...") in the generateFunctionsS mapping
      put (s { generatedNamesS = Map.insert (srcType, dstType) name names })
      addWorklist name srcType dstType
      return name

-- looks to see if the user specified a name
-- otherwise, generates a new name
getNewName :: Type -> Type -> M Name
getNewName srcType dstType = do
  names <- asks namedFunctionsR
  case Map.lookup (srcType, dstType) names of
    Just name -> return name
    Nothing -> lift $ newName "go"


--------
-- Worklist Functions
--------

type SM = StateT Subst Maybe

-- Returns a subst that turns the first arg into the second arg
instantiate :: Type -> Type -> Maybe Subst
instantiate ty1 ty2 = execStateT (instantiate' ty1 ty2) Map.empty

instantiate' :: Type -> Type -> SM ()
instantiate' (VarT var) ty2 = do
  s <- get
  case Map.lookup var s of
    Nothing -> put (Map.insert var ty2 s)
    Just ty1 | ty1 == ty2 -> return ()
             | otherwise -> mzero
instantiate' (ForallT bndrs1 cxt1 ty1) (ForallT bndrs2 cxt2 ty2)
  | length bndrs1 /= length bndrs2 = mzero
  | otherwise = do
  s <- get
  let s' = Map.fromList [(tyVarBndrName b1, VarT (tyVarBndrName b2)) | (b1, b2) <- zip bndrs1 bndrs2]
  put (Map.union s' s) -- left biased by default
  zipWithM instantiate' cxt1 cxt2
  instantiate' ty1 ty2
  s'' <- get
  put (foldr (Map.updateWithKey (\k _ -> Map.lookup k s)) s'' (map tyVarBndrName bndrs1))
instantiate' (AppT argTy1 resTy1) (AppT argTy2 resTy2) = instantiate' argTy1 argTy2 >> instantiate' resTy1 resTy2
instantiate' (SigT ty1 _) ty2 = instantiate' ty1 ty2
instantiate' ty1 (SigT ty2 _) = instantiate' ty1 ty2
instantiate' ty1 ty2
  | ty1 == ty2 = return ()
  | otherwise = mzero

-- Generates code for transforming a given type to another type
generateFun :: Name -> Type -> Type -> M ()
generateFun name srcType dstType =
  generateFun' name srcType dstType >>= mapM_ addImplementation
  
typeCons :: Type -> Type -> M [(Maybe Con, Maybe Con)]
typeCons srcType dstType = do
  r <- asks consR
  cons <- mapM go r
  case catMaybes cons of
    [cons] -> return cons
    [] -> error $ "TODO: typeCons: check \"maybe\" mappings: " ++ show (srcType, dstType)
    _ -> error "TODO: typeCons: ambiguous mapping"
  where
  go (srcType', dstType', cons) = do
    case (instantiate srcType' srcType, instantiate dstType' dstType) of
      (Just srcSubst, Just dstSubst) -> liftM Just $ mapM (go' srcSubst dstSubst) cons
      _ -> return Nothing
  go' srcSubst dstSubst (srcCon, dstCon) = do
    srcCon' <- applySubstMaybeCon srcSubst srcCon
    dstCon' <- applySubstMaybeCon dstSubst dstCon
    return (srcCon', dstCon')

generateFun' :: Name -> Type -> Type -> M [Dec]
generateFun' name srcType dstType = do
  -- return TH like the following:
  --  name x = case x of ...clauses...
  -- where the clauses are created by 'generateClause'

  -- TODO: handle other kinds of TyConI
  -- TODO: handle non TyConI

  -- TODO: handle non-"data" types
  cons <- typeCons srcType dstType
  

{-
  (srcName, srcBndrs, srcCons, dstName, dstBndrs, dstCons) <- reifyTypes srcType dstType
  srcSubst <- unify srcType (foldl AppT (ConT srcName) (map bndrToType srcBndrs))

  TyConI (DataD _ dstName dstBndrs dstCons _) <- reifyHead dstType
  (dstName, dstBndrs, dstCons) <- reifyHead dstType
  dstSubst <- unify dstType (foldl AppT (ConT dstName) (map bndrToType dstBndrs))
  -}
  
  clauses <- mapM (uncurry generateClause) cons

  arg <- lift (newName "arg")
  return [SigD name (ArrowT `AppT` srcType `AppT` dstType),
          FunD name [Clause [VarP arg] (NormalB (CaseE (VarE arg) (catMaybes clauses))) []]]

bndrToType :: TyVarBndr -> Type
bndrToType (PlainTV n) = VarT n
bndrToType (KindedTV n k) = SigT (VarT n) k


type Subst = Map.Map Name Type

applySubstMaybeCon :: Subst -> Maybe Con -> M (Maybe Con)
applySubstMaybeCon subst con = traverse (applySubstCon subst) con
applySubstCon :: Subst -> Con -> M Con
applySubstCon subst (NormalC name args) = do
  args' <- mapM (applySubstStrictType subst) args
  return (NormalC name args')
applySubstStrictType :: Subst -> StrictType -> M StrictType
applySubstStrictType subst (strict, ty) = do
  ty' <- applySubst subst ty
  return (strict, ty')

applySubst :: Subst -> Type -> M Type
applySubst s typ =
  case typ of
    ForallT b c t -> do
      let b' = map tyVarBndrName b
      pests <- mapM (liftM VarT . lift . newName . nameBase) b'
      let pestSubst = Map.fromList $ zip b' pests
          s' = Map.union pestSubst s -- Map.union is left biased
      ForallT <$> return (map (applySubstTyVarBndr s') b)
              <*> (mapM (applySubst s') c)
              <*> (applySubst s' t)
    AppT l r -> AppT <$> (applySubst s l) <*> (applySubst s r)
    SigT t k -> SigT <$> (applySubst s t) <*> pure k
    VarT n ->
      case Map.lookup n s of
        Just t -> pure t
        Nothing -> pure typ
    _ -> pure typ

applySubstTyVarBndr :: Subst -> TyVarBndr -> TyVarBndr
applySubstTyVarBndr s b = case Map.lookup (tyVarBndrName b) s of
  Just (VarT n) -> tyVarBndrOther b n
  _ -> error "applySubstTyVarBndr: lookup failed"

tyVarBndrOther :: TyVarBndr -> Name -> TyVarBndr
tyVarBndrOther (PlainTV _) = PlainTV
tyVarBndrOther (KindedTV _ k) = flip KindedTV k

tyVarBndrName :: TyVarBndr -> Name
tyVarBndrName (PlainTV n) = n
tyVarBndrName (KindedTV n _) = n

tyVarBndrMapName :: (Name -> M Name) -> TyVarBndr -> M TyVarBndr
tyVarBndrMapName f (PlainTV n) = PlainTV <$> f n
tyVarBndrMapName f (KindedTV n k) = KindedTV <$> f n <*> return k

generateClause :: Maybe Con -> Maybe Con -> M (Maybe Match)
generateClause Nothing _dstCon  = return Nothing
generateClause (Just (NormalC srcName _)) Nothing  = do -- TODO: handle non-NormalC constructors
  -- TODO: more detailed message
  body <- lift [|error "translation error"|]
  return $ Just $ Match (RecP srcName []) (NormalB body) []
generateClause (Just (NormalC srcConName srcArgTypes))
               (Just (NormalC dstConName dstArgTypes)) = do
  -- TODO: handle custom user-specified clauses
  -- TODO: "Maybe Con" if constructor is deleted

  -- return TH like the following:
  --  srcCon x1 x2 ... -> dstCon (f1 x1) (f2 x2) ...
  -- calls 'getFun' to find f1, f2, etc.
  let generateApp :: Name -> StrictType -> StrictType -> M Exp
      generateApp srcArg (_, srcArgType) (_, dstArgType) = do
        funName <- getFun srcArgType dstArgType
        return (AppE (VarE funName) (VarE srcArg))

  srcArgs :: [Name] <- mapM (\i -> lift $ newName $ "arg"++show i)
                            (zipWith const [1..] srcArgTypes)
  dstArgs :: [Exp] <- sequence (zipWith3 generateApp srcArgs srcArgTypes dstArgTypes)

  let pat = ConP srcConName (map VarP srcArgs)
      body = NormalB (foldl (AppE) (ConE dstConName) dstArgs)
  return $ Just $ Match pat body [{-empty "where" block-}]


{-
generateClause :: Subst -> Subst -> Con -> Maybe Con -> M Match
generateClause srcSubst dstSubst srcCon Nothing  = do
  -- TODO: more detailed message
  body <- lift [|error "translation error"|]
  Match (RecP srcName []) (NormalB body)
generateClause srcSubst dstSubst srcCon (Just dstCon) = do
  -- TODO: handle custom user-specified clauses
  -- TODO: "Maybe Con" if constructor is deleted

  -- return TH like the following:
  --  srcCon x1 x2 ... -> dstCon (f1 x1) (f2 x2) ...
  -- calls 'getFun' to find f1, f2, etc.
  let NormalC srcConName srcStrictTypes = srcCon
  
  let srcArgTypes :: [Type]
      srcArgTypes = mapM (applySubst srcSubst . snd) srcStrictTypes

  srcArgs :: [Name] <- mapM (\i -> lift $ newName $ "arg"++show i)
                            (zipWith const [1..] srcArgTypes)

  let generateApp :: Name -> Type -> Type -> M Exp
      generateApp srcArg srcArgType dstArgType = do
        funName <- getFun srcArgType dstArgType
        return (AppE (VarE funName) (VarE srcArg))

  let dstArgTypes :: [Type]
      dstArgTypes = mapM (applySubst dstSubst . snd) dstStrictTypes

  dstArgs :: [Exp] <- sequence (zipWith3 generateApp srcArgs srcArgTypes dstArgTypes)

  let pat = ConP srcConName (map VarP srcArgs)
      body = NormalB (foldl (AppE) (ConE dstConName) dstArgs)
  return $ Match pat body [{-empty "where" block-}]
  
-}
