{-# LANGUAGE TemplateHaskell, GADTs, ScopedTypeVariables #-}
module Nanopass where

-- TODO: implement "backwards"
-- TODO: copy the fixity of constructors

import Control.Applicative
import Control.Monad.RWS
import qualified Data.Map as Map
import Data.Monoid
import Language.Haskell.TH
import Language.Haskell.TH.Syntax hiding (lift)

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
  namedFunctionsR :: Map.Map (Type{-srcType-}, Type{-dstType-}) Name
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
typeDeltas :: [Delta] -> Q Dec
typeDeltas deltas = do
  error "typeDeltas not implemented" -- FIXME

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

  -- The worklist contains functions that should be generated.
  let loop = do r <- popWorklist
                case r of
                  Nothing -> return ()
                  Just (name, srcType, dstType) ->
                    generateFun name srcType dstType >> loop
      userFunctions = error "No user functions yet"
      initialState = error "No initial state yet"
  ((), finalState, finalImpls) <- runRWST loop userFunctions initialState

  -- return function that looks like:
  --   forward u1 u2 u3 = (e1, e2, e3) where
  --     ... results from calling generateFun ...
  -- 
  error "typeDeltas not implemented"

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

-- Generates code for transforming a given type to another type
generateFun :: Name -> Type -> Type -> M ()
generateFun name srcType dstType = do
  generateFun' name srcType dstType >>= addImplementation

generateFun' :: Name -> Type -> Type -> M Dec
generateFun' name srcType dstType = do
  -- return TH like the following:
  --  name = \x -> case x of ...
  -- calls 'generateClause' for generating clauses of the 'case'
  error "unimplemented: generateFun'"
  
type Subst = Map.Map Name Type

applySubst :: Subst -> Type -> Type
applySubst = error "unimplemented: applySubst"

generateClause :: Con -> Subst -> Con -> Subst -> M Match
generateClause srcCon srcSubst dstCon dstSubst = do
  -- TODO: handle custom user-specified clauses

  -- return TH like the following:
  --  srcCon x1 x2 ... -> dstCon (f1 x1) (f2 x2) ...
  -- calls 'getFun' to find f1, f2, etc.
  let NormalC srcConName srcStrictTypes = srcCon
  let NormalC dstConName dstStrictTypes = dstCon
  
  let srcArgTypes :: [Type]
      srcArgTypes = map (applySubst srcSubst. snd) srcStrictTypes

  srcArgs :: [Name] <- mapM (\i -> lift $ newName $ "arg"++show i)
                            (zipWith const [1..] srcArgTypes)

  let generateApp :: Name -> Type -> Type -> M Exp
      generateApp srcArg srcArgType dstArgType = do
        funName <- getFun srcArgType dstArgType
        return (AppE (VarE funName) (VarE srcArg))

  let dstArgTypes :: [Type]
      dstArgTypes = map (applySubst dstSubst. snd) dstStrictTypes

  dstArgs :: [Exp] <- sequence (zipWith3 generateApp srcArgs srcArgTypes dstArgTypes)

  let pat = ConP srcConName (map VarP srcArgs)
      body = NormalB (foldl (AppE) (ConE dstConName) dstArgs)
  return $ Match pat body [{-empty "where" block-}]
