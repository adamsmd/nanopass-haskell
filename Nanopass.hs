{-# LANGUAGE ParallelListComp, TemplateHaskell, GADTs #-}
module Nanopass where

import Control.Applicative
import Control.Monad.RWS
import qualified Data.Map as Map
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

-- User level syntax

type ConFun = (Con, [Type]) -> Maybe (Con, [Type])

data Delta where
  (:->:) :: Q Type -> ConFun -> Q Dec -> Delta

-- Internal data types

type M a = RWST R W S Q a

data R = R {
  -- Names for functions that the user supplies to us
  userFunctionsR :: Map.Map (Type{-srcType-}, Type{-dstType-}) Name
  }
  
data W = W {
  generatedImplementationsW :: [Dec]
  }

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
               return x

addWorklist :: Name -> Type -> Type -> M ()
addWorklist name srcType dstType =
  modify (\s -> s { worklistS = name : (worklistS s) })

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

typeDeltas :: [Delta] -> Q Dec
typeDeltas deltas = do
  -- put user written functions (u1, u2, u3) in the 'fun' list
  --  i.e., addFun u1 u1SrcType u1DstType, etc.
  -- put entry point functions (e1, e2, e3) in the worklist
  --  i.e., addWorklist e1 e1SrcType e1DstType, etc.
  
  error "typeDeltas not implemented" -- FIXME
  
  -- Generate the actual functions
  let loop = do r <- popWorklist
                case r of
                  Nothing -> return ()
                  Just (name, srcType, dstType) ->
                    generateFun name srcType dstType >> loop
  loop
  -- Generate:
  --   forward u1 u2 u3 = (e1, e2, e3) where
  --     ... results from calling generateFun ...
  -- 

-- We call generateFun in a worklist style algorithm.
-- The initial functions to generate in that worklist
-- are based on the entry points.

-- The worklist contains functions that should be generated.

-- 'generateFun' checks if there is already a user supplied
-- function and if so, does not put anything in the worklist.

getFun :: Type -> Type -> M Name
getFun srcType dstType = do
  userFun <- getUserFun srcType dstType
  case userFun of -- would prefer 'case<-'
    Just name -> return name
    Nothing -> generateFunNoUser srcType dstType

-- 'generateFunNoUser' checks if there is already a generated
-- function and if so, does not put anything in the worklist.

getFunNoUser :: Type -> Type -> M Name
getFunNoUser srcType dstType = do
  fun <- getGeneratedFun srcType dstType
  case fun of
    Just name -> return name
    Nothing -> do
      name <- nameFor srcType dstType
      addWorklist name srcType dstType
      return name



      fun <- generateFun' name srcType dstType
      return (name, fun)

-- Generates code for transforming a given type to another type
generateFun :: Name -> Type -> Type -> M ()
generateFun name srcType dstType = do
  error "generateFun unimplemented" 
  -- Record the name before starting processing so we properly handle recursion
  -- Puts (name, error "Impossible in ...") in the generateFunctionsS mapping
  addGeneratedName srcType dstType name
  implementation <- error "generateFun not implemented."
  
  -- Record the implementation for the generated function
  addGeneratedImplementation srcType dstType implementation
  return ()

generateFun' :: Name -> Type -> Type -> M Dec
generateFun' name srcType dstType = do
  -- return TH like the following:
  --  name :: srcType -> dstType
  --  name x = case x of ...
  -- calls 'generateClause' for generating clauses of the 'case'
  error "unimplemented: generateFun'"

generateClause :: Name -> [Type] -> Name -> [Type] -> M (Pat, Exp)
generateClause srcCon srcTypes dstCon dstTypes =
  -- return TH like the following:
  --  srcCon x1 x2 ... -> dstCon (f1 x1) (f2 x2) ...
  -- calls 'getFun' to find f1, f2, etc.
  error "unimplemented: generateClause"
