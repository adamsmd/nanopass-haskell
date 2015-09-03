{-# LANGUAGE ParallelListComp #-}
module Nanopass where

import Language.Haskell.TH
import Language.Haskell.TH.Syntax

data TypeDelta =
  TypeDelta { oldType :: Name,
              forwardFunction :: String,
              backwardFunction :: String,
              nameMangler :: Name -> Maybe Name,
              removedConstructors :: [Name],
              newType :: Q [Dec] } |
  TypeDeltaNop { noOpOldType :: Name, noOpNewType :: Name }

defineData :: [TypeDelta] -> Q [Dec]
defineData [td@TypeDelta {}] = do
  TyConI (DataD _oldCxt oldTypeName _oldTyVarBndr oldCons _oldDeriving) <- reify (oldType td)
  [DataD newCxt newTypeName newTyVarBndr addedCons newDeriving] <- newType td
  let rename n | n `elem` removedConstructors td = Nothing
               | otherwise = nameMangler td n
  let forwardCons = [(oldCon, rename (conName oldCon)) | oldCon <- oldCons]
      backwardCons = [(renameArgs oldTypeName newTypeName newCon, Just (conName oldCon)) |
                      oldCon <- oldCons,
                      Just newCon <- [renameCon rename oldCon]] ++
                     [(addedCon, Nothing) | addedCon <- addedCons]
  return [DataD newCxt newTypeName newTyVarBndr (map fst backwardCons) newDeriving,
          SigD (mkName (forwardFunction td))
                 (ArrowT `AppT` (ArrowT `AppT` ConT oldTypeName `AppT` ConT newTypeName)
                         `AppT` (ArrowT `AppT` ConT oldTypeName `AppT` ConT newTypeName)),
          FunD (mkName (forwardFunction td)) (translateFun oldTypeName forwardCons),
          SigD (mkName (backwardFunction td))
                 (ArrowT `AppT` (ArrowT `AppT` ConT newTypeName `AppT` ConT oldTypeName)
                         `AppT` (ArrowT `AppT` ConT newTypeName `AppT` ConT oldTypeName)),
          FunD (mkName (backwardFunction td)) (translateFun newTypeName backwardCons)]

conName :: Con -> Name
conName (NormalC n _) = n
conName (RecC n _) = n
conName (InfixC _ n _) = n
conName (ForallC _ _ c) = conName c

renameArgs :: Name -> Name -> Con -> Con
renameArgs oldTypeName newTypeName = go where
  go (NormalC n ts) = NormalC n (map (renameStrictType oldTypeName newTypeName) ts)
  go (RecC n ts) = RecC n (map (renameNameStrictType oldTypeName newTypeName) ts)
  go (InfixC t1 n t2) = InfixC (renameStrictType oldTypeName newTypeName t1) n (renameStrictType oldTypeName newTypeName t2)
  go (ForallC xs c con) = ForallC xs (renameCxt oldTypeName newTypeName c) (go con)

renameNameStrictType :: Name -> Name -> VarStrictType -> VarStrictType
renameNameStrictType oldTypeName newTypeName (n, s, t) = (n, s, renameType oldTypeName newTypeName t)

renameStrictType :: Name -> Name -> StrictType -> StrictType
renameStrictType oldTypeName newTypeName (s, t) = (s, renameType oldTypeName newTypeName t)

renameType :: Name -> Name -> Type -> Type
renameType oldTypeName newTypeName = go where
  go (ConT n) | n == oldTypeName = ConT newTypeName
              | otherwise = ConT n
  go (ForallT tvbs c t) = ForallT tvbs (renameCxt oldTypeName newTypeName c) (go t)
  go (AppT t1 t2) = AppT (go t1) (go t2)
  go (SigT t k) = SigT (go t) k
  go t = t

renameCxt :: Name -> Name -> Cxt -> Cxt
renameCxt oldTypeName newTypeName x = map (renamePred oldTypeName newTypeName) x

renamePred :: Name -> Name -> Pred -> Pred
renamePred oldTypeName newTypeName (ClassP c ts) = ClassP c (map (renameType oldTypeName newTypeName) ts)
renamePred oldTypeName newTypeName (EqualP t1 t2) = EqualP (renameType oldTypeName newTypeName t1) (renameType oldTypeName newTypeName t2)

renameCon :: (Name -> Maybe Name) -> Con -> Maybe Con
renameCon f con = case f (conName con) of
                    Nothing -> Nothing
                    Just n -> Just (go con) where
                      go (NormalC _ ts) = NormalC n ts
                      go (RecC _ ts) = RecC n ts
                      go (InfixC t1 _ t2) = InfixC t1 n t2
                      go (ForallC xs c con') = ForallC xs c (go con')

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
  body | Just n'' <- n' = foldl AppE (ConE n'') (map snd args)
       | otherwise = VarE (mkName "error") `AppE` LitE (StringL "translation error")
translate f (RecC n ts, n') = translate f (NormalC n (map (\(_, x, y) -> (x, y)) ts), n')
translate f (InfixC t1 n t2, n') = translate f (NormalC n [t1, t2], n')
translate f (ForallC _xs _c con, n') = translate f (con, n')
