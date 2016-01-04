{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
module Test where

import Nanopass
import qualified Test0
import Language.Haskell.TH
import Control.Monad
import Control.Applicative

redefineTypes [
  RedefineType [t|Test0.Foo|] "forward" "backward" (removeCons ['Test0.Bar] >=> (Just . mkName . ("F" ++) . nameBase))
                 [d|data Quux = Wibble deriving (Show)|]]

{-
redefineTypes 'forward 'backward [
  RedefineType [t|Test0.Foo (Maybe b)|] (removeCons ['Test0.Bar] >=> (Just . mkName . ("F" ++) . nameBase))
                 [d|data Quux b = Wibble deriving (Show)|],
  Transform 'forward 'backward [t|forall b. Quux b|]


C :: a -> b -> c -> t
C' :: a -> b -> Maybe -> t'


redefineTypes [
  RedefineType ''Test0.Foo "forward" "backward" (removeCons ['Test0.Bar] >=> (Just . mkName . ("F" ++) . nameBase))
                 [d|data Quux = Wibble deriving (Show)|]
{-  TransformType [t|Maybe Foo|] [t|Maybe Bar|] [|\t1 t2 -> fmap (forward t1 t2)|] [|\t1 t2 -> fmap (backward t1 t2)|] -}
 ]
-}

g :: Quux -> Integer
g Wibble = 3
g (FBaz _) = 4
g (FBloop _ _) = 5

trans :: (Applicative a) => Test0.Foo -> a Quux
trans (Test0.Bar _) = pure Wibble
trans x = forward trans x

trans' :: (Applicative a) => Quux -> a Test0.Foo
trans' Wibble = pure (Test0.Bloop undefined Nothing)
trans' x = backward trans' x
