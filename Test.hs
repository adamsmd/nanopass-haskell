{-# LANGUAGE TemplateHaskell #-}
module Test where

import Nanopass
import qualified Test0
import Language.Haskell.TH
import Control.Monad
import Control.Applicative

redefineTypes [
  RedefineType ''Test0.Foo "forward" "backward" (removeCons ['Test0.Bar] >=> (Just . mkName . ("F" ++) . nameBase))
                 [d|data Quux = Wibble deriving (Show)|]]

g :: Quux -> Integer
g Wibble = 3
g (FBaz _) = 4
g FBloop = 5

trans :: (Applicative a) => Test0.Foo -> a Quux
trans (Test0.Bar _) = pure Wibble
trans x = forward trans x

trans' :: (Applicative a) => Quux -> a Test0.Foo
trans' Wibble = pure Test0.Bloop
trans' x = backward trans' x
