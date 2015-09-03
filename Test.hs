{-# LANGUAGE TemplateHaskell #-}
module Test where

import Nanopass
import qualified Test0
import Language.Haskell.TH

defineData [
  TypeDelta ''Test0.Foo "forward" "backward" (\x -> Just $ mkName ("F" ++ nameBase x))
              ['Test0.Bar]
              [d|data Quux = Wibble|]]

g :: Quux -> Integer
g Wibble = 3
g (FBaz _) = 4
g FBloop = 5

trans :: Test0.Foo -> Quux
trans (Test0.Bar _) = Wibble
trans x = forward trans x

trans' :: Quux -> Test0.Foo
trans' Wibble = Test0.Bloop
trans' x = backward trans' x
