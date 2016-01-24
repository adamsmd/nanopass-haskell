{-# LANGUAGE TemplateHaskell #-}
import Nanopass
import TestTypes

typeDeltas "function" -- name
  [[t|ListInt -> ListInt'|]] -- exported
  [(Just "u1", [t|ListInt -> ListInt'|])] --userFunctionsR
  [("e1", [t|ListInt -> ListInt'|])] -- namedFunctionsR
  [([t| ListInt|], [t|ListInt'|], [
    (Just ('Cons, [[t|Int|], [t|ListInt|]]), Just ('Cons', [[t|Int|], [t|ListInt'|]]))])]
