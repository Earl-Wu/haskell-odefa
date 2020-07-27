{-# LANGUAGE AllowAmbiguousTypes #-}

-- TODO: Selective export?
module PlumeAnalysis.Context where

import AST.AbstractAst

import Data.List as L
import Data.Set as S

class (Eq c, Ord c, Show c) => Context c where
  empty :: c
  add :: AbstractCls -> c -> c
  name :: String

newtype SetContext = SetContext (S.Set AbstractCls)
  deriving (Eq, Ord, Show)

instance Context SetContext where
  empty = SetContext S.empty
  add cls (SetContext s) = SetContext (S.insert cls s)
  name = "Set"

newtype UnitListContext = UnitListContext [AbstractCls]
  deriving (Eq, Ord, Show)

instance Context UnitListContext where
  empty = UnitListContext []
  add _ ctx = ctx
  name = "Unit List"

newtype SingleElementListContext = SingleElementListContext [AbstractCls]
  deriving (Eq, Ord, Show)

instance Context SingleElementListContext where
  empty = SingleElementListContext []
  add cls (SingleElementListContext lst) = SingleElementListContext [cls]
  name = "Single Element List"

newtype TwoElementListContext = TwoElementListContext [AbstractCls]
  deriving (Eq, Ord, Show)

instance Context TwoElementListContext where
  empty = TwoElementListContext []
  add cls (TwoElementListContext lst) = 
    case lst of
      [] -> TwoElementListContext [cls]
      hd : _ -> TwoElementListContext [cls, hd]
  name = "Two Element List"

{-

{-# LANGUAGE TypeApplications #-}

name @SetContext

id :: ∀α.α→α
id x = x
n :: Int
n = id 5


let id = Λα.λx:α.x

id int 5

e ::= x | λx:τ.e | Λα.e | ℤ
τ ::= α | τ → τ | int

-}
