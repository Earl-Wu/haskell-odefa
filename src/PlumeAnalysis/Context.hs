{-# LANGUAGE AllowAmbiguousTypes #-}

module PlumeAnalysis.Context
( Context(..)
) where

import AST.Ast

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
