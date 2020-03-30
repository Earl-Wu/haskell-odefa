{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module PdsReachability.Specification where

import GHC.Exts (Constraint)

type family Node a :: *
type family Element a :: *
type family TargetedDynPop a :: *
type family UntargetedDynPop a :: *

type TargetedSpecIs c a =  -- :: (* -> Constraint) -> * -> Constraint
  ((c (Node a),
    c (Element a),
    c (TargetedDynPop a))
   :: Constraint
  )

type SpecIs c a =  -- :: (* -> Constraint) -> * -> Constraint
  ((TargetedSpecIs c a,
    c (UntargetedDynPop a))
   :: Constraint
  )

type TargetedSpec a = -- :: * -> Constraint
  ((TargetedSpecIs Eq a,
    TargetedSpecIs Ord a,
    TargetedSpecIs Show a)
   :: Constraint
  )

type Spec a = ((SpecIs Eq a, SpecIs Ord a, SpecIs Show a) :: Constraint)
