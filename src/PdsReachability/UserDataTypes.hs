{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module PdsReachability.UserDataTypes where

import PdsReachability.Specification

-- Destinations which are described to us by the user.
data Terminus a
  = StaticTerminus (Node a)
  | DynamicTerminus (UntargetedDynPop a)
deriving instance (SpecIs Eq a) => (Eq (Terminus a))
deriving instance (SpecIs Ord a) => (Ord (Terminus a))
deriving instance (SpecIs Show a) => (Show (Terminus a))

data StackAction a
  = Push (Element a)
  | Pop (Element a)
  | DynamicPop (TargetedDynPop a)
  | Nop
deriving instance (TargetedSpecIs Eq a) => (Eq (StackAction a))
deriving instance (TargetedSpecIs Ord a) => (Ord (StackAction a))
deriving instance (TargetedSpecIs Show a) => (Show (StackAction a))

data Path a = Path [StackAction a]
deriving instance (SpecIs Show a) => (Show (Path a))

data EdgeFunction a = EdgeFunction (Node a -> [(Path a, Terminus a)])

data Question a = Question (Node a) [StackAction a]
deriving instance (SpecIs Show a) => (Show (Question a))
deriving instance (SpecIs Eq a) => (Eq (Question a))
deriving instance (SpecIs Ord a) => (Ord (Question a))
