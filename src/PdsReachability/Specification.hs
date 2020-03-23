{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}

module PdsReachability.Specification where

class Specification a where
  type family Node a :: *
  type family Element a :: *
  type family DynPop a :: *
  type family UntargetedPop a :: *
