{-# LANGUAGE TypeFamilies #-}

module PlumeAnalysis.PlumeSpecification where

import PdsReachability
import PlumeAnalysis.Pds.PlumePdsDynamicPopTypes
import PlumeAnalysis.Pds.PlumePdsStructureTypes
import PlumeAnalysis.Types.PlumeGraph

-- Phantom type for Plume analysis which can be used with the PDS
data PlumePds context
-- TODO: type instance definitions for "PlumePds context"

type instance Node (PlumePds context) = PdsState context
type instance NodeClass (PlumePds context) = PdsState context
type instance Element (PlumePds context) = PdsContinuation context
type instance TargetedDynPop (PlumePds context) = PdsTargetedDynamicPopAction context
type instance UntargetedDynPop (PlumePds context) = PdsUntargetedDynamicPopAction
