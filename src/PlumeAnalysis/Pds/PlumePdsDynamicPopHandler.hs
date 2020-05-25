module PlumeAnalysis.Pds.PlumePdsDynamicPopHandler where

import PdsReachability
import PlumeAnalysis.PlumeSpecification

plumeTargetedDynPop ::
  TargetedDynPop (PlumePds context) ->
  Element (PlumePds context) ->
  [Path (PlumePds context)]
plumeTargetedDynPop targetedDynPop element = undefined

plumeUntargetedDynPop ::
  UntargetedDynPop (PlumePds context) ->
  Element (PlumePds context) ->
  [(Path (PlumePds context), Terminus (PlumePds context))]
plumeUntargetedDynPop untargetedDynPop element = undefined
