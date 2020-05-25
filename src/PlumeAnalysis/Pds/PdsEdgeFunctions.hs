module PlumeAnalysis.Pds.PdsEdgeFunctions where

import PdsReachability
import PlumeAnalysis.Context
import PlumeAnalysis.PlumeSpecification
import PlumeAnalysis.Types.PlumeGraph
import PlumeAnalysis.Pds.PlumePdsStructureTypes

createEdgeFunction ::
  (Context context) => CFGEdge context -> EdgeFunction (PlumePds context)
createEdgeFunction =
  -- TODO: note that this has to handle both the "createEdgeFunction" from the
  -- original code as well as the original code's
  -- "createDynamicPopActionFunction"
  -- let CFGEdge n1 n2 = edge in
    undefined
