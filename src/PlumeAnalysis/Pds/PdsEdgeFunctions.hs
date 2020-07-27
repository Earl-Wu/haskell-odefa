module PlumeAnalysis.Pds.PdsEdgeFunctions where

import AST.Ast
import AST.AbstractAst
import PdsReachability
import PlumeAnalysis.Context
import PlumeAnalysis.PlumeSpecification
import PlumeAnalysis.Types.PlumeGraph
import PlumeAnalysis.Pds.PlumePdsDynamicPopTypes
import PlumeAnalysis.Pds.PlumePdsStructureTypes
import PlumeAnalysis.Utils.PlumeUtils

import Control.Monad
import Data.Function
import qualified Data.List as L
import qualified Data.Maybe as MB

createEdgeFunction ::
  (Context context) => CFGEdge context -> EdgeFunction (PlumePds context)
createEdgeFunction edge = EdgeFunction $ \state ->
  -- TODO: note that this has to handle both the "createEdgeFunction" from the
  -- original code as well as the original code's
  -- "createDynamicPopActionFunction"
  let CFGEdge n1 n0 = edge in
  case state of
    ProgramPointState n0' ->
      if (n0 == n0') then
        let targetedDynamicPops = MB.catMaybes $
               [ -- Variable Discovery
                 -- Intermediate Value
                 return (ValueDrop, ProgramPointState n0)
                 -- Variable Search
                 -- Value Alias
               , case n1 of
                    CFGNode (UnannotatedClause (Clause x (VarBody x'))) _ ->
                      return (VariableAliasing x x', ProgramPointState n1)
                    otherwise -> mzero
                 -- Clause Skip
               , case n1 of
                    CFGNode (UnannotatedClause (Clause x _)) _ ->
                      return (StatelessNonmatchingClauseSkip1of2 x, ProgramPointState n1)
                    otherwise -> mzero
                 -- Navigation
                 -- Capture
               , return (ValueCapture1of3, ProgramPointState n0)
                 -- Function Wiring
                 -- Function Top: Parameter Variable
               , case n1 of
                    CFGNode (EnterClause x x' c) _ ->
                      case c of
                        -- NOTE: ignoring call site annotations
                        -- as none apply to Plume lookup.
                        Clause _ (ApplBody _ x3'' _) ->
                          if not (x' == x3'') then undefined
                          else
                            return (VariableAliasing x x', ProgramPointState n1)
                    otherwise -> mzero
                 -- Function Bottom: Return Variable
               , case n1 of
                    CFGNode (ExitClause x x' c) _ ->
                      case c of
                        Clause x1'' (ApplBody _ _ _) ->
                          if not (x == x1'') then undefined
                          else
                            return (VariableAliasing x x', ProgramPointState n1)
                    otherwise -> mzero
                 -- Function Top: Non-local Variable
               , case n1 of
                    CFGNode (EnterClause x'' x' c) _ ->
                      case c of
                        Clause _ (ApplBody x2'' x3'' _) ->
                          if not (x' == x3'') then undefined
                          else
                            return (FunctionClosureLookup x'' x2'', ProgramPointState n1)
                    otherwise -> mzero
                 -- Condtional Wiring
                 -- Conditional Top: Subject Positive
                 -- Conditional Top: Subject Negative
                 -- Conditional Top: Non-subject Variable
               , case n1 of
                    -- This block represents *all* conditional closure handling
                    -- on the entering side.
                    CFGNode (EnterClause x' x1 c) _ ->
                      case c of
                        Clause _ (ConditionalBody x1' p f1 _) ->
                          if not (x1 == x1') then undefined
                          else
                            let FunctionValue f1x _ = f1 in
                            let closureForPositivePath = (f1x == x') in
                            return (ConditionalClosureLookup x' x1 p closureForPositivePath,
                                    ProgramPointState n1)
                    otherwise -> mzero
               , case n1 of
                    CFGNode (ExitClause x x' c) _ ->
                      case c of
                        Clause x2 (ConditionalBody _ _ _ _) ->
                          if not (x == x2) then undefined
                          else
                            return (VariableAliasing x x',
                                    ProgramPointState n1)
                    otherwise -> mzero
                 -- Record Construction/Destruction
                 -- Record Projection Start
               , case n1 of
                    CFGNode (UnannotatedClause (Clause x (ProjectionBody x' l))) _ ->
                      return (RecordProjectionLookup x x' l,
                              ProgramPointState n1)
                    otherwise -> mzero
                 -- Record Projection Stop
               , return (RecordProjection1of2, ProgramPointState n0)
                 -- Filter Validation
                 -- Filter Immediate
               , case n1 of
                    CFGNode (UnannotatedClause (Clause x (ValueBody v))) _ ->
                      do
                        immediatePatterns <- immediatelyMatchedBy v
                        return (ImmediateFilterValidation x immediatePatterns v,
                                ProgramPointState n1)
                    otherwise -> mzero
                 -- Filter Record
               , case n1 of
                    CFGNode (UnannotatedClause (Clause x (ValueBody (AbsValueRecord r)))) _ ->
                      let targetState = ProgramPointState n1 in
                      return (RecordFilterValidation x r n1, targetState)
                    otherwise -> mzero
                 -- Operations
                 -- Binary Operation Start
               , case n1 of
                    CFGNode (UnannotatedClause (Clause x1 (BinaryOperationBody x2 _ x3))) _ ->
                      return (BinaryOperatorLookupInit x1 x2 x3 n1 n0,
                              ProgramPointState n1)
                    otherwise -> mzero
                 -- Binary Operation Evaluation
               , case n1 of
                    CFGNode (UnannotatedClause (Clause x1 (BinaryOperationBody _ op _))) _ ->
                      return (BinaryOperatorResolution1of4 x1 op,
                              ProgramPointState n1)
                    otherwise -> mzero
                 -- Unary Operation Start
               , case n1 of
                    CFGNode (UnannotatedClause (Clause x1 (UnaryOperationBody _ x2))) _ ->
                      return (UnaryOperatorLookupInit x1 x2 n0,
                              ProgramPointState n1)
                    otherwise -> mzero
                  -- Unary Operation Evaluation
               ,  case n1 of
                    CFGNode (UnannotatedClause (Clause x1 (UnaryOperationBody op _))) _ ->
                      return (UnaryOperatorResolution1of3 x1 op,
                              ProgramPointState n1)
                    otherwise -> mzero
               ]
        in
        let CFGNode acl1 _ = n1 in
        let nopStates =
              case acl1 of
                StartClause _ -> [ProgramPointState n1]
                EndClause _ -> []
        in
        let targetedPopEdges =
              targetedDynamicPops
              & L.map (\(action, state) -> (Path [DynamicPop action], StaticTerminus state))
        in
        let nopEdges =
              nopStates
              & L.map (\state -> (Path [], StaticTerminus state))
        in
        let untargetedPopEdges =
              [ (Path [], DynamicTerminus ValueDiscovery1of2)
              , (Path [], DynamicTerminus DoJump)
              ]
        in
        targetedPopEdges ++ nopEdges ++ untargetedPopEdges
      else []
    otherwise -> []
