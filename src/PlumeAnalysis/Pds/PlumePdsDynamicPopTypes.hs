module PlumeAnalysis.Pds.PlumePdsDynamicPopTypes where

import PdsReachability
import AST.Ast
import PlumeAnalysis.Pds.PlumePdsStructureTypes
import PlumeAnalysis.PlumeSpecification

import qualified Data.Set as S

data PdsTargetedDynamicPopAction context
  = ValueDrop
  | ValueDiscovery2of2
  | VariableAliasing AbstractVar AbstractVar
  | StatelessNonmatchingClauseSkip1of2 AbstractVar
  | StatelessNonmatchingClauseSkip2of2 (PdsContinuation context)
  | ValueCapture1of3
  | ValueCapture2of3 AbsFilteredVal
  | ValueCapture3of3 AbsFilteredVal (PdsContinuation context) BoundedCaptureSize
  | FunctionClosureLookup AbstractVar AbstractVar
  | ConditionalClosureLookup AbstractVar AbstractVar Pattern Pattern Bool
  | RecordProjectionLookup AbstractVar AbstractVar Ident
  | RecordProjection1of2
  | RecordProjection2of2 AbstractVar (S.Set Pattern) (S.Set Pattern)
  | ImmediateFilterValidation AbstractVar (S.Set Pattern) AbstractValue
  | RecordFilterValidation AbstractVar AbstractRec (Node (PlumePds context))
  | EmptyRecordValueDiscovery AbstractVar
  | BinaryOperatorLookupInit AbstractVar AbstractVar AbstractVar (Node (PlumePds context)) (Node (PlumePds context))
  | UnaryOperatorLookupInit AbstractVar AbstractVar (Node (PlumePds context))
  | BinaryOperatorResolution1of4 AbstractVar BinaryOperator
  | BinaryOperatorResolution2of4 AbstractVar BinaryOperator
  | BinaryOperatorResolution3of4 AbstractVar BinaryOperator AbstractValue
  | BinaryOperatorResolution4of4 AbstractVar AbstractValue
  | UnaryOperatorResolution1of3 AbstractVar UnaryOperator
  | UnaryOperatorResolution2of3 AbstractVar UnaryOperator
  | UnaryOperatorResolution3of3 AbstractVar AbstractValue
  deriving (Eq, Ord, Show)

data PdsUntargetedDynamicPopAction
  = DoJump
  | ValueDiscovery1of2
  deriving (Eq, Ord, Show)
