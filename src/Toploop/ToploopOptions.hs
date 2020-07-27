module Toploop.ToploopOptions where

import Toploop.ToploopTypes

data EvaluationMode
 = NeverEvaluate
 | SafelyEvaluate
 | AlwaysEvaluate

data Configuration 
  = Configuration 
  {
    topConfAnalyses :: [AnalysisTask],
    topConfAnalyzeVars :: AnalyzeVariablesSelection,
    topConfEvaluationMode :: EvaluationMode,
    topConfDisableInconsistencyCheck :: Bool,
    topConfDisableAnalysis :: Bool,
    topConfReportAnalysisTimes :: Bool
  }

-- TODO: context
data AnalyzeVariablesSelection 
  = AnalyzeNoVariables
  | AnalyzeToplevelVariables
  | AnalyzeSpecificVariables [(LookupVar, GraphPosition, UserContext)]
  deriving (Eq, Ord, Show)