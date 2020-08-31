{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}

module Toploop.ToploopTypes where

import GHC.Generics (Generic)

import AST.Ast
import AST.AbstractAst
import AST.AstWellformedness
import Control.DeepSeq
import Interpreter.Interpreter
import Interpreter.InterpreterAst
import Toploop.ToploopAnalysisTypes

import qualified Data.Map as M
import qualified Data.Set as S

data AnalysisTask
  = PLUME Int
  | SPLUME
  -- | OSKPLUME
  -- | OSMPLUME
  deriving (Eq, Ord, Show, Generic, NFData)

newtype LookupVar = LUVar String
  deriving (Eq, Ord, Show, Generic, NFData)

data GraphPosition
  = ProgramPoint String
  | END
  deriving (Eq, Ord, Show, Generic, NFData)

-- TODO: refactor so that this can be generic.  Let a user specify the
--       context in a way dependent upon the context type rather than
--       requiring the user to produce the context via concatenation.
type UserContext = [LookupVar]

data Query = Query LookupVar GraphPosition UserContext
  deriving (Eq, Ord, Show, Generic, NFData)

data QnA = QnA Query (S.Set AbsFilteredVal)
  deriving (Eq, Ord, Show, Generic, NFData)

data AnalysisResult = AnalysisResult [QnA] [AnalysisError]
  deriving (Show, Generic, NFData)

type AnalysisReport = M.Map AnalysisTask AnalysisResult

data EvaluationResult
  = EvaluationCompleted InterpVar Environment
  | EvaluationFailure String
  | EvaluationInvalidated
  | EvaluationDisabled
  deriving (Show)

type VariableAnalysis = ((String, Maybe String, Maybe [String]), S.Set AbsFilteredVal)

data Result
  = Result
      {
        illformednesses :: [IllFormedness],
        analysisReport :: AnalysisReport,
        evaluationResult :: EvaluationResult
      }
    deriving (Show)

class (Monad m) => ToploopMonad m where
  getCallbacks :: m (Callbacks m)
  -- Given a monadic operation, how long does it take (in ms) to compute?
  time :: (NFData x) => m x -> m (x, Integer)
  toploopIllformednesses :: [IllFormedness] -> m ()
  toploopIllformednesses ills = do
    cb <- getCallbacks
    (cbIllformednesses cb) ills
  toploopVariableAnalysis :: LookupVar
                          -> GraphPosition
                          -> UserContext
                          -> S.Set AbsFilteredVal
                          -> String
                          -> m ()
  toploopVariableAnalysis var graphPos ctx absfiltval analysisName = do
    cb <- getCallbacks
    (cbVariableAnalysis cb) var graphPos ctx absfiltval analysisName
  toploopEvaluationDisabled :: () -> m ()
  toploopEvaluationDisabled () = do
    cb <- getCallbacks
    (cbEvaluationDisabled cb) ()
  toploopEvaluationResult :: InterpVar -> Environment -> m ()
  toploopEvaluationResult v env = do
    cb <- getCallbacks
    (cbEvaluationResult cb) v env
  toploopErrors :: [AnalysisError] -> m ()
  toploopErrors errors = do
    cb <- getCallbacks
    (cbErrors cb) errors
  toploopAnalysisTimeReport :: Integer -> m ()
  toploopAnalysisTimeReport time = do
    cb <- getCallbacks
    (cbAnalysisTimeReport cb) time

data Callbacks m
  = Callbacks
      { cbIllformednesses :: [IllFormedness] -> m (),
        cbVariableAnalysis :: 
          LookupVar -> GraphPosition -> 
          UserContext ->
          S.Set AbsFilteredVal -> String -> m (),
        cbErrors :: [AnalysisError] -> m (),
        cbEvaluationResult :: InterpVar -> Environment -> m (),
        cbEvaluationFailed :: String -> m (),
        cbEvaluationDisabled :: () -> m (),
        cbAnalysisTimeReport:: Integer -> m ()
        -- TODO: Do we need this?
        -- cbSourceStatisticsCallback ::           
      }

