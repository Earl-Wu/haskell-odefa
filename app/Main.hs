{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Main where

import AST.AbstractAst
import AST.Ast
import AST.AstUtils
import AST.AstWellformedness
import Interpreter.Interpreter
import Interpreter.InterpreterAst
import Parser.Parser
import Parser.Lexer
import Toploop.Toploop
import Toploop.ToploopAnalysisTypes
import Toploop.ToploopTypes
import Toploop.ToploopOptions
import Utils.Exception

import Control.DeepSeq
import Control.Exception
import Control.Monad
import Data.Char
import Data.Fixed
import Data.Function
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Time.Clock.System
import GHC.Generics (Generic)
import System.Environment
import System.IO

parseFile :: FilePath -> IO (ConcreteExpr)
parseFile f = do
  contents <- readFile f
  let tokenList = alexScanTokens contents
  let ast = parseProgram tokenList
  return ast

stdoutCallbacks :: Callbacks MainMonad
stdoutCallbacks = Callbacks
      { cbIllformednesses = stdoutIllformednessesCallback,
        cbVariableAnalysis = stdoutVariableAnalysisCallback,
        cbErrors = stdoutErrorsCallback,
        cbEvaluationResult = stdoutEvaluationResultCallback,
        cbEvaluationFailed = stdoutEvaluationFailedCallback,
        cbEvaluationDisabled = stdoutEvaluationDisabledCallback,
        cbAnalysisTimeReport = stdoutAnalysisTimeReportCallback
      }

newtype MainMonad x = MainMonad (IO x)
  deriving (Functor, Applicative, Monad)
instance ToploopMonad MainMonad where
  getCallbacks = MainMonad $ pure $ stdoutCallbacks
  
  --time :: MainMonad a -> MainMonad (a, Integer)
  time m =
    do
      startTime <- MainMonad getSystemTime
      a <- m
      endTime <- deepseq a (MainMonad getSystemTime)
      let systemTimeToMs (MkSystemTime secs picoseconds) =
            toInteger secs * 1000 + toInteger picoseconds `div` 1000000000
      let startMs = systemTimeToMs startTime
      let endMs = systemTimeToMs endTime
      return (a, endMs - startMs)
    
runMainMonad (MainMonad m) = m  

mainPutStr :: String -> MainMonad ()
mainPutStr = MainMonad . putStr

mainPutStrLn :: String -> MainMonad ()
mainPutStrLn = MainMonad . putStrLn

stdoutIllformednessesCallback :: [IllFormedness] -> MainMonad ()
stdoutIllformednessesCallback ills = do
  mainPutStrLn "Provided expression is ill-formed:\n"
  forM_ ills (\ill -> mainPutStrLn $ ("  " ++ show ill))

stdoutVariableAnalysisCallback :: 
  LookupVar -> 
  GraphPosition -> 
  UserContext ->
  S.Set AbsFilteredVal -> 
  String ->
  MainMonad ()
stdoutVariableAnalysisCallback varName siteName userContext values analysisName =
  let (LUVar varStr) = varName in
  do
    mainPutStrLn (analysisName ++ ": ")
    mainPutStr ("Lookup of variable " ++ varStr)    
    case siteName of
      ProgramPoint siteNameStr ->
        mainPutStr (" from clause " ++ siteNameStr)
      END -> return $ ()
    case userContext of
      [] -> return $ ()
      contextList -> do
        mainPutStr " in context "
        let loop = \ss -> 
              case ss of
                [] -> mainPutStr "[]"
                LUVar s : [] -> mainPutStr s
                LUVar s : ss' -> do
                  mainPutStr s
                  mainPutStr ","
                  loop ss'
        loop contextList
    mainPutStrLn " yields values:"
    mainPutStr "   "
    mainPutStrLn $ show values

stdoutErrorsCallback :: [AnalysisError] -> MainMonad ()
stdoutErrorsCallback errors =
  forM_ errors (\error -> mainPutStrLn $ show error)

stdoutEvaluationResultCallback :: InterpVar -> Environment -> MainMonad ()
stdoutEvaluationResultCallback v env =
  mainPutStrLn $ show v ++ " where " ++ showEnvironment env 

stdoutEvaluationFailedCallback :: String -> MainMonad ()
stdoutEvaluationFailedCallback msg = 
  mainPutStrLn $ "Evaluation failed: " ++ msg

stdoutEvaluationDisabledCallback :: () -> MainMonad ()
stdoutEvaluationDisabledCallback () =
  mainPutStrLn "Evaluation disabled"

stdoutAnalysisTimeReportCallback :: Integer -> MainMonad ()
stdoutAnalysisTimeReportCallback time = 
  mainPutStrLn $ "Analysis took " ++ show time ++ " ms." 

handleExpr ::  Configuration -> ConcreteExpr -> IO Result
handleExpr conf expr = do
  -- Make call to the handleExpression in Toploop
  -- Note that the toploop will print things for us if we give it the right
  -- callbacks
  runMainMonad $ handleExpression stdoutCallbacks conf expr

-- parseCLIArgs :: Configuration -> [String] -> (Configuration, [String])
-- parseCLIArgs configuration arguments =
--   case arguments of
--     [] -> (configuration, [])
--     "-A" : arguments' ->
--       let configuration' =
--             configuration { topConfAnalyzeVars = AnalyzeNoVariables, 
--                             topConfDisableAnalysis = True
--                           }
--       in
--       parseCLIArgs configuration' arguments'
--     "-I" : arguments' ->
--       let configuration' =
--             configuration { topConfDisableInconsistencyCheck = True }
--       in
--       parseCLIArgs configuration' arguments'
--     "-E" : arguments' ->
--       let configuration' =
--             configuration { topConfEvaluationMode = NeverEvaluate }
--       in
--       parseCLIArgs configuration' arguments'
--     "--report-analysis-time" : arguments' ->
--       let configuration' =
--             configuration { topConfReportAnalysisTimes = True }
--       in
--       parseCLIArgs configuration' arguments'
--     "--select-analysis" : analysisLst : arguments' ->
--       let analyses = stringSplit ',' analysisLst in
--       let addAnalysis conf analysisName = 
--             case analysisName of
--               "splume" ->
--                 let analysisTask = topConfAnalyses conf in
--                 conf { topConfAnalyses =  SPLUME : analysisTask}
--               num : analysisName' ->
--                 -- TODO: issue - cannot parse number > 9
--                 if (isDigit num) 
--                 then 
--                   if analysisName' == "plume" then
--                     let analysisTask = topConfAnalyses conf in
--                     let n = digitToInt num in
--                     conf { topConfAnalyses = PLUME n : analysisTask }
--                   else
--                   -- TODO: Report Error 
--                     undefined
--                 else
--                   -- TODO: Report Error 
--                   undefined
--       in
--       let configuration' = L.foldl addAnalysis configuration analyses in
--       parseCLIArgs configuration' arguments'
--     "--analyze-all-variables" : arguments' ->
--       let configuration' =
--             configuration { topConfAnalyzeVars =  AnalyzeToplevelVariables }
--       in
--       parseCLIArgs configuration' arguments'
--     "--analyze-no-variables" : arguments' ->
--       let configuration' =
--             configuration { topConfAnalyzeVars =  AnalyzeNoVariables }
--       in
--       parseCLIArgs configuration' arguments'
--     "--analyze-variable" : spec : arguments' ->
--       {-
--         a spec is of the following form:
--           var@loc:stackel,stackel,...
--       -}
--       let (varname, afterVarname) = break (=='@') spec in
--       let (loc, stack) =
--             case afterVarname of
--               [] -> (END, [])
--               _ : afterVarname' ->
--                 let (locationName, afterLocationName) =
--                       break (==':') afterVarname'
--                 in
--                 case afterLocationName of
--                   [] -> (ProgramPoint locationName, [])
--                   _ : afterLocationName' ->
--                     let ctxLst = stringSplit ',' afterLocationName' in
--                     (ProgramPoint locationName, L.map (\c -> LUVar c) ctxLst)
--       in
--       case topConfAnalyzeVars configuration of
--         AnalyzeToplevelVariables ->
--           {- TODO: error -}
--           undefined
--         AnalyzeNoVariables ->
--           let configuration' =
--                 configuration
--                   { topConfAnalyzeVars = AnalyzeSpecificVariables $
--                       (LUVar varname, loc, stack) : []
--                   }
--           in
--           parseCLIArgs configuration' arguments'
--         AnalyzeSpecificVariables lookups ->
--           let configuration' =
--                 configuration
--                   { topConfAnalyzeVars = AnalyzeSpecificVariables $
--                       (LUVar varname, loc, stack) : lookups
--                   }
--           in
--           parseCLIArgs configuration' arguments'
--     ["--select-analysis"] -> missingArgument
--     otherArg ->
--       -- If otherArg starts with "-" then complain.
--       -- Otherwise, do nothing and be finished.
--       if (L.any (\(c : rest) -> c == '-') otherArg)
--       then throw InvalidArgument
--       else (configuration, otherArg)
      
--   where
--     missingArgument =
--       throw MissingCommandLineArgument

-- defaultConfiguration :: Configuration
-- defaultConfiguration = Configuration 
--   {
--     topConfAnalyses = [],
--     topConfAnalyzeVars = AnalyzeNoVariables,
--     topConfEvaluationMode = NeverEvaluate,
--     topConfDisableInconsistencyCheck = False,
--     topConfDisableAnalysis = False,
--     topConfReportAnalysisTimes = False
--   }

main :: IO ()
main =
  do
    args <- getArgs
    let (spareArgs, configuration) = parseCLIArgs args
    case spareArgs of
      [] -> do
        text <- getContents
        let tokenList = alexScanTokens text
        putStrLn (show tokenList)
        (pure $ parseProgram tokenList) >>= (handleExpr configuration)
        return () 
      [filename] -> do -- read from file
        (parseFile filename) >>= (handleExpr configuration)
        return ()
      otherwise ->
        throw $ TooManyCommandLineArguments -- complain about too many arguments
