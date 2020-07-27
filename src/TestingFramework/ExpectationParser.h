{

module TestingFramework.ExpectationParser where

import ASTT.Ast
import TestingFramework.ExpectationLexer
import qualified TestingFramework.Token as TT
import qualified Data.Map as M
import qualified Data.Set as S

}

%name parseExpectation Expectation

%tokentype { TT.TestToken }

%error{ parseError }

%token

      "@"           { TT.AT }
      "&"           { TT.AMPERSAND }
      ":"           { TT.COLON }
      ";"           { TT.SEMICOLON }
      ","           { TT.COMMA }
      "="           { TT.EQUAL }
      "("           { TT.OPENPAREN }
      ")"          { TT.CLOSEPAREN }
      "["           { TT.OPENBRACKET }
      "]"           { TT.CLOSEBRACKET }
      "QUERY"           { TT.QUERY }
      "ANALYSES"           { TT.ANALYSES }
      "RESULTS" { TT.RESULTS }
      "CONSISTENCIES"           { TT.CONSISTENCIES }
      "WELL_FORMED"           { TT.WELL_FORMED }
      "ILL_FORMED"           { TT.ILL_FORMED }
      "STUCK"           { TT.STUCK }
      "NO_INCONSISTENCIES"           { TT.NO_INCONSISTENCIES }
      "INCONSISTENCIES_AT"           { TT.INCONSISTENCIES_AT }
      "DDPA"           { TT.DDPA }
      "PLUME"           { TT.PLUME }
      "SPLUME"           { TT.SPLUME }
      "OSKPLUME"           { TT.OSKPLUME }
      "OSMPLUME"           { TT.OSMPLUME }
      int				    { TT.INTEGER $$ }
      id	        { TT.IDENTIFIER $$ }
      id          { TT.OUTPUT $$ }

%%

Prog : ExpectationFile { $1 }

ExpectationFile
  : AnalysisExpectation ExpectationList { Expectations (Just $1) $2 }
  | ExpectationList { Expectations Nothing $1 }

AnalysisExpectation : QUERY COLON QueryList SEMICOLON
                      ANALYSES COLON AnalysisList SEMICOLON
                      RESULTS COLON ResultList SEMICOLON
                      CONSISTENCIES COLON AnalysisConsistencyExpectationList SEMICOLON
                      { AnalysisExpectation ($3, $7, $11, $15) }
                    | QUERY COLON SEMICOLON
                      ANALYSES COLON AnalysisList SEMICOLON
                      RESULTS COLON SEMICOLON
                      CONSISTENCIES COLON AnalysisConsistencyExpectationList SEMICOLON
                      { AnalysisExpectation ([], $6, [], $13)}
                    | QUERY COLON QueryList SEMICOLON
                      ANALYSES COLON AnalysisList SEMICOLON
                      RESULTS COLON ResultList SEMICOLON
                      CONSISTENCIES COLON SEMICOLON
                      { AnalysisExpectation ($3, $7, $11, [])}
                    | QUERY COLON SEMICOLON
                      ANALYSES COLON AnalysisList SEMICOLON
                      RESULTS COLON SEMICOLON
                      CONSISTENCIES COLON SEMICOLON
                      { AnalysisExpectation ([], $6, [], [])}

ExpectationList : Expectation SEMICOLON ExpectationList { $1 : $3 }
                | Expectation SEMICOLON { [$1] }

Expectation: EVALUATE { ExpectEvaluate }
           | STUCK { ExpectStuck }
           | WELL_FORMED { ExpectWellFormed }
           | ILL_FORMED { ExpectIllFormed }

AnalysisConsistencyExpectationList
  : AnalysisConsistencyExpectation AMPERSAND AnalysisConsistencyExpectationList { $1 : $3 }
  | AnalysisConsistencyExpectation { [$1] }

InconsistenciesList
  : Inconsistency COMMA InconsistenciesList
    { $1 : $3 }
  | Inconsistency
    { [$1] }

ResultList : Result COMMA ResultList { case $1 of
                                         Just n -> n:$3
                                         Nothing -> $3 }
           | Result { maybeToList $1 }

QueryList : Query COMMA QueryList { $1 : $3 }
          | Query { [$1] }

AnalysisList : Analysis COMMA AnalysisList { $1 : $3 }
             | Analysis { [$1] }

AnalysisConsistencyExpectation : Analysis EQUAL Consistency { ($1, $3) }

Inconsistency: INCONSISTENCIES_AT LookupVar { ExpectAnalysisInconsistencyAt $2 }

Consistency : NO_INCONSISTENCIES { ExpectAnalysisNoInconsistencies }
            | InconsistenciesList { ExpectAnalysisInconsistencyAt $1 }

Result : Analysis OPENPAREN QUERY CLOSEPAREN EQUAL ExpectedOutput { fmap (\analysis -> Result analysis $3 $6) $1 }

Query : LookupVar AT GraphPosition AT OPENBRACKET Context CLOSEBRACKET { Query $1 $3 $6 }
      | LookupVar AT GraphPosition { Query $1 $3 [] }
      | LookupVar { Query $1 END [] }

Analysis : int PLUME { Just $ PLUME $1 }
         | SPLUME { Just $ SPLUME }
         | int DDPA { Nothing }
         | DDPA { Nothing }

Context : LookupVar COMMA LookupVarList { $1 : $3 }

GraphPosition : id { ProgramPoint $1 }

ExpectedOutput : OUTPUT { ResultString $1 }

LookupVarList : LookupVar { [$1] }
              | LookupVar COMMA LookupVarList { $1 : $3 }

LookupVar : id { LUVar $1 }

{
parseError :: [TT.TestToken] -> a
parseError _ = error "Parse error"
}
