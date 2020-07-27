module Toploop.ToploopUtils where

import AST.Ast
import AST.AbstractAst
import PlumeAnalysis.PlumeAnalysis

import qualified Data.List as L

plumeAnalysisToStack name = undefined

lastVarOf :: ConcreteExpr -> AbstractVar
lastVarOf (Expr cls) = 
    let Clause x _ = L.last cls in x

expressionOf :: PlumeAnalysis context -> ConcreteExpr
expressionOf = undefined

iterateAbstractClauses :: AbstractExpr -> b
iterateAbstractClauses = undefined
