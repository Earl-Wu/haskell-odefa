module AST.AstWellformedness where

import AST.Ast
import AST.AstUtils
import Data.Function
import qualified Data.List as L
import qualified Data.Set as S

data Illformedness
  = DuplicateVariableBinding ConcreteVar
  | VariableNotInScope (ConcreteVar, ConcreteVar) deriving (Eq, Ord, Show)

checkWellformedExpr :: ConcreteExpr -> Either [Illformedness] ()
checkWellformedExpr expr =
  let exprNonUniqueBindings = nonUniqueBindings expr in
  if not (S.null exprNonUniqueBindings) then
    let illformedness =
          exprNonUniqueBindings
          & S.toList
          & L.map (\nonUniqueBinding -> DuplicateVariableBinding nonUniqueBinding)
    in Left illformedness
  else
    let exprScopeViolations = scopeViolations expr in
    if not (L.null exprScopeViolations) then
      let illformedness =
            exprScopeViolations
            & L.map (\(programPoint, dependency) -> VariableNotInScope (programPoint, dependency))
      in Left illformedness
    else Right ()
