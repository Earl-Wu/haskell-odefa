module Main where

import AST.Ast
import Interpreter.Interpreter
import qualified Data.Map as M

main :: IO ()
main =
  let test = eval (Expr([Clause(Var (Ident "x0", Nothing), ValueBody(ValueInt 5)),
                         Clause(Var (Ident "x1", Nothing), UnaryOperatorBody(UnaOpBoolNot, Var (Ident "x0", Nothing)))
                        ])) in
  case test of Left err -> putStrLn (show err)
               Right (v, env) -> let val = env M.! v in
                                 putStrLn (show val)
