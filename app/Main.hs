module Main where

import AST.Ast
import Interpreter.Interpreter
import Parser.Parser
import Parser.Lexer
import qualified Data.Map as M

parseFile :: FilePath -> IO ()
parseFile f = do
  contents <- readFile f
  let tokenList = alexScanTokens contents
  -- putStrLn (show tokenList)
  let ast = parseExpr tokenList
  -- putStrLn (show ast)
  let res = eval ast
  case res of Left err -> putStrLn (show err)
              Right (v, env) -> let val = env M.! v in
                                 putStrLn (show v ++ ": " ++ show val)

main :: IO ()
main = do
  text <- getLine
  parseFile text

-- main :: IO ()
-- main = do
--   text <- getLine
--   let tokenList = alexScanTokens text
--   putStrLn (show tokenList)
--   let ast = parseExpr tokenList
--   let test = eval ast
--   case test of Left err -> putStrLn (show err)
--                Right (v, env) -> let val = env M.! v in
--                                  putStrLn (show val)
