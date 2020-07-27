module Utils.Exception
( InvariantFailureException(..),
  InvalidVariableAnalysis(..)
) where

import Control.Exception

data InvariantFailureException = InvariantFailureException String
  deriving (Show)

instance Exception InvariantFailureException

data InvalidVariableAnalysis = InvalidVariableAnalysis String
  deriving (Show)

instance Exception InvalidVariableAnalysis
