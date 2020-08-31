module Utils.Exception
( InvariantFailureException(..),
  InvalidVariableAnalysis(..),
  MissingCommandLineArgument(..),
  TooManyCommandLineArguments(..),
  InvalidArgument(..)
) where

import Control.Exception

data InvariantFailureException = InvariantFailureException String
  deriving (Show)

instance Exception InvariantFailureException

data InvalidVariableAnalysis = InvalidVariableAnalysis String
  deriving (Show)

instance Exception InvalidVariableAnalysis

data MissingCommandLineArgument = MissingCommandLineArgument
  deriving (Show)

instance Exception MissingCommandLineArgument

data TooManyCommandLineArguments = TooManyCommandLineArguments
  deriving (Show)

instance Exception TooManyCommandLineArguments

data InvalidArgument = InvalidArgument
  deriving (Show)

instance Exception InvalidArgument