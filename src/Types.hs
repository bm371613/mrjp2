module Types (ClsSig(..), ClsSigItem(..), FunSig(..), Globals(..)) where

import Data.Map (Map)

import Parser.AbsLatte

data FunSig = FunSig Type [Type] deriving (Show)

data ClsSig = ClsSig (Maybe String) [ClsSigItem] deriving (Show)
data ClsSigItem = Attr String Type | Method String FunSig deriving (Show)

data Globals = Globals (Map String ClsSig) (Map String FunSig) deriving (Show)


