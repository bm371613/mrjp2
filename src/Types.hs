module Types (ClsSig(..), ClsSigItem(..), FunSig(..), Globals(..)) where

import Data.Map (Map)

import Parser.AbsLatte

data FunSig = FunSig Type [Type] deriving (Show, Eq)

data ClsSig = ClsSig
    { superNames :: [String]
    , clsItems ::[ClsSigItem]
    } deriving (Show)
data ClsSigItem = Attr String Type | Method String FunSig deriving (Show)

data Globals = Globals
    { classes :: (Map String ClsSig)
    , functions :: (Map String FunSig)
    } deriving (Show)

instance Named ClsSigItem where
    name (Attr name _) = name
    name (Method name _) = name

