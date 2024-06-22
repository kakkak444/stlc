{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}

module Core.Types
    ( Id(..), Literal(..)
    , mkId
    , mkLitInt, mkLitDouble, mkLitBool, mkLitUnit
    , Type(..), LitType(..)
    ) where

import Data.Coerce (coerce)
import Data.Int (Int64)

newtype Id = Id { unId :: String }
    deriving stock Show
    deriving newtype (Eq, Semigroup, Monoid, Ord)

mkId :: String -> Id
mkId = coerce


data Literal
    = LitInt Integer
    | LitDouble Rational
    | LitBool Bool
    | LitUnit
    deriving (Show, Eq)

mkLitInt :: Int64 -> Literal
mkLitInt = LitInt . toInteger

mkLitDouble :: Rational -> Literal
mkLitDouble = LitDouble

mkLitBool :: Bool -> Literal
mkLitBool = LitBool

mkLitUnit :: () -> Literal
mkLitUnit _ = LitUnit


data Type
    = TyLit LitType
    | TyArrow Type Type
    deriving (Show, Eq)

data LitType
    = TyInt
    | TyDouble
    | TyBool
    | TyUnit
    deriving (Show, Eq)
