{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExplicitForAll #-}

module STLC.Types
    ( Id(..)
    , mkId
    , IdType(..)
    , Literal(..)
    , mkLitInt, mkLitDouble, mkLitBool, mkLitUnit
    , Type(..), LitType(..)
    ) where

import Data.Coerce (coerce)
import Data.Int(Int64)

newtype Id (ty :: IdType) = Id { unId :: String }
    deriving stock Show
    deriving newtype (Eq, Semigroup, Monoid, Ord)

data IdType
    = Unique
    | Original
    | WithType
    deriving (Show, Eq)

mkId :: forall (ty :: IdType). String -> Id ty
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


data Type (ty :: IdType)
    = TyLit LitType
    | TyArrow (Type ty) (Type ty)
    | TyTuple [Type ty]
    | TyForAll (Id ty)
    | TyVar (Id ty)
    deriving (Show, Eq)

data LitType
    = TyInt
    | TyDouble
    | TyBool
    | TyUnit
    deriving (Show, Eq)
