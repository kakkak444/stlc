{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

module STLC.Expr
    ( Phase(..)
    , Expr(..)
    , IdTy
    ) where

import STLC.Types

data Expr (p :: Phase)
    = Var (Id (IdTy p))
    | Lam (Id (IdTy p)) (Expr p)
    | App (Expr p) (Expr p)
    | Lit Literal
    | Let (Id (IdTy p), Expr p) (Expr p)
    | If (Expr p) (Expr p) (Expr p)
    | Fix (Expr p)
    | Tuple [Expr p]
    | TupleNthElem (Expr p) Int Int
    deriving (Show)

data Phase
    = None
    | Renamed
    | TyChecked
    deriving (Show, Eq, Enum, Ord)

type family IdTy (p :: Phase) :: IdType where
    IdTy 'None = 'Original
    IdTy 'Renamed = 'Unique
    IdTy 'TyChecked = 'Unique
