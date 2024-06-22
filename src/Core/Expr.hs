module Core.Expr
    ( Expr(..)
    ) where

import Core.Types

data Expr
    = Var Id
    | Lam (Id, Type) Expr
    | App Expr Expr
    | Lit Literal
    | Let (Id, Expr) Expr
    | If Expr Expr Expr
    | Fix Expr
    deriving Show
