module Core
    ( Expr(..)
    , Type(..)
    , LitType(..)
    , getType
    , isValidExpr
    , TyEnv
    ) where

import Core.Expr
import Core.Types
import Core.TypeCheck