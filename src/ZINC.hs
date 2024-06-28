module ZINC
    ( Instruction(..)
    , PrimOp(..)
    , Code
    ) where

data Instruction
    = Access Int
    | AccessGlbl Int
    | AppTerm
    | Apply
    | Push
    | PushMark
    | Cur Code
    | Fix
    | Grab
    | Return
    | Let
    | EndLet

    | LoadInt Integer
    | LoadBool Bool
    | LoadDouble Rational
    | LoadUnit
    | Test Code Code
    | Prim PrimOp
    deriving (Show)

data PrimOp
    = Add | Sub | Mul | Div
    | Eq | Lt | Gt
    | Le | Ge
    | TupleNthElem Int | MkTuple Int
    deriving (Show, Eq, Ord)

type Code = [Instruction]
