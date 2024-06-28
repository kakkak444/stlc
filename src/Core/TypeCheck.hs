{-# LANGUAGE LambdaCase #-}

module Core.TypeCheck
    ( getType
    , isValidExpr
    , TyEnv
    ) where

import Core.Types
import Core.Expr

import qualified Data.Map.Strict as M
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad

type TyEnv = M.Map Id Type

isValidExpr :: TyEnv -> Expr -> Bool
isValidExpr env e = either (const False) (const True) $ runReaderT (getType e) env

getType :: Expr -> ReaderT TyEnv (Either ()) Type
getType = \case
    Var x -> do
        b <- asks $ M.lookup x
        case b of
            Nothing -> throwError ()
            Just b' -> return b'
    Lam (x, t) e -> do
        te <- local (M.insert x t) $ getType e
        return $ TyArrow t te
    App e1 e2 -> do
        te1 <- getType e1
        te2 <- getType e2
        case (te1, te2) of
            (TyArrow t1 t2, t3)
                | t1 == t3 -> return t2
            _ -> throwError ()
    Lit lit -> return $ TyLit $ case lit of
        LitInt _ -> TyInt
        LitDouble _ -> TyDouble
        LitBool _ -> TyBool
        LitUnit -> TyUnit
    Let (x, e) expr -> do
        tx <- getType e
        local (M.insert x tx) $ getType expr
    If cond e1 e2 -> do
        tcond <- getType cond
        te1 <- getType e1
        te2 <- getType e2
        case tcond of
            TyLit TyBool
                | te1 == te2 -> return te1
            _ -> throwError ()
    Fix e -> do
        te <- getType e
        case te of
            TyArrow te1 te2
                | te1 == te2 -> return te1
            _ -> throwError ()
    Tuple xs -> do
        types <- forM xs getType
        return $ TyTuple types
    TupleNthElem expr idx -> do
        t <- getType expr
        case t of
            TyTuple ts
                | length ts > idx -> return $ ts !! idx
            _ -> throwError ()
