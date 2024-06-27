{-# LANGUAGE LambdaCase #-}

module CoreToZINC
    ( coreToZinc
    ) where

import Core.Expr as C
import Core.Types
import ZINC as Z

import Data.List (elemIndex)
import Data.Maybe
import Data.Bifunctor
import Control.Monad.Reader

type Globl = [Id]
type Env = ([Id], Globl)

coreToZinc :: Globl -> [Expr] -> Code
coreToZinc env progs = flip runReader ([], env) $ concat <$> mapM c progs

c :: Expr -> Reader Env Code
c = \case
    Var x -> do
        -- n <- fromJust <$> findLocal x
        -- return [Access $ toInteger n]
        n <- findLocal x
        case n of
            Just n' -> return [Access n']
            Nothing -> do
                n' <- fromJust <$> findGlobal x
                return [AccessGlbl n']
    App e1 eN -> do
        e1' <- flatApp e1
        eN' <- c eN
        return $ PushMark : eN' ++ e1' ++ [Apply]
    Lam (x, _) e -> do
        e' <- withNewVar x $ t e
        return [Cur $ e' ++ [Return]]
    C.Let (x, e) expr -> do
        e' <- c e
        expr' <- withNewVar x $ c expr
        return $ e' ++ [Z.Let] ++ expr' ++ [EndLet]
    Lit lit -> return [ case lit of
            LitInt i -> LoadInt i
            LitBool b -> LoadBool b
            LitDouble d -> LoadDouble d
            LitUnit -> LoadUnit
        ]
    If cond e1 e2 -> do
        cond' <- c cond
        e1' <- c e1
        e2' <- c e2
        return $ cond' ++ [Test e1' e2']
    C.Fix e -> do
        e' <- c e
        return $ e' ++ [Z.Fix]


t :: Expr -> Reader Env Code
t = \case
    Var x -> do
        n <- fromJust <$> findLocal x
        return $ [Access n]
    App e1 eN -> do
        e1' <- flatApp e1
        eN' <- c eN
        return $ eN' ++ e1' ++ [AppTerm]
    Lam (x, _) e -> do
        e' <- withNewVar x $ t e
        return $ Grab : e'
    C.Let (x, e) expr -> do
        e' <- c e
        expr' <- withNewVar x $ t expr
        return $ e' ++ [Z.Let] ++ expr'
    Lit lit -> return [ case lit of
            LitInt i -> LoadInt i
            LitBool b -> LoadBool b
            LitDouble d -> LoadDouble d
            LitUnit -> LoadUnit
        ]
    If cond e1 e2 -> do
        cond' <- c cond
        e1' <- t e1
        e2' <- t e2
        return $ cond' ++ [Test e1' e2']
    C.Fix e -> do
        e' <- c e
        return $ e' ++ [Z.Fix]

findLocal :: Id -> Reader Env (Maybe Int)
findLocal x = asks (elemIndex x . fst)

findGlobal :: Id -> Reader Env (Maybe Int)
findGlobal x = asks (elemIndex x . snd)

withNewVar :: Id -> Reader Env a -> Reader Env a
withNewVar x = local $ first (x:)

flatApp :: Expr -> Reader Env Code
flatApp (App e1 e2) = do
    e1' <- flatApp e1
    e2' <- c e2
    return $ Push : e2' ++ e1'
flatApp e = (Push :) <$> c e
