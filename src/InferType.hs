{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module InferType
    ( infer
    , runInferer
    ) where

import STLC.Types
import STLC.Expr

import Data.Maybe (maybe, fromMaybe)
import Data.Coerce (coerce)
import Control.Monad
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Except

type Env = M.Map (Id 'Unique) (Type 'Unique)
type Subst = M.Map (Id 'Unique) (Type 'Unique)
newtype TyEnv = TyEnv (M.Map (Id 'Unique) (Scheme 'Unique))

newtype Inferer a = Inferer (ReaderT Env (StateT Int (Except String)) a)
    deriving
        ( Functor, Applicative, Monad
        , MonadReader Env
        , MonadState  Int
        , MonadError  String
        )

instance MonadFail Inferer where
    fail = throwError

runInferer :: Inferer a -> Env -> Int -> Either String (a, Int)
runInferer (Inferer i) e c = runExcept $ flip runStateT c $ runReaderT i e


infer :: M.Map (Id 'Unique) (Scheme 'Unique) -> Expr 'Renamed -> Inferer (Type 'Unique)
infer env e = do
    (s, t) <- inferExpr (TyEnv env) e
    return $ apply s t

inferExpr :: TyEnv -> Expr 'Renamed -> Inferer (Subst, Type 'Unique)
inferExpr tyenv@(TyEnv env) = \case
    Var x -> case env M.!? x of
        Nothing -> fail $ "unbound variable `" <> unId x <> "`"
        Just scheme -> do
            t <- instantiate scheme
            return (nullSubst, t)
    Lit lit -> inferLit lit
    Lam x e -> do
        tv <- freshTyVar
        let env' = remove tyenv x
        let env'' = TyEnv $ coerce env' <> M.singleton x (ForAll [] tv)
        (s1, t1) <- inferExpr env'' e
        return (s1, TyArrow (apply s1 tv) t1)
    App e1 e2 -> do
        tv <- freshTyVar
        (s1, t1) <- inferExpr tyenv e1
        (s2, t2) <- inferExpr (apply s1 tyenv) e2
        s3 <- mgu (apply s2 t1) (TyArrow t2 tv)
        return (s3 `composeSubst` s2 `composeSubst` s1, apply s3 tv)
    Let (x, e1) e2 -> do
        (s1, t1) <- inferExpr tyenv e1
        let env' = remove tyenv x
        let t' = generalise (apply s1 tyenv) t1
        let env'' = TyEnv $ M.insert x t' $ coerce env'
        (s2, t2) <- inferExpr (apply s1 env'') e2
        return (composeSubst s1 s2, t2)
    If cond e1 e2 -> do
        (s1, TyLit TyBool) <- inferExpr tyenv cond
        (s2, t1) <- inferExpr (apply s1 tyenv) e1
        (s3, t2) <- inferExpr (apply (composeSubst s1 s2) tyenv) e2
        if t1 == t2 then
            return ((s1 `composeSubst` s2) `composeSubst` s3, t1)
        else
            fail $ "In `If` arm: type `" <> show t1 <> "` and `" <> show t2 <> "` are not equal"
    Fix e -> do
        (s1, TyArrow a b) <- inferExpr tyenv e
        if a == b then
            return (s1, a)
        else
            fail $ "In `Fix` arm: type `" <> show a <> "` and `" <> show b <> "` are not equal"
    Tuple tuple -> do
        (ss, ts) <- mapAndUnzipM (inferExpr tyenv) tuple
        let s = foldr1 composeSubst ss
        return (s, TyTuple ts)
    TupleNthElem tuple i -> do
        (s, TyTuple tuple') <- inferExpr tyenv tuple
        return (s, tuple' !! i)

inferLit :: Literal -> Inferer (Subst, Type 'Unique)
inferLit = \case
    LitInt _ -> return (nullSubst, TyLit TyInt)
    LitBool _ -> return (nullSubst, TyLit TyBool)
    LitDouble _ -> return (nullSubst,  TyLit TyDouble)
    LitUnit -> return (nullSubst, TyLit TyUnit)

class Types a where
    ftv   :: a -> S.Set (Id 'Unique)
    apply :: Subst -> a -> a

instance Types (Type 'Unique) where
    ftv (TyVar x) = S.singleton x
    ftv (TyLit _) = S.empty
    ftv (TyArrow t1 t2) = S.union (ftv t1) (ftv t2)
    ftv (TyTuple tuple) = S.unions $ map ftv tuple

    apply s v@(TyVar x) = fromMaybe v $ s M.!? x
    apply s (TyArrow t1 t2) = TyArrow (apply s t1) (apply s t2)
    apply s (TyTuple tuple) = TyTuple $ map (apply s) tuple
    apply _ t = t

instance Types (Scheme 'Unique) where
    ftv (ForAll vars t) = ftv t S.\\ S.fromList vars
    apply s (ForAll vars t) = ForAll vars $ apply (foldr M.delete s vars) t

instance Types a => Types [a] where
    ftv = foldr (S.union . ftv) S.empty
    apply s = map (apply s)

instance Types TyEnv where
    ftv (TyEnv e) = ftv $ M.elems e
    apply s e = TyEnv $ M.map (apply s) $ coerce e

nullSubst :: Subst
nullSubst = M.empty

composeSubst :: Subst -> Subst -> Subst
composeSubst s1 s2 = M.map (apply s1) s2 <> s1

remove :: TyEnv -> Id 'Unique -> TyEnv
remove e v = TyEnv $ M.delete v $ coerce e

generalise :: TyEnv -> Type 'Unique -> Scheme 'Unique
generalise e t = ForAll vars t
  where
    vars = S.toList $ ftv t S.\\ ftv e

instantiate :: Scheme 'Unique -> Inferer (Type 'Unique)
instantiate (ForAll vs t) = do
    vs' <- mapM (const freshTyVar) vs
    let s = M.fromList $ zip vs vs'
    return $ apply s t

mgu :: Type 'Unique -> Type 'Unique -> Inferer Subst
mgu (TyArrow l1 r1) (TyArrow l2 r2) = do
    s1 <- mgu l1 l2
    s2 <- mgu (apply s1 r1) (apply s1 r2)
    return $ composeSubst s1 s2
mgu (TyVar u) t = occursCheck u t
mgu t (TyVar u) = occursCheck u t
mgu (TyLit l1) (TyLit l2)
    | l1 == l2 = return nullSubst
    | otherwise = fail "cannot unify"
mgu (TyTuple t1) (TyTuple t2) = M.unions <$> zipWithM mgu t1 t2
mgu _ _ = fail "cannot unify"


freshTyVar :: Inferer (Type 'Unique)
freshTyVar = do
    x <- freshise $ mkId "t"
    return $ TyVar x

freshise :: Id a -> Inferer (Id 'Unique)
freshise x = do
    i <- getNewNum
    return $ mkId $ coerce x <> "#" <> show i

getNewNum :: Inferer Int
getNewNum = do
    i <- get
    increment
    return i

increment :: Inferer ()
increment = modify' (+1)

occursCheck :: Id 'Unique -> Type 'Unique -> Inferer Subst
occursCheck u t
    | t == TyVar u = return $ nullSubst
    | S.member u $ ftv t = fail "occurs check failed"
    | otherwise = return $ M.singleton u t
