{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}

module TypeInference
    ( infer
    , mkTEnv
    , TEnv

    -- debug
    , inferExpr
    , runInferer
    ) where

import STLC.Types
import STLC.Expr

import Data.Coerce (coerce)
import Control.Monad
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.State.Strict
import Control.Monad.Except

type TVar a = Id a

type Subst = M.Map (TVar 'Unique) (Type 'Unique)
newtype TEnv = TEnv (M.Map (TVar 'Unique) (Scheme 'Unique))

newtype Inferer a = Inferer (StateT Int (Except String) a)
    deriving
        ( Functor, Applicative, Monad
        , MonadState  Int
        , MonadError  String
        )

instance MonadFail Inferer where
    fail = throwError

runInferer :: Inferer a -> Either String (a, Int)
runInferer (Inferer a) = runExcept $ runStateT a 0

mkTEnv :: M.Map (TVar 'Unique) (Scheme 'Unique) -> TEnv
mkTEnv = coerce


infer :: TEnv -> Expr 'Renamed -> Either String (Scheme 'Unique)
infer tenv expr = case runInferer $ inferExpr tenv expr of
    Left err -> Left err
    Right ((s, t), _) -> Right $ normalise $ generalise tenv $ apply s t


class Types a where
    apply :: Subst -> a -> a
    ftv   :: a -> S.Set (TVar 'Unique)

instance Types (Type 'Unique) where
    apply _ lit@(TyLit _) = lit
    apply s t@(TyVar a) = M.findWithDefault t a s
    apply s (TyArrow t1 t2) = TyArrow (apply s t1) (apply s t2)
    apply s (TyTuple tuple) = TyTuple $ map (apply s) tuple

    ftv (TyLit _) = S.empty
    ftv (TyVar x) = S.singleton x
    ftv (TyArrow t1 t2) = ftv t1 <> ftv t2
    ftv (TyTuple tuple) = S.unions $ map ftv tuple

instance Types (Scheme 'Unique) where
    apply s (ForAll xs t) = ForAll xs $ apply s' t
      where
        s' = foldr M.delete s xs
    ftv (ForAll xs t) = ftv t S.\\ S.fromList xs

instance Types a => Types [a] where
    apply = fmap . apply
    -- ftv = foldr (S.union . ftv) S.empty
    ftv xs = S.unions $ map ftv xs

instance Types TEnv where
    apply s (TEnv env) = TEnv $ M.map (apply s) env
    ftv (TEnv env) = ftv $ M.elems env

inferExpr :: TEnv -> Expr 'Renamed -> Inferer (Subst, Type 'Unique)
inferExpr tenv = \case
    Var x -> lookupTEnv tenv x
    Lit lit -> inferLit tenv lit
    Lam x e -> do
        tv <- freshTyVar
        let env' = extendTEnv tenv x $ ForAll [] tv
        (s1, t1) <- inferExpr env' e
        return (s1, TyArrow (apply s1 tv) t1)
    App e1 e2 -> do
        tv <- freshTyVar
        (s1, t1) <- inferExpr tenv e1
        (s2, t2) <- inferExpr (apply s1 tenv) e2
        s3 <- unify (apply s2 t1) (TyArrow t2 tv)
        return (s3 `compose` s2 `compose` s1, apply s3 tv)
    Let (x, e1) e2 -> do
        (s1, t1) <- inferExpr tenv e1
        let env' = apply s1 tenv
            t'   = generalise env' t1
        (s2, t2) <- inferExpr (extendTEnv env' x t') e2
        return (s1 `compose` s2, t2)
    If cond e1 e2 -> do
        (s1, t1) <- inferExpr tenv cond
        s2 <- unify t1 $ TyLit TyBool
        let s3 = compose s2 s1
            tenv' = apply s3 tenv
        (s4, t2) <- inferExpr tenv' e1
        let s5 = compose s4 s3
            tenv'' = apply s5 tenv'
        (s6, t3) <- inferExpr tenv'' e2
        let s7 = compose s6 s5
            (t2', t3') = (apply s7 t2, apply s7 t3)
        s8 <- unify t2' t3'
        let s9 = compose s8 s7
        return (s9, apply s9 t2')
        -- (s1, t1) <- inferExpr tenv cond
        -- (s2, t2) <- inferExpr tenv e1
        -- (s3, t3) <- inferExpr tenv e2
        -- s4 <- unify t1 $ TyLit TyBool
        -- s5 <- unify t2 t3
        -- return (s5 `compose` s4 `compose` s3 `compose` s2 `compose` s1, apply s5 t2)
    Fix e -> do
        (s1, t) <- inferExpr tenv e
        tA <- freshTyVar
        tB <- freshTyVar
        let tAB = TyArrow tA tB
        s2 <- unify (TyArrow tAB tAB) t
        return (s2 `compose` s1, apply s2 tAB)
    Tuple tuple -> do
        let len = length tuple
        tvars <- replicateM len freshTyVar
        (s, ts, _tenv') <- foldM (
            \(s, t, tenv_) e -> do
                (s', t') <- inferExpr tenv_ e
                return (compose s' s, t ++ [t'], apply s' tenv_)
            ) (nullSubst, [], tenv) tuple
        s' <- foldl compose nullSubst <$> zipWithM unify ts tvars
        let s'' = compose s' s
            tuple' = apply s'' $ TyTuple ts
        return (s'', tuple')
    TupleNthElem e i l -> do
        tvars <- replicateM l freshTyVar
        (s, t) <- inferExpr tenv e
        s' <- unify t $ TyTuple tvars
        let s'' = compose s' s
        case apply s'' t of
            TyTuple ts
                | length ts == l -> return (s'', ts !! i)
            other -> throwError $ "type mismatch `" <> show other <> "`"
    -- e -> fail $ "not implemented yet `" <> show e <> "`"

inferLit :: TEnv -> Literal -> Inferer (Subst, Type 'Unique)
inferLit _tenv lit = return
    ( nullSubst
    , TyLit $ case lit of
        LitInt    _ -> TyInt
        LitBool   _ -> TyBool
        LitDouble _ -> TyDouble
        LitUnit     -> TyUnit
    )


unify :: Type 'Unique -> Type 'Unique -> Inferer Subst
unify (TyArrow l1 r1) (TyArrow l2 r2) = do
    s1 <- unify l1 l2
    s2 <- unify (apply s1 r1) (apply s1 r2)
    return $ compose s2 s1
unify (TyVar a) t = bind a t
unify t (TyVar a) = bind a t
unify (TyLit a) (TyLit b)
    | a == b = return nullSubst
unify (TyTuple tuple1) (TyTuple tuple2) = foldM (\sAcc (t1, t2) -> do { s <- unify t1 t2; return $ compose s sAcc }) nullSubst $ zip tuple1 tuple2
unify t1 t2 = throwError $ "failed to unify `" <> show t1 <> "` and `" <> show t2 <> "`"

instantiate :: Scheme 'Unique -> Inferer (Type 'Unique)
instantiate (ForAll xs t) = do
    xs' <- mapM (const freshTyVar) xs
    let s = M.fromList $ zip xs xs'
    return $ apply s t

generalise :: TEnv -> Type 'Unique -> Scheme 'Unique
generalise env t = ForAll xs t
  where
    xs = S.toList $ ftv t S.\\ ftv env

normalise :: Scheme 'Unique -> Scheme 'Unique
normalise (ForAll _ts e) = ForAll (M.elems ord) (normtype e)
  where
    ord = flip evalState 0 $ foldM (\acc x -> do { a <- freshise $ mkId "a"; return $ M.insert x a acc }) M.empty $ ftv e

    normtype (TyArrow a b) = TyArrow (normtype a) (normtype b)
    normtype lit@(TyLit _) = lit
    normtype (TyTuple tuple) = TyTuple $ map normtype tuple
    normtype (TyVar x) = case ord M.!? x of
        Just x' -> TyVar x'
        Nothing -> error "noramalise: not expected"


bind :: TVar 'Unique -> Type 'Unique -> Inferer Subst
bind a t
    | t == TyVar a = return nullSubst
    | occursCheck a t = throwError "infinite type"
    | otherwise = return $ M.singleton a t

occursCheck :: Types a => TVar 'Unique -> a -> Bool
occursCheck a t = S.member a $ ftv t

lookupTEnv :: TEnv -> Id 'Unique -> Inferer (Subst, Type 'Unique)
lookupTEnv (TEnv env) x = do
    case env M.!? x of
        Nothing -> throwError $ "unbound variable: `" <> show x <> "`"
        Just s -> do
            t <- instantiate s
            return (nullSubst, t)

extendTEnv :: TEnv -> TVar 'Unique -> Scheme 'Unique -> TEnv
extendTEnv (TEnv env) x s = TEnv $ M.insert x s env

nullSubst :: Subst
nullSubst = M.empty

compose :: Subst -> Subst -> Subst
compose s1 s2 = M.map (apply s1) s2 <> s1


freshTyVar :: MonadState Int m => m (Type 'Unique)
freshTyVar = do
    x <- freshise $ mkId "t"
    return $ TyVar x

freshise :: MonadState Int m => Id a -> m (Id 'Unique)
freshise x = do
    i <- getNewNum
    return $ mkId $ unId x <> "#" <> show i

getNewNum :: MonadState Int m => m Int
getNewNum = do
    i <- get
    increment
    return i

increment :: MonadState Int m => m ()
increment = modify' (+1)
