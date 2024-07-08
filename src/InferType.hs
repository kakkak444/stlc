{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module InferType
    ( inferType
    ) where

import STLC.Types
import STLC.Expr

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Except

type Env = M.Map (Id 'Unique) (Scheme 'Unique)
type Subst = M.Map (Id 'Unique) (Type 'Unique)

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


class Types a where
    apply :: Subst -> a -> a
    ftv :: a -> S.Set (Id 'Unique)

instance Types (Type 'Unique) where
    apply s t@(TyVar x) = M.findWithDefault t x s
    apply _ t@(TyLit _) = t
    apply s (TyArrow t1 t2) = TyArrow (apply s t1) (apply s t2)
    apply s (TyTuple tuple) = TyTuple $ map (apply s) tuple

    ftv (TyVar x) = S.singleton x
    ftv (TyLit _) = S.empty
    ftv (TyArrow t1 t2) = ftv t1 <> ftv t2
    ftv (TyTuple tuple) = S.unions $ map ftv tuple

instance Types (Scheme 'Unique) where
    apply s (ForAll xs t) = ForAll xs $ apply (foldr M.delete s xs) t
    ftv (ForAll xs t) = ftv t S.\\ S.fromList xs

ftvEnv :: Env -> S.Set (Id 'Unique)
ftvEnv = mconcat . map ftv . M.elems


inferExpr :: Expr 'Renamed -> Inferer (Subst, Type 'Unique)
inferExpr = \case
    Var x -> do
    --     let lookupEnv' x = do
    --             env <- ask
    --             case env M.!? x of
    --                 Nothing -> fail $ "Unbound variable `" <> show x <> "`"
    --                 Just s -> do
    --                     t <- instantiate s
    --                     return (emptySubst, t)
    --     lookupEnv' x

        scheme <- lookupEnv x
        t <- instantiate scheme
        return (emptySubst, t)
    App e1 e2 -> do
        (s1, t1) <- inferExpr e1
        (s2, t2) <- applyEnv s1 $ inferExpr e2
        t3 <- freshTyVar
        s3 <- unify (apply s2 t1) (TyArrow t2 t3)
        return (s3 `compose` s2 `compose` s1, apply s3 t3)
    Lam x e -> do
        t <- freshTyVar
        (s1, te) <- withNewScheme x (ForAll [] t) $ inferExpr e
        return (s1, TyArrow (apply s1 t) te)
    Let (x, e1) e2 -> do
        (s1, t1) <- inferExpr e1
        (s2, t2) <- applyEnv s1 $ do
            gen <- generalise t1
            withNewScheme x gen $ inferExpr e2
        return (s2 `compose` s1, t2)
    Lit lit -> inferLit lit
    If cond e1 e2 -> do
        (s1, tcond) <- inferExpr cond
        (s2, t1) <- inferExpr e1
        (s3, t2) <- inferExpr e2
        s4 <- unify tcond $ TyLit TyBool
        s5 <- unify t1 t2
        return (s5 `compose` s4 `compose` s3 `compose` s2 `compose` s1, apply s5 t1)
    Fix e -> do
        -- (s1, t) <- inferExpr e
        -- tA <- freshTyVar
        -- tB <- freshTyVar
        -- let tAB = TyArrow tA tB
        -- s2 <- unify (TyArrow tAB tAB) t
        -- return (s2, apply s1 tAB)

        (s1, t) <- inferExpr e
        tv <- freshTyVar
        s2 <- unify (TyArrow tv tv) t
        return (s2, apply s1 tv)
    _ -> fail "inferExpr: not implemented yet"

inferLit :: Literal -> Inferer (Subst, Type 'Unique)
inferLit lit = return
        ( emptySubst
        , TyLit $ case lit of
            LitInt _ -> TyInt
            LitBool _ -> TyBool
            LitDouble _ -> TyDouble
            LitUnit -> TyUnit
        )

inferScheme :: Expr 'Renamed -> Inferer (Scheme 'Unique)
inferScheme e = do
    (_, t) <- inferExpr e
    generalise t

inferType :: Env -> Expr 'Renamed -> Either String (Scheme 'Unique)
inferType env e = fst <$> runInferer (inferScheme e) env 0


instantiate :: Scheme 'Unique -> Inferer (Type 'Unique)
instantiate (ForAll xs t) = do
    tvs <- mapM (const freshTyVar) xs
    let s = newSubst xs tvs
    return $ apply s t

unify :: Type 'Unique -> Type 'Unique -> Inferer Subst
unify (TyVar u) t = unifyVar u t
unify t (TyVar u) = unifyVar u t
unify (TyLit l1) (TyLit l2)
    | l1 == l2 = return emptySubst
unify (TyArrow l1 r1) (TyArrow l2 r2) = do
    s1 <- unify l1 l2
    s2 <- unify r1 r2
    return $ compose s2 s1
unify _t1 _t2 = fail "Cannot unify"


unifyVar :: Id 'Unique -> Type 'Unique -> Inferer Subst
unifyVar u ty
    | ty == TyVar u = return emptySubst
    | S.member u $ ftv ty = fail "occurs check failed"
    | otherwise = return $ M.singleton u ty

generalise :: Type 'Unique -> Inferer (Scheme 'Unique)
generalise t = do
    env <- ask
    let xs = S.toList $ ftv t S.\\ ftvEnv env
    return $ ForAll xs t

withNewScheme :: Id 'Unique -> Scheme 'Unique -> Inferer a -> Inferer a
withNewScheme x t = local $ M.insert x t

lookupEnv :: Id 'Unique -> Inferer (Scheme 'Unique)
lookupEnv x = do
    env <- ask
    case env M.!? x of
        Just t -> return t
        Nothing -> fail $ "not found `" <> show x <> "`"

applyEnv :: Subst -> Inferer a -> Inferer a
applyEnv s = local $ M.map $ apply s

emptySubst :: Subst
emptySubst = M.empty

newSubst :: [Id 'Unique] -> [Type 'Unique] -> Subst
newSubst xs ts = M.fromList $ zip xs ts

compose :: Subst -> Subst -> Subst
compose s1 s2 = M.map (apply s1) s2 <> s1

freshTyVar :: Inferer (Type 'Unique)
freshTyVar = do
    x <- freshise $ mkId "t"
    return $ TyVar x

freshise :: Id a -> Inferer (Id 'Unique)
freshise x = do
    i <- getNewNum
    return $ mkId $ unId x <> "#" <> show i

getNewNum :: Inferer Int
getNewNum = do
    i <- get
    increment
    return i

increment :: Inferer ()
increment = modify' (+1)
