{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}

module Rename
    ( rename
    , FreeVar
    ) where

import STLC.Types
import STLC.Expr

import Data.Coerce (coerce)
import Control.Monad.State.Strict
import Control.Monad.Reader

type FreeVar = [Id 'Unique]
newtype Renamer a = Renamer (ReaderT FreeVar (State Int) a)
    deriving
        ( Functor, Applicative, Monad
        , MonadState Int
        , MonadReader FreeVar
        )

runRenamer :: Renamer a -> FreeVar -> Int -> (a, Int)
runRenamer (Renamer r) f i = flip runState i $ runReaderT r f

rename :: FreeVar -> Expr 'None -> Expr 'Renamed
rename fv e = fst $ runRenamer (ren e) fv 0

ren :: Expr 'None -> Renamer (Expr 'Renamed)
ren = \case
    Var x -> do
        is_fv <- isFV $ unId x
        if is_fv then
            return $ Var $ toRenamed x
        else
            Var <$> freshize x
    Lam x e -> do
        x' <- freshize x
        e' <- withFV x' $ ren $ subst x x' e
        return $ Lam x' e'
    App e1 e2 -> App <$> ren e1 <*> ren e2
    Lit lit -> return $ Lit lit
    Let (x0, e0) e1 -> do
        x0' <- freshize x0
        e0' <- ren e0
        e1' <- withFV x0' $ ren $ subst x0 x0' e1
        return $ Let (x0', e0') e1'
    If cond e1 e2 -> If <$> ren cond <*> ren e1 <*> ren e2
    Fix e -> Fix <$> ren e
    Tuple tuple -> Tuple <$> mapM ren tuple
    TupleNthElem e i -> TupleNthElem <$> ren e <*> pure i

subst :: Id 'Original -> Id 'Unique -> Expr 'None -> Expr 'None
subst before after = \case
    Var x -> Var $ if x == before then toUnRenamed after else x
    Lam x e -> if x == before then Lam x e else Lam x $ subst before after e
    App e1 e2 -> App (subst before after e1) (subst before after e2)
    Lit lit -> Lit lit
    Let (x0, e0) e1 -> Let (x0, subst before after e0) $ if x0 == before then e1 else subst before after e1
    If cond e1 e2 -> If (subst before after cond) (subst before after e1) (subst before after e2)
    Fix e -> Fix $ subst before after e
    Tuple tuple -> Tuple $ map (subst before after) tuple
    TupleNthElem e i -> TupleNthElem (subst before after e) i

getNewNum :: Renamer Int
getNewNum = do
    i <- get
    increment
    return i

isFV :: String -> Renamer Bool
isFV x = do
    fv <- ask
    return $ mkId x `elem` fv

withFV :: Id 'Unique -> Renamer a -> Renamer a
withFV x = local (x :)

freshize :: Id 'Original -> Renamer (Id 'Unique)
freshize x = do
    i <- getNewNum
    return $ mkId $ unId x <> "/" <> show i

increment :: Renamer ()
increment = modify' (+1)

toRenamed :: Id 'Original -> Id 'Unique
toRenamed = coerce

toUnRenamed :: Id 'Unique -> Id 'Original
toUnRenamed = coerce
