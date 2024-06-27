{-# LANGUAGE LambdaCase #-}

module ZINCInterpreter
    ( runZAM
    , Value(..)
    , Env, Stack, RetStack, Accum, Glbl

    -- debug
    , interpret
    , debug
    ) where

import ZINC

import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import Data.Maybe (fromJust)
import Control.Monad.State.Strict
import Control.Monad

data Value
    = IntVal Integer
    | BoolVal Bool
    | DoubleVal Rational
    | UnitVal
    | ClosVal Code (Maybe Int)
    | Epsilon
    | Dummy
    deriving (Show)

type Env = [Value]
type Glbl = [Value]
type Stack = [Value]
type RetStack = [Value]
type Accum = Maybe Value

type ZAMState a = State (Code, Accum, IM.IntMap Env, Stack, RetStack, Glbl) a

primOps :: M.Map PrimOp (ZAMState Value)
primOps = M.fromList
    [ (Add, do
            lhs <- getAccum
            rhs <- popStack
            return $ case (lhs, rhs) of
                (IntVal l, IntVal r) -> IntVal $ l + r
                (DoubleVal l, DoubleVal r) -> DoubleVal $ l + r
                _ -> error "never come")
    , (Sub, do
            lhs <- getAccum
            rhs <- popStack
            return $ case (lhs, rhs) of
                (IntVal l, IntVal r) -> IntVal $ l - r
                (DoubleVal l, DoubleVal r) -> DoubleVal $ l - r
                _ -> error "never come")
    , (Mul, do
            lhs <- getAccum
            rhs <- popStack
            return $ case (lhs, rhs) of
                (IntVal l, IntVal r) -> IntVal $ l * r
                (DoubleVal l, DoubleVal r) -> DoubleVal $ l * r
                _ -> error "never come")
    , (Div, do
            lhs <- getAccum
            rhs <- popStack
            return $ case (lhs, rhs) of
                (IntVal l, IntVal r) -> IntVal $ l `div` r
                (DoubleVal l, DoubleVal r) -> DoubleVal $ l / r
                _ -> error "never come")

    , (Eq, do
            lhs <- getAccum
            rhs <- popStack
            return $ case (lhs, rhs) of
                (IntVal l, IntVal r) -> BoolVal $ l == r
                (DoubleVal l, DoubleVal r) -> BoolVal $ l == r
                (BoolVal l, BoolVal r) -> BoolVal $ l == r
                (UnitVal, UnitVal) -> BoolVal True
                _ -> error "never come")
    , (Lt, do
            lhs <- getAccum
            rhs <- popStack
            return $ case (lhs, rhs) of
                (IntVal l, IntVal r) -> BoolVal $ l < r
                (DoubleVal l, DoubleVal r) -> BoolVal $ l < r
                _ -> error "never come")
    , (Gt, do
            lhs <- getAccum
            rhs <- popStack
            return $ case (lhs, rhs) of
                (IntVal l, IntVal r) -> BoolVal $ l > r
                (DoubleVal l, DoubleVal r) -> BoolVal $ l > r
                _ -> error "never come")
    , (Le, do
            lhs <- getAccum
            rhs <- popStack
            return $ case (lhs, rhs) of
                (IntVal l, IntVal r) -> BoolVal $ l <= r
                (DoubleVal l, DoubleVal r) -> BoolVal $ l <= r
                _ -> error "never come")
    , (Ge, do
            lhs <- getAccum
            rhs <- popStack
            return $ case (lhs, rhs) of
                (IntVal l, IntVal r) -> BoolVal $ l >= r
                (DoubleVal l, DoubleVal r) -> BoolVal $ l >= r
                _ -> error "never come")
    ]

runZAM :: (Code, Accum, Env, Stack, RetStack, Glbl) -> (Code, Accum, IM.IntMap Env, Stack, RetStack, Glbl)
runZAM (c, a, e, s, r, g) =
    let (c', a', e', s', r', g') = execState helper (c, a, IM.singleton 0 e, s, r, g)
    in
        (c', a', e', s', r', g')
  where
    helper :: ZAMState ()
    helper = do
        interpret
        code <- getCode
        unless (null code) helper

debug :: ZAMState a -> (Code, Accum, IM.IntMap Env, Stack, RetStack, Glbl) ->  (Code, Accum, IM.IntMap Env, Stack, RetStack, Glbl)
debug = execState

interpret :: ZAMState ()
interpret = takeInstruction >>= \case
    Access i -> findGlblEnv i >>= pushAccum
    AccessGlbl i -> findGlbl i >>= pushAccum
    AppTerm -> do
        (c1, e1) <- getAccum >>= unClosure
        case e1 of
            (Dummy : e1') -> putGlblEnv e1'
            _ -> do
                v <- popStack
                putGlblEnv $ v : e1
        putCode c1
    Apply -> do
        (c1, e1) <- getAccum >>= unClosure
        pushRtFrame
        case e1 of
            (Dummy : e1') -> putGlblEnv e1'
            _ -> do
                v <- popStack
                putGlblEnv $ v : e1
        putCode c1
    Push -> getAccum >>= pushStack
    PushMark -> pushStack Epsilon
    Cur c1 -> do
        e <- getGlblEnv
        makeClos c1 e >>= pushAccum

    Grab -> popStack >>= \case
        Epsilon -> do
            clos1 <- popRtStack
            (c1, e1) <- unClosure clos1
            case snd $ destructClos clos1 of
                Nothing -> return ()
                Just i -> deleteEnv i
            clos0 <- makeCurClos
            pushAccum clos0
            putCode c1
            putGlblEnv e1
        v -> pushGlblEnv v
    Return -> popStack >>= \case
        Epsilon -> do
            clos1 <- popRtStack
            (c1, e1) <- unClosure clos1
            case snd $ destructClos clos1 of
                Nothing -> return ()
                Just i -> deleteEnv i
            putCode c1
            putGlblEnv e1
        v -> do
            (c1, e1) <- getAccum >>= unClosure
            putCode c1
            putGlblEnv $ v : e1
    Let -> getAccum >>= pushGlblEnv
    EndLet -> void popGlblEnv
    LoadInt i -> pushAccum $ IntVal i
    LoadBool b -> pushAccum $ BoolVal b
    LoadDouble d -> pushAccum $ DoubleVal d
    LoadUnit -> pushAccum UnitVal
    Test c1 c2 -> getAccum >>= \case
        BoolVal True -> pushCode c1
        BoolVal False -> pushCode c2
        _ -> error "interpret: Test: never come"
    Prim prim -> primOps M.! prim >>= pushAccum
    Fix -> do
        clos0 <- getAccum
        let (c, idx) = destructClos clos0
        case idx of
            Just i -> pushNthEnv i clos0 >> pushNthEnv i Dummy
            Nothing -> do
                idx' <- newEnv [clos0]
                pushAccum $ ClosVal c $ Just idx'

makeCurClos :: ZAMState Value
makeCurClos = do
    code <- getCode
    env <- getGlblEnv
    makeClos code env

makeClos :: Code -> Env -> ZAMState Value
makeClos c e = do
    leng <- newEnv e
    return $ ClosVal c $ Just leng

destructClos :: Value -> (Code, Maybe Int)
destructClos (ClosVal c i) = (c, i)
destructClos _ = error "destructClos: never come"

pushRtFrame :: ZAMState ()
pushRtFrame = makeCurClos >>= pushRtStack

getCode :: ZAMState Code
getCode = do
    (c, _, _, _, _, _) <- get
    return c

putCode :: Code -> ZAMState ()
putCode c = modify $ \(_, a, e, s, r, g) -> (c, a, e, s, r, g)

pushCode :: Code -> ZAMState ()
pushCode c = modify $ \(c', a, e, s, r, g) -> (c ++ c', a, e, s, r, g)

getAccum :: ZAMState Value
getAccum = do
    (_, a, _, _, _, _) <- get
    return $ fromJust a

pushAccum :: Value -> ZAMState ()
pushAccum v = modify $ \(c, _, e, s, r, g) -> (c, Just v, e, s, r, g)

getGlbl :: ZAMState Glbl
getGlbl = do
    (_, _, _, _, _, g) <- get
    return g

getGlblEnv :: ZAMState Env
getGlblEnv = do
    (_, _, e, _, _, _) <- get
    return $ e IM.! 0

getEnvs :: ZAMState (IM.IntMap Env)
getEnvs = do
    (_, _, e, _, _, _) <- get
    return e

newEnv :: Env -> ZAMState Int
newEnv env = do
    envs <- getEnvs
    let next = fst (IM.findMax envs) + 1
        envs' = IM.insert next env envs
    putEnvs envs'
    return next

deleteEnv :: Int -> ZAMState ()
deleteEnv i = do
    envs <- getEnvs
    putEnvs $ IM.delete i envs

putEnvs :: IM.IntMap Env -> ZAMState ()
putEnvs envs = modify $ \(c, a, _, s, r, g) -> (c, a, envs, s, r, g)

pushGlblEnv :: Value -> ZAMState ()
pushGlblEnv v = do
    env <- getGlblEnv
    putGlblEnv $ v : env

pushNthEnv :: Int -> Value -> ZAMState ()
pushNthEnv i v = do
    envs <- getEnvs
    putEnvs $ IM.update (Just . (v :)) i envs

putGlblEnv :: Env -> ZAMState ()
putGlblEnv e = do
    envs <- getEnvs
    putEnvs $ IM.insert 0 e envs

popGlblEnv :: ZAMState Value
popGlblEnv = do
    e <- getGlblEnv
    putGlblEnv $ tail e
    return $ head e

getStack :: ZAMState Stack
getStack = do
    (_, _, _, s, _, _) <- get
    return s

pushStack :: Value -> ZAMState ()
pushStack v = modify $ \(c, a, e, s, r, g) -> (c, a, e, v : s, r, g)

popStack :: ZAMState Value
popStack = do
    (c, a, e, s, r, g) <- get
    put (c, a, e, tail s, r, g)
    return $ head s

getRtStack :: ZAMState RetStack
getRtStack = do
    (_, _,  _, _, r, _) <- get
    return r

pushRtStack :: Value -> ZAMState ()
pushRtStack v = modify $ \(c, a, e, s, r, g) -> (c, a, e, s, v : r, g)

popRtStack :: ZAMState Value
popRtStack = do
    (c, a, e, s, r, g) <- get
    put (c, a, e, s, tail r, g)
    return $ head r

unClosure :: Value -> ZAMState (Code, Env)
unClosure (ClosVal c i) = do
    envs <- getEnvs
    let e = maybe [] (envs IM.!) i
    return (c, e)
unClosure _ = error "unClosure: never come"

findGlblEnv :: Int -> ZAMState Value
findGlblEnv i = do
    e <- getGlblEnv
    return $ e !! i

findGlbl :: Int -> ZAMState Value
findGlbl i = do
    g <- getGlbl
    return $ g !! i

takeInstruction :: ZAMState Instruction
takeInstruction = do
    (c, a, e, s, r, g) <- get
    put (tail c, a, e, s, r, g)
    return $ head c
