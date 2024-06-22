module CoreToZincSpec
    ( spec
    ) where

import Test.Hspec

import Core.Types
import Core as C
import ZINC as Z
import ZINCInterpreter
import CoreToZINC

import Data.Int
import Data.Maybe (fromJust)
import qualified Data.IntMap.Strict as IM

spec :: Spec
spec = do
    describe "Test ZINC Interpreter works well" $ do
        it "{ let add = \\a -> \\b -> a + b in add 100 200 } === 300" $
            case runZAM'' zinc' of
                IntVal i -> i `shouldBe` 300
                _ -> error "never come"

        it "{ fix (\\sum -> \\n -> if n == 0 then 0 else n + sum (n - 1)) 2 } === 3" $
            case runZAM'' zinc'' of
                IntVal i -> i `shouldBe` 3
                _ -> error "never come"

        it "{ fix (\\f -> \\n -> n) 0 } === 0" $
            case runZAM'' fixNothing' of
                IntVal i -> i `shouldBe` 0
                _ -> error "never come"

        it "{ 2 - 1 } === 1" $
            case runZAM'' subTest' of
                IntVal i -> i `shouldBe` 1
                _ -> error "never come"

        it "{ let sum0 = \\f -> \\n -> if n == 0 then 0 else n + f (n - 1) in let sum_fix = fix sum0 in sum_fix 10 } === 55" $
            case runZAM'' zinc of
                IntVal i -> i `shouldBe` 55
                _ -> error "never come"

        it "{ fix (\\f -> \\acc -> \\n -> if n == 0 then acc else f (acc + n) (n - 1) ) 0 10 } === 55" $
            case runZAM'' tailCall' of
                IntVal i -> i `shouldBe` 55
                _ -> error "never come"

        it "{ let add = \\a -> \\b -> a + b in let add100 = add 100 in add100 200 } === 300" $
            case runZAM'' partialApply' of
                IntVal i -> i `shouldBe` 300
                _ -> error "never come"

runZAM'' :: Code -> Value
runZAM'' c =
    let (_, a, _, _, _) = runZAM' c
    in
        fromJust a

runZAM' :: Code -> (Code, Accum, IM.IntMap Env, Stack, RetStack)
runZAM' c = runZAM (c, Nothing, env, [], [])

core :: Expr
core =
    C.Let
    [(
        mkId "sum0",
        Lam (mkId "f") (
            Lam (mkId "n") (
                If (App (App (s2v "==") (s2v "n")) (i2l 0))
                (i2l 0)
                (App (App (s2v "+") (s2v "n")) (App (s2v "f") (App (App (s2v "-") (s2v "n")) (i2l 1))))
            )
        ))
    ,(
        mkId "sum_fix",
        C.Fix $ s2v "sum0"
    -- )] (App (s2v "sum_fix") (i2l 10))
    )] (s2v "sum_fix" `App` i2l 10)

core'' :: Expr
core'' =
    C.Fix (
        Lam (mkId "f") (
            Lam (mkId "n") (
                If (App (App (s2v "==") (s2v "n")) (i2l 0))
                (i2l 0)
                ((s2v "+" `App` s2v "n") `App` (s2v "f" `App` ((s2v "-" `App` s2v "n") `App` i2l 1)))
            )
        )
    )
    `App` i2l 2

core' :: Expr
core' =
    C.Let [(
        mkId "add",
        Lam (mkId "a") (
            Lam (mkId "b") (
                App (App (s2v "+") (s2v "a")) (s2v "b")
            )
        )
    )] (App (App (s2v "add") (i2l 100)) (i2l 200))

subTest :: Expr
subTest = (s2v "-" `App` i2l 2) `App` i2l 1

subTest' :: Code
subTest' = coreToZinc env' [subTest]

fixNothing :: Expr
fixNothing = C.Fix (
        Lam (mkId "f") (
            Lam (mkId "n") (s2v "n")
        )
    ) `App` i2l 0

fixNothing' :: Code
fixNothing' = coreToZinc env' [fixNothing]

tailCall :: Expr
tailCall =
    (C.Fix (
        Lam (mkId "f") (
            Lam (mkId "acc") (
                Lam (mkId "n") (
                    If ( (s2v "==" `App` s2v "n") `App` i2l 0 )
                    ( s2v "acc" )
                    ( (s2v "f" `App` ( (s2v "+" `App` s2v "acc") `App` s2v "n" )) `App` ( (s2v "-" `App` s2v "n") `App` i2l 1 ) )
                )
            )
        )
    ) `App` i2l 0) `App` i2l 10

tailCall' :: Code
tailCall' = coreToZinc env' [tailCall]

partialApply :: Expr
partialApply =
    C.Let [
        (
            mkId "add",
            Lam (mkId "a") (
                Lam (mkId "b") (
                    App (App (s2v "+") (s2v "a")) (s2v "b")
                )
            )
        ),
        (
            mkId "add100",
            s2v "add" `App` i2l 100
        )
    ] (s2v "add100" `App` i2l 200)

partialApply' :: Code
partialApply' = coreToZinc env' [partialApply]

zinc :: Code
zinc = coreToZinc (map mkId ["==", "+", "-"]) [core]

zinc' :: Code
zinc' = coreToZinc (map mkId ["==", "+", "-"]) [core']

zinc'' :: Code
zinc'' = coreToZinc (map mkId ["==", "+", "-"]) [core'']

env :: Env
env =
    [ ClosVal [Grab, Access 0, Push, Access 1, Prim Eq, Return] Nothing
    , ClosVal [Grab, Access 0, Push, Access 1, Prim Add, Return] Nothing
    , ClosVal [Grab, Access 0, Push, Access 1, Prim Sub, Return] Nothing
    ]

env' :: [Id]
env' = map mkId ["==", "+", "-"]

s2v :: String -> Expr
s2v = Var . mkId

i2l :: Int64 -> Expr
i2l = Lit . mkLitInt
