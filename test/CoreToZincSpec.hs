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
import qualified Data.Map.Strict as M

spec :: Spec
spec = do
    describe "Test Core is Typed well and ZINC Interpreter works well" $ do
        it "{ let add = \\a -> \\b -> a + b in add 100 200 } === 300" $ do
            assertValidExpr core'
            case runZAM'' zinc' of
                IntVal i -> i `shouldBe` 300
                _ -> error "never come"

        it "{ fix (\\sum -> \\n -> if n == 0 then 0 else n + sum (n - 1)) 2 } === 3" $ do
            assertValidExpr core''
            case runZAM'' zinc'' of
                IntVal i -> i `shouldBe` 3
                _ -> error "never come"

        it "{ fix (\\f -> \\n -> n) 0 } === 0" $ do
            assertValidExpr fixNothing
            case runZAM'' fixNothing' of
                IntVal i -> i `shouldBe` 0
                _ -> error "never come"

        it "{ 2 - 1 } === 1" $ do
            assertValidExpr subTest
            case runZAM'' subTest' of
                IntVal i -> i `shouldBe` 1
                _ -> error "never come"

        it "{ let sum0 = \\f -> \\n -> if n == 0 then 0 else n + f (n - 1) in let sum_fix = fix sum0 in sum_fix 10 } === 55" $ do
            assertValidExpr core
            case runZAM'' zinc of
                IntVal i -> i `shouldBe` 55
                _ -> error "never come"

        it "{ fix (\\f -> \\acc -> \\n -> if n == 0 then acc else f (acc + n) (n - 1) ) 0 10 } === 55" $ do
            assertValidExpr tailCall
            case runZAM'' tailCall' of
                IntVal i -> i `shouldBe` 55
                _ -> error "never come"

        it "{ let add = \\a -> \\b -> a + b in let add100 = add 100 in add100 200 } === 300" $ do
            assertValidExpr partialApply
            case runZAM'' partialApply' of
                IntVal i -> i `shouldBe` 300
                _ -> error "never come"

        it "{ let gcd0 = \\gcd -> \\ab -> if ab.1 == 0 then ab.1 else gcd (ab.1, ab.0 % ab.1) in let gcd' = fix gcd0 in gcd' 253 644 } === 23" $ do
            assertValidExpr gcd'
            case runZAM'' gcd'' of
                IntVal i -> i `shouldBe` 23
                _ -> error "never come"

        it "test mutual recursion (evenOdd)" $ do
            assertValidExpr evenOdd
            case runZAM'' evenOdd' of
                BoolVal b -> b `shouldBe` True
                _ -> error "never come"

runZAM'' :: Code -> Value
runZAM'' c =
    let (_, a, _, _, _, _) = runZAM' c
    in
        fromJust a

runZAM' :: Code -> (Code, Accum, IM.IntMap Env, Stack, RetStack, Glbl)
runZAM' c = runZAM (c, Nothing, [], [], [], global)

core :: Expr
core =
    C.Let (
        mkId "sum0",
        Lam (mkId "f", TyArrow tyInt tyInt) (
            Lam (mkId "n", tyInt) (
                If (App (App (s2v "==") (s2v "n")) (i2l 0))
                (i2l 0)
                (App (App (s2v "+") (s2v "n")) (App (s2v "f") (App (App (s2v "-") (s2v "n")) (i2l 1))))
            )
        ))
    ( C.Let (
        mkId "sum_fix",
        C.Fix $ s2v "sum0"
        )
        (s2v "sum_fix" `App` i2l 10)
    )

core'' :: Expr
core'' =
    C.Fix (
        Lam (mkId "f", TyArrow tyInt tyInt) (
            Lam (mkId "n", tyInt) (
                If (App (App (s2v "==") (s2v "n")) (i2l 0))
                (i2l 0)
                ((s2v "+" `App` s2v "n") `App` (s2v "f" `App` ((s2v "-" `App` s2v "n") `App` i2l 1)))
            )
        )
    )
    `App` i2l 2

core' :: Expr
core' =
    C.Let (
        mkId "add",
        Lam (mkId "a", tyInt) (
            Lam (mkId "b", tyInt) (
                App (App (s2v "+") (s2v "a")) (s2v "b")
            )
        )
    ) (App (App (s2v "add") (i2l 100)) (i2l 200))

subTest :: Expr
subTest = (s2v "-" `App` i2l 2) `App` i2l 1

subTest' :: Code
subTest' = coreToZinc env' [subTest]

fixNothing :: Expr
fixNothing = C.Fix (
        Lam (mkId "f", TyArrow tyInt tyInt) (
            Lam (mkId "n", tyInt) (s2v "n")
        )
    ) `App` i2l 0

fixNothing' :: Code
fixNothing' = coreToZinc env' [fixNothing]

tailCall :: Expr
tailCall =
    (C.Fix (
        Lam (mkId "f", TyArrow tyInt (TyArrow tyInt tyInt)) (
            Lam (mkId "acc", tyInt) (
                Lam (mkId "n", tyInt) (
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
    C.Let (
        mkId "add",
        Lam (mkId "a", tyInt) (
            Lam (mkId "b", tyInt) (
                App (App (s2v "+") (s2v "a")) (s2v "b")
            )
        )
    ) ( C.Let (
            mkId "add100",
            s2v "add" `App` i2l 100
        ) (s2v "add100" `App` i2l 200)
    )

partialApply' :: Code
partialApply' = coreToZinc env' [partialApply]

gcd' :: Expr
gcd' =
    C.Let (
        mkId "gcd0",
        Lam (mkId "gcd", TyArrow (TyTuple [tyInt, tyInt]) tyInt) (
            Lam (mkId "ab", TyTuple [tyInt, tyInt]) (
                If ( (s2v "==" `App` C.TupleNthElem (s2v "ab") 1) `App` i2l 0 )
                ( C.TupleNthElem (s2v "ab") 0 )
                ( s2v "gcd" `App` Tuple [C.TupleNthElem (s2v "ab") 1, (s2v "%" `App` C.TupleNthElem (s2v "ab") 0) `App` C.TupleNthElem (s2v "ab") 1] )
            )
        )
    ) ( C.Let (
            mkId "gcd'",
            C.Fix (s2v "gcd0")
        ) (
            s2v "gcd'" `App` Tuple [i2l 253, i2l 644]
        )
    )

gcd'' :: Code
gcd'' = coreToZinc env' [gcd']

evenOdd :: Expr
evenOdd =
    C.Let (
        mkId "map",
        Lam (mkId "f", TyArrow intBoolTupleIntBool intBool ) (
            Lam (mkId "t", TyTuple [intBoolTupleIntBool, intBoolTupleIntBool]) (
                Tuple [ s2v "f" `App` C.TupleNthElem (s2v "t") 0, s2v "f" `App` C.TupleNthElem (s2v "t") 1 ]
            )
        )
    ) ( C.Let (
            mkId "fixPoly",
            Lam (mkId "l", TyTuple [intBoolTupleIntBool, intBoolTupleIntBool]) (
                C.Fix (
                    Lam (mkId "self", TyArrow (TyTuple [intBoolTupleIntBool, intBoolTupleIntBool]) intBoolTuple) (
                        Lam (mkId "l'", TyTuple [intBoolTupleIntBool, intBoolTupleIntBool]) (
                            s2v "map" `App` Lam (mkId "li", intBoolTupleIntBool) (
                                Lam (mkId "x", tyInt) (
                                    (s2v "li" `App` (s2v "self" `App` s2v "l'")) `App` s2v "x"
                                )
                            ) `App` s2v "l'"
                        )
                    )
                ) `App` s2v "l"
            )
        ) ( C.Let (
                mkId "evenOdd'",
                Tuple
                    [ Lam (mkId "evenOdd0", intBoolTuple) (
                        Lam (mkId "n0", tyInt) (
                            If ( (s2v "==" `App` s2v "n0") `App` i2l 0 )
                            ( b2l True )
                            ( If ( (s2v "==" `App` s2v "n0") `App` i2l 1 )
                              ( b2l False )
                              ( C.TupleNthElem (s2v "evenOdd0") 1 `App` ( (s2v "-" `App` s2v "n0") `App` i2l 1 ) )
                            )
                        )
                    )
                    , Lam (mkId "evenOdd1", intBoolTuple) (
                        Lam (mkId "n1", tyInt) (
                            If ( (s2v "==" `App` s2v "n1") `App` i2l 0 )
                            ( b2l False )
                            ( If ( (s2v "==" `App` s2v "n1") `App` i2l 1 )
                              ( b2l True )
                              ( C.TupleNthElem (s2v "evenOdd1") 0 `App` ( (s2v "-" `App` s2v "n1") `App` i2l 1 ) )
                            )
                        )
                    )
                    ]
            ) ( C.Let (
                    mkId "evenOdd",
                    s2v "fixPoly" `App` s2v "evenOdd'"
                ) ( C.Let (
                        mkId "even",
                        C.TupleNthElem (s2v "evenOdd") 0
                    ) (
                        s2v "even" `App` i2l 100
                    )
                )
            )
        )
    )
  where
    intBool = TyArrow tyInt tyBool
    intBoolTuple = TyTuple [intBool, intBool]
    intBoolTupleIntBool = TyArrow intBoolTuple intBool

evenOdd' :: Code
evenOdd' = coreToZinc env' [evenOdd]

zinc :: Code
zinc = coreToZinc (map mkId ["==", "+", "-"]) [core]

zinc' :: Code
zinc' = coreToZinc (map mkId ["==", "+", "-"]) [core']

zinc'' :: Code
zinc'' = coreToZinc (map mkId ["==", "+", "-"]) [core'']

global :: Glbl
global =
    [ ClosVal [Grab, Access 0, Push, Access 1, Prim Eq, Return] Nothing
    , ClosVal [Grab, Access 0, Push, Access 1, Prim Add, Return] Nothing
    , ClosVal [Grab, Access 0, Push, Access 1, Prim Sub, Return] Nothing
    , ClosVal [Grab, Access 0, Push, Access 1, Prim Mul, Return] Nothing
    , ClosVal [Grab, Access 0, Push, Access 1, Prim Div, Return] Nothing
    , ClosVal [Grab, Access 0, Push, Access 1, Prim Mod, Return] Nothing
    ]

tyEnv :: TyEnv
tyEnv = M.fromList
    [ (mkId "==", TyArrow tyInt (TyArrow tyInt tyBool))
    , (mkId "+", TyArrow tyInt (TyArrow tyInt tyInt))
    , (mkId "-", TyArrow tyInt (TyArrow tyInt tyInt))
    , (mkId "*", TyArrow tyInt (TyArrow tyInt tyInt))
    , (mkId "/", TyArrow tyInt (TyArrow tyInt tyInt))
    , (mkId "%", TyArrow tyInt (TyArrow tyInt tyInt))
    ]

env' :: [Id]
env' = map mkId ["==", "+", "-", "*", "/", "%"]

s2v :: String -> Expr
s2v = Var . mkId

i2l :: Int64 -> Expr
i2l = Lit . mkLitInt

b2l :: Bool -> Expr
b2l = Lit . mkLitBool

tyInt :: Type
tyInt = TyLit TyInt

tyBool :: Type
tyBool = TyLit TyBool

tyCheck :: Expr -> Bool
tyCheck = isValidExpr tyEnv

assertValidExpr :: Expr -> Expectation
assertValidExpr = (`shouldSatisfy` tyCheck)
