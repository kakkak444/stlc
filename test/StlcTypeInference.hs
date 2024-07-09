{-# LANGUAGE DataKinds #-}

module StlcTypeInference
    ( spec
    ) where

import Test.Hspec

import STLC.Expr
import STLC.Types
import Rename
import TypeInference

import qualified Data.Map.Strict as M
import Data.Int (Int64)
-- import Data.List

spec :: Spec
spec = do
    describe "Test whether Type Inference of STLC worked correctly" $ do
        it "{ let id = \\x -> x in (id True, id 100, id) }: forall a. (Bool, Int, a -> a)" $ do
            assertTypes letGeneralise $ ForAll [mkId "a#0"] $ TyTuple [tyBool, tyInt, TyArrow (tyVar "a#0") (tyVar "a#0")]

        it "mutual recursion (evenOdd)" $ do
            assertTypes evenOdd $ ForAll [] tyBool


letGeneralise :: Expr 'None
letGeneralise =
    Let (
        mkId "id",
        Lam (mkId "x") (s2v "x")
    ) (
        Tuple [ App (s2v "id") (b2l True), App (s2v "id") (i2l 100), s2v "id" ]
    )

evenOdd :: Expr 'None
evenOdd =
    Let (
        mkId "map",
        Lam (mkId "f") (
            Lam (mkId "t") (
                Tuple [ s2v "f" `App` TupleNthElem (s2v "t") 0 2, s2v "f" `App` TupleNthElem (s2v "t") 1 2 ]
            )
        )
    ) ( Let (
            mkId "fixPoly",
            Lam (mkId "l") (
                Fix (
                    Lam (mkId "self") (
                        Lam (mkId "l") (
                            s2v "map" `App` Lam (mkId "li") (
                                Lam (mkId "x") (
                                    (s2v "li" `App` (s2v "self" `App` s2v "l")) `App` s2v "x"
                                )
                            ) `App` s2v "l"
                        )
                    )
                ) `App` s2v "l"
            )
        ) ( Let (
                mkId "evenOdd'",
                Tuple
                    [ Lam (mkId "evenOdd") (
                        Lam (mkId "n") (
                            If ( (s2v "==" `App` s2v "n") `App` i2l 0 )
                            ( b2l True )
                            ( If ( (s2v "==" `App` s2v "n") `App` i2l 1 )
                              ( b2l False )
                              ( TupleNthElem (s2v "evenOdd") 1 2 `App` ( (s2v "-" `App` s2v "n") `App` i2l 1 ) )
                            )
                        )
                    )
                    , Lam (mkId "evenOdd") (
                        Lam (mkId "n") (
                            If ( (s2v "==" `App` s2v "n") `App` i2l 0 )
                            ( b2l False )
                            ( If ( (s2v "==" `App` s2v "n") `App` i2l 1 )
                              ( b2l True )
                              ( TupleNthElem (s2v "evenOdd") 0 2 `App` ( (s2v "-" `App` s2v "n") `App` i2l 1 ) )
                            )
                        )
                    )
                    ]
            ) ( Let (
                    mkId "evenOdd",
                    s2v "fixPoly" `App` s2v "evenOdd'"
                ) ( Let (
                        mkId "even",
                        TupleNthElem (s2v "evenOdd") 0 2
                    ) (
                        s2v "even" `App` i2l 100
                    )
                )
            )
        )
    )


infer' :: Expr 'None -> Either String (Scheme 'Unique, TEnv)
infer' expr =
    let expr' = rename fv expr
    in
        infer fv' expr'

assertTypes :: Expr 'None -> Scheme 'Unique -> Expectation
assertTypes expr t =
    let res = infer' expr
    in
        fst <$> res `shouldBe` Right t

-- schemeEqual :: Scheme 'Unique -> Scheme 'Unique -> Bool
-- schemeEqual = _

-- tyVar2Int :: [Id 'Unique] -> Type 'Unique -> Type 'Unique
-- tyVar2Int env (TyVar x) = case elemIndex x env of
--     Nothing -> TyVar x
--     Just i -> TyVar $ mkId $ show i
-- tyVar2Int env (TyArrow t1 t2) = TyArrow (tyVar2Int env t1) (tyVar2Int env t2)
-- tyVar2Int _env lit@(TyLit _) = lit
-- tyVar2Int env (TyTuple tuple) = TyTuple $ map (tyVar2Int env) tuple

s2v :: String -> Expr 'None
s2v = Var . mkId

i2l :: Int64 -> Expr a
i2l = Lit . mkLitInt

b2l :: Bool -> Expr a
b2l = Lit . mkLitBool

tyBool :: Type a
tyBool = TyLit TyBool

tyInt :: Type a
tyInt = TyLit TyInt

tyVar :: String -> Type 'Unique
tyVar = TyVar . mkId

fv :: FreeVar
fv = map mkId ["==", "+", "-", "*", "/", "%"]

fv' :: TEnv
fv' = mkTEnv $ M.fromList
    [ (mkId "==", ForAll [mkId "a"] (TyArrow (tyVar "a") (TyArrow (tyVar "a") tyBool)))
    , (mkId "+", ForAll [] (TyArrow tyInt (TyArrow tyInt tyInt)))
    , (mkId "-", ForAll [] (TyArrow tyInt (TyArrow tyInt tyInt)))
    , (mkId "*", ForAll [] (TyArrow tyInt (TyArrow tyInt tyInt)))
    , (mkId "/", ForAll [] (TyArrow tyInt (TyArrow tyInt tyInt)))
    , (mkId "%", ForAll [] (TyArrow tyInt (TyArrow tyInt tyInt)))
    ]
