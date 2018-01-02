{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}

module Tests where

import Test.Hspec
import qualified Data.Text.Lazy as TL

import Overture hiding ((|>), (<+>))
import Types
import Pretty
import Infer
import Eval

tests :: IO ()
tests = hspec tests'

eTermSort :: Tm -> Either Text Sort
eTermSort = evalTcM . inferSort initialContext

eInfer' :: TcCtx -> Expr -> Either Text (Ty, Prin, TcCtx)
eInfer' ctx = evalTcM . infer ctx

eInferPred' :: (Either Text (Ty, Prin, TcCtx) -> Expectation) -> TcCtx -> Expr -> SpecWith ()
eInferPred' pred ctx e = it (renderString e) (pred (eInfer' ctx e))

eInferValid' :: TcCtx -> Expr -> SpecWith ()
eInferValid' = eInferPred' (`shouldSatisfy` isRight)

eInferInvalid' :: TcCtx -> Expr -> SpecWith ()
eInferInvalid' = eInferPred' (`shouldSatisfy` isLeft)

eInfer :: Expr -> Either Text (Ty, Prin, TcCtx)
eInfer = eInfer' initialContext

eInferPred :: (Either Text (Ty, Prin, TcCtx) -> Expectation) -> Expr -> SpecWith ()
eInferPred pred = eInferPred' pred initialContext 

eInferValid :: Expr -> SpecWith ()
eInferValid = eInferValid' initialContext

eInferInvalid :: Expr -> SpecWith ()
eInferInvalid = eInferInvalid' initialContext

eBigStep lhs rhs =
  it (renderString (ppr lhs <+> "⇓" <+> ppr rhs)) $ do
      evalTcM (bigStep initEvCtx lhs) `shouldBe` Right rhs

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft (Right _) = False

isRight :: Either a b -> Bool
isRight = not . isLeft

instance Show Sort where show = renderPlainString
instance Show Ty where show = renderPlainString
instance Show Prin where show = renderPlainString
instance Show TcCtx where show = renderPlainString
instance Show Expr where show = renderPlainString

tests' :: SpecWith ()
tests' = do
  describe "inferSort" $ do
    it "sort of Unit is Star" $ 
      eTermSort TmUnit `shouldBe` Right Star
    context "given an existential variable" $ 
      it "fails if the variable is unknown" $ 
        eTermSort (TmExVar (ExSym "foo")) `shouldSatisfy` isLeft
  describe "infer" $ do
    context "succeeds for well-typed expressions" $ do
      eInferValid fstExpr
      eInferValid sndExpr
      eInferValid swapExpr
      context "example from the paper" $ do
        eInferValid' idCtx idApp
      -- eInferValid mapExpr
      -- eInferValid zipExpr
      -- eInferValid curriedZipExpr
    context "fails for ill-typed expressions" $ do
      eInferInvalid badSndExpr
  describe "bigStep" $ do
    eBigStep EpUnit EpUnit
    eBigStep (EpApp idExpr (Spine [EpUnit])) EpUnit
    eBigStep (EpApp fstExpr (Spine [EpProd EpUnit EpUnit])) EpUnit

lam :: Text -> Expr -> Expr
lam v = EpLam (Sym v)

ann :: Expr -> Ty -> Expr
ann = EpAnn

tyUniv :: Text -> Ty
tyUniv s = TyUnVar (UnSym s)

tyExtl :: Text -> Ty
tyExtl s = TyExVar (ExSym s)

idExpr :: Expr
idExpr = EpLam x (EpVar x) where x = Sym "x"

-- Bool ~ Either () ()
eTrue, eFalse :: Expr
eTrue = EpInj InjR EpUnit
eFalse = EpInj InjL EpUnit

eIf :: Expr -> Expr -> Expr -> Expr
eIf cond t f = EpCase
  cond
  (Alts [Branch [PatInj InjL PatUnit] t, Branch [PatInj InjR PatUnit] f])

ifExpr :: Expr
ifExpr = eIf (EpAnn eTrue (TySum TyUnit TyUnit)) eFalse eTrue

fstExpr :: Expr
fstExpr = EpAnn expr ty
 where
  ty = TyForall
    a
    Star
    (TyForall b Star (TyArrow (TyProd (TyUnVar a) (TyUnVar b)) (TyUnVar a)))
  expr = EpLam
    x
    (EpCase (EpVar x) (Alts [Branch [PatProd (PatVar l) PatWild] (EpVar l)]))
  a = UnSym "a"
  b = UnSym "b"
  x = Sym "x"
  l = Sym "l"

sndExpr, badSndExpr :: Expr
(sndExpr, badSndExpr) = (EpAnn expr ty, EpAnn expr ty')
 where
  ty' = TyForall
    a
    Star
    (TyForall b Star (TyArrow (TyProd (TyUnVar a) (TyUnVar b)) (TyUnVar a)))
  ty = TyForall
    a
    Star
    (TyForall b Star (TyArrow (TyProd (TyUnVar a) (TyUnVar b)) (TyUnVar b)))
  expr = EpLam
    x
    (EpCase (EpVar x) (Alts [Branch [PatProd PatWild (PatVar r)] (EpVar r)]))
  a = UnSym "a"
  b = UnSym "b"
  x = Sym "x"
  r = Sym "r"

swapExpr :: Expr
swapExpr = EpAnn expr ty
 where
  ty = TyForall
    a
    Star
    ( TyForall
      b
      Star
      ( TyArrow (TyProd (TyUnVar a) (TyUnVar b))
                (TyProd (TyUnVar b) (TyUnVar a))
      )
    )
  expr = EpLam
    x
    ( EpCase
      (EpVar x)
      ( Alts
        [Branch [PatProd (PatVar l) (PatVar r)] (EpProd (EpVar r) (EpVar l))]
      )
    )
  a = UnSym "a"
  b = UnSym "b"
  x = Sym "x"
  l = Sym "l"
  r = Sym "r"

{-
rec map = \f -> \xs -> case xs of
  [] -> []
  (y : ys) -> f y : map f ys
-}

mapExpr :: Expr
mapExpr = expr -: ty
 where
  ty = TyForall n Nat $ TyForall alpha Star $ TyForall beta Star $ TyArrow
    (TyArrow (TyUnVar alpha) (TyUnVar beta))
    ( TyArrow (TyVec (TmUnVar n) (TyUnVar alpha))
              (TyVec (TmUnVar n) (TyUnVar beta))
    )
  expr = EpRec mapv $ EpLam f $ EpLam xs $ EpCase (EpVar xs) $ Alts
    [ PatVec Nil ~> EpVec Nil
    , PatVec [PatVar y, PatVar ys] ~> EpVec
      [ EpApp (EpVar f)    (Spine [EpVar y])
      , EpApp (EpVar mapv) (Spine [EpVar f, EpVar ys])
      ]
    ]
  alpha = UnSym "a"
  beta  = UnSym "b"
  n     = UnSym "n"
  mapv  = Sym "map"
  f     = Sym "f"
  xs    = Sym "xs"
  y     = Sym "y"
  ys    = Sym "ys"

pairOfLists, listOfPairs :: Pat
(pairOfLists, listOfPairs) = (f, s)
 where
  f = PatProd (PatVec [PatVar x, PatVar xs]) (PatVec [PatVar y, PatVar ys])
  s = PatVec [patProd x y, patProd xs ys]
  patProd a b = PatProd (PatVar a) (PatVar b)
  x  = Sym "x"
  xs = Sym "xs"
  y  = Sym "y"
  ys = Sym "ys"

zipExpr :: Expr
zipExpr = expr -: ty
 where
  ty = TyForall n Nat $ TyForall alpha Star $ TyForall beta Star $ TyArrow
    ( TyProd (TyVec (TmUnVar n) (TyUnVar alpha))
             (TyVec (TmUnVar n) (TyUnVar beta))
    )
    (TyVec (TmUnVar n) (TyProd (TyUnVar alpha) (TyUnVar beta)))
  expr = EpRec zipv $ EpLam p $ EpCase (EpVar p) $ Alts
    [ PatProd (PatVec Nil)                   (PatVec Nil) ~> EpVec Nil
    , PatProd (PatVec [PatVar x, PatVar xs]) (PatVec [PatVar y, PatVar ys])
      ~> EpVec
           [ EpProd (EpVar x)    (EpVar y)
           , EpApp  (EpVar zipv) (Spine [EpProd (EpVar xs) (EpVar ys)])
           ]
    ]
  alpha = UnSym "a"
  beta  = UnSym "b"
  n     = UnSym "n"
  zipv  = Sym "zip"
  p     = Sym "p"
  x     = Sym "x"
  xs    = Sym "xs"
  y     = Sym "y"
  ys    = Sym "ys"

curriedZipExpr :: Expr
curriedZipExpr = expr -: ty
 where
  ty = TyForall n Nat $ TyForall alpha Star $ TyForall beta Star $ TyArrow
    (TyVec (TmUnVar n) (TyUnVar alpha))
    ( TyArrow (TyVec (TmUnVar n) (TyUnVar beta))
              (TyVec (TmUnVar n) (TyProd (TyUnVar alpha) (TyUnVar beta)))
    )
  expr = EpRec zipv $ EpLam p $ EpLam q $ EpCase (EpVar p) $ Alts
    [ PatVec Nil ~> EpCase (EpVar q) (Alts [PatVec Nil ~> EpVec Nil])
    , PatVec [PatVar x, PatVar xs] ~> EpCase
      (EpVar q)
      ( Alts
        [ PatVec [PatVar y, PatVar ys] ~> EpVec
            [ EpProd (EpVar x)    (EpVar y)
            , EpApp  (EpVar zipv) (Spine [EpProd (EpVar xs) (EpVar ys)])
            ]
        ]
      )
    ]
  alpha = UnSym "a"
  beta  = UnSym "b"
  n     = UnSym "n"
  zipv  = Sym "zip"
  p     = Sym "p"
  q     = Sym "q"
  x     = Sym "x"
  xs    = Sym "xs"
  y     = Sym "y"
  ys    = Sym "ys"


match :: Expr -> [Branch] -> Expr
match e bs = EpCase e (Alts bs)

(-:) = EpAnn
infixr 8 -:

p ~> e = Branch [p] e
infixr 6 ~>

idUnit :: Expr
idUnit = match (EpUnit -: TyUnit) [PatWild ~> EpUnit -: TyUnit]

idType :: Ty
idType = TyForall ua Star (TyArrow uv uv)
 where
  ua = UnSym "t"
  uv = TyUnVar ua

constType :: Ty
constType = TyForall ua Star (TyForall ub Star (TyArrow va (TyArrow vb va)))
 where
  ua = UnSym "a"
  ub = UnSym "b"
  va = TyUnVar ua
  vb = TyUnVar ub

idCtx :: TcCtx
idCtx =
  initialContext
    |> FcVarTy (Sym "id")    idType    Bang
    |> FcVarTy (Sym "const") constType Bang

constApp :: Expr
constApp = EpApp (EpVar (Sym "const")) (Spine [EpUnit])

idApp :: Expr
idApp = EpApp (EpVar (Sym "id")) (Spine [EpUnit])
