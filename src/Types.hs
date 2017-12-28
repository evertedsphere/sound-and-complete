{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DerivingStrategies, DeriveGeneric, DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts #-}

module Types where

import Overture 

import Data.Sequence (Seq)
import qualified Data.Sequence as S
import GHC.Exts (IsList)

--
-- Representations of types and terms for algorithmic typing.
--

newtype Var   = Sym   Text deriving (Show, Ord, Eq, Generic, Data)

newtype UnVar = UnSym Text deriving (Show, Ord, Eq, Generic, Data)
newtype ExVar = ExSym Text deriving (Show, Ord, Eq, Generic, Data)

-- | Subtyping polarity
data Polarity = Positive | Negative | Nonpolar deriving (Show, Ord, Eq, Generic, Data)

-- | Expressions
data Expr
  = EpVar   Var
  | EpUnit
  | EpLam   Var   Expr
  | EpRec   Var   Expr
  | EpApp   Expr  Spine
  | EpAnn   Expr  Ty
  | EpProd  Expr  Expr
  | EpInj   Inj   Expr
  | EpCase  Expr  Alts
  | EpVec   (Vec Expr)
  deriving (Show, Ord, Eq, Generic, Data)

instance Plated Expr 

isValue :: Expr -> Bool
isValue EpVar{} = True
isValue EpUnit = True
isValue (EpAnn e _) = isValue e
isValue _ = unimplemented

data Inj = InjL | InjR
  deriving (Show, Ord, Eq, Generic, Data)

pattern EpInjL :: Expr -> Expr
pattern EpInjL e = EpInj InjL e

pattern EpInjR :: Expr -> Expr
pattern EpInjR e = EpInj InjR e

newtype Spine = Spine [Expr]
  deriving (Show, Ord, Eq, Generic, Data)

newtype Alts = Alts [Branch]
  deriving (Show, Ord, Eq, Generic, Data)

-- | Patterns
data Pat
  = PatWild  -- not shown in Figure 1
  | PatUnit  -- not shown in Figure 1
  | PatVar   Var
  | PatProd  Pat   Pat
  | PatInj   Inj   Pat
  | PatVec   (Vec Pat)
  deriving (Show, Ord, Eq, Generic, Data)

data Branch = Branch [Pat] Expr
  deriving (Show, Ord, Eq, Generic, Data)

data Binop    = OpArrow | OpSum | OpProd    deriving (Show, Ord, Eq, Generic, Data)
data Nat      = Zero    | Succ Nat          deriving (Show, Ord, Eq, Generic, Data)

newtype Vec  a  = Vec [a]         deriving (Show, Ord, Eq, Generic, Data, IsList)

deriving instance Functor Vec 
deriving instance Foldable Vec 
instance AsEmpty (Vec a) where
  _Empty = prism' (const Nil) (\case
    Nil -> Just ()
    _ -> Nothing)

pattern Nil <- Vec []
  where Nil = Vec []

pattern Cons x xs = Vec (x : xs)

-- | Terms
data Tm
  = TmUnit
  | TmUnVar   UnVar
  | TmExVar   ExVar
  | TmBinop   Tm Binop Tm
  | TmNat     Nat
  | TmVec     (Vec Expr)
  deriving (Show, Ord, Eq, Generic, Data)

pattern TmSum :: Tm -> Tm -> Tm
pattern TmSum l r = TmBinop l OpSum r

pattern TmProd :: Tm -> Tm -> Tm
pattern TmProd l r = TmBinop l OpProd r

pattern TmArrow :: Tm -> Tm -> Tm
pattern TmArrow l r = TmBinop l OpArrow r

instance Plated Tm

instance HasTerms Tm where
  terms f = 
    \case
      TmBinop a op b -> TmBinop <$> terms f a <*> pure op <*> terms f b
      -- TmVec ty -> TmVec <$> terms f n <*> terms f ty
      o -> pure o

class HasTerms a where
  terms :: Traversal' a Tm

-- | Propositions (equality constraints)
data Prop = Equation Tm Tm
  deriving (Show, Ord, Eq, Generic, Data)

instance HasTerms Prop where
  terms f (Equation x y) = Equation <$> f x <*> f y

data Sort  = Star | Nat
  deriving (Show, Ord, Eq, Generic, Data)

-- | Types
data Ty
  = TyUnit
  | TyUnVar   UnVar
  | TyExVar   ExVar
  | TyArrow   Ty    Ty
  | TySum     Ty    Ty
  | TyProd    Ty    Ty
  | TyForall  UnVar Sort Ty
  | TyExists  UnVar Sort Ty
  | TyImplies Prop  Ty
  | TyWith    Ty    Prop
  | TyVec     Tm   Ty
  deriving (Show, Ord, Eq, Generic, Data)

instance Plated Ty

instance HasTerms Ty where
  terms f = 
    \case
      TyForall u s ty -> TyForall <$> pure u <*> pure s <*> terms f ty
      TyExists u s ty -> TyExists <$> pure u <*> pure s <*> terms f ty
      TyBinop a op b -> TyBinop <$> terms f a <*> pure op <*> terms f b
      TyImplies eq ty -> TyImplies <$> terms f eq <*> terms f ty
      TyWith ty eq -> TyWith <$> terms f ty <*> terms f eq
      TyVec n ty -> TyVec <$> terms f n <*> terms f ty
      o -> pure o

pattern TyBinop :: Ty -> Binop -> Ty -> Ty
pattern TyBinop left op right <- (binopOfType -> Just (left, op, right))
  where TyBinop = binopType

binopOfType :: Ty -> Maybe (Ty, Binop, Ty)
binopOfType (TyArrow a b) = Just (a, OpArrow, b)
binopOfType (TySum   a b) = Just (a, OpSum,   b)
binopOfType (TyProd  a b) = Just (a, OpProd,  b)
binopOfType _             = Nothing

binopType :: Ty -> Binop -> Ty -> Ty
binopType a OpArrow b = TyArrow a b
binopType a OpSum   b = TySum a b
binopType a OpProd  b = TyProd a b

-- | Principalities.
data Prin 
  = Bang  -- ^ principal
  | Slash -- ^ nonprincipal
  deriving (Show, Ord, Eq)

-- | Elements of the context, representing units of knowledge
-- possessed by the typechecker.
data Fact
  -- sort judgments
  = FcUnSort   UnVar Sort
  | FcExSort   ExVar Sort
  -- equality judgments
  | FcUnEq     UnVar      Tm
  | FcExEq     ExVar Sort Tm
  -- markers
  | FcUnMark   UnVar
  | FcExMark   ExVar
  | FcPropMark Prop
  -- variable types (with principality)
  | FcVarTy    Var   Ty   Prin
  deriving (Show, Ord, Eq)

data VarSort = Univ | Extl

pattern FcMark v s <- (markOfFact -> Just (v, s))
  where FcMark = markFact

markOfFact (FcUnMark (UnSym s)) = Just (Univ, s)
markOfFact (FcExMark (ExSym s)) = Just (Extl, s)
markOfFact _                    = Nothing

markFact Univ s = FcUnMark (UnSym s)
markFact Extl s = FcExMark (ExSym s)

sortOfFact (FcUnSort (UnSym s) _) = Just (Univ, s)
sortOfFact (FcExSort (ExSym s) _) = Just (Extl, s)
sortOfFact _                      = Nothing

newtype Ctx = Ctx (Seq Fact)
  deriving (Show, Ord, Eq, Monoid, Semigroup)

-- | A possibly-inconsistent context
-- This is isomorphic to Maybe Ctx.
data PICtx
  = ConCtx Ctx
  -- ^ A consistent context.
  | Bottom
  -- ^ Inconsistency.
  deriving (Show, Ord, Eq)

(|>) :: Ctx -> Fact -> Ctx
Ctx c |> f = Ctx (c S.|> f)

data JudgmentItem
  = JCtx Ctx
  | JPrin Prin
  | JExpr Expr
  | JTy Ty
  | JTm Tm
  | JAlts Alts
  | JJudgN Text
  | JRuleN RuleName
  | Pre PreData
  | RuleMatch Rule
  | Post PostData

data PreData
  = PreTypeWF Ctx Ty
  | PreInfer Ctx Expr
  | PreCheck Ctx Expr Ty Prin
  | PreSpine Ctx Spine Ty Prin
  | PreSpineRecover Ctx Spine Ty Prin

data Rule
  = RuleCheck CheckRule
  | RuleInfer InferRule
  | RuleSpine SpineRule
  | RuleSpineRecover SpineRecoverRule
  | RuleMatchBranches MatchBranchesRule

data SpineRule = RNilSpine | RArrowSpine | RForallSpine deriving Show
data SpineRecoverRule = RSpinePass | RSpineRecover deriving Show
data CheckRule = RForallIntro | RArrowIntro | RCase | RUnitIntro_Extl deriving Show
data InferRule = RVar | RArrowE deriving Show
data MatchBranchesRule = RMatchSeq | RMatchBase | RMatchNil deriving Show

data PostData
  = PostCheck Ctx
  | PostInfer Ty Prin Ctx
  | PostSpine Ty Prin Ctx
  | PostSpineRecover Ty Prin Ctx

newtype RuleName = RuleName Text

data Tree a = Leaf a | Rose [Tree a]
  deriving Foldable

data LogItem a = LogItem { _logItem_depth :: Int, _logItem_message :: a }
