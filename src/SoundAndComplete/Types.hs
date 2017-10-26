{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DerivingStrategies, DeriveGeneric, DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}

module SoundAndComplete.Types where

import Overture hiding (set, pred, sum)

import Data.Sequence (Seq, pattern (:<|), pattern (:|>))
import qualified Data.Sequence as S

import Data.Hashable

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

pattern EpInjL, EpInjR :: Expr -> Expr
pattern EpInjL e = EpInj InjL e
pattern EpInjR e = EpInj InjR e

data Spine = Spine [Expr]
  deriving (Show, Ord, Eq, Generic, Data)

data Alts = Alts [Branch]
  deriving (Show, Ord, Eq, Generic, Data)

-- | Patterns
data Pat
  = PatVar   Var
  | PatProd  Expr  Expr
  | PatInj   Inj   Expr
  | PatVec   (Vec Pat)
  deriving (Show, Ord, Eq, Generic, Data)

data Branch = Branch [Pat] Expr
  deriving (Show, Ord, Eq, Generic, Data)

data Binop    = OpArrow | OpSum | OpProd    deriving (Show, Ord, Eq, Generic, Data)
data Nat      = Zero    | Succ Nat          deriving (Show, Ord, Eq, Generic, Data)

data Vec   a  = Empty   | Cons a (Vec a)    deriving (Show, Ord, Eq, Generic, Data)

-- | Terms
data Tm
  = TmUnit
  | TmUnVar   UnVar
  | TmExVar   ExVar
  | TmArrow   Tm Tm
  | TmSum     Tm Tm
  | TmProd    Tm Tm
  | TmNat     Nat
  | TmVec     (Vec Expr)
  deriving (Show, Ord, Eq, Generic, Data)

instance Plated Tm

pattern TmBinop :: Tm -> Binop -> Tm -> Tm
pattern TmBinop left op right <- (binopOfTerm -> Just (left, op, right))
  where TmBinop = binopTerm

binopOfTerm :: Tm -> Maybe (Tm, Binop, Tm)
binopOfTerm (TmArrow a b) = Just (a, OpArrow, b)
binopOfTerm (TmSum   a b) = Just (a, OpSum,   b)
binopOfTerm (TmProd  a b) = Just (a, OpProd,  b)
binopOfTerm _             = Nothing

binopTerm :: Tm -> Binop -> Tm -> Tm
binopTerm a OpArrow b = TmArrow a b
binopTerm a OpSum   b = TmSum a b
binopTerm a OpProd  b = TmProd a b

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
  | TyVec     Nat   Ty
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
      TyVec n ty -> TyVec <$> pure n <*> terms f ty
      o -> pure o

ty :: Ty
ty = TyWith (TyArrow TyUnit (TyImplies (Equation TmUnit TmUnit) TyUnit)) (Equation TmUnit TmUnit)

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
  deriving (Show, Ord, Eq)

pattern FcMark v s <- (markOfFact -> Just (v, s))
  where FcMark = markFact

markOfFact (FcUnMark (UnSym s)) = Just (Univ, s)
markOfFact (FcExMark (ExSym s)) = Just (Extl, s)
markOfFact _                    = Nothing

markFact Univ s = (FcUnMark (UnSym s))
markFact Extl s = (FcExMark (ExSym s))

sortOfFact (FcUnSort (UnSym s) _) = Just (Univ, s)
sortOfFact (FcExSort (ExSym s) _) = Just (Extl, s)
sortOfFact _                      = Nothing

newtype Ctx = Ctx (Seq Fact)
  deriving (Show, Ord, Eq)
  deriving newtype Monoid
  deriving newtype Semigroup

-- | A possibly-inconsistent context.
data PICtx 
  = ConCtx Ctx
  -- ^ A consistent context.
  | Bottom
  -- ^ Inconsistency.
  deriving (Show, Ord, Eq)

(|>) :: Ctx -> Fact -> Ctx
Ctx c |> f = Ctx (c S.|> f)
