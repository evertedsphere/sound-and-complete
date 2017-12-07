{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}
module SoundAndComplete.Pretty where

import Overture hiding ((<+>),Empty)

import SoundAndComplete.Types

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Util (putDocW)
import Data.Text.Prettyprint.Doc.Render.Terminal

import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TL

globalIndentWidth :: Int
globalIndentWidth = 2

class AnsiPretty a where ppr :: a -> Doc AnsiStyle

instance AnsiPretty Expr where ppr = pprExpr
instance AnsiPretty Tm where ppr = pprTm
instance AnsiPretty Ty where ppr = pprTy
instance AnsiPretty (Ty,Prin) where ppr = pprTyWithPrin
instance AnsiPretty Nat where ppr = pprNat
instance AnsiPretty Branch where ppr = pprBranch
instance AnsiPretty Alts where ppr = pprAlts
instance AnsiPretty Prin where ppr = pprPrin
instance AnsiPretty Prop where ppr = pprProp
instance AnsiPretty Sort where ppr = pprSort
instance AnsiPretty Fact where ppr = pprFact
instance AnsiPretty Spine where ppr = pprSpine
instance AnsiPretty Ctx where ppr = pprCtx
instance AnsiPretty Pat where ppr = pprPat
instance AnsiPretty a => AnsiPretty (Vec a) where ppr = pprVec
instance AnsiPretty Var   where ppr = pprVar
instance AnsiPretty ExVar where ppr = pprExVar
instance AnsiPretty UnVar where ppr = pprUnVar
instance AnsiPretty Binop where ppr = pprBin
instance AnsiPretty Polarity where ppr = pprPolarity
instance AnsiPretty Text  where ppr = pretty

id :: a -> a
id x = x

fmtSort = annotate (color Blue)
fmtUnVar = annotate (color Yellow)
fmtExVar = annotate (color Magenta)
fmtVar = id
fmtPrin = id
fmtPolarity = id
fmtBinop = id
fmtTy = id
fmtTm = id
fmtNat = id
fmtCtx = id
fmtPat = id
fmtPatWild = id
fmtExpr = id

fmtKw = annotate (color Green <> bold)
fmtRec = fmtKw
fmtMatch = fmtKw

fmtSynSym = annotate (color Green <> bold)
fmtAltPipe = fmtSynSym
fmtOrPatPipe = fmtSynSym
fmtLam = fmtSynSym
fmtLamArrow = fmtSynSym
fmtCaseArrow = fmtSynSym

fmtQuantifier = annotate (color Yellow)

pprPolarity :: Polarity -> Doc AnsiStyle
pprPolarity = fmtPolarity . \case
  Positive -> "+"
  Negative -> "-"
  Nonpolar -> "0"

pprBin :: Binop -> Doc AnsiStyle
pprBin = fmtBinop . \case
  OpArrow -> "->"
  OpSum   -> "+"
  OpProd  -> "×"

pprUnVar :: UnVar -> Doc AnsiStyle
pprUnVar (UnSym s) = fmtUnVar (ppr s)

pprExVar :: ExVar -> Doc AnsiStyle
pprExVar (ExSym s) = fmtExVar (ppr s <> "^")

pprVar :: Var -> Doc AnsiStyle
pprVar (Sym s) = fmtVar (ppr s)

pprPrin :: Prin -> Doc AnsiStyle
pprPrin = fmtPrin . \case
  Bang  -> "!"
  Slash -> "?"

pprTyWithPrin :: (Ty, Prin) -> Doc AnsiStyle
pprTyWithPrin (ty,p) = parens (ppr p) <+> "" <> ppr ty

pprTy :: Ty -> Doc AnsiStyle
pprTy = fmtTy . \case
  TyUnit         -> "Unit"
  TyUnVar un     -> ppr un
  TyExVar ex     -> ppr ex
  TyBinop l op r -> parens (ppr l <+> ppr op <+> ppr r)
  TyForall s sort ty ->
    fmtQuantifier "∀" <> parens (ppr s <+> ":" <+> ppr sort) <> line <> "." <+> ppr ty
  TyVec n v -> "Vec" <+> ppr n <+> ppr v

pprTm :: Tm -> Doc AnsiStyle
pprTm = fmtTm . \case
  TmUnit         -> "Unit"
  TmUnVar un     -> ppr un
  TmExVar ex     -> ppr ex
  TmBinop l op r -> ppr l <+> ppr op <+> ppr r
  TmNat n        -> ppr n
  -- tm             -> ppr (tshow tm)

pprNat :: Nat -> Doc AnsiStyle
pprNat = fmtNat . \case
  Zero   -> "Z"
  Succ n -> "S" <+> parens (ppr n)

pprSort :: Sort -> Doc AnsiStyle
pprSort = fmtSort . ppr . tshow

pprExpr :: Expr -> Doc AnsiStyle
pprExpr = fmtExpr . \case
  EpUnit             -> "Unit"
  EpLam var e        -> fmtLam "\\" <> ppr var <+> fmtLamArrow "->" <+> ppr e
  EpRec var e        -> fmtRec "rec" <+> ppr var <> "." <+> ppr e
  EpAnn e   ty       -> parens (ppr e) <+> align (":" <+> ppr ty)
  EpVar s            -> ppr s
  EpApp  e (Spine s) -> parens (ppr (Spine (e : s)))
  EpProd l r         -> parens (ppr l <+> ppr OpProd <+> ppr r)
  EpCase e alts ->
    fmtMatch "match" <+> ppr e <+> line <> indent globalIndentWidth (ppr alts)
  EpVec v -> ppr v
  -- e       -> parens (ppr (tshow e))

pprAlts :: Alts -> Doc AnsiStyle
pprAlts (Alts bs) = vcat (map (\b -> fmtAltPipe "|" <+> ppr b) bs)

pprBranch :: Branch -> Doc AnsiStyle
pprBranch (Branch p e) = sep (punctuate (fmtOrPatPipe "|") (map ppr p)) <+> fmtCaseArrow "->" <+> ppr e

pprPat :: Pat -> Doc AnsiStyle
pprPat = fmtPat . \case
  PatWild -> fmtPatWild "_"
  PatUnit  -> "Unit"
  PatVar s -> ppr s
  PatVec v -> ppr v
  PatProd l r -> parens (ppr l <+> "*" <+> ppr r)
  PatInj i p -> parens ((if i == InjL then "L" else "R") <+> ppr p)

pprVec :: AnsiPretty a => Vec a -> Doc AnsiStyle
pprVec Empty          = "[]"
pprVec (Cons x Empty) = ppr x
pprVec (Cons x xs   ) = hsep [ppr x, "::", ppr xs]

pprCtx :: Ctx -> Doc AnsiStyle
pprCtx (Ctx s) = fmtCtx (sep (s & toList & map ppr))

pprProp :: Prop -> Doc AnsiStyle
pprProp (Equation a b) = "<" <> ppr a <+> "=" <+> ppr b <> ">"

pprFact :: Fact -> Doc AnsiStyle
pprFact f = "[" <> ppr' f <> "]"
 where
  ppr' :: Fact -> Doc AnsiStyle
  ppr' = \case
    FcExEq ex sort tm   -> ppr ex <+> ":" <+> ppr sort <+> "=" <+> ppr tm
    FcUnSort un sort    -> ppr un <+> ":" <+> ppr sort
    FcExSort ex sort    -> ppr ex <+> ":" <+> ppr sort
    FcUnEq   un tm      -> ppr un <+> "=" <+> ppr tm
    FcUnMark   un       -> "▶" <> ppr un
    FcExMark   ex       -> "▶" <> ppr ex
    FcPropMark prop     -> "▶" <> ppr prop
    FcVarTy var ty prin -> ppr var <+> ":" <+> ppr ty <+> ppr prin

pprSpine :: Spine -> Doc AnsiStyle
pprSpine (Spine s) = hsep (map ppr s)

