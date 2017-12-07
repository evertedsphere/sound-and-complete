{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeSynonymInstances #-}
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

render =
  TL.putStrLn
    . TL.replace "\ESC" "\\e"
    . renderLazy
    . layoutPretty defaultLayoutOptions

class AnsiPretty a where ppr :: a -> Doc AnsiStyle

instance AnsiPretty Text  where ppr = pretty

instance AnsiPretty Polarity where ppr = pprPolarity
instance AnsiPretty Binop where ppr = pprBin

instance AnsiPretty UnVar where ppr = pprUnVar
instance AnsiPretty ExVar where ppr = pprExVar
instance AnsiPretty Var   where ppr = pprVar

instance AnsiPretty a => AnsiPretty (Vec a) where ppr = pprVec
instance AnsiPretty Pat where ppr = pprPat
instance AnsiPretty Ctx where ppr = pprCtx

instance AnsiPretty Spine where ppr = pprSpine
instance AnsiPretty Fact where ppr = pprFact

id :: a -> a
id x = x

fmtSort = annotate (color Blue)
fmtUnVar = annotate (color Yellow)
fmtExVar = annotate (color Magenta)
fmtVar = annotate (color Green)
fmtPrin = id
fmtPolarity = id
fmtBinop = id
fmtTy = id
fmtTm = id
fmtNat = id
fmtCtx = id
fmtPat = id
fmtExpr = id

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

-- pprTyWithPrin :: Ty -> Prin -> Doc AnsiStyle
-- pprTyWithPrin ty p = parens (pprPrin p) <> " " <> pprTy ty

instance AnsiPretty Ty where ppr = pprTy
instance AnsiPretty Tm where ppr = pprTm

pprTy :: Ty -> Doc AnsiStyle
pprTy = fmtTy . \case
  TyUnit         -> "Unit"
  TyUnVar un     -> pprUnVar un
  TyExVar ex     -> pprExVar ex
  TyBinop l op r -> parens (pprTy l <+> pprBin op <+> pprTy r)
  TyForall s sort ty ->
    "∀"
      <>  parens (pprUnVar s <+> ":" <+> pprSort sort)
      <>  line
      <>  "."
      <+> pprTy ty
  TyVec n v -> "Vec" <+> pprTm n <+> pprTy v
  ty        -> ppr (tshow ty)

pprTm :: Tm -> Doc AnsiStyle
pprTm = fmtTm . \case
  TmUnit         -> "Unit"
  TmUnVar un     -> ppr un
  TmExVar ex     -> ppr ex
  TmBinop l op r -> pprTm l <+> ppr op <+> pprTm r
  TmNat n        -> pprNat n
  tm             -> ppr (tshow tm)

pprNat :: Nat -> Doc AnsiStyle
pprNat = fmtNat . \case
  Zero   -> "Z"
  Succ n -> "S" <+> parens (pprNat n)

pprSort :: Sort -> Doc AnsiStyle
pprSort = fmtSort . ppr . tshow

instance AnsiPretty Expr where ppr = pprExpr

pprExpr :: Expr -> Doc AnsiStyle
pprExpr = fmtExpr . \case
  EpUnit             -> "Unit"
  EpLam var e        -> "\\" <> ppr var <> " -> " <> ppr e
  EpRec var e        -> "rec " <> ppr var <> ". " <> ppr e
  EpAnn e   ty       -> parens (ppr e) <+> align (":" <+> ppr ty)
  EpVar s            -> pprVar s
  EpApp  e (Spine s) -> parens (pprSpine (Spine (e : s)))
  EpProd l r         -> parens (ppr l <+> pprBin OpProd <+> ppr r)
  EpCase e alts ->
    "case" <+> ppr e <+> line <> indent globalIndentWidth (pprAlts alts)
  EpVec v -> pprVec v
  e       -> parens (ppr (tshow e))

pprAlts :: Alts -> Doc AnsiStyle
pprAlts (Alts bs) = vcat (map pprBranch bs)

pprBranch :: Branch -> Doc AnsiStyle
pprBranch (Branch p e) = sep (punctuate "|" (map ppr p)) <+> "->" <+> pprExpr e

pprPat :: Pat -> Doc AnsiStyle
pprPat = fmtPat . \case
  PatUnit  -> "Unit"
  PatVar s -> ppr s
  PatVec v -> pprVec v

pprVec :: AnsiPretty a => Vec a -> Doc AnsiStyle
pprVec Empty          = "[]"
pprVec (Cons x Empty) = ppr x
pprVec (Cons x xs   ) = hsep [ppr x, "::", pprVec xs]

pprCtx :: Ctx -> Doc AnsiStyle
pprCtx (Ctx s) = fmtCtx (sep (s & toList & map pprFact))

pprProp :: Prop -> Doc AnsiStyle
pprProp (Equation a b) = "<" <> pprTm a <> " = " <> pprTm b <> ">"

pprFact :: Fact -> Doc AnsiStyle
pprFact f = "[" <> pprFact' f <> "]"
 where
  pprFact' :: Fact -> Doc AnsiStyle
  pprFact' = \case
    FcExEq ex sort tm ->
      ppr ex <> " : " <> pprSort sort <> " = " <> pprTm tm
    FcUnSort un sort    -> pprUnVar un <> " : " <> pprSort sort
    FcExSort ex sort    -> pprExVar ex <> " : " <> pprSort sort
    FcUnEq   un tm      -> pprUnVar un <> " = " <> pprTm tm
    FcUnMark   un       -> "▶" <> pprUnVar un
    FcExMark   ex       -> "▶" <> pprExVar ex
    FcPropMark prop     -> "▶" <> pprProp prop
    FcVarTy var ty prin -> pprVar var <> " : " <> pprTy ty <+> pprPrin prin

pprSpine :: Spine -> Doc AnsiStyle
pprSpine (Spine s) = hsep (map ppr s)

