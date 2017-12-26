{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Pretty where

import           Overture                                  hiding ((<+>))

import           Types

import Data.Text.Prettyprint.Doc (pretty, Doc, backslash, dot, equals, pipe, colon)
import          qualified Data.Text.Prettyprint.Doc as P
import           Data.Text.Prettyprint.Doc.Render.Terminal
import           Data.Text.Prettyprint.Doc.Util            (putDocW)

import qualified Data.Text.Lazy                            as TL
import qualified Data.Text.Lazy.IO                         as TL

import           Control.Monad.Reader

type Out = Doc AnsiStyle

vsep = P.vsep
vcat = P.vcat
group = P.group
annotate = P.annotate
parens = P.parens
angles = P.angles
brackets = P.brackets
braces = P.braces
align = P.align
indent = P.indent
hsep = P.hsep
sep = P.sep
punctuate = P.punctuate
(<+>) = (P.<+>)

globalIndentWidth :: Int
globalIndentWidth = 2

data PprEnv = PprEnv { _pprEnv_precedence :: Int }

precedence :: Lens' PprEnv Int
precedence = lens _pprEnv_precedence (\e prec -> e { _pprEnv_precedence = prec })

type PprM = Reader PprEnv

runPprM :: PprM a -> a
runPprM f = runReader f iEnv
  where iEnv = PprEnv (-1)

assoc :: Int -> PprM a -> PprM a
assoc p = local (precedence .~ p)

class AnsiPretty a where
  -- | Pretty-print a value. The default implementation
  -- omits surrounding parens.
  ppr :: a -> Out
  ppr = runPprM . pprM

  pprM :: a -> PprM Out
  pprM = pure . ppr

wrapOn :: Bool -> (PprM a -> PprM a) -> PprM a -> PprM a
wrapOn c f = if c then f else id
{-# INLINE wrapOn #-}

above :: (PprM a -> PprM a) -> Int -> PprM a -> PprM a
above f p m = do
  outerPrec <- view precedence
  wrapOn (outerPrec >>> p) f (assoc (p + 1) m)

nowrap :: PprM a -> PprM a
nowrap = assoc (-1)

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

a <-> b = vsep [a, b]
a <@> b = vcat [a, b]

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

pprPolarity :: Polarity -> Out
pprPolarity = fmtPolarity . \case
  Positive -> "+"
  Negative -> "-"
  Nonpolar -> "0"

pprBin :: Binop -> Out
pprBin = fmtBinop . \case
  OpArrow -> "->"
  OpSum   -> "+"
  OpProd  -> "×"

pprUnVar :: UnVar -> Out
pprUnVar (UnSym s) = fmtUnVar (ppr s)

pprExVar :: ExVar -> Out
pprExVar (ExSym s) = fmtExVar (ppr s <> "^")

pprVar :: Var -> Out
pprVar (Sym s) = fmtVar (ppr s)

pprPrin :: Prin -> Out
pprPrin = fmtPrin . \case
  Bang  -> "!"
  Slash -> "?"

pprTyWithPrin :: (Ty, Prin) -> Out
pprTyWithPrin (ty, p) = parens (ppr p) <+> "" <> ppr ty

pprTy :: Ty -> Out
pprTy = fmtTy . \case
  TyUnit     -> "Unit"
  TyUnVar un -> ppr un
  TyExVar ex -> ppr ex
  TyBinop l op r ->
    parens (parens (ppr op) <+> parens (ppr l) <+> parens (ppr r))
  TyForall s sort ty ->
    fmtQuantifier "∀" <> parens (ppr s <+> ":" <+> ppr sort) <+> ppr ty
  TyVec n v -> "Vec" <+> ppr n <+> ppr v

pprTm :: Tm -> Out
pprTm = fmtTm . \case
  TmUnit         -> "Unit"
  TmUnVar un     -> ppr un
  TmExVar ex     -> ppr ex
  TmBinop l op r -> ppr l <+> ppr op <+> ppr r
  TmNat n        -> ppr n
  -- tm             -> ppr (tshow tm)

pprNat :: Nat -> Out
pprNat = fmtNat . \case
  Zero   -> "Z"
  Succ n -> "S" <+> parens (ppr n)

pprSort :: Sort -> Out
pprSort = fmtSort . \case
  Star -> "*"
  Nat  -> "Nat"

pprExpr :: Expr -> Out
pprExpr = fmtExpr . \case
  EpUnit -> "Unit"
  EpLam var e ->
    fmtLam backslash <> ppr var <+> fmtLamArrow "->" <+> parens (ppr e)
  EpRec var e        -> fmtRec "rec" <+> ppr var <+> parens (ppr e)
  EpAnn e   ty       -> align (parens (ppr e) <@> parens (ppr ty))
  EpVar s            -> ppr s
  EpApp  e (Spine s) -> parens (ppr (Spine (e : s)))
  EpProd l r         -> parens (ppr l <+> ppr OpProd <+> ppr r)
  EpCase e alts ->
    fmtMatch "case" <+> ppr e <+> indent globalIndentWidth (ppr alts)
  EpVec v -> ppr v
  -- e       -> parens (ppr (tshow e))

pprAlts :: Alts -> Out
pprAlts (Alts bs) = hsep (map (\b -> fmtAltPipe "of" <+> ppr b) bs)

pprBranch :: Branch -> Out
pprBranch (Branch p e) =
  sep (punctuate (fmtOrPatPipe pipe) (map ppr p))
    <+> fmtCaseArrow "->"
    <+> ppr e

pprPat :: Pat -> Out
pprPat = fmtPat . \case
  PatWild     -> fmtPatWild "_"
  PatUnit     -> "Unit"
  PatVar s    -> ppr s
  PatVec v    -> ppr v
  PatProd l r -> parens (ppr l <+> "*" <+> ppr r)
  PatInj  i p -> parens ((if i == InjL then "L" else "R") <+> ppr p)

pprVec :: AnsiPretty a => Vec a -> Out
pprVec Empty          = "nil"
pprVec (Cons x Empty) = ppr x
pprVec (Cons x xs   ) = hsep [ppr x, "::", ppr xs]

pprCtx :: Ctx -> Out
pprCtx (Ctx s) = fmtCtx (align (sep (map ppr s & toList)))

pprProp :: Prop -> Out
pprProp (Equation a b) = angles (ppr a <+> equals <+> ppr b)

pprFact :: Fact -> Out
pprFact f = brackets (ppr' f)
 where
  ppr' :: Fact -> Out
  ppr' = \case
    FcExEq ex sort tm   -> ppr ex <+> colon <+> ppr sort <+> equals <+> ppr tm
    FcUnSort un sort    -> ppr un <+> colon <+> ppr sort
    FcExSort ex sort    -> ppr ex <+> colon <+> ppr sort
    FcUnEq   un tm      -> ppr un <+> equals <+> ppr tm
    FcUnMark   un       -> "▶" <> ppr un
    FcExMark   ex       -> "▶" <> ppr ex
    FcPropMark prop     -> "▶" <> ppr prop
    FcVarTy var ty prin -> ppr var <+> colon <+> ppr ty <+> ppr prin

pprSpine :: Spine -> Out
pprSpine (Spine s) = hsep (map ppr s)

pprRuleName :: RuleName -> Doc a
pprRuleName (RuleName a) = pretty a

instance AnsiPretty RuleName where ppr = pprRuleName

pprJudgmentD :: JudgmentD -> Out
pprJudgmentD = \case
  JRuleN r   -> ppr r
  JJudgN t   -> ppr t
  JCtx   ctx -> indent globalIndentWidth (ppr ctx)
  JExpr  ep  -> ppr ep

instance AnsiPretty JudgmentD where ppr = pprJudgmentD

treeIndentWidth = globalIndentWidth

pprTree :: AnsiPretty a => Tree a -> Out
pprTree = \case
  Leaf a  -> ppr a
  Rose as -> vsep (map (indent treeIndentWidth . ppr) as)

instance AnsiPretty a => AnsiPretty (Tree a) where ppr = pprTree

pprLogItem :: AnsiPretty a => LogItem a -> Out
pprLogItem (LogItem d m) = pretty d <+> colon <+> group (ppr m)

instance AnsiPretty a => AnsiPretty (LogItem a) where ppr = pprLogItem
