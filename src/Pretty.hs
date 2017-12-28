{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables          #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeSynonymInstances       #-}
module Pretty where

import           Overture                                  hiding ((<+>), (^^))

import           Types

import           Data.Text.Prettyprint.Doc                 (Doc, backslash, dot,
                                                            pipe, pretty)
import qualified Data.Text.Prettyprint.Doc                 as P
import           Data.Text.Prettyprint.Doc.Render.Terminal
import           Data.Text.Prettyprint.Doc.Util            (putDocW)

import qualified Data.Text.Lazy                            as TL
import qualified Data.Text.Lazy.IO                         as TL

import           Control.Monad.Reader
import           Data.String

type Out = Doc AnsiStyle
type OutM = PprM Out

type OutEndo = OutM -> OutM
type OutFold = forall f. Foldable f => f OutM -> OutM

renderStdout :: AnsiPretty a => a -> IO ()
renderStdout = TL.putStrLn . renderText

renderText :: AnsiPretty a => a -> TL.Text
renderText =
  TL.replace "\\e" "\ESC"
    . renderLazy
    . P.layoutPretty layoutOpts
    . runPprM
    . pprM
  where layoutOpts = P.LayoutOptions (P.AvailablePerLine 80 0.7)

liftOutM :: (Foldable t) => ([a] -> b) -> t (PprM a) -> PprM b
liftOutM f = map f . sequence . toList

sep, vsep, hsep, fsep :: OutFold
sep = liftOutM P.sep
vsep = liftOutM P.vsep
hsep = liftOutM P.hsep
fsep = liftOutM P.fillSep

cat, vcat, hcat, fcat :: OutFold
cat = liftOutM P.cat
vcat = liftOutM P.vcat
hcat = liftOutM P.hcat
fcat = liftOutM P.fillCat

group :: OutEndo
group = map P.group

annotate :: AnsiStyle -> OutEndo
annotate = map . P.annotate

parens, angles, braces, brackets :: OutEndo
parens = map P.parens
angles = map P.angles
brackets = map P.brackets
braces = map P.braces

align :: OutEndo
align = map P.align

indent :: Int -> OutEndo
indent = map . P.indent

nest :: Int -> OutEndo
nest = map . P.nest

hang :: Int -> OutEndo
hang = map . P.hang

column :: (Int -> PprM Out) -> PprM Out
column f = PprM (\env -> P.column (pprWithEnv env . f))

nesting :: (Int -> PprM Out) -> PprM Out
nesting f = PprM (\env -> P.nesting (pprWithEnv env . f))

-- punctuate :: OutM -> PprM [Out] -> PprM [Out]
-- punctuate p os = P.punctuate <$> p <*> os

infixr 5 <+>
(<+>) :: OutM -> OutM -> OutM
(<+>) = liftA2 (P.<+>)

globalIndentWidth :: Int
globalIndentWidth = 2

data PprEnv = PprEnv { _pprEnv_precedence :: Int }

precedence :: Lens' PprEnv Int
precedence =
  lens _pprEnv_precedence (\e prec -> e { _pprEnv_precedence = prec })

newtype PprM a = PprM { unPprM :: PprEnv -> a }
  deriving (Functor, Applicative, Monad, MonadReader PprEnv, Semigroup)

pprWithEnv :: PprEnv -> PprM a -> a
pprWithEnv = flip unPprM

runPprM :: PprM a -> a
runPprM f = unPprM f iEnv where iEnv = PprEnv (-1)

assoc :: Int -> PprM a -> PprM a
assoc p = local (precedence .~ p)

infixr 8 %%
(%%) = assoc

class AnsiPretty a where
  -- | Pretty-print a value. The default implementation
  -- omits surrounding parens.
  ppr :: a -> Out
  ppr = runPprM . pprM

  pprM :: a -> OutM
  pprM = pure . ppr

wrapOn :: Bool -> (PprM a -> PprM a) -> PprM a -> PprM a
wrapOn c f = if c then f else id
{-# INLINE wrapOn #-}

above :: Int -> (PprM a -> PprM a) -> PprM a -> PprM a
above p f m = do
  outerPrec <- view precedence
  wrapOn (outerPrec >>> p) f (assoc (p + 1) m)

infixr 8 ^^
prec ^^ body = above prec parens body

nowrap :: PprM a -> PprM a
nowrap = assoc (-1)

instance (a ~ Out) => IsString (PprM a) where fromString = pure . fromString

instance AnsiPretty Expr where pprM = pprExprM
instance AnsiPretty Alts where pprM = pprAltsM
instance AnsiPretty Tm where pprM = pprTmM
instance AnsiPretty Ty where pprM = pprTyM
instance AnsiPretty (Ty,Prin) where pprM = pprTyWithPrinM
instance AnsiPretty Nat where pprM = pprNatM
instance AnsiPretty Branch where pprM = pprBranchM
instance AnsiPretty Prin where pprM = pprPrinM
instance AnsiPretty Prop where pprM = pprPropM
instance AnsiPretty Sort where pprM = pprSortM
instance AnsiPretty Fact where pprM = pprFactM
instance AnsiPretty Spine where pprM = pprSpineM
instance AnsiPretty Ctx where pprM = pprCtxM
instance AnsiPretty Pat where pprM = pprPatM
instance AnsiPretty a => AnsiPretty (Vec a) where pprM = pprVecM
instance AnsiPretty Var   where pprM = pprVarM
instance AnsiPretty ExVar where pprM = pprExVarM
instance AnsiPretty UnVar where pprM = fmtUnVar . pprUnVarM
instance AnsiPretty Binop where pprM = pprBinopM
instance AnsiPretty Polarity where pprM = pprPolarityM
instance AnsiPretty Text  where pprM = pure . pretty

(<->) :: OutM -> OutM -> OutM
a <-> b = vsep [a, b]

(<@>) :: OutM -> OutM -> OutM
a <@> b = vcat [a, b]

id :: a -> a
id x = x

fmtSort = annotate (color Blue)

fmtUnVar :: OutM -> OutM
fmtUnVar = annotate (color Yellow)

fmtExVar = annotate (color Magenta)
fmtPatWild = annotate (color Red <> bold)

fmtKw = annotate (color Green <> bold)
fmtRec = fmtKw
fmtMatch = fmtKw

fmtSynSym = fmtKw
fmtAltPipe = fmtSynSym
fmtOrPatPipe = fmtSynSym
fmtLam = fmtSynSym
fmtLamArrow = fmtSynSym
fmtCaseArrow = fmtSynSym

fmtQuantifier = fmtKw

pprPolarityM :: Polarity -> OutM
pprPolarityM = \case
  Positive -> "+"
  Negative -> "-"
  Nonpolar -> "0"

pprBinopM :: Binop -> OutM
pprBinopM = \case
  OpArrow -> "->"
  OpSum   -> "+"
  OpProd  -> "×"

pprUnVarM :: UnVar -> OutM
pprUnVarM (UnSym s) = pprM s

pprExVarM :: ExVar -> OutM
pprExVarM (ExSym s) = pprM s <> "^"

pprVarM :: Var -> OutM
pprVarM (Sym s) = pprM s

pprPrinM :: Prin -> OutM
pprPrinM = \case
  Bang  -> "!"
  Slash -> "?"

pprTyWithPrinM :: (Ty, Prin) -> OutM
pprTyWithPrinM (ty, p) = parens (pprM p) <+> "" <> pprM ty

tyAbsPrec = 1
tySumPrec = 2
tyProdPrec = 4

tyBinopPrec = \case
  OpSum   -> tySumPrec
  OpProd  -> tyProdPrec
  OpArrow -> tyAbsPrec

patBinopPrec = tyBinopPrec
exprBinopPrec = tyBinopPrec

pprTyM :: Ty -> OutM
pprTyM = \case
  TyUnit         -> "Unit"
  TyUnVar un     -> pprM un
  TyExVar ex     -> pprM ex
  TyBinop l op r -> prec ^^ (pprM l <+> pprM op <+> prec %% pprM r)
    where prec = tyBinopPrec op
  TyForall s sort ty -> group
    (   fmtQuantifier "∀"
    <+> parens (pprM s <+> ":" <+> pprM sort)
    <-> "."
    <+> pprM ty
    )
  TyVec n v -> "Vec" <+> pprM n <+> pprM v

pprTmM :: Tm -> OutM
pprTmM = \case
  TmUnit         -> "Unit"
  TmUnVar un     -> pprM un
  TmExVar ex     -> pprM ex
  TmBinop l op r -> pprM l <+> pprM op <+> pprM r
  TmNat n        -> pprM n
  -- tm             -> pprM (tshow tm)

pprNatM :: Nat -> OutM
pprNatM = \case
  Zero   -> "Z"
  Succ n -> "S" <+> parens (pprM n)

pprSortM :: Sort -> OutM
pprSortM = \case
  Star -> "Type"
  Nat  -> "Nat"

recPrec = 1
lamPrec = 1
casePrec = 1
annPrec = 0

pprExprM :: Expr -> OutM
pprExprM = \case
  EpUnit -> "Unit"
  EpLam var e ->
    fmtLam "\\"
      <>  nowrap (pprM var)
      <+> fmtLamArrow "->"
      <+> lamPrec
      ^^  (assoc lamPrec (pprM e))
  EpRec var e -> fmtRec "rec" <+> nowrap (pprM var) <+> above
    recPrec
    parens
    (assoc recPrec (pprM e))
  EpAnn e ty -> annPrec ^^ (annPrec %% pprM e <-> ":" <+> annPrec %% pprM ty)
  EpVar s            -> pprM s
  EpApp  e (Spine s) -> pprM (Spine (e : s))
  EpProd l r         -> pprM l <+> pprM OpProd <+> pprM r
  EpCase e alts ->
    casePrec
      ^^ ( fmtMatch "case" <+> nowrap (pprM e) <-> indent
           globalIndentWidth
           (casePrec %% pprM alts)
         )
  EpVec v -> pprM v
  -- e       -> parens (pprM (tshow e))

pprAltsM :: Alts -> OutM
pprAltsM (Alts bs) = align (vcat (map (\b -> fmtAltPipe "|" <+> pprM b) bs))

pprBranchM :: Branch -> OutM
pprBranchM (Branch p e) =
  pure (P.cat (P.punctuate "|" (map ppr p))) <+> "->" <+> nowrap (pprM e)

pprPatM :: Pat -> OutM
pprPatM = \case
  PatWild     -> fmtPatWild "_"
  PatUnit     -> "Unit"
  PatVar s    -> pprM s
  PatVec v    -> pprM v
  PatProd l r -> tyProdPrec ^^ (pprM l <+> "×" <+> tyProdPrec %% pprM r)
  PatInj i p ->
    tySumPrec ^^ ((if i == InjL then "L" else "R") <+> tySumPrec %% pprM p)

pprVecM :: AnsiPretty a => Vec a -> OutM
pprVecM Empty       = "Nil"
pprVecM (Cons x Empty) = pprM x
pprVecM (Cons x xs) = hsep [pprM x, "::", pprM xs]

pprCtxM :: Ctx -> OutM
pprCtxM (Ctx s) = align (sep (map pprM (toList s)))

pprPropM :: Prop -> OutM
pprPropM (Equation a b) = angles (pprM a <+> "=" <+> pprM b)

pprFactM :: Fact -> OutM
pprFactM f = brackets (go f)
 where
  go :: Fact -> OutM
  go = \case
    FcExEq ex sort tm   -> pprM ex <+> ":" <+> pprM sort <+> "=" <+> pprM tm
    FcUnSort un sort    -> pprM un <+> ":" <+> pprM sort
    FcExSort ex sort    -> pprM ex <+> ":" <+> pprM sort
    FcUnEq   un tm      -> pprM un <+> "=" <+> pprM tm
    FcUnMark   un       -> "▶" <+> pprM un
    FcExMark   ex       -> "▶" <+> pprM ex
    FcPropMark prop     -> "▶" <+> pprM prop
    FcVarTy var ty prin -> pprM var <+> ":" <+> pprM ty <+> pprM prin

pprSpineM :: Spine -> OutM
pprSpineM (Spine s) = hsep (map pprM s)

pprRuleNameM :: RuleName -> OutM
pprRuleNameM (RuleName a) = pure (pretty a)

instance AnsiPretty RuleName where pprM = pprRuleNameM

pprJudgmentDM :: JudgmentD -> OutM
pprJudgmentDM = \case
  JRuleN r   -> pprM r
  JJudgN t   -> pprM t
  JCtx   ctx -> pprM ctx
  JExpr  ep  -> pprM ep

instance AnsiPretty JudgmentD where pprM = pprJudgmentDM

treeIndentWidth = globalIndentWidth

pprTreeM :: AnsiPretty a => Tree a -> OutM
pprTreeM = \case
  Leaf a  -> pprM a
  Rose as -> vsep (map (indent treeIndentWidth . pprM) as)

instance AnsiPretty a => AnsiPretty (Tree a) where pprM = pprTreeM

pprLogItemM :: AnsiPretty a => LogItem a -> OutM
pprLogItemM (LogItem d m) = pure (pretty d) <+> pure ":" <+> group (pprM m)

instance AnsiPretty a => AnsiPretty (LogItem a) where pprM = pprLogItemM
