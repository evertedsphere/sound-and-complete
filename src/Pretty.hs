{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE ScopedTypeVariables          #-}
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
renderStdout = renderStdout' id

renderStdout' :: AnsiPretty a => (OutM -> OutM) -> a -> IO ()
renderStdout' f = TL.putStrLn . renderText' f

renderText'' :: AnsiPretty a => Bool -> (OutM -> OutM) -> a -> TL.Text
renderText'' c f =
   TL.replace "\\e" "\ESC"
    . renderLazy
    . P.layoutPretty layoutOpts
    . runPprM
    . (if c then id else map P.unAnnotate)
    . f
    . ppr
  where layoutOpts = P.LayoutOptions (P.AvailablePerLine 110 1.0)

renderText' :: AnsiPretty a => (OutM -> OutM) -> a -> TL.Text
renderText' = renderText'' True

renderText :: AnsiPretty a => a -> TL.Text
renderText = renderText' id

renderString :: AnsiPretty a => a -> [Char]
renderString = TL.unpack . renderText

renderPlainString :: AnsiPretty a => a -> [Char]
renderPlainString = TL.unpack . renderText'' False id

liftOutM :: (Foldable t) => ([a] -> b) -> t (PprM a) -> PprM b
liftOutM f = map f . sequence . toList

listed :: OutFold
listed = liftOutM P.list

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

unAnnotate :: OutEndo
unAnnotate = map P.unAnnotate

parens, angles, braces, brackets :: OutEndo
parens = map P.parens
angles = map P.angles
brackets = map P.brackets
braces = map P.braces

align :: OutEndo
align = map P.align

fill :: Int -> OutEndo
fill = map . P.fill

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

punctuate :: Out -> [Out] -> [OutM]
punctuate o = map pure . P.punctuate o

-- punctuate :: OutM -> PprM [Out] -> PprM [Out]
-- punctuate p os = P.punctuate <$> p <*> os

infixr 5 <+>
(<+>) :: OutM -> OutM -> OutM
(<+>) = liftA2 (P.<+>)

globalIndentWidth :: Int
globalIndentWidth = 4

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

pprPure :: AnsiPretty a => a -> Out
pprPure = runPprM . ppr

class AnsiPretty a where
  ppr :: a -> OutM

wrapOn :: Bool -> (PprM a -> PprM a) -> PprM a -> PprM a
wrapOn c f = if c then f else id
{-# INLINE wrapOn #-}

above :: Int -> (PprM a -> PprM a) -> PprM a -> PprM a
above p f m = do
  outerPrec <- view precedence
  wrapOn (outerPrec > p) f (assoc (p + 1) m)

infixr 8 ^^
prec ^^ body = above prec parens body

nowrap :: PprM a -> PprM a
nowrap = assoc (-1)

instance (a ~ Out) => IsString (PprM a) where fromString = pure . fromString

instance AnsiPretty OutM where ppr = id
instance AnsiPretty Expr where ppr = pprExpr
instance AnsiPretty Alts where ppr = pprAlts
instance AnsiPretty Tm where ppr = pprTm
instance AnsiPretty Ty where ppr = pprTy
instance AnsiPretty [Ty] where ppr = vcat . map ppr
instance AnsiPretty (Ty,Prin) where ppr = pprTyWithPrin
instance AnsiPretty Nat where ppr = pprNat
instance AnsiPretty Branch where ppr = pprBranch
instance AnsiPretty Prin where ppr = pprPrin
instance AnsiPretty Prop where ppr = pprProp
instance AnsiPretty Sort where ppr = pprSort
instance AnsiPretty Fact where ppr = pprFact
instance AnsiPretty Spine where ppr = pprSpine
instance AnsiPretty TcCtx where ppr = pprCtx
instance AnsiPretty Pat where ppr = pprPat
instance AnsiPretty a => AnsiPretty (Vec a) where ppr = pprVec
instance AnsiPretty Var   where ppr = pprVar
instance AnsiPretty ExVar where ppr = pprExVar
instance AnsiPretty UnVar where ppr = fmtUnVar . pprUnVar
instance AnsiPretty Binop where ppr = pprBinop
instance AnsiPretty Polarity where ppr = pprPolarity

instance AnsiPretty a => AnsiPretty (Tree a) where ppr = pprTree
instance AnsiPretty a => AnsiPretty (LogItem a) where ppr = pprLogItem

instance AnsiPretty RuleName where ppr = pprRuleName
instance AnsiPretty JudgmentItem where ppr = pprJudgmentItem
instance AnsiPretty Judgment where ppr = pprJudgment
instance AnsiPretty PreData where ppr = pprPreData
instance AnsiPretty PostData where ppr = pprPostData
instance AnsiPretty Rule where ppr = pprRule

instance AnsiPretty Text  where ppr = pure . pretty

(<->) :: OutM -> OutM -> OutM
a <-> b = vsep [a, b]

(<@>) :: OutM -> OutM -> OutM
a <@> b = vcat [a, b]

fmtSort = annotate (color Blue)

fmtUnVar :: OutM -> OutM
fmtUnVar = annotate (color Yellow)

fmtExVar = annotate (color Red <> bold)
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

pprPolarity :: Polarity -> OutM
pprPolarity = \case
  Positive -> "+"
  Negative -> "-"
  Nonpolar -> "0"

pprBinop :: Binop -> OutM
pprBinop = \case
  OpArrow -> "->"
  OpSum   -> "+"
  OpProd  -> "×"

pprUnVar :: UnVar -> OutM
pprUnVar (UnSym s) = ppr s

pprExVar :: ExVar -> OutM
pprExVar (ExSym s) = fmtExVar (ppr s <> "^")

pprVar :: Var -> OutM
pprVar (Sym s) = ppr s

pprPrin :: Prin -> OutM
pprPrin = \case
  Bang  -> "!"
  Slash -> "?"

pprTyWithPrin :: (Ty, Prin) -> OutM
pprTyWithPrin (ty, p) = parens (ppr p) <+> "" <> ppr ty

tyAbsPrec = 1
tySumPrec = 2
tyProdPrec = 4

tyBinopPrec = \case
  OpSum   -> tySumPrec
  OpProd  -> tyProdPrec
  OpArrow -> tyAbsPrec

patBinopPrec = tyBinopPrec
exprBinopPrec = tyBinopPrec

pprTy :: Ty -> OutM
pprTy = align . go
 where
  go = \case
    TyUnit         -> "Unit"
    TyUnVar un     -> ppr un
    TyExVar ex     -> ppr ex
    TyBinop l op r -> prec ^^ (go l <+> ppr op <+> prec %% go r)
      where prec = tyBinopPrec op
    TyForall s sort ty -> group
      (   fmtQuantifier "∀"
      <+> parens (ppr s <+> ":" <+> ppr sort)
      <-> "."
      <+> go ty
      )
    TyVec n v ->
      dataConPrec ^^ ("Vec" <+> dataConPrec %% ppr n <+> dataConPrec %% ppr v)

dataConPrec = 8

pprTm :: Tm -> OutM
pprTm = \case
  TmUnit         -> "Unit"
  TmUnVar un     -> ppr un
  TmExVar ex     -> ppr ex
  TmBinop l op r -> ppr l <+> ppr op <+> ppr r
  TmNat n        -> ppr n
  -- tm             -> ppr (tshow tm)

pprNat :: Nat -> OutM
pprNat = \case
  Zero   -> "Z"
  Succ n -> "S" <+> parens (ppr n)

pprSort :: Sort -> OutM
pprSort = \case
  Star -> "Type"
  Nat  -> "Nat"

recPrec = 1
lamPrec = 1
casePrec = 1
annPrec = 0
appPrec = 10

-- todo fix these: infixl both
sumPrec = 6
prodPrec = 7

-- infixr
consPrec = 5

fmtFunction = annotate (color Blue)

pprExpr :: Expr -> OutM
pprExpr = align . go
 where
  go = \case
    EpUnit -> "Unit"
    EpLam var e ->
      lamPrec ^^ (fmtLam "\\" <> nowrap (ppr var) <+> fmtLamArrow "->" <+> go e)
    EpRec var e ->
      fmtRec "rec" <+> nowrap (ppr var) <+> recPrec ^^ recPrec %% go e
    EpAnn e ty ->
      annPrec ^^ group (annPrec %% go e <-> ":" <+> annPrec %% ppr ty)
    EpVar s   -> ppr s
    EpApp e s -> appPrec ^^ (appPrec %% go e <+> appPrec %% ppr s)
    -- EpInj s r -> sumPrec ^^ (sumPrec %% ppr r)
    EpProd l r ->
      prodPrec ^^ (prodPrec %% go l <+> ppr OpProd <+> prodPrec %% go r)
    EpCase e alts ->
      casePrec
        ^^ ( fmtMatch "case" <+> nowrap (go e) <-> nest globalIndentWidth
                                                        (casePrec %% ppr alts)
           )
    EpVec v -> ppr v
      -- e       -> parens (ppr (tshow e))

pprAlts :: Alts -> OutM
pprAlts (Alts bs) = align (vcat (map (\b -> fmtAltPipe "|" <+> ppr b) bs))

pprBranch :: Branch -> OutM
pprBranch (Branch p e) =
  cat (punctuate "|" (map pprPure p)) <+> "->" <+> nowrap (ppr e)

pprPat :: Pat -> OutM
pprPat = \case
  PatWild  -> fmtPatWild "_"
  PatUnit  -> "Unit"
  PatVar s -> ppr s
  PatVec v -> ppr v
  PatProd l r ->
    tyProdPrec ^^ (tyProdPrec %% ppr l <+> "×" <+> (tyProdPrec + 1) %% ppr r)
  -- PatInj i p ->
  --   tySumPrec ^^ ((if i == InjL then "L" else "R") <+> tySumPrec %% ppr p)

pprVec :: AnsiPretty a => Vec a -> OutM
pprVec (Vec xs) = go xs
 where
  go []  = "[]"
  go [x] = consPrec ^^ ppr x
  go (x:xs) =
    consPrec ^^ hsep [(consPrec + 1) %% ppr x, fmtKw "::", consPrec %% go xs]

pprCtx :: TcCtx -> OutM
pprCtx (TcCtx s) = case s of
  Empty -> "<empty>"
  _     -> align (fsep (map ppr (toList s)))

pprProp :: Prop -> OutM
pprProp (Equation a b) = angles (ppr a <+> "=" <+> ppr b)

pprFact :: Fact -> OutM
pprFact f = brackets (go f)
 where
  go :: Fact -> OutM
  go = \case
    FcExEq ex sort tm   -> ppr ex <+> ":" <+> ppr sort <+> "=" <+> ppr tm
    FcUnSort un sort    -> ppr un <+> ":" <+> ppr sort
    FcExSort ex sort    -> ppr ex <+> ":" <+> ppr sort
    FcUnEq   un tm      -> ppr un <+> "=" <+> ppr tm
    FcUnMark   un       -> "▶" <+> ppr un
    FcExMark   ex       -> "▶" <+> ppr ex
    FcPropMark prop     -> "▶" <+> ppr prop
    FcVarTy var ty prin -> ppr var <+> ":" <+> ppr ty <+> ppr prin

pprSpine :: Spine -> OutM
pprSpine (Spine s) = hsep (map ppr s)

pprRuleName :: RuleName -> OutM
pprRuleName (RuleName a) = pure (pretty a)

pprJudgmentItem :: JudgmentItem -> OutM
pprJudgmentItem = \case
  JRuleN       r   -> ppr r
  JJudgN       t   -> ppr t
  JCtx         ctx -> ppr ctx
  JExpr        ep  -> ppr ep
  Pre          p   -> ppr p
  Post         p   -> ppr p
  JMatchedRule r   -> ppr r
  JMsg r msg       -> vcat
    [lhs "judgment" <+> fmtJ (ppr r), lhs "info" <+> fmtB (ppr msg)]
   where
    lhs  = fill 10
    fmtB = annotate (color Cyan <> bold)
    fmtJ = annotate (color Green <> bold)

pprPostData :: PostData -> OutM
pprPostData = \case
  PostCheck ctx -> vcat [lhs "post" <+> fmtJ "Check", lhs "ctx" <+> ppr ctx]
  PostInfer ty pr ctx -> vcat
    [ lhs "post" <+> fmtJ "Infer"
    , lhs "ty" <+> ppr ty
    , lhs "prin" <+> ppr pr
    , lhs "ctx" <+> ppr ctx
    ]
  PostSpine ty pr ctx -> ppr_tpc "Spine" ty pr ctx
  PostSpineRecover ty pr ctx -> ppr_tpc "SpineRecover" ty pr ctx
  PostMatch ctx -> vcat [lhs "post" <+> fmtJ "Match", lhs "ctx" <+> ppr ctx]
  PostSubtype ctx ->
    vcat [lhs "post" <+> fmtJ "Subtype", lhs "ctx" <+> ppr ctx]
 where
  ppr_tpc rule ty pr ctx = vcat
    [ lhs "post" <+> fmtJ "Spine"
    , lhs "ty" <+> ppr ty
    , lhs "prin" <+> ppr pr
    , lhs "ctx" <+> ppr ctx
    ]
  fmtJ = annotate (color Green <> bold)
  lhs  = fill 10

pprPreData :: PreData -> OutM
pprPreData = \case
  PreTypeWF ctx ty ->
    vcat
      [ lhs "pre" <+> fmtJ "TypeWF"
      , lhs "type" <+> ppr ty
      , lhs "ctx" <+> ppr ctx
      ]
  PreInfer ctx ep -> vcat
    [lhs "pre" <+> fmtJ "Infer", lhs "expr" <+> ppr ep, lhs "ctx" <+> ppr ctx]
  PreCheck ctx sp ty prin -> vcat
    [ lhs "pre" <+> fmtJ "Check"
    , lhs "spine" <+> ppr sp
    , lhs "type" <+> ppr ty
    , lhs "ctx" <+> ppr ctx
    ]
  PreSpine        ctx ep ty prin -> ppr_cetp "Spine" ctx ep ty prin
  PreSpineRecover ctx ep ty prin -> ppr_cetp "SpineRecover" ctx ep ty prin
  PreMatch ctx b ts t p          -> vcat
    [ lhs "pre" <+> fmtJ "Match"
    , lhs "alts" <+> ppr b
    , lhs "type" <+> ppr t
    , lhs "types" <+> hsep (map ppr ts)
    , lhs "prin" <+> ppr p
    , lhs "ctx" <+> ppr ctx
    ]
  PreElimeq c t t' s -> vcat
    [ lhs "pre" <+> fmtJ "Elimeq"
    , lhs "lhs" <+> ppr t
    , lhs "rhs" <+> ppr t'
    , lhs "sort" <+> ppr s
    , lhs "ctx" <+> ppr c
    ]
  PreSubtype c pol tl tr -> vcat
    [ lhs "pre" <+> fmtJ "Subtype"
    , lhs "ctx" <+> ppr c
    , lhs "pol" <+> ppr pol
    , lhs "left-ty" <+> ppr tl
    , lhs "right-ty" <+> ppr tr
    ]
 where
  ppr_cetp rule ctx ep ty prin = vcat
    [ lhs "pre" <+> fmtJ rule
    , lhs "expr" <+> ppr ep
    , lhs "type" <+> ppr ty
    , lhs "prin" <+> ppr prin
    , lhs "ctx" <+> ppr ctx
    ]
  fmtJ = annotate (color Green <> bold)
  lhs  = fill 10

pprRule = \case
  RuleCheck         r -> rule "Check" r
  RuleMatch         r -> rule "Match" r
  RuleInfer         r -> rule "Infer" r
  RuleSpine         r -> rule "Spine" r
  RuleSpineRecover  r -> rule "SpineRecover" r
  RuleMatchAssuming r -> rule "MatchAssuming" r
  RuleElimeq        r -> rule "Elimeq" r
  RuleSubtype       r -> rule "Subtype" r
  RuleFail          j -> vcat
    [ lhs "judgment" <+> fmtJ (pure (P.pretty (TL.drop 1 (tshow j))))
    , lhs "rule" <+> fmtRed "FAIL: no rules matched"
    ]
 where
  rule j r = vcat
    [ lhs "judgment" <+> fmtJ j
    , lhs "rule" <+> fmtR (pure (P.pretty (TL.drop 1 (tshow r))))
    ]
  fmtJ   = annotate (color Green <> bold)
  fmtR   = annotate (color Blue <> bold)
  fmtRed = annotate (color Red <> bold)
  lhs    = fill 10

treeIndentWidth = globalIndentWidth

pprTree :: AnsiPretty a => Tree a -> OutM
pprTree = \case
  Leaf a  -> ppr a
  Rose as -> vsep (map (indent treeIndentWidth . align . (<-> "") . ppr) as)

pprLogItem :: AnsiPretty a => LogItem a -> OutM
pprLogItem (LogItem d m) = if (d > 30)
  then unimplemented
  else fill 3 (pure (pretty d)) <+> ":" <+> align (ppr m)

pprJudgment :: Judgment -> OutM
pprJudgment = pure . P.pretty . TL.drop 1 . tshow
