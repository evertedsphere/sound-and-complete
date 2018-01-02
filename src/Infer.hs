{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts #-}

module Infer where

--
--
--                                 Glossary
--                                 ========
--
-- WT: "working theory", what I think something does
--
--                                  Links
--                                  =====
--
-- 1. "Sound and Complete", "current paper", "sequel", "DK 2016"
--
--    Dunfield and Krishnaswami 2016, "Sound and Complete Bidirectional
--    Typechecking for Higher-rank Polymorphism and Indexed Types".
--    <https://www.cl.cam.ac.uk/~nk480/bidir.pdf>
--
-- 2. "Complete and Easy", "original paper", "DK 2013"
--
--    Dunfield and Krishnaswami 2013, "Complete and Easy Bidirectional
--    Typechecking for Higher-rank Polymorphism".
--    <https://arxiv.org/pdf/1601.05106.pdf>
--
--                                  Notes
--                                  =====
--
-- 1. Even () cannot synthesize its own type:
--
--    >>> typecheck (infer (TcCtx S.Empty) EpUnit)
--
--    fails. We need to add a synthesis rule for it, mimicking the one from
--    Complete and Easy.
--
--    >>> typecheck (check (TcCtx S.Empty) EpUnit TyUnit Slash)

import Overture hiding (pred, un, op, (|>), left, right, (<+>))
import Test.Hspec

import Data.Sequence (Seq, pattern (:|>))
import qualified Data.Sequence as S
import qualified Data.Map as M

import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.IO as T

import Types

import Safe
import Pretty

import Data.Generics.Uniplate.Data

import qualified Data.List as L

--------------------------------------------------------------------------------
-- The typechecking monad.
--
-- All judgments are TcM actions.
--------------------------------------------------------------------------------

newtype TcM a
  = TcM { unTcM :: ExceptT TcErr
                      (ReaderT TcConfig
                        (WriterT' TcWrite
                          (State TcState))) a }
  deriving
   ( Functor
   , Applicative
   , Monad
   , MonadError  TcErr
   , MonadReader TcConfig
   , MonadWriter TcWrite
   , MonadState  TcState
   )

data TcState  = TcState  { _tcState_freshCounter :: Int } deriving (Show)
data TcConfig = TcConfig {  _tcConfig_log_indent :: Int } deriving (Show)
type TcWrite = Seq (LogItem JudgmentItem)
type TcErr = Text

initialContext :: TcCtx
initialContext = TcCtx Empty

initialState :: TcState
initialState = TcState 1

initialConfig :: TcConfig
initialConfig = TcConfig 0

-- | Run a (pure) action in the typechecker monad.
-- Returns a result (or an error), a log, and the final
-- typechecker state.
--
-- See 'runTcM_' if you don't want the log or the state.
runTcM :: TcM a -> ((Either Text a, TcWrite), TcState)
runTcM =
  unTcM
    >>> runExceptT
    >>> flip runReaderT initialConfig
    >>> runWriterT'
    >>> flip runState initialState

-- | Run a (pure) action in the typechecker monad.
-- Returns a result or an error.
evalTcM :: TcM a -> Either Text a
evalTcM action = runTcM action ^. _1 . _1

--------------------------------------------------------------------------------
--
--                       Utilities for working in TcM
--
--------------------------------------------------------------------------------

-- | Take a function to apply to the result of a typechecker action, and a
-- typechecker action.  
-- Run the typechecker, and apply the callback to the result.

evalTcMWith :: (a -> IO ()) -> TcM a -> IO ()
evalTcMWith f action = do
  let ((result, logLines), finalState) = runTcM action
  traverse_ (\l -> renderStdout l *> putTextLn "") logLines

  case result of
    Left err -> do
      putTextLn "Error while typechecking: "
      putTextLn err
    Right res -> do
      f res

  -- Pretty.renderStdout (logToTree logLines)

  -- putTextLn "Judgment structure:\n\n"

  -- let isRuleMatch = \case
  --       JMatchedRule{} -> True
  --       _ -> False
  -- Pretty.renderStdout (logToTree (S.filter (isRuleMatch . _logItem_message) logLines))

  putTextLn ""

  putTextLn "Final typechecker state:"
  print finalState

  putTextLn "Done."

-- | Throw a typechecker error.
failWith :: OutM -> TcM a
failWith = throwError . renderText

-- | Throw an error, naming the judgment that it involves.
-- TODO use a Reader to store the current judgment
tcError :: Judgment -> Text -> TcM a
tcError j t = do
  logMsg j t
  failWith (ppr t)

evalTcM_ :: AnsiPretty a => TcM a -> IO ()
evalTcM_ = evalTcMWith renderStdout

logIndent :: Lens' TcConfig Int
logIndent = lens _tcConfig_log_indent (\s l -> s { _tcConfig_log_indent = l })

counter :: Lens' TcState Int
counter = lens _tcState_freshCounter (\t c -> t { _tcState_freshCounter = c })

--------------------------------------------------------------------------------
--
--                      Utilities for working with contexts
--
--------------------------------------------------------------------------------

-- | Filter a context for a fact that satisfies a predicate.
factWith :: (Fact -> Bool) -> TcCtx -> Maybe Fact
factWith pred (TcCtx s) = s & S.filter pred & toList & headMay

-- | Search the context for a fact that solves an existential variable, and
-- return the sort contained in the fact.
solvedUnVar :: TcCtx -> UnVar -> Bool
solvedUnVar ctx un = isJust (factWith (solvedUnVar' un) ctx)
 where
  solvedUnVar' e1 (FcUnEq e2 _) = e1 == e2
  solvedUnVar' _  _             = False

-- | Search the context for a fact that solves an existential variable, and
-- return the sort contained in the fact.
solvedExVarSort :: TcCtx -> ExVar -> Maybe Sort
solvedExVarSort ctx ex
  | Just (FcExEq _ sort _) <- factWith (solvedExVarSort' ex) ctx = Just sort
  | otherwise = Nothing
 where
  solvedExVarSort' e1 (FcExEq e2 _ _) = e1 == e2
  solvedExVarSort' _  _               = False

-- | Search the context for a fact that tells what sort an existential variable
-- has.
exVarSort :: TcCtx -> ExVar -> Maybe Sort
exVarSort ctx ex
  | Just (FcExSort _ sort) <- factWith (exVarSort' ex) ctx = Just sort
  | otherwise = Nothing
 where
  exVarSort' e1 (FcExSort e2 _) = e1 == e2
  exVarSort' _  _               = False

-- | Search the context for a fact that tells what sort a universal variable
-- has.
unVarSort :: TcCtx -> UnVar -> Maybe Sort
unVarSort ctx un
  | Just (FcUnSort _ sort) <- factWith (unVarSort' un) ctx = Just sort
  | otherwise = Nothing
 where
  unVarSort' e1 (FcUnSort e2 _) = e1 == e2
  unVarSort' _  _               = False

-- | Try to find a fact in the context that tells us what type and principality
-- a variable has, or, failing that, return Nothing.
varTyPrin :: TcCtx -> Var -> Maybe (Ty, Prin)
varTyPrin ctx ex
  | Just (FcVarTy _ ty prin) <- factWith (varTyPrin' ex) ctx = Just (ty, prin)
  | otherwise = Nothing
 where
  varTyPrin' e1 (FcVarTy e2 _ _) = e1 == e2
  varTyPrin' _  _                = False

-- | Try to find a fact in the context. If this succeeds, create a "hole" and
-- return an ordered pair of the pieces of the context to the left and the
-- piece to the right.
hole :: Fact -> TcCtx -> Maybe (TcCtx, TcCtx)
hole mem (TcCtx ctx)
  | mem `notElem` ctx = Nothing
  | (left, r) <- S.breakl (== mem) ctx, right <- S.drop 1 r = Just
    (TcCtx left, TcCtx right)

-- | Given two contexts and a fact, join them up, with the fact in the middle.
fillHole :: TcCtx -> Fact -> TcCtx -> TcCtx
fillHole (TcCtx l) f (TcCtx r) = TcCtx ((l S.|> f) <> r)

--------------------------------------------------------------------------------
--
--                    Small "utility" judgments and functions
--
--------------------------------------------------------------------------------

-- "chkI" in the paper
checkedIntroForm :: Expr -> Bool
checkedIntroForm = \case
  EpUnit   -> True
  EpLam{}  -> True
  EpProd{} -> True
  EpInj{}  -> True
  EpVec{}  -> True
  _        -> False

-- Polarity utilities

polNeg :: Ty -> Bool
polNeg t = polarity t == Negative

polPos :: Ty -> Bool
polPos t = polarity t == Positive

polNonneg :: Ty -> Bool
polNonneg = not . polPos

polNonpos :: Ty -> Bool
polNonpos = not . polNeg

negNonpos :: Ty -> Ty -> Bool
negNonpos a b = polNeg a && polNonpos b

posNonneg :: Ty -> Ty -> Bool
posNonneg a b = polPos a && polNonneg b

isUnEqOf :: UnVar -> Fact -> Bool
isUnEqOf un = \case
  FcUnEq lhs _ -> lhs == un -- TODO only check LHS?
  _            -> False

-- | Does what it says on the tin. This is used by exactly one algorithmic
-- typing rule.
notACase :: Expr -> Bool
notACase = \case
  EpCase{} -> False
  _        -> True

-- | Does a type have an existential quantifier in the head?
notExistsHead :: Ty -> Bool
notExistsHead = \case
  TyExists{} -> False
  _          -> True

-- | Does a type have a universal quantifier in the head?
notForallHead :: Ty -> Bool
notForallHead = \case
  TyForall{} -> False
  _          -> True

-- | Does a type have some quantifier in the head?
notQuantifierHead :: Ty -> Bool
notQuantifierHead ty = notExistsHead ty && notForallHead ty

-- | Check for a clash on head constructors.
-- This is essentially (?) using the injectivity of `data`.
headConClash :: Tm -> Tm -> Bool
headConClash a b = hcc a b || hcc b a
 where
  hcc (TmNat Zero)      (TmNat (Succ _))  = True
  hcc TmUnit            TmBinop{}         = True
  hcc (TmBinop _ op1 _) (TmBinop _ op2 _) = op1 /= op2
  hcc _                 _                 = False

-- | The free existential variables in a type.
freeExtls :: TcCtx -> Ty -> [ExVar]
freeExtls ctx ty = filter (isFree ctx) exs
 where
  exs = childrenBi ty
  isFree ctx ex = isNothing (solvedExVarSort ctx ex)

-- | The free universal variables in a term.
freeUnivs :: TcCtx -> Tm -> [UnVar]
freeUnivs ctx tm = filter (not . solvedUnVar ctx) uns
  where uns = childrenBi tm

-- | Does this type have no free existential variables?
noFreeExtls :: TcCtx -> Ty -> Bool
noFreeExtls ctx = null . freeExtls ctx

-- | Does this type have free existential variables?
hasFreeExtls :: TcCtx -> Ty -> Bool
hasFreeExtls c = not . noFreeExtls c

unToEx :: UnVar -> ExVar
unToEx (UnSym sym) = ExSym sym

exToUn :: ExVar -> UnVar
exToUn (ExSym sym) = UnSym sym

freshHint :: Text -> TcM Text
freshHint hint = do
  n <- counter <+= 1
  pure (hint <> tshow n)

fresh :: TcM Text
fresh = freshHint "t"

freshEx :: TcM ExVar
freshEx = ExSym <$> fresh

-- | Turn a list of depth-annotated log items into a tree.
-- (c) mattoflambda / Matt Parsons
logToTree :: Foldable t => t (LogItem a) -> Tree a
logToTree = Rose . foldr (merge . deep) []
 where
  deep :: forall a . LogItem a -> Tree a
  deep (LogItem n a) | n <= 0    = Leaf a
                     | otherwise = Rose [deep (LogItem (n - 1) a)]

  merge :: forall a . Tree a -> [Tree a] -> [Tree a]
  merge (Rose a) (Rose b:xs) = Rose (foldr merge b a) : xs
  merge a        xs          = a : xs

--------------------------------------------------------------------------------
--
--                              Logging utilities
--
--------------------------------------------------------------------------------

render :: Pretty.AnsiPretty a => a -> IO ()
render = renderStdout' align

-- | Log the inputs to a judgment.
logPre :: PreData -> TcM ()
logPre p = do
  logD (Pre p)

logMsg :: Judgment -> Text -> TcM ()
logMsg j t = do
  logD (JMsg j t)

-- | Log the outputs from a judgment.
logPost :: PostData -> TcM ()
logPost p = do
  logD (Post p)

logRule :: Rule -> TcM ()
logRule r = do
  logD (JMatchedRule r)

logD :: JudgmentItem -> TcM ()
logD j = do
  indent <- view logIndent
  let ji = LogItem indent j
  -- liftIO (render ji)
  tell [ji]

logRecur :: TcM a -> TcM a
logRecur action = do
  local (logIndent +~ 1) action

withRule :: Text -> TcM a -> TcM a
withRule r x = logD (JRuleN (RuleName r)) *> x

--------------------------------------------------------------------------------
--
--                         Well-formedness judgments
--
--------------------------------------------------------------------------------

-- | Check if a type is well-formed in a context.
typeWF :: TcCtx -> Ty -> TcM Bool
typeWF ctx ty = logRecur $ do
  logPre (PreTypeWF ctx ty)
  go
 where
  go = case ty of

    --------------------------------------------------------------------------------
    -- [Rule: UnitWF]
    --------------------------------------------------------------------------------

    TyUnit     -> pure True

    --------------------------------------------------------------------------------
    -- [Rule: VarWF] (universal case)
    --------------------------------------------------------------------------------

    TyUnVar un -> inferSort ctx (TmUnVar un) >>= \case
      Star -> pure True
      _    -> failWith "lol"

    --------------------------------------------------------------------------------
    -- [Rule: VarWF] (existential case)
    -- and
    -- [Rule: SolvedVarWF]
    --------------------------------------------------------------------------------

    TyExVar ex -> inferSort ctx (TmExVar ex) >>= \case
      Star -> pure True
      _    -> failWith "lol"

    ------------------------------------------------------------------------------
    -- [Rule: BinWF]
    --
    -- A type with a binary connective joining two types is well-formed if both
    -- components are.
    ------------------------------------------------------------------------------

    TyBinop  a     _     b -> liftA2 (&&) (typeWF ctx a) (typeWF ctx b)

    ------------------------------------------------------------------------------
    -- [Rule: ForallWF]
    --
    -- Add a fact to the context that says what sort a forall's "variable" has,
    -- and check the "body" of the forall in this new context.
    ------------------------------------------------------------------------------

    TyForall alpha kappa a -> typeWF (ctx |> FcUnSort alpha kappa) a

    ------------------------------------------------------------------------------
    -- [Rule: ExistsWF]
    --
    -- Add a fact to the context that says what sort an existential type's
    -- "variable" has, and check the "body" in this new context.
    ------------------------------------------------------------------------------

    TyExists alpha kappa a -> typeWF (ctx |> FcUnSort alpha kappa) a

    ------------------------------------------------------------------------------
    -- [Rule: ImpliesWF]
    --
    -- An implies-type is well-formed if both the proposition and the type it
    -- comprises are.
    ------------------------------------------------------------------------------

    TyImplies pr a         -> liftA2 (&&) (propWF ctx pr) (typeWF ctx a)

    ------------------------------------------------------------------------------
    -- [Rule: WithWF]
    --
    -- Ditto: a with-type is well-formed if both the proposition and the type it
    -- comprises are.
    ------------------------------------------------------------------------------

    TyWith    a  pr        -> liftA2 (&&) (propWF ctx pr) (typeWF ctx a)

    _                      -> failWith "typeWF"

-- | Check if a proposition is well-formed in a context.
propWF :: TcCtx -> Prop -> TcM Bool
propWF ctx (Equation a b) = do

  ------------------------------------------------------------------------------
  -- [Rule: EqProp]
  ------------------------------------------------------------------------------

  sa <- inferSort ctx a
  sb <- inferSort ctx b
  case sa of
    Nat -> case sb of
      Nat -> pure True
      _   -> failWith "lol"
    _ -> failWith "lol"


prinTypeWF :: TcCtx -> Ty -> Prin -> Bool
prinTypeWF ctx ty p = True -- FIXME

ctxWF :: TcCtx -> Bool
ctxWF (TcCtx ctx) = case ctx of

  ------------------------------------------------------------------------------
  -- [Rule: NilCtx]
  ------------------------------------------------------------------------------

  Empty          -> True

  ------------------------------------------------------------------------------
  -- [Rule: MarkerCtx]
  ------------------------------------------------------------------------------

  s:|>m@FcMark{} -> m `notElem` s

  _              -> False

--------------------------------------------------------------------------------
--
--                               Sort-checking
--
--------------------------------------------------------------------------------

-- | Given a context, find the sort of a monotype.
--
-- For the TmNat branch, we know the sort "by type" since
-- our embedding of TmZero and TmSucc as TmNat Nat gives
-- us this for free. :)
inferSort :: TcCtx -> Tm -> TcM Sort
inferSort ctx = \case

  ------------------------------------------------------------------------------
  -- [Rule: ZeroSort] and [Rule: SuccSort]
  ------------------------------------------------------------------------------

  TmNat _       -> pure Nat

  ------------------------------------------------------------------------------
  -- [Rule: UnitSort]
  --
  -- Unit is a *-sorted type.
  ------------------------------------------------------------------------------

  TmUnit        -> pure Star

  ------------------------------------------------------------------------------
  -- [Rule: BinSort]
  ------------------------------------------------------------------------------

  TmBinop l _ r -> do
    lsort <- inferSort ctx l
    rsort <- inferSort ctx r
    case (lsort, rsort) of
      (Star, Star) -> pure Star
      _            -> failWith "lol"

  ------------------------------------------------------------------------------
  -- [Rule: VarSort] (universal variable case)
  ------------------------------------------------------------------------------

  TmUnVar un -> case unVarSort ctx un of
    Just s -> pure s
    _      -> failWith "boom"

  TmExVar ex -> case exVarSort ctx ex of

  -- Now we're trying to find what sort an existential variable has. There are
  -- two kinds of fact our context can contain that tell us this:

  ------------------------------------------------------------------------------
  -- [Rule: VarSort] (existential variable case)
  --
  -- This is an FcExSort judgment.
  ------------------------------------------------------------------------------
    Just sort -> pure sort

  ------------------------------------------------------------------------------
  -- [Rule: SolvedVarSort]
  --
  -- The other is an FcExEq judgment.
  --
  -- This is the case where the existential variable has actually been "solved"
  -- to some other type, so we can get the sort from there.
  ------------------------------------------------------------------------------

    _         -> case solvedExVarSort ctx ex of
      Just sort -> pure sort
      _         -> failWith "unknown exvar"

  _ -> failWith "This shouldn't happen"

checkSort :: TcCtx -> Tm -> Sort -> TcM ()
checkSort ctx tm s = do
  s' <- inferSort ctx tm
  unless (s == s') (failWith "checkSort")

-- | Substitute a context into a type.
subst :: TcCtx -> Ty -> Ty
subst ctx = transformOn terms subTm where subTm = substTm ctx

-- | Substitute a context into a term or monotype.
substTm :: TcCtx -> Tm -> Tm
substTm = error "substTm"

-- | Assume a hypothesis is true in a given context, and return either an
-- updated context or (in case the context becomes inconsistent) @Bottom@.
assumeHypo :: TcCtx -> Prop -> PICtx
assumeHypo = error "assumeHypo"

checkProp :: TcCtx -> Prop -> TcCtx
checkProp = error "checkProp"

-- | Check that two monotypes are equal, possibly modifying the
-- context.
checkEq :: TcCtx -> Tm -> Tm -> TcCtx
checkEq = error "checkEq"

--------------------------------------------------------------------------------
--
--                               Unification
--
--------------------------------------------------------------------------------

-- | Unify two terms or monotypes, with sort taken from the context, taking
-- context ctx = \Gamma to either a modified context \Delta or inconsistency.
unifyInfer :: TcCtx -> Tm -> Tm -> TcM (PICtx, Sort)
unifyInfer ctx a b = do
  sort <- inferSort ctx a
  checkSort ctx b sort
  ctx' <- unify ctx a b sort
  pure (ctx', sort)

-- | Unify two terms or monotypes, taking context ctx = \Gamma to either a
-- modified context \Delta or inconsistency.
unify :: TcCtx -> Tm -> Tm -> Sort -> TcM PICtx
unify ctx a b sort = logRecur $ do
  logPre (PreElimeq ctx a b sort)
  o <- go
  -- logPost (PostElimeq o)
  pure o
 where
  go = case a of

    -- [Rule: ElimeqUVarRefl]

    TmUnVar{} | a == b -> do
      logRule (RuleElimeq RElimeqUVarRefl)
      pure (ConCtx ctx)

    -- [Rule: ElimeqUnit]

    TmUnit | TmUnit <- b -> do
      logRule (RuleElimeq RElimeqUnit)
      pure (ConCtx ctx)

    -- [Rule: ElimeqZero]

    TmNat Zero | TmNat Zero <- b -> do
      logRule (RuleElimeq RElimeqZero)
      pure (ConCtx ctx)

    -- [Rule: ElimeqSucc]

    TmNat (Succ sigma) | TmNat (Succ tau) <- b, Nat <- sort -> do
      logRule (RuleElimeq RElimeqSucc)
      res <- unify ctx (TmNat sigma) (TmNat tau) sort
      case res of
        ConCtx _ -> pure res
        _        -> failWith "lol"

    -- [Rule: ElimeqUVarL]

    TmUnVar alpha -> do
      logRule (RuleElimeq RElimeqUvarL)
      unless (alpha `notElem` freeUnivs ctx b) (tcError JElimeq "not free")
      unless (none (isUnEqOf alpha) (toList (let TcCtx s = ctx in s)))
             (tcError JElimeq "isUnEqOf")
      pure (ConCtx (ctx |> FcUnEq alpha b))

    -- [Rule: ElimeqClash]

    _ | headConClash a b -> do
      logRule (RuleElimeq RElimeqClash)
      pure Bottom

    _ -> do
      logRule (RuleFail JElimeq)
      failWith "unify"

-- | Check two propositions for equivalence.
propEquiv :: TcCtx -> Prop -> Prop -> TcM TcCtx
propEquiv _ _ _ = failWith "propEquiv"

-- | Check two types for equivalence.
typeEquiv :: TcCtx -> Ty -> Ty -> TcM TcCtx
typeEquiv ctx a b = do
  go a b
 where
  go TyUnit TyUnit = pure ctx
  go (TyUnVar x) (TyUnVar y)
    | x == y = pure ctx
    | otherwise = failWith
      ("Cannot unify type variables" <+> ppr x <+> "and" <+> ppr y)
  go _ _ = failWith "typeEquiv: boom"

--------------------------------------------------------------------------------
--
--                            Subtype-checking
--
--------------------------------------------------------------------------------

-- | Given a context and a polarity p, check if a type is a p-subtype of
-- another.
checkSubtype :: TcCtx -> Polarity -> Ty -> Ty -> TcM TcCtx
checkSubtype ctx pol a b = logRecur $ do
  logPre (PreSubtype ctx pol a b)
  go
 where
  go = case pol of

    _ | notQuantifierHead a, notQuantifierHead b ->
      logRule (RuleSubtype REquiv) *> typeEquiv ctx a b

    Positive
      | negNonpos a b
      -> logRule (RuleSubtype RMinusPlusL) *> checkSubtype ctx Negative a b
      | negNonpos b a
      -> logRule (RuleSubtype RMinusPlusR) *> checkSubtype ctx Negative b a
      | otherwise
      -> tcError JSubtype "MinusPlus: negNonpos failed"

    Negative
      | posNonneg a b
      -> logRule (RuleSubtype RPlusMinusL) *> checkSubtype ctx Positive a b
      | posNonneg b a
      -> logRule (RuleSubtype RPlusMinusR) *> checkSubtype ctx Positive b a
      | otherwise
      -> tcError JSubtype "PlusMinus: posNonneg failed"

-- | Instantiate an existential variable.
instExVar :: TcCtx -> ExVar -> Tm -> Sort -> TcM TcCtx
instExVar = error "instExVar"

-- | Find the "polarity" of a type. Polarities are mainly (only?) used for the
-- subtyping judgment.
polarity :: Ty -> Polarity
polarity = \case
  TyExVar{} -> Positive
  TyUnVar{} -> Negative
  _         -> Nonpolar

-- | Turn A into [a^/a]A -- or, as I like to think of
-- it, A[a -> a^], read "A with a going to a^".
--
-- Reading a^ out loud is left as an exercise for the intrepid reader.
existentializeTy
  :: UnVar -- A
  -> Ty    -- a^
  -> Ty    -- [a^/a] A
existentializeTy u1@UnSym{} ty = case ty of
  TyUnVar u2 | u1 == u2 -> TyExVar (unToEx u1)
  TyBinop  l  op r      -> TyBinop (extlTy l) op (extlTy r)
  TyForall un s  a      -> TyForall un s (extlTy a)
  TyExists un s  a      -> TyExists un s (extlTy a)
  TyImplies prop a      -> TyImplies prop (extlTy a)
  TyWith    a    prop   -> TyWith (extlTy a) prop
  _                     -> ty
  where extlTy = existentializeTy u1

--------------------------------------------------------------------------------
-- 
--                        Typechecking and inference
--
--------------------------------------------------------------------------------

-- | The type-checking wrapper function. 
check :: TcCtx -> Expr -> Ty -> Prin -> TcM TcCtx
check ctx ep ty pr = logRecur $ do
  logPre (PreCheck ctx ep ty pr)
  ctx' <- check' ctx ep ty pr
  logPost (PostCheck ctx')
  pure ctx'

-- | The function that actually does all the type-checking.
check'
  :: TcCtx     -- ^ context representing knowledge before attempting the typecheck
  -> Expr    -- ^ expression to be checked
  -> Ty      -- ^ type to be checked against
  -> Prin    -- ^ are we claiming the type is principal?
  -> TcM TcCtx -- ^ an updated context, representing what we know after said attempt

------------------------------------------------------------------------------
-- [Rule: UnitIntro]
--
-- Introduction form for checking () against the type ().
------------------------------------------------------------------------------

check' ctx EpUnit TyUnit       _ = withRule "UnitIntro" (pure ctx)

------------------------------------------------------------------------------
-- [Rule: UnitIntro-Extl]
--
-- Introduction form for checking () against an unknown type.
------------------------------------------------------------------------------

check' ctx EpUnit (TyExVar ex) _ = do
  let Just (l, r) = hole (FcExSort ex Star) ctx
  logRule (RuleCheck RUnitIntro_Extl)
  pure (fillHole l (FcExEq ex Star TmUnit) r)

------------------------------------------------------------------------------
-- [Rule: WithIntro]
--
-- A With form is only valid if the proposition `prop` attached to the type
-- `a` is true in the current context.
------------------------------------------------------------------------------

check' ctx ep (TyWith a prop) prin = withRule "WithIntro" $ do
  unless (notACase ep) (failWith "case")
  -- 1. Check if the proposition is true in the current context `ctx`.
  let theta = checkProp ctx prop
  -- This gives us an updated context `theta` with possibly-new information.
  -- We then
  --   2. update the type by substituting this context in, and
  let ty'   = subst theta a
  --   3. check the expression against this updated type.
  check theta ep ty' prin

------------------------------------------------------------------------------
-- [Rule: ForallIntro]
--
-- α : κ => alpha : k
-- ν     => nu
-- A     => a
------------------------------------------------------------------------------

check' ctx nu (TyForall alpha k a) prin = do
  logRule (RuleCheck RForallIntro)
  unless (checkedIntroForm nu) (failWith "not chkI")
  let alpha'k = FcUnSort alpha k
  ctx' <- check (ctx |> alpha'k) nu a prin
  let Just (delta, theta) = hole alpha'k ctx'
  pure delta

-----------------------------------------------------------------------------
-- ImpliesIntro* rules
--
-- These match "implies" types. We are given a proposition (which is roughly
-- an equality between two monotypes, similar to Haskell's a ~ b) and a type.
--
-- To check an expression against a type of this form, we
--
--   1. incorporate the proposition into what we already know, the context
--      `ctx`
--   2. see whether it remains consistent or not:
--   3. if it does, we get an updated context `theta` in which to evaluate
--      the type-check, so we incorporate this new knowledge into the type
--      and recheck accordingly
--   4. if not, check whether the expression we're checking is a "checked
--      intro form". if it isn't, bail (TODO: why?)
-----------------------------------------------------------------------------

check' ctx nu (TyImplies prop a) Bang =
  let markP = FcPropMark prop
      ctx'  = assumeHypo (ctx |> markP) prop
  in  case ctx' of                                  -- 2.

-----------------------------------------------------------------------------
-- [Rule: ImpliesIntro]
--
-- Our assumption of the hypothesis left our context consistent (i.e. it
-- broke nothing), so we continue with the extra knowledge it gave us.
-----------------------------------------------------------------------------

        ConCtx theta -> withRule "ImpliesIntro" $ do -- 3.
          outputCtx <- check theta nu (subst theta a) Bang
          case hole markP outputCtx of
            Just (delta, delta') -> do
              pure delta
            Nothing -> failWith "lol"

-----------------------------------------------------------------------------
-- [Rule: ImpliesIntroBottom]
--
-- The hypothesis implied an inconsistency in the context!
-- This is checked, among other things, by seeing if we have a
-- head-constructor clash (using @headConClash@, the implementation of the
-- #-judgment from the paper), which is why I guess we need
-- @checkedIntroForm@ here.
-----------------------------------------------------------------------------

        Bottom | checkedIntroForm nu -> withRule "ImpliesIntroBottom" $ do -- 4.
          pure ctx
        _ -> do
          failWith "check: ImpliesIntro*: fail" -- 1.

------------------------------------------------------------------------------
-- [Rule: Rec]
--
-- TODO reduce duplication, combine with ArrowIntro
------------------------------------------------------------------------------

check' ctx (EpRec x nu) ty prin = do
  logRule (RuleCheck RRec)
  let xap = FcVarTy x ty prin
  check (ctx |> xap) nu ty prin <&> hole xap >>= \case
    Just (delta, theta) -> pure delta
    _                   -> failWith "lol"

-----------------------------------------------------------------------------
-- [Rule: ArrowIntro]
--
-- xap => x : A p
-----------------------------------------------------------------------------

check' ctx (EpLam x e) (TyArrow a b) p = do
  logRule (RuleCheck RArrowIntro)
  let xap = FcVarTy x a p
  check (ctx |> xap) e b p <&> hole xap >>= \case
    Just (delta, theta) -> pure delta
    _                   -> failWith "lol"

-----------------------------------------------------------------------------
-- [Rule: ArrowIntro-Extl]
--
-- WT: using Slash because unspecified principality.
-----------------------------------------------------------------------------

check' ctx (EpLam x e) (TyExVar ex@a) Slash = do
  logRule (RuleCheck RArrowIntro_Extl)
  let Just Star          = exVarSort ctx ex
  let Just (left, right) = hole (FcExSort ex Star) ctx
  a1 <- freshEx
  a2 <- freshEx
  let xa1   = FcVarTy x (TyExVar a1) Slash
      aeq   = FcExEq a Star (TmArrow (TmExVar a1) (TmExVar a2))
      a1s   = FcExSort a1 Star
      a2s   = FcExSort a2 Star
      ctx'  = left <> TcCtx [a1s, a2s, aeq] <> right
      ctx'' = ctx' |> xa1
  out <- check ctx'' e (TyExVar a2) Slash
  case hole xa1 out of
    Just (delta, _) -> pure delta
    _               -> failWith "lol"

-----------------------------------------------------------------------------
-- [Rule: SumIntroₖ]
--
-- Introduction form for checking a sum expression against a sum type.
--
-- We match on the head constructor of the type, deferring the "which
-- side am I injecting into" check to a case statement.
-----------------------------------------------------------------------------

check' ctx (EpInj inj e) (TySum a1 a2) prin = do
  logRule (RuleCheck (RSumIntro inj))
  check ctx e a prin
 where
  a = case inj of
    InjL -> a1
    InjR -> a2

------------------------------------------------------------------------------
-- [Rule: SumIntro-Extlₖ]
--
-- Introduction form for checking a sum expression against an unknown type.
------------------------------------------------------------------------------

check' ctx (EpInj inj e) (TyExVar a) Slash = do
  logRule (RuleCheck (RSumIntro_Extl inj))
  let Just Star          = exVarSort ctx a
      Just (left, right) = hole (FcExSort a Star) ctx
  a1 <- freshEx
  a2 <- freshEx
  let ak   = if inj == InjL then a1 else a2
      aeq  = FcExEq a Star (TmExVar a1 `TmProd` TmExVar a2)
      a1s  = FcExSort a1 Star
      a2s  = FcExSort a2 Star
      ctx' = left <> TcCtx [a1s, a2s, aeq] <> right
  delta <- check ctx' e (TyExVar ak) Slash
  pure delta

  -- TODO
  -- should we add, e.g. an EpInj case here that catches everything falling
  -- through? or is there a legitimate reason for sum expressions to fall
  -- to other cases? (subtyping is the last rule, remember)

------------------------------------------------------------------------------
-- [Rule: ProdIntro]
--
-- Introduction form for known product types.
------------------------------------------------------------------------------

check' ctx (EpProd e1 e2) (TyProd a1 a2) prin = do
  logRule (RuleCheck RProdIntro)
  theta <- check ctx e1 a1 prin
  check theta e2 (subst theta a2) prin

------------------------------------------------------------------------------
-- [Rule: ProdIntro-Extl]
--
-- Introduction form for unsolved-for product types.
------------------------------------------------------------------------------

check' ctx (EpProd e1 e2) (TyExVar a) Slash = do
  logRule (RuleCheck RProdIntro_Extl)
  let Just Star          = exVarSort ctx a
      Just (left, right) = hole (FcExSort a Star) ctx
  a1 <- freshEx
  a2 <- freshEx
  let aeq  = FcExEq a Star (TmExVar a1 `TmProd` TmExVar a2)
      a1s  = FcExSort a1 Star
      a2s  = FcExSort a2 Star
      ctx' = left <> TcCtx [a1s, a2s, aeq] <> right
  theta <- check ctx' e1 (TyExVar a1) Slash
  delta <- check theta e2 (subst theta (TyExVar a2)) Slash
  pure delta

------------------------------------------------------------------------------
-- [Rule: Case]
--
-- Case expressions, which are pattern vectors with bodies of some given type.
------------------------------------------------------------------------------

check' gamma (EpCase e alts) _C p = do
  logRule (RuleCheck RCase)
  (_A, Bang, theta) <- infer gamma e
  delta             <- matchBranches theta alts [subst theta _A] _C p
  True              <- coverageCheck delta alts [subst delta _A]
  -- FIXME continue from here
  pure delta

------------------------------------------------------------------------------
-- [Rule: Sub]
--
-- Subtype checking.
--
-- This does not take the principality @prin@ supplied to @check@ into account
-- since p is left free in [Rule: Sub] in the paper.
--
-- I've moved this rule to the end since it doesn't really match on either
-- the expression or the type, so other things should "fall through" to this.
------------------------------------------------------------------------------

check' ctx e b _ = do
  logRule (RuleCheck RSub)
  let polB = polarity b
  (a, q, theta) <- infer ctx e
  checkSubtype theta polB a b

-- | Given a context and an expression, infer its type, a principality for it,
-- and an updated context.
infer :: TcCtx -> Expr -> TcM (Ty, Prin, TcCtx)
infer ctx ep = logRecur $ do
  logPre (PreInfer ctx ep)
  r@(ty, prin, ctx') <- infer' ctx ep
  logPost (PostInfer ty prin ctx')
  pure r

infer' :: TcCtx -> Expr -> TcM (Ty, Prin, TcCtx)
infer' ctx ep = case ep of

  ------------------------------------------------------------------------------
  -- [Rule: Var]
  --
  -- Variable expressions (e.g. the "x" in \x -> body).
  --
  -- These can have their types inferred if the context contains an FcVarTy fact
  -- that tells us its type (principality included).
  ------------------------------------------------------------------------------

  EpVar var | Just (ty, prin) <- varTyPrin ctx var -> do
    logRule (RuleInfer RVar)
    pure (subst ctx ty, prin, ctx)

  ------------------------------------------------------------------------------
  -- [Rule: Anno]
  --
  -- Type-annotated expressions.
  --
  -- The type is inferred by checking the type of the expression against the
  -- annotation.
  ------------------------------------------------------------------------------

  EpAnn e a | prinTypeWF ctx a Bang -> do
    logRule (RuleInfer RAnno)
    delta <- check ctx e (subst ctx a) Bang
    pure (subst delta a, Bang, delta)

  ------------------------------------------------------------------------------
  -- [Rule: ArrowE]
  --
  -- Infer the type of a spine application, recovering principality where
  -- possible.
  ------------------------------------------------------------------------------

  EpApp e spine | Spine [_] <- spine -> do
    logRule (RuleInfer RArrowE)
    (a, p, theta) <- infer ctx e
    (c, q, delta) <- inferSpineRecover theta spine a p
    pure (c, q, delta)


  _ -> failWith ("infer: don't know how to infer type of " <> ppr ep)

-- | Infer the type of a spine application. This form does not attempt to
-- recover principality in the synthesized type.
--
-- I read the output (C, q, Δ) as "q-type C with output context Δ".
--
-- For example,
-- (Bang, TyUnit, TcCtx Nil) = "the principal type () with empty output context"

inferSpine
  :: TcCtx        -- ^ input context
  -> Spine      -- ^ spine being applied upon (ugh)
  -> Ty         -- ^ type of expression applied to the spine
  -> Prin       -- ^ principality of aforesaid expression
  -> TcM (Ty   --   inferred type of application
            , Prin --   inferred principality of application
                  , TcCtx)  --   output context      -- ^ judgment
inferSpine ctx sp ty p = logRecur $ do
  logPre (PreSpine ctx sp ty p)
  r@(rty, rp, rctx) <- inferSpine' ctx sp ty p
  logPost (PostSpine rty rp rctx)
  pure r

inferSpine' :: TcCtx -> Spine -> Ty -> Prin -> TcM (Ty, Prin, TcCtx)

------------------------------------------------------------------------------
-- [Rule: ForallSpine]
--
-- The principality is omitted in the "top" rule (the antecedent?), so per
-- the "sometimes omitted" note in [Figure: Syntax of declarative types and
-- constructs], I'm assuming that means it's nonprincipal.
------------------------------------------------------------------------------

inferSpine' ctx sp (TyForall alpha k a) p = do
  logRule (RuleSpine RForallSpine)
  let Spine (e:s) = sp
      alpha'      = unToEx alpha
  (c, q, delta) <- inferSpine (ctx |> FcExSort alpha' k)
                              sp
                              (existentializeTy alpha a)
                              Slash
  pure (c, q, delta)

------------------------------------------------------------------------------
-- [Rule: ImpliesSpine]
--
-- In context Γ, applying e to a spine of type P ⊃ A synthesizes (C, q, Δ)
-- if Γ tells us that the proposition P holds. (WT)
--
-- Questions:
-- Are we matching on sp to check that the spine is nonempty?
------------------------------------------------------------------------------

inferSpine' ctx sp (TyImplies prop a) p = do
  logRule (RuleSpine RImpliesSpine)
  let Spine (e:s) = sp
      theta       = checkProp ctx prop
  (c, q, delta) <- inferSpine theta sp (subst theta a) p
  pure (c, q, delta)

  ------------------------------------------------------------------------------
  -- [Rule: EmptySpine]
  --
  -- Applying an expression to an empty spine is trivial.
  -- Return everything unchanged.
  ------------------------------------------------------------------------------

inferSpine' ctx (Spine []) ty p = do
  logRule (RuleSpine REmptySpine)
  pure (ty, p, ctx)

  ------------------------------------------------------------------------------
  -- [Rule: ArrowSpine]
  --
  -- I think this is the main function type-inferring judgment.
  ------------------------------------------------------------------------------

inferSpine' ctx sp (TyArrow a b) p = do
  logRule (RuleSpine RArrowSpine)
  let Spine (e:s') = sp
      s            = Spine s'
  -- match the "function" against the input type a
  theta         <- check ctx e a p
  -- match the "argument" against the output type b
  (c, q, delta) <- inferSpine theta s (subst theta b) p
  pure (c, q, delta)

  ------------------------------------------------------------------------------
  -- [Rule: Spine-Extl]
  --
  -- FIXME: Should we be returning the original principality, or just Slash
  -- since it was left unspecified?
  ------------------------------------------------------------------------------

inferSpine' ctx sp (TyExVar ex@a') p = do
  let Spine (e:s') = sp
  Just Star          <- pure (exVarSort ctx ex)
  Just (left, right) <- pure (hole (FcExSort ex Star) ctx)
  a'1                <- freshEx
  a'2                <- freshEx

  let arrowMType = TmExVar a'1 `TmArrow` TmExVar a'2
      arrowType  = TyExVar a'1 `TyArrow` TyExVar a'2
      a'1s       = exStar a'1
      a'2s       = exStar a'2
      a'eq       = FcExEq a' Star arrowMType
      ctx'       = solveHole left right [a'1s, a'2s, a'eq]

  delta <- check ctx' e (TyExVar a'1) Slash
  pure (arrowType, p, delta)

inferSpine' _ _ _ _ = do
  logRule (RuleFail JSpine)
  failWith "inferSpine: the likely-impossible happened"

exStar :: ExVar -> Fact
exStar ex = FcExSort ex Star

solveHole :: TcCtx -> TcCtx -> Seq Fact -> TcCtx
solveHole l r fs = l <> TcCtx fs <> r

inferSpineRecover :: TcCtx -> Spine -> Ty -> Prin -> TcM (Ty, Prin, TcCtx)
inferSpineRecover ctx sp ty p = logRecur $ do
  logPre (PreSpineRecover ctx sp ty p)
  r@(rt, rp, rc) <- inferSpineRecover' ctx sp ty p
  logPost (PostSpineRecover rt rp rc)
  pure r

-- | Infer the type of a spine application. Additionally, this form
-- attempts to recover principality in the output type.
inferSpineRecover' :: TcCtx -> Spine -> Ty -> Prin -> TcM (Ty, Prin, TcCtx)
inferSpineRecover' ctx s a p = do

  ------------------------------------------------------------------------------
  -- [Rule: SpineRecover]
  --
  -- Upgrade a suitable nonprincipal type with no free existential
  -- tyvars into a principal type.
  ------------------------------------------------------------------------------
  res1 <- inferSpine ctx s a Bang
  case res1 of
    (c, Slash, delta) -> do
      let fevCond = noFreeExtls delta c
      if fevCond
        then do
          logMsg JSpineRecover
                 "No free existential variables. Recovering principality."
          logRule (RuleSpineRecover RSpineRecover)

          pure (c, Bang, delta)
        else do
        ------------------------------------------------------------------------------
        -- [Rule: SpinePass]
        --
        -- WT: guessing "pass" is for "pass the principality inferred by
        -- inferSpine through"
        ------------------------------------------------------------------------------
          logMsg JSpineRecover
                 "Free existential variables, passing principality through."
          logRule (RuleSpineRecover RSpinePass)

          res2 <- inferSpine ctx s a p
          case res2 of
            res@(c, q, delta) | p == Slash || q == Bang || hasFreeExtls delta c -> pure
              res
            _ -> failWith "is this even possible?"

-- | Check case-expressions.
-- Wrapper for @matchBranches'@.
matchBranches :: TcCtx -> Alts -> [Ty] -> Ty -> Prin -> TcM TcCtx
matchBranches ctx alts ts ty p = logRecur $ do
  logPre (PreMatch ctx alts ts ty p)
  ctx' <- matchBranches' ctx alts ts ty p
  logPost (PostMatch ctx')
  pure ctx'

-- | Check case-expressions.
-- Given an input context, a case-expression, a type-vector, and a 
-- type/prin pair, attempt to match the case-expr/typevec against the
-- type with the given principality, returning an updated output context.

matchBranches' :: TcCtx -> Alts -> [Ty] -> Ty -> Prin -> TcM TcCtx
------------------------------------------------------------------------------
-- [Rule: MatchEmpty]
------------------------------------------------------------------------------
matchBranches' gamma (Alts []) _ _ _ = do
  logRule (RuleMatch RMatchEmpty)
  pure gamma

------------------------------------------------------------------------------
-- [Rule: MatchBase]
--
-- A case-expression with one branch which in turn has no patterns, given
-- an empty type-vector, matches against a type/prin pair if the RHS of the
-- only branch checks against it.
------------------------------------------------------------------------------
matchBranches' gamma (Alts [Branch [] e]) [] _C p = do
  logRule (RuleMatch RMatchBase)
  delta <- check gamma e _C p
  pure delta

------------------------------------------------------------------------------
-- [Rule: MatchUnit]
--
-- FIXME[paper]: The paper doesn't seem to allow () in patterns.
------------------------------------------------------------------------------
matchBranches' gamma (Alts [Branch (PatUnit:ps) e]) (TyUnit:ts) ty p = do
  logRule (RuleMatch RMatchUnit)
  delta <- matchBranches gamma (Alts [Branch ps e]) ts ty p
  pure delta

matchBranches' gamma (Alts [Branch (PatProd p1 p2:ps) e]) (TyProd _A1 _A2:_As) ty p
  = do
    logRule (RuleMatch RMatchProd)
    delta <- matchBranches gamma
                           (Alts [Branch (p1 : p2 : ps) e])
                           (_A1 : _A2 : _As)
                           ty
                           p
    pure delta

------------------------------------------------------------------------------
-- [Rule: MatchInj_k]
--
-- Match an "Either" pattern.
------------------------------------------------------------------------------
matchBranches' gamma (Alts [Branch (PatInj k rho:ps) e]) (TySum _A1 _A2:_As) ty p
  = do
    logRule (RuleMatch (RMatchInj k))
    let _Ak = if k == InjL then _A1 else _A2
    delta <- matchBranches gamma (Alts [Branch (rho : ps) e]) (_Ak : _As) ty p
    pure delta

matchBranches' gamma (Alts [Branch (PatWild:ps) e]) (_A:_As) _C p = do
  logRule (RuleMatch RMatchWild)
  unless (notQuantifierHead _A) (tcError JMatch "quantifier-headed type")
  delta <- matchBranches gamma (Alts [Branch ps e]) _As _C p
  pure delta

matchBranches' gamma (Alts [Branch (PatVec Nil:ps) e]) (TyVec t _A:_As) _C p =
  do
    logRule (RuleMatch RMatchNil)
    delta <- matchBranchesAssuming gamma
                                   (Equation t (TmNat Zero))
                                   (Alts [Branch ps e])
                                   _As
                                   _C
                                   p
    pure delta

matchBranches' gamma (Alts [Branch (PatVar z:ps) e]) (_A:_As) _C p = do
  logRule (RuleMatch RMatchNeg)
  let zab    = FcVarTy z _A Bang
      in_ctx = gamma |> zab
  out_ctx <- matchBranches in_ctx (Alts [Branch ps e]) _As _C p
  let Just (g, g') = hole zab out_ctx
  pure g

------------------------------------------------------------------------------
-- [Rule: MatchSeq]
------------------------------------------------------------------------------
matchBranches' gamma (Alts (pi:_Pi)) _A _C p = do
  logRule (RuleMatch RMatchSeq)
  -- liftIO (Pretty.renderStdout pi)
  theta <- matchBranches gamma (Alts [pi]) _A _C p
  delta <- matchBranches theta (Alts _Pi) _A _C p
  pure delta

-- matchBranches' _ _ _ _ _ = do
--   logRule (RuleFail JMatch)
--   failWith "matchBranch'"

matchBranchesAssuming
  :: TcCtx -> Prop -> Alts -> [Ty] -> Ty -> Prin -> TcM TcCtx
matchBranchesAssuming gamma prop@(Equation lt rt) alts@(Alts bs) ts ty p =
  logRecur $ do
  -- logPre (PreMatchAssuming gamma prop alts ts ty p)
    go
 where
  go
    | length bs /= 1 = failWith "too many branches"
    | otherwise = do
      (ctx', sort) <- unifyInfer gamma lt rt
      case ctx' of
        Bottom   -> pure gamma
        ConCtx{} -> do
          ConCtx theta <- unify (gamma |> FcPropMark prop) lt rt sort
          ctx''        <- matchBranches theta alts ts ty p
          let Just (delta, delta') = hole (FcPropMark prop) ctx''
          pure delta

--------------------------------------------------------------------------------
--
--
--                           Coverage checking
--                           =================
--
--
-- The paper has two coverage-checking judgments:
--
-- 1. Γ   ⊢ Π covers [A..]
-- 2. Γ/P ⊢ Π covers [A..]
--
-- which are implemented and explained in @coverageCheck@ and
-- @coverageCheckAssuming@ respectively. 
--
--------------------------------------------------------------------------------

-- | This implements the first of the two coverage-checking judgments, written
--
--   Γ   ⊢ Π covers [A..]
--
-- in the paper. This means that, in context Γ, the patterns Π cover the
-- types in [A..].

coverageCheck :: TcCtx -> Alts -> [Ty] -> TcM Bool
coverageCheck ctx alts tys = logRecur $ do
  coverageCheck' ctx alts tys

coverageCheck' :: TcCtx -> Alts -> [Ty] -> TcM Bool

------------------------------------------------------------------------------
-- [Rule: CoversNil]
------------------------------------------------------------------------------

coverageCheck' ctx (Alts (Branch [] _e1:_Pi)) [] = pure True

------------------------------------------------------------------------------
-- [Rule: CoversVar]
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- [Rule: CoversUnit]
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- [Rule: CoversProd]
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- [Rule: CoversSum]
------------------------------------------------------------------------------

------------------------------------------------------------------------------
-- [Rule: CoversExists]
------------------------------------------------------------------------------

coverageCheck' _   _                          _  = pure True -- failWith "coverage"

prepareUnitAlts :: Alts -> TcM Alts
prepareUnitAlts (Alts bs) = Alts <$> go bs
 where
  go :: [Branch] -> TcM [Branch]
  go = \case
    []                  -> pure []
    Branch (r:rs) e:_Pi -> do
      unless (ok r) (failWith "prepareUnitAlts")
      _Pi' <- go _Pi
      pure (Branch rs e : _Pi')
   where
    ok = \case
      PatVar{} -> False
      PatWild  -> False
      PatUnit  -> False
      _        -> True

-- | This implements the second of the two coverage-checking judgments, which
-- takes a proposition into account.
--
--   Γ/P ⊢ Π covers [A..]
--
-- This means that, in context Γ, the patterns Π cover the types in [A..]
-- assuming the proposition P.

coverageCheckAssuming :: TcCtx -> Prop -> Alts -> [Ty] -> TcM Bool
coverageCheckAssuming ctx prop alts tys = failWith "coverageCheckAssuming"
