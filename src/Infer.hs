{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE GADTs #-}
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

--------------------------------------------------------------------------------
-- [Glossary]
--
-- WT: "working theory", what I think something does
--
--------------------------------------------------------------------------------
-- [Links]
--
-- 1. "Sound and Complete", "current paper", "sequel", "DK 2016"
--
--    Dunfield and Krishnaswami 2016, "Sound and Complete Bidirectional
--    Typechecking for Higher-rank Polymorphism and Indexed Types".
--    Link: <https://www.cl.cam.ac.uk/~nk480/bidir.pdf>
--
-- 2. "Complete and Easy", "original paper", "DK 2013"
--
--    Dunfield and Krishnaswami 2013, "Complete and Easy Bidirectional
--    Typechecking for Higher-rank Polymorphism".
--    <https://arxiv.org/pdf/1601.05106.pdf>
--
--------------------------------------------------------------------------------
-- [Notes]
--
-- 1. Even () cannot synthesize its own type:
--
--    >>> typecheck (infer (Ctx S.Empty) EpUnit)
--
--    fails. We need to add a synthesis rule for it, mimicking the one from
--    Complete and Easy.
--
--    >>> typecheck (check (Ctx S.Empty) EpUnit TyUnit Slash)

import Overture hiding (pred, un, op, (|>), left, right)
import Test.Hspec

import Data.Sequence (Seq, pattern (:|>))
import qualified Data.Sequence as S
import qualified Data.Map as M

import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.IO as T

import Types

import Safe
import qualified Pretty

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Util (putDocW)
import Data.Generics.Uniplate.Data

import qualified Data.List as L

-- (c) mattoflambda / Matt Parsons
logToTree :: Foldable t => t (LogItem a) -> Tree a 
logToTree = Rose . foldr (merge . deep) []
  where 
    deep :: forall a. LogItem a -> Tree a
    deep (LogItem n a) 
      | n <= 0 = Leaf a 
      | otherwise = Rose [deep (LogItem (n-1) a)] 

    merge :: forall a. Tree a -> [Tree a] -> [Tree a]
    merge (Rose a) (Rose b : xs) = Rose (foldr merge b a) : xs 
    merge a xs = a : xs

--------------------------------------------------------------------------------
  -- Constructing the typechecking monad 'TcM'
--------------------------------------------------------------------------------

{-# ANN TcState ("HLint: ignore Use camelCase" :: String) #-}
-- | Typechecker state
data TcState  = TcState
  { _tcState_freshCounter :: Int
  }
   deriving (Show, Eq)

initialContext :: Ctx
initialContext = Ctx Empty

initialState :: TcState
initialState = TcState 1

-- | Typechecker configuration
data TcConfig = TcConfig
  { _tcConfig_log_indent :: Int
  }
  deriving (Show, Eq)

initialConfig :: TcConfig
initialConfig = TcConfig 0

logIndent :: Lens' TcConfig Int
logIndent = lens _tcConfig_log_indent (\s l -> s { _tcConfig_log_indent = l })

type TcWrite = Seq (LogItem JudgmentItem)

newtype TcM a
  = TcM { runTcM :: ExceptT Text
                      (ReaderT TcConfig
                        (WriterT' TcWrite
                          (StateT TcState IO))) a }
  deriving
   ( Functor
   , Applicative
   , Monad
   , MonadError  Text
   , MonadReader TcConfig
   , MonadWriter TcWrite
   , MonadState  TcState
   , MonadIO
   )

counter :: Lens' TcState Int
counter = lens _tcState_freshCounter (\t c -> t { _tcState_freshCounter = c })

typecheck :: Show a => TcM a -> IO ()
typecheck = typecheck' print

ppInfer :: Ctx -> Expr -> IO ()
ppInfer ctx ep = typecheck' pp $ infer ctx ep
 where
   pp (t, p, c) = pure ()

ppCheck :: TcM a -> IO ()
ppCheck = typecheck' pp
 where
   pp c = pure ()

typecheck' :: (a -> IO ()) -> TcM a -> IO ()
typecheck' f action = do
  ((result, logLines), finalState) <-
    action
    & runTcM
    & runExceptT
    & flip runReaderT initialConfig
    & runWriterT'
    & flip runStateT initialState
  case result of
    Left err -> do
      putTextLn "Error while typechecking: "
      putTextLn err
    Right res -> do
      f res

  -- traverse_ (\l -> Pretty.renderStdout l *> putTextLn "") logLines
  Pretty.renderStdout (logToTree logLines)

  -- putTextLn "Judgment structure:\n\n"

  -- let isRuleMatch = \case
  --       JMatchedRule{} -> True
  --       _ -> False
  -- Pretty.renderStdout (logToTree (S.filter (isRuleMatch . _logItem_message) logLines))

  putTextLn ""

  putTextLn "Final typechecker state:"
  print finalState

  putTextLn "Done."

-- | Filter a context for a fact that satisfies a predicate.
factWith :: (Fact -> Bool) -> Ctx -> Maybe Fact
factWith pred (Ctx s) = s & S.filter pred & toList & headMay

-- | Search the context for a fact that solves an existential variable, and
-- return the sort contained in the fact.
solvedUnVar :: Ctx -> UnVar -> Bool
solvedUnVar ctx un = isJust (factWith (solvedUnVar' un) ctx)
 where
  solvedUnVar' e1 (FcUnEq e2 _) = e1 == e2
  solvedUnVar' _  _             = False


-- | Search the context for a fact that solves an existential variable, and
-- return the sort contained in the fact.
solvedExVarSort :: Ctx -> ExVar -> Maybe Sort
solvedExVarSort ctx ex
  | Just (FcExEq _ sort _) <- factWith (solvedExVarSort' ex) ctx = Just sort
  | otherwise = Nothing
 where
  solvedExVarSort' e1 (FcExEq e2 _ _) = e1 == e2
  solvedExVarSort' _  _               = False

-- | Search the context for a fact that tells what sort an existential variable
-- has.
exVarSort :: Ctx -> ExVar -> Maybe Sort
exVarSort ctx ex
  | Just (FcExSort _ sort) <- factWith (exVarSort' ex) ctx = Just sort
  | otherwise = Nothing
 where
  exVarSort' e1 (FcExSort e2 _) = e1 == e2
  exVarSort' _  _               = False

-- | Search the context for a fact that tells what sort a universal variable
-- has.
unVarSort :: Ctx -> UnVar -> Maybe Sort
unVarSort ctx un
  | Just (FcUnSort _ sort) <- factWith (unVarSort' un) ctx = Just sort
  | otherwise = Nothing
 where
  unVarSort' e1 (FcUnSort e2 _) = e1 == e2
  unVarSort' _  _               = False

checkSort :: Ctx -> Tm -> Sort -> TcM ()
checkSort ctx tm s = do
  s' <- inferSort ctx tm
  unless (s == s') (throwError "checkSort")

-- | Given a context, find the sort of a monotype.
--
-- Note [TmNat sort-checking]
-- -----------------------------------------------------------------------------
-- For the TmNat branch, we know the sort "by type" since
-- my embedding of TmZero and TmSucc as TmNat Nat gives
-- us this for free. :)

inferSort :: Ctx -> Tm -> TcM Sort
inferSort ctx = \case

  ------------------------------------------------------------------------------
  -- [Rule: ZeroSort] and [Rule: SuccSort]
  ------------------------------------------------------------------------------

  TmNat _ -> pure Nat

  ------------------------------------------------------------------------------
  -- [Rule: UnitSort]
  --
  -- Unit is a *-sorted type.
  ------------------------------------------------------------------------------

  TmUnit -> pure Star

  ------------------------------------------------------------------------------
  -- [Rule: BinSort]
  ------------------------------------------------------------------------------

  TmBinop l _ r
    -> do lsort <- inferSort ctx l
          rsort <- inferSort ctx r
          case (lsort, rsort) of
            (Star, Star) -> pure Star
            _ -> throwError "lol"

  ------------------------------------------------------------------------------
  -- [Rule: VarSort] (universal variable case)
  ------------------------------------------------------------------------------

  TmUnVar un ->
    case unVarSort ctx un of
      Just s -> pure s
      _ -> throwError "boom"

  TmExVar ex ->

  -- Now we're trying to find what sort an existential variable has. There are
  -- two kinds of fact our context can contain that tell us this:

  ------------------------------------------------------------------------------
  -- [Rule: VarSort] (existential variable case)
  --
  -- This is an FcExSort judgment.
  ------------------------------------------------------------------------------

    case exVarSort ctx ex of
      Just sort -> pure sort

  ------------------------------------------------------------------------------
  -- [Rule: SolvedVarSort]
  --
  -- The other is an FcExEq judgment.
  --
  -- This is the case where the existential variable has actually been "solved"
  -- to some other type, so we can get the sort from there.
  ------------------------------------------------------------------------------

      _ -> case solvedExVarSort ctx ex of
             Just sort -> pure sort
             _ -> throwError "unknown exvar"

  _ -> throwError "This shouldn't happen"

-- | Check if a proposition is well-formed in a context.
propWF :: Ctx -> Prop -> TcM Bool
propWF ctx (Equation a b) = do

  ------------------------------------------------------------------------------
  -- [Rule: EqProp]
  ------------------------------------------------------------------------------

  sa <- inferSort ctx a
  sb <- inferSort ctx b
  case sa of
    Nat -> case sb of
      Nat -> pure True
      _ -> throwError "lol"
    _ -> throwError "lol"

typeWF :: Ctx -> Ty -> TcM Bool
typeWF ctx ty = do
  logPre (PreTypeWF ctx ty)
  typeWF' ctx ty

typeWF' :: Ctx -> Ty -> TcM Bool
typeWF' ctx ty

  -- [Rule: VarWF] (universal case)

  | TyUnVar un <- ty
  = do
      sun <- inferSort ctx (TmUnVar un)
      case sun of
        Star -> pure True
        _ -> throwError "lol"

  -- [Rule: VarWF] (existential case)
  -- and
  -- [Rule: SolvedVarWF]

  | TyExVar ex <- ty
  = inferSort ctx (TmExVar ex) >>= \case
        Star -> pure True
        _ -> throwError "lol"

  -- [Rule: UnitWF]

  | TyUnit <- ty
  = pure True

  ------------------------------------------------------------------------------
  -- [Rule: BinWF]
  --
  -- A type with a binary connective joining two types is well-formed if both
  -- components are.
  ------------------------------------------------------------------------------

  | TyBinop a _ b <- ty
  = do
      awf <- typeWF ctx a
      bwf <- typeWF ctx b
      pure (awf && bwf)

  ------------------------------------------------------------------------------
  -- [Rule: ForallWF]
  --
  -- Add a fact to the context that says what sort a forall's "variable" has,
  -- and check the "body" of the forall in this new context.
  ------------------------------------------------------------------------------

  | TyForall alpha kappa a <- ty
  = typeWF (ctx |> FcUnSort alpha kappa) a

  ------------------------------------------------------------------------------
  -- [Rule: ExistsWF]
  --
  -- Add a fact to the context that says what sort an existential type's
  -- "variable" has, and check the "body" in this new context.
  ------------------------------------------------------------------------------

  | TyExists alpha kappa a <- ty
  = typeWF (ctx |> FcUnSort alpha kappa) a

  ------------------------------------------------------------------------------
  -- [Rule: ImpliesWF]
  --
  -- An implies-type is well-formed if both the proposition and the type it
  -- comprises are.
  ------------------------------------------------------------------------------

  | TyImplies pr a <- ty
  = liftA2 (&&) (propWF ctx pr) (typeWF ctx a)

  ------------------------------------------------------------------------------
  -- [Rule: WithWF]
  --
  -- Ditto: a with-type is well-formed if both the proposition and the type it
  -- comprises are.
  ------------------------------------------------------------------------------

  | TyWith a pr <- ty
  = liftA2 (&&) (propWF ctx pr) (typeWF ctx a)

  | otherwise
  = throwError "typeWF"

prinTypeWF :: Ctx -> Ty -> Prin -> Bool
prinTypeWF ctx ty p = True -- FIXME

ctxWF :: Ctx -> Bool
ctxWF (Ctx s)

  ------------------------------------------------------------------------------
  -- [Rule: NilCtx]
  ------------------------------------------------------------------------------

  | Empty <- s
  = True

  ------------------------------------------------------------------------------
  -- [Rule: MarkerCtx]
  ------------------------------------------------------------------------------

  | s' :|> m@FcMark {} <- s
  , m `notElem` s'
  = True

  | otherwise
  = False

checkedIntroForm :: Expr -> Bool
checkedIntroForm = \case
  EpUnit   -> True
  EpLam{}  -> True
  EpProd{} -> True
  EpInj{}  -> True
  EpVec{}  -> True
  _        -> False

-- | The notation from the paper, for the sake of completeness.
-- Prefer 'checkedIntroForm'.
chkI :: Expr -> Bool
chkI = checkedIntroForm

-- | Substitute a context into a type.
substituteCtx :: Ctx -> Ty -> Ty
substituteCtx ctx = transformOn terms subTm
-- \case
--   TyUnVar un -> unimplemented
--   TyExVar ex -> unimplemented
--   TyUnit -> TyUnit
--   TyBinop l op r -> TyBinop (sub l) op (sub r)
--   TyWith typ (Equation a b)
--     -> TyWith (sub typ) (Equation (subTm a) (subTm b))
--   TyImplies (Equation a b) typ
--     -> TyImplies (Equation (subTm a) (subTm b)) (sub typ)
--   TyForall un sort typ -> TyForall un sort (sub typ)
--   TyExists un sort typ -> TyExists un sort (sub typ)
  -- _ -> unimplemented
  -- TODO implement hole substitution

  where
    -- sub :: Ty -> Ty
    -- sub   = substituteCtx   ctx

    subTm :: Tm -> Tm
    subTm = substituteCtxTm ctx

-- | Substitute a context into a term or monotype.
substituteCtxTm :: Ctx -> Tm -> Tm
substituteCtxTm = error "substituteCtxTm"

-- | Assume a hypothesis is true in a given context, and return either an
-- updated context or (in case the context becomes inconsistent) @Bottom@.
assumeHypo :: Ctx -> Prop -> PICtx
assumeHypo = error "assumeHypo"

checkProp :: Ctx -> Prop -> Ctx
checkProp = error "checkProp"

-- | Check that two monotypes are equal, possibly modifying the
-- context.
checkEq :: Ctx -> Tm -> Tm -> Ctx
checkEq = error "checkEq"

-- | Unify two terms or monotypes, with sort taken from the context, taking
-- context ctx = \Gamma to either a modified context \Delta or inconsistency.

unifyInfer :: Ctx -> Tm -> Tm -> TcM (PICtx, Sort)
unifyInfer ctx a b = do
  sort <- inferSort ctx a
  checkSort ctx b sort
  ctx' <- unify ctx a b sort
  pure (ctx', sort)

-- | Unify two terms or monotypes, taking context ctx = \Gamma to either a
-- modified context \Delta or inconsistency.
unify :: Ctx -> Tm -> Tm -> Sort -> TcM PICtx
unify ctx a b sort = logRecur $ do
  logPre (PreElimeq ctx a b sort)
  o <- go 
  -- logPost (PostElimeq o)
  pure o
    
  where 
  go
    -- [Rule: ElimeqUVarRefl]
    | TmUnVar{} <- a
    , a == b = do 
      logRule (RuleElimeq RElimeqUVarRefl)
      pure (ConCtx ctx)

    -- [Rule: ElimeqUnit]

    | TmUnit <- a
    , TmUnit <- b = do
      logRule (RuleElimeq RElimeqUnit)
      pure (ConCtx ctx)

    -- [Rule: ElimeqZero]

    | TmNat Zero <- a
    , TmNat Zero <- b = do
      logRule (RuleElimeq RElimeqZero)
      pure (ConCtx ctx)

    -- [Rule: ElimeqSucc]

    | TmNat (Succ sigma) <- a
    , TmNat (Succ tau)   <- b
    , Nat <- sort = do
      logRule (RuleElimeq RElimeqSucc)
      res <- unify ctx (TmNat sigma) (TmNat tau) sort
      case res of
        ConCtx _ -> pure res
        _ -> throwError "lol"

    -- [Rule: ElimeqUVarL]
    
    | TmUnVar alpha <- a = do
      logRule (RuleElimeq RElimeqUvarL)
      unless (alpha `notElem` freeUnivs ctx b) (logMsg JElimeq "not free" *> throwError "die")
      unless (none (isUnEqOf alpha) (toList (let Ctx s = ctx in s))) (throwError "")
      pure (ConCtx (ctx |> FcUnEq alpha b))

    -- [Rule: ElimeqClash]

    | headConClash a b = do
      logRule (RuleElimeq RElimeqClash)
      pure Bottom

    | otherwise = do
      logRule (RuleFail JElimeq)
      throwError "unify"

isUnEqOf :: UnVar -> Fact -> Bool
isUnEqOf un = \case
  FcUnEq lhs _ -> lhs == un -- TODO only check LHS?
  _ -> False

-- | Check for a clash on head constructors.
-- This is essentially (?) using the injectivity of `data`.
headConClash :: Tm -> Tm -> Bool
headConClash a b
  | TmNat  Zero    <- a
  , TmNat (Succ _) <- b
  = True

  | TmNat (Succ _) <- a
  , TmNat  Zero    <- b
  = True

  | TmBinop{} <- a
  , TmUnit <- b
  = True

  | TmUnit <- a
  , TmBinop{} <- b
  = True

  | TmBinop _ op1 _ <- a
  , TmBinop _ op2 _ <- b
  = op1 /= op2

  | otherwise
  = False

-- | Check two propositions for equivalence.
propEquiv :: Ctx -> Prop -> Prop -> TcM Ctx
propEquiv _ _ _ = throwError "propEquiv"

-- | Check two types for equivalence.
typeEquiv :: Ctx -> Ty -> Ty -> TcM Ctx
typeEquiv ctx TyUnit TyUnit = pure ctx
typeEquiv _ _ _ = throwError "boom"

polNeg :: Ty -> Bool
polNeg t = polarity t == Negative

polPos :: Ty -> Bool
polPos t = polarity t == Positive

polNonneg :: Ty -> Bool
polNonneg = not . polPos

polNonpos :: Ty -> Bool
polNonpos = not . polNeg

negNonpos :: Ty -> Ty -> Bool
negNonpos a b = nnp a b || nnp b a
  where nnp p q = polNeg p && polNonpos q

posNonneg :: Ty -> Ty -> Bool
posNonneg a b = pnn a b || pnn b a
  where pnn p q = polPos p && polNonneg q

--------------------------------------------------------------------------------
-- [Subtype-checking]
--------------------------------------------------------------------------------

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

rethrowAfter :: MonadError e m => m a -> m b -> m a
rethrowAfter action post = action `catchError` \e -> post *> throwError e

finally action cleanup = do
  r <- action `rethrowAfter` cleanup
  cleanup
  pure r

-- | Logging wrapper for the real subtyping function.
checkSubtype :: Ctx -> Polarity -> Ty -> Ty -> TcM Ctx
checkSubtype c p t t' = do
  logD (JRuleN (RuleName "!!!"))
  checkSubtype' c p t t'

-- | Given a context and a polarity p, check if a type is a p-subtype of
-- another.
checkSubtype' :: Ctx -> Polarity -> Ty -> Ty -> TcM Ctx
checkSubtype' ctx p a b  = case p of

  --------------------------------------------------------------------------
  -- [Rules: Subtype-MinusPlus-L and Subtype-MinusPlus-R]
  --------------------------------------------------------------------------
  Positive -> withRule "Subtype-MinusPlus-*" $ do
    -- TODO Add Subtype-Exists-(L|R)
    unless (negNonpos a b) (throwError "subtyping fail: not negNonpos")
    checkSubtype ctx Negative a b

  --------------------------------------------------------------------------
  -- [Rules: Subtype-MinusPlus-L and Subtype-MinusPlus-R]
  --------------------------------------------------------------------------
  Negative -> withRule "Subtype-MinusPlus-*" $ do
    -- TODO Add Subtype-Forall-(L|R)
    unless (posNonneg a b) (throwError "subtyping fail: not negNonpos")
    checkSubtype ctx Positive a b

  ------------------------------------------------------------------------------
  -- [Rule: SubtypeEquiv]
  --
  -- We don't check the polarity in this case.
  ------------------------------------------------------------------------------
  Nonpolar -> withRule "SubtypeEquiv" $ do
    unless ((a, b) & allOf each notQuantifierHead) (throwError "nonpolar")
    typeEquiv ctx a b

-- | Instantiate an existential variable.
instExVar :: Ctx -> ExVar -> Tm -> Sort -> TcM Ctx
instExVar = error "instExVar"

-- | Try to find a fact in the context that tells us what type and principality
-- a variable has, or, failing that, return Nothing.
varTyPrin :: Ctx -> Var -> Maybe (Ty, Prin)
varTyPrin ctx ex
  | Just (FcVarTy _ ty prin) <- factWith (varTyPrin' ex) ctx
  = Just (ty, prin)
  | otherwise = Nothing
  where
    varTyPrin' e1 (FcVarTy e2 _ _) = e1 == e2
    varTyPrin' _   _              = False

-- | Try to find a fact in the context. If this succeeds, create a "hole" and
-- return an ordered pair of the pieces of the context to the left and the
-- piece to the right.
hole :: Fact -> Ctx -> Maybe (Ctx, Ctx)
hole mem (Ctx ctx)
  | mem `notElem` ctx = Nothing
  | (left, r) <- S.breakl (== mem) ctx
  , right     <- S.drop 1 r
  = Just (Ctx left, Ctx right)

-- | Given two contexts and a fact, join them up, with the fact in the middle.
fillHole :: Ctx -> Fact -> Ctx -> Ctx
fillHole (Ctx l) f (Ctx r) = Ctx ((l S.|> f) <> r)

-- | Find the "polarity" of a type. Polarities are mainly (only?) used for the
-- subtyping judgment.
polarity :: Ty -> Polarity
polarity = \case
  TyExVar{} -> Positive
  TyUnVar{} -> Negative
  _ -> Nonpolar

-- | Turn A into [a^/a]A -- or, as I like to think of
-- it, A[a -> a^], read "A with a going to a^".
--
-- Reading a^ out loud is left as an exercise for the intrepid reader.
existentializeTy
  :: UnVar -- A
  -> Ty    -- a^
  -> Ty    -- [a^/a] A
existentializeTy u1@(UnSym sym) ty =
  case ty of
    TyUnVar u2
      | u1 == u2     -> TyExVar (ExSym sym)
    TyBinop l op r   -> TyBinop (extlTy l) op (extlTy r)
    TyForall un s a  -> TyForall un s (extlTy a)
    TyExists un s a  -> TyExists un s (extlTy a)
    TyImplies prop a -> TyImplies prop (extlTy a)
    TyWith a prop    -> TyWith (extlTy a) prop
    _ -> ty

  where extlTy = existentializeTy u1

-- | Does what it says on the tin. This is used by exactly one algorithmic
-- typing rule.
notACase :: Expr -> Bool
notACase = \case
  EpCase {} -> False
  _         -> True


logPre :: PreData -> TcM ()
logPre = logD . Pre

logMsg :: Judgment -> Text -> TcM ()
logMsg j t = logD (JMsg j t)

logPost :: PostData -> TcM ()
logPost = logD . Post

logRule :: Rule -> TcM ()
logRule = logD . JMatchedRule

logD :: JudgmentItem -> TcM ()
logD j = do
  indent <- view logIndent
  tell [LogItem indent j]

logRecur action = do
  local (logIndent +~ 1) action

withRule :: Text -> TcM a -> TcM a
withRule r x = logD (JRuleN (RuleName r)) *> x

-- logRecurRule prefix action = do
--   (result, rule) <- logRecur action `finally` do
--     logText' " " ""
--     logText' "J" prefix
--   logText' "J" rule
--   pure result

-- | The type-checking wrapper function. For now, this just logs a bit of
-- data and calls out to the *real* type-checking function.
check :: Ctx -> Expr -> Ty -> Prin -> TcM Ctx
check ctx ep ty pr = logRecur $ do
  logPre (PreCheck ctx ep ty pr)
  ctx' <- check' ctx ep ty pr
  logPost (PostCheck ctx')
  pure ctx'

-- | The function that actually does all the type-checking.
check'
  :: Ctx     -- ^ context representing knowledge before attempting the typecheck
  -> Expr    -- ^ expression to be checked
  -> Ty      -- ^ type to be checked against
  -> Prin    -- ^ are we claiming the type is principal?
  -> TcM Ctx -- ^ an updated context, representing what we know after said attempt

check' ctx ep ty prin
  | EpUnit <- ep
  , TyUnit <- ty
  = do
      withRule "UnitIntro" (pure ctx)

  ------------------------------------------------------------------------------
  -- [Rule: UnitIntro-Extl]
  --
  -- Introduction form for checking () against an unknown type.
  ------------------------------------------------------------------------------

  | EpUnit      <- ep
  , TyExVar ex  <- ty
  , Just (l, r) <- hole (FcExSort ex Star) ctx = do 
    logRule (RuleCheck RUnitIntro_Extl)
    pure (fillHole l (FcExEq ex Star TmUnit) r)

  ------------------------------------------------------------------------------
  -- [Rule: WithIntro]
  --
  -- A With form is only valid if the proposition `prop` attached to the type
  -- `a` is true in the current context.  On encountering one, we
  --
  --   1. check if the proposition is true in the current context `ctx`,
  --
  -- which gives us an updated context `theta` with possibly-new information.
  -- We then
  --
  --   2. update the type by substituting this context in, and
  --   3. check the expression against this updated type.
  ------------------------------------------------------------------------------

  | notACase ep
  , TyWith a prop <- ty
  , theta         <- checkProp ctx prop -- 1.
  = withRule "WithIntro" $ do
       let ty' = substituteCtx theta a  -- 2.
       check theta ep ty' prin          -- 3.

  ------------------------------------------------------------------------------
  -- [Rule: ForallIntro]
  --
  -- α : κ => alpha : k
  -- ν     => nu
  -- A     => a
  ------------------------------------------------------------------------------

  | nu <- ep
  , checkedIntroForm nu
  , TyForall alpha k a  <- ty
  , alpha'k             <- FcUnSort alpha k = do
      logRule (RuleCheck RForallIntro)
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

  | nu <- ep
  , TyImplies prop a     <- ty
  , Bang                 <- prin
  , markP                <- FcPropMark prop
  = let ctx' = assumeHypo (ctx |> markP) prop in  -- 1.
    case ctx' of                                  -- 2.

  -----------------------------------------------------------------------------
  -- [Rule: ImpliesIntro]
  --
  -- Our assumption of the hypothesis left our context consistent (i.e. it
  -- broke nothing), so we continue with the extra knowledge it gave us.
  -----------------------------------------------------------------------------

      ConCtx theta -> withRule "ImpliesIntro" $ do -- 3.
         outputCtx <- check theta nu (substituteCtx theta a) Bang
         case hole markP outputCtx of
           Just (delta, delta') -> do
             pure delta
           Nothing -> throwError "lol"

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
        throwError "check: ImpliesIntro*: fail"

  -----------------------------------------------------------------------------
  -- [Rule: ArrowIntro]
  --
  -- xap => x : A p
  -----------------------------------------------------------------------------

  | p                   <- prin
  , EpLam x e           <- ep
  , TyArrow a b         <- ty
  , xap                 <- FcVarTy x a p = do
      logRule (RuleCheck RArrowIntro)
      let xap = FcVarTy x a p
      check (ctx |> xap) e b p
        <&> hole xap
        >>= \case 
        Just (delta, theta) -> pure delta
        _ -> throwError "lol"

  ------------------------------------------------------------------------------
  -- [Rule: Rec]
  --
  -- TODO reduce duplication, combine with ArrowIntro
  ------------------------------------------------------------------------------

  | EpRec x nu <- ep = do
    logRule (RuleCheck RRec)
    let xap = FcVarTy x ty prin
    check (ctx |> xap) nu ty prin 
      <&> hole xap
      >>= \case 
      Just (delta, theta) -> pure delta
      _ -> throwError "lol"

  -----------------------------------------------------------------------------
  -- [Rule: ArrowIntro-Extl]
  --
  -- WT: using Slash because unspecified principality.
  -----------------------------------------------------------------------------

  | p                    <- Slash
  , EpLam x e            <- ep
  , TyExVar ex@a'        <- ty
  , Just Star            <- exVarSort ctx ex
  , Just (left, right)   <- hole (FcExSort ex Star) ctx = do
    logRule (RuleCheck RArrowIntro_Extl)
    a'1 <- freshEx
    a'2 <- freshEx

    let xa'1  = FcVarTy x (TyExVar a'1) Slash
        a'eq  = FcExEq a' Star (TmArrow (TmExVar a'1) (TmExVar a'2))
        a'1s  = FcExSort a'1 Star
        a'2s  = FcExSort a'2 Star
        ctx'  = left <> Ctx [a'1s, a'2s, a'eq] <> right
        ctx'' = ctx' |> xa'1

    out <- check ctx'' e (TyExVar a'2) Slash
    case hole xa'1 out of
      Just (delta, _) -> pure delta
      _ -> throwError "lol"

  -----------------------------------------------------------------------------
  -- SumIntroₖ
  --
  -- Introduction form for checking a sum expression against a sum type.
  --
  -- We match on the head constructor of the type, deferring the "which
  -- side am I injecting into" check to a case statement.
  -----------------------------------------------------------------------------

  | EpInj inj e     <- ep
  , TySum a1 a2     <- ty
  = withRule "SumIntro-k" 
  $ case inj of
      InjL -> check ctx e a1 prin
      InjR -> check ctx e a2 prin

  ------------------------------------------------------------------------------
  -- [Rule: SumIntro-Extlₖ]
  --
  -- Introduction form for checking a sum expression against an unknown type.
  ------------------------------------------------------------------------------

  | p <- Slash
  , EpInj inj e <- ep
  , TyExVar a'  <- ty
  , Just Star   <- exVarSort ctx a'
  , Just (left, right) <- hole (FcExSort a' Star) ctx
  = withRule "SumIntro-Extlₖ"
  $ do throwError ""
       a'1 <- freshEx
       a'2 <- freshEx

       let a'k = if inj == InjL then a'1 else a'2
           a'eq  = FcExEq a' Star (TmExVar a'1 `TmProd` TmExVar a'2)
           a'1s  = FcExSort a'1 Star
           a'2s  = FcExSort a'2 Star
           ctx'  = left <> Ctx [a'1s, a'2s, a'eq] <> right

       delta <- check ctx' e (TyExVar a'k) Slash
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

  | EpProd e1 e2    <- ep
  , TyProd a1 a2    <- ty
  = withRule "ProdIntro" $ do
       theta <- check ctx   e1 a1 prin
       check theta e2 (substituteCtx theta a2) prin

  ------------------------------------------------------------------------------
  -- [Rule: ProdIntro-Extl]
  --
  -- Introduction form for unsolved-for product types.
  ------------------------------------------------------------------------------

  | p                    <- Slash
  , EpProd e1 e2         <- ep
  , TyExVar ex@a'        <- ty
  , Just Star            <- exVarSort ctx ex
  , Just (left, right)   <- hole (FcExSort ex Star) ctx
  = withRule "ProdIntro-Extl" 
  $ do
      a'1 <- freshEx
      a'2 <- freshEx

      let a'eq  = FcExEq a' Star (TmExVar a'1 `TmProd` TmExVar a'2)
          a'1s  = FcExSort a'1 Star
          a'2s  = FcExSort a'2 Star
          ctx'  = left <> Ctx [a'1s, a'2s, a'eq] <> right

      theta <- check ctx' e1 (TyExVar a'1) Slash
      delta <- check theta e2 (substituteCtx theta (TyExVar a'2)) Slash
      pure delta

  ------------------------------------------------------------------------------
  -- [Rule: Case]
  --
  -- Case expressions, which are pattern vectors with bodies of some given type.
  ------------------------------------------------------------------------------
  | EpCase e alts <- ep
  , _C <- ty
  , p <- prin = do
    logRule (RuleCheck RCase)
    let gamma = ctx
    (_A, Bang, theta) <- infer ctx e
    delta <- matchBranches theta alts [substituteCtx theta _A] _C p
    True <- coverageCheck delta alts [substituteCtx delta _A]
    -- TODO continue from here
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

  | e <- ep
  , b <- ty
  , polB <- polarity b
  = withRule "Sub" $ do
       (a, q, theta) <- infer ctx e
       checkSubtype theta polB a b

  | otherwise
  = throwError "this shouldn't happen"

-- | Given a context and an expression, infer its type, a principality for it,
-- and an updated context.
infer :: Ctx -> Expr -> TcM (Ty, Prin, Ctx)
infer ctx ep = logRecur $ do
  logPre (PreInfer ctx ep)
  r@(ty, prin, ctx') <- infer' ctx ep
  logPost (PostInfer ty prin ctx')
  pure r

infer' :: Ctx -> Expr -> TcM (Ty, Prin, Ctx)
infer' ctx ep = case ep of

  ------------------------------------------------------------------------------
  -- [Rule: Var]
  --
  -- Variable expressions (e.g. the "x" in \x -> body).
  --
  -- These can have their types inferred if the context contains an FcVarTy fact
  -- that tells us its type (principality included).
  ------------------------------------------------------------------------------

  EpVar var
    | Just (ty, prin) <- varTyPrin ctx var -> do
      logRule (RuleInfer RVar)
      pure (substituteCtx ctx ty, prin, ctx)

  ------------------------------------------------------------------------------
  -- [Rule: Anno]
  --
  -- Type-annotated expressions.
  --
  -- The type is inferred by checking the type of the expression against the
  -- annotation.
  ------------------------------------------------------------------------------

  EpAnn e a
    | prinTypeWF ctx a Bang -> do
      logRule (RuleInfer RAnno)
      delta <- check ctx e (substituteCtx ctx a) Bang
      pure (substituteCtx delta a, Bang, delta)

  ------------------------------------------------------------------------------
  -- [Rule: ArrowE]
  --
  -- Infer the type of a spine application, recovering principality where
  -- possible.
  ------------------------------------------------------------------------------

  EpApp e spine
    | Spine [_] <- spine -> do
      logRule (RuleInfer RArrowE)
      (a, p, theta) <- infer ctx e
      (c, q, delta) <- inferSpineRecover theta spine a p
      pure (c, q, delta)


  _ -> throwError ("infer: don't know how to infer type of " <> Pretty.renderText ep)

freshHint :: Text -> TcM Text
freshHint hint = do
  n <- counter <+= 1
  pure (hint <> tshow n)

fresh :: TcM Text
fresh = freshHint "a"

freshEx :: TcM ExVar
freshEx = ExSym <$> fresh

-- | The free existential variables in a type.
freeExtls :: Ctx -> Ty -> [ExVar]
freeExtls ctx ty = filter (isFree ctx) exs
  where 
    exs = childrenBi ty
    isFree ctx ex = isNothing (solvedExVarSort ctx ex)

-- | The free universal variables in a ter.
freeUnivs :: Ctx -> Tm -> [UnVar]
freeUnivs ctx tm = filter (solvedUnVar ctx) uns
  where
    uns = childrenBi tm

-- | A synonym for @freeExtls@ matching the notation from the paper.
fev :: Ctx -> Ty -> [ExVar]
fev = freeExtls

noFreeExtls :: Ctx -> Ty -> Bool
noFreeExtls ctx = null . freeExtls ctx

hasFreeExtls :: Ctx -> Ty -> Bool
hasFreeExtls c = not . noFreeExtls c

unToEx :: UnVar -> ExVar
unToEx (UnSym sym) = ExSym sym

exToUn :: ExVar -> UnVar
exToUn (ExSym sym) = UnSym sym

-- | Infer the type of a spine application. This form does not attempt to
-- recover principality in the synthesized type.
--
-- I read the output (C, q, Δ) as "q-type C with output context Δ".
--
-- For example,
-- (Bang, TyUnit, Ctx Nil) = "the principal type () with empty output context"

inferSpine
  :: Ctx        -- ^ input context
  -> Spine      -- ^ spine being applied upon (ugh)
  -> Ty         -- ^ type of expression applied to the spine
  -> Prin       -- ^ principality of aforesaid expression
  -> TcM ( Ty   --   inferred type of application
         , Prin --   inferred principality of application
         , Ctx  --   output context
         )      -- ^ judgment
inferSpine ctx sp ty p = logRecur $ do
  logPre (PreSpine ctx sp ty p)
  r@(rty, rp, rctx) <- inferSpine' ctx sp ty p
  logPost (PostSpine rty rp rctx)
  pure r

inferSpine'
  :: Ctx        
  -> Spine     
  -> Ty       
  -> Prin       
  -> TcM (Ty, Prin, Ctx)

------------------------------------------------------------------------------
-- [Rule: ForallSpine]
--
-- The principality is omitted in the "top" rule (the antecedent?), so per
-- the "sometimes omitted" note in [Figure: Syntax of declarative types and
-- constructs], I'm assuming that means it's nonprincipal.
------------------------------------------------------------------------------
inferSpine' ctx sp (TyForall alpha k a) p = do
  logRule (RuleSpine RForallSpine)
  let
    Spine (e : s) = sp
    alpha'        = unToEx alpha
  (c, q, delta)   <- inferSpine (ctx |> FcExSort alpha' k) sp
                                (existentializeTy alpha a) Slash
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
  let
    Spine (e : s) = sp
    theta = checkProp ctx prop
  (c, q, delta) <- inferSpine theta sp (substituteCtx theta a) p
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
  let
    Spine (e : s') = sp
    s = Spine s'
  -- match the "function" against the input type a
  theta <- check ctx e a p
  -- match the "argument" against the output type b
  (c, q, delta) <- inferSpine theta s (substituteCtx theta b) p
  pure (c, q, delta)

  ------------------------------------------------------------------------------
  -- [Rule: Spine-Extl]
  --
  -- FIXME: Should we be returning the original principality, or just Slash
  -- since it was left unspecified?
  ------------------------------------------------------------------------------

inferSpine' ctx sp (TyExVar ex@a') p = do
  let
    Spine (e : s') = sp
  Just Star            <- pure (exVarSort ctx ex)
  Just (left, right)   <- pure (hole (FcExSort ex Star) ctx)
  a'1 <- freshEx
  a'2 <- freshEx

  let
    arrowMType = TmExVar a'1 `TmArrow` TmExVar a'2
    arrowType  = TyExVar a'1 `TyArrow` TyExVar a'2
    a'1s  = exStar a'1
    a'2s  = exStar a'2
    a'eq  = FcExEq a' Star arrowMType
    ctx'  = solveHole left right [a'1s, a'2s, a'eq]

  delta <- check ctx' e (TyExVar a'1) Slash
  pure (arrowType, p, delta)

inferSpine' _ _ _ _ = do
  logRule (RuleFail JSpine)
  throwError "inferSpine: the likely-impossible happened"

exStar :: ExVar -> Fact
exStar ex = FcExSort ex Star

solveHole :: Ctx -> Ctx -> Seq Fact -> Ctx
solveHole l r fs = l <> Ctx fs <> r

inferSpineRecover ctx sp ty p = logRecur $ do
  logPre (PreSpineRecover ctx sp ty p)
  r@(rt, rp, rc) <- inferSpineRecover' ctx sp ty p
  logPost (PostSpineRecover rt rp rc)
  pure r

-- | Infer the type of a spine application. Additionally, this form
-- attempts to recover principality in the output type.
inferSpineRecover' :: Ctx -> Spine -> Ty -> Prin -> TcM (Ty, Prin, Ctx)
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
      if fevCond then do
        logMsg JSpineRecover "No free existential variables. Recovering principality."
        logRule (RuleSpineRecover RSpineRecover)

        pure (c, Bang, delta)
      else do
        ------------------------------------------------------------------------------
        -- [Rule: SpinePass]
        --
        -- WT: guessing "pass" is for "pass the principality inferred by
        -- inferSpine through"
        ------------------------------------------------------------------------------
        logMsg JSpineRecover "Free existential variables, passing principality through."
        logRule (RuleSpineRecover RSpinePass)

        res2 <- inferSpine ctx s a p
        case res2 of
          res@(c, q, delta)
            | p == Slash || q == Bang || hasFreeExtls delta c
            -> pure res
          _ -> throwError "is this even possible?"

-- | Check case-expressions.
-- Wrapper for @matchBranches'@.
matchBranches :: Ctx -> Alts -> [Ty] -> Ty -> Prin -> TcM Ctx
matchBranches ctx alts ts ty p = logRecur $ do
  logPre (PreMatch ctx alts ts ty p)
  ctx' <- matchBranches' ctx alts ts ty p
  logPost (PostMatch ctx')
  pure ctx'

-- | Check case-expressions.
-- Given an input context, a case-expression, a type-vector, and a 
-- type/prin pair, attempt to match the case-expr/typevec against the
-- type with the given principality, returning an updated output context.
matchBranches' :: Ctx -> Alts -> [Ty] -> Ty -> Prin -> TcM Ctx

------------------------------------------------------------------------------
-- [Rule: MatchNil]
------------------------------------------------------------------------------
matchBranches' gamma (Alts []) _ _ _ = do
  logRule (RuleMatch RMatchNil)
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

matchBranches' gamma (Alts [Branch (PatProd p1 p2:ps) e]) (TyProd _A1 _A2:_As) ty p = do
  logRule (RuleMatch RMatchProd)
  delta <- matchBranches gamma (Alts [Branch (p1 : p2 : ps) e]) (_A1 : _A2 : _As) ty p
  pure delta

------------------------------------------------------------------------------
-- [Rule: MatchInj_k]
--
-- Match an "Either" pattern.
------------------------------------------------------------------------------
matchBranches' gamma (Alts [Branch (PatInj k rho:ps) e]) (TySum _A1 _A2:_As) ty p = do
  logRule (RuleMatch (RMatchInj k))
  let _Ak = if k == InjL then _A1 else _A2
  delta <- matchBranches gamma (Alts [Branch (rho : ps) e]) (_Ak : _As) ty p
  pure delta

matchBranches' gamma (Alts [Branch (PatWild:ps) e]) (_A:_As) _C p = do
  logRule (RuleMatch RMatchWild)
  unless (notQuantifierHead _A) (throwError "quantifier-headed type")
  delta <- matchBranches gamma (Alts [Branch ps e]) _As _C p
  pure delta

matchBranches' gamma (Alts [Branch (PatVec Nil:ps) e]) (TyVec t _A:_As) _C p = do
  logRule (RuleMatch RMatchNil)
  delta <- matchBranchesAssuming gamma
                                 (Equation t (TmNat Zero))
                                 (Alts [Branch ps e])
                                 _As
                                 _C
                                 p
  pure delta

------------------------------------------------------------------------------
-- [Rule: MatchSeq]
------------------------------------------------------------------------------
matchBranches' gamma (Alts (pi : _Pi)) _A _C p = do 
  logRule (RuleMatch RMatchSeq)
  theta <- matchBranches gamma (Alts [pi]) _A _C p
  delta <- matchBranches theta (Alts _Pi) _A _C p
  pure delta

-- matchBranches' _ _ _ _ _ = do
--   logRule (RuleFail JMatch)
--   throwError "matchBranch'"

matchBranchesAssuming :: Ctx -> Prop -> Alts -> [Ty] -> Ty -> Prin -> TcM Ctx
matchBranchesAssuming gamma prop@(Equation lt rt) alts@(Alts bs) ts ty p = do
  -- logPre (PreMatchAssuming gamma prop alts ts ty p)
  go

  where
    go
      | length bs /= 1 = throwError "too many branches"
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
-- [Coverage checking]
--
-- The paper has two coverage-checking judgments:
--
-- 1. Γ   ⊢ Π covers [A..]
-- 2. Γ/P ⊢ Π covers [A..]
--
-- which are implemented and explained in @coverageCheck@ and
-- @coverageCheckAssuming@ respectively. See the documentation for those to
-- know what they do.
--------------------------------------------------------------------------------

-- | This implements the first of the two coverage-checking judgments, written
--
--   Γ   ⊢ Π covers [A..]
--
-- in the paper. This means that, in context Γ, the patterns Π cover the
-- types in [A..].

coverageCheck :: Ctx -> Alts -> [Ty] -> TcM Bool
coverageCheck ctx alts tys = do
  logRecur (coverageCheck' ctx alts tys)

coverageCheck' :: Ctx -> Alts -> [Ty] -> TcM Bool
coverageCheck' ctx alts tys

  ------------------------------------------------------------------------------
  -- [Rule: CoversNil]
  ------------------------------------------------------------------------------

  | [] <- tys
  , Alts (Branch [] _e1 : _Pi) <- alts
  = pure True

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

  | otherwise
  = pure True -- error "coverage"

prepareUnitAlts :: Alts -> TcM Alts
prepareUnitAlts (Alts bs) = Alts <$> go bs
 where
  go :: [Branch] -> TcM [Branch]
  go = \case
    []                  -> pure []
    Branch (r:rs) e:_Pi -> do
      unless (ok r) (throwError "fail")
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

coverageCheckAssuming :: Ctx -> Prop -> Alts -> [Ty] -> Bool
coverageCheckAssuming ctx prop alts tys

  ------------------------------------------------------------------------------
  -- [Rule: CoversEq]
  ------------------------------------------------------------------------------

  ------------------------------------------------------------------------------
  -- [Rule: CoversEqBot]
  ------------------------------------------------------------------------------

  | otherwise
  = error "coverageCheckAssuming"

lam :: Text -> Expr -> Expr
lam v = EpLam (Sym v)

ann :: Expr -> Ty -> Expr
ann = EpAnn

tyUniv :: Text -> Ty
tyUniv s = TyUnVar (UnSym s)

tyExtl :: Text -> Ty
tyExtl s = TyExVar (ExSym s)

ty_unit_to_unit :: Ty
ty_unit_to_unit = TyUnit `TyArrow` TyUnit

--------------------------------------------------------------------------------
-- Pretty-printing
--------------------------------------------------------------------------------

execTcM :: TcM a -> IO (Either Text a)
execTcM action = do
  ((result, tcLog), finalState) <-
    action
    & runTcM
    & runExceptT
    & (runReaderT ?? initialConfig)
    & runWriterT'
    & (runStateT ?? initialState)
  pure result

-- tests :: IO ()
-- tests = hspec tests'

-- eTermSort :: Tm -> Either Text Sort
-- eTermSort = execTcM . inferSort initialContext

-- tests' :: SpecWith ()
-- tests' =
--   describe "inferring the sort of a term (`inferSort`)" $ do
--     context "given an existential variable" $ 
--       it "fails if the variable is unknown" $ 
--         eTermSort (TmExVar (ExSym "foo")) `shouldSatisfy` isn't _Right

--     it "sort of Unit is Star" $ 
--       eTermSort TmUnit `shouldBe` Right Star

--     it "sort of Unit -> Unit is Star" $ 
--       eTermSort (TmUnit `TmArrow` TmUnit) `shouldBe` Right Star

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
  x = Sym "a"
  l = Sym "l"

sndExpr :: Expr
sndExpr = EpAnn expr ty
 where
  ty = TyForall
    a
    Star
    (TyForall b Star (TyArrow (TyProd (TyUnVar a) (TyUnVar b)) (TyUnVar a)))
  expr = EpLam
    x
    (EpCase (EpVar x) (Alts [Branch [PatProd PatWild (PatVar r)] (EpVar r)]))
  a = UnSym "a"
  b = UnSym "b"
  x = Sym "a"
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
  x = Sym "a"
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
(pairOfLists,listOfPairs) = (f,s)
  where
    f = PatProd (PatVec [PatVar x, PatVar xs]) (PatVec [PatVar y, PatVar ys])
    s = PatVec [patProd x y, patProd xs ys]
    patProd a b = PatProd (PatVar a) (PatVar b)
    x     = Sym "x"
    xs    = Sym "xs"
    y     = Sym "y"
    ys    = Sym "ys"

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

idCtx :: Ctx
idCtx =
  initialContext
    |> FcVarTy (Sym "id")    idType    Bang
    |> FcVarTy (Sym "const") constType Bang

constApp :: Expr
constApp = EpApp (EpVar (Sym "const")) (Spine [EpUnit])

idApp :: Expr
idApp = EpApp (EpVar (Sym "id")) (Spine [EpUnit])

bigStep :: Ctx -> Expr -> TcM Expr
bigStep ctx = \case
  EpUnit     -> pure EpUnit
  EpProd a b -> EpProd <$> bigStep ctx a <*> bigStep ctx b

