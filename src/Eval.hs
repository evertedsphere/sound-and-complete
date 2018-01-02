{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Eval where

import qualified Data.Map as Map
import Data.Map (Map)

import Overture

import Types
import Pretty
import Infer

newtype EvCtx = EvCtx { unEvCtx :: Map Var Expr }

initEvCtx :: EvCtx
initEvCtx = EvCtx Map.empty

isValue :: Expr -> Bool
isValue x = 
  case x of
    EpVar{} -> True
    EpUnit -> True
    EpLam _ e -> True -- TODO not a value?
    EpRec _ v -> isValue v
    EpAnn v _ -> isValue v
    EpProd v1 v2 -> isValue v1 && isValue v2
    EpInj _ v -> isValue v
    EpVec (Vec vs) -> all isValue vs
    EpCase{} -> False
    EpApp{} -> False

bigStep :: EvCtx -> Expr -> TcM Expr
bigStep (EvCtx ev_ctx) e = go ev_ctx e
 where
  go ctx = \case
    EpUnit         -> pure EpUnit
    EpProd a b     -> EpProd <$> go ctx a <*> go ctx b
    EpInj  i e     -> EpInj i <$> go ctx e
    EpAnn  e ty    -> go ctx e
    EpVec (Vec es) -> EpVec . Vec <$> traverse (go ctx) es
    EpVar v        -> case Map.lookup v ctx of
      Just val -> go ctx val
      Nothing  -> failWith ("unknown binding" <+> ppr v)

    EpApp (EpAnn e ty) args -> go ctx (EpApp e args)
    EpApp e  (Spine []      ) -> go ctx e
    EpApp fn (Spine (arg:as)) -> case fn of
      EpLam v e -> go extended_ctx (EpApp e (Spine as))
        where extended_ctx = Map.insert v arg ctx
      _ -> failWith ("attempt to apply non-lambda expression" <+> ppr e)

    EpCase v@EpVar{} alts -> EpCase <$> go ctx v <*> pure alts >>= go ctx
    EpCase (EpProd el er) (Alts [Branch [PatProd pl pr] body]) -> 
      case pl of
        PatVar vl -> go extended_ctx body
          where extended_ctx = Map.insert vl el ctx

    p -> failWith ("bigStep: boom" <+> unAnnotate (ppr p))

  -- | EpRec   Var   Expr
  -- | EpCase  Expr  Alts
