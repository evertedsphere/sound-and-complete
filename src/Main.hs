{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
module Main where

import Pretty
import Types
import Infer
import Data.Text.Prettyprint.Doc.Util (putDocW)

import GHC.TypeLits
import Data.Kind

main :: IO ()
main = do
  ppInfer initialContext fstExpr  
  ppInfer initialContext badSndExpr

pprs es = let
  pprPlain n e = do
    putStrLn ""
    renderStdout e
    putStrLn ""
  in do
    mapM_ (pprPlain 40) es
