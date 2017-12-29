module Main where

import Pretty
import Types
import Infer
import Data.Text.Prettyprint.Doc.Util (putDocW)

main :: IO ()
main = do
  ppInfer initialContext curriedZipExpr

pprs es = let
  pprPlain n e = do
    putStrLn ""
    renderStdout e
    putStrLn ""
  in do
    mapM_ (pprPlain 40) es
