module Main where

import Pretty
import Types
import Infer

main :: IO ()
main = do
  putStrLn ""
  putStrLn ""
  putStrLn ""
  putStrLn (show (ppr mapExpr))
  putStrLn ""
  putStrLn ""

expr :: E
expr = Const 1 :+: Const 2 :*: ((Const 3 :+: Const 4) :/: Const 6)

data E =
  Const Int |
  E :+: E |
  E :-: E |
  E :*: E |
  E :/: E

infixl 6 :+:
infixl 6 :-:
infixl 7 :*:
infixl 7 :/:

instance Show E where
  showsPrec p e0 =
    case e0 of
     Const n -> showParen (p > 10) $ showString "Const " . showsPrec 11 n
     x :+: y -> showParen (p > 6) $ showsPrec 6 x . showString " :+: " . showsPrec 7 y
     x :-: y -> showParen (p > 6) $ showsPrec 6 x . showString " :-: " . showsPrec 7 y
     x :*: y -> showParen (p > 7) $ showsPrec 7 x . showString " :*: " . showsPrec 8 y
     x :/: y -> showParen (p > 7) $ showsPrec 7 x . showString " :/: " . showsPrec 8 y
