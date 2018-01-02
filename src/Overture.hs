{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
module Overture
  ( module X
  , module Prelude
  , sshow
  , LText.toStrict
  , LText.fromStrict
  , LText.Text
  , Text'
  , tshow
  , tshow'
  , putTextLn
  , putTextLn'
  , LByteString.ByteString
  , ByteString'
  , bshow
  , bshow'
  , putBSLn
  , putBSLn'

  , unimplemented
  , error

  , map
  , for
  , pass
  , Map.Map

  , LState.State
  , LState.StateT
  , State'
  , StateT'
  , LState.runStateT
  , LState.runState
  , runStateT'

  , LWriter.Writer
  , LWriter.WriterT
  , Writer'
  , WriterT'
  , runWriterT'
  ) where

import Prelude hiding
  ( error
  , undefined
  , map
  , concat
  , (!!)
  )

import qualified Data.Text.Lazy      as LText
import qualified Data.Text.Lazy.IO   as LTextIO
import qualified Data.Text           as SText
import qualified Data.Text.IO        as STextIO

import qualified Data.Map       as Map

import qualified Data.ByteString.Lazy as LByteString
import qualified Data.ByteString      as SByteString
import qualified Data.ByteString.Lazy.Char8 as LByteString8
import qualified Data.ByteString.Char8 as SByteString8

import qualified Prelude as P

import qualified Data.String

import qualified Data.Monoid

import qualified Control.Monad.State.Lazy   as LState
import qualified Control.Monad.State.Strict as SState

import qualified Control.Monad.Writer.Lazy   as LWriter
import qualified Control.Monad.Writer.Strict as SWriter

import qualified Control.Monad.Reader       as Reader

import Data.Kind as X (Constraint, Type)

import Control.Arrow as X ((>>>), (<<<))

import qualified Control.Category as Category

import Control.Lens as X
import Data.Function as X
import Data.Functor as X
import Data.Foldable as X
import Control.Applicative as X
import Data.Maybe as X
import Control.Monad as X
import Data.Int as X
import Data.List.NonEmpty as X (NonEmpty(..), (!!))
import Data.Semigroup as X

import GHC.Generics as X (Generic)
import Data.Data as X (Data)
import Data.Typeable as X (Typeable)

-- | A polymorphic @P.show@ function for any instance of the 
-- @Data.String.IsString@ class.
--
-- Sometimes the polymorphism must be constrained using, e.g.
-- explicit type annotations. For convenience, we provide synonyms
-- for the Text and ByteString types.
sshow :: (P.Show a, Data.String.IsString s) => a -> s
sshow a = Data.String.fromString (P.show a)

type Text' = SText.Text
type ByteString' = SByteString.ByteString

-- | @sshow@ specialised to @Text@.
tshow :: P.Show a => a -> LText.Text
tshow a = LText.pack (P.show a)

-- | @sshow@ specialised to @Text'@.
tshow' :: P.Show a => a -> Text'
tshow' a = SText.pack (P.show a)

-- | @sshow@ specialised to @ByteString@.
bshow :: P.Show a => a -> LByteString.ByteString
bshow = sshow

-- | @sshow@ specialised to @ByteString'@.
bshow' :: P.Show a => a -> ByteString'
bshow' = sshow

{-# WARNING unimplemented "Partial function `unimplemented` left in code" #-}
unimplemented :: a
unimplemented = P.error "Not implemented"

{-# WARNING error "Partial function `error` left in code" #-}
error :: Text' -> a
error a = P.error (SText.unpack a)

map :: Functor f => (a -> b) -> f a -> f b
map = P.fmap
{-# INLINE map #-}

for :: Functor f => f a -> (a -> b) -> f b
for = P.flip fmap
{-# INLINE for #-}

putTextLn :: LText.Text -> IO ()
putTextLn = LTextIO.putStrLn

putTextLn' :: SText.Text -> IO ()
putTextLn' = STextIO.putStrLn

putBSLn :: LByteString8.ByteString -> IO ()
putBSLn = LByteString8.putStrLn

putBSLn' :: SByteString8.ByteString -> IO ()
putBSLn' = SByteString8.putStrLn

-- | Return a unit from an arbitrary applicative.
pass :: Applicative f => f ()
pass = pure ()
{-# INLINE pass #-}

concatList :: [a] -> [a] -> [a]
concatList = (P.++)
{-# INLINE concatList #-}

concat :: Monoid s => [s] -> s
concat = Data.Monoid.mconcat
{-# INLINE concat #-}

type State'  s = SState.State  s
type StateT'   = SState.StateT

type Writer' w = SWriter.Writer w
type WriterT'  = SWriter.WriterT

runWriterT' :: WriterT' w m a -> m (a, w)
runWriterT' = SWriter.runWriterT
{-# INLINE runWriterT' #-}

runStateT' :: StateT' s m a -> s -> m (a, s)
runStateT' = SState.runStateT
{-# INLINE runStateT' #-}
