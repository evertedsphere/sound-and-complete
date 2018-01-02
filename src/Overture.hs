{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
module Overture
  ( module X
  , module Prelude
  , sshow
  , String
  , LText.toStrict
  , LText.fromStrict
  , Text
  , Text'
  , tshow
  , tshow'
  , putTextLn
  , putTextLn'
  , ByteString
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
  , String
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

import Data.Void as X (Void, absurd, vacuous)
import Data.Kind as X (Constraint, Type)

import Control.Lens as X
import Control.Arrow as X ((>>>), (<<<))

import qualified Control.Category as Category

import Control.Monad.State.Class as X (
    MonadState(..)
  , put
  , get
  , gets
  , modify
  , state
  )

import Control.Monad.Reader as X
  ( MonadReader(..)
  , ask
  , asks
  , local
  , reader
  , Reader
  , ReaderT(ReaderT)
  , runReader
  , runReaderT
  )

import Control.Monad.Writer.Class as X
  ( MonadWriter
  , writer
  , tell
  , listen
  )

import Control.Monad.Except as X (
    MonadError(..)
  , throwError
  , catchError
  , runExcept
  , runExceptT

  , Except
  , ExceptT(ExceptT)
  )

import Control.Monad.Trans as X
  ( MonadIO(..)
  , lift
  , liftIO
  )

import Control.Lens as X

import Data.Void as X
  ( Void
  , absurd
  , vacuous
  )

import Data.Function as X
  ( const
  , ($)
  , flip
  , fix
  , on
  , (&)
  )

import Data.Functor as X
  ( Functor(..)
  , (<$)
  , ($>)
  , (<$>)
  , void
  )

import System.Environment as X (getArgs)

import qualified System.Exit

import System.Exit as X (
    ExitCode(..)
  , exitWith
  , exitFailure
  , exitSuccess
  )
import System.IO as X
  ( Handle
  , FilePath
  , IOMode(..)
  , stdin
  , stdout
  , stderr
  , withFile
  , openFile
  )

import Data.Foldable as X

import Control.Applicative as X

import Data.Typeable as X (Typeable)

import Data.Maybe as X

import Control.Monad as X

import Data.Int as X

import Data.List.NonEmpty as X (NonEmpty(..), (!!))

import Data.Semigroup as X

import GHC.Generics as X (Generic)
import Data.Data as X (Data)
import Data.Typeable as X (Typeable)

type String = Data.String.String

-- | A polymorphic @P.show@ function for any instance of the 
-- @Data.String.IsString@ class.
--
-- Sometimes the polymorphism must be constrained using, e.g.
-- explicit type annotations. For convenience, we provide synonyms
-- for the Text and ByteString types.
sshow :: (P.Show a, Data.String.IsString s) => a -> s
sshow a = Data.String.fromString (P.show a)

type Text  = LText.Text
type Text' = SText.Text

type ByteString  = LByteString.ByteString
type ByteString' = SByteString.ByteString

-- | @sshow@ specialised to @Text@.
tshow :: P.Show a => a -> Text
tshow a = LText.pack (P.show a)

-- | @sshow@ specialised to @Text'@.
tshow' :: P.Show a => a -> Text'
tshow' a = SText.pack (P.show a)

-- | @sshow@ specialised to @ByteString@.
bshow :: P.Show a => a -> ByteString
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

-- | Do nothing returning unit inside applicative.
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

-- These are pretty useless since (<$) and ($>) exist
-- (&>) :: Functor f => b -> f a -> f b
-- (&>) = map . const
-- (<&) :: Functor f => f a -> b -> f b
-- (<&) fa = for fa . const
