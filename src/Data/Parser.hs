{-# language BangPatterns #-}
{-# language BinaryLiterals #-}
{-# language DataKinds #-}
{-# language DeriveFunctor #-}
{-# language DerivingStrategies #-}
{-# language GADTSyntax #-}
{-# language KindSignatures #-}
{-# language LambdaCase #-}
{-# language MagicHash #-}
{-# language MultiWayIf #-}
{-# language PolyKinds #-}
{-# language RankNTypes #-}
{-# language ScopedTypeVariables #-}
{-# language StandaloneDeriving #-}
{-# language TypeApplications #-}
{-# language UnboxedSums #-}
{-# language UnboxedTuples #-}

module Data.Parser
  ( Parser(..)
  , Result(..)
  , Slice(..)
  , parseSmallArray
  , parseSmallArrayEffectfully
    -- * Primitives
  , any
  , opt
  , peek
  , token
  , effect
  , fail
    -- * Control Flow
  , foldSepBy1
  , sepBy1
  , skipWhile
  ) where

import Prelude hiding (length,any,fail)

import Data.Bool (bool)
import Data.Kind (Type)
import Data.Primitive (SmallArray(..))
import Data.Bytes.Parser.Types (Result(..),Slice(..))
import GHC.Exts (TYPE,Int(I#),Int#,State#,SmallArray#)
import GHC.ST (ST(ST),runST)

import qualified Control.Monad
import qualified Data.Primitive as PM
import qualified GHC.Exts as Exts

type SmallVector# a = (# SmallArray# a, Int#, Int# #)
type ST# s (a :: TYPE r) = State# s -> (# State# s, a #)
type Result# e (a :: TYPE r) =
  (# e
  | (# a, Int#, Int# #) #) -- ints are offset and length

newtype Parser :: Type -> Type -> Type -> Type -> Type where
  Parser :: { runParser :: SmallVector# a -> ST# s (Result# e b) }
         -> Parser a e s b

instance Functor (Parser a e s) where
  {-# inline fmap #-}
  fmap f (Parser g) = Parser
    (\x s0 -> case g x s0 of
      (# s1, r #) -> case r of
        (# e | #) -> (# s1, (# e | #) #)
        (# | (# a, b, c #) #) -> (# s1, (# | (# f a, b, c #) #) #)
    )

instance Applicative (Parser a e s) where
  pure = pureParser
  (<*>) = Control.Monad.ap

instance Monad (Parser a e s) where
  {-# inline return #-}
  {-# inline (>>=) #-}
  return = pureParser
  Parser f >>= g = Parser
    (\x@(# arr, _, _ #) s0 -> case f x s0 of
      (# s1, r0 #) -> case r0 of
        (# e | #) -> (# s1, (# e | #) #)
        (# | (# y, b, c #) #) ->
          runParser (g y) (# arr, b, c #) s1
    )

pureParser :: b -> Parser a e s b
pureParser a = Parser
  (\(# _, b, c #) s -> (# s, (# | (# a, b, c #) #) #))

-- | Consumes and returns the next token from the input.
-- Fails if no tokens are left.
any :: e -> Parser a e s a
{-# inline any #-}
any e = uneffectful $ \array off len -> case len of
  0 -> Failure e
  _ ->
    let w = PM.indexSmallArray array off
     in Success (Slice (off + 1) (len - 1) w)

opt :: Parser a e s (Maybe a)
{-# inline opt #-}
opt = uneffectful $ \array off len -> case len of
  0 -> Success (Slice off 0 Nothing)
  _ -> 
    let w = PM.indexSmallArray array off
     in Success (Slice (off + 1) (len - 1) (Just w))

-- | Lift an effect into a parser.
effect :: ST s b -> Parser a e s b
{-# inline effect #-}
effect (ST f) = Parser
  (\(# _, off, len #) s0 -> case f s0 of
    (# s1, b #) -> (# s1, (# | (# b, off, len #) #) #)
  )

-- | Consumes and returns the next token from the input.
-- Fails if no tokens are left.
fail :: e -> Parser a e s b
{-# inline fail #-}
fail e = Parser (\_ s0 -> (# s0, (# e | #) #) )

-- | Consumes the next token from the input. Fails if it
-- is not equal to the expected value.
token :: Eq a
  => e -- ^ Error message
  -> a -- ^ Expected value of next token
  -> Parser a e s ()
{-# inline token #-}
token e a = do
  b <- any e
  bool (fail e) (pure ()) (a == b)

-- | Returns the next token from the input without consuming
-- it. Fails if no tokens are left.
peek :: e -> Parser a e s a
{-# inline peek #-}
peek e = uneffectful $ \array off len -> if len > 0
  then
    let w = PM.indexSmallArray array off
     in Success (Slice off len w)
  else Failure e

-- | Fold over the tokens, repeatedly running @step@ followed
-- by @separator@ until @separator@ returns 'False'. This is
-- strict in the accumulator and always runs @step@ at least
-- once. There is no backtracking; any failure causes the whole
-- combinator to fail. 
foldSepBy1 ::
     Parser a e s Bool -- ^ Separator
  -> (b -> Parser a e s b) -- ^ Step
  -> b -- ^ Initial value
  -> Parser a e s b
{-# inline foldSepBy1 #-}
foldSepBy1 sep f b0 = f b0 >>= go
  where
  go !b = sep >>= \case
    True -> f b >>= go
    False -> pure b

-- | Skip tokens for which the predicate is true.
skipWhile ::
     (a -> Bool) -- ^ Predicate
  -> Parser a e s ()
{-# inline skipWhile #-}
skipWhile f = go where
  go = opt >>= \case
    Nothing -> pure ()
    Just t -> case f t of
      True -> go
      False -> internalUnconsume 1

-- | Fold over the tokens, repeatedly running @step@ followed
-- by @separator@ until @separator@ returns 'False'. The results
-- of @step@ are discarded, but in conjunction with @effect@,
-- this can be used to populate an array or a builder. This
-- always runs @step@ at least once.
--
-- > sepBy1 sep step === step *> (sep >>= bool (pure ()) (step *> (sep >>= bool (pure ()) (...))))
sepBy1 ::
     Parser a e s Bool -- ^ Separator
  -> Parser a e s b -- ^ Step
  -> Parser a e s ()
{-# inline sepBy1 #-}
sepBy1 sep f = f *> go where
  go = sep >>= \case
    True -> f *> go
    False -> pure ()
    
uneffectful :: (SmallArray a -> Int -> Int -> Result e b) -> Parser a e s b
{-# inline uneffectful #-}
uneffectful f = Parser
  ( \(# arr,off,len #) s0 -> (# s0, unboxResult (f (SmallArray arr) (I# off) (I# len)) #) )

unboxResult :: Result e a -> Result# e a
unboxResult (Success (Slice (I# b) (I# c) a)) = (# | (# a, b, c #) #)
unboxResult (Failure e) = (# e | #)

parseSmallArray ::
     forall a e b. (forall s. Parser a e s b)
  -> SmallArray a
  -> Result e b
parseSmallArray p (SmallArray arr) = runST action
  where
  action :: forall s. ST s (Result e b)
  action = case p @s of
    Parser f -> ST
      (\s0 -> case f (# arr, 0#, (Exts.sizeofSmallArray# arr) #) s0 of
        (# s1, r #) -> (# s1, boxResult r #)
      )

parseSmallArrayEffectfully :: Parser a e s b -> SmallArray a -> ST s (Result e b)
parseSmallArrayEffectfully (Parser f) (SmallArray arr) = ST
  (\s0 -> case f (# arr, 0#, (Exts.sizeofSmallArray# arr) #) s0 of
    (# s1, r #) -> (# s1, boxResult r #)
  )

boxResult :: Result# e a -> Result e a
boxResult (# | (# a, b, c #) #) = Success (Slice (I# b) (I# c) a)
boxResult (# e | #) = Failure e

-- A copy of unconsume so that the modules do not need to
-- be restructured.
internalUnconsume :: Int -> Parser a e s ()
{-# inline internalUnconsume #-}
internalUnconsume n = uneffectful $ \_ off len ->
  Success (Slice (off - n) (len + n) ())

