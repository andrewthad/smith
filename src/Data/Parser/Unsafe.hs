{-# language UnboxedTuples #-}
{-# language MagicHash #-}

module Data.Parser.Unsafe
  ( unconsume
  ) where

import GHC.Exts (Int(I#),Int#)
import Data.Parser (Parser(..),Result(..),Slice(..))
import Data.Primitive.SmallArray (SmallArray(SmallArray))

-- | Move the cursor back by @n@ tokens. Precondition: you
-- must have previously consumed at least @n@ tokens.
unconsume :: Int -> Parser a e s ()
unconsume n = uneffectful $ \_ off len ->
  Success (Slice (off - n) (len + n) ())

uneffectful ::
     (SmallArray a -> Int -> Int -> Result e b)
  -> Parser a e s b
{-# inline uneffectful #-}
uneffectful f = Parser
  ( \(# arr,off,len #) s0 -> (# s0, unboxResult (f (SmallArray arr) (I# off) (I# len)) #) )

unboxResult :: Result e a -> (# e | (# a, Int#, Int# #) #) 
unboxResult (Success (Slice (I# b) (I# c) a)) = (# | (# a, b, c #) #)
unboxResult (Failure e) = (# e | #)

