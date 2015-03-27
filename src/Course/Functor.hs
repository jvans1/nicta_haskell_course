{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}

module Course.Functor where

import Course.Core
import Course.Id
import Course.Optional
import Course.List
import qualified Prelude as P

-- | All instances of the `Functor` type-class must satisfy two laws. These laws
-- are not checked by the compiler. These laws are given as:
--
-- * The law of identity
--   `∀x. (id <$> x) ≅ x`
--
-- * The law of composition
--   `∀f g x.(f . g <$> x) ≅ (f <$> (g <$> x))`
class Functor f where
  -- Pronounced, eff-map.
  (<$>) :: (a -> b) -> f a -> f b

infixl 4 <$>

-- $setup
-- >>> :set -XOverloadedStrings
-- >>> import Course.Core
-- >>> import qualified Prelude as P(return, (>>))

-- | Maps a function on the Id functor.
--
-- >>> (+1) <$> Id 2
-- Id 3
instance Functor Id where
  (<$>) :: (a -> b) -> Id a -> Id b
  (<$>) f (Id a) = Id $ f a

-- | Maps a function on the List functor.
--
-- >>> (+1) <$> Nil
-- []
--
-- >>> (+1) <$> (1 :. 2 :. 3 :. Nil)
-- [2,3,4]
--
-- data List t = Nil | t :. List t deriving (Eq, Ord)
--
instance Functor List where
  (<$>) :: (a -> b) -> List a -> List b
  (<$>) f Nil = Nil
  (<$>) f (a :. xs) = f a :. (f <$> xs)

-- | Maps a function on the Optional functor.
--
-- >>> (+1) <$> Empty
-- Empty
--
-- >>> (+1) <$> Full 2
-- Full 3
-- - data Optional a = Full a | Empty deriving (Eq, Show)
instance Functor Optional where
  (<$>) :: (a -> b) -> Optional a -> Optional b
  (<$>) f Empty = Empty
  (<$>) f (Full a) = Full $ f a

-- | Maps a function on the reader ((->) t) functor.
--
-- >>> ((+1) <$> (*2)) 8
-- 17
instance Functor ((->) t) where
  (<$>) :: (a -> b) -> ((->) t a) -> ((->) t b)
  (<$>) f fn = f . fn

-- | Anonymous map. Maps a constant value on a functor.
--
-- >>> 7 <$ [1,2,3]
-- [7,7,7]
--
-- prop> x <$ [a,b,c] == [x,x,x]
--
-- prop> x <$ Full q == Full x
(<$) :: Functor f => a -> f b -> f a
(<$) x c = (\_ -> x) <$> c

-- | Anonymous map producing unit value.
--
-- >>> void [1,2,3]
-- [(),(),()]
--
-- >>> void (Full 7)
-- Full ()
--
-- >>> void Empty
-- Empty
--
-- >>> void (+10) 5
-- ()
void :: Functor f => f a -> f ()
void fa = (\_ -> ()) <$> fa

-----------------------
-- SUPPORT LIBRARIES --
-----------------------

-- | Maps a function on an IO program.
--
-- >>> reverse <$> (putStr "hi" P.>> P.return ("abc" :: List Char))
-- hi"cba"
instance Functor IO where
  (<$>) = P.fmap

instance Functor [] where
  (<$>) = P.fmap 
instance Functor P.Maybe where
  (<$>) = P.fmap
