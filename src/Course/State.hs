{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RebindableSyntax #-}

module Course.State where

import Course.Core
import qualified Prelude as P
import Course.Optional
import Course.List
import Course.Functor
import Course.Apply
import Course.Applicative
import Course.Bind
import Course.Monad
import qualified Data.Set as S

-- $setup
-- >>> import Test.QuickCheck.Function
-- >>> import Data.List(nub)
-- >>> import Test.QuickCheck
-- >>> import qualified Prelude as P(fmap)
-- >>> import Course.Core
-- >>> import Course.List
-- >>> instance Arbitrary a => Arbitrary (List a) where arbitrary = P.fmap listh arbitrary

-- A `State` is a function from a state value `s` to (a produced value `a`, and a resulting state `s`).
newtype State s a = State { runState :: s -> (a, s) }

-- | Implement the `Functor` instance for `State s`.
-- >>> runState ((+1) <$> pure 0) 0
-- (1,0)
instance Functor (State s) where
  (<$>) :: (a -> b) -> State s a -> State s b
  (<$>) f = State . newState . runState 
    where
      {- newState :: (s -> (a,s)) -> s -> (a, s) -}
      newState sf s = let (val, s') = sf s in
                        (f val, s')


-- | Implement the `Apply` instance for `State s`.
-- >>> runState (pure (+1) <*> pure 0) 0
-- (1,0)
--
-- >>> import qualified Prelude as P
-- >>> runState (State (\s -> ((+3), s P.++ ["apple"])) <*> State (\s -> (7, s P.++ ["banana"]))) []
-- (10,["apple","banana"])
instance Apply (State s) where
  (<*>) :: State s (a -> b) -> State s a -> State s b 
  (<*>) sf stateVal = State newState 
    where
      newState st = let fn = fst $ runState sf st
                        (val, state) = runState stateVal st
                    in
                       (fn val, state)



-- | Implement the `Applicative` instance for `State s`.
-- >>> runState (pure 2) 0
-- (2,0)
instance Applicative (State s) where
  pure :: a -> State s a
  pure a = State (\s -> (a, s))

-- | Implement the `Bind` instance for `State s`.
-- >>> runState ((const $ put 2) =<< put 1) 0
-- ((),2)
instance Bind (State s) where
  (=<<) :: (a -> State s b) -> State s a -> State s b
  (=<<) fn st = State newState
    where
      newState s = let (val, s') = runState st s
                       state     = fn val 
                    in
                      runState state s'




instance Monad (State s) where

-- | Run the `State` seeded with `s` and retrieve the resulting state.
--
-- prop> \(Fun _ f) -> exec (State f) s == snd (runState (State f) s)
exec :: State s a -> s -> s
exec st v = snd $ runState st v

-- | Run the `State` seeded with `s` and retrieve the resulting value.
--
-- prop> \(Fun _ f) -> eval (State f) s == fst (runState (State f) s)
eval :: State s a -> s -> a
eval st = fst . (runState st)

-- | A `State` where the state also distributes into the produced value.
--
-- >>> runState get 0
-- (0,0)
get :: State s s
get = State (\s -> (s, s))

-- | A `State` where the resulting state is seeded with the given value.
--
-- >>> runState (put 1) 0
-- ((),1)
put :: s -> State s ()
put seed = State (\_ -> ((), seed))

-- | Find the first element in a `List` that satisfies a given predicate.
-- It is possible that no element is found, hence an `Optional` result.
-- However, while performing the search, we sequence some `Monad` effect through.
--
-- Note the similarity of the type signature to List#find
-- where the effect appears in every return position:
--   find ::  (a ->   Bool) -> List a ->    Optional a
--   findM :: (a -> f Bool) -> List a -> f (Optional a)
--
-- >>> let p x = (\s -> (const $ pure (x == 'c')) =<< put (1+s)) =<< get in runState (findM p $ listh ['a'..'h']) 0
-- (Full 'c',3)
--
-- >>> let p x = (\s -> (const $ pure (x == 'i')) =<< put (1+s)) =<< get in runState (findM p $ listh ['a'..'h']) 0
-- (Empty,8)
findM :: Monad f => (a -> f Bool) -> List a -> f (Optional a)
findM _  Nil       = return Empty
findM fn (x :. xs) = do 
  isTrue <- fn x
  if isTrue then return (Full x)
            else findM fn xs


-- | Find the first element in a `List` that repeats.
-- It is possible that no element repeats, hence an `Optional` result.
--
-- /Tip:/ Use `findM` and `State` with a @Data.Set#Set@.
--
-- newtype State s a = State { runState :: s -> (a, s) }
-- findM :: Monad f => (a -> f Bool) -> List a -> f (Optional a)
-- isMember :: Ord b => b -> State (S.Set b) Bool
--
-- prop> case firstRepeat xs of Empty -> let xs' = hlist xs in nub xs' == xs'; Full x -> length (filter (== x) xs) > 1
-- prop> case firstRepeat xs of Empty -> True; Full x -> let (l, (rx :. rs)) = span (/= x) xs in let (l2, r2) = span (/= x) rs in let l3 = hlist (l ++ (rx :. Nil) ++ l2) in nub l3 == l3
firstRepeat :: Ord a => List a -> Optional a
firstRepeat xs = fst $ runState (findM isMember xs) S.empty where
  isMember :: Ord b => b -> State (S.Set b) Bool
  isMember opt = do 
    set <- get
    if S.member opt set then
      return $ S.member opt set
    else do 
      State (\x -> (False, S.insert opt set))


-- | Remove all duplicate elements in a `List`.
-- /Tip:/ Use `filtering` and `State` with a @Data.Set#Set@.
--
-- prop> firstRepeat (distinct xs) == Empty
--
-- prop> distinct xs == distinct (flatMap (\x -> x :. x :. Nil) xs)
distinct :: Ord a => List a -> List a
distinct xs = fst $ runState (filtering isDuplicate xs) S.empty where
  {- isDuplicate :: Applicative f => a -> f Bool -}
  isDuplicate val = do 
    set <- get
    if S.member val set  then
      return True
    else State (\x -> (False, S.insert val set))


-- | A happy number is a positive integer, where the sum of the square of its digits eventually reaches 1 after repetition.
-- In contrast, a sad number (not a happy number) is where the sum of the square of its digits never reaches 1
-- because it results in a recurring sequence.
--
-- /Tip:/ Use `findM` with `State` and `produce`.
--
-- /Tip:/ Use `join` to write a @square@ function.
--
-- /Tip:/ Use library functions: @Optional#contains@, @Data.Char#digitToInt@.
--
-- >>> isHappy 4
-- False
--
-- >>> isHappy 7
-- True
--
-- >>> isHappy 42
-- False
--
-- >>> isHappy 44
-- True
isHappy :: Integer -> Bool
isHappy i = (contains 1) . fst $ runState (findM stateHappy (sumAllSquares i)) Nil where
    stateHappy :: Integer -> State (List Integer) Bool 
    stateHappy i = do 
      xs <- get
      if i == 1 || elem i xs then
        return True
      else
        State (\x -> (False, i :. xs))

sumAllSquares :: Integer -> List Integer
sumAllSquares = produce sumSquareOfDigits

square :: Int -> Int
square = join (*)

sumSquareOfDigits :: Integer -> Integer
sumSquareOfDigits i = P.toInteger . sum . (map square) $ digits (P.fromIntegral i)

digits :: Int -> List Int
digits = digitsFromInt Nil where
  digitsFromInt :: List Int -> Int -> List Int
  digitsFromInt xs int
    | int == 0          = xs
    | int `mod` 10 == 0 = digitsFromInt (0 :. xs) (int `div` 10)
    | otherwise         = let digit = int `mod` 10 in 
                              digitsFromInt (digit :. xs) ((int - digit) `div` 10)
