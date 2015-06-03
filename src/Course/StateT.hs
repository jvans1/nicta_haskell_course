{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE OverloadedStrings #-}

module Course.StateT where

import Course.Core
import Course.Id
import Course.Optional
import Course.List
import Course.Functor
import Course.Apply
import Course.Applicative
import Course.Bind
import Course.Monad
import Course.State
import qualified Data.Set as S
import qualified Prelude as P

-- $setup
-- >>> import Test.QuickCheck
-- >>> import qualified Prelude as P(fmap)
-- >>> instance Arbitrary a => Arbitrary (List a) where arbitrary = P.fmap listh arbitrary

-- | A `StateT` is a function from a state value `s` to a functor f of (a produced value `a`, and a resulting state `s`).
newtype StateT s f a = StateT { runStateT :: s -> f (a, s) }

-- | Implement the `Functor` instance for @StateT s f@ given a @Functor f@.
--
-- >>> runStateT ((+1) <$> (pure 2) :: StateT Int List Int) 0
-- [(3,0)]
instance Functor f => Functor (StateT s f) where
  (<$>) :: (a -> b) -> StateT s f a -> StateT s f b
  (<$>) f sa = StateT newState where
    newState s1 = (\(x, y) -> (f x, y)) <$> runStateT sa s1

-- | Implement the `Apply` instance for @StateT s f@ given a @Bind f@.
--
-- >>> runStateT (pure (+2) <*> ((pure 2) :: StateT Int List Int)) 0
-- [(4,0)]
--
-- >>> import qualified Prelude as P
-- >>> runStateT (StateT (\s -> Full ((+2), s P.++ [1])) <*> (StateT (\s -> Full (2, s P.++ [2])))) [0]
-- Full (4,[0,1,2])
--
-- >>> runStateT (StateT (\s -> ((+2), s P.++ [1]) :. ((+3), s P.++ [1]) :. Nil) <*> (StateT (\s -> (2, s P.++ [2]) :. Nil))) [0]
-- [(4,[0,1,2]),(5,[0,1,2])]
instance Bind f => Apply (StateT s f) where
  (<*>) :: StateT s f (a -> b) -> StateT s f a -> StateT s f b
  (<*>) s1 s2 = StateT $ \state -> do 
    (fn, state2) <- runStateT s1 state 
    fstFunc fn <$> runStateT s2 state2 where
      fstFunc fn1 (x, y) = (fn1 x, y)

-- | Implement the `Applicative` instance for @StateT s f@ given a @Applicative f@.
--
-- >>> runStateT (pure 2) 0
-- (2,0)
--
-- >>> runStateT ((pure 2) :: StateT Int List Int) 0
-- [(2,0)]
instance Monad f => Applicative (StateT s f) where
  pure :: a -> StateT s f a
  pure v =  StateT (\s -> pure (v, s) )

-- | Implement the `Bind` instance for @StateT s f@ given a @Monad f@.
--   Make sure the state value is passed through in `bind`.
--
-- newtype StateT s f a = StateT { runStateT :: s -> f (a, s) }
-- >>> runStateT ((const $ putT 2) =<< putT 1) 0
-- ((),2)
instance Monad f => Bind (StateT s f) where
  (=<<) :: (a -> StateT s f b) -> StateT s f a -> StateT s f b
  (=<<) stfn st = StateT $ \state ->
    (runStateT st state) >>= (\(x, y) -> (runStateT (stfn x) state))

instance Monad f => Monad (StateT s f) where

-- | A `State'` is `StateT` specialised to the `Id` functor.
type State' s a = StateT s Id a

-- | Provide a constructor for `State'` values
--
-- >>> runStateT (state' $ runState $ put 1) 0
-- Id ((),1)
state' :: (s -> (a, s)) -> State' s a
state' fn = StateT $ return <$> fn

-- | Provide an unwrapper for `State'` values.
--
-- >>> runState' (state' $ runState $ put 1) 0
-- ((),1)
runState' :: State' s a -> s -> (a, s)
runState' st = runId . (runStateT st)

-- | Run the `StateT` seeded with `s` and retrieve the resulting state.
execT :: Functor f => StateT s f a -> s -> f s
execT st seed = snd <$> runStateT st seed

-- | Run the `State` seeded with `s` and retrieve the resulting state.
exec' :: State' s a -> s -> s
exec' st = runId . (execT st)

-- | Run the `StateT` seeded with `s` and retrieve the resulting value.
evalT :: Functor f => StateT s f a -> s -> f a
evalT st seed = fst <$> runStateT st seed

-- | Run the `State` seeded with `s` and retrieve the resulting value.
eval' :: State' s a -> s -> a
eval' st = runId . (evalT st)

-- | A `StateT` where the state also distributes into the produced value.
--
-- newtype StateT s f a = StateT { runStateT :: s -> f (a, s) }
-- >>> (runStateT (getT :: StateT Int List Int) 3)
-- [(3,3)]
getT :: Monad f => StateT s f s
getT = StateT (\s -> return (s, s))

-- | A `StateT` where the resulting state is seeded with the given value.
--
-- >>> runStateT (putT 2) 0
-- ((),2)
--
-- >>> runStateT (putT 2 :: StateT Int List ()) 0
-- [((),2)]
putT :: Monad f => s -> StateT s f ()
putT s = StateT (\_ -> return ((), s) )

-- | Remove all duplicate elements in a `List`.
--
-- /Tip:/ Use `filtering` and `State'` with a @Data.Set#Set@.
--
-- prop> distinct' xs == distinct' (flatMap (\x -> x :. x :. Nil) xs)
distinct' :: (Ord a, Num a) => List a -> List a
distinct' xs = eval' (filtering isStateMember xs) S.empty where

isStateMember ::(Ord b, Num b) => b -> State' (S.Set b) Bool
isStateMember opt = do
  set <- getT
  if S.member opt set then
    return False
  else do 
    StateT (\_ -> Id (True, S.insert opt set) )

-- | Remove all duplicate elements in a `List`.
-- However, if you see a value greater than `100` in the list,
-- abort the computation by producing `Empty`.
--
-- /Tip:/ Use `filtering` and `StateT` over `Optional` with a @Data.Set#Set@.
--
-- >>> distinctF $ listh [1,2,3,2,1]
-- Full [1,2,3]
--
--
-- >>> distinctF $ listh [1,2,3,2,1,101]
-- Empty
type StateOptional a b = StateT (S.Set a) Optional b
distinctF :: (Ord a, Num a) => List a -> Optional (List a)
distinctF xs = evalT (filtering isOptionalMember xs) S.empty
isOptionalMember :: (Ord b, Num b) =>  b -> StateOptional b Bool
isOptionalMember val = do
  set <- getT
  if val > 100 then StateT (\_ -> Empty)
               else StateT (\_ -> Full (not (S.member val set), S.insert val set))
               -- newtype StateT s f a = StateT { runStateT :: s -> f (a, s) }
--

-- | An `OptionalT` is a functor of an `Optional` value.
data OptionalT f a = OptionalT {
    runOptionalT :: f (Optional a)
  }

-- | Implement the `Functor` instance for `OptionalT f` given a Functor f.
--
-- >>> runOptionalT $ (+1) <$> OptionalT (Full 1 :. Empty :. Nil)
-- [Full 2,Empty]
instance Functor f => Functor (OptionalT f) where
  (<$>) f opt = OptionalT $ (\x -> f <$> x) <$> (runOptionalT opt)

-- | Implement the `Apply` instance for `OptionalT f` given a Apply f.
-- >>> runOptionalT $ OptionalT (Full (+1) :. Full (+2) :. Nil) <*> OptionalT (Full 1 :. Empty :. Nil)
-- [Full 2,Empty,Full 3,Empty]
instance Apply f => Apply (OptionalT f) where
  (<*>) ffn fa = OptionalT $ (\x y -> x <*> y) <$> (runOptionalT ffn) <*> (runOptionalT fa)

-- | Implement the `Applicative` instance for `OptionalT f` given a Applicative f.
instance Applicative f => Applicative (OptionalT f) where
  pure v = OptionalT . pure $ pure v

-- | Implement the `Bind` instance for `OptionalT f` given a Monad f.
--
--
--  runOptionalT :: f (Optional a)
-- >>> runOptionalT $ (\a -> OptionalT (Full (a+1) :. Full (a+2) :. Nil)) =<< OptionalT (Full 1 :. Empty :. Nil)
-- [Full 2,Full 3,Empty]
instance Monad f => Bind (OptionalT f) where
  (=<<) f ma = OptionalT $ runOptionalT ma >>= go  where
    go (Full a) = runOptionalT $ f a
    go Empty    = return Empty

instance Monad f => Monad (OptionalT f) where

-- | A `Logger` is a pair of a list of log values (`[l]`) and an arbitrary value (`a`).
data Logger l a = Logger (List l) a deriving (Eq, Show)

-- | Implement the `Functor` instance for `Logger
--
-- >>> (+3) <$> Logger (listh [1,2]) 3
-- Logger [1,2] 6
instance Functor (Logger l) where
  (<$>) f (Logger xs a) = Logger xs (f a)

-- | Implement the `Apply` instance for `Logger`.
--
-- >>> Logger (listh [1,2]) (+7) <*> Logger (listh [3,4]) 3
-- Logger [1,2,3,4] 10
instance Apply (Logger l) where
  (<*>) (Logger xs1 f) (Logger xs2 a) = Logger (xs1 ++ xs2) (f a)

-- | Implement the `Applicative` instance for `Logger`.
--
-- >>> pure "table" :: Logger Int P.String
-- Logger [] "table"
instance Applicative (Logger l) where
  pure = Logger Nil

-- | Implement the `Bind` instance for `Logger`.
-- The `bind` implementation must append log values to maintain associativity.
--
-- >>> (\a -> Logger (listh [4,5]) (a+3)) =<< Logger (listh [1,2]) 3
-- Logger [1,2,4,5] 6
instance Bind (Logger l) where
  (=<<) f (Logger xs i) = (Logger xs id) <*> f i

instance Monad (Logger l) where

-- | A utility function for producing a `Logger` with one log value.
--
-- >>> log1 1 2
-- Logger [1] 2
log1 :: l -> a -> Logger l a
log1 =
  error "todo148"

-- | Remove all duplicate integers from a list. Produce a log as you go.
-- If there is an element above 100, then abort the entire computation and produce no result.
-- However, always keep a log. If you abort the computation, produce a log with the value,
-- "aborting > 100: " followed by the value that caused it.
-- If you see an even number, produce a log message, "even number: " followed by the even number.
-- Other numbers produce no log message.
--
-- /Tip:/ Use `filtering` and `StateT` over (`OptionalT` over `Logger` with a @Data.Set#Set@).
--
-- >>> distinctG $ listh [1,2,3,2,6]
-- Logger ["even number: 2","even number: 2","even number: 6"] (Full [1,2,3,6])
--
-- >>> distinctG $ listh [1,2,3,2,6,106]
-- Logger ["even number: 2","even number: 2","even number: 6","aborting > 100: 106"] Empty
distinctG ::
  (Integral a, Show a) =>
  List a
  -> Logger Chars (Optional (List a))
distinctG =
  error "todo148"
