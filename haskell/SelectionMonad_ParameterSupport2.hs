{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-missing-methods #-}

module SelectionMonadParameterSupport where

import Control.Monad (ap)
import Data.List (group, maximumBy, minimumBy, sort)
import Data.Monoid (Sum (..))
import Prelude hiding (Left, Right, max, min)

-- ---------------------------------------------------------------------
-- Free Monad
-- ---------------------------------------------------------------------

data Free e a
  = Pure a
  | Op (e (Free e a))

instance Functor e => Functor (Free e) where
  fmap f (Pure x) = Pure (f x)
  fmap f (Op t)   = Op (fmap (fmap f) t)

instance (Functor e) => Applicative (Free e) where
  pure x = Pure x
  (<*>) = ap

instance Functor e => Monad (Free e) where
  return = pure

  Pure x >>= k  =  k x
  Op t   >>= k  =  Op (fmap (>>= k) t)

-- ---------------------------------------------------------------------
-- Effect signatures as a sum of functors.
-- ---------------------------------------------------------------------

infixr 5 :*

data (:*) f g x
  = LeftEff (f x)
  | RightEff (g x)

instance (Functor f, Functor g) => Functor ((:*) f g) where
  fmap f (LeftEff l) = LeftEff (fmap f l)
  fmap f (RightEff r) = RightEff (fmap f r)

-- | Is @sub@ present among the effects @sup@?
class (Functor sub, Functor sup) => sub :? sup where
  inj :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)

instance (Functor f) => f :? f where
  inj = id
  prj = Just

instance {-# OVERLAPPING #-} (Functor f, Functor g) => f :? (f :* g) where
  inj = LeftEff
  prj (LeftEff a) = Just a
  prj _ = Nothing

instance
  {-# OVERLAPPABLE #-}
  (Functor f, Functor g, Functor h, f :? g) =>
  f :? (h :* g)
  where
  inj = RightEff . inj
  prj (RightEff a) = prj a
  prj _ = Nothing

data VoidEff cnt deriving (Functor)


-- ---------------------------------------------------------------------
-- Selection Monad.
-- ---------------------------------------------------------------------

data What e a x 
  = Leaf a
  | Node (e x)

instance Functor e => Functor (What e a) where
  fmap f (Leaf x) = Leaf x
  fmap f (Node t) = Node (fmap f t)

newtype Sel r e a = Sel { runSelWith :: (a -> Free e r) -> (r, What e a (Sel r e a)) }

instance Functor e => Functor (Sel r e) where
  fmap f p = Sel (\ g -> let (r, w) = runSelWith p (g . f) in (r, mapWhat f w))

mapWhat :: (Functor e) => (a -> b) -> What e a (Sel r e a) -> What e b (Sel r e b)
mapWhat f (Leaf x) = Leaf (f x)
mapWhat f (Node t) = Node (fmap (fmap f) t)

instance (Functor e, Monoid r) => Applicative (Sel r e) where
  pure x = Sel (\ lc -> (mempty, Leaf x))
  (<*>) = ap

instance (Functor e, Monoid r) => Monad (Sel r e) where
  return = pure

  p >>= k = Sel $ \g ->
    let (r1, w) = runSelWith p (\x -> thenE g (k x))
    in case w of
          Leaf x -> addLoss' r1 (runSelWith (k x) g)
          Node t -> (r1, Node (fmap (>>= k) t))

zeroLC :: (Functor e, Monoid r) => a -> Free e r
zeroLC _ = pure mempty
 
addLoss :: (Functor e, Monoid r) => r -> Sel r e a -> Sel r e a
addLoss r1 p = Sel $ \g ->
  addLoss' r1 (runSelWith p g)

addLoss' :: (Monoid r) => r -> (r, a) -> (r, a)
addLoss' r1 (r2, w) = (r1 <> r2, w)

loss :: (Functor e, Monoid r) => r -> Sel r e ()
loss r = addLoss r (pure ())

-- | an operation call.
opS :: (Functor e, Monoid r) => e (Sel r e a) -> Sel r e a
opS t = Sel $ \ _ -> ( mempty, Node t)
 
op :: (f :? e, Monoid r) => f (Sel r e a) -> Sel r e a
op = opS . inj

-- | Evaluate a closed program (no pending effects) under the canonical
-- zero continuation γ₀ = λ_. η̂(0#).
run :: (Monoid r) => Sel r VoidEff a -> (a, r)
run p = case runSelWith p zeroLC of
  (r, Leaf x) -> (x, r)
  (r, Node t) -> case t of {} 

glocal :: (Functor e, Monoid r) => (a -> Free e r) -> Sel r e a -> Sel r e a
glocal g1 e = Sel $ \ g ->
  case runSelWith e g1 of
    (r, Leaf x) -> (r, Leaf x)
    (r, Node t) -> (r, Node (fmap (glocal g1) t))
 
thenE :: (Functor e, Monoid r) =>  (a -> Free e r) -> Sel r e a -> Free e r
thenE g1 p = 
  case runSelWith p g1 of
    (r, Leaf x) -> fmap (r <>) (g1 x)
    (r, Node t) -> fmap (r <>) (Op (fmap (thenE g1) t))

upE :: (Functor e, Monoid r) => Free e r -> Sel r e r
upE (Pure x) = Sel $ \ g -> (mempty, Leaf x)
upE (Op t)   = Sel $ \ g -> (mempty, Node (fmap upE t))

widen :: (Functor e, Functor f) => 
  Free e a -> Free (f :* e) a
widen (Pure x) = Pure x
widen (Op t)   = Op (RightEff (fmap widen t))

data Handler r f e p a b = Handler
  { hret :: p -> a -> Sel r e b,
    hops :: f (p -> Sel r e r, p -> Sel r e b) -> p -> Sel r e b
 }

handle :: (Functor f, Functor e, Monoid r) =>
  Handler r f e p a b -> p -> Sel r (f :* e) a -> Sel r e b
handle h par p = Sel $ \ g ->
  let (r, w) = runSelWith p (\ a -> widen (thenE g (hret h par a)))
  in case w of
    Leaf x -> addLoss' r (runSelWith (hret h par x) g)
    Node (LeftEff t) ->  addLoss' r
      (runSelWith 
        (hops h 
           (fmap 
              (\ q -> 
                ( \ par' -> upE (thenE g (handle h par' q))
                , \ par' -> glocal g (handle h par' q)  
                )
              )
              t)
          par
        ) g)
    Node (RightEff t) -> (r, Node (fmap (handle h par) t))

reset :: (Functor e, Monoid r) => Sel r e a -> Sel r e a
reset p = Sel $ \ g ->
  let (r, w) = runSelWith p g
  in case w of
    Leaf x -> (mempty, Leaf x)
    Node t -> (mempty, Node (fmap (reset) t))
