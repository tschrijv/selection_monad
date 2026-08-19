{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-tabs #-}
{-# LANGUAGE DeriveFunctor #-}


module Cliff where

import SelectionMonad_ParameterSupport2
import DataDual
import Data.List (maximumBy)
import Data.Ord (comparing)
import Control.Monad (foldM)

-- ---------------------------------------------------------------------
-- cliff walking（6x3）
-- ---------------------------------------------------------------------
 
type State    = (Int, Int)
type Reward = Float
 
data Action = N | S | E | W deriving (Eq, Ord, Show, Enum, Bounded)
 
actions :: [Action]
actions = [minBound .. maxBound]
 
width, height :: Int
width  = 6
height = 3
 
start, goal :: State
start = (0, 0)
goal  = (5, 0)
 
isGoal :: State -> Bool
isGoal = (== goal)
 
isCliff :: State -> Bool
isCliff (x, y) = y == 0 && x >= 1 && x <= 4
 
cliffStep :: State -> Action -> (Reward, State)
cliffStep (x, y) a =
  let (x1, y1) = case a of
        N -> (x, y + 1); S -> (x, y - 1); E -> (x + 1, y); W -> (x - 1, y)
      s' = (clamp 0 (width - 1) x1, clamp 0 (height - 1) y1)
  in if isCliff s' then (-100, start) else (-1, s')
  where clamp lo hi v | v < lo = lo | v > hi = hi | otherwise = v
 
stateIx :: State -> Int
stateIx (x, y) = y * width + x
 
nStates :: Int
nStates = width * height

-- ---------------------------------------------------------------------
-- hyperparameter
-- ---------------------------------------------------------------------

alpha, gamma, epsilon :: Float
alpha   = 0.5
gamma   = 1.0
epsilon = 0.1

-- ---------------------------------------------------------------------
-- Q-table
-- ---------------------------------------------------------------------

thetaIx :: State -> Action -> Int
thetaIx s a = fromEnum a * nStates + stateIx s

setAt :: Int -> a -> [a] -> [a]
setAt i x xs = take i xs ++ x : drop (i + 1) xs

find_max_reward :: Theta -> Feedback -> Float
find_max_reward th (_, _, _, s')
  | isGoal s' = 0
  | otherwise = maximum [primal (qOf th s' a') | a' <- actions]

update :: Theta -> Float -> Feedback -> Theta
update th max_re (s, a, r, _) =
  let old = primal (qOf th s a)
      new = old + alpha * (r + gamma * max_re - old)
  in setAt (thetaIx s a) (liftDual new) th


type Feedback = (State, Action, Reward, State)

data Agent a = 
    Predict State (Action -> a)
  | FB Feedback (() -> a)
    deriving Functor

predict :: (Agent :? e, Monoid r) => State -> Sel r e Action
predict s = op $ Predict s pure

feedback :: (Agent :? e, Monoid r) => Feedback -> Sel r e ()
feedback fb = op $ FB fb (pure)

data Obsrv a = Obsrv State Action ((Reward, State) -> a) deriving Functor

observe :: (Obsrv :? e, Monoid r) => State -> Action -> Sel r e (Reward, State)
observe s a = op $ Obsrv s a pure

data Rand k = Uniform Float Float (Float -> k) deriving Functor
 
uniform :: (Monoid r, Functor e, Rand :? e) => Float -> Float -> Sel r e Float
uniform lo hi = op (Uniform lo hi pure)



run_episode :: (Monoid r, Agent :? e, Obsrv :? e) => State -> Sel r e State
run_episode s = 
	if isGoal s 
		then return s
		else do
			a <- predict s
			(r,s') <- observe s a
			feedback (s, a, r, s')
			run_episode s'



type Theta = [DF]
 
initTheta :: Theta
initTheta = replicate (nStates * length actions) (liftDual 0)
 
qOf :: Theta -> State -> Action -> DF
qOf th s a = th !! thetaIx s a
 
maxQOf :: Theta -> State -> Float
maxQOf th s = maximum [primal (qOf th s a) | a <- actions]
 
greedyAction :: Theta -> State -> Action
greedyAction th s = maximumBy (comparing (primal . qOf th s)) actions


hAgent :: (Functor e, Monoid r, Rand :? e)
       => Theta -> Sel r (Agent :* e) b -> Sel r e (Theta, b)
hAgent = handle Handler { hret = \p x -> return (p, x)
                        , hops = agentAlg } where
    agentAlg :: (Functor e, Monoid r, Rand :? e)
             => Agent (Theta -> Sel r e r, Theta -> Sel r e a) -> Theta -> Sel r e a
    agentAlg (Predict s k) p = do
        x <- uniform 0 1
        a <- if x < epsilon
               then do i <- uniform 0 (fromIntegral (length actions))
                       return (actions !! (floor i `mod` length actions))
               else return (greedyAction p s)
        (snd . k) a p
    agentAlg (FB fb k) p = do
        let max_re = find_max_reward p fb
            p' = update p max_re fb
        (snd . k) () p'

hObsrv :: (Functor e, Monoid r) => Sel r (Obsrv :* e) b -> Sel r e b
hObsrv = handleP obsAlg () where
    obsAlg :: Obsrv (p -> Sel r e r, p -> Sel r e a) -> p -> Sel r e a
    obsAlg (Obsrv s a k) p = do
        let (re, s') = cliffStep s a
        (snd . k) (re, s') p

hRand :: (Functor e, Monoid r) => Int -> Sel r (Rand :* e) b -> Sel r e b
hRand = handleP randAlg where
    randAlg :: Rand (Int -> Sel r e r, Int -> Sel r e a) -> Int -> Sel r e a
    randAlg (Uniform lo hi k) g =
        let g' = (1103515245 * g + 12345) `mod` 2147483648
            x  = lo + (hi - lo) * fromIntegral g' / 2147483648
        in (snd . k) x g'



episode :: (Functor e, Monoid r, Rand :? e) => Theta -> Sel r e (Theta, State)
episode th = hAgent th (hObsrv (run_episode start))

train :: (Functor e, Monoid r, Rand :? e) => Int -> Theta -> Sel r e Theta
train n th0 = foldM (\th _ -> fmap fst (episode th)) th0 [1 .. n]

learned :: Theta
learned = fst (run (hRand 42 (train 500 initTheta) :: Sel Float VoidEff Theta))

-- ---------------------------------------------------------------------
-- 動作確認
-- ---------------------------------------------------------------------

evalLoss :: Theta -> Float
evalLoss th = go (0 :: Int) start
  where go n s | isGoal s = 0
               | n > 100  = 100
               | otherwise = let (r, s') = cliffStep s (greedyAction th s)
                             in negate r + go (n + 1) s'

showPolicy :: Theta -> String
showPolicy th = unlines
  [ concat [ cell (x, y) | x <- [0 .. width - 1] ] | y <- [height - 1, height - 2 .. 0] ]
  where
    cell s | isGoal s  = " G"
           | isCliff s = " ."
           | otherwise = case greedyAction th s of
               N -> " ^"; S -> " v"; E -> " >"; W -> " <"





