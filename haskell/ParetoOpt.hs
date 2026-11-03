{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# OPTIONS_GHC -Wno-tabs #-}
{-# LANGUAGE QuasiQuotes, ExplicitForAll #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}


module ParetoOpt where

import Control.Monad (ap, foldM)
import Data.List (group, maximumBy, minimumBy, sort)
import Data.Monoid (Sum (..))
import Prelude hiding (Left, Right, max, min)
import DataDual ( Float' )
import Debug.Trace (trace)
import SelectionMonad_ParameterSupport2 
import OriginalExamples
import Cliff (qOf)

-- pareto optimization

-- loss value
type Cost = Float'
type Time = Float'
type CT = (Cost, Time)

type Transfer = Float'
type CTT = (Cost, Time, Transfer)


-- types of transportation
data Mode = Bus | Train | Taxi deriving (Show, Eq, Enum)

mode_list :: [Mode]
mode_list = [Bus, Train, Taxi]

-- route
data Node = Start | A | B | C | Goal deriving (Show, Eq, Enum, Bounded)

node_list :: [Node]
node_list = [Start, A, B, C, Goal] 

ct_bus :: [[CT]]
ct_bus = 
    [ [(0,0), (800,60), (0,0),   (1000,90), (0,0)]
    , [(0,0), (0,0),    (600,50),(700,65),  (0,0)]
    , [(0,0), (0,0),    (0,0),   (0,0),     (700,55)]
    , [(0,0), (0,0),    (0,0),   (0,0),     (900,70)]
    , [(0,0), (0,0),    (0,0),   (0,0),     (0,0)]
    ]

ct_train :: [[CT]]
ct_train = 
    [ [(0,0), (1200,25), (0,0),    (0,0),      (0,0)]     -- S -> B not avairable
    , [(0,0), (0,0),     (900,20),(1100,22),   (0,0)]
    , [(0,0), (0,0),     (0,0),   (0,0),       (0,0)]     -- A -> C not avairable
    , [(0,0), (0,0),     (0,0),   (0,0),       (1000,18)]
    , [(0,0), (0,0),     (0,0),   (0,0),       (0,0)]
    ]

ct_taxi :: [[CT]]
ct_taxi = 
    [ [(0,0), (3000,20), (0,0),    (3500,25), (0,0)]
    , [(0,0), (0,0),     (2500,15),(2800,18), (0,0)]
    , [(0,0), (0,0),     (0,0),    (0,0),     (2200,12)]
    , [(0,0), (0,0),     (0,0),    (0,0),     (2600,16)]
    , [(0,0), (0,0),     (0,0),    (0,0),     (0,0)]
    ]

matrixOf :: Mode -> [[CT]]
matrixOf Bus   = ct_bus
matrixOf Train = ct_train
matrixOf Taxi  = ct_taxi

loss_CT :: (Functor e) => Node -> Mode -> Node -> Sel CT e ()
loss_CT n1 m n2 = loss $ onePathLoss n1 (m, n2)

-- calculate loss for the given path
pathLoss :: [(Mode, Node)] -> CT
pathLoss path = go Start (reverse path)
  where
    go :: Node -> [(Mode, Node)] -> CT
    go _    []                = (0, 0)
    go from ((m, to) : rest) =
      let (c, t)   = onePathLoss from (m, to)
          (cs, ts) = go to rest
      in (c + cs, t + ts)

onePathLoss :: Node -> (Mode,Node) -> CT
onePathLoss from (mode, to) = matrixOf mode !! fromEnum from !! fromEnum to

addCT :: CT -> CT -> CT
addCT (a, b) (c, d) = (a + c, b + d)

-- calculate possible next nodes
candidatesFrom :: Node -> [(Mode, Node)]
candidatesFrom n =
  [ (m, n')
  | m  <- mode_list
  , n' <- node_list
  , let w = matrixOf m !! fromEnum n !! fromEnum n'
  , w /= (0, 0)
  ]




-- effect 
-- pick next node given current node
data Pareto m n k = Pareto n ((m, n) -> k) deriving Functor

pareto :: (Monoid r, Functor e, Pareto Mode Node :? e) => Node -> Sel r e (Mode, Node)
pareto node = op (Pareto node pure)


-- one step of choosing next node
step :: (Functor e, Pareto Mode Node :? e) => Node -> Sel CT e (Mode, Node)
step node = do
  (mode, next) <- pareto node
  loss_CT node mode next
  return (mode, next)



walk_greedy :: (Functor e) 
    => [(Mode, Node)] 
    -> Node 
    -> ([(Mode, Node)] -> Sel CT (Pareto Mode Node :* e) (Mode, Node) -> Sel CT e (Mode, Node)) 
    -> Sel CT e [(Mode, Node)]
walk_greedy path current handler = do
  (mode, next) <- lreset $ handler path (step current)
  if (next == Goal)
      then return ((mode, next) : path)
      else walk_greedy ((mode, next) : path) next handler

walk :: (Functor e, Pareto Mode Node :? e) => [(Mode, Node)] -> Node -> Sel CT e [(Mode, Node)]
walk path current = do
    (mode, next) <- step current
    if (next == Goal)
        then return ((mode, next) : path)
        else walk ((mode, next) : path) next




-------------
-- best cost 
-------------
hCost :: (Functor e) => [(Mode, Node)] -> Sel CT (Pareto Mode Node :* e) a -> Sel CT e a
hCost p = handleP costAlg p 

costAlg :: (Functor e) 
        => Pareto Mode Node (([(Mode, Node)] -> Sel CT e CT, [(Mode, Node)] -> Sel CT e a)) 
        -> [(Mode, Node)]
        -> Sel CT e a
costAlg (Pareto node k) path = do
  x <- minWith (\c -> (fst . k) c path) (candidatesFrom node)
--   trace ("pareto: " ++ show x) return ()
  (snd . k) x path



greedyCost :: ([(Mode, Node)], CT)
greedyCost = run (walk_greedy [] Start hCost)

optimalCost :: ([(Mode, Node)], CT)
optimalCost = run (hCost [] (walk [] Start))



-------------
-- best time 
-------------
hTime :: (Functor e) => [(Mode, Node)] -> Sel CT (Pareto Mode Node :* e) a -> Sel CT e a
hTime p = handleP timeAlg p 

timeAlg :: (Functor e) 
        => Pareto Mode Node (([(Mode, Node)] -> Sel CT e CT, [(Mode, Node)] -> Sel CT e a)) 
        -> [(Mode, Node)]
        -> Sel CT e a
timeAlg (Pareto node k) path = do
  x <- minWith (\c -> fmap (\(c,t) -> (t,c)) ((fst . k) c path)) (candidatesFrom node)
--   trace ("pareto: " ++ show x) return ()
  (snd . k) x path

greedyTime :: ([(Mode, Node)], CT)
greedyTime = run (walk_greedy [] Start hTime)

optimalTime :: ([(Mode, Node)], CT)
optimalTime = run (hTime [] (walk [] Start))



-- -- optimal
-- -- path is updated
-- hOptimal :: (Functor e) => [(Mode, Node)] -> Sel CT (Pareto Mode Node :* e) a -> Sel CT e a
-- hOptimal p = handleP optimalAlg  p 

-- optimalAlg  :: (Functor e) 
--         => Pareto Mode Node (([(Mode, Node)] -> Sel CT e CT, [(Mode, Node)] -> Sel CT e a)) 
--         -> [(Mode, Node)]
--         -> Sel CT e a
-- optimalAlg  (Pareto node k) path= do
--   x <- minWith (\c -> loss (pathLoss path) >> (fst . k) c path) (candidatesFrom node)
--   trace ("pareto: " ++ show x ++ " pass: " ++ show path) return ()
--   (snd . k) x (x : path)





-------------------------------------------
-- time is money
-------------------------------------------

hTM :: (Functor e) => Float' -> Sel CT (Pareto Mode Node :* e) a -> Sel CT e a
hTM rate = handleP tmAlg rate 

tmAlg :: (Functor e) 
        => Pareto Mode Node ((Float' -> Sel CT e CT, Float' -> Sel CT e a)) 
        -> Float'
        -> Sel CT e a
tmAlg (Pareto node k) rate = do
  x <- minWith (\c -> do
            (c,t) <- (fst . k) c rate
            return $ c + t * rate) 
        (candidatesFrom node)
  (snd . k) x rate

tmResult :: Float' -> ([(Mode, Node)], CT)
tmResult rate = run (hTM rate (walk [] Start))


-------------------------------------------
-- the least times of transfer is the best
-------------------------------------------

-- hTransfer :: (Functor e) => Int -> Sel CT (Pareto Mode Node :* e) a -> Sel CT e a
-- hTransfer t = handleP transAlg t 

-- transAlg :: (Functor e) 
--         => Pareto Mode Node ((Int -> Sel CT e CT, Int -> Sel CT e a)) 
--         -> Int
--         -> Sel CT e a
-- transAlg (Pareto node k) trans = do
--   x <- minWith (\c -> _) (candidatesFrom node)
--   trace ("pareto: " ++ show x) return ()
--   (snd . k) x (trans + 1)

-- transferResult :: ([(Mode, Node)], CT)
-- transferResult = run (hTransfer 0 (walk [] Start))


-------------------------------
-- best cost with time cut-off
-------------------------------

hCutOff :: (Functor e) => Float' -> CT -> Sel CT (Pareto Mode Node :* e) a -> Sel CT e a
hCutOff co p = handleP (cutoffAlg co) p

cutoffAlg :: (Functor e)
    => Cost
    -> Pareto Mode Node ((CT -> Sel CT e CT, CT -> Sel CT e a))
    -> CT -> Sel CT e a
cutoffAlg co (Pareto node k) past = do
  x <- minWith (\c -> do
        let past' = addCT past (onePathLoss node c)  
        future <- (fst . k) c past' 
        return (score co (addCT past future))
            )
            (candidatesFrom node)
  (snd . k) x (addCT past (onePathLoss node x))

-- if time fit in the cut-off, compare with cost,
-- otherwise with time (not chosen unless there is no route that fit in the cut-off anyway)
score :: Cost -> CT -> (Int, Float')
score dl (c, t) | t <= dl   = (0, c) 
                | otherwise = (1, t)

cutoffResult :: Float' -> ([(Mode, Node)], CT)
cutoffResult co = run (hCutOff co (0, 0) (walk [] Start))


-- pareto frontier









