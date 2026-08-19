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

module SelectionMonad_ParameterSupport2 where

import Control.Monad (ap, foldM)
import Data.List (group, maximumBy, minimumBy, sort)
import Data.Monoid (Sum (..))
import Prelude hiding (Left, Right, max, min)
import DataDual
deriving instance (Enum a)     => Enum (Sum a)
deriving instance (Real a)     => Real (Sum a)
deriving instance (Integral a) => Integral (Sum a)

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

-- for linearReg function in linear regression exapmle
instance (Monoid r, Functor e) => MonadFail (Sel r e) where
  fail :: (Monoid r, Functor e) => String -> Sel r e a
  fail = undefined

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


handleP :: (Functor f, Functor e, Monoid r) => 
  (f (p -> Sel r e r, p -> Sel r e b) -> p -> Sel r e b) -> p -> Sel r (f :* e) b -> Sel r e b
handleP alg p = handle Handler { 
                    hret = (\p x -> return x) 
                  , hops = alg 
                  } p

reset :: (Functor e, Monoid r) => Sel r e a -> Sel r e a
reset p = Sel $ \ g ->
  let (r, w) = runSelWith p g
  in case w of
    Leaf x -> (mempty, Leaf x)
    Node t -> (mempty, Node (fmap (reset) t))

-- lreset = reset (<e> \x.0)
lreset :: (Functor e, Monoid r) => Sel r e a -> Sel r e a
lreset p = reset $ glocal zeroLC p

---------------------------
-- Examples
---------------------------

-- non-determinism

data NDet r = Decide (Bool -> r) deriving Functor

decide :: (Monoid r, Functor e, NDet :? e) => Sel r e Bool
decide = op (Decide pure) 

ndtp :: (Functor e, Monoid r, NDet :? e) => Sel r e Bool
ndtp = do
    b <- decide
    return (not b) 

nDetAlg :: (Monoid r, Functor e) 
              => NDet ((p -> Sel r e r, p -> Sel r e [a])) -> p -> Sel r e [a]
nDetAlg (Decide k) p = do
  x <- (snd . k) True p
  y <- (snd . k) False p
  return (x ++ y)

hNDet :: (Functor e, Monoid r) => Sel r (NDet :* e) Bool -> Sel r e [Bool]
hNDet = handle Handler { 
                    hret = (\p x -> return [x]) 
                  , hops = nDetAlg 
                  } ()

ndtpResult :: ([Bool], ())
ndtpResult = run $ hNDet ndtp





-- mini, max

data Max c k = Max [c] (c -> k) deriving Functor

max :: (Monoid r, Functor e, Max a :? e) => [a] -> Sel r e a
max lst = op (Max lst pure)

maxWith :: (Monad m, Ord b) 
            => (a -> m b) -> [a] -> m a
maxWith f x = do
  bs <- mapM f x
  -- trace ("maxWith: " ++ show bs) return ()
  let r = maximumBy (\x y -> compare (fst x) (fst y)) $ zip bs [0..]
  -- trace ("r: " ++ show r) return ()
  return $ x !! (snd r)


password :: (Max String :? e, Monoid r, Num r) => Sel r e String
password = do
  s <- max ["aaa", "akane", "aabb", "abc"]
  len s
  distinct s
  return $ "password is " ++ s

len :: (Num r, Monoid r, Functor e) => String -> Sel r e ()
len x = loss (fromIntegral (length x))

distinct :: (Num r, Monoid r, Functor e) => String -> Sel r e ()
distinct x = let i = fromIntegral (length (group (sort x))) in loss (i * i)

maxAlg :: (Ord r, Monoid r, Functor e) 
    => Max c (p -> Sel r e r, p -> Sel r e b) -> p -> Sel r e b
maxAlg (Max c k) p = do
    -- snd . k returns loss value, so the loss info in snd . k has no need and should be silenced
    b <- maxWith (\x -> (fst . k) x p ) c 
    (snd . k) b p

hMax :: forall c r e a. (Monoid r, Ord a, Ord r, Functor e) 
        => Sel r (Max c :* e) a -> Sel r e a
hMax = handleP maxAlg ()

passResult :: (String, (Sum Int))
passResult =  run $ hMax @String password





-- minimax

data Min c k = Min [c] (c -> k) deriving Functor

min :: (Monoid r, Functor e, Min a :? e) => [a] -> Sel r e a
min lst = op (Min lst pure)

minWith :: (Monad m, Ord b) 
           => (a -> m b) -> [a] -> m a
minWith f x = do
  bs <- mapM f x
  -- trace ("minWith: " ++ show bs) return ()
  let r = minimumBy (\x y -> compare (fst x) (fst y)) $ zip bs [0..]
  -- trace ("r: " ++ show r) return ()
  return $ x !! (snd r)

minAlgebra :: forall c r e p a. (Ord r, Monoid r, Functor e) 
              => Min c (p -> Sel r e r, p -> Sel r e a) -> p -> Sel r e a
minAlgebra (Min l k) p = do
  x <- minWith (\x -> (fst . k) x p ) l 
  (snd . k) x p

data Strategy = Left | Right deriving (Show, Eq, Enum, Ord)

hMin :: forall c e r a. (Ord r, Monoid r, Functor e) 
        => Sel r (Min c :* e) a -> Sel r e a
hMin = handleP minAlgebra ()


minimax :: (Functor e) => Sel (Sum Float) e (Strategy, Strategy)
minimax = hMax @Strategy $ hMin @Strategy $ do
            a <- max [Left, Right]
            b <- min [Left, Right]
            loss $ ([5, 3, 2, 9] !! ((fromEnum a) * 2 + (fromEnum b)))
            return (a,b)

minimaxResult :: ((Strategy, Strategy), (Sum Float))
minimaxResult = run minimax





-- nash

getStrtgy :: Step -> Strategy
getStrtgy (Stay x) = x
getStrtgy (Move x) = x

move :: Strategy -> Strategy
move Left =  Right
move Right =  Left

data Step = Move Strategy | Stay Strategy deriving (Eq, Show)

data Play r = Play (Step, Step) ((Step ,Step) -> r) deriving Functor

play :: (Monoid r, Functor e, Play :? e) => (Step, Step) -> Sel r e (Step, Step)
play (a,b) = op (Play (a,b) pure)

isMove :: Step -> Bool
isMove (Move _) = True
isMove _ = False

isStay :: Step -> Bool
isStay (Stay _) = True
isStay _ = False

exampleNash :: (Functor e) 
               => Step -> Step -> Sel (Sum (Float), Sum (Float)) e ((Step,Step))
exampleNash a b = do
  (a', b') <- lreset $ hNash $ do
                (a1, b1) <- play (a,b)
                let (a2, b2) = (getStrtgy a1, getStrtgy b1)
                loss $ fmap Sum $ [(2,2),(0,3),(3,0),(1,1)] 
                                  !! ((fromEnum a2) * 2 + (fromEnum b2))
                return (a1,b1)
  if isStay a' && isStay b' 
    then return (a',b') 
    else exampleNash a' b'

hNash :: (Ord r, Monoid r, Functor e) 
        => Sel (r, r) (Play :* e) a -> Sel (r, r) e a 
hNash = handleP playAlgebra ()

playAlgebra :: (Ord r, Monoid r, Functor e) 
               => Play (p -> Sel (r,r) e (r,r), p -> Sel (r,r) e a) -> p -> Sel (r,r) e a
playAlgebra (Play (s1,s2) k) p = do
    let (a1, b1) = (getStrtgy s1, getStrtgy s2)
        (a2, b2) = (move a1, move b1)
    l1 <- (fst . k) (Stay a1, Stay b1) p
    -- trace ("l1: " ++ show l1) return ()
    l2 <- (fst . k) (Stay a2, Stay b1) p
    -- trace ("l2: " ++ show l2) return ()
    l3 <- (fst . k) (Stay a1, Stay b2) p
    -- trace ("l3: " ++ show l3) return ()
    if (fst l2 < fst l1) -- A make move
      then (snd . k) (Move a2, Stay b1) p
    else if (snd l3 < snd l1) -- B make move
      then (snd . k) (Stay a1, Move b2) p
      else (snd . k) (Stay a1, Stay b1) p
        

nashResult :: ((Step, Step), (Sum Float, Sum Float))
nashResult = run $ exampleNash (Move Right) (Move Right)



-- linear regression

training_n = ((length ldata) * 7 `div` 10 )

training_data = take training_n ldata
validation_data = drop training_n ldata

type Param = DF

-- [effect|data Opt = Opt { optimize :: Op [Param] [Param] } |]
data Opt r = Opt [Param] ([Param] -> r) deriving Functor

optimize :: (Monoid r, Functor e, Opt :? e) => [Param] -> Sel r e [Param]
optimize lst = op (Opt lst pure)

-- [effect|data LR = LR { lrate :: Op () Float } |]
data LR r = LR (Float -> r) deriving Functor

lrate :: (Monoid r, Functor e, LR :? e) => Sel r e Float
lrate = op (LR pure)

gd :: (Functor e, LR :? e) 
      => Sel DF (Opt :* e) a -> Sel DF e a
gd = handleP gdAlgebra ()

gdAlgebra :: (Functor e, LR :? e) => Opt (p -> Sel DF e DF, p -> Sel DF e a) -> p -> Sel DF e a
gdAlgebra (Opt ps k) p = do 
  ds <- autodiff (\x -> (fst . k) x p) ps
  l <- lrate 
  let ps' = zipWith (\w d -> liftDual (primal w - l * d)) ps ds
  (snd . k) ps' p

readLR :: (Show r, Ord r, Monoid r, Functor e) 
          => Float -> Sel r (LR :* e) a -> Sel r e a
readLR alpha = handleP (readLRAlgebra alpha) ()

readLRAlgebra :: (Monoid r, Functor e) => Float -> LR (p -> Sel r e r, p -> Sel r e a) -> p -> Sel r e a
readLRAlgebra alpha (LR k) p = (snd . k) alpha p

linearReg :: (Functor e, Opt :? e) => [DF] -> DF -> DF -> Sel DF e [DF]
linearReg [w,b] datap target = 
  do [w', b'] <- optimize [w, b]
     let output = w' * datap + b'
     loss $ (output - target) * (output - target)
     return [w', b']

random_params :: [DF]
random_params = [0.1, -0.1]

learning :: (Functor e) => Sel DF e [DF]
learning =
  readLR 0.01 $
    foldM (\w (x, y) ->
        lreset $
        gd $
        linearReg w x y
    ) random_params training_data

learningResult :: ([DF], DF)
learningResult = run learning


learningData :: [Float]
learningData = map primal (fst learningResult)



-- -- hyper parameter tuning 

tuneLR :: (Monoid r, Ord r, Functor e) 
          => (Float, Float) -> Sel r (LR :* e) a -> Sel r e (Float, a)
tuneLR (a1, a2) = handle Handler {
                              hret = \p x -> return (a1, x)
                            , hops = alg
                            } () where
    alg :: (Monoid r, Ord r, Functor e) 
          => LR (p -> Sel r e r, p -> Sel r e (Float, a)) -> p -> Sel r e (Float, a)
    alg (LR k) p = do 
      err1 <- (fst . k) a1 p
      err2 <- (fst . k) a2 p
      let a = if err1 < err2 then a1 else a2
      (_, r) <- (snd . k) a p
      return (a, r)
    bind :: (Monoid r, Functor es) 
            => (Float, a) -> (a -> Sel r es (Float, c)) -> Sel r es (Float, c)
    bind (a, x) k = do 
      (_, y) <- k x
      return (a, y)


hyperOptim :: (Functor e) => Sel DF e (Float, [[DF]])
hyperOptim =
  tuneLR (0.01, 0.03) $ do
    alpha <- lrate
    readLR alpha $ do
        params <- foldM (\params (x, y) -> lreset $ gd $ linearReg params x y)
                        random_params training_data
        handleP alg () (mapM (\(x, y) -> linearReg params x y) validation_data) where
          alg (Opt lst k) p = (snd . k) lst p
       
hyperOptimResult :: (Float, DF)
hyperOptimResult = 
  let ((a,_), r) = run $ hyperOptim 
  in (a,r)


-- experiment
experiment :: (Max String :? e) => Sel Float e String
experiment = do
  loss 1
  s <- max ["aaa", "aabb", "abc"]
  return s

exAlgebra :: forall r e p a. (Monoid r, Ord r, Num r, Functor e) 
              => Max String ((p -> Sel r e r, p -> Sel r e a)) -> p -> Sel r e a
exAlgebra (Max [s1, s2, s3] k) p = do
    b <- (fst . k) s1 p
    if (b > 0) 
      then (snd . k) s1 p
      else (snd . k) s2 p

hEx :: forall r e a. (Monoid r, Ord r, Num r, Functor e) 
        => Sel r (Max String :* e) a -> Sel r e a
hEx = handleP exAlgebra ()


exResult :: (String, Float)
exResult =  run $ hEx experiment




-- counterexample for handler parameter

data Prm r = Prm (Int -> r) deriving Functor

cop :: (Monoid r, Functor e, Prm :? e) => Sel r e Int
cop = op (Prm pure) 

cex :: (Functor e, Monoid r, Prm :? e) => Sel r e Int
cex = do cop; cop

cAlg :: (Monoid r, Functor e, Num p, Num r, Integral r) 
              => Prm ((p -> Sel r e r, p -> Sel r e a)) -> p -> Sel r e a
cAlg (Prm k) p = do
  i <- (fst . k) 0 (p+1)
  if (even i)
    then do loss 1
            (snd . k) 0 (p+1)
    else do loss 2
            (snd . k) 0 p

hCex :: (Functor e, Monoid r, Integral r) => Sel r (Prm :* e) Int -> Sel r e Int
hCex = handle Handler { 
                    hret = (\p x -> return x) 
                  , hops = cAlg 
                  } 0

cexResult :: (Int, Sum (Int))
cexResult = run $ hCex cex
  

-- hyperparameter optimization (hadler parameter ver)

gd' :: (Functor e, LR :? e) 
      => Sel DF (Opt :* e) a -> Sel DF e a
gd' sl = do 
	l <- lrate
	handleP gdAlgebra' l sl

gdAlgebra' :: (Functor e, LR :? e) => Opt (Float -> Sel DF e DF, Float -> Sel DF e a) -> Float -> Sel DF e a
gdAlgebra' (Opt ps k) p = do 
  ds <- autodiff (\x -> (fst . k) x p) ps
  let ps' = zipWith (\w d -> liftDual (primal w - p * d)) ps ds
  (snd . k) ps' p

learning' :: (Functor e) => Sel DF e [DF]
learning' =
  readLR 0.01 $
    foldM (\w (x, y) ->
        lreset $
        gd' $
        linearReg w x y
    ) random_params training_data

learningResult' :: ([DF], DF)
learningResult' = run learning'


learningData' :: [Float]
learningData' = map primal (fst learningResult')



hyperOptim' :: (Functor e) => Sel DF e (Float, [[DF]])
hyperOptim' =
  tuneLR (0.01, 0.03) $ do
    alpha <- lrate
    readLR alpha $ do
        params <- foldM (\params (x, y) -> lreset $ gd' $ linearReg params x y)
                        random_params training_data
        handleP alg () (mapM (\(x, y) -> linearReg params x y) validation_data) where
          alg (Opt lst k) p = (snd . k) lst p
       



hyperOptimResult' :: (Float, DF)
hyperOptimResult' = 
  let ((a,_), r) = run $ hyperOptim 
  in (a,r)


