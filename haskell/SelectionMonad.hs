{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE InstanceSigs #-}
module SelectionMonad where

import Control.Monad (ap, foldM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Free (FreeT (FreeT), iterT, wrap, FreeF (Pure, Free), runFreeT, transFreeT, hoistFreeT)
import Control.Monad.Trans.Writer (Writer, runWriter, tell)
import Control.Monad.Writer.Class (listen, censor)
import Data.Monoid (Sum (..))
import Prelude hiding (max, min, Left, Right)
import Data.List ( maximumBy, minimumBy, group, sort )
import DataDual ( DF, primal, liftDual, autodiff, ldata )



infixr 5 :*

data (:*) f g x 
    = LeftEff (f x) 
    | RightEff (g x) 

instance (Functor f, Functor g) => Functor((:*) f g) where
  fmap f (LeftEff l)  = LeftEff (fmap f l)
  fmap f (RightEff r) = RightEff (fmap f r)

-- is `h` in the effect context `e` ?
class (Functor sub, Functor sup) => sub :? sup where 
  inj :: sub a -> sup a
  prj :: sup a -> Maybe (sub a)

instance Functor f => f :? f where 
    inj = id  
    prj = Just

instance {-# OVERLAPPING #-} (Functor f , Functor g) => f :? (f :* g) where 
    inj = LeftEff  
    prj (LeftEff a) = Just a
    prj _           = Nothing
    
instance {-# OVERLAPPABLE #-} (Functor f , Functor g, Functor h, f :? g) 
      => f :? (h :* g) where 
    inj = RightEff . inj
    prj (RightEff a) = prj a
    prj _            = Nothing

data VoidEff cnt deriving Functor

newtype Sel r e a = Sel { _runSel :: (a -> FreeT e (Writer r) ()) -> FreeT e (Writer r) a }

runSel :: (a -> FreeT e (Writer r) ()) -> Sel r e a -> FreeT e (Writer r) a
runSel = flip _runSel

evalFreeT :: (Functor e, Monad m) => (m b -> b) -> (a -> b) -> (e b -> b) -> (FreeT e m a -> b)
evalFreeT malg gen ealg = goM . runFreeT where
  goM = malg . fmap goF
  goF (Pure x) = gen x
  goF (Free t) = ealg (fmap (goM . runFreeT) t)


instance (Functor e, Monoid r) => Functor (Sel r e) where
  fmap f (Sel g) = Sel (\k -> fmap f (g (k . f)))

instance (Functor e, Monoid r) => Applicative (Sel r e) where
  pure = hoist . pure
  (<*>) = ap

instance (Functor e, Monoid r) => Monad (Sel r e) where
  return = pure
  Sel g >>= f = Sel $ \k ->
    let h x = runSel k (f x)
    in g (\x -> h x >>= k) >>= h

-- for linearReg function in linear regression exapmle
instance (Monoid r, Functor e) => MonadFail (Sel r e) where
  fail :: (Monoid r, Functor e) => String -> Sel r e a
  fail = undefined



hoist :: (Functor e, Monoid r) 
  => FreeT e (Writer r) a
  -> Sel r e a
hoist m = Sel $ \_ -> m

loss :: (Functor e, Monoid r) => r -> Sel r e ()
loss r = hoist (lift (tell r))



op' :: (Functor e, Monoid r) => e (Sel r e a) -> Sel r e a
op' t = Sel $ \ g -> wrap (fmap (runSel g) t)

op :: (f :? e, Monoid r) => f (Sel r e a) -> Sel r e a
op = op' . inj


-- eval
run :: Monoid r => Sel r VoidEff a -> (a, r)
run p = runWriter (iterT (\v -> case v of {}) (runSel (\_ -> pure ()) p))

data Handler r f e a b = Handler {
    hret :: a -> Sel r e b,
    hops :: f (Sel r e r, Sel r e b) -> Sel r e b
  }

handle :: (Functor f, Functor e, Monoid r) =>
  Handler r f e a b -> Sel r (f :* e) a -> Sel r e b
handle h p =
    Sel (\ g -> 
      let  go g m = 
             FreeT $ do 
               v <- runFreeT m
               case v of
                   Pure a -> runFreeT (runSel g (hret h a))
                   Free (LeftEff t)  -> 
                     runFreeT (runSel g (hops h (fmap (\ y -> (hoist (triangle (go g y >>= g)), handle h (hoist y))) t)))
                   Free (RightEff e) -> pure (Free (fmap (go g) e))
      in go g (runSel (\ x -> transFreeT RightEff (runSel g (hret h x) >>= g)) p))     
              
handleP :: (Functor f, Functor e, Monoid r) => 
  (f (Sel r e r, Sel r e b) -> Sel r e b) -> Sel r (f :* e) b -> Sel r e b
handleP alg = handle Handler { 
                    hret = (\x -> return x) 
                  , hops = alg 
                  }

-- reset e 
reset :: (Functor e, Monoid r) => Sel r e a -> Sel r e a
reset p = Sel { _runSel = (\ g -> censor (const mempty) (runSel g p)) }
              
-- lreset
-- reset (<e> \x.0)
lreset :: (Functor e, Monoid r) => Sel r e a -> Sel r e a
lreset (Sel sl) = reset $ Sel $ \_ -> sl (\_ -> pure ())
  

-- loss continuationizer ?
triangle :: (Functor e, Monoid r) => FreeT e (Writer r) () -> FreeT e (Writer r) r
triangle p = censor (const mempty) (fmap snd (listen p))
              

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
              => NDet ((Sel r e r, Sel r e [a])) -> Sel r e [a]
nDetAlg (Decide k) = do
  x <- (snd . k) True
  y <- (snd . k) False
  return (x ++ y)

hNDet :: (Functor e, Monoid r) => Sel r (NDet :* e) Bool -> Sel r e [Bool]
hNDet = handle Handler { 
                    hret = (\x -> return [x]) 
                  , hops = nDetAlg 
                  }

ndtpResult :: (Show r, Ord r, Monoid r) => ([Bool], r)
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

maxAlg :: (Ord r, Monoid r, Functor e) => Max c (Sel r e r, Sel r e b) -> Sel r e b
maxAlg (Max c k) = do
    -- snd . k returns loss value, so the loss info in snd . k has no need and should be silenced
    b <- maxWith (fst . k) c
    (snd . k) b

hMax :: forall c r e a. (Monoid r, Ord a, Ord r, Functor e) 
        => Sel r (Max c :* e) a -> Sel r e a
hMax = handleP  maxAlg

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

minAlgebra :: forall c r e a. (Ord r, Monoid r, Functor e) 
              => Min c (Sel r e r, Sel r e a) -> Sel r e a
minAlgebra (Min l k) = do
  x <- minWith (fst . k) l 
  (snd . k) x

data Strategy = Left | Right deriving (Show, Eq, Enum, Ord)

hMin :: forall c e r a. (Ord r, Monoid r, Functor e) 
        => Sel r (Min c :* e) a -> Sel r e a
hMin = handleP minAlgebra 


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
hNash = handleP playAlgebra

playAlgebra :: (Ord r, Monoid r, Functor e) 
               => Play (Sel (r,r) e (r,r), Sel (r,r) e a) -> Sel (r,r) e a
playAlgebra (Play (s1,s2) k) = do
    let (a1, b1) = (getStrtgy s1, getStrtgy s2)
        (a2, b2) = (move a1, move b1)
    l1 <- fst . k $ (Stay a1, Stay b1)
    -- trace ("l1: " ++ show l1) return ()
    l2 <- fst . k $ (Stay a2, Stay b1)
    -- trace ("l2: " ++ show l2) return ()
    l3 <- fst . k $ (Stay a1, Stay b2)
    -- trace ("l3: " ++ show l3) return ()
    if (fst l2 < fst l1) -- A make move
      then (snd . k $ (Move a2, Stay b1))
    else if (snd l3 < snd l1) -- B make move
      then snd . k $ (Stay a1, Move b2)
      else snd . k $ (Stay a1, Stay b1)
        

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
gd = handleP gdAlgebra

gdAlgebra :: (Functor e, LR :? e) => Opt (Sel DF e DF, Sel DF e a) -> Sel DF e a
gdAlgebra (Opt ps k) = do 
  ds <- autodiff (\x -> (fst . k) x) ps
  l <- lrate 
  let ps' = zipWith (\w d -> liftDual (primal w - l * d)) ps ds
  (snd . k) ps'

readLR :: (Show r, Ord r, Monoid r, Functor e) 
          => Float -> Sel r (LR :* e) a -> Sel r e a
readLR alpha = handleP $ readLRAlgebra alpha

readLRAlgebra :: (Monoid r, Functor e) => Float -> LR (Sel r e r, Sel r e a) -> Sel r e a
readLRAlgebra alpha (LR k) = snd . k $ alpha

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



-- hyper parameter tuning 

tuneLR :: (Monoid r, Ord r, Functor e) 
          => (Float, Float) -> Sel r (LR :* e) a -> Sel r e (Float, a)
tuneLR (a1, a2) = handle Handler {
                              hret = \x -> return (a1, x)
                            , hops = alg
                            } where
    alg :: (Monoid r, Ord r, Functor e) 
          => LR (Sel r e r, Sel r e (Float, a)) -> Sel r e (Float, a)
    alg (LR k) = do 
      err1 <- (fst . k) a1
      err2 <- (fst . k) a2
      let a = if err1 < err2 then a1 else a2
      (_, r) <- (snd . k) a
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
        handleP alg (mapM (\(x, y) -> linearReg params x y) validation_data) where
          alg (Opt lst k) = (snd . k) lst
       
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

exAlgebra :: forall r e a. (Monoid r, Ord r, Num r, Functor e) 
              => Max String ((Sel r e r, Sel r e a)) -> Sel r e a
exAlgebra (Max [s1, s2, s3] k) = do
    b <- (fst . k) s1
    if (b > 0) 
      then (snd . k) s1
      else (snd . k) s2

hEx :: forall r e a. (Monoid r, Ord r, Num r, Functor e) 
        => Sel r (Max String :* e) a -> Sel r e a
hEx = handleP exAlgebra


exResult :: (String, Float)
exResult =  run $ hEx experiment



