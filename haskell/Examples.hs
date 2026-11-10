{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

-- | A port of the repo-root @Examples.hs@ (written against @Control.Mp.Sel@
-- \/ "Sel.hs", this project's original multi-prompt-delimited-continuation
-- implementation) onto our own implementation ("EffectTH.hs" \/
-- "SelectionMonad_ParameterSupport2.hs"). GHC's TH staging restriction
-- requires this to live in a different module from "EffectTH.hs" itself,
-- which is why it lives here rather than being folded into that file.
--
-- Three kinds of change were needed everywhere, mechanically:
--
--   1. Every handler definition @Eff { field = operation (...) }@ becomes
--      @Eff (operation (...))@ -- positional constructor application
--      instead of record syntax. See "EffectTH.hs"'s module header for why
--      record syntax is not available under our dispatch (the same
--      \"decide\" double-duty issue prototype.tex sec:interface now
--      documents).
--
--   2. Every effect-membership constraint @(Eff :? e)@\/@(Eff :* e)@
--      becomes @(Eff_F :? e)@\/@(Eff_F :* e)@: our quasiquoter generates a
--      separate dispatch FUNCTOR @Eff_F@ (one constructor per operation
--      field, found structurally via @(:?)@\/@op@), distinct from the
--      handler-definition record type @Eff@ itself (whose fields hold
--      'operation' clauses) -- Sel.hs's own @Eff@ plays both roles at
--      once, via its marker\/prompt-based dispatch instead of a
--      structural functor. @hmax \@String@-style explicit
--      'Data.Typeable.TypeApplications' are correspondingly unnecessary:
--      our dispatch functor's own type argument is always determined by
--      ordinary unification against the program it's applied to, with no
--      existential hiding the way Sel.hs's runtime 'Marker' search needs.
--
--   3. The repo-root file's very first example ('program'\/'example')
--      hand-writes its own @NDet p r e ans@ datatype directly against
--      Sel.hs's low-level @Op a b c r e ans@ shape (bypassing its OWN
--      @effect@ quasiquoter entirely). There is no equivalent low-level
--      @Op@ type to hand-write against here -- our @Op I O@ only exists
--      inside an @[effect| ... |]@ block, which 'EffectTH.genEffect'
--      expands into the dispatch functor\/handler-definition pair itself.
--      So this one example is ported through the quasiquoter instead
--      (exactly as "Section4Example.hs" already does for the same
--      NDet\/decide example from prototype.tex sec:interface).
--
-- One genuine gap: the linear-regression\/GAN examples read a dataset
-- @ldata@ via @import Data (ldata)@, but no such module or dataset exists
-- ANYWHERE in this repository (confirmed: @Data.hs@ does not exist, and
-- "OriginalExamples.hs" -- a separate, independent port living alongside
-- this one -- references the exact same undefined @ldata@ without
-- defining it either). A small synthetic placeholder dataset
-- ('syntheticData', points near @y = 2x + 1@ with light noise) is
-- substituted below, clearly marked, purely so 'learning'\/'hyperOptim'\/
-- 'gan' can actually run end-to-end rather than being untested dead code.
module Examples where

import Prelude hiding (max, min, Left, Right)
import Control.Monad (foldM)
import Data.List (group, maximumBy, minimumBy, sort)
import DataDual
import Debug.Trace (trace)
import EffectTH
import SelectionMonad_ParameterSupport2

-- ---------------------------------------------------------------------
-- The prototype.tex sec:interface worked example (NDet\/decide), ported
-- through our real @effect@ quasiquoter -- see point 3 in the module
-- header above for why this differs from the repo-root file's own
-- hand-written @NDet p r e ans@ datatype.
-- ---------------------------------------------------------------------

[effect|data NDet = NDet { decide :: Op () Bool } |]

program :: (NDet_F :? e, Monoid r) => Sel r e Bool
program = do
  x <- perform decide ()
  return (not x)

example :: Sel () VoidEff [Bool]
example =
  handlerRet
    (\x -> return [x])
    (NDet (operation (\x lk k -> (++) <$> k True <*> k False)))
    program

-- ---------------------------------------------------------------------
-- Greedy algorithms
-- ---------------------------------------------------------------------

[effect|data Max a = Max { max :: Op [a] a } |]

maxWith :: (Monad m, Show b, Ord b) => (a -> m b) -> [a] -> m a
maxWith f x = do
  bs <- mapM f x
  trace ("maxWith: " ++ show bs) return ()
  let r = maximumBy (\p q -> compare (fst p) (fst q)) $ zip bs [0 ..]
  trace ("r: " ++ show r) return ()
  return $ x !! snd r

hmax :: forall b r e a. (Monoid r, Ord r, Show r, Functor e) => Sel r (Max_F b :* e) a -> Sel r e a
hmax = handler (Max (operation (\p l k -> do b <- maxWith l p; k b)))

len :: (Num r, Monoid r, Functor e) => String -> Sel r e ()
len x = loss (fromIntegral (length x))

distinct :: (Num r, Monoid r, Functor e) => String -> Sel r e ()
distinct x = let i = fromIntegral (length (group (sort x))) in loss (i * i)

pgm :: (Max_F String :? e, Monoid r, Num r) => Sel r e String
pgm = do
  s <- perform max ["aaa", "aabb", "abc"]
  len s
  distinct s
  return $ "hello " ++ s

test1 :: String
test1 = runSel (hmax @String pgm :: Sel Float VoidEff String)

-- ---------------------------------------------------------------------
-- Minimax
-- ---------------------------------------------------------------------

[effect|data Min a = Min { min :: Op [a] a } |]

minWith :: (Monad m, Ord b) => (a -> m b) -> [a] -> m a
minWith f x = do
  bs <- mapM f x
  let r = minimumBy (\p q -> compare (fst p) (fst q)) $ zip bs [0 ..]
  return $ x !! snd r

hmin :: forall b r e a. (Monoid r, Ord r, Functor e) => Sel r (Min_F b :* e) a -> Sel r e a
hmin = handler (Min (operation (\p l k -> do b <- minWith l p; k b)))

pgmMin :: (Min_F String :? e, Monoid r, Num r) => Sel r e String
pgmMin = do
  s <- perform min ["aaa", "aabb", "abc"]
  len s
  distinct s
  return $ "hello " ++ s

test2 :: String
test2 = runSel (hmin @String pgmMin :: Sel Float VoidEff String)

data Strategy = SLeft | SRight deriving (Show, Eq, Enum)

minimax :: (Max_F Strategy :? e, Min_F Strategy :? e, Num r, Monoid r) => Sel r e (Strategy, Strategy)
minimax = do
  a <- perform max [SLeft, SRight]
  b <- perform min [SLeft, SRight]
  let i = [5, 3, 2, 9] !! (fromEnum a * 2 + fromEnum b)
  loss (fromIntegral i)
  return (a, b)

test3 :: (Strategy, Strategy)
test3 = runSel (hmax @Strategy (hmin @Strategy minimax) :: Sel Float VoidEff (Strategy, Strategy))

-- ---------------------------------------------------------------------
-- Nash equilibrium
-- ---------------------------------------------------------------------

getStrtgy :: Step -> Strategy
getStrtgy (Stay x) = x
getStrtgy (Move x) = x

move :: Strategy -> Strategy
move SLeft = SRight
move SRight = SLeft

data Step = Move Strategy | Stay Strategy deriving (Eq, Show)

[effect|data Play = Play { play :: Op (Step, Step) (Step, Step) } |]

isStay :: Step -> Bool
isStay (Stay _) = True
isStay _ = False

hNash :: (Ord r, Monoid r, Show r, Functor e) => Sel (r, r) (Play_F :* e) a -> Sel (r, r) e a
hNash = handler
  ( Play
      ( operation
          ( \(a, b) l k -> do
              let (a1, b1) = (getStrtgy a, getStrtgy b)
              let (a2, b2) = (move a1, move b1)
              l1 <- l (Stay a1, Stay b1)
              l2 <- l (Stay a2, Stay b1)
              l3 <- l (Stay a1, Stay b2)
              if fst l2 < fst l1
                then k (Move a2, Stay b1)
                else
                  if snd l3 < snd l1
                    then k (Stay a1, Move b2)
                    else k (Stay a1, Stay b1)
          )
      )
  )

game :: Functor e => Step -> Step -> Sel (Float, Float) e (Step, Step)
game a b = do
  (a', b') <- lreset (hNash (do
        (a1, b1) <- perform play (a, b)
        let (a2, b2) = (getStrtgy a1, getStrtgy b1)
        loss ([(3, 3), (0, 5), (5, 0), (1, 1)] !! (fromEnum a2 * 2 + fromEnum b2))
        return (a1, b1)))
  if isStay a' && isStay b'
    then return (a', b')
    else lreset (game a' b')

test4 :: (Step, Step)
test4 = runSel (game (Move SRight) (Move SRight) :: Sel (Float, Float) VoidEff (Step, Step))

add_up :: Monoid r => (r, r) -> r
add_up (x, y) = mappend x y

hCoop :: (Ord r, Monoid r, Show r, Functor e) => Sel (r, r) (Play_F :* e) a -> Sel (r, r) e a
hCoop = handler
  ( Play
      ( operation
          ( \(a, b) l k -> do
              let (a1, b1) = (getStrtgy a, getStrtgy b)
              let (a2, b2) = (move a1, move b1)
              l1 <- l (Stay a1, Stay b1)
              l2 <- l (Stay a2, Stay b1)
              l3 <- l (Stay a1, Stay b2)
              if add_up l2 < add_up l1
                then k (Move a2, Stay b1)
                else
                  if add_up l3 < add_up l1
                    then k (Stay a1, Move b2)
                    else k (Stay a1, Stay b1)
          )
      )
  )

game2 :: Functor e => Step -> Step -> Sel (Float, Float) e (Step, Step)
game2 a b = do
  (a', b') <- lreset (hCoop (do
        (a1, b1) <- perform play (a, b)
        let (a2, b2) = (getStrtgy a1, getStrtgy b1)
        loss ([(3, 3), (0, 5), (5, 0), (1, 1)] !! (fromEnum a2 * 2 + fromEnum b2))
        return (a1, b1)))
  if isStay a' && isStay b'
    then return (a', b')
    else lreset (game a' b')

test5 :: (Step, Step)
test5 = runSel (game2 (Move SRight) (Move SRight) :: Sel (Float, Float) VoidEff (Step, Step))

-- ---------------------------------------------------------------------
-- Linear regression
--
-- NOT a genuine gap in our port: `ldata` (the repo-root Examples.hs's own
-- training set, via `import Data (ldata)`) does not exist anywhere in
-- this repository at all -- `Data.hs` is not present, and the only other
-- reference to `ldata` (in "OriginalExamples.hs") is equally undefined
-- there. `syntheticData` below is a stand-in, clearly not from the
-- original, so `learning`\/`hyperOptim`\/`gan` can run end-to-end.
-- ---------------------------------------------------------------------

syntheticData :: [(DF, DF)]
syntheticData =
  [ (liftDual x, liftDual (2 * x + 1 + n))
    | (x, n) <- zip [0, 0.5 .. 9.5] (cycle [0.05, -0.05, 0.02, -0.03, 0.01])
  ]

training_n :: Int
training_n = length syntheticData * 7 `div` 10

training_data, validation_data :: [(DF, DF)]
training_data = take training_n syntheticData
validation_data = drop training_n syntheticData

type Param = DF

[effect|data Opt = Opt { optimize :: Op [Param] [Param] } |]

gd :: (LR_F :? e, Functor e) => Sel DF (Opt_F :* e) a -> Sel DF e a
gd = handler
  ( Opt
      ( operation
          ( \params lk k -> do
              ds <- autodiff lk params
              l <- perform lrate ()
              let params' = zipWith (\w d -> liftDual (primal w - l * d)) params ds
              k params'
          )
      )
  )

[effect|data LR = LR { lrate :: Op () Float } |]

readLR :: (Monoid m, Functor e) => Float -> Sel m (LR_F :* e) a -> Sel m e a
readLR alpha = handler (LR (operation (\_ _ k -> k alpha)))

linearReg :: (Opt_F :? e, Functor e) => [DF] -> DF -> DF -> Sel DF e [DF]
linearReg [w, b] datap target = do
  [w', b'] <- perform optimize [w, b]
  let output = w' * datap + b'
  loss ((output - target) * (output - target))
  return [w', b']

random_params :: [DF]
random_params = [0.1, -0.1]

learning :: [Param]
learning =
  runSel
    ( readLR
        0.01
        ( foldM
            (\w (x, y) -> lreset (gd (linearReg w x y)))
            random_params
            training_data
        ) ::
        Sel DF VoidEff [Param]
    )

learningData :: [Float]
learningData = map primal learning

main :: IO ()
main = print learningData

-- ---------------------------------------------------------------------
-- Hyperparameter tuning
-- ---------------------------------------------------------------------

tuneLR :: (Monoid r, Ord r, Functor e) => (Float, Float) -> Sel r (LR_F :* e) a -> Sel r e Float
tuneLR (a1, a2) =
  handlerRet
    (\_ -> return a1)
    ( LR
        ( operation
            ( \_ lk _ -> do
                err1 <- lk a1
                err2 <- lk a2
                return (if err1 < err2 then a1 else a2)
            )
        )
    )

hyperOptim :: Float
hyperOptim =
  runSel
    ( tuneLR
        (0.01, 0.03)
        ( do
            alpha <- perform lrate ()
            readLR
              alpha
              ( do
                  params <-
                    foldM
                      (\params (x, y) -> lreset (gd (linearReg params x y)))
                      random_params
                      training_data
                  handler
                    (Opt (operation (\p _ k -> k p)))
                    (mapM (\(x, y) -> linearReg params x y) validation_data)
              )
        ) ::
        Sel DF VoidEff Float
    )

-- ---------------------------------------------------------------------
-- An illustrative GAN model
-- ---------------------------------------------------------------------

hGen :: (LR_F :? e, Functor e) => Sel DF (Opt_F :* e) a -> Sel DF e a
hGen = gd

[effect|data DChoose = DChoose { dChoose :: Op [Param] [Param] } |]

hDis :: (Functor e) => Sel DF (DChoose_F :* e) a -> Sel DF e a
hDis = handler
  ( DChoose
      ( operation
          ( \ws lk k -> do
              ds <- autodiff lk ws
              let w' = zipWith (\w d -> liftDual (primal w + 0.01 * d)) ws ds
              k w'
          )
      )
  )

randomInitDW, randomInitGW :: [DF]
randomInitDW = [0.2, 0.3]
randomInitGW = [0.4, 0.5]

gan :: (LR_F :? e, Functor e) => [DF] -> [DF] -> DF -> DF -> Sel DF e ([Param], [Param])
gan [w1, b1] [w2, b2] sample noise =
  hDis
    ( do
        [dw, db] <- perform dChoose [w2, b2]
        let m2 = dw * sample + db
            l2 = log (m2 * m2)
        loss l2
        hGen
          ( do
              [gw, gb] <- perform optimize [w1, b1]
              let m1 = dw * (gw * noise + gb) + db
                  l1 = log ((1 - m1) * (1 - m1))
              loss l1
              return ([dw, db], [gw, gb])
          )
    )
