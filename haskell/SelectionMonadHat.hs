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

-- | A literal, explicit-datatype companion to
-- @agda_noparam\/src\/Domains.agda@ and @agda_noparam\/src\/Denotational.agda@.
--
-- 'SelectionMonad.Correct' (the sibling module in this directory) already
-- realises the same "hat" construction, but does so by reusing the
-- library types @FreeT e (Writer r)@ and the standard machinery around
-- them (@transFreeT@, @hoistFreeT@, @wrap@, ...). This module instead
-- writes out \(\widehat W_\varepsilon\) as its own explicit recursive
-- type (isomorphic to @FreeT e (Writer r) x@, but not defined in terms
-- of it) and gives every combinator from Domains.agda\/Denotational.agda
-- its own, separately-typechecked definition, named after its Agda
-- counterpart (dropping the hats: @What@ for \(\widehat W_\varepsilon\),
-- @Sel@ for \(\widehat S_\varepsilon\), @bindW@\/@etaW@\/@tellW@\/...).
--
-- Two design choices carried over unchanged from 'SelectionMonad.Correct'
-- (they are not part of what the swap or the parameter-removal changed):
--
--   * Effect signatures (Domains.agda's @Op : Effect -> Set@ together
--     with @out@\/@in'@) are realised the usual shallow-embedding way, as
--     a functor per effect plus the @(:*)@\/@(:?)@ sum-and-injection
--     machinery, rather than as a Haskell encoding of @EffCxt@-as-list-
--     with-membership-proofs. Membership @l1 : ℓ1 ∈ ε@ becomes "which
--     disjunct of the functor sum": Haskell's @LeftEff@\/@RightEff@ can
--     never be position-ambiguous the way a list-membership proof can,
--     so @handlerΨ@'s dispatch (Denotational.agda's whole point in
--     switching from position- to label-based dispatch, see its own
--     comment above @demoteMem@) is simply how pattern matching on
--     @(:*)@ already works here.
--
--   * @loss@ is a smart constructor taking an already-evaluated Haskell
--     value @r@, not a full transliteration of the @lossE@ clause's
--     embedded sub-expression @e : loss ! ε@ (Haskell values passed to
--     @loss@ are, definitionally, already pure results of running
--     whatever effectful code produced them).
--
-- Everything else -- @What@\/@Sel@ themselves, and every combinator
-- built from them -- is written to match the current (parameter-free)
-- Domains.agda\/Denotational.agda definition by definition, including
-- the two respects in which those files have moved past what
-- @paper.tex@ documents: the loss-continuation type is @What r e r@
-- (i.e. \(\widehat R_\varepsilon = \widehat W_\varepsilon(R)\)), not
-- @What r e ()@, and 'rHatOf' is computed via 'collectXW'\/'mapW'
-- rather than a plain homomorphic extension.
module SelectionMonadHat where

import Control.Monad (ap)
import Data.List (group, maximumBy, minimumBy, sort)
import Data.Monoid (Sum (..))
import Prelude hiding (Left, Right, max, min)

-- ---------------------------------------------------------------------
-- Effect signatures as a sum of functors (Domains.agda's @Op : Effect ->
-- Set@, realised the shallow-embedding way; unrelated to the swap).
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
-- Domains.agda §3.1: the carrier \(\widehat W_\varepsilon\).
--
--   data Ŵ (ε : EffCxt) (X : Set) : Set where
--     leaf : R → X → Ŵ ε X
--     node : ∀ {ℓ} → ℓ ∈ ε → (op : Op ℓ) → R → ⟦ out op ⟧ᴳ
--          → (⟦ in′ op ⟧ᴳ → Ŵ ε X) → Ŵ ε X
--
-- The effect context ε and an operation's own (ℓ, op, o) triple both
-- collapse, in this shallow embedding, into "which functor and which of
-- its values": @Node r t@ already IS "(0#-or-r, node m op o κ)" bundled
-- into a single functor value @t :: e (What r e x)@ (e.g. for
-- @data Max c k = Max [c] (c -> k)@, @t = Max cs (\a -> ...)@ plays the
-- role of @op = Max, o = cs, κ = \a -> ...@ all at once).
-- ---------------------------------------------------------------------

data What r e x
  = Leaf r x
  | Node r (e (What r e x))

-- | mapŴ (§3.1: "the evident and harmless map").
mapW :: (Functor e) => (x -> y) -> What r e x -> What r e y
mapW f (Leaf r x) = Leaf r (f x)
mapW f (Node r t) = Node r (fmap (mapW f) t)

-- | widenŴ, along an inclusion of effect contexts. Here that inclusion is
-- always "one more functor summand on the right", so widening is just
-- the @RightEff@ injection, recursively.
widenW :: (Functor e) => What r e x -> What r (f :* e) x
widenW (Leaf r x) = Leaf r x
widenW (Node r t) = Node r (RightEff (fmap widenW t))

-- | η̂.
etaW :: (Monoid r) => x -> What r e x
etaW = Leaf mempty

-- | tell.
tellW :: (Monoid r) => r -> What r e x -> What r e x
tellW r (Leaf r0 x) = Leaf (r <> r0) x
tellW r (Node r0 t) = Node (r <> r0) t

-- ---------------------------------------------------------------------
-- Domains.agda §3.2: free layered ε-algebras, and bind̂ as the Kleisli
-- extension over Ŵ's own native algebra Ŵ-alg.
-- ---------------------------------------------------------------------

data LayeredAlg g r y = LayeredAlg
  { psi :: g y -> y,
    act :: r -> y -> y
  }

-- | f†Ŵ : the unique homomorphic extension of f over a layered algebra.
extHat :: (Functor g) => LayeredAlg g r y -> (x -> y) -> What r g x -> y
extHat alg f (Leaf r x) = act alg r (f x)
extHat alg f (Node r t) = act alg r (psi alg (fmap (extHat alg f) t))

-- | Ŵ-alg : Ŵ ε X's own native layered algebra (φ̂ with own-loss 0,
-- action = tell).
whatAlg :: (Functor e, Monoid r) => LayeredAlg e r (What r e x)
whatAlg = LayeredAlg {psi = Node mempty, act = tellW}

-- | bind̂ = ext̂ Ŵ-alg.
bindW :: (Functor e, Monoid r) => What r e x -> (x -> What r e y) -> What r e y
bindW w f = extHat whatAlg f w

-- ---------------------------------------------------------------------
-- Domains.agda §3.3: loss, commutativity, and what changes.
-- ---------------------------------------------------------------------

-- | censor : recursively zero every recorded loss, leaving shape/leaves
-- untouched.
censorW :: (Functor e, Monoid r) => What r e x -> What r e x
censorW (Leaf _ x) = Leaf mempty x
censorW (Node _ t) = Node mempty (fmap censorW t)

-- | bump_r : add r into the recorded total at every leaf beneath the
-- current node.
bumpW :: (Functor e, Semigroup r) => r -> What r e (x, r) -> What r e (x, r)
bumpW r (Leaf r0 (x, s)) = Leaf r0 (x, r <> s)
bumpW r (Node r0 t) = Node r0 (fmap (bumpW r) t)

-- | collectX : pair each leaf value with the total accumulated loss on
-- its path, zeroing every node's own recorded loss along the way.
collectXW :: (Functor e, Monoid r) => What r e x -> What r e (x, r)
collectXW (Leaf r x) = Leaf mempty (x, r)
collectXW (Node r t) = Node mempty (fmap (bumpW r . collectXW) t)

-- | collect : Ŵ_ε(1) → Ŵ_ε(R), summing all losses along each
-- root-to-leaf path into that leaf's now R-valued payload. Note the
-- node case keeps the node's own recorded loss @r@ (unlike censor):
-- 'collectW' only ever touches leaves.
collectW :: (Functor e, Monoid r) => What r e () -> What r e r
collectW (Leaf r ()) = Leaf mempty r
collectW (Node r t) = Node r (fmap collectW t)

-- ---------------------------------------------------------------------
-- Domains.agda §3.4: the selection monad
--   Ŝ ε X = (X → Ŵ ε R) → Ŵ ε X,   R̂ ε := Ŵ ε R.
--
-- (This is the CURRENT Domains.agda: R̂_ε is Ŵ_ε(R), migrated from the
-- earlier Ŵ_ε(⊤) that paper.tex still documents -- so a loss
-- continuation's codomain here is @What r e r@, not @What r e ()@.)
-- ---------------------------------------------------------------------

newtype Sel r e a = Sel {runSelWith :: (a -> What r e r) -> What r e a}

-- | η̂ˢ.
pureS :: (Monoid r) => x -> Sel r e x
pureS x = Sel (\_ -> Leaf mempty x)

-- | R̂_ε(F ∣ γ) := the loss associated to a selection function. Routed
-- through collectX/mapŴ (the current definition), not a plain γ†Ŵ(F γ).
rHatOf :: (Functor e, Monoid r) => Sel r e y -> (y -> What r e r) -> What r e r
rHatOf f gamma = bindW (collectXW (runSelWith f gamma)) (\(a, r1) -> mapW (r1 <>) (gamma a))

-- | bind̂ˢ (equation (6)): the Kleisli extension of Ŝ.
bindS :: (Functor e, Monoid r) => Sel r e x -> (x -> Sel r e y) -> Sel r e y
bindS fx f = Sel $ \gamma ->
  bindW (runSelWith fx (\x -> rHatOf (f x) gamma)) (\x -> runSelWith (f x) gamma)

instance (Functor e) => Functor (Sel r e) where
  fmap f (Sel g) = Sel (\k -> mapW f (g (k . f)))

instance (Functor e, Monoid r) => Applicative (Sel r e) where
  pure = pureS
  (<*>) = ap

instance (Functor e, Monoid r) => Monad (Sel r e) where
  return = pure
  (>>=) = bindS

-- | φ̂ˢ, the Ŝ ε X-algebra structure -- an operation call.
opS :: (Functor e, Monoid r) => e (Sel r e a) -> Sel r e a
opS t = Sel $ \gamma -> Node mempty (fmap (\s -> runSelWith s gamma) t)

op :: (f :? e, Monoid r) => f (Sel r e a) -> Sel r e a
op = opS . inj

-- ---------------------------------------------------------------------
-- Denotational.agda §4: loss, reset. (@loss@ here takes an
-- already-evaluated value, cf. the module header; @Esem (lossE e)@'s
-- full sub-expression-embedding form is not needed in a shallow
-- embedding.)
-- ---------------------------------------------------------------------

loss :: (Functor e, Monoid r) => r -> Sel r e ()
loss r = Sel $ \_ -> tellW r (Leaf mempty ())

-- | Ssem(reset e)(ρ) = λγ. censor(Ssem e(ρ)(γ)).
reset :: (Functor e, Monoid r) => Sel r e a -> Sel r e a
reset p = Sel $ \gamma -> censorW (runSelWith p gamma)

-- | lreset = reset (⟨e⟩ λx.0), i.e. reset composed with running under
-- the zero continuation.
lreset :: (Functor e, Monoid r) => Sel r e a -> Sel r e a
lreset p = reset $ Sel $ \_ -> runSelWith p (\_ -> Leaf mempty mempty)

-- | Evaluate a closed program (no pending effects) under the canonical
-- zero continuation γ₀ = λ_. η̂(0#).
run :: (Monoid r) => Sel r VoidEff a -> (a, r)
run p = case runSelWith p (\_ -> Leaf mempty mempty) of
  Leaf r x -> (x, r)
  Node _ t -> case t of {}

-- ---------------------------------------------------------------------
-- Denotational.agda §5, parameter-free handlers. Fix γ : ⟦σ'⟧ → Ŵ ε R
-- and build the layered (f:*e)-algebra on A = Ŵ ε ⟦σ'⟧ directly (no
-- ⟦par⟧-exponent on the carrier: this is the "noparam" simplification,
-- dropping the extra @par@ index Handler carries in the sibling agda/
-- (parameterized) directory).
--
-- A @Handler r f e a b@ plays exactly the role of Denotational.agda's
-- object-language @Handler Γ ℓ σ σ' ε@ record, evaluated already: @hret@
-- is @handlerRet@/@ret h@'s semantics, and @hops@ takes, for each
-- operation, the pair (choice continuation l1v, delimited continuation
-- k1v) that handlerΨ's "yes" branch constructs -- i.e. @hops@'s own
-- argument type already IS @l1v,k1v@, one pair per possible input.
-- ---------------------------------------------------------------------

data Handler r f e a b = Handler
  { hret :: a -> Sel r e b,
    hops :: f (Sel r e r, Sel r e b) -> Sel r e b
  }

-- | handlerΨ, both branches: LeftEff is the handler's own label (the
-- "yes" branch, ℓ1 ≟ᵉ ℓ ↦ yes); RightEff is pass-through (the "no"
-- branch) -- which Haskell's @(:*)@ pattern match already dispatches by
-- label, never by a position-dependent witness (cf. the module header).
handlerPsi ::
  (Functor f, Functor e, Monoid r) =>
  Handler r f e a b ->
  (b -> What r e r) ->
  (f :* e) (What r e b) ->
  What r e b
handlerPsi h gamma (LeftEff t) =
  runSelWith (hops h (fmap (\y -> (l1v y, k1v y)) t)) gamma
  where
    -- l1(a) = λγ1. mapŴ(r1+r2)(collectX_R(γ†Ŵε(k(a)))) -- generalising
    -- Ŵ_ε(⊤)'s plain "collect" to the now R-valued leaves of γ†Ŵε(k a),
    -- which R̂_ε's Ŵ_ε(R) migration requires (a leaf here already
    -- carries a genuine R value from γ, not unit, so the per-path total
    -- r1 must be added to it, not just substituted for it).
    l1v y = Sel $ \_ -> mapW (\(r1, r2) -> r1 <> r2) (collectXW (bindW y gamma))
    -- k1(a) = k(a), promoted to a (γ-independent) selection function.
    k1v y = Sel $ \_ -> y
handlerPsi _ _ (RightEff t) = Node mempty t

-- | s(a) = Ssem(ret h)(ρ[a/z])(γ).
handlerRet :: Handler r f e a b -> (b -> What r e r) -> a -> What r e b
handlerRet h gamma a = runSelWith (hret h a) gamma

handlerAlg :: (Functor f, Functor e, Monoid r) => Handler r f e a b -> (b -> What r e r) -> LayeredAlg (f :* e) r (What r e b)
handlerAlg h gamma = LayeredAlg {psi = handlerPsi h gamma, act = tellW}

-- | Ssem(handle h e)(ρ)(γ) = s†Ŵ_{ε,ℓℓ}(G(λa. widenŴ(R̂_ε(ret h ∣ γ)))).
handlerSem ::
  (Functor f, Functor e, Monoid r) =>
  Handler r f e a b ->
  Sel r (f :* e) a ->
  (b -> What r e r) ->
  What r e b
handlerSem h p gamma =
  extHat
    (handlerAlg h gamma)
    (handlerRet h gamma)
    (runSelWith p (\a -> widenW (rHatOf (hret h a) gamma)))

handle :: (Functor f, Functor e, Monoid r) => Handler r f e a b -> Sel r (f :* e) a -> Sel r e b
handle h p = Sel (handlerSem h p)

-- | handleP: a handler whose return clause is just η̂ˢ.
handleP :: (Functor f, Functor e, Monoid r) => (f (Sel r e r, Sel r e b) -> Sel r e b) -> Sel r (f :* e) b -> Sel r e b
handleP alg = handle Handler {hret = pure, hops = alg}

---------------------------
-- Examples
--
-- The public interface above (op, loss, run, handle, handleP, reset,
-- lreset, Handler{hret,hops}) has exactly the same names and types as
-- SelectionMonad.Correct's, so these examples are the familiar ones,
-- unchanged, now running over the explicit What/Sel encoding instead of
-- FreeT e (Writer r). (The autodiff/linear-regression example is
-- omitted here: it exercises ordinary numeric/AD machinery orthogonal
-- to the Ŵ/Ŝ construction, and is not affected by anything ported from
-- Domains.agda/Denotational.agda in this file.)
---------------------------

-- non-determinism

data NDet r = Decide (Bool -> r) deriving (Functor)

decide :: (Monoid r, Functor e, NDet :? e) => Sel r e Bool
decide = op (Decide pure)

ndtp :: (Functor e, Monoid r, NDet :? e) => Sel r e Bool
ndtp = do
  b <- decide
  return (not b)

nDetAlg :: (Monoid r, Functor e) => NDet (Sel r e r, Sel r e [a]) -> Sel r e [a]
nDetAlg (Decide k) = do
  x <- (snd . k) True
  y <- (snd . k) False
  return (x ++ y)

hNDet :: (Functor e, Monoid r) => Sel r (NDet :* e) Bool -> Sel r e [Bool]
hNDet = handle Handler {hret = \x -> return [x], hops = nDetAlg}

ndtpResult :: (Show r, Ord r, Monoid r) => ([Bool], r)
ndtpResult = run $ hNDet ndtp

-- max, and a password-strength example combining it with loss

data Max c k = Max [c] (c -> k) deriving (Functor)

max :: (Monoid r, Functor e, Max a :? e) => [a] -> Sel r e a
max lst = op (Max lst pure)

maxWith :: (Monad m, Ord b) => (a -> m b) -> [a] -> m a
maxWith f x = do
  bs <- mapM f x
  let r = maximumBy (\p q -> compare (fst p) (fst q)) $ zip bs [0 ..]
  return $ x !! snd r

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
  b <- maxWith (fst . k) c
  (snd . k) b

hMax :: forall c r e a. (Monoid r, Ord a, Ord r, Functor e) => Sel r (Max c :* e) a -> Sel r e a
hMax = handleP maxAlg

passResult :: (String, Sum Int)
passResult = run $ hMax @String password

-- min, and minimax combining max and min under the same loss

data Min c k = Min [c] (c -> k) deriving (Functor)

min :: (Monoid r, Functor e, Min a :? e) => [a] -> Sel r e a
min lst = op (Min lst pure)

minWith :: (Monad m, Ord b) => (a -> m b) -> [a] -> m a
minWith f x = do
  bs <- mapM f x
  let r = minimumBy (\p q -> compare (fst p) (fst q)) $ zip bs [0 ..]
  return $ x !! snd r

minAlgebra :: forall c r e a. (Ord r, Monoid r, Functor e) => Min c (Sel r e r, Sel r e a) -> Sel r e a
minAlgebra (Min l k) = do
  x <- minWith (fst . k) l
  (snd . k) x

data Strategy = Left | Right deriving (Show, Eq, Enum, Ord)

hMin :: forall c e r a. (Ord r, Monoid r, Functor e) => Sel r (Min c :* e) a -> Sel r e a
hMin = handleP minAlgebra

minimax :: (Functor e) => Sel (Sum Float) e (Strategy, Strategy)
minimax = hMax @Strategy $
  hMin @Strategy $ do
    a <- max [Left, Right]
    b <- min [Left, Right]
    loss $ [5, 3, 2, 9] !! (fromEnum a * 2 + fromEnum b)
    return (a, b)

minimaxResult :: ((Strategy, Strategy), Sum Float)
minimaxResult = run minimax

-- a two-player repeated game, exercising a custom effect, loss, and
-- lreset/handle together in recursion

getStrtgy :: Step -> Strategy
getStrtgy (Stay x) = x
getStrtgy (Move x) = x

move :: Strategy -> Strategy
move Left = Right
move Right = Left

data Step = Move Strategy | Stay Strategy deriving (Eq, Show)

data Play r = Play (Step, Step) ((Step, Step) -> r) deriving (Functor)

play :: (Monoid r, Functor e, Play :? e) => (Step, Step) -> Sel r e (Step, Step)
play (a, b) = op (Play (a, b) pure)

isMove :: Step -> Bool
isMove (Move _) = True
isMove _ = False

isStay :: Step -> Bool
isStay (Stay _) = True
isStay _ = False

exampleNash :: (Functor e) => Step -> Step -> Sel (Sum Float, Sum Float) e (Step, Step)
exampleNash a b = do
  (a', b') <- lreset $ hNash $ do
    (a1, b1) <- play (a, b)
    let (a2, b2) = (getStrtgy a1, getStrtgy b1)
    loss $
      fmap Sum $
        [(2, 2), (0, 3), (3, 0), (1, 1)]
          !! (fromEnum a2 * 2 + fromEnum b2)
    return (a1, b1)
  if isStay a' && isStay b'
    then return (a', b')
    else exampleNash a' b'

hNash :: (Ord r, Monoid r, Functor e) => Sel (r, r) (Play :* e) a -> Sel (r, r) e a
hNash = handleP playAlgebra

playAlgebra :: (Ord r, Monoid r, Functor e) => Play (Sel (r, r) e (r, r), Sel (r, r) e a) -> Sel (r, r) e a
playAlgebra (Play (s1, s2) k) = do
  let (a1, b1) = (getStrtgy s1, getStrtgy s2)
      (a2, b2) = (move a1, move b1)
  l1 <- fst . k $ (Stay a1, Stay b1)
  l2 <- fst . k $ (Stay a2, Stay b1)
  l3 <- fst . k $ (Stay a1, Stay b2)
  if fst l2 < fst l1 -- A makes a move
    then snd . k $ (Move a2, Stay b1)
    else
      if snd l3 < snd l1 -- B makes a move
        then snd . k $ (Stay a1, Move b2)
        else snd . k $ (Stay a1, Stay b1)

nashResult :: ((Step, Step), (Sum Float, Sum Float))
nashResult = run $ exampleNash (Move Right) (Move Right)
