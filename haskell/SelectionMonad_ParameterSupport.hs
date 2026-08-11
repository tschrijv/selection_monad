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

newtype Sel r e a = Sel { runSelWith :: (a -> Sel r e r) -> (r, What e a (Sel r e a)) }
  
instance Functor e => Functor (Sel r e) where
  fmap f (Sel g) = Sel (\k -> let (r, w) = g (k . f) in (r, mapWhat f w))
    where
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

zeroLC :: (Functor e, Monoid r) => a -> Sel r e r
zeroLC _ = Sel $ \k -> (mempty, Leaf (mempty))

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
run p = case runSelWith p (\ _ -> Sel ( \ _ -> (mempty, Leaf mempty))) of
  (r, Leaf x) -> (x, r)
  (r, Node t) -> case t of {} 

glocal :: (Functor e, Monoid r) => (a -> Sel r e r) -> Sel r e a -> Sel r e a
glocal g1 e = Sel $ \ g ->
  case runSelWith e g1 of
    (r, Leaf x) -> (r, Leaf x)
    (r, Node t) -> (r, Node (fmap (glocal g1) t))

thenE :: (Functor e, Monoid r) =>  (a -> Sel r e r) -> Sel r e a -> Sel r e r
thenE g1 p = Sel $ \ g ->
  case runSelWith p g1 of
    (r, Leaf x) -> runSelWith (glocal zeroLC (fmap (r <>) (g1 x))) g
    (r, Node t) -> (mempty, Node (fmap (fmap (r <>) . thenE g1) t))

widen :: (Monoid r, Functor e, Functor f) => 
  Sel r e a -> Sel r (f :* e) a
widen p = Sel $ \ g ->
  let (r, w) = runSelWith p g
  in case w of
       Leaf x -> (r, Leaf x)
       Node t -> (r, Node (RightEff (fmap widen t)))

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
                ( \ par' -> thenE g (handle h par' q)
                , \ par' -> glocal g (handle h par' q)  
                )
              )
              t)
          par
        ) g)
    Node (RightEff t) -> (r, Node (fmap (fmap (handle h par) t)))

reset :: (Functor e, Monoid r) => Sel r e a -> Sel r e a
reset p = Sel $ \ g ->
  let (r, w) = runSelWith p g
  in case w of
    Leaf x -> (mempty, Leaf x)
    Node t -> (mempty, Node (fmap (reset) t))

--  let (r, w) = runSelWith p (\ a -> runSelWith (hret h a) gamma)
--  in case w of
--    Leaf x -> (r, Leaf x)
--    Node t -> (r, Node (fmap (\(l1v, k1v) -> runSelWith (hops h (fmap (\y -> (l1v y, k1v y)) t)) gamma) t))

-- -- | widenŴ, along an inclusion of effect contexts. Here that inclusion is
-- -- always "one more functor summand on the right", so widening is just
-- -- the @RightEff@ injection, recursively.
-- widenW :: (Functor e) => What r e x -> What r (f :* e) x
-- widenW (Leaf r x) = Leaf r x
-- widenW (Node r t) = Node r (RightEff (fmap widenW t))



-- -- ---------------------------------------------------------------------
-- -- Domains.agda §3.2: free layered ε-algebras, and bind̂ as the Kleisli
-- -- extension over Ŵ's own native algebra Ŵ-alg.
-- -- ---------------------------------------------------------------------

-- data LayeredAlg g r y = LayeredAlg
--   { psi :: g y -> y,
--     act :: r -> y -> y
--   }

-- -- | f†Ŵ : the unique homomorphic extension of f over a layered algebra.
-- extHat :: (Functor g) => LayeredAlg g r y -> (x -> y) -> What r g x -> y
-- extHat alg f (Leaf r x) = act alg r (f x)
-- extHat alg f (Node r t) = act alg r (psi alg (fmap (extHat alg f) t))

-- -- | Ŵ-alg : Ŵ ε X's own native layered algebra (φ̂ with own-loss 0,
-- -- action = tell).
-- whatAlg :: (Functor e, Monoid r) => LayeredAlg e r (What r e x)
-- whatAlg = LayeredAlg {psi = Node mempty, act = tellW}

-- -- | bind̂ = ext̂ Ŵ-alg.
-- bindW :: (Functor e, Monoid r) => What r e x -> (x -> What r e y) -> What r e y
-- bindW w f = extHat whatAlg f w

-- -- ---------------------------------------------------------------------
-- -- Domains.agda §3.3: loss, commutativity, and what changes.
-- -- ---------------------------------------------------------------------

-- -- | censor : recursively zero every recorded loss, leaving shape/leaves
-- -- untouched.
-- censorW :: (Functor e, Monoid r) => What r e x -> What r e x
-- censorW (Leaf _ x) = Leaf mempty x
-- censorW (Node _ t) = Node mempty (fmap censorW t)

-- -- | collect : Ŵ_ε(1) → Ŵ_ε(R), summing all losses along each
-- -- root-to-leaf path into that leaf's now R-valued payload. Note the
-- -- node case keeps the node's own recorded loss @r@ (unlike censor):
-- -- 'collectW' only ever touches leaves.
-- collectW :: (Functor e, Monoid r) => What r e () -> What r e r
-- collectW (Leaf r ()) = Leaf mempty r
-- collectW (Node r t) = Node r (fmap collectW t)

-- -- ---------------------------------------------------------------------
-- -- Domains.agda §3.4: the selection monad
-- --   Ŝ ε X = (X → Ŵ ε R) → Ŵ ε X,   R̂ ε := Ŵ ε R.
-- --
-- -- (This is the CURRENT Domains.agda: R̂_ε is Ŵ_ε(R), migrated from the
-- -- earlier Ŵ_ε(⊤) that paper.tex still documents -- so a loss
-- -- continuation's codomain here is @What r e r@, not @What r e ()@.)
-- -- ---------------------------------------------------------------------

-- newtype Sel r e a = Sel {runSelWith :: (a -> What r e r) -> What r e a}

-- -- | R̂_ε(F ∣ γ) := the loss associated to a selection function. Routed
-- -- through collectX/mapŴ (the current definition), not a plain γ†Ŵ(F γ).
-- rHatOf :: (Functor e, Monoid r) => Sel r e y -> (y -> What r e r) -> What r e r
-- rHatOf f gamma = bindW (collectXW (runSelWith f gamma)) (\(a, r1) -> mapW (r1 <>) (gamma a))

-- -- | bind̂ˢ (equation (6)): the Kleisli extension of Ŝ.
-- bindS :: (Functor e, Monoid r) => Sel r e x -> (x -> Sel r e y) -> Sel r e y
-- bindS fx f = Sel $ \gamma ->
--   bindW (runSelWith fx (\x -> rHatOf (f x) gamma)) (\x -> runSelWith (f x) gamma)


-- -- ---------------------------------------------------------------------
-- -- Denotational.agda §4: loss, reset. (@loss@ here takes an
-- -- already-evaluated value, cf. the module header; @Esem (lossE e)@'s
-- -- full sub-expression-embedding form is not needed in a shallow
-- -- embedding.)
-- -- ---------------------------------------------------------------------

-- -- | Ssem(reset e)(ρ) = λγ. censor(Ssem e(ρ)(γ)).
-- reset :: (Functor e, Monoid r) => Sel r e a -> Sel r e a
-- reset p = Sel $ \gamma -> censorW (runSelWith p gamma)

-- -- | lreset = reset (⟨e⟩ λx.0), i.e. reset composed with running under
-- -- the zero continuation.
-- lreset :: (Functor e, Monoid r) => Sel r e a -> Sel r e a
-- lreset p = reset $ Sel $ \_ -> runSelWith p (\_ -> Leaf mempty mempty)

-- -- ---------------------------------------------------------------------
-- -- Denotational.agda §5, parameter-free handlers. Fix γ : ⟦σ'⟧ → Ŵ ε R
-- -- and build the layered (f:*e)-algebra on A = Ŵ ε ⟦σ'⟧ directly (no
-- -- ⟦par⟧-exponent on the carrier: this is the "noparam" simplification,
-- -- dropping the extra @par@ index Handler carries in the sibling agda/
-- -- (parameterized) directory).
-- --
-- -- A @Handler r f e a b@ plays exactly the role of Denotational.agda's
-- -- object-language @Handler Γ ℓ σ σ' ε@ record, evaluated already: @hret@
-- -- is @handlerRet@/@ret h@'s semantics, and @hops@ takes, for each
-- -- operation, the pair (choice continuation l1v, delimited continuation
-- -- k1v) that handlerΨ's "yes" branch constructs -- i.e. @hops@'s own
-- -- argument type already IS @l1v,k1v@, one pair per possible input.
-- -- ---------------------------------------------------------------------



-- -- | handlerΨ, both branches: LeftEff is the handler's own label (the
-- -- "yes" branch, ℓ1 ≟ᵉ ℓ ↦ yes); RightEff is pass-through (the "no"
-- -- branch) -- which Haskell's @(:*)@ pattern match already dispatches by
-- -- label, never by a position-dependent witness (cf. the module header).
-- handlerPsi ::
--   (Functor f, Functor e, Monoid r) =>
--   Handler r f e a b ->
--   (b -> What r e r) ->
--   (f :* e) (What r e b) ->
--   What r e b
-- handlerPsi h gamma (LeftEff t) =
--   runSelWith (hops h (fmap (\y -> (l1v y, k1v y)) t)) gamma
--   where
--     -- l1(a) = λγ1. mapŴ(r1+r2)(collectX_R(γ†Ŵε(k(a)))) -- generalising
--     -- Ŵ_ε(⊤)'s plain "collect" to the now R-valued leaves of γ†Ŵε(k a),
--     -- which R̂_ε's Ŵ_ε(R) migration requires (a leaf here already
--     -- carries a genuine R value from γ, not unit, so the per-path total
--     -- r1 must be added to it, not just substituted for it).
--     l1v y = Sel $ \_ -> mapW (\(r1, r2) -> r1 <> r2) (collectXW (bindW y gamma))
--     -- k1(a) = k(a), promoted to a (γ-independent) selection function.
--     k1v y = Sel $ \_ -> y
-- handlerPsi _ _ (RightEff t) = Node mempty t

-- -- | s(a) = Ssem(ret h)(ρ[a/z])(γ).
-- handlerRet :: Handler r f e a b -> (b -> What r e r) -> a -> What r e b
-- handlerRet h gamma a = runSelWith (hret h a) gamma

-- handlerAlg :: (Functor f, Functor e, Monoid r) => Handler r f e a b -> (b -> What r e r) -> LayeredAlg (f :* e) r (What r e b)
-- handlerAlg h gamma = LayeredAlg {psi = handlerPsi h gamma, act = tellW}

-- -- | Ssem(handle h e)(ρ)(γ) = s†Ŵ_{ε,ℓℓ}(G(λa. widenŴ(R̂_ε(ret h ∣ γ)))).
-- handlerSem ::
--   (Functor f, Functor e, Monoid r) =>
--   Handler r f e a b ->
--   Sel r (f :* e) a ->
--   (b -> What r e r) ->
--   What r e b
-- handlerSem h p gamma =
--   extHat
--     (handlerAlg h gamma)
--     (handlerRet h gamma)
--     (runSelWith p (\a -> widenW (rHatOf (hret h a) gamma)))

-- handle :: (Functor f, Functor e, Monoid r) => Handler r f e a b -> Sel r (f :* e) a -> Sel r e b
-- handle h p = Sel (handlerSem h p)

-- -- | handleP: a handler whose return clause is just η̂ˢ.
-- handleP :: (Functor f, Functor e, Monoid r) => (f (Sel r e r, Sel r e b) -> Sel r e b) -> Sel r (f :* e) b -> Sel r e b
-- handleP alg = handle Handler {hret = pure, hops = alg}
