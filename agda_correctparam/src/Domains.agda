-- Signature of the object language, and a "parameter-correct" selection
-- monad construction ported from haskell/SelectionMonad_ParameterSupport2.hs,
-- rather than from paper.tex §3's Ŵ_ε-embeds-R ("hat") construction that
-- agda/src/Domains.agda uses.
--
-- WHY A NEW CONSTRUCTION. agda/'s Denotational.agda builds parameterized-
-- handler semantics (handlerΨ/handlerSem) via a layered-algebra/ext̂
-- homomorphic extension over Ŵ_ε (which embeds the running loss R at
-- EVERY leaf/node of the tree). That has a known soundness gap
-- (agda/src/Proofs.agda's theorem-B9-R5-WF; see paper_noparam's writeup
-- for the counterexample shape): an outer handler resuming its own
-- delimited continuation at a DIFFERENT parameter than its own bound one,
-- combined with a nested handler leaking its own choice-continuation's
-- value, breaks the layered-algebra's own homomorphism property.
--
-- SelectionMonad_ParameterSupport2.hs sidesteps this with two changes:
--   (1) the accumulated loss is kept SEPARATE from the effect tree -- a
--       plain (R, tree) pair, Writer-monad style -- instead of embedded
--       at every tree node;
--   (2) handler dispatch (`handle`) is written as a DIRECT structural
--       recursion over the selection function's own unfolding, matching
--       OpSem.agda's own (R5) rule shape by construction, instead of
--       going through a homomorphic extension whose own correctness (vs.
--       R5's literal fk/fl construction) is exactly what theorem-B9-R5-WF
--       could not discharge.
--
-- This file ports (1); Denotational.agda ports (2) (`handlerSem`, mirroring
-- Haskell's `handle`). Syntax.agda/Subst.agda/OpSem.agda are copied
-- unchanged from agda/ -- the object language and its operational
-- semantics do not depend on which denotational construction backs them.
--
-- NOT ported here: agda/src/Domains.agda's ŴMonad/ŜMonad modules (the
-- monad-law proofs for Ŵ/Ŝ) -- Denotational.agda does not need them, and
-- proving them for this construction is future work, not requested here.
module Domains where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans; sym; refl)
open import Relation.Nullary using (Dec)
open import Data.Unit using (⊤; tt)
open import Axiom.Extensionality.Propositional using (Extensionality)

-- ---------------------------------------------------------------------
-- Ground (first-order) types: what operations/primitive functions take
-- and return. Unchanged from agda/src/Domains.agda -- independent of
-- which Ŝ_ε construction backs the semantics.
-- ---------------------------------------------------------------------

module Ground (Base : Set) (⟦_⟧ᵇ : Base → Set) (R : Set) where

  data GTy : Set where
    base  : Base → GTy
    loss  : GTy            -- the distinguished type of loss constants r : loss
    unit  : GTy             -- the type "()"
    _`×_  : GTy → GTy → GTy

  ⟦_⟧ᴳ : GTy → Set
  ⟦ base b ⟧ᴳ  = ⟦ b ⟧ᵇ
  ⟦ loss ⟧ᴳ    = R
  ⟦ unit ⟧ᴳ    = ⊤
  ⟦ σ `× τ ⟧ᴳ  = ⟦ σ ⟧ᴳ × ⟦ τ ⟧ᴳ

-- ---------------------------------------------------------------------
-- General types. Unchanged from agda/src/Domains.agda.
-- ---------------------------------------------------------------------

module Types (Effect Base : Set) (⟦_⟧ᵇ : Base → Set) (R : Set) where
  open Ground Base ⟦_⟧ᵇ R public

  -- Effect contexts ε: multisets of effect labels, represented as lists so
  -- that the position of an occurrence plays the role of the paper's index
  -- i, 0 < i ≤ ε(ℓ).
  EffCxt : Set
  EffCxt = List Effect

  -- εℓ : extend ε by one further (freshly introduced, "outermost") copy of ℓ.
  _,ℓ_ : EffCxt → Effect → EffCxt
  ε ,ℓ ℓ = ε ++ (ℓ ∷ [])

  -- ε₁ ⊆ ε : every occurrence available in ε₁ is (also) available in ε.
  _⊆ᵉ_ : EffCxt → EffCxt → Set
  ε₁ ⊆ᵉ ε = ∀ {ℓ} → ℓ ∈ ε₁ → ℓ ∈ ε

  ⊆ᵉ-refl : ∀ {ε} → ε ⊆ᵉ ε
  ⊆ᵉ-refl m = m

  ⊆ᵉ-,ℓ : ∀ {ε ℓ} → ε ⊆ᵉ (ε ,ℓ ℓ)
  ⊆ᵉ-,ℓ {ε} m = ∈-++⁺ˡ m

  data Ty : Set where
    gnd   : GTy → Ty
    _`×_  : Ty → Ty → Ty
    _⇒_!_ : Ty → Ty → EffCxt → Ty

  Loss : Ty
  Loss = gnd loss

  UnitTy : Ty
  UnitTy = gnd unit

-- ---------------------------------------------------------------------
-- §3 replacement: the "correct-param" Ŝ_ε construction, given a concrete
-- (ground-typed) set of operations, and the general type semantics ⟦_⟧
-- built from Ŝ.
-- ---------------------------------------------------------------------

module SCorrect (Effect Base : Set) (⟦_⟧ᵇ : Base → Set) (R : Set) (0# : R) (_+_ : R → R → R)
            (Op : Effect → Set)
            (out in′ : ∀ {ℓ} → Op ℓ → Types.GTy Effect Base ⟦_⟧ᵇ R)
            where

  open Types Effect Base ⟦_⟧ᵇ R public

  -- F̂ ε X : a plain effect tree over ε (Haskell's `Free e a`) -- unlike
  -- agda/'s Ŵ, NO loss is embedded at any leaf/node; the accumulated loss
  -- is tracked entirely separately (see Ŝ below), Writer-monad style.
  -- Constructor named `opF̂` (not `op`): `op` is used pervasively as a
  -- plain *variable* name throughout Syntax.agda/Subst.agda/OpSem.agda
  -- (`(op : Op ℓ)`), and since this constructor ends up in scope there
  -- too (via `open Sig Sg`), naming it `op` shadow-collides with those
  -- bound variables and confuses Agda's copattern elaboration (surfaced
  -- as a spurious "cannot split on non-datatype Op" error in Subst.agda).
  data F̂ (ε : EffCxt) (X : Set) : Set where
    pure : X → F̂ ε X
    opF̂  : ∀ {ℓ} → ℓ ∈ ε → (o : Op ℓ) → ⟦ out o ⟧ᴳ → (⟦ in′ o ⟧ᴳ → F̂ ε X) → F̂ ε X

  mapF̂ : ∀ {ε X Y} → (X → Y) → F̂ ε X → F̂ ε Y
  mapF̂ f (pure x)       = pure (f x)
  mapF̂ f (opF̂ m o v κ)  = opF̂ m o v (λ a → mapF̂ f (κ a))

  bindF̂ : ∀ {ε X Y} → F̂ ε X → (X → F̂ ε Y) → F̂ ε Y
  bindF̂ (pure x)    f = f x
  bindF̂ (opF̂ m o v κ) f = opF̂ m o v (λ a → bindF̂ (κ a) f)

  -- Widening along an inclusion of effect contexts (Haskell's `widen`,
  -- generalised from "one more functor summand" to our list-of-labels ε).
  widenF̂ : ∀ {ε ε' X} → ε ⊆ᵉ ε' → F̂ ε X → F̂ ε' X
  widenF̂ sub (pure x)      = pure x
  widenF̂ sub (opF̂ m o v κ) = opF̂ (sub m) o v (λ a → widenF̂ sub (κ a))

  -- R̂ ε : the type of reports a loss continuation can produce (Haskell's
  -- `Free e r`).
  R̂ : EffCxt → Set
  R̂ ε = F̂ ε R

  -- ---------------------------------------------------------------------
  -- Selection functions. Ŝ/ŜStep are mutually defined, matching Haskell's
  -- `Sel r e a` / `What e a x`: ŜStep is one step of a selection
  -- function's own unfolding (done, or one pending operation call), and
  -- Ŝ's own runSelWith pairs that with the loss ACCUMULATED SO FAR --
  -- never embedded inside ŜStep itself.
  -- ---------------------------------------------------------------------

  mutual
    record Ŝ (ε : EffCxt) (X : Set) : Set where
      inductive
      constructor sel
      field
        runSelWith : (X → R̂ ε) → R × ŜStep ε X

    data ŜStep (ε : EffCxt) (X : Set) : Set where
      leaf : X → ŜStep ε X
      node : ∀ {ℓ} → ℓ ∈ ε → (o : Op ℓ) → ⟦ out o ⟧ᴳ → (⟦ in′ o ⟧ᴳ → Ŝ ε X) → ŜStep ε X

  open Ŝ public

  -- §3.1-analogue: unit, functorial action, Kleisli extension.
  η̂ˢ : ∀ {ε X} → X → Ŝ ε X
  runSelWith (η̂ˢ x) γ = 0# , leaf x

  mutual
    mapŜ : ∀ {ε X Y} → (X → Y) → Ŝ ε X → Ŝ ε Y
    runSelWith (mapŜ f p) γ with runSelWith p (λ x → γ (f x))
    ... | r , w = r , mapŜStep f w

    mapŜStep : ∀ {ε X Y} → (X → Y) → ŜStep ε X → ŜStep ε Y
    mapŜStep f (leaf x)       = leaf (f x)
    mapŜStep f (node m o v κ) = node m o v (λ a → mapŜ f (κ a))

  -- thenS g1 p : collapse p down to a plain R̂ ε report, running it under
  -- (fixed) loss-continuation g1 throughout -- Haskell's `thenE`. Used
  -- both for Kleisli extension (bindŜ) and directly for the object
  -- language's own THEN/handler-return bookkeeping (Denotational.agda).
  thenS : ∀ {ε X} → (X → R̂ ε) → Ŝ ε X → R̂ ε
  thenS g1 p with runSelWith p g1
  ... | r , leaf x       = mapF̂ (r +_) (g1 x)
  ... | r , node m o v κ = mapF̂ (r +_) (opF̂ m o v (λ a → thenS g1 (κ a)))

  bindŜ : ∀ {ε X Y} → Ŝ ε X → (X → Ŝ ε Y) → Ŝ ε Y
  runSelWith (bindŜ p k) g with runSelWith p (λ x → thenS g (k x))
  ... | r1 , leaf x       = let (r2 , w) = runSelWith (k x) g in (r1 + r2) , w
  ... | r1 , node m o v κ = r1 , node m o v (λ a → bindŜ (κ a) k)

  -- φ̂ˢ, the Ŝ ε X-algebra structure -- an operation call (Haskell's `opS`).
  φ̂ˢ : ∀ {ε X ℓ} → ℓ ∈ ε → (op : Op ℓ) → ⟦ out op ⟧ᴳ → (⟦ in′ op ⟧ᴳ → Ŝ ε X) → Ŝ ε X
  runSelWith (φ̂ˢ m o v κ) γ = 0# , node m o v κ

  -- addLossŜ/lossŜ : Haskell's addLoss/loss.
  addLossŜ : ∀ {ε X} → R → Ŝ ε X → Ŝ ε X
  runSelWith (addLossŜ r1 p) γ = let (r2 , w) = runSelWith p γ in (r1 + r2) , w

  lossŜ : ∀ {ε} → R → Ŝ ε ⊤
  lossŜ r = addLossŜ r (η̂ˢ tt)

  -- upS : promote a γ-independent effect tree into a selection function
  -- (Haskell's `upE`) -- used to build R5-style "choice continuation"
  -- values that ignore whatever γ they are later run against.
  upS : ∀ {ε X} → F̂ ε X → Ŝ ε X
  runSelWith (upS (pure x))      γ = 0# , leaf x
  runSelWith (upS (opF̂ m o v κ)) γ = 0# , node m o v (λ a → upS (κ a))

  -- glocalS sub g1 p : fix p's own loss-continuation to g1 (ignoring
  -- whatever γ is later supplied), recursively, at every future step --
  -- Haskell's `glocal`, generalised with a widening `sub : ε₁ ⊆ᵉ ε` fused
  -- into the recursion (g1 stays at its own, possibly smaller, ε₁
  -- throughout, so each node's membership witness needs promoting as we
  -- go -- there is no general "Ŝ ε₁ X → Ŝ ε X" widening independent of
  -- this recursion, since Ŝ is itself continuation-shaped).
  glocalS : ∀ {ε₁ ε X} → ε₁ ⊆ᵉ ε → (X → R̂ ε₁) → Ŝ ε₁ X → Ŝ ε X
  runSelWith (glocalS sub g1 p) γ with runSelWith p g1
  ... | r , leaf x       = r , leaf x
  ... | r , node m o v κ = r , node (sub m) o v (λ a → glocalS sub g1 (κ a))

  -- resetS : Haskell's `reset` -- discard the accumulated loss at every
  -- step (not just the top), matching censor's "recursively zero" shape.
  resetS : ∀ {ε X} → Ŝ ε X → Ŝ ε X
  runSelWith (resetS p) γ with runSelWith p γ
  ... | r , leaf x       = 0# , leaf x
  ... | r , node m o v κ = 0# , node m o v (λ a → resetS (κ a))

  -- Fig. 8 (hat-version): semantics of general types. Unchanged shape --
  -- only Ŝ's own internal definition changed.
  ⟦_⟧ : Ty → Set
  ⟦ gnd γ ⟧      = ⟦ γ ⟧ᴳ
  ⟦ σ `× τ ⟧     = ⟦ σ ⟧ × ⟦ τ ⟧
  ⟦ σ ⇒ τ ! ε ⟧  = ⟦ σ ⟧ → Ŝ ε ⟦ τ ⟧

-- ---------------------------------------------------------------------
-- The bundled signature record used by all downstream modules. Same
-- field structure as agda/src/Domains.agda's Sig -- Syntax.agda/
-- Subst.agda/OpSem.agda (copied unchanged) only ever consume these
-- fields, never Ŝ/F̂'s own internals directly.
-- ---------------------------------------------------------------------

record Sig : Set₁ where
  field
    Effect  : Set
    _≟ᵉ_    : (ℓ1 ℓ2 : Effect) → Dec (ℓ1 ≡ ℓ2)
    Base    : Set
    ⟦_⟧ᵇ    : Base → Set
    R       : Set
    0#      : R
    _+_     : R → R → R
    +-identityˡ : ∀ r → (0# + r) ≡ r
    +-identityʳ : ∀ r → (r + 0#) ≡ r
    +-assoc     : ∀ r s t → ((r + s) + t) ≡ (r + (s + t))
    +-comm      : ∀ r s → (r + s) ≡ (s + r)

  field
    -- Primitive (first-order) functions f : σ → τ.
    PrimFun : Types.GTy Effect Base ⟦_⟧ᵇ R → Types.GTy Effect Base ⟦_⟧ᵇ R → Set
    ⟦_⟧f    : ∀ {γ δ} → PrimFun γ δ → Types.⟦_⟧ᴳ Effect Base ⟦_⟧ᵇ R γ → Types.⟦_⟧ᴳ Effect Base ⟦_⟧ᵇ R δ

    -- Operations op : out --ℓ--> in ∈ Σ, ground argument/result types.
    Op   : Effect → Set
    out  : ∀ {ℓ} → Op ℓ → Types.GTy Effect Base ⟦_⟧ᵇ R
    in′  : ∀ {ℓ} → Op ℓ → Types.GTy Effect Base ⟦_⟧ᵇ R

  open SCorrect Effect Base ⟦_⟧ᵇ R 0# _+_ Op out in′ public
