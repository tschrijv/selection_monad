-- The denotational semantics of expressions and handlers, ported from
-- haskell/SelectionMonad_ParameterSupport2.hs (see Domains.agda's header
-- for why: agda/'s handlerΨ/handlerSem, built via a layered-algebra/ext̂
-- homomorphic extension over Ŵ_ε, has a known soundness gap at
-- parameterized handlers -- agda/src/Proofs.agda's theorem-B9-R5-WF).
--
-- The key structural difference from agda/src/Denotational.agda:
-- `handlerSem` below is written as a DIRECT structural recursion over the
-- handled body's own Ŝ-unfolding (mirroring Haskell's `handle`, and by
-- construction shaped like OpSem.agda's own (R5) rule: peel one step,
-- dispatch on whether its label is this handler's own, recurse), rather
-- than via `ext̂`/`LayeredAlg`. Everywhere a plain `Ŝ`-value used to be
-- "applied to a continuation" directly (agda/'s Ŝ was a bare function
-- type), it is now threaded through `runSelWith`/`thenS`/`glocalS`/`upS`
-- (Domains.agda) instead, since Ŝ is now a genuine (co)recursive record.
open import Domains using (Sig)

module Denotational (Sg : Sig) where

open Sig Sg
open import Syntax Sg
open import Subst Sg using (Ren; extR; renV; renE; renH; weaken1; weaken1V; wkSub; cons)

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ---------------------------------------------------------------------
-- Environments. Unchanged.
-- ---------------------------------------------------------------------

Env : Cxt → Set
Env Γ = ∀ {σ} → Γ ∋ σ → ⟦ σ ⟧

_,,_ : ∀ {Γ σ} → Env Γ → ⟦ σ ⟧ → Env (Γ , σ)
(ρ ,, a) Z     = a
(ρ ,, a) (S x) = ρ x

-- ---------------------------------------------------------------------
-- Semantics of values. Unchanged in shape -- only ⟦_⟧/Ŝ's own internal
-- definition (Domains.agda) changed.
-- ---------------------------------------------------------------------

mutual
  Vsem : ∀ {Γ σ} → Val Γ σ → Env Γ → ⟦ σ ⟧
  Vsem (vvar x)    ρ = ρ x
  Vsem (vgnd x)    ρ = x
  Vsem (vpair v w) ρ = Vsem v ρ , Vsem w ρ
  Vsem (vabs e)    ρ = λ a → Esem e (ρ ,, a)

  -- §4's auxiliary loss-function semantics ℒ: the loss g would eventually
  -- report at a, run to completion. g's own body is Loss-typed (σ→Loss),
  -- so its OWN eventual value (an R, at whatever leaf `Vsem g ρ a`
  -- reaches) IS ITSELF a loss contribution, not a value to discard --
  -- collapsing via `thenS pure` folds that leaf value into the
  -- accumulated loss (mapF̂(r+_)(pure x) = pure(r+x)) exactly the way
  -- agda_noparam's own R̂-of/collectX/bump machinery combines a Ŵ leaf's
  -- separately-carried (r,x) pair into a single total. Collapsing at the
  -- CONSTANT zero continuation (λ_→pure0#) instead -- this construction's
  -- first attempt -- silently discards g's own returned value, which is
  -- unsound: Theorem 7.9/B.9's (R7) case (v▶g --0--> ⟨e[v]⟩^εg_zeroLC,
  -- below) is a concrete counterexample (g = vabs(val(vgnd 5)) reports 0#
  -- under the old definition but 5 under this one, and only the latter
  -- matches the reduct's own denotation).
  Lsem : ∀ {Γ σ ε} → LC Γ σ ε → Env Γ → ⟦ σ ⟧ → R̂ ε
  Lsem g ρ a = thenS pure (Vsem g ρ a)

  -- ---------------------------------------------------------------------
  -- Semantics of expressions.
  -- ---------------------------------------------------------------------

  Esem : ∀ {Γ σ ε} → Γ ⊢ σ ! ε → Env Γ → Ŝ ε ⟦ σ ⟧
  Esem (val v) ρ          = η̂ˢ (Vsem v ρ)
  Esem (fun f e) ρ        = bindŜ (Esem e ρ) (λ a → η̂ˢ (⟦ f ⟧f a))
  Esem (pair e1 e2) ρ     = bindŜ (Esem e1 ρ) (λ a → bindŜ (Esem e2 ρ) (λ b → η̂ˢ (a , b)))
  Esem (fst e) ρ          = bindŜ (Esem e ρ) (λ{ (a , b) → η̂ˢ a })
  Esem (snd e) ρ          = bindŜ (Esem e ρ) (λ{ (a , b) → η̂ˢ b })
  Esem (app e1 e2) ρ      = bindŜ (Esem e1 ρ) (λ φ → bindŜ (Esem e2 ρ) φ)
  Esem (opE m op e) ρ     = bindŜ (Esem e ρ) (λ a → φ̂ˢ m op a η̂ˢ)
  Esem (lossE e) ρ        = bindŜ (Esem e ρ) (λ r → addLossŜ r (η̂ˢ tt))

  -- Ssem(e1 ▶ g)(ρ) : run e1, but collapse the whole thing down to a
  -- plain R̂ ε report using g's own (widened) semantics as the loss
  -- continuation throughout (`thenS`), then promote that γ-independent
  -- report back into a selection function (`upS`) -- ▶'s own result
  -- genuinely does not depend on whatever γ the caller later supplies,
  -- matching "disregards g" directly rather than needing collectX/bump/
  -- mapŴ bookkeeping to establish it.
  Esem (thenE sub e1 g) ρ = upS (thenS (λ a → widenF̂ sub (Lsem g ρ a)) (Esem e1 ρ))

  -- Ssem(e1 + e2)(ρ) : run e1 to a loss value r, run e2 to a loss value
  -- s, report r+s -- the LOSS TYPE's own Sig-provided _+_, matching
  -- Rplus's own operational reduction directly (OpSem.agda).
  Esem (plusE e1 e2) ρ = bindŜ (Esem e1 ρ) (λ r → bindŜ (Esem e2 ρ) (λ s → η̂ˢ (r + s)))

  -- Ssem(⟨e⟩^ε₁_g)(ρ) : fix e's own loss-continuation to (widened) g,
  -- ignoring whatever γ is later supplied, throughout -- `glocalS` fuses
  -- this with widening e's own tree from its natural ε₁ up to ε (sub2),
  -- since Ŝ has no continuation-independent "widen" of its own (see
  -- Domains.agda's note on glocalS).
  Esem (glocalE sub1 sub2 e g) ρ = glocalS sub2 (λ a → widenF̂ sub1 (Lsem g ρ a)) (Esem e ρ)

  Esem (resetE e) ρ              = resetS (Esem e ρ)
  Esem (handleE h e1 e2) ρ       = bindŜ (Esem e1 ρ) (λ p → handlerSem h ρ p (Esem e2 ρ))

  -- ---------------------------------------------------------------------
  -- §5: semantics of handlers, ported from SelectionMonad_ParameterSupport2.hs's
  -- `handle`. Fix ρ, and the running parameter p; handlerSem is called
  -- afresh (recursively) at each new p a clause chooses to resume/select
  -- at, exactly mirroring `handle h par' q` inside Haskell's own
  -- (choice, delim) construction below -- there is no separate "carrier
  -- algebra" to build first.
  -- ---------------------------------------------------------------------

  -- ℓ1 ≠ ℓ rules out m pointing at the freshly-appended slot of (ε ,ℓ ℓ)
  -- (the only element there IS ℓ), so ∈-++⁻ is forced into its inj₁ case.
  -- Unchanged from agda/src/Denotational.agda.
  demoteMem : ∀ {ℓ ℓ1 ε} → ℓ1 ∈ (ε ,ℓ ℓ) → ¬ (ℓ1 ≡ ℓ) → ℓ1 ∈ ε
  demoteMem {ε = ε} m neq with ∈-++⁻ ε m
  ... | inj₁ x          = x
  ... | inj₂ (here eq)  = ⊥-elim (neq eq)
  ... | inj₂ (there ())

  -- s(a) = Ssem(er)(ρ[(p,a)/z]) (no γ baked in -- Esem already returns a
  -- selection function, not a value pre-applied to a continuation).
  -- Top-level (not handlerSem-local), mirroring agda/'s own handlerRet.
  handlerRet : ∀ {Γ ℓ par σ σ' ε} → Handler Γ ℓ par σ σ' ε → Env Γ → ⟦ σ ⟧ → ⟦ gnd par ⟧ → Ŝ ε ⟦ σ' ⟧
  handlerRet h ρ a p' = Esem (ret h) ((ρ ,, p') ,, a)

  -- handlerSem h ρ p G : dispatch G's own next unfolding step.
  --   * G is already done (leaf x): report x's own loss via ret h, run
  --     under the ambient γ, combined with the loss G already
  --     accumulated (Haskell's `Leaf x -> addLoss' r (runSelWith (hret
  --     h par x) g)`).
  --   * G's next step is an operation OF THIS HANDLER's OWN label ℓ
  --     (dispatched via ℓ1 ≟ᵉ ℓ, witness-independent -- see
  --     agda/src/Denotational.agda's own comment on this, still the
  --     right fix here): jump directly to the object-language clause,
  --     instantiated at (p, v, l1v, k1v) -- z's own tupling (par × in)
  --     matches Syntax.agda's clause signature; l1v/k1v are exactly
  --     Haskell's (choice, delim) pair, l1v further collapsed to a plain
  --     R̂-report (upS ∘ thenS) since fl's own codomain is Loss, and k1v
  --     left as a genuine selection function (glocalS, fixing γ) since
  --     fk's own codomain is σ' -- matching R5's own fl/fk shapes
  --     (thenE-wrapped vs. glocalE-wrapped) by construction.
  --   * G's next step is an operation for a DIFFERENT label: pass
  --     through unchanged (demoting the membership witness), recursing
  --     into each continuation.
  handlerSem : ∀ {Γ ℓ par σ σ' ε} → Handler Γ ℓ par σ σ' ε → Env Γ → ⟦ gnd par ⟧ → Ŝ (ε ,ℓ ℓ) ⟦ σ ⟧ → Ŝ ε ⟦ σ' ⟧
  runSelWith (handlerSem h ρ p G) γ = handlerStep h ρ γ p (runSelWith G (λ a → widenF̂ ⊆ᵉ-,ℓ (thenS γ (handlerRet h ρ a p))))

  -- Split out of handlerSem (rather than a `with`/`...`-chain on
  -- handlerSem's own copattern clause) purely to dodge an Agda layout
  -- quirk: nesting `with runSelWith G ...` then `with ℓ1 ≟ᵉ ℓ` then
  -- `with eq` under a record copattern made the trailing `| no neq`
  -- continuation mis-associate with the innermost `with eq` instead of
  -- `with ℓ1 ≟ᵉ ℓ` (agda/'s own handlerΨ dodges the same issue by
  -- re-stating its full LHS for the `no` case rather than using `...`).
  -- An ordinary top-level function with an explicit `step` argument has
  -- no such issue.
  handlerStep : ∀ {Γ ℓ par σ σ' ε} → Handler Γ ℓ par σ σ' ε → Env Γ → (⟦ σ' ⟧ → R̂ ε) → ⟦ gnd par ⟧
              → R × ŜStep (ε ,ℓ ℓ) ⟦ σ ⟧ → R × ŜStep ε ⟦ σ' ⟧
  handlerStep h ρ γ p (r , leaf x) =
    let (r2 , w2) = runSelWith (handlerRet h ρ x p) γ
    in (r + r2) , w2
  handlerStep {ℓ = ℓ} h ρ γ p (r , node {ℓ = ℓ1} m o v κ) with ℓ1 ≟ᵉ ℓ
  handlerStep {ℓ = ℓ} h ρ γ p (r , node {ℓ = ℓ1} m o v κ) | yes eq with eq
  handlerStep {ℓ = ℓ} h ρ γ p (r , node {ℓ = .ℓ} m o v κ) | yes eq | refl =
    let (r2 , w2) = runSelWith (Esem (clause h o) ((((ρ ,, p) ,, v) ,, l1v h ρ γ o κ) ,, k1v h ρ γ o κ)) γ
    in (r + r2) , w2
  handlerStep h ρ γ p (r , node m o v κ) | no neq =
    r , node (demoteMem m neq) o v (λ a → handlerSem h ρ p (κ a))

  -- l1v/k1v : Haskell's own (choice, delim) pair, per operation branch a
  -- and freshly-chosen parameter p' -- z's own tupling (par × in) matches
  -- Syntax.agda's clause signature. l1v collapses to a plain R̂-report
  -- (upS ∘ thenS, since fl's own codomain is Loss); k1v stays a genuine
  -- selection function that fixes γ throughout (glocalS, since fk's own
  -- codomain is σ') -- matching R5's own thenE-wrapped fl / glocalE-
  -- wrapped fk shapes by construction, not by a separate soundness proof.
  l1v : ∀ {Γ ℓ par σ σ' ε} → Handler Γ ℓ par σ σ' ε → Env Γ → (⟦ σ' ⟧ → R̂ ε)
      → (op : Op ℓ) → (⟦ in′ op ⟧ᴳ → Ŝ (ε ,ℓ ℓ) ⟦ σ ⟧) → ⟦ gnd par `× gnd (in′ op) ⟧ → Ŝ ε R
  l1v h ρ γ op κ (p' , a) = upS (thenS γ (handlerSem h ρ p' (κ a)))

  k1v : ∀ {Γ ℓ par σ σ' ε} → Handler Γ ℓ par σ σ' ε → Env Γ → (⟦ σ' ⟧ → R̂ ε)
      → (op : Op ℓ) → (⟦ in′ op ⟧ᴳ → Ŝ (ε ,ℓ ℓ) ⟦ σ ⟧) → ⟦ gnd par `× gnd (in′ op) ⟧ → Ŝ ε ⟦ σ' ⟧
  k1v h ρ γ op κ (p' , a) = glocalS ⊆ᵉ-refl γ (handlerSem h ρ p' (κ a))

