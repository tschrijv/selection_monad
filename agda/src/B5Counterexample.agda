-- Scratch check: a concrete instantiation of Lemma 7.5(1)/B.5(1) that
-- (per hand computation in the session transcript) makes the two sides
-- disagree. Written against Example.agda's `mySig` (R = ℕ) purely so we
-- have a concrete Sig to instantiate against; the effect signature itself
-- is irrelevant (the counterexample never calls an operation), so ε = []
-- throughout.
module B5Counterexample where

open import Domains
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityˡ; +-identityʳ; +-assoc; +-comm)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Eff : Set where
data Bse : Set where

⟦_⟧ᵇ' : Bse → Set
⟦_⟧ᵇ' ()

data Op' : Eff → Set where

module GT = Ground Bse ⟦_⟧ᵇ' ℕ

out' in′' : ∀ {ℓ} → Op' ℓ → GT.GTy
out' ()
in′' ()

mySig : Sig
mySig = record
  { Effect  = Eff
  ; Base    = Bse
  ; ⟦_⟧ᵇ    = ⟦_⟧ᵇ'
  ; R       = ℕ
  ; 0#      = 0
  ; _+_     = _+_
  ; +-identityˡ = +-identityˡ
  ; +-identityʳ = +-identityʳ
  ; +-assoc     = +-assoc
  ; +-comm      = +-comm
  ; PrimFun = λ _ _ → ⊥
  ; ⟦_⟧f    = λ ()
  ; Op      = Op'
  ; out     = out'
  ; in′     = in′'
  }

open Sig mySig
open import Syntax mySig
open import Subst mySig
open import OpSem mySig
open import Denotational mySig

-- σ is irrelevant to g's body (it ignores its argument), so pick UnitTy.
-- g = λ_. snd(pair(loss(vgnd 1), val(vgnd 2)))  :  LC ∅ UnitTy []
gBody : (∅ , UnitTy) ⊢ Loss ! []
gBody = snd (pair (lossE (val (vgnd 1))) (val (vgnd 2)))

g : LC ∅ UnitTy []
g = vabs gBody

e1 : ∅ ⊢ UnitTy ! []
e1 = val (vgnd tt)

ρ0 : Env ∅
ρ0 ()

-- LHS of Lemma 7.5(1): Esem(e1 ▶ g)(ρ)(γ1), for an arbitrary γ1 (here the
-- canonical zero one -- the equation is claimed to hold for *every* γ1).
lhs : Ŵ [] ⟦ Loss ⟧
lhs = Esem (thenE ⊆ᵉ-refl e1 g) ρ0 (λ _ → η̂ tt)

-- RHS of Lemma 7.5(1): collect(R̂-of(Esem e1 ρ) ⌊g⌋).
Gg : ⟦ UnitTy ⟧ → Ŵ [] ⊤
Gg a = widenŴ ⊆ᵉ-refl (Lsem g ρ0 a)

rhs : Ŵ [] ⟦ Loss ⟧
rhs = collect (R̂-of (Esem e1 ρ0) Gg)

-- Hand computation predicts lhs = leaf 1 2 (root loss 1 = the *discarded*
-- lossE's own contribution, payload 2 = the kept `snd` component), while
-- rhs = leaf 0 2 (the discarded lossE contribution is lost -- `collapse`
-- only ever recovers the payload sitting at the point `Lsem` looks at,
-- never the loss accumulated *before* reaching it). Check both by `refl`.
lhs-check : lhs ≡ leaf 1 2
lhs-check = refl

rhs-check : rhs ≡ leaf 0 2
rhs-check = refl

-- So if Lemma 7.5(1)/B.5(1) held unconditionally, lhs ≡ rhs, i.e.
-- leaf 1 2 ≡ leaf 0 2 -- refuted by feeding that into a discriminator.
leaf-loss : Ŵ [] ⟦ Loss ⟧ → ℕ
leaf-loss (leaf r x)     = r
leaf-loss (node () op r o κ)

lemma-B5-1-general-is-false : lhs ≡ rhs → (1 ≡ 0)
lemma-B5-1-general-is-false eq = Relation.Binary.PropositionalEquality.cong leaf-loss eq
  where import Relation.Binary.PropositionalEquality

-- Made airtight: assuming Lemma 7.5(1)/B.5(1) held for this g yields ⊥.
lemma-B5-1-general-refuted : (lhs ≡ rhs) → ⊥
lemma-B5-1-general-refuted eq with lemma-B5-1-general-is-false eq
... | ()
