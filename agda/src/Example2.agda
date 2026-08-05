-- A second minimal signature instance, mirroring Example.agda but with
-- TWO distinct effect labels (ndetA, ndetB), each with one operation
-- `decide : () → Bool`. Needed specifically to test k1v-match's own
-- S-handleB case: R5's own `¬ Handles k ℓ` precondition forbids a
-- nested handler h2 from sharing the OUTER handler h's own label, so
-- testing "k embeds a DIFFERENT handler h2 via S-handleB" genuinely
-- needs two distinct labels -- Example.agda's own single-label ndet
-- can't host this scenario at all.
module Example2 where

open import Domains
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityˡ; +-identityʳ; +-assoc; +-comm)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Eff2 : Set where
  ndetA ndetB : Eff2

_≟ᵉ2_ : (ℓ1 ℓ2 : Eff2) → Dec (ℓ1 ≡ ℓ2)
ndetA ≟ᵉ2 ndetA = yes refl
ndetA ≟ᵉ2 ndetB = no (λ ())
ndetB ≟ᵉ2 ndetA = no (λ ())
ndetB ≟ᵉ2 ndetB = yes refl

data Bse2 : Set where
  bool2 : Bse2

⟦_⟧ᵇ2 : Bse2 → Set
⟦_⟧ᵇ2 bool2 = Bool

data Op2 : Eff2 → Set where
  decideA : Op2 ndetA
  decideB : Op2 ndetB

module GT2 = Ground Bse2 ⟦_⟧ᵇ2 ℕ

out2 in′2 : ∀ {ℓ} → Op2 ℓ → GT2.GTy
out2 decideA = GT2.unit
out2 decideB = GT2.unit
in′2 decideA = GT2.base bool2
in′2 decideB = GT2.base bool2

mySig2 : Sig
mySig2 = record
  { Effect  = Eff2
  ; _≟ᵉ_    = _≟ᵉ2_
  ; Base    = Bse2
  ; ⟦_⟧ᵇ    = ⟦_⟧ᵇ2
  ; R       = ℕ
  ; 0#      = 0
  ; _+_     = _+_
  ; +-identityˡ = +-identityˡ
  ; +-identityʳ = +-identityʳ
  ; +-assoc     = +-assoc
  ; +-comm      = +-comm
  ; PrimFun = λ _ _ → ⊥
  ; ⟦_⟧f    = λ ()
  ; Op      = Op2
  ; out     = out2
  ; in′     = in′2
  }
