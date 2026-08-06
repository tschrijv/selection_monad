-- A minimal instantiation of the whole development, to check that
-- Domains/Syntax/Subst/OpSem/Denotational actually apply to a concrete
-- signature end to end. Mirrors the paper's own running NDet example
-- (§2.2/4.1): a single nullary-parameter effect with one operation
-- `decide : () → Bool`.
module Example where

open import Domains
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-identityˡ; +-identityʳ; +-assoc; +-comm)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Nullary using (Dec; yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- One effect label, one operation.
data Eff : Set where
  ndet : Eff

_≟ᵉ'_ : (ℓ1 ℓ2 : Eff) → Dec (ℓ1 ≡ ℓ2)
ndet ≟ᵉ' ndet = yes refl

data Bse : Set where
  bool : Bse

⟦_⟧ᵇ' : Bse → Set
⟦_⟧ᵇ' bool = Bool

data Op' : Eff → Set where
  decide : Op' ndet

module GT = Ground Bse ⟦_⟧ᵇ' ℕ

out' in′' : ∀ {ℓ} → Op' ℓ → GT.GTy
out' decide = GT.unit
in′' decide = GT.base bool

mySig : Sig
mySig = record
  { Effect  = Eff
  ; _≟ᵉ_    = _≟ᵉ'_
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

-- ε = [ndet] : decide is available.
εNdet : EffCxt
εNdet = ndet ∷ []

m∈εNdet : ndet ∈ εNdet
m∈εNdet = here Relation.Binary.PropositionalEquality.refl
  where import Relation.Binary.PropositionalEquality

-- pgm = decide() : Bool ! [ndet]
pgm : ∅ ⊢ gnd (base bool) ! εNdet
pgm = opE m∈εNdet decide (val (vgnd tt))

-- A handler for ndet with parameter type unit that always resumes with
-- `true`, discarding the choice continuation (a trivial, non-choosing
-- handler, just to exercise the construction).
hAlways : Handler ∅ ndet unit (gnd (base bool)) (gnd (base bool)) []
-- z : (par, out, choiceCont, delimCont) -- Z is delimCont (innermost).
clause hAlways decide = app (val (vvar Z)) (pair (val (vvar (S (S (S Z))))) (val (vgnd true)))
ret    hAlways        = val (vvar Z)

-- with hAlways from () handle pgm : Bool ! []
handled : ∅ ⊢ gnd (base bool) ! []
handled = handleE hAlways (val (vgnd tt)) pgm

-- The denotational semantics of the whole program (a genuine Ŝ [] Bool
-- value), and its loss-function semantics against the zero continuation.
handledSem : Ŝ [] Bool
handledSem = Esem handled (λ ())

handledResult : Ŵ [] Bool
handledResult = handledSem (λ _ → η̂ 0#)

-- A single small-step reduction: decide()'s argument (()) is already a
-- value, so the whole program is stuck on `decide` under the empty
-- continuation context, ready for rule R5 once wrapped in a handler; here
-- we instead just exercise rule (R6) directly on a trivial handled value.
handledValueStep : (g : LC ∅ (gnd (base bool)) []) → g ⊢ handleE hAlways (val (vgnd tt)) (val (vgnd false)) -[ 0 ]→ val (vgnd false)
handledValueStep g = R6 hAlways (vgnd tt) (vgnd false)
