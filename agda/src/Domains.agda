-- Signature of the object language, and the "hat" denotational domains
-- (Ŵ_ε, Ŝ_ε) from paper.tex §3 -- the alternative construction obtained by
-- applying the free-monad transformer to the writer monad, i.e. the monad
-- realised by `Sel r e a = FreeT e (Writer r)` in the companion Haskell
-- development.
--
-- SCOPING DECISION. The source note (paper.tex) inherits, unchanged, the
-- original paper's mutual recursion between the semantics of *types* and
-- the effect-indexed monads S_ε/W_ε/F_ε, justified there by an assumed
-- well-ordering of effect labels (§3.4 / Appendix A.4 of the arXiv paper).
-- Formalising that induction-recursion in full generality needs a further,
-- undocumented (even in the source) well-founded recursion on a
-- (level, size) measure once operations are allowed themselves to take
-- *higher-order* (effectful-function-typed) arguments/results -- see the
-- Spike.agda / Spike2.agda scratch files for the failed naive attempt and
-- the diagnosis (Agda's strict-positivity checker correctly refuses it: a
-- function-typed operation argument makes W_ε occur contravariantly inside
-- its own recursive unfolding). Every worked example in the paper (decide,
-- max, optimize, ...) has *ground* (first-order) operation argument/result
-- types, so we restrict operation signatures to ground types (`GTy` below,
-- with no `_⇒_!_`). This makes Ŵ_ε/Ŝ_ε an ordinary, non-mutual
-- inductive-recursive definition (Ŵ never needs the general type semantics
-- ⟦_⟧, only the ground one ⟦_⟧ᴳ), while the object language itself remains
-- fully higher-order: expressions and values may still have arbitrary
-- function types, values may be passed to and returned from handlers, etc.
-- Lifting this restriction is future work, exactly as the original paper's
-- well-foundedness assumption is left as a standing hypothesis rather than
-- discharged for a specific signature.
module Domains where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec)
open import Data.Unit using (⊤; tt)

-- ---------------------------------------------------------------------
-- Ground (first-order) types: what operations/primitive functions take
-- and return. Parametrised by the base types and the loss monoid R.
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
-- General types (of the core fragment: no sums/nat/list, cf. paper.tex §7
-- which restricts the ported proofs the same way and calls the rest
-- "routine, entirely orthogonal to the swap").
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
-- §3: the Ŵ_ε / Ŝ_ε construction, given a concrete (ground-typed) set of
-- operations, and the general type semantics ⟦_⟧ built from Ŝ.
-- ---------------------------------------------------------------------

module WHat (Effect Base : Set) (⟦_⟧ᵇ : Base → Set) (R : Set) (0# : R) (_+_ : R → R → R)
            (Op : Effect → Set)
            (out in′ : ∀ {ℓ} → Op ℓ → Types.GTy Effect Base ⟦_⟧ᵇ R)
            where

  open Types Effect Base ⟦_⟧ᵇ R public

  -- §3.1 The carrier Ŵ_ε: the least Y with
  --   Y = R × (X + Σ_{ℓ∈ε, op:out→ℓ→in, 0<i≤ε(ℓ)} ⟦out⟧ × Y^⟦in⟧)
  -- Elements are written (r, ι₁ x) [leaf] or (r, ι₂((ℓ,op,i),(o,κ))) [node];
  -- here the membership proof ℓ∈ε plays the role of the index i.
  data Ŵ (ε : EffCxt) (X : Set) : Set where
    leaf : R → X → Ŵ ε X
    node : ∀ {ℓ} → ℓ ∈ ε → (op : Op ℓ) → R → ⟦ out op ⟧ᴳ → (⟦ in′ op ⟧ᴳ → Ŵ ε X) → Ŵ ε X

  -- Functorial action (not in the source note explicitly, but the evident
  -- and harmless map used e.g. to relate `collect` to `collectX`).
  mapŴ : ∀ {ε X Y} → (X → Y) → Ŵ ε X → Ŵ ε Y
  mapŴ f (leaf r x)          = leaf r (f x)
  mapŴ f (node m op r o κ)   = node m op r o (λ a → mapŴ f (κ a))

  -- Widening along an inclusion of effect contexts, i.e. the inclusion
  -- R̂_ε ↪ R̂_{ε'} (for ε⊆ε') that §5 leaves implicit in the handler
  -- semantics formula, and that Correct.hs realises as `transFreeT
  -- RightEff`.
  widenŴ : ∀ {ε ε' X} → ε ⊆ᵉ ε' → Ŵ ε X → Ŵ ε' X
  widenŴ sub (leaf r x)        = leaf r x
  widenŴ sub (node m op r o κ) = node (sub m) op r o (λ a → widenŴ sub (κ a))

  -- §3.1 unit, and the additive action r · (r₀, n) = (r + r₀, n), i.e. `tell`.
  η̂ : ∀ {ε X} → X → Ŵ ε X
  η̂ x = leaf 0# x

  tell : ∀ {ε X} → R → Ŵ ε X → Ŵ ε X
  tell r (leaf r₀ x)        = leaf (r + r₀) x
  tell r (node m op r₀ o κ) = node m op (r + r₀) o κ

  -- §3.2 Free layered ε-algebras: (Y, ψ, act) with ψ an ε-algebra structure
  -- and act : R → Y → Y an additive action, with *no* commutation required
  -- between them (this is exactly what the swap gives up, cf. §3.3).
  record LayeredAlg (ε : EffCxt) (Y : Set) : Set where
    field
      ψ   : ∀ {ℓ} → ℓ ∈ ε → (op : Op ℓ) → ⟦ out op ⟧ᴳ → (⟦ in′ op ⟧ᴳ → Y) → Y
      act : R → Y → Y

  -- The unique homomorphic extension f†Ŵ of f : X → Y over a layered algebra.
  ext̂ : ∀ {ε X Y} → LayeredAlg ε Y → (X → Y) → Ŵ ε X → Y
  ext̂ A f (leaf r x)        = LayeredAlg.act A r (f x)
  ext̂ A f (node m op r o κ) = LayeredAlg.act A r (LayeredAlg.ψ A m op o (λ a → ext̂ A f (κ a)))

  -- Ŵ_ε(X) is itself a layered ε-algebra (φ̂ with own-loss 0, action = tell);
  -- the Kleisli extension (bind, "let_Ŵε") is the homomorphic extension over it.
  Ŵ-alg : ∀ {ε X} → LayeredAlg ε (Ŵ ε X)
  Ŵ-alg = record { ψ = (λ m op o κ → node m op 0# o κ) ; act = tell }

  bind̂ : ∀ {ε X Y} → Ŵ ε X → (X → Ŵ ε Y) → Ŵ ε Y
  bind̂ w f = ext̂ Ŵ-alg f w

  -- §3.3 loss, commutativity, and what changes: tell (above), censor, and
  -- the collect/collectX/bump family.

  -- censor : recursively zero every recorded loss, leaving shape/leaves untouched.
  censor : ∀ {ε X} → Ŵ ε X → Ŵ ε X
  censor (leaf r x)        = leaf 0# x
  censor (node m op r o κ) = node m op 0# o (λ a → censor (κ a))

  -- bump_r : add r into the recorded total at every leaf beneath the current node.
  bump : ∀ {ε X} → R → Ŵ ε (X × R) → Ŵ ε (X × R)
  bump r (leaf r₀ (x , s))  = leaf r₀ (x , r + s)
  bump r (node m op r₀ o κ) = node m op r₀ o (λ a → bump r (κ a))

  -- collectX : pair each leaf value with the total accumulated loss on its
  -- path (matching Haskell's `listen`), zeroing every node's own recorded
  -- loss along the way.
  collectX : ∀ {ε X} → Ŵ ε X → Ŵ ε (X × R)
  collectX (leaf r x)        = leaf 0# (x , r)
  collectX (node m op r o κ) = node m op 0# o (λ a → bump r (collectX (κ a)))

  -- collect : Ŵ_ε(1) → Ŵ_ε(R), summing all losses along each root-to-leaf
  -- path into that leaf's now R-valued payload (matching `triangle`).
  collect : ∀ {ε} → Ŵ ε ⊤ → Ŵ ε R
  collect (leaf r tt)       = leaf 0# r
  collect (node m op r o κ) = node m op r o (λ a → collect (κ a))
  -- (The source note also asserts collect ≡ mapŴ proj₂ ∘ collectX; that
  -- equation is a fact about these definitions, not needed to state them,
  -- and is left for the proof pass.)

  -- §3.4 The selection monad Ŝ_ε(X) = (X → R̂_ε) → Ŵ_ε(X), R̂_ε := Ŵ_ε(1).
  Ŝ : EffCxt → Set → Set
  Ŝ ε X = (X → Ŵ ε ⊤) → Ŵ ε X

  R̂ : EffCxt → Set
  R̂ ε = Ŵ ε ⊤

  η̂ˢ : ∀ {ε X} → X → Ŝ ε X
  η̂ˢ x = λ γ → η̂ x

  -- R̂_ε(F ∣ γ) := γ†Ŵ(F(γ)), the loss associated to a selection function.
  R̂-of : ∀ {ε Y} → Ŝ ε Y → (Y → R̂ ε) → R̂ ε
  R̂-of F γ = ext̂ Ŵ-alg γ (F γ)

  -- Kleisli extension of Ŝ (equation (6) of the source note).
  bind̂ˢ : ∀ {ε X Y} → (X → Ŝ ε Y) → Ŝ ε X → Ŝ ε Y
  bind̂ˢ f F = λ γ → bind̂ (F (λ x → R̂-of (f x) γ)) (λ x → f x γ)

  -- Ŝ_ε(X) is an ε-algebra via φ̂^X.
  φ̂ˢ : ∀ {ε X ℓ} → ℓ ∈ ε → (op : Op ℓ) → ⟦ out op ⟧ᴳ → (⟦ in′ op ⟧ᴳ → Ŝ ε X) → Ŝ ε X
  φ̂ˢ m op o f = λ γ → node m op 0# o (λ a → f a γ)

  -- §2 / Fig. 8 (hat-version): semantics of general types.
  ⟦_⟧ : Ty → Set
  ⟦ gnd γ ⟧      = ⟦ γ ⟧ᴳ
  ⟦ σ `× τ ⟧     = ⟦ σ ⟧ × ⟦ τ ⟧
  ⟦ σ ⇒ τ ! ε ⟧  = ⟦ σ ⟧ → Ŝ ε ⟦ τ ⟧

-- ---------------------------------------------------------------------
-- The bundled signature record used by all downstream modules.
-- ---------------------------------------------------------------------

record Sig : Set₁ where
  field
    Effect  : Set
    -- Decidable equality on effect labels. Needed so handlerΨ (Denotational.
    -- agda) can dispatch a stuck operation to "is this MY label" rather than
    -- "does this WITNESS happen to point at the freshly-introduced slot" --
    -- the latter is what made theorem-B9-R5-gen false as originally stated
    -- (EffCxt is an explicit multiset, so ℓ ∈ ε can have multiple, position-
    -- distinct witnesses for the same label; dispatch must depend only on ℓ
    -- itself, not on which witness was supplied).
    _≟ᵉ_    : (ℓ1 ℓ2 : Effect) → Dec (ℓ1 ≡ ℓ2)
    Base    : Set
    ⟦_⟧ᵇ    : Base → Set
    R       : Set
    0#      : R
    _+_     : R → R → R
    -- R is a commutative monoid (§2.1 of the arXiv paper: "We assume R is
    -- a commutative monoid (R,+,0)"). Not needed to *state* the Ŵ_ε/Ŝ_ε
    -- construction (Domains.agda proper), only to *prove* things about it,
    -- so these were omitted from the first, definitions-only pass and are
    -- added now that Proofs.agda needs them.
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

  open WHat Effect Base ⟦_⟧ᵇ R 0# _+_ Op out in′ public
