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
open import Relation.Binary.PropositionalEquality using (_≡_; cong; trans; sym; refl)
open import Relation.Nullary using (Dec)
open import Data.Unit using (⊤; tt)
open import Axiom.Extensionality.Propositional using (Extensionality)

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
  Ŝ ε X = (X → Ŵ ε R) → Ŵ ε X

  R̂ : EffCxt → Set
  R̂ ε = Ŵ ε R

  η̂ˢ : ∀ {ε X} → X → Ŝ ε X
  η̂ˢ x = λ γ → η̂ x

  -- R̂_ε(F ∣ γ) := γ†Ŵ(F(γ)), the loss associated to a selection function.
  R̂-of : ∀ {ε Y} → Ŝ ε Y → (Y → R̂ ε) → R̂ ε
  R̂-of F γ = 
    bind̂ (collectX (F γ)) (λ{ (a , r1) → mapŴ (r1 +_) (γ a) })

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

-- ---------------------------------------------------------------------
-- Monad laws for Ŵ_ε (bind̂'s left/right unit and associativity).
-- Ported from Proofs.agda, where they originally lived -- moved here
-- since they are facts about Ŵ_ε itself (§3.2's bind̂/η̂), not about the
-- object language Proofs.agda is otherwise concerned with. They need R's
-- monoid laws (+-identityˡ/+-identityʳ/+-assoc), which WHat's own
-- parameters deliberately omit (see the SCOPING DECISION note at the top
-- of this file), so this module takes a full Sig instead.
-- ---------------------------------------------------------------------

module ŴMonad (Sg : Sig) where
  open Sig Sg

  postulate
    funext : ∀ {a b} → Extensionality a b

  -- tell(r) then tell(s) is tell(r+s): the additive action law of §3.2,
  -- specialised to Ŵ's own native action.
  tell-+ : ∀ {ε X} (r s : R) (w : Ŵ ε X) → tell (r + s) w ≡ tell r (tell s w)
  tell-+ r s (leaf r₀ x)        = cong (λ z → leaf z x) (+-assoc r s r₀)
  tell-+ r s (node m op r₀ o κ) = cong (λ z → node m op z o κ) (+-assoc r s r₀)

  tell-0 : ∀ {ε X} (w : Ŵ ε X) → tell 0# w ≡ w
  tell-0 (leaf r x)        = cong (λ z → leaf z x) (+-identityˡ r)
  tell-0 (node m op r o κ) = cong (λ z → node m op z o κ) (+-identityˡ r)

  -- tell commutes with bind̂'s own binding: tell r only ever touches the
  -- root, so bind̂'s ext̂ and tell's root-update commute regardless of what
  -- K does with the leaf value.
  tell-bind̂-comm : ∀ {ε X Y} (r : R) (w : Ŵ ε X) (K : X → Ŵ ε Y) → bind̂ (tell r w) K ≡ tell r (bind̂ w K)
  tell-bind̂-comm r (leaf r₀ x) K        = tell-+ r r₀ (K x)
  tell-bind̂-comm r (node m op r₀ o κ) K = tell-+ r r₀ (node m op 0# o (λ a → bind̂ (κ a) K))

  -- Left unit: bind̂ (η̂ x) f = f x. Immediate, since η̂ x = leaf 0# x and
  -- bind̂'s action at a leaf is exactly tell.
  bind̂-unitˡ : ∀ {ε X Y} (x : X) (f : X → Ŵ ε Y) → bind̂ (η̂ x) f ≡ f x
  bind̂-unitˡ x f = tell-0 (f x)

  -- Right unit: bind̂ w η̂ = w.
  bind̂-unitʳ : ∀ {ε X} (w : Ŵ ε X) → bind̂ w η̂ ≡ w
  bind̂-unitʳ (leaf r x)        = cong (λ z → leaf z x) (+-identityʳ r)
  bind̂-unitʳ (node m op r o κ) =
    trans (cong (λ z → node m op z o (λ a → bind̂ (κ a) η̂)) (+-identityʳ r))
          (cong (node m op r o) (funext (λ a → bind̂-unitʳ (κ a))))

  -- Associativity: bind̂ (bind̂ w f) g = bind̂ w (λ x → bind̂ (f x) g).
  bind̂-assoc : ∀ {ε X Y Z} (w : Ŵ ε X) (f : X → Ŵ ε Y) (g : Y → Ŵ ε Z)
             → bind̂ (bind̂ w f) g ≡ bind̂ w (λ x → bind̂ (f x) g)
  bind̂-assoc (leaf r x)        f g = tell-bind̂-comm r (f x) g
  bind̂-assoc (node m op r o κ) f g =
    trans (tell-bind̂-comm r (node m op 0# o (λ a → bind̂ (κ a) f)) g)
          (cong (tell r) (trans (tell-0 _) (cong (node m op 0# o) (funext (λ a → bind̂-assoc (κ a) f g)))))

  -- ---------------------------------------------------------------------
  -- bump/collectX/mapŴ interchange laws (ported from Proofs.agda, where
  -- they originally lived -- needed here now that R̂-of routes through
  -- collectX/mapŴ instead of a plain bind̂, so bindˢ-assoc's proof below
  -- needs them too).
  -- ---------------------------------------------------------------------

  bump-fusion : ∀ {ε X} (r s : R) (T : Ŵ ε (X × R)) → bump r (bump s T) ≡ bump (r + s) T
  bump-fusion r s (leaf r₀ (x , y))  = cong (λ z → leaf r₀ (x , z)) (sym (+-assoc r s y))
  bump-fusion r s (node m op r₀ o κ) = cong (node m op r₀ o) (funext (λ a → bump-fusion r s (κ a)))

  bump-0 : ∀ {ε X} (T : Ŵ ε (X × R)) → bump 0# T ≡ T
  bump-0 (leaf r₀ (x , y))  = cong (λ z → leaf r₀ (x , z)) (+-identityˡ y)
  bump-0 (node m op r₀ o κ) = cong (node m op r₀ o) (funext (λ a → bump-0 (κ a)))

  bump-collectX-comm : ∀ {ε X} (r : R) (S : Ŵ ε X) → bump r (collectX S) ≡ collectX (tell r S)
  bump-collectX-comm r (leaf r₀ x)        = refl
  bump-collectX-comm r (node m op r₀ o κ) = cong (node m op 0# o) (funext (λ a → bump-fusion r r₀ (collectX (κ a))))

  bump-shift : ∀ {ε X Y} (bumpAmt : R) (T : Ŵ ε (X × R)) (h : X → R → Ŵ ε Y)
    → bind̂ (bump bumpAmt T) (λ { (a , r1) → h a r1 }) ≡ bind̂ T (λ { (a , r1) → h a (bumpAmt + r1) })
  bump-shift bumpAmt (leaf r₀ (x , y)) h = refl
  bump-shift bumpAmt (node m op r₀ o κ) h =
    cong (tell r₀) (cong (node m op 0# o) (funext (λ a → bump-shift bumpAmt (κ a) h)))

  tell-mapŴ-comm : ∀ {ε X Y} (r : R) (f : X → Y) (W : Ŵ ε X) → tell r (mapŴ f W) ≡ mapŴ f (tell r W)
  tell-mapŴ-comm r f (leaf r₀ x)        = refl
  tell-mapŴ-comm r f (node m op r₀ o κ) = refl

  mapŴ-∘ : ∀ {ε X Y Z} (f : Y → Z) (g : X → Y) (W : Ŵ ε X) → mapŴ f (mapŴ g W) ≡ mapŴ (λ x → f (g x)) W
  mapŴ-∘ f g (leaf r x)        = refl
  mapŴ-∘ f g (node m op r o κ) = cong (node m op r o) (funext (λ a → mapŴ-∘ f g (κ a)))

  bind̂-mapŴ-after : ∀ {ε X Y Z} (T : Ŵ ε X) (k : X → Ŵ ε Y) (f : Y → Z) → bind̂ T (λ x → mapŴ f (k x)) ≡ mapŴ f (bind̂ T k)
  bind̂-mapŴ-after (leaf r x) k f = tell-mapŴ-comm r f (k x)
  bind̂-mapŴ-after (node m op r o κ) k f =
    trans (cong (tell r) (cong (node m op 0# o) (funext (λ a → bind̂-mapŴ-after (κ a) k f))))
          (tell-mapŴ-comm r f (node m op 0# o (λ a → bind̂ (κ a) k)))

  collectX-bind̂-fusion-gen : ∀ {ε X Y} (off : R) (w : Ŵ ε X) (f : X → Ŵ ε Y)
    → bind̂ (collectX w) (λ { (a , r1) → bump (off + r1) (collectX (f a)) }) ≡ bump off (collectX (bind̂ w f))
  collectX-bind̂-fusion-gen off (leaf r x) f =
    trans (tell-0 _) (trans (sym (bump-fusion off r (collectX (f x)))) (cong (bump off) (bump-collectX-comm r (f x))))
  collectX-bind̂-fusion-gen off (node m op r o κ) f = trans lhsEq (sym rhsEq)
    where
    lhsEq : bind̂ (collectX (node m op r o κ)) (λ { (a , r1) → bump (off + r1) (collectX (f a)) })
          ≡ node m op 0# o (λ a → bump (off + r) (collectX (bind̂ (κ a) f)))
    lhsEq = trans (tell-0 _)
                  (cong (node m op 0# o) (funext (λ a →
                    trans (bump-shift r (collectX (κ a)) (λ a' r1 → bump (off + r1) (collectX (f a'))))
                          (trans (cong (bind̂ (collectX (κ a)))
                                       (funext (λ { (a' , r1) → cong (λ z → bump z (collectX (f a'))) (sym (+-assoc off r r1)) })))
                                 (collectX-bind̂-fusion-gen (off + r) (κ a) f)))))
    rhsEq : bump off (collectX (bind̂ (node m op r o κ) f))
          ≡ node m op 0# o (λ a → bump (off + r) (collectX (bind̂ (κ a) f)))
    rhsEq = trans (cong (bump off) (sym (bump-collectX-comm r (node m op 0# o (λ a → bind̂ (κ a) f)))))
                  (cong (node m op 0# o) (funext (λ a →
                    trans (cong (bump off) (bump-fusion r 0# (collectX (bind̂ (κ a) f))))
                          (trans (bump-fusion off (r + 0#) (collectX (bind̂ (κ a) f)))
                                 (cong (λ z → bump z (collectX (bind̂ (κ a) f))) (cong (off +_) (+-identityʳ r)))))))

  collectX-bind̂-fusion : ∀ {ε X Y} (w : Ŵ ε X) (f : X → Ŵ ε Y)
    → collectX (bind̂ w f) ≡ bind̂ (collectX w) (λ { (a , r1) → bump r1 (collectX (f a)) })
  collectX-bind̂-fusion w f =
    trans (sym (bump-0 _))
          (trans (sym (collectX-bind̂-fusion-gen 0# w f))
                 (cong (bind̂ (collectX w)) (funext (λ { (a , r1) → cong (λ z → bump z (collectX (f a))) (+-identityˡ r1) }))))

-- ---------------------------------------------------------------------
-- Monad laws for Ŝ_ε (§3.4's selection monad): bind̂ˢ's left/right unit
-- and associativity. Ported from/extending Proofs.agda, where only the
-- left unit law (bindˢ-unitˡ) previously existed -- the right unit and
-- associativity laws below are new. All three reduce to ŴMonad's own
-- bind̂ laws once R̂-of/η̂ˢ are unfolded, since bind̂ˢ is exactly bind̂
-- wrapped in a loss-continuation (γ) abstraction.
-- ---------------------------------------------------------------------

module ŜMonad (Sg : Sig) where
  open Sig Sg
  open ŴMonad Sg

  -- Left unit: bind̂ˢ f (η̂ˢ x) = f x. η̂ˢ x's own continuation-independence
  -- (η̂ˢ x γ = η̂ x for every γ) reduces bind̂ˢ's outer bind̂ to a tell 0#
  -- at the root, discharged by tell-0.
  bindˢ-unitˡ : ∀ {ε X Y} (f : X → Ŝ ε Y) (x : X) → bind̂ˢ f (η̂ˢ x) ≡ f x
  bindˢ-unitˡ f x = funext (λ γ → tell-0 (f x γ))

  -- mapŴ (0# +_) is the identity -- mapŴ only ever touches leaf payloads,
  -- so no root/node-structure subtlety arises here at all. Needed below
  -- to show R̂-of (η̂ˢ x) γ ≡ γ x now that R̂-of routes through
  -- collectX/mapŴ instead of a plain bind̂.
  mapŴ-plus-0 : ∀ {ε} (T : Ŵ ε R) → mapŴ (0# +_) T ≡ T
  mapŴ-plus-0 (leaf r x)        = cong (leaf r) (+-identityˡ x)
  mapŴ-plus-0 (node m op r o κ) = cong (node m op r o) (funext (λ a → mapŴ-plus-0 (κ a)))

  -- Right unit: bind̂ˢ η̂ˢ F = F. R̂-of (η̂ˢ x) γ = bind̂ (collectX (η̂ x))
  -- (λ(a,r1)→mapŴ(r1+_)(γa)), which computes (leaf case, r1=0#) to
  -- tell 0# (mapŴ (0#+_) (γ x)) ≡ γ x via tell-0/mapŴ-plus-0, so the
  -- selection-function argument bind̂ˢ passes to F collapses back to γ
  -- itself; what remains is exactly bind̂'s own right unit law.
  bindˢ-unitʳ : ∀ {ε X} (F : Ŝ ε X) → bind̂ˢ η̂ˢ F ≡ F
  bindˢ-unitʳ F = funext (λ γ →
    trans (cong (λ h → bind̂ (F h) η̂) (funext (λ x → trans (tell-0 _) (mapŴ-plus-0 (γ x)))))
          (bind̂-unitʳ (F γ)))

  -- Associativity: bind̂ˢ g (bind̂ˢ f F) = bind̂ˢ (λ x → bind̂ˢ g (f x)) F.
  -- Both sides unfold to a `bind̂ (F h) κ` for the same continuation κ (the
  -- OUTER bind̂-assoc, unaffected by R̂-of's own redefinition); what remains
  -- is R̂-of(f x)ψ ≡ R̂-of(bind̂ˢ g (f x))γ for every x. Now that R̂-of routes
  -- through collectX/mapŴ (not a plain bind̂), BOTH sides of that further
  -- reduce to the SAME normal form -- bind̂ (collectX (f x ψ)) (λ(y,r1') →
  -- bind̂ (collectX (g y γ)) (λ(a,r1) → mapŴ ((r1'+r1)+_) (γ a))) -- via
  -- collectX-bind̂-fusion/bind̂-assoc/bump-shift on one side and
  -- bind̂-mapŴ-after/mapŴ-∘/+-assoc on the other, so no new axioms.
  bindˢ-assoc : ∀ {ε X Y Z} (F : Ŝ ε X) (f : X → Ŝ ε Y) (g : Y → Ŝ ε Z)
              → bind̂ˢ g (bind̂ˢ f F) ≡ bind̂ˢ (λ x → bind̂ˢ g (f x)) F
  bindˢ-assoc {ε} {X} {Y} {Z} F f g = funext lemma
    where
    lemma : ∀ γ → bind̂ˢ g (bind̂ˢ f F) γ ≡ bind̂ˢ (λ x → bind̂ˢ g (f x)) F γ
    lemma γ = trans (bind̂-assoc (F h) (λ x → f x ψ) m)
                     (cong (λ w → bind̂ w κ) (cong F (funext R̂-of-eq)))
      where
      ψ : Y → R̂ ε
      ψ y = R̂-of (g y) γ
      m : Y → Ŵ ε Z
      m y = g y γ
      h : X → R̂ ε
      h x = R̂-of (f x) ψ
      κ : X → Ŵ ε Z
      κ x = bind̂ (f x ψ) m

      R̂-of-eq : ∀ x → R̂-of (f x) ψ ≡ R̂-of (bind̂ˢ g (f x)) γ
      R̂-of-eq x = trans stepB (sym stepA)
        where
        inner : Y → R → Ŵ ε R
        inner y r1' = bind̂ (collectX (g y γ)) (λ { (a , r1) → mapŴ ((r1' + r1) +_) (γ a) })

        stepA : R̂-of (bind̂ˢ g (f x)) γ ≡ bind̂ (collectX (f x ψ)) (λ { (y , r1') → inner y r1' })
        stepA = trans (cong (λ w → bind̂ w (λ { (a , r1) → mapŴ (r1 +_) (γ a) })) (collectX-bind̂-fusion (f x ψ) m))
                      (trans (bind̂-assoc (collectX (f x ψ)) (λ { (y , r1') → bump r1' (collectX (m y)) }) (λ { (a , r1) → mapŴ (r1 +_) (γ a) }))
                             (cong (bind̂ (collectX (f x ψ)))
                                   (funext (λ { (y , r1') → bump-shift r1' (collectX (m y)) (λ a r1 → mapŴ (r1 +_) (γ a)) }))))

        stepB : R̂-of (f x) ψ ≡ bind̂ (collectX (f x ψ)) (λ { (y , r1') → inner y r1' })
        stepB = cong (bind̂ (collectX (f x ψ)))
                     (funext (λ { (y , r1') →
                       trans (sym (bind̂-mapŴ-after (collectX (g y γ)) (λ { (a , r1) → mapŴ (r1 +_) (γ a) }) (r1' +_)))
                             (cong (bind̂ (collectX (g y γ)))
                                   (funext (λ { (a , r1) →
                                     trans (mapŴ-∘ (r1' +_) (r1 +_) (γ a))
                                           (cong (λ h' → mapŴ h' (γ a)) (funext (λ w → sym (+-assoc r1' r1 w)))) }))) }))
