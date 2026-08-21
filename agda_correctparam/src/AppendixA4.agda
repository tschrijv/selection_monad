-- Appendix A.4 ("Termination"), source paper pages 32-37: the Tait-
-- style computability proof, rebuilt from its own opening definitions
-- onward. Split into its own module (importing OpSemProofs, itself
-- already fully proven/stable) purely for compile-cycle speed: Agda
-- caches an imported module's interface as long as ITS OWN source
-- hasn't changed, so editing this file alone -- which is where all of
-- this section's still-in-progress development happens -- no longer
-- forces a full recheck of OpSemProofs.agda's ~3300 lines on every
-- edit. theorem-A4-1/A4-2/A4-3/A4-4, big-step-unique, corollary-A5, and
-- everything else already proven before this section began stay in
-- OpSemProofs.agda, unchanged.
open import Domains using (Sig)

module AppendixA4 (Sg : Sig) where

open Sig Sg
open import Syntax Sg
open import Subst Sg
open import OpSem Sg
open import OpSemProofs Sg

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (ℕ; zero; suc; _⊔_; _<_; _≤_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; m≤m+n; m≤n+m; m≤n⇒m<n∨m≡n; ≤-trans; ⊔-monoˡ-≤)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
open import Induction.WellFounded using (Acc; acc; WfRec; WellFounded)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

-- ---------------------------------------------------------------------
-- labelsTy: e(σ)/e(ε), "the effect labels appearing in σ or ε" -- as an
-- EffCxt (a list; only membership in it is ever used, so no dedup/set
-- structure is needed). e(σ→τ!ε) = e(σ) ++ e(τ) ++ ε, matching the
-- paper's own e(σ→τ!ε) = e(σ)∪e(τ)∪(ε) exactly. e(gnd γ) = [] always --
-- GTy (out/in′'s own codomain, Domains.agda) has no constructor
-- mentioning Effect at all, so a ground type can never mention an
-- effect label, regardless of Sig.
--
-- Well-foundedness assumption: postulated exactly as the paper states
-- it (an ordering of effect labels under which every operation's own
-- argument/return-type labels come strictly before the operation's own
-- label), rather than exploiting that it's provable outright here: for
-- THIS specific Sig record, out/in′ (OpSem.agda's own Frame/op
-- machinery) return GTy specifically, so e(out op) and e(in′ op) are
-- always [], making the assumption's own antecedent vacuous -- but
-- postulating it generically keeps this development structurally
-- parallel to the source rather than leaning on that GTy-restriction as
-- a shortcut.
-- ---------------------------------------------------------------------

labelsTy : Ty → EffCxt
labelsTy (gnd γ)     = []
labelsTy (σ `× τ)     = labelsTy σ ++ labelsTy τ
labelsTy (σ ⇒ τ ! ε)  = labelsTy σ ++ labelsTy τ ++ ε

postulate
  effLevel    : Effect → ℕ
  effLevel-wf : ∀ {ℓ} (op : Op ℓ) {ℓ'} → ℓ' ∈ (labelsTy (gnd (out op)) ++ labelsTy (gnd (in′ op))) → effLevel ℓ' < effLevel ℓ

-- l(ε)/l(σ): the effect LEVEL of an effect context/type -- the max
-- (0 if none) of effLevel over every label appearing in it. levelTy
-- agrees with (levelEffCxt ∘ labelsTy) by construction (mirrors
-- labelsTy's own recursive structure exactly), so is given directly
-- rather than composed, to keep it computing in one pass.
levelEffCxt : EffCxt → ℕ
levelEffCxt []       = 0
levelEffCxt (ℓ ∷ εs) = effLevel ℓ ⊔ levelEffCxt εs

levelTy : Ty → ℕ
levelTy (gnd γ)     = 0
levelTy (σ `× τ)     = levelTy σ ⊔ levelTy τ
levelTy (σ ⇒ τ ! ε)  = levelTy σ ⊔ levelTy τ ⊔ levelEffCxt ε

-- |σ|: the paper's own type SIZE, "|σ→τ!ε| = 1+|σ|+|τ|+|ε|" -- |ε|
-- taken as ε's own length (the paper doesn't spell this choice out, but
-- it's the natural one, and all that's needed downstream is that |ε,ℓℓ|
-- > |ε|, which length gives directly).
sizeTy : Ty → ℕ
sizeTy (gnd γ)     = 1
sizeTy (σ `× τ)     = suc (sizeTy σ +ℕ sizeTy τ)
sizeTy (σ ⇒ τ ! ε)  = suc (sizeTy σ +ℕ sizeTy τ +ℕ length ε)

-- ---------------------------------------------------------------------
-- The measure m(-) (page 32): a lexicographic pair (level, size),
-- built via Data.Product.Relation.Binary.Lex.Strict's ×-Lex/
-- ×-wellFounded combinator over Data.Nat.Induction's own <-wellFounded
-- for each component -- ℕ's usual well-ordering, combined
-- lexicographically with itself.
--
-- The paper states FOUR separate formulas (m(v)=(l(σ),|σ|) for values;
-- m(g)=m(e)=(l(σ)⊔l(ε),|σ|), shared by loss continuations g:σ→loss!ε'
-- and general expressions e:σ!ε; and m(e)=(l(ε),1) for e:loss!ε
-- specifically) -- but the last is just the second formula specialised
-- at σ=Loss (l(Loss)=0 and |Loss|=1, since Loss=gnd loss is a ground
-- type), so only two formulas (mVal/mExpr below) are needed.
-- ---------------------------------------------------------------------

M : Set
M = ℕ × ℕ

_<M_ : M → M → Set
_<M_ = ×-Lex _≡_ _<_ _<_

<M-wellFounded : WellFounded _<M_
<M-wellFounded = ×-wellFounded <-wellFounded <-wellFounded

mVal : Ty → M
mVal σ = levelTy σ , sizeTy σ

mExpr : Ty → EffCxt → M
mExpr σ ε = levelTy σ ⊔ levelEffCxt ε , sizeTy σ

-- Every decrease lemma below combines a (weak) inequality on the level
-- component with a (strict) one on the size component -- exactly the
-- shape ≤×<⇒<M packages once and for all.
≤×<⇒<M : ∀ {a1 a2 b1 b2} → a1 ≤ a2 → b1 < b2 → (a1 , b1) <M (a2 , b2)
≤×<⇒<M a1≤a2 b1<b2 with m≤n⇒m<n∨m≡n a1≤a2
... | inj₁ a1<a2 = inj₁ a1<a2
... | inj₂ a1≡a2 = inj₂ (a1≡a2 , b1<b2)

-- Generic ⊔/+ bookkeeping for the (two- and three-way) sums levelTy/
-- sizeTy build at σ`×τ and σ⇒τ!ε.
a≤a⊔b⊔c : ∀ a b c → a ≤ a ⊔ b ⊔ c
a≤a⊔b⊔c a b c = ≤-trans (m≤m⊔n a b) (m≤m⊔n (a ⊔ b) c)

b≤a⊔b⊔c : ∀ a b c → b ≤ a ⊔ b ⊔ c
b≤a⊔b⊔c a b c = ≤-trans (m≤n⊔m a b) (m≤m⊔n (a ⊔ b) c)

bc≤a⊔b⊔c : ∀ a b c → b ⊔ c ≤ a ⊔ b ⊔ c
bc≤a⊔b⊔c a b c = ⊔-monoˡ-≤ c (m≤n⊔m a b)

a<suc[a+b] : ∀ a b → a < suc (a +ℕ b)
a<suc[a+b] a b = s≤s (m≤m+n a b)

b<suc[a+b] : ∀ a b → b < suc (a +ℕ b)
b<suc[a+b] a b = s≤s (m≤n+m b a)

a<suc[a+b+c] : ∀ a b c → a < suc (a +ℕ b +ℕ c)
a<suc[a+b+c] a b c = s≤s (≤-trans (m≤m+n a b) (m≤m+n (a +ℕ b) c))

b<suc[a+b+c] : ∀ a b c → b < suc (a +ℕ b +ℕ c)
b<suc[a+b+c] a b c = s≤s (≤-trans (m≤n+m b a) (m≤m+n (a +ℕ b) c))

-- The four places Computable's own value case (below) needs mVal to
-- strictly decrease: both components of a pair, and both the domain
-- and codomain of a function type (the codomain landing in mExpr, not
-- mVal, since it is used to justify a *expression's* computability,
-- τ,ε, not a further value's).
mVal-pair-decrease1 : ∀ σ τ → mVal σ <M mVal (σ `× τ)
mVal-pair-decrease1 σ τ = ≤×<⇒<M (m≤m⊔n (levelTy σ) (levelTy τ)) (a<suc[a+b] (sizeTy σ) (sizeTy τ))

mVal-pair-decrease2 : ∀ σ τ → mVal τ <M mVal (σ `× τ)
mVal-pair-decrease2 σ τ = ≤×<⇒<M (m≤n⊔m (levelTy σ) (levelTy τ)) (b<suc[a+b] (sizeTy σ) (sizeTy τ))

mVal-arrow-decrease-dom : ∀ σ τ ε → mVal σ <M mVal (σ ⇒ τ ! ε)
mVal-arrow-decrease-dom σ τ ε = ≤×<⇒<M (a≤a⊔b⊔c (levelTy σ) (levelTy τ) (levelEffCxt ε)) (a<suc[a+b+c] (sizeTy σ) (sizeTy τ) (length ε))

-- NB targets mVal τ, not mExpr τ ε: ComputableV-acc's own arrow case
-- (below) feeds this directly into a further ComputableV-acc τ call
-- (Acc _<M_ (mVal τ)), not into anything Acc-indexed by mExpr -- the
-- expression-level notions (ComputableE-at and everything built on it)
-- take their value-predicate as a plain, already-resolved parameter,
-- with no well-founded recursion of their own (see the comment above
-- GComputable). mExpr itself is not yet used anywhere in this file --
-- kept for when Lemma A.10's own handle-construct proof needs it, the
-- one place in the source where the level component genuinely drops
-- (ε,ℓ → ε).
mVal-arrow-decrease-cod : ∀ σ τ ε → mVal τ <M mVal (σ ⇒ τ ! ε)
mVal-arrow-decrease-cod σ τ ε = ≤×<⇒<M (b≤a⊔b⊔c (levelTy σ) (levelTy τ) (levelEffCxt ε)) (b<suc[a+b+c] (sizeTy σ) (sizeTy τ) (length ε))

-- ---------------------------------------------------------------------
-- Computability (page 32, clauses (1)-(4)).
--
-- GComputable is the paper's own G-computability (clause 2): an
-- inductively-defined ("least fixed point") property of an expression
-- e:σ!ε, relative to a value-computability predicate P (clause 2's own
-- implicit use of "computable value") and a set G of loss continuations
-- (of type g:σ→loss!ε' for varying ε'⊆ε). Both P and G are taken as
-- ORDINARY, externally-supplied parameters here -- not as further
-- well-founded-recursive calls -- exactly mirroring how the source
-- itself treats G-computability as parametric in an arbitrary G (Def.
-- on page 32: "for a set G ..."), and sidestepping any need to
-- interleave THIS recursion (over the operational semantics, an
-- ordinary strictly-positive structure -- the same "make it a
-- datatype" fix used for Eval earlier) with the Ty-measured one that
-- only ComputableV-acc below genuinely needs.
--
-- Mirrors Terminal/theorem-A4-1's own vocabulary directly: clause (2b)
-- (an unhandled operation call K[op(v)]) is stated with EXACTLY
-- Terminal's own terminalOp shape, and needs no separate "v:out(op) is
-- computable" hypothesis -- out(op)/in′(op) are always ground (GTy),
-- and ComputableV-acc's own (gnd γ) case (below) is unconditionally ⊤,
-- so that hypothesis would be vacuous.
-- ---------------------------------------------------------------------

data GComputable {σ ε} (P : Val ∅ σ → Set) (G : ∀ {εg} → εg ⊆ᵉ ε → LC ∅ σ εg → Set) : ∅ ⊢ σ ! ε → Set where
  gc-val   : ∀ {v} → P v → GComputable P G (val v)
  gc-stuck : ∀ {ℓ εop} {m : ℓ ∈ εop} {op : Op ℓ} {v : Val ∅ (gnd (out op))}
             {K : ContCxt ∅ (gnd (in′ op)) εop σ ε} (nh : ¬ Handles K ℓ)
           → (∀ {v1 : Val ∅ (gnd (in′ op))} → GComputable P G (plugK K (val v1)))
           → GComputable P G (plugK K (opE m op (val v)))
  -- Carries ¬ Terminal e explicitly (the source's own "e is not
  -- stuck", read here as "e cannot be Terminal", i.e. is neither a
  -- value nor an unhandled operation call -- both already have their
  -- own dedicated clauses above) -- not just decoration: every
  -- {g}-induction proof (Lemma A.6 onward) that needs to invert a step
  -- OUT OF a wrapped e (e.g. g₁⊢F[e]→e'' for a regular frame F) needs
  -- to rule out e ALSO being a value first (else the wrapping's own
  -- value-rule, e.g. R8 for glocalE, could equally apply), and a bare
  -- conditional ("if e steps, then...") is vacuously satisfiable by a
  -- value or a stuck e too, so would not let that inversion go through.
  gc-step  : ∀ {e} → ¬ Terminal e
           → (∀ {εg} {sub : εg ⊆ᵉ ε} {g : LC ∅ σ εg} → G sub g → ∀ {r e'} → _⊢_-[_]→_ {sub = sub} g e r e' → GComputable P G e')
           → GComputable P G e

-- R-computability (clause 3a): G-computable at Loss w.r.t. the
-- singleton set containing only the zero continuation at the SAME ε
-- (value-computability at Loss, a ground type, is unconditionally ⊤).
RComputable : ∀ {ε} → ∅ ⊢ Loss ! ε → Set
RComputable {ε} = GComputable {σ = Loss} {ε} (λ _ → ⊤) G₀
  where
  G₀ : ∀ {εg} → εg ⊆ᵉ ε → LC ∅ Loss εg → Set
  G₀ {εg} _ g = Σ (εg ≡ ε) (λ eq → subst (λ ε' → LC ∅ Loss ε') eq g ≡ zeroLC)

-- Loss-computability (clause 3b): g=λ^ε x:σ.e' is loss-computable if
-- e'[v/x] is R-computable for every P-computable v:σ. (Val∅(σ⇒Loss!ε)
-- is always vabs-shaped, per val-closed-abs -- the vvar case is
-- excluded via the impossible Γ=∅ variable, exactly as val-closed-abs
-- itself does.)
LossComputable : ∀ {σ ε} (P : Val ∅ σ → Set) → LC ∅ σ ε → Set
LossComputable P (vvar ())
LossComputable P (vabs e') = ∀ {v} → P v → RComputable (e' [ v ])

-- General expression computability (clause 4): e:σ!ε is computable if
-- it is L_σ,ε-computable, i.e. G-computable w.r.t. the set of ALL
-- loss-computable continuations g:σ→loss!ε' for any ε'⊆ε.
ComputableE-at : (σ : Ty) (ε : EffCxt) (P : Val ∅ σ → Set) → ∅ ⊢ σ ! ε → Set
ComputableE-at σ ε P = GComputable {σ} {ε} P (λ _ g → LossComputable P g)

-- Value computability (clause 1): by well-founded recursion on mVal
-- via Acc, so that the σ⇒τ!ε case's own reference to computability of
-- EXPRESSIONS at τ,ε (ComputableE-at, fed the SAME, already-in-hand
-- ComputableV-acc τ witness as its value-predicate P) is justified by
-- mVal-arrow-decrease-cod, exactly mirroring the source's own
-- justification for defining Computable by recursion on m(-) rather
-- than on σ's bare syntax.
ComputableV-acc : (σ : Ty) → Acc _<M_ (mVal σ) → Val ∅ σ → Set
ComputableV-acc (gnd γ)     _       v             = ⊤
ComputableV-acc (σ `× τ)    _       (vvar ())
ComputableV-acc (σ `× τ)    (acc rs) (vpair v1 v2) =
  ComputableV-acc σ (rs (mVal-pair-decrease1 σ τ)) v1 ×
  ComputableV-acc τ (rs (mVal-pair-decrease2 σ τ)) v2
ComputableV-acc (σ ⇒ τ ! ε) _       (vvar ())
ComputableV-acc (σ ⇒ τ ! ε) (acc rs) (vabs e)      =
  ∀ {v' : Val ∅ σ} → ComputableV-acc σ (rs (mVal-arrow-decrease-dom σ τ ε)) v'
                    → ComputableE-at τ ε (ComputableV-acc τ (rs (mVal-arrow-decrease-cod σ τ ε))) (e [ v' ])

ComputableV : (σ : Ty) → Val ∅ σ → Set
ComputableV σ = ComputableV-acc σ (<M-wellFounded (mVal σ))

ComputableE : (σ : Ty) (ε : EffCxt) → ∅ ⊢ σ ! ε → Set
ComputableE σ ε = ComputableE-at σ ε (ComputableV σ)

-- ---------------------------------------------------------------------
-- Two small reusable consequences of theorem-A4-1/theorem-A4-2, needed
-- throughout the {g}-/G/L/R-induction proofs below to invert a step out
-- of a wrapped source expression: ¬Terminal-of-step turns "e has a
-- step" into "e is not Terminal" for free, and step-det-with turns "a
-- CONCRETE step instance is known" into "any other step from the same
-- source agrees with it" (determinism, packaged for direct use rather
-- than re-deriving the cong/Σ-splitting dance at each use site).
-- ---------------------------------------------------------------------

¬Terminal-of-step : ∀ {Γ σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} {e e' : Γ ⊢ σ ! ε} {r : R}
                   → _⊢_-[_]→_ {sub = sub} g e r e' → ¬ Terminal e
¬Terminal-of-step stp term = theorem-A4-1 term stp

step-det-with : ∀ {Γ σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} {e : Γ ⊢ σ ! ε} {r0 : R} {e0' : Γ ⊢ σ ! ε}
              (stp0 : _⊢_-[_]→_ {sub = sub} g e r0 e0') {r : R} {e' : Γ ⊢ σ ! ε}
              (stp : _⊢_-[_]→_ {sub = sub} g e r e') → r ≡ r0 × e' ≡ e0'
step-det-with stp0 stp with cong (λ { (_ , r , e' , _) → r , e' }) (theorem-A4-2-core stp stp0)
... | reEq = cong proj₁ reEq , cong proj₂ reEq

-- ---------------------------------------------------------------------
-- Lemma A.6 (page 33): if e:σ!ε₁ is {g}-computable for a loss-
-- computable g:σ→loss!ε₂ (ε₂⊆ε₁), then ⟨e⟩^ε₁_g:σ!ε (ε₁⊆ε) is
-- computable. "{g}-computable" is G-computable w.r.t. the SINGLETON set
-- containing just g (Gsingle below) -- the paper's own "{(λx:loss.0)}-
-- induction" (renamed R-induction, used by Lemma A.7) is the SAME
-- pattern one level down, specialized to Loss/zeroLC, matching
-- RComputable's own G₀.
-- ---------------------------------------------------------------------

Gsingle : ∀ {σ ε₁ ε₂} → LC ∅ σ ε₂ → ∀ {εg} → εg ⊆ᵉ ε₁ → LC ∅ σ εg → Set
Gsingle {ε₂ = ε₂} g0 {εg} _ g = Σ (εg ≡ ε₂) (λ eq → subst (λ ε' → LC ∅ _ ε') eq g ≡ g0)

-- Proceeds by {g}-induction on e (source page 33's own proof, verbatim:
-- three GComputable clauses, matched one-for-one against gc-val/
-- gc-stuck/gc-step below). The gc-val case exhibits R8 as e's ONLY
-- possible step (any other alleged step is unified with it via
-- step-det-with); the gc-stuck case simply extends K by one more
-- S-glocal frame (plugK's own recursive equations make the two sides
-- literally the same term, no rewriting needed); the gc-step case
-- inverts a step out of ⟨e⟩^ε₁_g by case-splitting e's own status via
-- progress-dichotomy -- e Terminal contradicts nterm directly, e
-- reducible exhibits S3 (wrapping e's own step) as the unique
-- possibility, whose result matches the recursive call to go via the
-- ORIGINAL gc-step's own second field applied to e's step -- the
-- "recurse through a function field obtained by pattern-matching",
-- exactly Acc-recursion's own idiom.
lemma-A6 : ∀ {σ ε₁ ε₂ ε} (sub1 : ε₂ ⊆ᵉ ε₁) (sub2 : ε₁ ⊆ᵉ ε) {g : LC ∅ σ ε₂} {e : ∅ ⊢ σ ! ε₁}
         → LossComputable (ComputableV σ) g
         → GComputable (ComputableV σ) (Gsingle g) e
         → ComputableE σ ε (glocalE sub1 sub2 e g)
lemma-A6 {σ} {ε₁} {ε₂} {ε} sub1 sub2 {g} lossCompG = go
  where
  go : ∀ {e} → GComputable (ComputableV σ) (Gsingle g) e → ComputableE σ ε (glocalE sub1 sub2 e g)
  go (gc-val {v} Pv) = gc-step (¬Terminal-of-step {sub = ⊆ᵉ-refl} {g = zeroLC} (R8 sub1 sub2 v g)) step-case
    where
    step-case : ∀ {εg} {subX : εg ⊆ᵉ ε} {g₁ : LC ∅ σ εg} → LossComputable (ComputableV σ) g₁
              → ∀ {r e''} → _⊢_-[_]→_ {sub = subX} g₁ (glocalE sub1 sub2 (val v) g) r e''
              → GComputable (ComputableV σ) (λ _ g' → LossComputable (ComputableV σ) g') e''
    step-case _ stp with step-det-with (R8 sub1 sub2 v g) stp
    ... | (refl , refl) = gc-val Pv
  go (gc-stuck {K = K} nh ihK) = gc-stuck {K = S∘ K (S-glocal sub1 sub2 g)} nh (λ {v1} → go (ihK {v1}))
  go (gc-step {e} nterm ih) = gc-step nterm' step-case
    where
    nterm' : ¬ Terminal (glocalE sub1 sub2 e g)
    nterm' term with progress-dichotomy {sub = sub1} {g = g} e
    ... | inj₁ t = nterm t
    ... | inj₂ (r0 , e0' , stp0) = theorem-A4-1 {sub = λ {ℓ} m → sub2 (sub1 m)} {g = g} term (S3 sub1 sub2 g stp0)
    step-case : ∀ {εg} {subX : εg ⊆ᵉ ε} {g₁ : LC ∅ σ εg} → LossComputable (ComputableV σ) g₁
              → ∀ {r e''} → _⊢_-[_]→_ {sub = subX} g₁ (glocalE sub1 sub2 e g) r e''
              → GComputable (ComputableV σ) (λ _ g' → LossComputable (ComputableV σ) g') e''
    step-case _ stp with progress-dichotomy {sub = sub1} {g = g} e
    ... | inj₁ t = ⊥-elim (nterm t)
    ... | inj₂ (r0 , e0' , stp0) with step-det-with (S3 sub1 sub2 g stp0) stp
    ...   | (refl , refl) = go (ih {sub = sub1} {g = g} (refl , refl) stp0)

