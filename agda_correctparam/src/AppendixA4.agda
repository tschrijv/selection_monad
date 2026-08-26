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
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Axiom.Extensionality.Propositional using (Extensionality; implicit-extensionality)

-- Same axiom as Proofs.agda's own funext (postulated locally here too,
-- rather than importing Proofs.agda, to keep this file's own import
-- footprint -- and hence its compile cycle -- independent of it).
postulate funext : ∀ {a b} → Extensionality a b

-- Accessibility witnesses for the same relation/element are
-- propositionally unique -- a standard fact (Acc's own constructor
-- takes a FUNCTION, so proving two Acc's equal needs function
-- extensionality one level down at every recursive layer). This is
-- what actually discharges the various "Acc-irrelevance" postulates
-- ComputableV-acc's own well-founded recursion (over Ty, via _<M_)
-- otherwise needs below: rather than separately postulating that
-- differently-obtained Acc witnesses give interchangeable
-- ComputableV-acc's, that fact now follows by ordinary subst along
-- this equality.
Acc-irrelevant : ∀ {A : Set} {R : A → A → Set} {x : A} (a1 a2 : Acc R x) → a1 ≡ a2
Acc-irrelevant (acc rs1) (acc rs2) =
  cong acc (implicit-extensionality funext (λ {y} → funext (λ r → Acc-irrelevant (rs1 r) (rs2 r))))

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

-- K-outer-r/K-target: hoisted up from their original home (just above
-- plugK-cong, where the FULL motivating comment for them still lives)
-- purely so gc-stuck below can reference K-target directly in its own
-- new ihK-target field -- see that field's own comment for why.
-- K-outer-r/K-target/plugK-cong only ever depend on OpSem.agda's own
-- ContCxt/plugF/plugS machinery, never on anything defined later in
-- THIS file, so moving these two definitions earlier changes nothing
-- about how they typecheck.
K-outer-r : ∀ {α εα τ ε} → ContCxt ∅ α εα τ ε → R → R
K-outer-r ▫ r                       = r
K-outer-r (F∘ k f) r                = K-outer-r k r
K-outer-r (S∘ k (S-handleB h v)) r  = K-outer-r k r
K-outer-r (S∘ k (S-then sub g)) r   = 0#
K-outer-r (S∘ k (S-glocal s1 s2 g)) r = K-outer-r k r
K-outer-r (S∘ k S-reset) r          = 0#

K-target : ∀ {α εα τ ε} (K : ContCxt ∅ α εα τ ε) (r : R) → ∅ ⊢ α ! εα → ∅ ⊢ τ ! ε
K-target ▫ r e'                       = e'
K-target (F∘ k f) r e'                = plugF f (K-target k r e')
K-target (S∘ k (S-handleB h v)) r e'  = handleE h (val v) (K-target k r e')
K-target (S∘ k (S-then sub g)) r e'   = plusE (val (vgnd (K-outer-r k r))) (thenE sub (K-target k r e') g)
K-target (S∘ k (S-glocal s1 s2 g)) r e' = glocalE s1 s2 (K-target k r e') g
K-target (S∘ k S-reset) r e'          = resetE (K-target k r e')

-- K-outer-r K 0# is ALWAYS 0#, for every K: every non-(S-then/S-reset)
-- clause just passes r through unchanged (so induction applies with
-- r=0# fixed throughout), and the S-then/S-reset clauses return 0#
-- outright regardless of r. Used below (gc-stuck's ihK-target field,
-- S-then case) to identify K-target's own plusE(val(vgnd(K-outer-r K
-- 0#)))(-) wrapper with the plain plusE(val(vgnd 0#))(-) that
-- lemma-A8-1 (further below) produces.
K-outer-r-zero : ∀ {α εα τ ε} (K : ContCxt ∅ α εα τ ε) → K-outer-r K 0# ≡ 0#
K-outer-r-zero ▫                       = refl
K-outer-r-zero (F∘ k f)                = K-outer-r-zero k
K-outer-r-zero (S∘ k (S-handleB h v))  = K-outer-r-zero k
K-outer-r-zero (S∘ k (S-then sub g))   = refl
K-outer-r-zero (S∘ k (S-glocal s1 s2 g)) = K-outer-r-zero k
K-outer-r-zero (S∘ k S-reset)          = refl

data GComputable {σ ε} (P : Val ∅ σ → Set) (G : ∀ {εg} → εg ⊆ᵉ ε → LC ∅ σ εg → Set) : ∅ ⊢ σ ! ε → Set where
  gc-val   : ∀ {v} → P v → GComputable P G (val v)
  gc-stuck : ∀ {ℓ εop} {m : ℓ ∈ εop} {op : Op ℓ} {v : Val ∅ (gnd (out op))}
             {K : ContCxt ∅ (gnd (in′ op)) εop σ ε} (nh : ¬ Handles K ℓ)
           → (∀ {v1 : Val ∅ (gnd (in′ op))} → GComputable P G (plugK K (val v1)))
           -- The analogous fact for K-target instead of plugK, at the
           -- one and only r this development ever needs (0#) -- see
           -- K-settle's own former home (postulate, now deleted) for
           -- why: this is exactly what lets Lemma A.10's Fcomp-inner
           -- bridge K[v]'s computability to K-target K 0# (val v)'s,
           -- built FORWARD at each gc-stuck construction site (below)
           -- rather than extracted backward from an opaque witness.
           → (∀ {v1 : Val ∅ (gnd (in′ op))} → GComputable P G (K-target K 0# (val v1)))
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
  go (gc-stuck {K = K} nh ihK ihKt) = gc-stuck {K = S∘ K (S-glocal sub1 sub2 g)} nh (λ {v1} → go (ihK {v1})) (λ {v1} → go (ihKt {v1}))
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

-- ---------------------------------------------------------------------
-- Lemma A.7 (page 33). "r + e" is now plusE (val (vgnd r)) e directly
-- (Syntax.agda/OpSem.agda), NOT desugared through thenE/lossE -- see
-- OpSem.agda's own S2 comment for why the original desugaring diverges.
-- ---------------------------------------------------------------------

-- plusE (val (vgnd r)) (val v) is always R-computable: one further
-- Rplus step settles it directly (v is already vgnd-shaped, being a
-- closed Loss value). Reusable base case for Lemma A.7(1)'s own gc-val
-- clause below, and likely again for A.7(2)/A.8.
plusVal-RComputable : ∀ {ε} (r : R) (v : Val ∅ Loss) → RComputable {ε} (plusE (val (vgnd r)) (val v))
plusVal-RComputable {ε} r v with val-closed-gnd v
... | (v' , refl) = gc-step (¬Terminal-of-step {sub = ⊆ᵉ-refl} {g = zeroLC} (Rplus r v')) step-case
  where
  step-case : ∀ {εg} {subX : εg ⊆ᵉ ε} {g₁ : LC ∅ Loss εg} → Σ (εg ≡ ε) (λ eq → subst (λ ε' → LC ∅ Loss ε') eq g₁ ≡ zeroLC)
            → ∀ {r2 e''} → _⊢_-[_]→_ {sub = subX} g₁ (plusE (val (vgnd r)) (val (vgnd v'))) r2 e''
            → RComputable {ε} e''
  step-case _ stp with step-det-with (Rplus r v') stp
  ... | (refl , refl) = gc-val tt

-- Lemma A.7(1): if e:loss!ε₁ is R-computable, so is r + ⟨e⟩^{ε₁}_{0}
-- : loss!ε (ε₁⊆ε). Proceeds by R-induction on e, exactly mirroring
-- Lemma A.6's own three cases, but through F-plusR's own congruence
-- (a REGULAR frame, hence a single, direct step at each level) rather
-- than thenE/S2's administrative machinery -- much simpler than the
-- old (buggy) encoding would have needed.
lemma-A7-1 : ∀ {ε₁ ε} (sub2 : ε₁ ⊆ᵉ ε) (r : R) {e : ∅ ⊢ Loss ! ε₁}
           → RComputable e
           → RComputable {ε} (plusE (val (vgnd r)) (glocalE ⊆ᵉ-refl sub2 e zeroLC))
lemma-A7-1 {ε₁} {ε} sub2 r = go
  where
  go : ∀ {e} → RComputable e → RComputable {ε} (plusE (val (vgnd r)) (glocalE ⊆ᵉ-refl sub2 e zeroLC))
  go (gc-val {v} _) = gc-step nterm step-case
    where
    nterm = ¬Terminal-of-step {sub = ⊆ᵉ-refl} {g = zeroLC}
              (F-rule ⊆ᵉ-refl (F-plusR (vgnd r)) (R8 ⊆ᵉ-refl sub2 v zeroLC))
    step-case : ∀ {εg} {subX : εg ⊆ᵉ ε} {g₁ : LC ∅ Loss εg} → Σ (εg ≡ ε) (λ eq → subst (λ ε' → LC ∅ Loss ε') eq g₁ ≡ zeroLC)
              → ∀ {r2 e''} → _⊢_-[_]→_ {sub = subX} g₁ (plusE (val (vgnd r)) (glocalE ⊆ᵉ-refl sub2 (val v) zeroLC)) r2 e''
              → RComputable {ε} e''
    step-case {subX = subX} _ stp with step-det-with (F-rule subX (F-plusR (vgnd r)) (R8 ⊆ᵉ-refl sub2 v zeroLC)) stp
    ... | (refl , refl) = plusVal-RComputable r v
  go (gc-stuck {K = K} nh ihK ihKt) =
    gc-stuck {K = F∘ (S∘ K (S-glocal ⊆ᵉ-refl sub2 zeroLC)) (F-plusR (vgnd r))} nh (λ {v1} → go (ihK {v1})) (λ {v1} → go (ihKt {v1}))
  go (gc-step {e} nterm ih) = gc-step nterm' step-case
    where
    nterm' : ¬ Terminal (plusE (val (vgnd r)) (glocalE ⊆ᵉ-refl sub2 e zeroLC))
    nterm' term with progress-dichotomy {sub = ⊆ᵉ-refl} {g = zeroLC} e
    ... | inj₁ t = nterm t
    ... | inj₂ (r0 , e0' , stp0) =
      theorem-A4-1 {sub = ⊆ᵉ-refl} {g = zeroLC} term
        (F-rule ⊆ᵉ-refl (F-plusR (vgnd r)) (S3 ⊆ᵉ-refl sub2 zeroLC stp0))
    step-case : ∀ {εg} {subX : εg ⊆ᵉ ε} {g₁ : LC ∅ Loss εg} → Σ (εg ≡ ε) (λ eq → subst (λ ε' → LC ∅ Loss ε') eq g₁ ≡ zeroLC)
              → ∀ {r2 e''} → _⊢_-[_]→_ {sub = subX} g₁ (plusE (val (vgnd r)) (glocalE ⊆ᵉ-refl sub2 e zeroLC)) r2 e''
              → RComputable {ε} e''
    step-case {subX = subX} _ stp with progress-dichotomy {sub = ⊆ᵉ-refl} {g = zeroLC} e
    ... | inj₁ t = ⊥-elim (nterm t)
    ... | inj₂ (r0 , e0' , stp0) with step-det-with (F-rule subX (F-plusR (vgnd r)) (S3 ⊆ᵉ-refl sub2 zeroLC stp0)) stp
    ...   | (refl , refl) = go (ih {sub = ⊆ᵉ-refl} {g = zeroLC} (refl , refl) stp0)

-- ---------------------------------------------------------------------
-- Substitution lemmas needed for Lemma A.7(2): substituting the freshly
-- bound variable of `vabs (... (weaken1V g))` back in must collapse to
-- plain `g` (g being closed already), which Agda does not see
-- definitionally -- no such lemma exists yet anywhere in Subst.agda /
-- OpSemProofs.agda / Proofs.agda. Standard PLFA-style rename/subst
-- fusion, plus "identity substitution is a no-op", both by mutual
-- induction on Val/Handler/Expr.
-- ---------------------------------------------------------------------

Handler-eq : ∀ {Γ ℓ par σ σ' ε} {h1 h2 : Handler Γ ℓ par σ σ' ε}
           → (∀ op → clause h1 op ≡ clause h2 op) → ret h1 ≡ ret h2 → h1 ≡ h2
Handler-eq {h1 = h1} {h2 = h2} cEq rEq = cong₂ (λ c r → record { clause = c ; ret = r }) (funext cEq) rEq

-- Every "substitute, given two POINTWISE-equal substitutions" fact
-- below is proved by structural induction on the term (never by
-- packaging the two substitutions into one Sub-level `_≡_` and using
-- `cong`/pattern-matching on it: cong's implicit {A} metavariable
-- cannot be solved when A is itself the rank-2, implicitly-quantified-
-- over-σ Sub type, and Agda also refuses to split on `refl : σs ≡ σs'`
-- for the very same reason -- so the induction carries the pointwise
-- hypothesis through directly instead, PLFA-style).
mutual
  subV-cong : ∀ {Γ Γ' σ} {σs σs' : Sub Γ Γ'} → (∀ {τ} (x : Γ ∋ τ) → σs x ≡ σs' x) → (v : Val Γ σ) → subV σs v ≡ subV σs' v
  subV-cong eq (vvar x)    = eq x
  subV-cong eq (vgnd x)    = refl
  subV-cong eq (vpair v w) = cong₂ vpair (subV-cong eq v) (subV-cong eq w)
  subV-cong eq (vabs e)    = cong vabs (subE-cong (extS-cong eq) e)

  extS-cong : ∀ {Γ Γ' τ0} {σs σs' : Sub Γ Γ'} → (∀ {τ} (x : Γ ∋ τ) → σs x ≡ σs' x) → ∀ {τ} (x : (Γ , τ0) ∋ τ) → extS σs x ≡ extS σs' x
  extS-cong eq Z     = refl
  extS-cong eq (S x) = cong weaken1V (eq x)

  subH-cong : ∀ {Γ Γ' ℓ par σ σ' ε} {σs σs' : Sub Γ Γ'} → (∀ {τ} (x : Γ ∋ τ) → σs x ≡ σs' x) → (h : Handler Γ ℓ par σ σ' ε) → subH σs h ≡ subH σs' h
  subH-cong eq h = Handler-eq
    (λ op → subE-cong (extS-cong (extS-cong (extS-cong (extS-cong eq)))) (clause h op))
    (subE-cong (extS-cong (extS-cong eq)) (ret h))

  subE-cong : ∀ {Γ Γ' σ ε} {σs σs' : Sub Γ Γ'} → (∀ {τ} (x : Γ ∋ τ) → σs x ≡ σs' x) → (e : Γ ⊢ σ ! ε) → subE σs e ≡ subE σs' e
  subE-cong eq (val v)          = cong val (subV-cong eq v)
  subE-cong eq (fun f e)        = cong (fun f) (subE-cong eq e)
  subE-cong eq (pair e e₁)      = cong₂ pair (subE-cong eq e) (subE-cong eq e₁)
  subE-cong eq (fst e)          = cong fst (subE-cong eq e)
  subE-cong eq (snd e)          = cong snd (subE-cong eq e)
  subE-cong eq (app e e₁)       = cong₂ app (subE-cong eq e) (subE-cong eq e₁)
  subE-cong eq (opE m op e)     = cong (opE m op) (subE-cong eq e)
  subE-cong eq (lossE e)        = cong lossE (subE-cong eq e)
  subE-cong eq (thenE s e g)    = cong₂ (thenE s) (subE-cong eq e) (subV-cong eq g)
  subE-cong eq (plusE e1 e2)    = cong₂ plusE (subE-cong eq e1) (subE-cong eq e2)
  subE-cong eq (glocalE s1 s2 e g) = cong₂ (glocalE s1 s2) (subE-cong eq e) (subV-cong eq g)
  subE-cong eq (resetE e)       = cong resetE (subE-cong eq e)
  subE-cong {σs = σs} {σs' = σs'} eq (handleE h e e₁) =
    trans (cong (λ h' → handleE h' (subE σs e) (subE σs e₁)) (subH-cong eq h))
          (cong₂ (handleE (subH σs' h)) (subE-cong eq e) (subE-cong eq e₁))

extS-extR-pointwise : ∀ {Γ Γ' Γ'' τ0 τ} (σs : Sub Γ' Γ'') (ρ : Ren Γ Γ') (x : (Γ , τ0) ∋ τ)
                     → extS σs (extR ρ x) ≡ extS (λ y → σs (ρ y)) x
extS-extR-pointwise σs ρ Z     = refl
extS-extR-pointwise σs ρ (S x) = refl

extS²-extR²-pointwise : ∀ {Γ Γ' Γ'' τ0 τ1 τ} (σs : Sub Γ' Γ'') (ρ : Ren Γ Γ') (x : ((Γ , τ0) , τ1) ∋ τ)
                       → extS (extS σs) (extR (extR ρ) x) ≡ extS (extS (λ y → σs (ρ y))) x
extS²-extR²-pointwise σs ρ Z     = refl
extS²-extR²-pointwise σs ρ (S x) = cong weaken1V (extS-extR-pointwise σs ρ x)

extS³-extR³-pointwise : ∀ {Γ Γ' Γ'' τ0 τ1 τ2 τ} (σs : Sub Γ' Γ'') (ρ : Ren Γ Γ') (x : (((Γ , τ0) , τ1) , τ2) ∋ τ)
                       → extS (extS (extS σs)) (extR (extR (extR ρ)) x) ≡ extS (extS (extS (λ y → σs (ρ y)))) x
extS³-extR³-pointwise σs ρ Z     = refl
extS³-extR³-pointwise σs ρ (S x) = cong weaken1V (extS²-extR²-pointwise σs ρ x)

extS⁴-extR⁴-pointwise : ∀ {Γ Γ' Γ'' τ0 τ1 τ2 τ3 τ} (σs : Sub Γ' Γ'') (ρ : Ren Γ Γ') (x : ((((Γ , τ0) , τ1) , τ2) , τ3) ∋ τ)
                       → extS (extS (extS (extS σs))) (extR (extR (extR (extR ρ))) x) ≡ extS (extS (extS (extS (λ y → σs (ρ y))))) x
extS⁴-extR⁴-pointwise σs ρ Z     = refl
extS⁴-extR⁴-pointwise σs ρ (S x) = cong weaken1V (extS³-extR³-pointwise σs ρ x)

mutual
  subV-renV-fuse : ∀ {Γ Γ' Γ'' σ} (σs : Sub Γ' Γ'') (ρ : Ren Γ Γ') (v : Val Γ σ)
                  → subV σs (renV ρ v) ≡ subV (λ x → σs (ρ x)) v
  subV-renV-fuse σs ρ (vvar x)    = refl
  subV-renV-fuse σs ρ (vgnd x)    = refl
  subV-renV-fuse σs ρ (vpair v w) = cong₂ vpair (subV-renV-fuse σs ρ v) (subV-renV-fuse σs ρ w)
  subV-renV-fuse σs ρ (vabs e)    =
    cong vabs (trans (subE-renE-fuse (extS σs) (extR ρ) e)
                      (subE-cong (extS-extR-pointwise σs ρ) e))

  subH-renH-fuse : ∀ {Γ Γ' Γ'' ℓ par σ σ' ε} (σs : Sub Γ' Γ'') (ρ : Ren Γ Γ') (h : Handler Γ ℓ par σ σ' ε)
                  → subH σs (renH ρ h) ≡ subH (λ x → σs (ρ x)) h
  subH-renH-fuse σs ρ h = Handler-eq
    (λ op → trans (subE-renE-fuse (extS (extS (extS (extS σs)))) (extR (extR (extR (extR ρ)))) (clause h op))
                  (subE-cong (extS⁴-extR⁴-pointwise σs ρ) (clause h op)))
    (trans (subE-renE-fuse (extS (extS σs)) (extR (extR ρ)) (ret h))
           (subE-cong (extS²-extR²-pointwise σs ρ) (ret h)))

  subE-renE-fuse : ∀ {Γ Γ' Γ'' σ ε} (σs : Sub Γ' Γ'') (ρ : Ren Γ Γ') (e : Γ ⊢ σ ! ε)
                  → subE σs (renE ρ e) ≡ subE (λ x → σs (ρ x)) e
  subE-renE-fuse σs ρ (val v)          = cong val (subV-renV-fuse σs ρ v)
  subE-renE-fuse σs ρ (fun f e)        = cong (fun f) (subE-renE-fuse σs ρ e)
  subE-renE-fuse σs ρ (pair e e₁)      = cong₂ pair (subE-renE-fuse σs ρ e) (subE-renE-fuse σs ρ e₁)
  subE-renE-fuse σs ρ (fst e)          = cong fst (subE-renE-fuse σs ρ e)
  subE-renE-fuse σs ρ (snd e)          = cong snd (subE-renE-fuse σs ρ e)
  subE-renE-fuse σs ρ (app e e₁)       = cong₂ app (subE-renE-fuse σs ρ e) (subE-renE-fuse σs ρ e₁)
  subE-renE-fuse σs ρ (opE m op e)     = cong (opE m op) (subE-renE-fuse σs ρ e)
  subE-renE-fuse σs ρ (lossE e)        = cong lossE (subE-renE-fuse σs ρ e)
  subE-renE-fuse σs ρ (thenE s e g)    = cong₂ (thenE s) (subE-renE-fuse σs ρ e) (subV-renV-fuse σs ρ g)
  subE-renE-fuse σs ρ (plusE e1 e2)    = cong₂ plusE (subE-renE-fuse σs ρ e1) (subE-renE-fuse σs ρ e2)
  subE-renE-fuse σs ρ (glocalE s1 s2 e g) = cong₂ (glocalE s1 s2) (subE-renE-fuse σs ρ e) (subV-renV-fuse σs ρ g)
  subE-renE-fuse σs ρ (resetE e)       = cong resetE (subE-renE-fuse σs ρ e)
  subE-renE-fuse σs ρ (handleE h e e₁) =
    trans (cong (λ h' → handleE h' (subE σs (renE ρ e)) (subE σs (renE ρ e₁))) (subH-renH-fuse σs ρ h))
          (cong₂ (handleE (subH (λ x → σs (ρ x)) h)) (subE-renE-fuse σs ρ e) (subE-renE-fuse σs ρ e₁))

extS-idSub-pointwise : ∀ {Γ τ0 τ} (x : (Γ , τ0) ∋ τ) → extS idSub x ≡ idSub x
extS-idSub-pointwise Z     = refl
extS-idSub-pointwise (S x) = refl

extS²-idSub-pointwise : ∀ {Γ τ0 τ1 τ} (x : ((Γ , τ0) , τ1) ∋ τ) → extS (extS idSub) x ≡ idSub x
extS²-idSub-pointwise Z     = refl
extS²-idSub-pointwise (S x) = cong weaken1V (extS-idSub-pointwise x)

extS³-idSub-pointwise : ∀ {Γ τ0 τ1 τ2 τ} (x : (((Γ , τ0) , τ1) , τ2) ∋ τ) → extS (extS (extS idSub)) x ≡ idSub x
extS³-idSub-pointwise Z     = refl
extS³-idSub-pointwise (S x) = cong weaken1V (extS²-idSub-pointwise x)

extS⁴-idSub-pointwise : ∀ {Γ τ0 τ1 τ2 τ3 τ} (x : ((((Γ , τ0) , τ1) , τ2) , τ3) ∋ τ) → extS (extS (extS (extS idSub))) x ≡ idSub x
extS⁴-idSub-pointwise Z     = refl
extS⁴-idSub-pointwise (S x) = cong weaken1V (extS³-idSub-pointwise x)

mutual
  subV-idSub : ∀ {Γ σ} (v : Val Γ σ) → subV idSub v ≡ v
  subV-idSub (vvar x)    = refl
  subV-idSub (vgnd x)    = refl
  subV-idSub (vpair v w) = cong₂ vpair (subV-idSub v) (subV-idSub w)
  subV-idSub (vabs e)    = cong vabs (trans (subE-cong extS-idSub-pointwise e) (subE-idSub e))

  subH-idSub : ∀ {Γ ℓ par σ σ' ε} (h : Handler Γ ℓ par σ σ' ε) → subH idSub h ≡ h
  subH-idSub h = Handler-eq
    (λ op → trans (subE-cong extS⁴-idSub-pointwise (clause h op)) (subE-idSub (clause h op)))
    (trans (subE-cong extS²-idSub-pointwise (ret h)) (subE-idSub (ret h)))

  subE-idSub : ∀ {Γ σ ε} (e : Γ ⊢ σ ! ε) → subE idSub e ≡ e
  subE-idSub (val v)          = cong val (subV-idSub v)
  subE-idSub (fun f e)        = cong (fun f) (subE-idSub e)
  subE-idSub (pair e e₁)      = cong₂ pair (subE-idSub e) (subE-idSub e₁)
  subE-idSub (fst e)          = cong fst (subE-idSub e)
  subE-idSub (snd e)          = cong snd (subE-idSub e)
  subE-idSub (app e e₁)       = cong₂ app (subE-idSub e) (subE-idSub e₁)
  subE-idSub (opE m op e)     = cong (opE m op) (subE-idSub e)
  subE-idSub (lossE e)        = cong lossE (subE-idSub e)
  subE-idSub (thenE s e g)    = cong₂ (thenE s) (subE-idSub e) (subV-idSub g)
  subE-idSub (plusE e1 e2)    = cong₂ plusE (subE-idSub e1) (subE-idSub e2)
  subE-idSub (glocalE s1 s2 e g) = cong₂ (glocalE s1 s2) (subE-idSub e) (subV-idSub g)
  subE-idSub (resetE e)       = cong resetE (subE-idSub e)
  subE-idSub (handleE h e e₁) =
    trans (cong (λ h' → handleE h' (subE idSub e) (subE idSub e₁)) (subH-idSub h))
          (cong₂ (handleE h) (subE-idSub e) (subE-idSub e₁))

-- Instantiating the fusion+identity lemmas at σs = cons v idSub, ρ = S
-- gives exactly "weaken1V then substitute the fresh variable to v
-- collapses to the identity": the middle term of the trans below is
-- convertible to `subV idSub g` since `cons v idSub (S x)` reduces to
-- `idSub x` by cons's own S-clause, and `λ x → idSub x` is `idSub` by
-- eta -- so Agda accepts the two `subV-renV-fuse`/`subV-idSub` calls
-- chaining directly without any further rewriting.
weaken1V-sub1-cancel : ∀ {Γ σ τ} (v : Val Γ τ) (g : Val Γ σ) → subV (cons v idSub) (renV S g) ≡ g
weaken1V-sub1-cancel v g = trans (subV-renV-fuse (cons v idSub) S g) (subV-idSub g)

-- Lemma A.7(2): if g:loss→loss!ε₁ is loss-computable, so is λ^ε
-- x:loss.(r+x)▶g (ε₁⊆ε), for any r. Proceeds by exhibiting the paper's
-- own two-step reduction (S2, unfreezing r+v via Rplus, THEN F-rule/
-- F-plusR/R7, unfreezing the resulting v▶g via g's own value clause)
-- directly, via gc-step/step-det-with at each step (both steps are
-- deterministic, so "the successor is computable" suffices to show the
-- SOURCE is too), landing on lemma-A7-1's own conclusion at the very
-- end -- exactly "we apply part 1", per the paper's own proof.
lemma-A7-2 : ∀ {ε₁ ε} (sub : ε₁ ⊆ᵉ ε) (r : R) {g : LC ∅ Loss ε₁}
           → LossComputable (ComputableV Loss) g
           → LossComputable (ComputableV Loss) (vabs (thenE sub (plusE (val (vgnd r)) (val (vvar Z))) (weaken1V g)))
lemma-A7-2 {ε₁} {ε} sub r {g} lc-g {v} _ with val-closed-gnd v
... | (v' , refl) with val-closed-abs g
...   | (e , refl) =
        subst (λ g' → RComputable {ε} (thenE sub (plusE (val (vgnd r)) (val (vgnd v'))) g'))
              (sym (weaken1V-sub1-cancel (vgnd v') (vabs e))) step1-back
  where
  s : R
  s = r + v'
  final : RComputable {ε} (plusE (val (vgnd 0#)) (glocalE ⊆ᵉ-refl sub (e [ vgnd s ]) zeroLC))
  final = lemma-A7-1 sub 0# (lc-g {vgnd s} tt)
  step2-back : RComputable {ε} (plusE (val (vgnd 0#)) (thenE sub (val (vgnd s)) (vabs e)))
  step2-back = gc-step (¬Terminal-of-step {sub = ⊆ᵉ-refl} {g = zeroLC} (F-rule ⊆ᵉ-refl (F-plusR (vgnd 0#)) (R7 sub (vgnd s) e))) step2-case
    where
    step2-case : ∀ {εg} {subX : εg ⊆ᵉ ε} {g₁ : LC ∅ Loss εg} → Σ (εg ≡ ε) (λ eq → subst (λ ε' → LC ∅ Loss ε') eq g₁ ≡ zeroLC)
               → ∀ {r2 e''} → _⊢_-[_]→_ {sub = subX} g₁ (plusE (val (vgnd 0#)) (thenE sub (val (vgnd s)) (vabs e))) r2 e''
               → RComputable {ε} e''
    step2-case {subX = subX} _ stp with step-det-with (F-rule subX (F-plusR (vgnd 0#)) (R7 sub (vgnd s) e)) stp
    ... | (refl , refl) = final
  step1-back : RComputable {ε} (thenE sub (plusE (val (vgnd r)) (val (vgnd v'))) (vabs e))
  step1-back = gc-step (¬Terminal-of-step {sub = ⊆ᵉ-refl} {g = zeroLC} (S2 sub (vabs e) (Rplus r v'))) step1-case
    where
    step1-case : ∀ {εg} {subX : εg ⊆ᵉ ε} {g₁ : LC ∅ Loss εg} → Σ (εg ≡ ε) (λ eq → subst (λ ε' → LC ∅ Loss ε') eq g₁ ≡ zeroLC)
               → ∀ {r2 e''} → _⊢_-[_]→_ {sub = subX} g₁ (thenE sub (plusE (val (vgnd r)) (val (vgnd v'))) (vabs e)) r2 e''
               → RComputable {ε} e''
    step1-case _ stp with step-det-with (S2 sub (vabs e) (Rplus r v')) stp
    ... | (refl , refl) = step2-back

-- ---------------------------------------------------------------------
-- Lemma A.8 (page 34).
-- ---------------------------------------------------------------------

-- Lemma A.8(1): if e:loss!ε is (fully) computable, so is r+e, for any
-- r:R. Proceeds by L_loss,ε-induction on e -- the FULL notion (any
-- loss-computable g at any εg⊆ε), unlike Lemma A.7's own {0}-restricted
-- R-induction -- mirroring lemma-A6's own three-case template with
-- plusE/Rplus/F-plusR standing in for glocalE/R8/S3/S-glocal. Unlike
-- lemma-A7-1's gc-step case, the ambient g here is a genuinely
-- arbitrary loss-computable g₁ (not pinned to zeroLC by G₀), so
-- progress-dichotomy/F-rule inside step-case must be applied at the
-- step-case's OWN {subX}/{g₁}, not a fixed ⊆ᵉ-refl/zeroLC (only
-- nterm'/theorem-A4-1's throwaway witness may use a fixed choice, since
-- Terminal itself does not depend on which sub/g is used to build it).
lemma-A8-1 : ∀ {ε} (r : R) {e : ∅ ⊢ Loss ! ε} → ComputableE Loss ε e → ComputableE Loss ε (plusE (val (vgnd r)) e)
lemma-A8-1 {ε} r = go
  where
  go : ∀ {e} → ComputableE Loss ε e → ComputableE Loss ε (plusE (val (vgnd r)) e)
  go (gc-val {v} _) with val-closed-gnd v
  ... | (v' , refl) = gc-step (¬Terminal-of-step {sub = ⊆ᵉ-refl} {g = zeroLC} (Rplus r v')) step-case
    where
    step-case : ∀ {εg} {subX : εg ⊆ᵉ ε} {g₁ : LC ∅ Loss εg} → LossComputable (ComputableV Loss) g₁
              → ∀ {r2 e''} → _⊢_-[_]→_ {sub = subX} g₁ (plusE (val (vgnd r)) (val (vgnd v'))) r2 e''
              → GComputable (ComputableV Loss) (λ _ g' → LossComputable (ComputableV Loss) g') e''
    step-case _ stp with step-det-with (Rplus r v') stp
    ... | (refl , refl) = gc-val tt
  go (gc-stuck {K = K} nh ihK ihKt) = gc-stuck {K = F∘ K (F-plusR (vgnd r))} nh (λ {v1} → go (ihK {v1})) (λ {v1} → go (ihKt {v1}))
  go (gc-step {e} nterm ih) = gc-step nterm' step-case
    where
    -- F-rule's premise needs a step of e under a BOOSTED ambient (a
    -- fresh vabs whose body first re-plugs the F-plusR frame back
    -- around a bound-variable placeholder before falling through to
    -- the real ambient) -- NOT e's step under the plain outer ambient
    -- directly; progress-dichotomy's own plusE case (OpSemProofs.agda)
    -- builds exactly this shape internally when inverting a step out of
    -- a regular-frame-wrapped source, so it is reproduced here
    -- explicitly. Crucially, this boosted continuation is EXACTLY
    -- lemma-A7-2's own subject (plusE(val(vgnd r))(val(vvar Z)), up to
    -- the definitional plugF/weaken1F unfoldings), so lemma-A7-2 itself
    -- supplies its loss-computability -- meaning `ih` can be invoked at
    -- this boosted ambient directly, rather than at (subX, g₁).
    nterm' : ¬ Terminal (plusE (val (vgnd r)) e)
    nterm' term with progress-dichotomy {g = vabs (thenE ⊆ᵉ-refl (plusE (val (vgnd r)) (val (vvar Z))) (weaken1V zeroLC))} e
    ... | inj₁ t = nterm t
    ... | inj₂ (r0 , e0' , stp0) = theorem-A4-1 {sub = ⊆ᵉ-refl} {g = zeroLC} term (F-rule ⊆ᵉ-refl (F-plusR (vgnd r)) stp0)
    step-case : ∀ {εg} {subX : εg ⊆ᵉ ε} {g₁ : LC ∅ Loss εg} → LossComputable (ComputableV Loss) g₁
              → ∀ {r2 e''} → _⊢_-[_]→_ {sub = subX} g₁ (plusE (val (vgnd r)) e) r2 e''
              → GComputable (ComputableV Loss) (λ _ g' → LossComputable (ComputableV Loss) g') e''
    step-case {subX = subX} {g₁ = g₁} Gg₁ stp
      with progress-dichotomy {g = vabs (thenE subX (plusE (val (vgnd r)) (val (vvar Z))) (weaken1V g₁))} e
    ... | inj₁ t = ⊥-elim (nterm t)
    ... | inj₂ (r0 , e0' , stp0) with step-det-with (F-rule subX (F-plusR (vgnd r)) stp0) stp
    ...   | (refl , refl) =
            go (ih {sub = ⊆ᵉ-refl}
                   {g = vabs (thenE subX (plusE (val (vgnd r)) (val (vvar Z))) (weaken1V g₁))}
                   (lemma-A7-2 subX r Gg₁) stp0)

-- G-computability is antitone in G: a bigger set of admissible ambient
-- continuations is a STRONGER hypothesis for gc-step's own induction
-- step, so anything G-computable is automatically G'-computable for
-- any G'⊆G (page 33's "as an example" remark, generalised from its own
-- G'⊆G-is-computable-too phrasing into a reusable combinator -- needed
-- twice in Lemma A.8(3) below, going both from the FULL "is loss-
-- computable" G down to a single Gsingle g, and down to R-
-- computability's own G₀ = Gsingle zeroLC).
GComputable-antimono : ∀ {σ ε} {P : Val ∅ σ → Set} {G G' : ∀ {εg} → εg ⊆ᵉ ε → LC ∅ σ εg → Set}
                      → (∀ {εg} {sub : εg ⊆ᵉ ε} {g : LC ∅ σ εg} → G' sub g → G sub g)
                      → ∀ {e} → GComputable P G e → GComputable P G' e
GComputable-antimono G'⊆G (gc-val Pv) = gc-val Pv
GComputable-antimono G'⊆G (gc-stuck {K = K} nh ihK ihKt) =
  gc-stuck {K = K} nh (λ {v1} → GComputable-antimono G'⊆G (ihK {v1})) (λ {v1} → GComputable-antimono G'⊆G (ihKt {v1}))
GComputable-antimono G'⊆G (gc-step {e = e} nterm ih) =
  gc-step {e = e} nterm (λ {εg} {sub} {g} G'sg {r} {e'} stp → GComputable-antimono G'⊆G (ih {sub = sub} {g = g} (G'⊆G G'sg) stp))

-- zeroLC is (trivially) loss-computable for any value predicate P: its
-- body is the closed constant `val (vgnd 0#)`, substitution into it is
-- a no-op, and R-computability of a bare ground value is immediate
-- (ComputableV-acc's own (gnd γ) case is unconditionally ⊤).
zeroLC-lossComputable : ∀ {ε} → LossComputable (ComputableV Loss) (zeroLC {ε = ε})
zeroLC-lossComputable {v = v} _ = gc-val tt

-- Lemma A.8(2): if g:σ→loss!ε' is loss-computable and e:σ!ε is {g}-
-- computable (ε'⊆ε), then e▶g:loss!ε is (fully) computable. Proceeds
-- by {g}-induction on e, mirroring lemma-A6's own three-case template
-- with thenE/R7/S-then standing in for glocalE/R8/S-glocal -- unlike
-- lemma-A6's own gc-val case (which lands directly on a value via R8),
-- here R7's own result is glocalE-shaped, so lemma-A6 itself (with
-- g=zeroLC, itself always loss-computable) finishes it off; the
-- gc-step case's S2 step is ambient-transparent (unlike F-rule, its
-- premise already uses thenE's own sub/g1 directly, no boosted
-- continuation needed), landing on lemma-A8-1 to close the "r+(-)"
-- wrapping S2 introduces.
lemma-A8-2 : ∀ {σ ε' ε} (sub : ε' ⊆ᵉ ε) {g : LC ∅ σ ε'} {e : ∅ ⊢ σ ! ε}
           → LossComputable (ComputableV σ) g
           → GComputable (ComputableV σ) (Gsingle g) e
           → ComputableE Loss ε (thenE sub e g)
lemma-A8-2 {σ} {ε'} {ε} sub {g} lossCompG = go
  where
  go : ∀ {e} → GComputable (ComputableV σ) (Gsingle g) e → ComputableE Loss ε (thenE sub e g)
  go (gc-val {v} Pv) with val-closed-abs g
  ... | (e0 , refl) = gc-step (¬Terminal-of-step {sub = ⊆ᵉ-refl} {g = zeroLC} (R7 sub v e0)) step-case
    where
    step-case : ∀ {εg} {subX : εg ⊆ᵉ ε} {g₁ : LC ∅ Loss εg} → LossComputable (ComputableV Loss) g₁
              → ∀ {r2 e''} → _⊢_-[_]→_ {sub = subX} g₁ (thenE sub (val v) (vabs e0)) r2 e''
              → GComputable (ComputableV Loss) (λ _ g' → LossComputable (ComputableV Loss) g') e''
    step-case _ stp with step-det-with (R7 sub v e0) stp
    ... | (refl , refl) = lemma-A6 {σ = Loss} ⊆ᵉ-refl sub {g = zeroLC} (λ {v = v1} → zeroLC-lossComputable {ε = ε'} {v = v1}) (lossCompG {v} Pv)
  go (gc-stuck {K = K} nh ihK ihKt) = gc-stuck {K = S∘ K (S-then sub g)} nh (λ {v1} → go (ihK {v1})) ihKt-target
    where
    -- The one genuinely new case (see the comment above gc-stuck's own
    -- ihK-target field): K-target's S-then clause inserts an extra
    -- plusE(val(vgnd(K-outer-r K 0#)))(-) wrapper around
    -- thenE sub (K-target K 0# (val v1)) g, unlike plugK's own S-then
    -- clause (which is bare thenE sub (plugK K (val v1)) g). go itself
    -- applied to ihKt {v1} builds exactly ComputableE Loss ε of the
    -- UNwrapped thenE term (go's own conclusion type), so lemma-A8-1
    -- (0# specifically) supplies the missing plusE wrapper, and
    -- K-outer-r-zero identifies K-outer-r K 0# with the plain 0#
    -- lemma-A8-1 itself wraps with.
    ihKt-target : ∀ {v1} → GComputable (ComputableV Loss) (λ _ g0 → LossComputable (ComputableV Loss) g0)
                    (K-target (S∘ K (S-then sub g)) 0# (val v1))
    ihKt-target {v1} = subst (λ r0 → ComputableE Loss ε (plusE (val (vgnd r0)) (thenE sub (K-target K 0# (val v1)) g)))
                              (sym (K-outer-r-zero K))
                              (lemma-A8-1 0# (go (ihKt {v1})))
  go (gc-step {e} nterm ih) = gc-step nterm' step-case
    where
    nterm' : ¬ Terminal (thenE sub e g)
    nterm' term with progress-dichotomy {sub = sub} {g = g} e
    ... | inj₁ t = nterm t
    ... | inj₂ (r0 , e0' , stp0) = theorem-A4-1 {sub = ⊆ᵉ-refl} {g = zeroLC} term (S2 sub g stp0)
    step-case : ∀ {εg} {subX : εg ⊆ᵉ ε} {g₁ : LC ∅ Loss εg} → LossComputable (ComputableV Loss) g₁
              → ∀ {r2 e''} → _⊢_-[_]→_ {sub = subX} g₁ (thenE sub e g) r2 e''
              → GComputable (ComputableV Loss) (λ _ g' → LossComputable (ComputableV Loss) g') e''
    step-case _ stp with progress-dichotomy {sub = sub} {g = g} e
    ... | inj₁ t = ⊥-elim (nterm t)
    ... | inj₂ (r0 , e0' , stp0) with step-det-with (S2 sub g stp0) stp
    ...   | (refl , refl) = lemma-A8-1 r0 (go (ih {sub = sub} {g = g} (refl , refl) stp0))

-- Lemma A.8(3): a direct corollary of part 2 -- go from a FULLY
-- computable e[v]:σ!ε (part 2's own {g}-computable hypothesis is
-- strictly weaker, via GComputable-antimono since Gsingle g ⊆ the full
-- "is loss-computable" G, g itself being loss-computable), through
-- lemma-A8-2, then a second GComputable-antimono call narrows the
-- FULLY-computable *result* down to R-computable specifically (since
-- LossComputable's own body clause demands RComputable, not full
-- ComputableE -- G₀ = Gsingle zeroLC ⊆ full G too, zeroLC itself always
-- being loss-computable), and weaken1V-sub1-cancel discharges the
-- administrative weaken1V/sub1 mismatch between the substituted goal
-- and lemma-A8-2's own g-shaped conclusion (the same gap lemma-A7-2
-- closed).
lemma-A8-3 : ∀ {σ τ ε' ε} (sub : ε' ⊆ᵉ ε) {g : LC ∅ σ ε'} {e : (∅ , τ) ⊢ σ ! ε}
           → LossComputable (ComputableV σ) g
           → (∀ {v : Val ∅ τ} → ComputableV τ v → ComputableE σ ε (e [ v ]))
           → LossComputable (ComputableV τ) (vabs (thenE sub e (weaken1V g)))
lemma-A8-3 {σ} {τ} {ε'} {ε} sub {g} {e} lossCompG compE {v} Pv =
  subst (λ g' → RComputable {ε} (thenE sub (e [ v ]) g'))
        (sym (weaken1V-sub1-cancel v g))
        (GComputable-antimono {σ = Loss} {ε = ε}
          {G = λ _ g0 → LossComputable (ComputableV Loss) g0} {G' = Gsingle zeroLC}
          (λ { (refl , refl) {v = v1} → zeroLC-lossComputable {v = v1} })
          (lemma-A8-2 sub lossCompG
            (GComputable-antimono {σ = σ} {ε = ε}
              {G = λ _ g0 → LossComputable (ComputableV σ) g0} {G' = Gsingle g}
              (λ { (refl , refl) → lossCompG }) (compE Pv))))

-- weaken1V-sub1-cancel's own companions for Expr/Handler (same
-- fusion+identity argument, just through subE-renE-fuse/subE-idSub and
-- subH-renH-fuse/subH-idSub instead of the Val-level versions).
weaken1-sub1-cancelE : ∀ {Γ σ τ ε} (v : Val Γ τ) (e : Γ ⊢ σ ! ε) → subE (cons v idSub) (renE S e) ≡ e
weaken1-sub1-cancelE v e = trans (subE-renE-fuse (cons v idSub) S e) (subE-idSub e)

weaken1-sub1-cancelH : ∀ {Γ ℓ par σ σ' ε τ} (v : Val Γ τ) (h : Handler Γ ℓ par σ σ' ε) → subH (cons v idSub) (renH S h) ≡ h
weaken1-sub1-cancelH v h = trans (subH-renH-fuse (cons v idSub) S h) (subH-idSub h)

-- The other substitution gap Lemma A.9 needs: plugging a FRESH bound
-- variable into a (weakened) frame's hole, then substituting that
-- variable back to v, collapses to plugging v into the frame directly
-- -- i.e. "F[x][v/x] = F[v]", by exhaustive case analysis on F (its
-- subcomponents, all closed since F : Frame ∅ ..., are individually
-- restored by weaken1-sub1-cancelE/V/H).
subE-plugF-weaken1F : ∀ {α τ ε} (F : Frame ∅ α ε τ ε) (v : Val ∅ α)
                     → subE (cons v idSub) (plugF (weaken1F F) (val (vvar Z))) ≡ plugF F (val v)
subE-plugF-weaken1F (F-fun f)       v = refl
subE-plugF-weaken1F (F-pairL e)     v = cong (pair (val v)) (weaken1-sub1-cancelE v e)
subE-plugF-weaken1F (F-pairR w)     v = cong (λ w' → pair (val w') (val v)) (weaken1V-sub1-cancel v w)
subE-plugF-weaken1F F-fst           v = refl
subE-plugF-weaken1F F-snd           v = refl
subE-plugF-weaken1F (F-appL e)      v = cong (app (val v)) (weaken1-sub1-cancelE v e)
subE-plugF-weaken1F (F-appR w)      v = cong (λ w' → app (val w') (val v)) (weaken1V-sub1-cancel v w)
subE-plugF-weaken1F (F-op m op)     v = refl
subE-plugF-weaken1F F-loss          v = refl
subE-plugF-weaken1F (F-handleP h b) v = cong₂ (λ h' b' → handleE h' (val v) b') (weaken1-sub1-cancelH v h) (weaken1-sub1-cancelE v b)
subE-plugF-weaken1F (F-plusL e)     v = cong (plusE (val v)) (weaken1-sub1-cancelE v e)
subE-plugF-weaken1F (F-plusR w)     v = cong (λ w' → plusE (val w') (val v)) (weaken1V-sub1-cancel v w)

-- Lemma A.9: if F is a regular frame such that F[v]:τ!ε is (fully)
-- computable for every computable v:α, then F[e] is (fully) computable
-- for any (fully) computable e:α!ε. The workhorse behind pushing
-- regular-frame congruence through a computability argument -- used
-- throughout Lemma A.11 wherever a subexpression sits under an
-- F-fun/F-pairL/.../F-handleP frame.
--
-- Unlike Lemma A.6/A.7/A.8's own {g}-inductions (all of which invert
-- steps via S2/S3/R7/R8/R9/Rplus -- rules whose CONCLUSION ambient is
-- an implicit, unconstrained metavariable, freely unifying with
-- whatever the surrounding proof needs), F-rule's conclusion ambient
-- is tied DIRECTLY to its own explicit `sub` argument, which itself
-- gets baked into the boosted continuation its premise demands
-- (`vabs (thenE sub ...)`). So inverting a step of F[e] at an
-- otherwise-arbitrary ambient (subX, g) forces the boosted
-- continuation used to also be subX/g-specific -- there is no single
-- FIXED continuation g' (as in Lemma A.6/A.7-1's own glocalE-based
-- proofs) that simultaneously matches every possible (subX, g). The
-- induction is therefore carried out w.r.t. a FAMILY of continuations
-- (GboostedFamily below: "g'' is the (subX,g)-boosted continuation,
-- for SOME loss-computable g and matching subX" -- existentially
-- quantified, not tied to the ambient sub/g slot GComputable's own
-- gc-step exposes) rather than Lemma A.6's single-valued Gsingle --
-- and, since nothing is fixed ahead of time, the conclusion comes out
-- at FULL strength (every g), not just {g}-computability for one g.
lemma-A9 : ∀ {α τ ε} (F : Frame ∅ α ε τ ε)
         → (∀ {v : Val ∅ α} → ComputableV α v → ComputableE τ ε (plugF F (val v)))
         → ∀ {e : ∅ ⊢ α ! ε} → ComputableE α ε e
         → ComputableE τ ε (plugF F e)
lemma-A9 {α} {τ} {ε} F Fcomp {e} compE = go compE'
  where
  boosted : ∀ {ε' : EffCxt} → ε' ⊆ᵉ ε → LC ∅ τ ε' → LC ∅ α ε
  boosted {ε'} subX g = vabs (thenE subX (plugF (weaken1F F) (val (vvar Z))) (weaken1V g))

  GboostedFamily : ∀ {εg} → εg ⊆ᵉ ε → LC ∅ α εg → Set
  GboostedFamily {εg} _ g'' = Σ (εg ≡ ε) (λ eq → Σ EffCxt (λ ε' → Σ (ε' ⊆ᵉ ε) (λ subX → Σ (LC ∅ τ ε') (λ g →
    LossComputable (ComputableV τ) g × subst (LC ∅ α) eq g'' ≡ boosted subX g))))

  boosted-lossComp : ∀ {ε' : EffCxt} {subX : ε' ⊆ᵉ ε} {g : LC ∅ τ ε'} → LossComputable (ComputableV τ) g
                    → LossComputable (ComputableV α) (boosted subX g)
  boosted-lossComp {subX = subX} lossCompG = lemma-A8-3 subX lossCompG Fcomp''
    where
    Fcomp'' : ∀ {v : Val ∅ α} → ComputableV α v → ComputableE τ ε ((plugF (weaken1F F) (val (vvar Z))) [ v ])
    Fcomp'' {v} Pv = subst (ComputableE τ ε) (sym (subE-plugF-weaken1F F v)) (Fcomp Pv)

  compE' : GComputable (ComputableV α) GboostedFamily e
  compE' = GComputable-antimono {σ = α} {ε = ε}
             {G = λ _ g0 → LossComputable (ComputableV α) g0} {G' = GboostedFamily}
             (λ { (refl , ε' , subX , g , lossCompG , refl) → boosted-lossComp lossCompG }) compE
  go : ∀ {e} → GComputable (ComputableV α) GboostedFamily e → ComputableE τ ε (plugF F e)
  go (gc-val {v} Pv) = Fcomp Pv
  go (gc-stuck {K = K} nh ihK ihKt) = gc-stuck {K = F∘ K F} nh (λ {v1} → go (ihK {v1})) (λ {v1} → go (ihKt {v1}))
  go (gc-step {e0} nterm ih) = gc-step nterm' step-case
    where
    nterm' : ¬ Terminal (plugF F e0)
    nterm' term with progress-dichotomy {sub = ⊆ᵉ-refl} {g = boosted ⊆ᵉ-refl zeroLC} e0
    ... | inj₁ t = nterm t
    ... | inj₂ (r0 , e0' , stp0) = theorem-A4-1 {sub = ⊆ᵉ-refl} {g = zeroLC} term (F-rule ⊆ᵉ-refl F stp0)
    step-case : ∀ {εg} {subX : εg ⊆ᵉ ε} {g₁ : LC ∅ τ εg} → LossComputable (ComputableV τ) g₁
              → ∀ {r2 e''} → _⊢_-[_]→_ {sub = subX} g₁ (plugF F e0) r2 e''
              → ComputableE τ ε e''
    step-case {subX = subX} {g₁ = g₁} lossCompG1 stp
      with progress-dichotomy {sub = ⊆ᵉ-refl} {g = boosted subX g₁} e0
    ... | inj₁ t = ⊥-elim (nterm t)
    ... | inj₂ (r0 , e0'' , stp0) with step-det-with (F-rule subX F stp0) stp
    ...   | (refl , refl) = go (ih {sub = ⊆ᵉ-refl} {g = boosted subX g₁} (refl , _ , subX , g₁ , lossCompG1 , refl) stp0)

-- ---------------------------------------------------------------------
-- The last regular-congruence-style prerequisite Lemma A.11 needs:
-- "reset e is computable given e is" (its own case 5(d), proven there
-- by an inline L_σ,ε-induction on e). Much simpler than Lemma A.9's F
-- case: S4's own conclusion evaluates e under the very SAME ambient g
-- (no boosted continuation, no antimono narrowing needed at all) --
-- Terminal(reset e) is refuted uniformly via theorem-A4-1 applied to
-- whichever of R9 (e a value)/S4 (e steps) actually fires, using
-- progress-dichotomy on e itself to rule out e being stuck (which nterm
-- already excludes in the gc-step case).
-- ---------------------------------------------------------------------

lemma-reset : ∀ {σ ε} {e : ∅ ⊢ σ ! ε} → ComputableE σ ε e → ComputableE σ ε (resetE e)
lemma-reset {σ} {ε} = go
  where
  go : ∀ {e} → ComputableE σ ε e → ComputableE σ ε (resetE e)
  go (gc-val {v} Pv) = gc-step nterm' step-case
    where
    nterm' : ¬ Terminal (resetE (val v))
    nterm' t = theorem-A4-1 {sub = ⊆ᵉ-refl} {g = zeroLC} t (R9 v)
    step-case : ∀ {εg} {subX : εg ⊆ᵉ ε} {g₁ : LC ∅ σ εg} → LossComputable (ComputableV σ) g₁
              → ∀ {r e'} → _⊢_-[_]→_ {sub = subX} g₁ (resetE (val v)) r e' → ComputableE σ ε e'
    step-case {subX = subX} {g₁ = g₁} _ stp with step-det-with (R9 {sub = subX} {g = g₁} v) stp
    ... | (refl , refl) = gc-val Pv
  go (gc-stuck {K = K} nh ihK ihKt) = gc-stuck {K = S∘ K S-reset} nh (λ {v1} → go (ihK {v1})) (λ {v1} → go (ihKt {v1}))
  go (gc-step {e0} nterm ih) = gc-step nterm' step-case
    where
    nterm' : ¬ Terminal (resetE e0)
    nterm' t with progress-dichotomy {sub = ⊆ᵉ-refl} {g = zeroLC} e0
    ... | inj₁ te0 = nterm te0
    ... | inj₂ (r0 , e0' , stp0) = theorem-A4-1 {sub = ⊆ᵉ-refl} {g = zeroLC} t (S4 stp0)
    step-case : ∀ {εg} {subX : εg ⊆ᵉ ε} {g₁ : LC ∅ σ εg} → LossComputable (ComputableV σ) g₁
              → ∀ {r e'} → _⊢_-[_]→_ {sub = subX} g₁ (resetE e0) r e' → ComputableE σ ε e'
    step-case {subX = subX} {g₁ = g₁} lossCompG1 stp
      with progress-dichotomy {sub = subX} {g = g₁} e0
    ... | inj₁ t = ⊥-elim (nterm t)
    ... | inj₂ (r0 , e0'' , stp0) with step-det-with (S4 {sub = subX} {g = g₁} stp0) stp
    ...   | (refl , refl) = go (ih {sub = subX} {g = g₁} lossCompG1 stp0)

-- ---------------------------------------------------------------------
-- A further substitution-algebra layer Lemma A.10 needs: composing TWO
-- substitutions (retApplied's own substitution of the handler param,
-- then the OUTER substitution of the return value) into a single one,
-- to match R6's own one-shot conclusion. Built bottom-up: pointwise
-- renaming congruence and rename-rename fusion first (renV-renV-fuse),
-- since rename-then-substitute fusion's own vabs case needs it, and
-- THAT in turn is what substitute-then-substitute fusion's own vabs
-- case needs.
-- ---------------------------------------------------------------------

mutual
  renV-cong : ∀ {Γ Γ' σ} {ρ ρ' : Ren Γ Γ'} → (∀ {τ} (x : Γ ∋ τ) → ρ x ≡ ρ' x) → (v : Val Γ σ) → renV ρ v ≡ renV ρ' v
  renV-cong eq (vvar x)    = cong vvar (eq x)
  renV-cong eq (vgnd x)    = refl
  renV-cong eq (vpair v w) = cong₂ vpair (renV-cong eq v) (renV-cong eq w)
  renV-cong eq (vabs e)    = cong vabs (renE-cong (extR-cong eq) e)

  extR-cong : ∀ {Γ Γ' τ0} {ρ ρ' : Ren Γ Γ'} → (∀ {τ} (x : Γ ∋ τ) → ρ x ≡ ρ' x) → ∀ {τ} (x : (Γ , τ0) ∋ τ) → extR ρ x ≡ extR ρ' x
  extR-cong eq Z     = refl
  extR-cong eq (S x) = cong S (eq x)

  renH-cong : ∀ {Γ Γ' ℓ par σ σ' ε} {ρ ρ' : Ren Γ Γ'} → (∀ {τ} (x : Γ ∋ τ) → ρ x ≡ ρ' x) → (h : Handler Γ ℓ par σ σ' ε) → renH ρ h ≡ renH ρ' h
  renH-cong eq h = Handler-eq
    (λ op → renE-cong (extR-cong (extR-cong (extR-cong (extR-cong eq)))) (clause h op))
    (renE-cong (extR-cong (extR-cong eq)) (ret h))

  renE-cong : ∀ {Γ Γ' σ ε} {ρ ρ' : Ren Γ Γ'} → (∀ {τ} (x : Γ ∋ τ) → ρ x ≡ ρ' x) → (e : Γ ⊢ σ ! ε) → renE ρ e ≡ renE ρ' e
  renE-cong eq (val v)          = cong val (renV-cong eq v)
  renE-cong eq (fun f e)        = cong (fun f) (renE-cong eq e)
  renE-cong eq (pair e e₁)      = cong₂ pair (renE-cong eq e) (renE-cong eq e₁)
  renE-cong eq (fst e)          = cong fst (renE-cong eq e)
  renE-cong eq (snd e)          = cong snd (renE-cong eq e)
  renE-cong eq (app e e₁)       = cong₂ app (renE-cong eq e) (renE-cong eq e₁)
  renE-cong eq (opE m op e)     = cong (opE m op) (renE-cong eq e)
  renE-cong eq (lossE e)        = cong lossE (renE-cong eq e)
  renE-cong eq (thenE s e g)    = cong₂ (thenE s) (renE-cong eq e) (renV-cong eq g)
  renE-cong eq (plusE e1 e2)    = cong₂ plusE (renE-cong eq e1) (renE-cong eq e2)
  renE-cong eq (glocalE s1 s2 e g) = cong₂ (glocalE s1 s2) (renE-cong eq e) (renV-cong eq g)
  renE-cong eq (resetE e)       = cong resetE (renE-cong eq e)
  renE-cong {ρ = ρ} {ρ' = ρ'} eq (handleE h e e₁) =
    trans (cong (λ h' → handleE h' (renE ρ e) (renE ρ e₁)) (renH-cong eq h))
          (cong₂ (handleE (renH ρ' h)) (renE-cong eq e) (renE-cong eq e₁))

extR-extR-pointwise : ∀ {Γ Γ' Γ'' τ0 τ} (ρ2 : Ren Γ' Γ'') (ρ1 : Ren Γ Γ') (x : (Γ , τ0) ∋ τ)
                     → extR ρ2 (extR ρ1 x) ≡ extR (λ y → ρ2 (ρ1 y)) x
extR-extR-pointwise ρ2 ρ1 Z     = refl
extR-extR-pointwise ρ2 ρ1 (S x) = refl

extR²-extR²-pointwise : ∀ {Γ Γ' Γ'' τ0 τ1 τ} (ρ2 : Ren Γ' Γ'') (ρ1 : Ren Γ Γ') (x : ((Γ , τ0) , τ1) ∋ τ)
                       → extR (extR ρ2) (extR (extR ρ1) x) ≡ extR (extR (λ y → ρ2 (ρ1 y))) x
extR²-extR²-pointwise ρ2 ρ1 Z     = refl
extR²-extR²-pointwise ρ2 ρ1 (S x) = cong S (extR-extR-pointwise ρ2 ρ1 x)

extR³-extR³-pointwise : ∀ {Γ Γ' Γ'' τ0 τ1 τ2 τ} (ρ2 : Ren Γ' Γ'') (ρ1 : Ren Γ Γ') (x : (((Γ , τ0) , τ1) , τ2) ∋ τ)
                       → extR (extR (extR ρ2)) (extR (extR (extR ρ1)) x) ≡ extR (extR (extR (λ y → ρ2 (ρ1 y)))) x
extR³-extR³-pointwise ρ2 ρ1 Z     = refl
extR³-extR³-pointwise ρ2 ρ1 (S x) = cong S (extR²-extR²-pointwise ρ2 ρ1 x)

extR⁴-extR⁴-pointwise : ∀ {Γ Γ' Γ'' τ0 τ1 τ2 τ3 τ} (ρ2 : Ren Γ' Γ'') (ρ1 : Ren Γ Γ') (x : ((((Γ , τ0) , τ1) , τ2) , τ3) ∋ τ)
                       → extR (extR (extR (extR ρ2))) (extR (extR (extR (extR ρ1))) x) ≡ extR (extR (extR (extR (λ y → ρ2 (ρ1 y))))) x
extR⁴-extR⁴-pointwise ρ2 ρ1 Z     = refl
extR⁴-extR⁴-pointwise ρ2 ρ1 (S x) = cong S (extR³-extR³-pointwise ρ2 ρ1 x)

mutual
  renV-renV-fuse : ∀ {Γ Γ' Γ'' σ} (ρ2 : Ren Γ' Γ'') (ρ1 : Ren Γ Γ') (v : Val Γ σ)
                  → renV ρ2 (renV ρ1 v) ≡ renV (λ x → ρ2 (ρ1 x)) v
  renV-renV-fuse ρ2 ρ1 (vvar x)    = refl
  renV-renV-fuse ρ2 ρ1 (vgnd x)    = refl
  renV-renV-fuse ρ2 ρ1 (vpair v w) = cong₂ vpair (renV-renV-fuse ρ2 ρ1 v) (renV-renV-fuse ρ2 ρ1 w)
  renV-renV-fuse ρ2 ρ1 (vabs e)    =
    cong vabs (trans (renE-renE-fuse (extR ρ2) (extR ρ1) e)
                      (renE-cong (extR-extR-pointwise ρ2 ρ1) e))

  renH-renH-fuse : ∀ {Γ Γ' Γ'' ℓ par σ σ' ε} (ρ2 : Ren Γ' Γ'') (ρ1 : Ren Γ Γ') (h : Handler Γ ℓ par σ σ' ε)
                  → renH ρ2 (renH ρ1 h) ≡ renH (λ x → ρ2 (ρ1 x)) h
  renH-renH-fuse ρ2 ρ1 h = Handler-eq
    (λ op → trans (renE-renE-fuse (extR (extR (extR (extR ρ2)))) (extR (extR (extR (extR ρ1)))) (clause h op))
                  (renE-cong (extR⁴-extR⁴-pointwise ρ2 ρ1) (clause h op)))
    (trans (renE-renE-fuse (extR (extR ρ2)) (extR (extR ρ1)) (ret h))
           (renE-cong (extR²-extR²-pointwise ρ2 ρ1) (ret h)))

  renE-renE-fuse : ∀ {Γ Γ' Γ'' σ ε} (ρ2 : Ren Γ' Γ'') (ρ1 : Ren Γ Γ') (e : Γ ⊢ σ ! ε)
                  → renE ρ2 (renE ρ1 e) ≡ renE (λ x → ρ2 (ρ1 x)) e
  renE-renE-fuse ρ2 ρ1 (val v)          = cong val (renV-renV-fuse ρ2 ρ1 v)
  renE-renE-fuse ρ2 ρ1 (fun f e)        = cong (fun f) (renE-renE-fuse ρ2 ρ1 e)
  renE-renE-fuse ρ2 ρ1 (pair e e₁)      = cong₂ pair (renE-renE-fuse ρ2 ρ1 e) (renE-renE-fuse ρ2 ρ1 e₁)
  renE-renE-fuse ρ2 ρ1 (fst e)          = cong fst (renE-renE-fuse ρ2 ρ1 e)
  renE-renE-fuse ρ2 ρ1 (snd e)          = cong snd (renE-renE-fuse ρ2 ρ1 e)
  renE-renE-fuse ρ2 ρ1 (app e e₁)       = cong₂ app (renE-renE-fuse ρ2 ρ1 e) (renE-renE-fuse ρ2 ρ1 e₁)
  renE-renE-fuse ρ2 ρ1 (opE m op e)     = cong (opE m op) (renE-renE-fuse ρ2 ρ1 e)
  renE-renE-fuse ρ2 ρ1 (lossE e)        = cong lossE (renE-renE-fuse ρ2 ρ1 e)
  renE-renE-fuse ρ2 ρ1 (thenE s e g)    = cong₂ (thenE s) (renE-renE-fuse ρ2 ρ1 e) (renV-renV-fuse ρ2 ρ1 g)
  renE-renE-fuse ρ2 ρ1 (plusE e1 e2)    = cong₂ plusE (renE-renE-fuse ρ2 ρ1 e1) (renE-renE-fuse ρ2 ρ1 e2)
  renE-renE-fuse ρ2 ρ1 (glocalE s1 s2 e g) = cong₂ (glocalE s1 s2) (renE-renE-fuse ρ2 ρ1 e) (renV-renV-fuse ρ2 ρ1 g)
  renE-renE-fuse ρ2 ρ1 (resetE e)       = cong resetE (renE-renE-fuse ρ2 ρ1 e)
  renE-renE-fuse ρ2 ρ1 (handleE h e e₁) =
    trans (cong (λ h' → handleE h' (renE ρ2 (renE ρ1 e)) (renE ρ2 (renE ρ1 e₁))) (renH-renH-fuse ρ2 ρ1 h))
          (cong₂ (handleE (renH (λ x → ρ2 (ρ1 x)) h)) (renE-renE-fuse ρ2 ρ1 e) (renE-renE-fuse ρ2 ρ1 e₁))

-- "weaken then substitute (or rename) commutes with weaken" -- the
-- pointwise engine behind every depth->1 extR-extS/extS-extS-pointwise
-- S-case below (each such case is exactly one of these two facts,
-- composed with the depth-(n-1) fact at the peeled-off variable).
renV-S-commute : ∀ {Γ Γ' τ0 σ} (ρ : Ren Γ Γ') (v : Val Γ σ) → renV (extR {τ = τ0} ρ) (renV S v) ≡ renV S (renV ρ v)
renV-S-commute ρ v = trans (renV-renV-fuse (extR ρ) S v) (sym (renV-renV-fuse S ρ v))

extR-extS-pointwise : ∀ {Γ Γ' Γ'' τ0 τ} (ρ : Ren Γ' Γ'') (σs : Sub Γ Γ') (x : (Γ , τ0) ∋ τ)
                     → renV (extR ρ) (extS σs x) ≡ extS (λ y → renV ρ (σs y)) x
extR-extS-pointwise ρ σs Z     = refl
extR-extS-pointwise ρ σs (S x) = renV-S-commute ρ (σs x)

extR²-extS²-pointwise : ∀ {Γ Γ' Γ'' τ0 τ1 τ} (ρ : Ren Γ' Γ'') (σs : Sub Γ Γ') (x : ((Γ , τ0) , τ1) ∋ τ)
                       → renV (extR (extR ρ)) (extS (extS σs) x) ≡ extS (extS (λ y → renV ρ (σs y))) x
extR²-extS²-pointwise ρ σs Z     = refl
extR²-extS²-pointwise ρ σs (S x) = trans (renV-S-commute (extR ρ) (extS σs x)) (cong (renV S) (extR-extS-pointwise ρ σs x))

extR³-extS³-pointwise : ∀ {Γ Γ' Γ'' τ0 τ1 τ2 τ} (ρ : Ren Γ' Γ'') (σs : Sub Γ Γ') (x : (((Γ , τ0) , τ1) , τ2) ∋ τ)
                       → renV (extR (extR (extR ρ))) (extS (extS (extS σs)) x) ≡ extS (extS (extS (λ y → renV ρ (σs y)))) x
extR³-extS³-pointwise ρ σs Z     = refl
extR³-extS³-pointwise ρ σs (S x) = trans (renV-S-commute (extR (extR ρ)) (extS (extS σs) x)) (cong (renV S) (extR²-extS²-pointwise ρ σs x))

extR⁴-extS⁴-pointwise : ∀ {Γ Γ' Γ'' τ0 τ1 τ2 τ3 τ} (ρ : Ren Γ' Γ'') (σs : Sub Γ Γ') (x : ((((Γ , τ0) , τ1) , τ2) , τ3) ∋ τ)
                       → renV (extR (extR (extR (extR ρ)))) (extS (extS (extS (extS σs))) x) ≡ extS (extS (extS (extS (λ y → renV ρ (σs y))))) x
extR⁴-extS⁴-pointwise ρ σs Z     = refl
extR⁴-extS⁴-pointwise ρ σs (S x) = trans (renV-S-commute (extR (extR (extR ρ))) (extS (extS (extS σs)) x)) (cong (renV S) (extR³-extS³-pointwise ρ σs x))

mutual
  renV-subV-fuse : ∀ {Γ Γ' Γ'' σ} (ρ : Ren Γ' Γ'') (σs : Sub Γ Γ') (v : Val Γ σ)
                  → renV ρ (subV σs v) ≡ subV (λ x → renV ρ (σs x)) v
  renV-subV-fuse ρ σs (vvar x)    = refl
  renV-subV-fuse ρ σs (vgnd x)    = refl
  renV-subV-fuse ρ σs (vpair v w) = cong₂ vpair (renV-subV-fuse ρ σs v) (renV-subV-fuse ρ σs w)
  renV-subV-fuse ρ σs (vabs e)    =
    cong vabs (trans (renE-subE-fuse (extR ρ) (extS σs) e)
                      (subE-cong (extR-extS-pointwise ρ σs) e))

  renH-subH-fuse : ∀ {Γ Γ' Γ'' ℓ par σ σ' ε} (ρ : Ren Γ' Γ'') (σs : Sub Γ Γ') (h : Handler Γ ℓ par σ σ' ε)
                  → renH ρ (subH σs h) ≡ subH (λ x → renV ρ (σs x)) h
  renH-subH-fuse ρ σs h = Handler-eq
    (λ op → trans (renE-subE-fuse (extR (extR (extR (extR ρ)))) (extS (extS (extS (extS σs)))) (clause h op))
                  (subE-cong (extR⁴-extS⁴-pointwise ρ σs) (clause h op)))
    (trans (renE-subE-fuse (extR (extR ρ)) (extS (extS σs)) (ret h))
           (subE-cong (extR²-extS²-pointwise ρ σs) (ret h)))

  renE-subE-fuse : ∀ {Γ Γ' Γ'' σ ε} (ρ : Ren Γ' Γ'') (σs : Sub Γ Γ') (e : Γ ⊢ σ ! ε)
                  → renE ρ (subE σs e) ≡ subE (λ x → renV ρ (σs x)) e
  renE-subE-fuse ρ σs (val v)          = cong val (renV-subV-fuse ρ σs v)
  renE-subE-fuse ρ σs (fun f e)        = cong (fun f) (renE-subE-fuse ρ σs e)
  renE-subE-fuse ρ σs (pair e e₁)      = cong₂ pair (renE-subE-fuse ρ σs e) (renE-subE-fuse ρ σs e₁)
  renE-subE-fuse ρ σs (fst e)          = cong fst (renE-subE-fuse ρ σs e)
  renE-subE-fuse ρ σs (snd e)          = cong snd (renE-subE-fuse ρ σs e)
  renE-subE-fuse ρ σs (app e e₁)       = cong₂ app (renE-subE-fuse ρ σs e) (renE-subE-fuse ρ σs e₁)
  renE-subE-fuse ρ σs (opE m op e)     = cong (opE m op) (renE-subE-fuse ρ σs e)
  renE-subE-fuse ρ σs (lossE e)        = cong lossE (renE-subE-fuse ρ σs e)
  renE-subE-fuse ρ σs (thenE s e g)    = cong₂ (thenE s) (renE-subE-fuse ρ σs e) (renV-subV-fuse ρ σs g)
  renE-subE-fuse ρ σs (plusE e1 e2)    = cong₂ plusE (renE-subE-fuse ρ σs e1) (renE-subE-fuse ρ σs e2)
  renE-subE-fuse ρ σs (glocalE s1 s2 e g) = cong₂ (glocalE s1 s2) (renE-subE-fuse ρ σs e) (renV-subV-fuse ρ σs g)
  renE-subE-fuse ρ σs (resetE e)       = cong resetE (renE-subE-fuse ρ σs e)
  renE-subE-fuse ρ σs (handleE h e e₁) =
    trans (cong (λ h' → handleE h' (renE ρ (subE σs e)) (renE ρ (subE σs e₁))) (renH-subH-fuse ρ σs h))
          (cong₂ (handleE (subH (λ x → renV ρ (σs x)) h)) (renE-subE-fuse ρ σs e) (renE-subE-fuse ρ σs e₁))

subV-S-commute : ∀ {Γ Γ' τ0 σ} (σs : Sub Γ Γ') (v : Val Γ σ) → subV (extS {τ = τ0} σs) (renV S v) ≡ renV S (subV σs v)
subV-S-commute σs v = trans (subV-renV-fuse (extS σs) S v) (sym (renV-subV-fuse S σs v))

extS-extS-pointwise : ∀ {Γ Γ' Γ'' τ0 τ} (σs2 : Sub Γ' Γ'') (σs1 : Sub Γ Γ') (x : (Γ , τ0) ∋ τ)
                     → subV (extS σs2) (extS σs1 x) ≡ extS (λ y → subV σs2 (σs1 y)) x
extS-extS-pointwise σs2 σs1 Z     = refl
extS-extS-pointwise σs2 σs1 (S x) = subV-S-commute σs2 (σs1 x)

extS²-extS²-pointwise : ∀ {Γ Γ' Γ'' τ0 τ1 τ} (σs2 : Sub Γ' Γ'') (σs1 : Sub Γ Γ') (x : ((Γ , τ0) , τ1) ∋ τ)
                       → subV (extS (extS σs2)) (extS (extS σs1) x) ≡ extS (extS (λ y → subV σs2 (σs1 y))) x
extS²-extS²-pointwise σs2 σs1 Z     = refl
extS²-extS²-pointwise σs2 σs1 (S x) = trans (subV-S-commute (extS σs2) (extS σs1 x)) (cong (renV S) (extS-extS-pointwise σs2 σs1 x))

extS³-extS³-pointwise : ∀ {Γ Γ' Γ'' τ0 τ1 τ2 τ} (σs2 : Sub Γ' Γ'') (σs1 : Sub Γ Γ') (x : (((Γ , τ0) , τ1) , τ2) ∋ τ)
                       → subV (extS (extS (extS σs2))) (extS (extS (extS σs1)) x) ≡ extS (extS (extS (λ y → subV σs2 (σs1 y)))) x
extS³-extS³-pointwise σs2 σs1 Z     = refl
extS³-extS³-pointwise σs2 σs1 (S x) = trans (subV-S-commute (extS (extS σs2)) (extS (extS σs1) x)) (cong (renV S) (extS²-extS²-pointwise σs2 σs1 x))

extS⁴-extS⁴-pointwise : ∀ {Γ Γ' Γ'' τ0 τ1 τ2 τ3 τ} (σs2 : Sub Γ' Γ'') (σs1 : Sub Γ Γ') (x : ((((Γ , τ0) , τ1) , τ2) , τ3) ∋ τ)
                       → subV (extS (extS (extS (extS σs2)))) (extS (extS (extS (extS σs1))) x) ≡ extS (extS (extS (extS (λ y → subV σs2 (σs1 y))))) x
extS⁴-extS⁴-pointwise σs2 σs1 Z     = refl
extS⁴-extS⁴-pointwise σs2 σs1 (S x) = trans (subV-S-commute (extS (extS (extS σs2))) (extS (extS (extS σs1)) x)) (cong (renV S) (extS³-extS³-pointwise σs2 σs1 x))

mutual
  subV-subV-fuse : ∀ {Γ Γ' Γ'' σ} (σs2 : Sub Γ' Γ'') (σs1 : Sub Γ Γ') (v : Val Γ σ)
                  → subV σs2 (subV σs1 v) ≡ subV (λ x → subV σs2 (σs1 x)) v
  subV-subV-fuse σs2 σs1 (vvar x)    = refl
  subV-subV-fuse σs2 σs1 (vgnd x)    = refl
  subV-subV-fuse σs2 σs1 (vpair v w) = cong₂ vpair (subV-subV-fuse σs2 σs1 v) (subV-subV-fuse σs2 σs1 w)
  subV-subV-fuse σs2 σs1 (vabs e)    =
    cong vabs (trans (subE-subE-fuse (extS σs2) (extS σs1) e)
                      (subE-cong (extS-extS-pointwise σs2 σs1) e))

  subH-subH-fuse : ∀ {Γ Γ' Γ'' ℓ par σ σ' ε} (σs2 : Sub Γ' Γ'') (σs1 : Sub Γ Γ') (h : Handler Γ ℓ par σ σ' ε)
                  → subH σs2 (subH σs1 h) ≡ subH (λ x → subV σs2 (σs1 x)) h
  subH-subH-fuse σs2 σs1 h = Handler-eq
    (λ op → trans (subE-subE-fuse (extS (extS (extS (extS σs2)))) (extS (extS (extS (extS σs1)))) (clause h op))
                  (subE-cong (extS⁴-extS⁴-pointwise σs2 σs1) (clause h op)))
    (trans (subE-subE-fuse (extS (extS σs2)) (extS (extS σs1)) (ret h))
           (subE-cong (extS²-extS²-pointwise σs2 σs1) (ret h)))

  subE-subE-fuse : ∀ {Γ Γ' Γ'' σ ε} (σs2 : Sub Γ' Γ'') (σs1 : Sub Γ Γ') (e : Γ ⊢ σ ! ε)
                  → subE σs2 (subE σs1 e) ≡ subE (λ x → subV σs2 (σs1 x)) e
  subE-subE-fuse σs2 σs1 (val v)          = cong val (subV-subV-fuse σs2 σs1 v)
  subE-subE-fuse σs2 σs1 (fun f e)        = cong (fun f) (subE-subE-fuse σs2 σs1 e)
  subE-subE-fuse σs2 σs1 (pair e e₁)      = cong₂ pair (subE-subE-fuse σs2 σs1 e) (subE-subE-fuse σs2 σs1 e₁)
  subE-subE-fuse σs2 σs1 (fst e)          = cong fst (subE-subE-fuse σs2 σs1 e)
  subE-subE-fuse σs2 σs1 (snd e)          = cong snd (subE-subE-fuse σs2 σs1 e)
  subE-subE-fuse σs2 σs1 (app e e₁)       = cong₂ app (subE-subE-fuse σs2 σs1 e) (subE-subE-fuse σs2 σs1 e₁)
  subE-subE-fuse σs2 σs1 (opE m op e)     = cong (opE m op) (subE-subE-fuse σs2 σs1 e)
  subE-subE-fuse σs2 σs1 (lossE e)        = cong lossE (subE-subE-fuse σs2 σs1 e)
  subE-subE-fuse σs2 σs1 (thenE s e g)    = cong₂ (thenE s) (subE-subE-fuse σs2 σs1 e) (subV-subV-fuse σs2 σs1 g)
  subE-subE-fuse σs2 σs1 (plusE e1 e2)    = cong₂ plusE (subE-subE-fuse σs2 σs1 e1) (subE-subE-fuse σs2 σs1 e2)
  subE-subE-fuse σs2 σs1 (glocalE s1 s2 e g) = cong₂ (glocalE s1 s2) (subE-subE-fuse σs2 σs1 e) (subV-subV-fuse σs2 σs1 g)
  subE-subE-fuse σs2 σs1 (resetE e)       = cong resetE (subE-subE-fuse σs2 σs1 e)
  subE-subE-fuse σs2 σs1 (handleE h e e₁) =
    trans (cong (λ h' → handleE h' (subE σs2 (subE σs1 e)) (subE σs2 (subE σs1 e₁))) (subH-subH-fuse σs2 σs1 h))
          (cong₂ (handleE (subH (λ x → subV σs2 (σs1 x)) h)) (subE-subE-fuse σs2 σs1 e) (subE-subE-fuse σs2 σs1 e₁))

-- retApplied h v1, applied to v2, collapses to R6's own one-shot
-- substitution: the composed substitution (cons v2 idSub)∘(cons(vvarZ)
-- (cons(weaken1Vv1)wkSub)) agrees pointwise with cons v2(consv1idSub)
-- -- at Z (retApplied's own vvarZ placeholder) it is v2 directly, and
-- at SZ (retApplied's own weaken1Vv1) it is v1, via
-- weaken1V-sub1-cancel (the same cancellation Lemma A.7(2) needed).
retApplied-sub1 : ∀ {ℓ par σ σ' ε} (h : Handler ∅ ℓ par σ σ' ε) (v1 : Val ∅ (gnd par)) (v2 : Val ∅ σ)
                 → subE (cons v2 idSub) (retApplied h v1) ≡ subE (cons v2 (cons v1 idSub)) (ret h)
retApplied-sub1 {par = par} {σ = σ} h v1 v2 =
  trans (subE-subE-fuse (cons v2 idSub) (cons (vvar Z) (cons (weaken1V v1) wkSub)) (ret h))
        (subE-cong pointwise (ret h))
  where
  pointwise : ∀ {τ} (x : ((∅ , gnd par) , σ) ∋ τ) → subV (cons v2 idSub) ((cons (vvar Z) (cons (weaken1V v1) wkSub)) x) ≡ (cons v2 (cons v1 idSub)) x
  pointwise Z     = refl
  pointwise (S Z) = weaken1V-sub1-cancel v2 v1

-- ---------------------------------------------------------------------
-- Lemma A.10's f_k/f_l are built (R5) from h/K weakened one variable
-- (into the fresh pair-parameter's context) and then, once that pair
-- is destructured, immediately paired back against a concrete value --
-- so plugF/plugS/plugK "commute" with weaken-then-substitute-back
-- (a strictly more general form of subE-plugF-weaken1F above, which is
-- exactly this fact specialised at the plugged-in expression being the
-- bound variable itself, val (vvar Z)).
-- ---------------------------------------------------------------------

subE-plugF-weaken1F-gen : ∀ {α τ ε τ0} (F : Frame ∅ α ε τ ε) (v : Val ∅ τ0) (X : (∅ , τ0) ⊢ α ! ε)
                         → subE (cons v idSub) (plugF (weaken1F F) X) ≡ plugF F (subE (cons v idSub) X)
subE-plugF-weaken1F-gen (F-fun f)       v X = refl
subE-plugF-weaken1F-gen (F-pairL e)     v X = cong (pair (subE (cons v idSub) X)) (weaken1-sub1-cancelE v e)
subE-plugF-weaken1F-gen (F-pairR w)     v X = cong (λ w' → pair (val w') (subE (cons v idSub) X)) (weaken1V-sub1-cancel v w)
subE-plugF-weaken1F-gen F-fst           v X = refl
subE-plugF-weaken1F-gen F-snd           v X = refl
subE-plugF-weaken1F-gen (F-appL e)      v X = cong (app (subE (cons v idSub) X)) (weaken1-sub1-cancelE v e)
subE-plugF-weaken1F-gen (F-appR w)      v X = cong (λ w' → app (val w') (subE (cons v idSub) X)) (weaken1V-sub1-cancel v w)
subE-plugF-weaken1F-gen (F-op m op)     v X = refl
subE-plugF-weaken1F-gen F-loss          v X = refl
subE-plugF-weaken1F-gen (F-handleP h b) v X = cong₂ (λ h' b' → handleE h' (subE (cons v idSub) X) b') (weaken1-sub1-cancelH v h) (weaken1-sub1-cancelE v b)
subE-plugF-weaken1F-gen (F-plusL e)     v X = cong (plusE (subE (cons v idSub) X)) (weaken1-sub1-cancelE v e)
subE-plugF-weaken1F-gen (F-plusR w)     v X = cong (λ w' → plusE (val w') (subE (cons v idSub) X)) (weaken1V-sub1-cancel v w)

subE-plugS-weaken1S-gen : ∀ {α τ ε ε' τ0} (s : SFrame ∅ α ε τ ε') (v : Val ∅ τ0) (X : (∅ , τ0) ⊢ α ! ε)
                         → subE (cons v idSub) (plugS (renS S s) X) ≡ plugS s (subE (cons v idSub) X)
subE-plugS-weaken1S-gen (S-handleB h w) v X = cong₂ (λ h' w' → handleE h' (val w') (subE (cons v idSub) X)) (weaken1-sub1-cancelH v h) (weaken1V-sub1-cancel v w)
subE-plugS-weaken1S-gen (S-then sub g)  v X = cong (thenE sub (subE (cons v idSub) X)) (weaken1V-sub1-cancel v g)
subE-plugS-weaken1S-gen (S-glocal s1 s2 g) v X = cong (glocalE s1 s2 (subE (cons v idSub) X)) (weaken1V-sub1-cancel v g)
subE-plugS-weaken1S-gen S-reset         v X = refl

-- Every regular frame's own hole ambient literally IS its codomain
-- ambient (every one of the 12 constructors uses the same EffCxt
-- variable in both slots) -- but Frame's own general type signature
-- allows them to differ in principle (it is a property of every
-- INHABITANT, not encoded in the type itself), so a frame `f`
-- extracted opaquely from a ContCxt (as F∘'s own second field) is not
-- automatically known to satisfy it until pattern-matched down to a
-- concrete constructor. Needed to let weaken1K-sub1-plugK's own F∘
-- case invoke subE-plugF-weaken1F-gen (which, like every lemma in this
-- file, is stated at a single shared ambient).
Frame-amb-eq : ∀ {Γ σ ε τ ε'} → Frame Γ σ ε τ ε' → ε ≡ ε'
Frame-amb-eq (F-fun f)       = refl
Frame-amb-eq (F-pairL e)     = refl
Frame-amb-eq (F-pairR v)     = refl
Frame-amb-eq F-fst           = refl
Frame-amb-eq F-snd           = refl
Frame-amb-eq (F-appL e)      = refl
Frame-amb-eq (F-appR v)      = refl
Frame-amb-eq (F-op m op)     = refl
Frame-amb-eq F-loss          = refl
Frame-amb-eq (F-handleP h b) = refl
Frame-amb-eq (F-plusL e)     = refl
Frame-amb-eq (F-plusR v)     = refl

weaken1K-sub1-plugK : ∀ {α εα σ ε τ0} (v : Val ∅ τ0) (k : ContCxt ∅ α εα σ ε) (e : (∅ , τ0) ⊢ α ! εα)
                     → subE (cons v idSub) (plugK (weaken1K k) e) ≡ plugK k (subE (cons v idSub) e)
weaken1K-sub1-plugK v ▫        e = refl
weaken1K-sub1-plugK v (F∘ k f) e with Frame-amb-eq f
... | refl = trans (subE-plugF-weaken1F-gen f v (plugK (weaken1K k) e)) (cong (plugF f) (weaken1K-sub1-plugK v k e))
weaken1K-sub1-plugK v (S∘ k s) e = trans (subE-plugS-weaken1S-gen s v (plugK (weaken1K k) e)) (cong (plugS s) (weaken1K-sub1-plugK v k e))

-- ---------------------------------------------------------------------
-- Context congruence: an ambient-INDEPENDENT step of e (one that holds
-- under every sub/g, matching how R1-R4/R6/R2-fst/R2-snd/Rplus are all
-- stated -- unlike F-rule/S1, whose own premise is pinned to a single,
-- boosted ambient) lifts through an ENTIRE evaluation context K, not
-- just a single frame. Lemma A.9 already handles a single regular
-- frame's own boosted-continuation congruence (via GboostedFamily,
-- since its OWN target is Gsingle-restricted and its hole's
-- computability proof is genuinely arbitrary/opaque); this needs no
-- such machinery, since the hypothesis here is already a concrete,
-- ambient-independent STEP WITNESS (not an arbitrary computability
-- proof to induct on) -- so each layer just gets applied directly,
-- instantiating the recursive call at exactly the ambient that layer's
-- own congruence rule demands.
--
-- S2/S4 (S-then/S-reset) do NOT preserve r or the plugged-in shape the
-- way F-rule/S1/S3 do: S2 forces its OWN step index to 0#, hoisting
-- whatever r it was given out into a fresh plusE wrapper (and S4
-- likewise always forces 0#, discarding r entirely) -- so the
-- resulting index and target expression have to be COMPUTED from K
-- itself (K-outer-r/K-target, hoisted up above GComputable's own
-- definition -- gc-stuck's ihK-target field needs to refer to K-target
-- directly), not assumed to stay r/plugK K e' unchanged throughout, the
-- way a naive single-shape statement would.
plugK-cong : ∀ {α εα τ ε} (K : ContCxt ∅ α εα τ ε) {e e' : ∅ ⊢ α ! εα} (r : R)
           → (∀ {εg} {sub : εg ⊆ᵉ εα} {g : LC ∅ α εg} → _⊢_-[_]→_ {sub = sub} g e r e')
           → ∀ {εg2} {sub2 : εg2 ⊆ᵉ ε} {g2 : LC ∅ τ εg2} → _⊢_-[_]→_ {sub = sub2} g2 (plugK K e) (K-outer-r K r) (K-target K r e')
plugK-cong ▫ r hyp = hyp
plugK-cong (F∘ k f) r hyp {sub2 = sub2} {g2 = g2} with Frame-amb-eq f
... | refl =
  F-rule sub2 f (plugK-cong k r hyp {sub2 = ⊆ᵉ-refl} {g2 = vabs (thenE sub2 (plugF (weaken1F f) (val (vvar Z))) (weaken1V g2))})
plugK-cong (S∘ k (S-handleB h v)) r hyp {sub2 = sub2} {g2 = g2} =
  S1 sub2 h v (plugK-cong k r hyp {sub2 = ⊆ᵉ-,ℓ} {g2 = vabs (thenE sub2 (retApplied h v) (weaken1V g2))})
plugK-cong (S∘ k (S-then sub g)) r hyp = S2 sub g (plugK-cong k r hyp {sub2 = sub} {g2 = g})
plugK-cong (S∘ k (S-glocal s1 s2 g)) r hyp = S3 s1 s2 g (plugK-cong k r hyp {sub2 = s1} {g2 = g})
plugK-cong (S∘ k S-reset) r hyp = S4 (plugK-cong k r hyp)

-- ---------------------------------------------------------------------
-- K-target and plugK agree exactly (same term, not just related by a
-- step) whenever K contains no S-then layer: every OTHER K-target
-- clause (F∘/S-handleB/S-glocal/S-reset -- note S-reset itself never
-- introduces a divergence either, since K-target's own S-reset clause
-- doesn't consult K-outer-r at all, only wrapping resetE around
-- whatever the recursive call produces) is syntactically identical to
-- plugK's own clause, recursively. S-then is the ONLY constructor
-- whose K-target clause inserts anything K-outer-r-dependent
-- (the plusE(val(vgnd _))(-) wrapper), so it is the only source of the
-- gap K-settle exists to bridge -- this lemma isolates exactly that,
-- needing no computability at all (a purely syntactic fact).
-- ---------------------------------------------------------------------

data NoSThen : ∀ {α εα τ ε} → ContCxt ∅ α εα τ ε → Set where
  nst-▫        : ∀ {α εα} → NoSThen {α} {εα} ▫
  nst-F        : ∀ {α εα β εβ τ ε} {k : ContCxt ∅ α εα β εβ} {f : Frame ∅ β εβ τ ε}
               → NoSThen k → NoSThen (F∘ k f)
  nst-handleB  : ∀ {α εα ℓ par σ σ' ε} {k : ContCxt ∅ α εα σ (ε ,ℓ ℓ)} {h : Handler ∅ ℓ par σ σ' ε} {w : Val ∅ (gnd par)}
               → NoSThen k → NoSThen (S∘ k (S-handleB h w))
  nst-glocal   : ∀ {α εα σ ε₂ ε₁ ε} {k : ContCxt ∅ α εα σ ε₁} {s1 : ε₂ ⊆ᵉ ε₁} {s2 : ε₁ ⊆ᵉ ε} {g : LC ∅ σ ε₂}
               → NoSThen k → NoSThen (S∘ k (S-glocal s1 s2 g))
  nst-reset    : ∀ {α εα σ ε} {k : ContCxt ∅ α εα σ ε}
               → NoSThen k → NoSThen (S∘ k S-reset)

K-target-plugK-eq : ∀ {α εα τ ε} (K : ContCxt ∅ α εα τ ε) → NoSThen K → (r : R) (e' : ∅ ⊢ α ! εα)
                   → K-target K r e' ≡ plugK K e'
K-target-plugK-eq ▫ nst-▫ r e' = refl
K-target-plugK-eq (F∘ k f) (nst-F nst) r e' = cong (plugF f) (K-target-plugK-eq k nst r e')
K-target-plugK-eq (S∘ k (S-handleB h w)) (nst-handleB nst) r e' = cong (handleE h (val w)) (K-target-plugK-eq k nst r e')
K-target-plugK-eq (S∘ k (S-glocal s1 s2 g)) (nst-glocal nst) r e' = cong (λ x → glocalE s1 s2 x g) (K-target-plugK-eq k nst r e')
K-target-plugK-eq (S∘ k S-reset) (nst-reset nst) r e' = cong resetE (K-target-plugK-eq k nst r e')

-- ---------------------------------------------------------------------
-- What was once "the one gap in this development": R5's f_k/f_l apply
-- their own (single-variable) argument via fst/snd, leaving an
-- fst/snd reduction that has to be pushed through the captured
-- continuation K (same as plugK-cong), landing on
-- "K-target K 0# (val v) is computable given plugK K (val v) is" --
-- exactly the gap NoSThen/K-target-plugK-eq above localise to the
-- S-then layer alone. A first attempt tried extracting this from an
-- ALREADY-BUILT ComputableE witness for plugK K (val v) after the
-- fact (as a standalone postulate, K-settle) and hit a real wall: that
-- style of Tait/reducibility proof does not, in general, let you
-- extract a subterm's own computability from the computability of a
-- compound term built around it.
--
-- Resolved instead by strengthening GComputable's own gc-stuck
-- constructor with a second field (ihK-target, above) carrying the
-- K-target-shaped fact ALONGSIDE the plugK-shaped one, built FORWARD
-- at each of the (few) places in this file that construct a gc-stuck
-- value, using exactly the local facts already in hand there (in
-- particular, the S-then case -- lemma-A8-2 above -- uses lemma-A8-1
-- and K-outer-r-zero to account for the extra plusE(val(vgnd 0#))(-)
-- wrapper K-target's own S-then clause inserts). Lemma A.10's
-- Fcomp-inner (below) then consumes ihK-target directly -- no separate
-- K-settle lemma needed at all. (NoSThen/K-target-plugK-eq above,
-- and the K-settle-NoSThen fragment that used to sit here, are
-- superseded by this -- the general case now holds outright, so the
-- NoSThen-restricted special case is no longer separately needed.)
--
-- ComputableV-acc's own well-founded recursion (over Ty, via _<M_)
-- means a computability proof arriving through an outer arrow-case's
-- own Acc field (e.g. the domain-computability hypothesis ComputableV's
-- arrow clause supplies) carries a DIFFERENT (opaque, pattern-bound)
-- Acc witness than the one <M-wellFounded builds fresh at top level --
-- so Agda's definitional equality does not, by itself, identify
-- ComputableV (σ `× τ) (vpair v1 v2) arriving that way with the
-- "clean" ComputableV σ v1 × ComputableV τ v2 shape. Both are
-- propositionally the very same thing (Acc proofs being
-- interchangeable, per Acc-irrelevant above), so a plain subst along
-- Acc-irrelevant's equality -- applied through ComputableV-acc σ,
-- which is a well-defined FUNCTION of the Acc witness -- discharges
-- this directly, no separate induction on Ty needed.
ComputableV-acc-conv : ∀ {σ} {accX : Acc _<M_ (mVal σ)} {v : Val ∅ σ} → ComputableV-acc σ accX v → ComputableV σ v
ComputableV-acc-conv {σ} {accX} = subst (λ a → ComputableV-acc σ a _) (Acc-irrelevant accX (<M-wellFounded (mVal σ)))

ComputableV-acc-conv-rev : ∀ {σ} {accX : Acc _<M_ (mVal σ)} {v : Val ∅ σ} → ComputableV σ v → ComputableV-acc σ accX v
ComputableV-acc-conv-rev {σ} {accX} = subst (λ a → ComputableV-acc σ a _) (Acc-irrelevant (<M-wellFounded (mVal σ)) accX)

ComputableV-pair-proj : ∀ {σ τ} {accP : Acc _<M_ (mVal (σ `× τ))} (v1 : Val ∅ σ) (v2 : Val ∅ τ)
                       → ComputableV-acc (σ `× τ) accP (vpair v1 v2) → ComputableV σ v1 × ComputableV τ v2
ComputableV-pair-proj {accP = acc rs} v1 v2 (c1 , c2) = ComputableV-acc-conv c1 , ComputableV-acc-conv c2

ComputableV-pair-intro : ∀ {σ τ} (v1 : Val ∅ σ) (v2 : Val ∅ τ) → ComputableV σ v1 → ComputableV τ v2 → ComputableV (σ `× τ) (vpair v1 v2)
ComputableV-pair-intro {σ} {τ} v1 v2 c1 c2 with <M-wellFounded (mVal (σ `× τ))
... | acc rs = ComputableV-acc-conv-rev c1 , ComputableV-acc-conv-rev c2

-- The same Acc-irrelevance issue recurs one level up: ComputableV's
-- own arrow case checks its codomain obligation using ITS OWN nested
-- Acc witness (via the arrow-decrease-cod field), not the fresh one
-- <M-wellFounded builds for the "clean" top-level ComputableE -- so a
-- computability fact built via lemma-A6/lemma-A8-2 (using the clean
-- notion) needs converting to match. Discharged the same way as
-- ComputableV-acc-conv above: ComputableV-acc σ is a function of the
-- Acc witness, so Acc-irrelevant's equality between witnesses gives,
-- via cong, an equality of PREDICATES (ComputableV σ ≡
-- ComputableV-acc σ accX, as functions Val ∅ σ → Set) -- and
-- ComputableE/GComputable's own G field is built UNIFORMLY from
-- whichever predicate P is supplied (λ _ g → LossComputable P g), so
-- substituting P throughout, via a single motive parametrised by P
-- alone, converts the whole GComputable structure at once (no
-- separate induction over its own gc-val/gc-stuck/gc-step shape
-- needed).
ComputableE-acc-conv : ∀ {σ ε} {accX : Acc _<M_ (mVal σ)} {e : ∅ ⊢ σ ! ε}
                      → ComputableE σ ε e
                      → GComputable (ComputableV-acc σ accX) (λ _ g → LossComputable (ComputableV-acc σ accX) g) e
ComputableE-acc-conv {σ} {ε} {accX} {e} = subst motive eq
  where
  eq : ComputableV σ ≡ ComputableV-acc σ accX
  eq = cong (ComputableV-acc σ) (Acc-irrelevant (<M-wellFounded (mVal σ)) accX)
  motive : (Val ∅ σ → Set) → Set
  motive P = GComputable P (λ _ g → LossComputable P g) e

-- The reverse direction: Lemma A.11-E's own app case consumes a
-- ComputableV at an arrow type applied to an argument, landing on an
-- accX-based ComputableE-at obligation that needs converting back
-- down to the clean, top-level ComputableE.
ComputableE-acc-conv-rev : ∀ {σ ε} {accX : Acc _<M_ (mVal σ)} {e : ∅ ⊢ σ ! ε}
                          → GComputable (ComputableV-acc σ accX) (λ _ g → LossComputable (ComputableV-acc σ accX) g) e
                          → ComputableE σ ε e
ComputableE-acc-conv-rev {σ} {ε} {accX} {e} = subst motive eq
  where
  eq : ComputableV-acc σ accX ≡ ComputableV σ
  eq = cong (ComputableV-acc σ) (Acc-irrelevant accX (<M-wellFounded (mVal σ)))
  motive : (Val ∅ σ → Set) → Set
  motive P = GComputable P (λ _ g → LossComputable P g) e

-- ---------------------------------------------------------------------
-- Two small, mechanical consequences needed throughout Lemma A.11:
--
-- value-redex-computable packages the "e is a single, ambient-
-- independent redex reducing to an already-computable e'" pattern
-- (R1/R2-fst/R2-snd/R3/R4/Rplus all have exactly this shape: generic
-- in εg/sub/g, firing regardless of what continuation is in force) --
-- reused for every direct value-value reduction Lemma A.11's own
-- fun/fst/snd/app/lossE/(pair, once both operands are values) cases
-- bottom out on, rather than re-deriving the gc-step/step-det-with
-- boilerplate at each one.
--
-- ComputableV-to-LossComputable bridges ComputableV at an arrow-to-
-- Loss type (the "clean", top-level notion Lemma A.11-V's own vabs
-- case uniformly produces for EVERY value, including one that happens
-- to be a loss continuation) down to LossComputable (the strictly
-- narrower clause-3b notion Lemma A.6/A.8's own machinery expects):
-- clause 4 at Loss quantifies over every loss-computable g'', of which
-- zeroLC is one (zeroLC-lossComputable), so GComputable-antimono
-- narrows a proof valid for all of them down to the zeroLC-only
-- instance RComputable asks for.
-- ---------------------------------------------------------------------

value-redex-computable : ∀ {τ ε} {e : ∅ ⊢ τ ! ε} {r : R} {e' : ∅ ⊢ τ ! ε}
                        → (∀ {εg} {sub : εg ⊆ᵉ ε} {g : LC ∅ τ εg} → _⊢_-[_]→_ {sub = sub} g e r e')
                        → ComputableE τ ε e' → ComputableE τ ε e
value-redex-computable {τ = τ} {ε = ε} {e = e} stpGen comp = gc-step nterm' step-case
  where
  nterm' : ¬ Terminal e
  nterm' t = theorem-A4-1 {sub = ⊆ᵉ-refl} {g = zeroLC} t stpGen
  step-case : ∀ {εg} {subX : εg ⊆ᵉ ε} {g₁ : LC ∅ τ εg} → LossComputable (ComputableV τ) g₁
            → ∀ {r2 e''} → _⊢_-[_]→_ {sub = subX} g₁ e r2 e'' → ComputableE τ ε e''
  step-case {subX = subX} {g₁ = g₁} _ stp with step-det-with (stpGen {sub = subX} {g = g₁}) stp
  ... | (refl , refl) = comp

-- Bridging ComputableV at an arrow-to-Loss type down to LossComputable
-- runs into the very same Acc-witness opacity ComputableV-acc-conv
-- exists to paper over (cg's own domain/codomain obligation, once its
-- ComputableV-acc unfolding is exposed, carries an opaque nested `rs`
-- witness) -- now discharged by the same real ComputableV-acc-conv-rev
-- proof (rather than a bare postulate), landing the codomain check on
-- the WIDE "every loss-computable g''" family (ComputableV-acc Loss
-- being unconditionally ⊤, per Loss's own ground clause, regardless of
-- which Acc witness is threaded through it -- so no separate
-- conversion is even needed there), which GComputable-antimono then
-- narrows down to the zeroLC-only instance RComputable asks for,
-- mirroring RComputable's own local G₀.
ComputableV-arrow-apply : ∀ {σ τ ε} {e : (∅ , σ) ⊢ τ ! ε} → ComputableV (σ ⇒ τ ! ε) (vabs e)
                         → ∀ {v : Val ∅ σ} → ComputableV σ v → ComputableE τ ε (e [ v ])
ComputableV-arrow-apply {σ} {τ} {ε} cg {v} Pv = ComputableE-acc-conv-rev (cg {v} (ComputableV-acc-conv-rev Pv))

-- Full computability at Loss implies R-computability (the
-- {zeroLC}-restricted clause-3a notion): clause 4 quantifies over
-- every loss-computable g'', of which zeroLC is one
-- (zeroLC-lossComputable), so GComputable-antimono narrows a proof
-- valid for all of them down to the zeroLC-only instance -- exactly
-- lemma-A8-3's own inner GComputable-antimono call (further above),
-- just hoisted to its own top-level lemma. Uses Gsingle zeroLC (the
-- SAME shape as RComputable's own local G₀, just the existing,
-- already-battle-tested helper) rather than a freshly re-declared G₀:
-- a locally re-declared G₀ here left the analogous (refl , refl)
-- hypothesis with an unsolved meta, for reasons not fully pinned down
-- (Agda apparently type-checks against Gsingle's own reduction more
-- readily than an equivalent, freshly-written local definition).
ComputableE-Loss-to-RComputable : ∀ {ε} {e : ∅ ⊢ Loss ! ε} → ComputableE Loss ε e → RComputable e
ComputableE-Loss-to-RComputable {ε} {e} ce =
  GComputable-antimono {σ = Loss} {ε = ε}
    {G = λ _ g0 → LossComputable (ComputableV Loss) g0} {G' = Gsingle zeroLC}
    (λ { (refl , refl) {v = v1} → zeroLC-lossComputable {v = v1} }) ce

ComputableV-to-LossComputable : ∀ {σ ε} {g : LC ∅ σ ε} → ComputableV (σ ⇒ Loss ! ε) g → LossComputable (ComputableV σ) g
ComputableV-to-LossComputable {σ} {ε} {g} cg with val-closed-abs g
... | (e' , refl) = go
  where
  go : LossComputable (ComputableV σ) (vabs e')
  go {v'} Pv' = ComputableE-Loss-to-RComputable (ComputableV-arrow-apply cg Pv')

-- A handler h : par,σ!(ε,ℓ) ⇒ σ'!ε is computable if each of its
-- operation clauses (extended open in FOUR variables: the handler
-- param, the operation's own argument, and the two continuations
-- fl/fk R5 threads through) and its return clause (extended open in
-- the param and the handled value) are computable once every free
-- variable is instantiated at a computable closed value -- the
-- paper's own "extend computability to open expressions" remark
-- (page 33), specialised to clause/ret's own fixed context shapes.
ComputableH : ∀ {ℓ par σ σ' ε} → Handler ∅ ℓ par σ σ' ε → Set
ComputableH {ℓ} {par} {σ} {σ'} {ε} h =
  (∀ (op : Op ℓ) {v1 : Val ∅ (gnd par)} {v2 : Val ∅ (gnd (out op))}
     {fl : Val ∅ ((gnd par `× gnd (in′ op)) ⇒ Loss ! ε)} {fk : Val ∅ ((gnd par `× gnd (in′ op)) ⇒ σ' ! ε)}
   → ComputableV (gnd par) v1 → ComputableV (gnd (out op)) v2
   → ComputableV ((gnd par `× gnd (in′ op)) ⇒ Loss ! ε) fl → ComputableV ((gnd par `× gnd (in′ op)) ⇒ σ' ! ε) fk
   → ComputableE σ' ε (subE (cons fk (cons fl (cons v2 (cons v1 idSub)))) (clause h op)))
  × (∀ {v1 : Val ∅ (gnd par)} {v2 : Val ∅ σ}
   → ComputableV (gnd par) v1 → ComputableV σ v2
   → ComputableE σ' ε (subE (cons v2 (cons v1 idSub)) (ret h)))

-- Double-weakening analogues of weaken1V-sub1-cancel/
-- weaken1-sub1-cancelE/weaken1-sub1-cancelH -- cancelling TWO
-- weakenings against a TWO-variable substitution at once, each proved
-- by chaining the underlying *-renE/renV/renH-fuse fact twice against
-- the SAME single-weakening cancellation lemma. Needed below to relate
-- a K/h/g wrapped in TWO nested vabs (Lemma A.10's own curried
-- reconstruction of f_k/f_l, replacing the earlier fst/snd-projecting
-- single-pair-argument encoding) back down to K/h/g applied directly.
-- (Also needed by Lemma A.11's own binder cases further below, which
-- reuse it directly rather than redefining it.)
cons-weaken1V-cancel : ∀ {Γ σ τ} (v : Val ∅ τ) (σs : Sub Γ ∅) (g : Val Γ σ) → subV (cons v σs) (renV S g) ≡ subV σs g
cons-weaken1V-cancel v σs g = subV-renV-fuse (cons v σs) S g

weaken2-sub2-cancelV : ∀ {Γ σ τ1 τ2} (v1 : Val Γ τ1) (v2 : Val Γ τ2) (g : Val Γ σ) → subV (cons v2 (cons v1 idSub)) (renV S (renV S g)) ≡ g
weaken2-sub2-cancelV v1 v2 g = trans (subV-renV-fuse (cons v2 (cons v1 idSub)) S (renV S g)) (weaken1V-sub1-cancel v1 g)

weaken2-sub2-cancelE : ∀ {Γ σ ε τ1 τ2} (v1 : Val Γ τ1) (v2 : Val Γ τ2) (e : Γ ⊢ σ ! ε) → subE (cons v2 (cons v1 idSub)) (renE S (renE S e)) ≡ e
weaken2-sub2-cancelE v1 v2 e = trans (subE-renE-fuse (cons v2 (cons v1 idSub)) S (renE S e)) (weaken1-sub1-cancelE v1 e)

weaken2-sub2-cancelH : ∀ {Γ ℓ par σ σ' ε τ1 τ2} (v1 : Val Γ τ1) (v2 : Val Γ τ2) (h : Handler Γ ℓ par σ σ' ε) → subH (cons v2 (cons v1 idSub)) (renH S (renH S h)) ≡ h
weaken2-sub2-cancelH v1 v2 h = trans (subH-renH-fuse (cons v2 (cons v1 idSub)) S (renH S h)) (weaken1-sub1-cancelH v1 h)

-- Double-weakening analogue of weaken1K-sub1-plugK (itself built from
-- subE-plugF-weaken1F-gen/subE-plugS-weaken1S-gen), mirroring its
-- structural recursion on K exactly but cancelling TWO weakening
-- layers against a two-variable substitution throughout -- everything
-- stays closed (Γ = ∅) exactly as the single-weakening original does,
-- since Frame/SFrame/ContCxt have no substitution operation of their
-- own to fall back on for a genuinely open Γ.
subE-plugF-weaken2F-gen : ∀ {α τ ε τ1 τ2} (F : Frame ∅ α ε τ ε) (v1 : Val ∅ τ1) (v2 : Val ∅ τ2) (X : ((∅ , τ1) , τ2) ⊢ α ! ε)
                         → subE (cons v2 (cons v1 idSub)) (plugF (weaken1F (weaken1F F)) X) ≡ plugF F (subE (cons v2 (cons v1 idSub)) X)
subE-plugF-weaken2F-gen (F-fun f)       v1 v2 X = refl
subE-plugF-weaken2F-gen (F-pairL e)     v1 v2 X = cong (pair (subE (cons v2 (cons v1 idSub)) X)) (weaken2-sub2-cancelE v1 v2 e)
subE-plugF-weaken2F-gen (F-pairR w)     v1 v2 X = cong (λ w' → pair (val w') (subE (cons v2 (cons v1 idSub)) X)) (weaken2-sub2-cancelV v1 v2 w)
subE-plugF-weaken2F-gen F-fst           v1 v2 X = refl
subE-plugF-weaken2F-gen F-snd           v1 v2 X = refl
subE-plugF-weaken2F-gen (F-appL e)      v1 v2 X = cong (app (subE (cons v2 (cons v1 idSub)) X)) (weaken2-sub2-cancelE v1 v2 e)
subE-plugF-weaken2F-gen (F-appR w)      v1 v2 X = cong (λ w' → app (val w') (subE (cons v2 (cons v1 idSub)) X)) (weaken2-sub2-cancelV v1 v2 w)
subE-plugF-weaken2F-gen (F-op m op)     v1 v2 X = refl
subE-plugF-weaken2F-gen F-loss          v1 v2 X = refl
subE-plugF-weaken2F-gen (F-handleP h b) v1 v2 X = cong₂ (λ h' b' → handleE h' (subE (cons v2 (cons v1 idSub)) X) b') (weaken2-sub2-cancelH v1 v2 h) (weaken2-sub2-cancelE v1 v2 b)
subE-plugF-weaken2F-gen (F-plusL e)     v1 v2 X = cong (plusE (subE (cons v2 (cons v1 idSub)) X)) (weaken2-sub2-cancelE v1 v2 e)
subE-plugF-weaken2F-gen (F-plusR w)     v1 v2 X = cong (λ w' → plusE (val w') (subE (cons v2 (cons v1 idSub)) X)) (weaken2-sub2-cancelV v1 v2 w)

subE-plugS-weaken2S-gen : ∀ {α τ ε ε' τ1 τ2} (s : SFrame ∅ α ε τ ε') (v1 : Val ∅ τ1) (v2 : Val ∅ τ2) (X : ((∅ , τ1) , τ2) ⊢ α ! ε)
                         → subE (cons v2 (cons v1 idSub)) (plugS (renS S (renS S s)) X) ≡ plugS s (subE (cons v2 (cons v1 idSub)) X)
subE-plugS-weaken2S-gen (S-handleB h w) v1 v2 X = cong₂ (λ h' w' → handleE h' (val w') (subE (cons v2 (cons v1 idSub)) X)) (weaken2-sub2-cancelH v1 v2 h) (weaken2-sub2-cancelV v1 v2 w)
subE-plugS-weaken2S-gen (S-then sub g)  v1 v2 X = cong (thenE sub (subE (cons v2 (cons v1 idSub)) X)) (weaken2-sub2-cancelV v1 v2 g)
subE-plugS-weaken2S-gen (S-glocal s1 s2 g) v1 v2 X = cong (glocalE s1 s2 (subE (cons v2 (cons v1 idSub)) X)) (weaken2-sub2-cancelV v1 v2 g)
subE-plugS-weaken2S-gen S-reset         v1 v2 X = refl

weaken2K-sub2-plugK : ∀ {α εα σ ε τ1 τ2} (v1 : Val ∅ τ1) (v2 : Val ∅ τ2) (k : ContCxt ∅ α εα σ ε) (e : ((∅ , τ1) , τ2) ⊢ α ! εα)
                     → subE (cons v2 (cons v1 idSub)) (plugK (weaken1K (weaken1K k)) e) ≡ plugK k (subE (cons v2 (cons v1 idSub)) e)
weaken2K-sub2-plugK v1 v2 ▫        e = refl
weaken2K-sub2-plugK v1 v2 (F∘ k f) e with Frame-amb-eq f
... | refl = trans (subE-plugF-weaken2F-gen f v1 v2 (plugK (weaken1K (weaken1K k)) e)) (cong (plugF f) (weaken2K-sub2-plugK v1 v2 k e))
weaken2K-sub2-plugK v1 v2 (S∘ k s) e = trans (subE-plugS-weaken2S-gen s v1 v2 (plugK (weaken1K (weaken1K k)) e)) (cong (plugS s) (weaken2K-sub2-plugK v1 v2 k e))

-- Lemma A.10 (page 34): the handler construct. Proceeds by (full)
-- induction on e's own computability -- e's gc-val/gc-stuck cases use
-- R6/R5 directly (the operation-triggering gc-stuck case further
-- splitting, via _≟ᵉ_, on whether the stuck operation is one of h's
-- own), and the gc-step case mirrors Lemma A.8(1)'s own style (S1
-- playing F-rule's role, Lemma A.8(3) supplying the boosted
-- continuation's loss-computability fresh, per ambient, exactly as
-- Lemma A.8(1) needed for plusE).
lemma-A10 : ∀ {ℓ par σ σ' ε} (h : Handler ∅ ℓ par σ σ' ε) → ComputableH h
          → ∀ {e : ∅ ⊢ σ ! (ε ,ℓ ℓ)} → ComputableE σ (ε ,ℓ ℓ) e
          → ∀ {v0 : Val ∅ (gnd par)} → ComputableV (gnd par) v0
          → ComputableE σ' ε (handleE h (val v0) e)
lemma-A10 {ℓ} {par} {σ} {σ'} {ε} h (hClause , hRet) {e} compE {v0} v0Comp = go compE v0Comp
  where
  go : ∀ {e} → ComputableE σ (ε ,ℓ ℓ) e → ∀ {v : Val ∅ (gnd par)} → ComputableV (gnd par) v → ComputableE σ' ε (handleE h (val v) e)
  go (gc-val {w} wComp) {v} vComp = gc-step (¬Terminal-of-step {sub = ⊆ᵉ-refl} {g = zeroLC} (R6 h v w)) step-case
    where
    step-case : ∀ {εg} {subX : εg ⊆ᵉ ε} {g₁ : LC ∅ σ' εg} → LossComputable (ComputableV σ') g₁
              → ∀ {r2 e''} → _⊢_-[_]→_ {sub = subX} g₁ (handleE h (val v) (val w)) r2 e''
              → GComputable (ComputableV σ') (λ _ g0 → LossComputable (ComputableV σ') g0) e''
    step-case _ stp with step-det-with (R6 h v w) stp
    ... | (refl , refl) = hRet vComp wComp
  go (gc-stuck {ℓ = ℓop} {m = m} {op = op} {v = w} {K = K} nh ihK ihKt) {v} vComp with ℓ ≟ᵉ ℓop
  ... | no neq = gc-stuck {K = S∘ K (S-handleB h v)} (λ { (inj₁ eq2) → neq (sym eq2) ; (inj₂ hk) → nh hk })
                          (λ {w1} → go (ihK {w1}) vComp) (λ {w1} → go (ihKt {w1}) vComp)
  ... | yes eq with eq
  ...   | refl = gc-step (¬Terminal-of-step {sub = ⊆ᵉ-refl} {g = zeroLC} (R5 ⊆ᵉ-refl h v m op w K nh)) step-case
    where
    step-case : ∀ {εg} {subX : εg ⊆ᵉ ε} {g₁ : LC ∅ σ' εg} → LossComputable (ComputableV σ') g₁
              → ∀ {r2 e''} → _⊢_-[_]→_ {sub = subX} g₁ (handleE h (val v) (plugK K (opE m op (val w)))) r2 e''
              → GComputable (ComputableV σ') (λ _ g0 → LossComputable (ComputableV σ') g0) e''
    step-case {εg = εg} {subX = subX} {g₁ = g₁} Gg₁ stp with step-det-with (R5 subX h v m op w K nh) stp
    ... | (refl , refl) = hClause op vComp tt flComp fkComp
      where
      g' : LC (∅ , (gnd par `× gnd (in′ op))) σ' εg
      g' = renV S g₁
      handled : (∅ , (gnd par `× gnd (in′ op))) ⊢ σ' ! ε
      handled = handleE (renH S h) (fst (val (vvar Z))) (plugK (weaken1K K) (snd (val (vvar Z))))
      fk : Val ∅ ((gnd par `× gnd (in′ op)) ⇒ σ' ! ε)
      fk = vabs {σ = gnd par `× gnd (in′ op)} (glocalE subX ⊆ᵉ-refl handled g')
      fl : Val ∅ ((gnd par `× gnd (in′ op)) ⇒ Loss ! ε)
      fl = vabs {σ = gnd par `× gnd (in′ op)} (thenE subX handled g')

      -- {g}-computable "with h from q handle K[y]", for an arbitrary
      -- computable q, given y is fixed and already computable: pushes
      -- snd's own reduction through K (plugK-cong), landing on
      -- K-target (S∘ K (S-handleB h q)) 0# (val y) -- which is
      -- DEFINITIONALLY handleE h (val q) (K-target K 0# (val y))
      -- (K-target's own S-handleB clause), i.e. exactly what
      -- go (ihKt {y}) qComp produces (go's own conclusion, applied to
      -- the OUTER gc-stuck's new ihK-target field). No K-settle needed
      -- (that former postulate's whole reason for existing was to
      -- bridge exactly this gap after the fact; ihKt supplies it
      -- directly, having been built forward at each gc-stuck
      -- construction site instead).
      Fcomp-inner : (p : Val ∅ (gnd par)) (y : Val ∅ (gnd (in′ op))) → ComputableV (gnd (in′ op)) y → ∀ {q : Val ∅ (gnd par)} → ComputableV (gnd par) q
                  → ComputableE σ' ε (handleE h (val q) (plugK K (snd (val (vpair p y)))))
      Fcomp-inner p y yComp {q} qComp = gc-step (¬Terminal-of-step {sub = ⊆ᵉ-refl} {g = zeroLC}
                                        (plugK-cong (S∘ K (S-handleB h q)) 0# (λ {sub} {g} → R2-snd p y) {sub2 = ⊆ᵉ-refl} {g2 = zeroLC}))
                                      step-case2
        where
        step-case2 : ∀ {εg2} {subX2 : εg2 ⊆ᵉ ε} {g₂ : LC ∅ σ' εg2} → LossComputable (ComputableV σ') g₂
                   → ∀ {r3 e'''} → _⊢_-[_]→_ {sub = subX2} g₂ (handleE h (val q) (plugK K (snd (val (vpair p y))))) r3 e'''
                   → GComputable (ComputableV σ') (λ _ g0 → LossComputable (ComputableV σ') g0) e'''
        step-case2 {subX2 = subX2} {g₂ = g₂} _ stp2
          with step-det-with (plugK-cong (S∘ K (S-handleB h q)) 0# (λ {sub} {g} → R2-snd p y) {sub2 = subX2} {g2 = g₂}) stp2
        ... | (refl , refl) = go (ihKt {y}) qComp

      -- Full computability of "with h from (fst (p,y)) handle K[snd
      -- (p,y)]" -- fst's own reduction via F-rule/R2-fst directly
      -- (no plugK-cong needed here, F-handleP being a single frame),
      -- landing on Fcomp-inner at q=p.
      handledComp : (p : Val ∅ (gnd par)) (y : Val ∅ (gnd (in′ op))) → ComputableV (gnd par) p → ComputableV (gnd (in′ op)) y
                  → ComputableE σ' ε (handleE h (fst (val (vpair p y))) (plugK K (snd (val (vpair p y)))))
      handledComp p y pComp yComp = gc-step (¬Terminal-of-step {sub = ⊆ᵉ-refl} {g = zeroLC}
                              (F-rule ⊆ᵉ-refl (F-handleP h (plugK K (snd (val (vpair p y))))) (R2-fst p y)))
                            step-case3
        where
        step-case3 : ∀ {εg3} {subX3 : εg3 ⊆ᵉ ε} {g₃ : LC ∅ σ' εg3} → LossComputable (ComputableV σ') g₃
                   → ∀ {r4 e''''} → _⊢_-[_]→_ {sub = subX3} g₃ (handleE h (fst (val (vpair p y))) (plugK K (snd (val (vpair p y))))) r4 e''''
                   → GComputable (ComputableV σ') (λ _ g0 → LossComputable (ComputableV σ') g0) e''''
        step-case3 {subX3 = subX3} _ stp3
          with step-det-with (F-rule subX3 (F-handleP h (plugK K (snd (val (vpair p y))))) (R2-fst p y)) stp3
        ... | (refl , refl) = Fcomp-inner p y yComp pComp

      -- handled[pyPair] = handleE h (fst(val pyPair)) (plugK K (snd
      -- (val pyPair))), and g'[pyPair] = g₁ -- both via the weaken-
      -- then-substitute-back cancellation lemmas (Lemma A.9's own
      -- weaken1K-sub1-plugK, and Lemma A.7's weaken1-sub1-cancelH/V).
      handled-eq : (p : Val ∅ (gnd par)) (y : Val ∅ (gnd (in′ op))) → subE (cons (vpair p y) idSub) handled
                 ≡ handleE h (fst (val (vpair p y))) (plugK K (snd (val (vpair p y))))
      handled-eq p y = cong₂ (λ h'' k'' → handleE h'' (fst (val (vpair p y))) k'')
                              (weaken1-sub1-cancelH (vpair p y) h)
                              (weaken1K-sub1-plugK (vpair p y) K (snd (val (vvar Z))))
      g'-eq : (p : Val ∅ (gnd par)) (y : Val ∅ (gnd (in′ op))) → subV (cons (vpair p y) idSub) g' ≡ g₁
      g'-eq p y = weaken1V-sub1-cancel (vpair p y) g₁

      fkComp : ComputableV ((gnd par `× gnd (in′ op)) ⇒ σ' ! ε) fk
      fkComp {pyPair} pyComp with val-closed-pair pyPair
      ... | (p , y , refl) =
              ComputableE-acc-conv
                (subst (ComputableE σ' ε) (sym (cong₂ (glocalE subX ⊆ᵉ-refl) (handled-eq p y) (g'-eq p y)))
                      (lemma-A6 subX ⊆ᵉ-refl Gg₁
                        (GComputable-antimono {σ = σ'} {ε = ε}
                          {G = λ _ g0 → LossComputable (ComputableV σ') g0} {G' = Gsingle g₁}
                          (λ { (refl , refl) → Gg₁ })
                          (handledComp p y (proj₁ (ComputableV-pair-proj p y pyComp)) (proj₂ (ComputableV-pair-proj p y pyComp))))))
      flComp : ComputableV ((gnd par `× gnd (in′ op)) ⇒ Loss ! ε) fl
      flComp {pyPair} pyComp with val-closed-pair pyPair
      ... | (p , y , refl) =
              ComputableE-acc-conv {accX = <M-wellFounded (mVal Loss)}
                (subst (ComputableE Loss ε) (sym (cong₂ (thenE subX) (handled-eq p y) (g'-eq p y)))
                      (lemma-A8-2 subX Gg₁
                        (GComputable-antimono {σ = σ'} {ε = ε}
                          {G = λ _ g0 → LossComputable (ComputableV σ') g0} {G' = Gsingle g₁}
                          (λ { (refl , refl) → Gg₁ })
                          (handledComp p y (proj₁ (ComputableV-pair-proj p y pyComp)) (proj₂ (ComputableV-pair-proj p y pyComp))))))
  go (gc-step {e0} nterm ih) {v} vComp = gc-step nterm' step-case
    where
    nterm' : ¬ Terminal (handleE h (val v) e0)
    nterm' term with progress-dichotomy {sub = ⊆ᵉ-,ℓ} {g = vabs (thenE ⊆ᵉ-refl (retApplied h v) (weaken1V zeroLC))} e0
    ... | inj₁ t = nterm t
    ... | inj₂ (r0 , e0' , stp0) = theorem-A4-1 {sub = ⊆ᵉ-refl} {g = zeroLC} term (S1 ⊆ᵉ-refl h v stp0)
    step-case : ∀ {εg} {subX : εg ⊆ᵉ ε} {g₁ : LC ∅ σ' εg} → LossComputable (ComputableV σ') g₁
              → ∀ {r2 e''} → _⊢_-[_]→_ {sub = subX} g₁ (handleE h (val v) e0) r2 e''
              → GComputable (ComputableV σ') (λ _ g0 → LossComputable (ComputableV σ') g0) e''
    step-case {subX = subX} {g₁ = g₁} Gg₁ stp
      with progress-dichotomy {sub = ⊆ᵉ-,ℓ} {g = vabs (thenE subX (retApplied h v) (weaken1V g₁))} e0
    ... | inj₁ t = ⊥-elim (nterm t)
    ... | inj₂ (r0 , e0'' , stp0) with step-det-with (S1 subX h v stp0) stp
    ...   | (refl , refl) =
            go (ih {sub = ⊆ᵉ-,ℓ} {g = vabs (thenE subX (retApplied h v) (weaken1V g₁))}
                   (lemma-A8-3 subX Gg₁ hRet') stp0) vComp
      where
      hRet' : ∀ {w : Val ∅ σ} → ComputableV σ w → ComputableE σ' ε ((retApplied h v) [ w ])
      hRet' {w} wComp = subst (ComputableE σ' ε) (sym (retApplied-sub1 h v w)) (hRet vComp wComp)

-- ---------------------------------------------------------------------
-- Lemma A.11 (page 33-37): the Fundamental Lemma -- every well-typed
-- (open) expression is computable once its free variables are
-- instantiated at computable closed values. Proceeds by ordinary
-- structural induction on the expression's own syntax (mutually with
-- values/handlers) rather than the paper's own size-based induction:
-- for this development's own concrete, fixed set of Frame/SFrame
-- constructors, the paper's "F[x] is computable via the induction
-- hypothesis, applied at the size-smaller F[x]" step reduces, case by
-- case, to either a direct value-value redex (independent of any
-- subterm), or a dependency on F's own OTHER component, which is
-- always a genuine syntactic subterm of e itself (e.g. e2 in F-pairL,
-- b in F-handleP) -- so Lemma A.9/lemma-reset's own internal induction
-- (over e's computability, not its size) already does everything the
-- paper's separate size-argument was for.
--
-- First, the substitution-algebra plumbing every binder case (vabs,
-- clause, ret) needs: composing an extended substitution (extS^n σs,
-- leaving the n freshly-bound variables open) with a substitution that
-- instantiates exactly those n variables, into a single n-ary
-- extension of σs itself. (cons-weaken1V-cancel itself now lives
-- earlier in the file, just before Lemma A.10, which needs it too.)
-- ---------------------------------------------------------------------

subE-ext-cons : ∀ {Γ σ τ ε} (σs : Sub Γ ∅) (v : Val ∅ σ) (e : (Γ , σ) ⊢ τ ! ε)
              → subE (cons v idSub) (subE (extS σs) e) ≡ subE (cons v σs) e
subE-ext-cons σs v e = trans (subE-subE-fuse (cons v idSub) (extS σs) e) (subE-cong pointwise e)
  where
  pointwise : ∀ {τ'} (x : (_ , _) ∋ τ') → subV (cons v idSub) (extS σs x) ≡ cons v σs x
  pointwise Z     = refl
  pointwise (S x) = weaken1V-sub1-cancel v (σs x)

subE-ext2-cons2 : ∀ {Γ σ1 σ2 τ ε} (σs : Sub Γ ∅) (v1 : Val ∅ σ1) (v2 : Val ∅ σ2) (e : ((Γ , σ1) , σ2) ⊢ τ ! ε)
                 → subE (cons v2 (cons v1 idSub)) (subE (extS (extS σs)) e) ≡ subE (cons v2 (cons v1 σs)) e
subE-ext2-cons2 {σ1 = σ1} {σ2 = σ2} σs v1 v2 e = trans (subE-subE-fuse (cons v2 (cons v1 idSub)) (extS (extS σs)) e) (subE-cong pointwise e)
  where
  pointwise : ∀ {τ'} (x : ((_ , σ1) , σ2) ∋ τ') → subV (cons v2 (cons v1 idSub)) (extS (extS σs) x) ≡ cons v2 (cons v1 σs) x
  pointwise Z         = refl
  pointwise (S Z)     = refl
  pointwise (S (S x)) = trans (cons-weaken1V-cancel v2 (cons v1 idSub) (weaken1V (σs x))) (weaken1V-sub1-cancel v1 (σs x))

subE-ext4-cons4 : ∀ {Γ σ1 σ2 σ3 σ4 τ ε} (σs : Sub Γ ∅) (v1 : Val ∅ σ1) (v2 : Val ∅ σ2) (v3 : Val ∅ σ3) (v4 : Val ∅ σ4)
                 (e : ((((Γ , σ1) , σ2) , σ3) , σ4) ⊢ τ ! ε)
                 → subE (cons v4 (cons v3 (cons v2 (cons v1 idSub)))) (subE (extS (extS (extS (extS σs)))) e)
                 ≡ subE (cons v4 (cons v3 (cons v2 (cons v1 σs)))) e
subE-ext4-cons4 {σ1 = σ1} {σ2 = σ2} {σ3 = σ3} {σ4 = σ4} σs v1 v2 v3 v4 e =
  trans (subE-subE-fuse (cons v4 (cons v3 (cons v2 (cons v1 idSub)))) (extS (extS (extS (extS σs)))) e) (subE-cong pointwise e)
  where
  pointwise : ∀ {τ'} (x : (((( _ , σ1) , σ2) , σ3) , σ4) ∋ τ')
            → subV (cons v4 (cons v3 (cons v2 (cons v1 idSub)))) (extS (extS (extS (extS σs))) x) ≡ cons v4 (cons v3 (cons v2 (cons v1 σs))) x
  pointwise Z             = refl
  pointwise (S Z)         = refl
  pointwise (S (S Z))     = refl
  pointwise (S (S (S Z))) = refl
  pointwise (S (S (S (S x)))) =
    trans (cons-weaken1V-cancel v4 (cons v3 (cons v2 (cons v1 idSub))) (weaken1V (weaken1V (weaken1V (σs x)))))
    (trans (cons-weaken1V-cancel v3 (cons v2 (cons v1 idSub)) (weaken1V (weaken1V (σs x))))
    (trans (cons-weaken1V-cancel v2 (cons v1 idSub) (weaken1V (σs x)))
           (weaken1V-sub1-cancel v1 (σs x))))

-- Every free variable of Γ instantiated at a computable closed value.
ComputableSub : ∀ {Γ} → Sub Γ ∅ → Set
ComputableSub {Γ} σs = ∀ {τ} (x : Γ ∋ τ) → ComputableV τ (σs x)

ComputableSub-cons : ∀ {Γ σ} {σs : Sub Γ ∅} {v : Val ∅ σ} → ComputableV σ v → ComputableSub σs → ComputableSub (cons v σs)
ComputableSub-cons Pv Cσs Z     = Pv
ComputableSub-cons Pv Cσs (S x) = Cσs x

mutual
  lemma-A11-V : ∀ {Γ σ} (v : Val Γ σ) {σs : Sub Γ ∅} → ComputableSub σs → ComputableV σ (subV σs v)
  lemma-A11-V (vvar x)    Cσs = Cσs x
  lemma-A11-V (vgnd x)    Cσs = tt
  lemma-A11-V (vpair v w) Cσs = ComputableV-pair-intro _ _ (lemma-A11-V v Cσs) (lemma-A11-V w Cσs)
  lemma-A11-V {Γ} (vabs {σ = σ} {τ = τ} {ε = ε} e) {σs} Cσs {v'} v'Comp =
    subst (ComputableE-at τ ε _) (sym (subE-ext-cons σs v' e))
      (ComputableE-acc-conv (lemma-A11-E e (ComputableSub-cons (ComputableV-acc-conv v'Comp) Cσs)))

  lemma-A11-H : ∀ {Γ ℓ par σ σ' ε} (h : Handler Γ ℓ par σ σ' ε) {σs : Sub Γ ∅} → ComputableSub σs → ComputableH (subH σs h)
  lemma-A11-H {Γ} {ℓ} {par} {σ} {σ'} {ε} h {σs} Cσs = clauseComp , retComp
    where
    clauseComp : ∀ (op : Op ℓ) {v1 : Val ∅ (gnd par)} {v2 : Val ∅ (gnd (out op))}
                   {fl : Val ∅ ((gnd par `× gnd (in′ op)) ⇒ Loss ! ε)} {fk : Val ∅ ((gnd par `× gnd (in′ op)) ⇒ σ' ! ε)}
               → ComputableV (gnd par) v1 → ComputableV (gnd (out op)) v2
               → ComputableV ((gnd par `× gnd (in′ op)) ⇒ Loss ! ε) fl → ComputableV ((gnd par `× gnd (in′ op)) ⇒ σ' ! ε) fk
               → ComputableE σ' ε (subE (cons fk (cons fl (cons v2 (cons v1 idSub)))) (clause (subH σs h) op))
    clauseComp op {v1} {v2} {fl} {fk} v1Comp v2Comp flComp fkComp =
      subst (ComputableE σ' ε) (sym (subE-ext4-cons4 σs v1 v2 fl fk (clause h op)))
            (lemma-A11-E (clause h op)
              (ComputableSub-cons fkComp (ComputableSub-cons flComp (ComputableSub-cons v2Comp (ComputableSub-cons v1Comp Cσs)))))
    retComp : ∀ {v1 : Val ∅ (gnd par)} {v2 : Val ∅ σ} → ComputableV (gnd par) v1 → ComputableV σ v2
            → ComputableE σ' ε (subE (cons v2 (cons v1 idSub)) (ret (subH σs h)))
    retComp {v1} {v2} v1Comp v2Comp =
      subst (ComputableE σ' ε) (sym (subE-ext2-cons2 σs v1 v2 (ret h)))
            (lemma-A11-E (ret h) (ComputableSub-cons v2Comp (ComputableSub-cons v1Comp Cσs)))

  lemma-A11-E : ∀ {Γ σ ε} (e : Γ ⊢ σ ! ε) {σs : Sub Γ ∅} → ComputableSub σs → ComputableE σ ε (subE σs e)
  lemma-A11-E (val v) Cσs = gc-val (lemma-A11-V v Cσs)
  lemma-A11-E {Γ} (fun {γ} {δ} {ε} f e0) {σs} Cσs = lemma-A9 (F-fun f) Fcomp (lemma-A11-E e0 Cσs)
    where
    Fcomp : ∀ {v : Val ∅ (gnd γ)} → ComputableV (gnd γ) v → ComputableE (gnd δ) ε (plugF (F-fun f) (val v))
    Fcomp {v} _ with val-closed-gnd v
    ... | (x , refl) = value-redex-computable (R1 f x) (gc-val tt)
  lemma-A11-E {Γ} (pair {σ} {τ} {ε} e1 e2) {σs} Cσs = lemma-A9 (F-pairL (subE σs e2)) Fcomp1 (lemma-A11-E e1 Cσs)
    where
    Fcomp1 : ∀ {v : Val ∅ σ} → ComputableV σ v → ComputableE (σ `× τ) ε (plugF (F-pairL (subE σs e2)) (val v))
    Fcomp1 {v} Pv = lemma-A9 (F-pairR v) Fcomp2 (lemma-A11-E e2 Cσs)
      where
      Fcomp2 : ∀ {w : Val ∅ τ} → ComputableV τ w → ComputableE (σ `× τ) ε (plugF (F-pairR v) (val w))
      Fcomp2 {w} Pw = value-redex-computable (R2-pair v w) (gc-val (ComputableV-pair-intro v w Pv Pw))
  lemma-A11-E {Γ} (fst {σ} {τ} {ε} e0) {σs} Cσs = lemma-A9 F-fst Fcomp (lemma-A11-E e0 Cσs)
    where
    Fcomp : ∀ {v : Val ∅ (σ `× τ)} → ComputableV (σ `× τ) v → ComputableE σ ε (plugF F-fst (val v))
    Fcomp {v} Pv with val-closed-pair v
    ... | (v1 , v2 , refl) = value-redex-computable (R2-fst v1 v2) (gc-val (proj₁ (ComputableV-pair-proj {accP = <M-wellFounded (mVal (σ `× τ))} v1 v2 Pv)))
  lemma-A11-E {Γ} (snd {σ} {τ} {ε} e0) {σs} Cσs = lemma-A9 F-snd Fcomp (lemma-A11-E e0 Cσs)
    where
    Fcomp : ∀ {v : Val ∅ (σ `× τ)} → ComputableV (σ `× τ) v → ComputableE τ ε (plugF F-snd (val v))
    Fcomp {v} Pv with val-closed-pair v
    ... | (v1 , v2 , refl) = value-redex-computable (R2-snd v1 v2) (gc-val (proj₂ (ComputableV-pair-proj {accP = <M-wellFounded (mVal (σ `× τ))} v1 v2 Pv)))
  lemma-A11-E {Γ} (app {σ} {τ} {ε} e1 e2) {σs} Cσs = lemma-A9 (F-appL (subE σs e2)) Fcomp1 (lemma-A11-E e1 Cσs)
    where
    Fcomp1 : ∀ {v : Val ∅ (σ ⇒ τ ! ε)} → ComputableV (σ ⇒ τ ! ε) v → ComputableE τ ε (plugF (F-appL (subE σs e2)) (val v))
    Fcomp1 {v} Pv = lemma-A9 (F-appR v) Fcomp2 (lemma-A11-E e2 Cσs)
      where
      Fcomp2 : ∀ {w : Val ∅ σ} → ComputableV σ w → ComputableE τ ε (plugF (F-appR v) (val w))
      Fcomp2 {w} Pw with val-closed-abs v
      ... | (e' , refl) = value-redex-computable (R3 e' w) (ComputableE-acc-conv-rev (Pv {w} (ComputableV-acc-conv-rev Pw)))
  lemma-A11-E {Γ} (opE {ℓ} {ε} m op e0) {σs} Cσs = lemma-A9 (F-op m op) Fcomp (lemma-A11-E e0 Cσs)
    where
    Fcomp : ∀ {v : Val ∅ (gnd (out op))} → ComputableV (gnd (out op)) v → ComputableE (gnd (in′ op)) ε (plugF (F-op m op) (val v))
    Fcomp {v} _ = gc-stuck {K = ▫} (λ ()) (λ {v1} → gc-val tt) (λ {v1} → gc-val tt)
  lemma-A11-E {Γ} (lossE {ε} e0) {σs} Cσs = lemma-A9 F-loss Fcomp (lemma-A11-E e0 Cσs)
    where
    Fcomp : ∀ {v : Val ∅ Loss} → ComputableV Loss v → ComputableE UnitTy ε (plugF F-loss (val v))
    Fcomp {v} _ with val-closed-gnd v
    ... | (r , refl) = value-redex-computable (R4 r) (gc-val tt)
  lemma-A11-E {Γ} (thenE {σ} {ε} sub e0 g) {σs} Cσs =
    lemma-A8-2 sub gComp
      (GComputable-antimono {σ = σ} {ε = ε}
        {G = λ _ g' → LossComputable (ComputableV σ) g'} {G' = Gsingle (subV σs g)}
        (λ { (refl , refl) → gComp }) (lemma-A11-E e0 Cσs))
    where
    gComp : LossComputable (ComputableV σ) (subV σs g)
    gComp = ComputableV-to-LossComputable (lemma-A11-V g Cσs)
  lemma-A11-E {Γ} (plusE {ε} e1 e2) {σs} Cσs = lemma-A9 (F-plusL (subE σs e2)) Fcomp1 (lemma-A11-E e1 Cσs)
    where
    Fcomp1 : ∀ {v : Val ∅ Loss} → ComputableV Loss v → ComputableE Loss ε (plugF (F-plusL (subE σs e2)) (val v))
    Fcomp1 {v} _ = lemma-A9 (F-plusR v) Fcomp2 (lemma-A11-E e2 Cσs)
      where
      Fcomp2 : ∀ {w : Val ∅ Loss} → ComputableV Loss w → ComputableE Loss ε (plugF (F-plusR v) (val w))
      Fcomp2 {w} _ with val-closed-gnd v | val-closed-gnd w
      ... | (r , refl) | (r2 , refl) = value-redex-computable (Rplus r r2) (gc-val tt)
  lemma-A11-E {Γ} (glocalE {σ} {ε₂} {ε₁} {ε} s1 s2 e0 g) {σs} Cσs =
    lemma-A6 s1 s2 gComp
      (GComputable-antimono {σ = σ} {ε = ε₁}
        {G = λ _ g' → LossComputable (ComputableV σ) g'} {G' = Gsingle (subV σs g)}
        (λ { (refl , refl) → gComp }) (lemma-A11-E e0 Cσs))
    where
    gComp : LossComputable (ComputableV σ) (subV σs g)
    gComp = ComputableV-to-LossComputable (lemma-A11-V g Cσs)
  lemma-A11-E (resetE e0) Cσs = lemma-reset (lemma-A11-E e0 Cσs)
  lemma-A11-E {Γ} (handleE {ℓ} {par} {σ} {σ'} {ε} h p b) {σs} Cσs =
    lemma-A9 (F-handleP (subH σs h) (subE σs b)) Fcomp (lemma-A11-E p Cσs)
    where
    Fcomp : ∀ {v : Val ∅ (gnd par)} → ComputableV (gnd par) v → ComputableE σ' ε (plugF (F-handleP (subH σs h) (subE σs b)) (val v))
    Fcomp {v} Pv = lemma-A10 (subH σs h) (lemma-A11-H h Cσs) (lemma-A11-E b Cσs) Pv

-- Every closed, well-typed expression is (unconditionally) computable
-- -- Γ = ∅ has no free variables, so ComputableSub idSub is vacuous.
lemma-A11-E-closed : ∀ {σ ε} (e : ∅ ⊢ σ ! ε) → ComputableE σ ε e
lemma-A11-E-closed e = subst (ComputableE _ _) (subE-idSub e) (lemma-A11-E e (λ ()))

lemma-A11-V-closed : ∀ {σ} (v : Val ∅ σ) → ComputableV σ v
lemma-A11-V-closed v = subst (ComputableV _) (subV-idSub v) (lemma-A11-V v (λ ()))

-- ---------------------------------------------------------------------
-- Theorem A.12 (page 37): termination -- for every e : σ ! ε and every
-- loss-computable g : σ → loss ! ε' (ε' ⊆ ε), there is no infinite
-- sequence of steps g ⊢ e0 -[r0]-> e1 -[r1]-> e2 -> ... starting from
-- e0 = e. Proceeds exactly as the paper's own one-line proof says: by
-- the Fundamental Lemma e is computable (lemma-A11-E-closed), hence
-- L_σ,ε-computable, and an "evident L-induction" (structural recursion
-- on the ComputableE witness -- gc-val/gc-stuck both preclude any step
-- at all via theorem-A4-1, and gc-step's own function field, applied
-- to the sequence's very next step, hands back a strictly smaller
-- ComputableE witness for the shifted sequence) shows no such sequence
-- exists.
-- ---------------------------------------------------------------------

theorem-A12 : ∀ {σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC ∅ σ εg} → LossComputable (ComputableV σ) g
             → (f : ℕ → ∅ ⊢ σ ! ε) → (∀ n → Σ R (λ r → _⊢_-[_]→_ {sub = sub} g (f n) r (f (suc n)))) → ⊥
theorem-A12 {σ} {ε} {sub = sub} {g = g} gComp = go
  where
  go : (f : ℕ → ∅ ⊢ σ ! ε) → (∀ n → Σ R (λ r → _⊢_-[_]→_ {sub = sub} g (f n) r (f (suc n)))) → ⊥
  go f steps = go' f steps (f 0) refl (lemma-A11-E-closed (f 0))
    where
    go' : (f : ℕ → ∅ ⊢ σ ! ε) → (∀ n → Σ R (λ r → _⊢_-[_]→_ {sub = sub} g (f n) r (f (suc n))))
        → (e : ∅ ⊢ σ ! ε) → f 0 ≡ e → ComputableE σ ε e → ⊥
    go' f steps e eq (gc-val {v} _) =
      ¬Terminal-of-step (subst (λ x → _⊢_-[_]→_ {sub = sub} g x (proj₁ (steps 0)) (f 1)) eq (proj₂ (steps 0))) (terminalVal v)
    go' f steps e eq (gc-stuck {m = m} {op = op} {v = v} {K = K} nh _ _) =
      ¬Terminal-of-step (subst (λ x → _⊢_-[_]→_ {sub = sub} g x (proj₁ (steps 0)) (f 1)) eq (proj₂ (steps 0))) (terminalOp m op v K nh)
    go' f steps e eq (gc-step nterm ih) =
      go' (λ n → f (suc n)) (λ n → steps (suc n)) (f 1) refl
          (ih {sub = sub} {g = g} gComp (subst (λ x → _⊢_-[_]→_ {sub = sub} g x (proj₁ (steps 0)) (f 1)) eq (proj₂ (steps 0))))

-- ---------------------------------------------------------------------
-- Theorem A.13 (existence half; page 37, combined with Corollary A.5
-- above for uniqueness): every e : σ ! ε and loss-computable
-- g : σ → loss ! ε' evaluate, in finitely many steps, to SOME terminal
-- w with SOME total loss r -- i.e. g ⊢ e ⇒[r] w. Exactly
-- theorem-A4-4's own statement (originally postulated in
-- OpSemProofs.agda, since termination is genuinely the crux of
-- Appendix A.4) -- proved here as a direct corollary of the Fundamental
-- Lemma (lemma-A11-E-closed) by the same structural recursion
-- theorem-A12 uses, this time building the big-step derivation itself
-- (via `done`/`step`) rather than deriving a contradiction: gc-val/
-- gc-stuck are already terminal (0 steps, `done`); gc-step exhibits
-- e's own next step via progress-dichotomy (ruled out from being
-- Terminal by nterm), recurses on the strictly smaller ComputableE
-- witness ih hands back, and prepends the exhibited step via `step`.
-- ---------------------------------------------------------------------

theorem-A13-exists : ∀ {σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC ∅ σ εg} → LossComputable (ComputableV σ) g
                    → (e : ∅ ⊢ σ ! ε) → Σ R (λ r → Σ (∅ ⊢ σ ! ε) (λ w → _⊢_⇒[_]_ {sub = sub} g e r w × Terminal w))
theorem-A13-exists {σ} {ε} {sub = sub} {g = g} gComp e = go (lemma-A11-E-closed e)
  where
  go : ∀ {e} → ComputableE σ ε e → Σ R (λ r → Σ (∅ ⊢ σ ! ε) (λ w → _⊢_⇒[_]_ {sub = sub} g e r w × Terminal w))
  go (gc-val {v} _)                = 0# , val v , done (val v) , terminalVal v
  go (gc-stuck {m = m} {op = op} {v = v} {K = K} nh _ _) =
    0# , plugK K (opE m op (val v)) , done (plugK K (opE m op (val v))) , terminalOp m op v K nh
  go (gc-step {e0} nterm ih) with progress-dichotomy {sub = sub} {g = g} e0
  ... | inj₁ term = ⊥-elim (nterm term)
  ... | inj₂ (r0 , e0' , stp0) with go (ih {sub = sub} {g = g} gComp stp0)
  ...   | (s , w , d , tw) = r0 + s , w , step stp0 d , tw

-- Matches theorem-A4-4's own type exactly -- Proofs.agda now imports
-- this directly (renamed back to theorem-A4-4) in place of the
-- postulate, which has been removed from OpSemProofs.agda entirely.
theorem-A13-exists-A4-4 : ∀ {σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC ∅ σ εg} (e : ∅ ⊢ σ ! ε)
                         → Σ R (λ r → Σ (∅ ⊢ σ ! ε) (λ w → _⊢_⇒[_]_ {sub = sub} g e r w × Terminal w))
theorem-A13-exists-A4-4 {g = g} e = theorem-A13-exists (ComputableV-to-LossComputable (lemma-A11-V-closed g)) e

-- Existence + uniqueness combined, matching the paper's own Theorem
-- A.13 statement directly: g ⊢ e ⇒[r] w for a UNIQUE r and terminal w.
theorem-A13 : ∀ {σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC ∅ σ εg}
            → (e : ∅ ⊢ σ ! ε) → Σ R (λ r → Σ (∅ ⊢ σ ! ε) (λ w → _⊢_⇒[_]_ {sub = sub} g e r w × Terminal w))
            × (∀ {r1 r2 w1 w2} → _⊢_⇒[_]_ {sub = sub} g e r1 w1 → Terminal w1 → _⊢_⇒[_]_ {sub = sub} g e r2 w2 → Terminal w2 → r1 ≡ r2 × w1 ≡ w2)
theorem-A13 {g = g} e = theorem-A13-exists-A4-4 e , corollary-A5

