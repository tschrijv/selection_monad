-- Scratch development attempting to prove Lemma 7.5(3)/B.5(3)
-- unconditionally (no restriction on g), since an initial check suggested
-- it might -- unlike B.5(1) -- hold in general. Conclusion, reached by
-- direct machine-checked experiment (see the b53-check* family below):
--
--   Lemma B.5(3) holds whenever EITHER (a) e's own accumulated loss r1
--   is 0 (e.g. e is a bare value, or more generally never discards a
--   lossE-reported amount), OR (b) g's body fully reduces to a value
--   (never gets stuck on an unhandled operation) -- checked separately
--   in b53-check (e clean, g stuck: HOLDS) and b53-check3 (e dirty, g
--   clean: HOLDS). It FAILS when BOTH fail at once: e discards a
--   nonzero loss (r1 ≠ 0) AND g gets stuck on an operation -- b53-check2
--   refutes it concretely (r1 := 7, discrepancy is exactly "0 vs 7").
--
-- So the gap in B.5 isn't really about restricting g's *syntactic shape*
-- (canonical thenE-chains vs arbitrary bodies) at all -- it's about a
-- genuinely global invariant that would need to hold of *every*
-- subexpression appearing anywhere in the program (both the "e"/frame
-- role and the "g"/continuation role): "no subterm discards a nonzero
-- loss it caused while its own evaluation also reaches a stuck,
-- unhandled operation". That is a materially bigger claim than "g is a
-- thenE-chain", and isn't closed here.
--
-- Follow-up (b53F-*/b9F-* below): does this failure actually break
-- theorem-B9-F's *own* conclusion, or only the auxiliary Lemma B.7
-- construction built on top of B.5(3)? Testing B.5(3) at exactly the
-- substitution F-rule's proof would need (b53F-*) confirms that instance
-- is false too. But testing theorem-B9-F's own conclusion directly, on a
-- genuine F-rule step through the very same dirty companion and stuck
-- ambient (b9F-*), it HOLDS -- the discrepancy lives inside the
-- intermediate Lsem(λx.F[x]▶g) construction the standard proof route
-- builds, not in the theorem's own directly observable equation. Read as
-- evidence (not proof) that F-rule/S1/R5/R7 are true statements blocked
-- by a genuine proof-technique gap, not false theorems -- see Proofs.agda's
-- comment above the theorem-B9-F/S1/R7/R5 postulate block for the fuller
-- account and the working assumption going forward.
module B5Core where

open import Domains
open import Example using (mySig)
open import Data.Nat using (ℕ; _*_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Axiom.Extensionality.Propositional using (Extensionality)

postulate
  funext : ∀ {a b} → Extensionality a b

open Sig mySig
open import Syntax mySig
open import Subst mySig
open import OpSem mySig
open import Denotational mySig

tell-0 : ∀ {ε X} (w : Ŵ ε X) → tell 0# w ≡ w
tell-0 (leaf r x)        = cong (λ z → leaf z x) (+-identityˡ r)
tell-0 (node m op r o κ) = cong (λ z → node m op z o κ) (+-identityˡ r)

-- bump_r ∘ bump_s = bump_{r+s} (paper's own stated fact, line 288).
bump-fusion : ∀ {ε X} (r s : R) (T : Ŵ ε (X × R)) → bump r (bump s T) ≡ bump (r + s) T
bump-fusion r s (leaf r₀ (x , y))  = cong (λ z → leaf r₀ (x , z)) (sym (+-assoc r s y))
bump-fusion r s (node m op r₀ o κ) = cong (node m op r₀ o) (funext (λ a → bump-fusion r s (κ a)))

-- tell fuses with itself the same way `+` does.
tell-tell : ∀ {ε X} (r s : R) (w : Ŵ ε X) → tell r (tell s w) ≡ tell (r + s) w
tell-tell r s (leaf r₀ x)        = cong (λ z → leaf z x) (sym (+-assoc r s r₀))
tell-tell r s (node m op r₀ o κ) = cong (λ z → node m op z o κ) (sym (+-assoc r s r₀))

-- bump r (collectX S) ≡ collectX (tell r S).
bump-collectX-comm : ∀ {ε X} (r : R) (S : Ŵ ε X) → bump r (collectX S) ≡ collectX (tell r S)
bump-collectX-comm r (leaf r₀ x)        = refl
bump-collectX-comm r (node m op r₀ o κ) = cong (node m op 0# o) (funext (λ a → bump-fusion r r₀ (collectX (κ a))))

-- "bump-outside": true at the leaf, but FALSE at a node (r0 gets dropped
-- entirely on one side, appearing as 0 instead of r0+0#, exactly as
-- bump-outside-concrete-lhs/rhs below witness concretely) -- an early,
-- mistaken attempt at decomposing B.5(3); the node case is deliberately
-- left unproven (it isn't true), kept only as a record of the wrong turn.

-- ---------------------------------------------------------------------
-- Direct concrete check: does Lemma 7.5(3)/B.5(3) hold when g's body
-- reaches a genuine (unhandled) operation node, rather than a leaf?
-- g := λ_. snd(pair(decide(), 5))  -- discards the choice, keeps 5:Loss.
-- ---------------------------------------------------------------------
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
import Example

εop : EffCxt
εop = Example.ndet ∷ []

mop : Example.ndet ∈ εop
mop = here refl

-- lemma-B5-3's own e,g live at context (Γ,σ) := (∅,UnitTy).
gOpBody : ((∅ , UnitTy) , UnitTy) ⊢ Loss ! εop
gOpBody = snd (pair (opE mop Example.decide (val (vgnd tt))) (val (vgnd 5)))

gOp : LC (∅ , UnitTy) UnitTy εop
gOp = vabs gOpBody

e1' : (∅ , UnitTy) ⊢ UnitTy ! εop
e1' = val (vgnd tt)

ρ0' : Env ∅
ρ0' ()

-- Lsem gOp (ρ0',,a) a', computed: should be node mop decide 0 tt (λ_ → leaf 5 tt).
Lsem-gOp-check : Lsem gOp (ρ0' ,, tt) tt ≡ node mop Example.decide 0 tt (λ _ → leaf 5 tt)
Lsem-gOp-check = refl

-- B.5(3): Lsem(vabs(thenE sub e1' gOp))ρ0' a ≡ R̂-of(Esem e1'(ρ0',,a))⌊gOp⌋.
b53-lhs : Ŵ εop ⟦ UnitTy ⟧
b53-lhs = Lsem (vabs (thenE ⊆ᵉ-refl e1' gOp)) ρ0' tt

b53-rhs : Ŵ εop ⟦ UnitTy ⟧
b53-rhs = R̂-of (Esem e1' (ρ0' ,, tt)) (λ b → widenŴ ⊆ᵉ-refl (Lsem gOp (ρ0' ,, tt) b))

b53-check : b53-lhs ≡ b53-rhs
b53-check = refl

-- Concrete sanity check of bump-outside at a node, before trying the
-- general proof: S := node mop decide 5 tt (λ_ → leaf 3 7), r0 := 1,
-- bumpAmt := 2.
bump-outside-concrete-lhs bump-outside-concrete-rhs : Ŵ εop R
bump-outside-concrete-lhs =
  bind̂ (bump 2 (collectX (node mop Example.decide 5 tt (λ _ → leaf 3 7))))
       (λ { (r3 , r2) → tell r2 (η̂ (1 + r3)) })
bump-outside-concrete-rhs =
  tell 2 (bind̂ (collectX (node mop Example.decide 5 tt (λ _ → leaf 3 7)))
               (λ { (r3 , r2) → tell r2 (η̂ (1 + r3)) }))

-- bump-outside-concrete-lhs has root 0 (r0=1 is dropped); rhs has root
-- r0+0#=1. Refuted via the same leaf-root discriminator style as
-- B5Counterexample.agda.
root : Ŵ εop R → R
root (leaf r x)     = r
root (node m op r o κ) = r

root-lhs-check : root bump-outside-concrete-lhs ≡ 0
root-lhs-check = refl

root-rhs-check : root bump-outside-concrete-rhs ≡ 2
root-rhs-check = refl

bump-outside-refuted : bump-outside-concrete-lhs ≡ bump-outside-concrete-rhs → (0 ≡ 2)
bump-outside-refuted eq = cong root eq

-- Does lemma-B5-3 hold when *e* itself contributes nonzero accumulated
-- loss r1 (not just when g gets stuck on an operation)? e2' discards a
-- loss(7) via snd, contributing r1 = 7 when reduced.
e2' : (∅ , UnitTy) ⊢ UnitTy ! εop
e2' = snd (pair (lossE (val (vgnd 7))) (val (vgnd tt)))

b53-lhs2 : Ŵ εop ⟦ UnitTy ⟧
b53-lhs2 = Lsem (vabs (thenE ⊆ᵉ-refl e2' gOp)) ρ0' tt

b53-rhs2 : Ŵ εop ⟦ UnitTy ⟧
b53-rhs2 = R̂-of (Esem e2' (ρ0' ,, tt)) (λ b → widenŴ ⊆ᵉ-refl (Lsem gOp (ρ0' ,, tt) b))

-- Refuted: b53-lhs2 has root 0 (e2's discarded loss(7) is dropped);
-- b53-rhs2 has root 7.
b53-root : Ŵ εop ⟦ UnitTy ⟧ → R
b53-root (leaf r x)     = r
b53-root (node m op r o κ) = r

b53-refuted2 : b53-lhs2 ≡ b53-rhs2 → (0 ≡ 7)
b53-refuted2 eq = cong b53-root eq

-- Now: e nonzero (r1=7 via a discarded loss), but g reaches a LEAF (not
-- stuck on an operation) -- does lemma-B5-3 hold in *this* combination?
gLeaf : LC (∅ , UnitTy) UnitTy εop
gLeaf = vabs (val (vgnd 3))

b53-lhs3 : Ŵ εop ⟦ UnitTy ⟧
b53-lhs3 = Lsem (vabs (thenE ⊆ᵉ-refl e2' gLeaf)) ρ0' tt

b53-rhs3 : Ŵ εop ⟦ UnitTy ⟧
b53-rhs3 = R̂-of (Esem e2' (ρ0' ,, tt)) (λ b → widenŴ ⊆ᵉ-refl (Lsem gLeaf (ρ0' ,, tt) b))

b53-check3 : b53-lhs3 ≡ b53-rhs3
b53-check3 = refl

-- The "core" fact behind B.5(3), generalised over an arbitrary Hg: TRUE
-- when Hg x is a leaf (any r,s -- this is the "e clean OR g clean" half
-- of the boundary above, doesn't even need r=0), genuinely FALSE when
-- Hg x is a node and r ≠ 0# (matches b53-refuted2 exactly: r there is
-- e2's own discarded loss, playing this same "r" role) -- the node case is
-- deliberately not proven below (it isn't true in general).
core-B5-3-base-leaf-case : ∀ {ε X} (r : R) (x : X) (Hg : X → Ŵ ε R) (s : R) (v : R)
  → Hg x ≡ leaf s v
  → collapse (bind̂ (collectX (leaf r x)) (λ { (b , r1) → bind̂ (collectX (Hg b)) (λ { (r3 , r2) → tell r2 (η̂ (r1 + r3)) }) }))
  ≡ bind̂ (leaf r x) (λ b → collapse (Hg b))
core-B5-3-base-leaf-case r x Hg s v eq rewrite eq = refl

-- ---------------------------------------------------------------------
-- Direct concrete test of theorem-B9-S2's actual goal (not an auxiliary
-- lemma): g1 stuck on decide(), e/e' a genuine (r=0) step via R2-fst.
-- ---------------------------------------------------------------------

g1S2 : LC ∅ Loss εop
g1S2 = vabs (snd (pair (opE mop Example.decide (val (vgnd tt))) (val (vgnd 5))))

eS2 : ∅ ⊢ Loss ! εop
eS2 = fst (pair (val (vgnd 3)) (val (vgnd {γ = loss} 4)))

eS2' : ∅ ⊢ Loss ! εop
eS2' = val (vgnd 3)

stpS2 : g1S2 ⊢ eS2 -[ 0 ]→ eS2'
stpS2 = R2-fst (vgnd 3) (vgnd {γ = loss} 4)

ρ0S2 : Env ∅
ρ0S2 ()

s2-lhs : Ŵ εop ⟦ Loss ⟧
s2-lhs = Esem (thenE ⊆ᵉ-refl eS2 g1S2) ρ0S2 (λ _ → η̂ tt)

s2-rhs : Ŵ εop ⟦ Loss ⟧
s2-rhs = tell 0 (Esem (thenE ⊆ᵉ-refl (lossE (val (vgnd 0))) (vabs (weaken1 (thenE ⊆ᵉ-refl eS2' g1S2)))) ρ0S2 (λ _ → η̂ tt))

s2-check : s2-lhs ≡ s2-rhs
s2-check = refl

-- Is `shift r T := bind̂(collectX T)(λ{(r3,r2)→tell r2(η̂(r+r3))})` simply
-- `mapŴ (r +_) T`? Test at a node.
shiftTest-lhs shiftTest-rhs : Ŵ εop R
shiftTest-lhs = bind̂ (collectX (node mop Example.decide 5 tt (λ _ → leaf 3 7)))
                      (λ { (r3 , r2) → tell r2 (η̂ (10 + r3)) })
shiftTest-rhs = mapŴ (10 +_) (node mop Example.decide 5 tt (λ _ → leaf 3 7))

-- Refuted (not a hole/refl -- a hard `refl` mismatch here would halt Agda's
-- checking of the REST of this file, silently preventing verification of
-- everything below; discovered the hard way when the b53F-* block below
-- turned out never to have actually been checked). shift's root is 0 (the
-- 10 gets redistributed into the leaf via collectX); mapŴ's root stays 5.
shiftTest-root : Ŵ εop R → R
shiftTest-root (leaf r x)        = r
shiftTest-root (node m op r o κ) = r

shiftTest-lhs-root : shiftTest-root shiftTest-lhs ≡ 0
shiftTest-lhs-root = refl

shiftTest-rhs-root : shiftTest-root shiftTest-rhs ≡ 5
shiftTest-rhs-root = refl

shiftTest-refuted : shiftTest-lhs ≡ shiftTest-rhs → (0 ≡ 5)
shiftTest-refuted eq = cong shiftTest-root eq

-- Hypothesis: collectX(bind̂ w k) ≡ bind̂(collectX w)(λ{(a,r1)→bump r1(collectX(k a))})
-- Test at a node w, arbitrary k.
kTest : R → Ŵ εop R
kTest x = node mop Example.decide 2 tt (λ _ → leaf 1 (x + 100))

cxbindTest-lhs cxbindTest-rhs : Ŵ εop (R × R)
cxbindTest-lhs = collectX (bind̂ (node mop Example.decide 5 tt (λ _ → leaf 3 7)) kTest)
cxbindTest-rhs = bind̂ (collectX (node mop Example.decide 5 tt (λ _ → leaf 3 7)))
                       (λ { (a , r1) → bump r1 (collectX (kTest a)) })

cxbindTest-check : cxbindTest-lhs ≡ cxbindTest-rhs
cxbindTest-check = refl

-- (An earlier "mainTest"/"shiftFusion"/"sfg" concrete pre-confirmation
-- block was deleted here: it was written *after* shiftTest-check's
-- deliberately-false `refl` above, so it was silently never actually
-- type-checked by Agda in any prior run of this file -- Agda halts a file
-- at its first hard type error, and shiftTest-check was one. Once that was
-- fixed (turned into a proper refutation instead of a bare `refl`), this
-- block turned out to itself contain a genuine type bug (a stray R value
-- where an operation's ⊤-typed output was expected) and, once THAT was
-- fixed, no longer held for the chosen numbers. Since the corresponding
-- general lemmas (collectX-bind̂-fusion, collectX-idem, shift-fusion) are
-- already fully proven independently in Proofs.agda, this scratch block
-- was simply removed rather than repaired.

-- Hypothesis: collectX(collectX W) ≡ mapŴ (λ{(x,r)→((x,r),0#)}) (collectX W)
-- (once collectX has already pushed loss to leaves, a second pass has
-- nothing left to redistribute). Test at a node.
ccTest-lhs ccTest-rhs : Ŵ εop ((R × R) × R)
ccTest-lhs = collectX (collectX (node mop Example.decide 5 tt (λ _ → leaf 3 7)))
ccTest-rhs = mapŴ (λ { (x , r) → (x , r) , 0# }) (collectX (node mop Example.decide 5 tt (λ _ → leaf 3 7)))

ccTest-check : ccTest-lhs ≡ ccTest-rhs
ccTest-check = refl

-- What is collectX(bump r (collectX S)) for a node-shaped S?
cbTest-lhs : Ŵ εop ((R × R) × R)
cbTest-lhs = collectX (bump 100 (collectX (node mop Example.decide 5 tt (λ _ → leaf 3 7))))

cbTest-rhs : Ŵ εop ((R × R) × R)
cbTest-rhs = mapŴ (λ { (x , r) → (x , 100 + r) , 0# }) (collectX (node mop Example.decide 5 tt (λ _ → leaf 3 7)))

cbTest-check : cbTest-lhs ≡ cbTest-rhs
cbTest-check = refl

-- (A further "cbGen"/"cbLeaf" block testing collectX(bump off S) for an
-- arbitrary (X×R)-payload S was deleted here for the same reason as above:
-- never actually checked by a prior run, and once reached, it turned out
-- to conflate S's own pair-payload with the pair collectX adds, giving a
-- type error, not a mathematical disagreement. collectX-bump-collectX in
-- Proofs.agda has the correct signature and is proven there directly.)

-- ---------------------------------------------------------------------
-- Does F-rule's OWN specific instance of B.5(3) fail? e-role := F[x] for
-- a frame whose companion piece is dirty; g-role := the outer ambient,
-- stuck on decide().
-- ---------------------------------------------------------------------

-- e2Frule : Loss ! εop -- discards a "loss(7)" via snd (contributing 7 to
-- the accumulated tell-loss along the way), then reports its own,
-- unrelated Loss-typed value 2 (chosen distinct from 7 so any confusion
-- between "the discarded 7" and "the reported 2" would show up plainly).
e2Frule : ∅ ⊢ Loss ! εop
e2Frule = snd (pair (lossE (val (vgnd 7))) (val (vgnd 2)))

fFrule : Frame ∅ UnitTy εop (UnitTy `× Loss) εop
fFrule = F-pairL e2Frule

gOuterFrule : LC ∅ (UnitTy `× Loss) εop
gOuterFrule = vabs (snd (pair (opE mop Example.decide (val (vgnd tt))) (val (vgnd 5))))

ρ0Frule : Env ∅
ρ0Frule ()

ρ1Frule : Env (∅ , UnitTy)
ρ1Frule = ρ0Frule ,, tt

-- Lsem's (and R̂-of's) codomain is R̂ ε = Ŵ ε ⊤ *unconditionally*
-- (collapse : Ŵ ε R → Ŵ ε ⊤ doesn't depend on the frame's hole type at
-- all) -- an earlier, never-actually-checked version of this test wrongly
-- declared these as Ŵ εop (⟦UnitTy⟧ × ⟦Loss⟧).
b53F-lhs : Ŵ εop ⊤
b53F-lhs = Lsem (vabs (thenE ⊆ᵉ-refl (plugF (weaken1F fFrule) (val (vvar Z))) (weaken1V gOuterFrule))) ρ0Frule tt

b53F-rhs : Ŵ εop ⊤
b53F-rhs = R̂-of {Y = ⟦ UnitTy `× Loss ⟧} (Esem (plugF (weaken1F fFrule) (val (vvar Z))) ρ1Frule)
                (λ b → widenŴ ⊆ᵉ-refl (Lsem (weaken1V gOuterFrule) ρ1Frule b))

b53F-root : Ŵ εop ⊤ → R
b53F-root (leaf r x)        = r
b53F-root (node m op r o κ) = r

b53F-lhs-root : b53F-root b53F-lhs ≡ 0
b53F-lhs-root = refl

b53F-rhs-root : b53F-root b53F-rhs ≡ 7
b53F-rhs-root = refl

b53F-refuted : b53F-lhs ≡ b53F-rhs → (0 ≡ 7)
b53F-refuted eq = cong b53F-root eq

-- ---------------------------------------------------------------------
-- Does the DISCREPANCY above actually leak into theorem-B9-F's own
-- conclusion (not just the auxiliary B.5(3) instance it would use)? Test
-- with the SAME dirty companion/stuck ambient, but now with a genuine
-- inner F-rule step: e := loss(rVal), e' := (), via R4 -- reusing the
-- SAME fFrule/gOuterFrule so the "dirty companion + stuck ambient" setup
-- is identical to the refuted case above.
-- ---------------------------------------------------------------------

rVal : R
rVal = 3

eB9F : ∅ ⊢ UnitTy ! εop
eB9F = lossE (val (vgnd rVal))

eB9F' : ∅ ⊢ UnitTy ! εop
eB9F' = val (vgnd tt)

-- The compound ambient F-rule's hypothesis actually needs (hole type
-- UnitTy, matching e/e' -- NOT gOuterFrule directly, whose own hole type
-- is UnitTy×Loss, the *target* type of the frame).
gStarB9F : LC ∅ UnitTy εop
gStarB9F = vabs (thenE ⊆ᵉ-refl (plugF (weaken1F fFrule) (val (vvar Z))) (weaken1V gOuterFrule))

-- R4 holds under ANY ambient, so it applies as-is to the compound one
-- F-rule's hypothesis requires (F-rule itself needs no separate proof
-- obligation for this half -- R4's OWN case of theorem-B9 is trivial).
stepB9F : gStarB9F ⊢ eB9F -[ rVal ]→ eB9F'
stepB9F = R4 rVal

-- Witness that this is a genuine instance of the F-rule hypothesis.
fruleStepB9F : gOuterFrule ⊢ plugF fFrule eB9F -[ rVal ]→ plugF fFrule eB9F'
fruleStepB9F = F-rule ⊆ᵉ-refl fFrule stepB9F

gammaFrule : ⟦ UnitTy `× Loss ⟧ → Ŵ εop ⊤
gammaFrule = λ a → widenŴ ⊆ᵉ-refl (Lsem gOuterFrule ρ0Frule a)

b9F-lhs : Ŵ εop ⟦ UnitTy `× Loss ⟧
b9F-lhs = Esem (plugF fFrule eB9F) ρ0Frule gammaFrule

b9F-rhs : Ŵ εop ⟦ UnitTy `× Loss ⟧
b9F-rhs = tell rVal (Esem (plugF fFrule eB9F') ρ0Frule gammaFrule)

-- theorem-B9-F's OWN conclusion for this instance: HOLDS (by refl). Both
-- eB9F and its companion e2Frule are operation-free, so the whole pair
-- never reaches a stuck node and gammaFrule (despite being built from a
-- genuinely stuck g) is never actually consulted by either side -- the
-- b53F-* discrepancy above lives entirely inside the *auxiliary*
-- Lsem(λx.F[x]▶g) construction used by Lemma B.7's proof, and doesn't
-- automatically transfer to the theorem's own, directly-observable
-- equation.
b9F-check : b9F-lhs ≡ b9F-rhs
b9F-check = refl

-- ---------------------------------------------------------------------
-- Quick concrete check before committing to a general proof: is
-- shift 0# T ≡ T for a NODE-shaped T (root loss r ≠ 0)?
-- ---------------------------------------------------------------------

shift0Test-T : Ŵ εop R
shift0Test-T = node mop Example.decide 5 tt (λ _ → leaf 3 7)

shift0Test-lhs shift0Test-rhs : Ŵ εop R
shift0Test-lhs = bind̂ (collectX shift0Test-T) (λ { (r3 , r2) → tell r2 (η̂ (0# + r3)) })
shift0Test-rhs = shift0Test-T

-- Refuted -- shift 0# is NOT the identity at a node (root loss 5 gets
-- redistributed into the leaf instead of staying at the root).
shift0Test-root : Ŵ εop R → R
shift0Test-root (leaf r x)        = r
shift0Test-root (node m op r o κ) = r

shift0Test-lhs-root : shift0Test-root shift0Test-lhs ≡ 0
shift0Test-lhs-root = refl

shift0Test-rhs-root : shift0Test-root shift0Test-rhs ≡ 5
shift0Test-rhs-root = refl

shift0Test-refuted : shift0Test-lhs ≡ shift0Test-rhs → (0 ≡ 5)
shift0Test-refuted eq = cong shift0Test-root eq

-- shift 0# T ≠ T (just confirmed above), but maybe collapse can't tell
-- the difference (both operations touch root-loss, and collapse discards
-- root-loss at every level anyway)? Test concretely.
shift0' : Ŵ εop R → Ŵ εop R
shift0' T = bind̂ (collectX T) (λ { (r3 , r2) → tell r2 (η̂ (0# + r3)) })

collapseShift0-lhs collapseShift0-rhs : Ŵ εop ⊤
collapseShift0-lhs = collapse (shift0' shift0Test-T)
collapseShift0-rhs = collapse shift0Test-T

collapseShift0-check : collapseShift0-lhs ≡ collapseShift0-rhs
collapseShift0-check = refl

-- Generalized hypothesis: collapse(shift r T) ≡ tell r(collapse T), for
-- ARBITRARY r (not just r=0#). Test at r=10, T a node.
collapseShiftGen-lhs collapseShiftGen-rhs : Ŵ εop ⊤
collapseShiftGen-lhs = collapse (bind̂ (collectX shift0Test-T) (λ { (r3 , r2) → tell r2 (η̂ (10 + r3)) }))
collapseShiftGen-rhs = tell 10 (collapse shift0Test-T)

-- Refuted -- the r=0# case (collapseShift0-check above) does NOT
-- generalize to arbitrary r. Root 0 vs 10.
collapseShiftGen-root : Ŵ εop ⊤ → R
collapseShiftGen-root (leaf r x)        = r
collapseShiftGen-root (node m op r o κ) = r

collapseShiftGen-lhs-root : collapseShiftGen-root collapseShiftGen-lhs ≡ 0
collapseShiftGen-lhs-root = refl

collapseShiftGen-rhs-root : collapseShiftGen-root collapseShiftGen-rhs ≡ 10
collapseShiftGen-rhs-root = refl

collapseShiftGen-refuted : collapseShiftGen-lhs ≡ collapseShiftGen-rhs → (0 ≡ 10)
collapseShiftGen-refuted eq = cong collapseShiftGen-root eq

-- ---------------------------------------------------------------------
-- Does theorem-B9-R7's postulated statement actually hold when e[v]
-- reaches a stuck operation? e := snd(pair(decide(), 5)) : Loss ! εop,
-- independent of the bound variable x (v itself is irrelevant).
-- ---------------------------------------------------------------------

r7-e : (∅ , UnitTy) ⊢ Loss ! εop
r7-e = snd (pair (opE mop Example.decide (val (vgnd tt))) (val (vgnd 5)))

r7-v : Val ∅ UnitTy
r7-v = vgnd tt

ρ0R7 : Env ∅
ρ0R7 ()

γ0R7 : ⟦ Loss ⟧ → Ŵ εop ⊤
γ0R7 = λ _ → η̂ tt

r7-lhs r7-rhs : Ŵ εop ⟦ Loss ⟧
r7-lhs = Esem (thenE ⊆ᵉ-refl (val r7-v) (vabs r7-e)) ρ0R7 γ0R7
r7-rhs = tell 0# (Esem (glocalE ⊆ᵉ-refl ⊆ᵉ-refl (r7-e [ r7-v ]) zeroLC) ρ0R7 γ0R7)

r7-root : Ŵ εop ⟦ Loss ⟧ → R
r7-root (leaf r x)        = r
r7-root (node m op r o κ) = r

r7-lhs-root : r7-root r7-lhs ≡ 0
r7-lhs-root = refl

r7-rhs-root : r7-root r7-rhs ≡ 0
r7-rhs-root = refl

r7-check : r7-lhs ≡ r7-rhs
r7-check = refl

-- ---------------------------------------------------------------------
-- Better test: e[v]'s OWN denotation should have a NONZERO root loss
-- BEFORE reaching decide() -- the previous test's e never accumulated
-- any loss ahead of the stuck point, so it couldn't discriminate.
-- e := snd(pair(loss(7), snd(pair(decide(), 5))))
--   -- records loss 7 immediately, THEN reaches decide(), THEN (once
--   -- resumed) discards the choice and reports 5.
-- ---------------------------------------------------------------------

r7b-e : (∅ , UnitTy) ⊢ Loss ! εop
r7b-e = snd (pair (lossE (val (vgnd 7)))
                   (snd (pair (opE mop Example.decide (val (vgnd tt))) (val (vgnd 5)))))

r7b-lhs r7b-rhs : Ŵ εop ⟦ Loss ⟧
r7b-lhs = Esem (thenE ⊆ᵉ-refl (val r7-v) (vabs r7b-e)) ρ0R7 γ0R7
r7b-rhs = tell 0# (Esem (glocalE ⊆ᵉ-refl ⊆ᵉ-refl (r7b-e [ r7-v ]) zeroLC) ρ0R7 γ0R7)

r7b-root : Ŵ εop ⟦ Loss ⟧ → R
r7b-root (leaf r x)        = r
r7b-root (node m op r o κ) = r

-- EXPERIMENTAL VARIANT (mapŴ-based Esem(thenE), see Denotational.agda):
-- the counterexample is GONE -- both sides now have root 7, and the full
-- equality r7b-check holds by refl.
r7b-lhs-root : r7b-root r7b-lhs ≡ 7
r7b-lhs-root = refl

r7b-rhs-root : r7b-root r7b-rhs ≡ 7
r7b-rhs-root = refl

r7b-check : r7b-lhs ≡ r7b-rhs
r7b-check = refl

-- ---------------------------------------------------------------------
-- Does the NEW mapŴ-based combine-step fix the companion-frame (F-pairL)
-- case too, or is b53F-* (still refuted above, unchanged) evidence of a
-- genuinely DIFFERENT defect? Isolate the exact claim theorem-B9-F's
-- companion cases would need: collapse(mapŴ(r+_) T) ≡ tell r(collapse T)
-- -- the direct analogue of the (already-refuted) collapse-shift claim,
-- but for mapŴ instead of shift. T := node, root loss 5, leaf 3 either
-- way; r := 10.
-- ---------------------------------------------------------------------

collapseMapGen-T : Ŵ εop R
collapseMapGen-T = node mop Example.decide 5 tt (λ _ → leaf 3 7)

collapseMapGen-lhs collapseMapGen-rhs : Ŵ εop ⊤
collapseMapGen-lhs = collapse (mapŴ (10 +_) collapseMapGen-T)
collapseMapGen-rhs = tell 10 (collapse collapseMapGen-T)

collapseMapGen-root : Ŵ εop ⊤ → R
collapseMapGen-root (leaf r x)        = r
collapseMapGen-root (node m op r o κ) = r

collapseMapGen-lhs-root : collapseMapGen-root collapseMapGen-lhs ≡ 0
collapseMapGen-lhs-root = refl

collapseMapGen-rhs-root : collapseMapGen-root collapseMapGen-rhs ≡ 10
collapseMapGen-rhs-root = refl

collapseMapGen-refuted : collapseMapGen-lhs ≡ collapseMapGen-rhs → (0 ≡ 10)
collapseMapGen-refuted eq = cong collapseMapGen-root eq

-- ---------------------------------------------------------------------
-- The genuinely discriminating test: does theorem-B9-F's OWN conclusion
-- (not just the mini-B7 auxiliary lemma) survive for F-pairL when the
-- INNER step is itself a swap-relevant rule (R7, now fixed under the
-- mapŴ-based semantics) whose reduct genuinely reaches decide() -- so
-- that pair(e, e2Frule) becomes a stuck node and the ambient gOuterFrule
-- is actually consulted by BOTH sides, unlike the earlier b9F-check
-- (which used R4 and never touched an operation at all)?
--
-- e := (() ▶ λx. snd(pair(decide(), 5)))   [thenE, R7's own shape]
-- e' := ⟨snd(pair(decide(), 5))⟩_zeroLC     [R7's reduct]
-- Frame's hole type is now Loss (not UnitTy), since thenE's own result
-- type is always Loss; companion e2Frule (dirty, discards loss 7) and
-- ambient gOuterFrule (stuck on decide, retyped to Loss×Loss) reused.
-- ---------------------------------------------------------------------

fFrule3 : Frame ∅ Loss εop (Loss `× Loss) εop
fFrule3 = F-pairL e2Frule

gOuterFrule3 : LC ∅ (Loss `× Loss) εop
gOuterFrule3 = vabs (snd (pair (opE mop Example.decide (val (vgnd tt))) (val (vgnd 5))))

ρ0Frule3 : Env ∅
ρ0Frule3 ()

r7nested-body : (∅ , UnitTy) ⊢ Loss ! εop
r7nested-body = snd (pair (opE mop Example.decide (val (vgnd tt))) (val (vgnd 5)))

eNested eNested' : ∅ ⊢ Loss ! εop
eNested  = thenE ⊆ᵉ-refl (val (vgnd tt)) (vabs r7nested-body)
eNested' = glocalE ⊆ᵉ-refl ⊆ᵉ-refl (r7nested-body [ vgnd tt ]) zeroLC

-- R7's own hypothesis is universally quantified over its ambient (it
-- "disregards g" entirely), but F-rule needs the step instantiated
-- specifically at the COMPOUND ambient it constructs -- gStarNested,
-- hole type Loss (matching fFrule3's own hole type), NOT gOuterFrule3
-- (type LC ∅ (Loss×Loss) εop, the outer frame's own ambient role).
gStarNested : LC ∅ Loss εop
gStarNested = vabs (thenE ⊆ᵉ-refl (plugF (weaken1F fFrule3) (val (vvar Z))) (weaken1V gOuterFrule3))

stepNested : gStarNested ⊢ eNested -[ 0 ]→ eNested'
stepNested = R7 ⊆ᵉ-refl (vgnd tt) r7nested-body

plugNested plugNested' : ∅ ⊢ Loss `× Loss ! εop
plugNested  = plugF fFrule3 eNested
plugNested' = plugF fFrule3 eNested'

-- Witness that F-rule genuinely applies here.
fruleStepNested : gOuterFrule3 ⊢ plugNested -[ 0 ]→ plugNested'
fruleStepNested = F-rule ⊆ᵉ-refl fFrule3 stepNested

gammaFrule3 : ⟦ Loss `× Loss ⟧ → Ŵ εop ⊤
gammaFrule3 = λ a → widenŴ ⊆ᵉ-refl (Lsem gOuterFrule3 ρ0Frule3 a)

bNested-lhs bNested-rhs : Ŵ εop ⟦ Loss `× Loss ⟧
bNested-lhs = Esem plugNested ρ0Frule3 gammaFrule3
bNested-rhs = tell 0# (Esem plugNested' ρ0Frule3 gammaFrule3)

-- Is the pair genuinely stuck (not accidentally resolved to a leaf)?
bNested-isNode : Ŵ εop ⟦ Loss `× Loss ⟧ → Set
bNested-isNode (leaf r x)     = ⊥
  where open import Data.Empty using (⊥)
bNested-isNode (node m op r o κ) = ⊤

bNested-lhs-isNode : bNested-isNode bNested-lhs
bNested-lhs-isNode = tt

bNested-check : bNested-lhs ≡ bNested-rhs
bNested-check = refl

-- ---------------------------------------------------------------------
-- Nail down the exact bridging identity theorem-B9-F needs for F-pairL:
-- test with r ≠ 0 AND a companion that itself reaches a stuck operation,
-- so tell r and mapŴ (r +_) genuinely disagree if either shows up.
-- Companion: e2Frule4 := snd(pair(decide(), 5)) -- reaches decide(),
-- discards the choice, reports 5 (no extra discarded loss of its own).
-- Hole: e := loss(3), e' := (), via R4 (r=3).
-- ---------------------------------------------------------------------

e2Frule4 : ∅ ⊢ Loss ! εop
e2Frule4 = snd (pair (opE mop Example.decide (val (vgnd tt))) (val (vgnd 5)))

fFrule4 : Frame ∅ UnitTy εop (UnitTy `× Loss) εop
fFrule4 = F-pairL e2Frule4

gOuterFrule4 : LC ∅ (UnitTy `× Loss) εop
gOuterFrule4 = vabs (val (vgnd 0#))

ρ0Frule4 : Env ∅
ρ0Frule4 ()

e4 e4' : ∅ ⊢ UnitTy ! εop
e4  = lossE (val (vgnd 3))
e4' = val (vgnd tt)

gStar4 : LC ∅ UnitTy εop
gStar4 = vabs (thenE ⊆ᵉ-refl (plugF (weaken1F fFrule4) (val (vvar Z))) (weaken1V gOuterFrule4))

step4 : gStar4 ⊢ e4 -[ 3 ]→ e4'
step4 = R4 3

plug4 plug4' : ∅ ⊢ UnitTy `× Loss ! εop
plug4  = plugF fFrule4 e4
plug4' = plugF fFrule4 e4'

fruleStep4 : gOuterFrule4 ⊢ plug4 -[ 3 ]→ plug4'
fruleStep4 = F-rule ⊆ᵉ-refl fFrule4 step4

gamma4 : ⟦ UnitTy `× Loss ⟧ → Ŵ εop ⊤
gamma4 = λ a → widenŴ ⊆ᵉ-refl (Lsem gOuterFrule4 ρ0Frule4 a)

b9F4-lhs : Ŵ εop ⟦ UnitTy `× Loss ⟧
b9F4-lhs = Esem plug4 ρ0Frule4 gamma4

-- theorem-B9-F's own target (note: a naive "mapŴ (3 +_)" alternative
-- doesn't even type-check here -- the frame's target payload is
-- UnitTy×Loss, not bare R, so mapŴ can't uniformly bump it the way
-- thenE's own combine-step bumps a bare Loss payload; tell is the only
-- operation that makes sense at this payload type regardless).
b9F4-rhs-tell : Ŵ εop ⟦ UnitTy `× Loss ⟧
b9F4-rhs-tell = tell 3 (Esem plug4' ρ0Frule4 gamma4)

b9F4-isNode : Ŵ εop ⟦ UnitTy `× Loss ⟧ → Set
b9F4-isNode (leaf r x)     = ⊥
  where open import Data.Empty using (⊥)
b9F4-isNode (node m op r o κ) = ⊤

b9F4-lhs-isNode : b9F4-isNode b9F4-lhs
b9F4-lhs-isNode = tt

b9F4-check-tell : b9F4-lhs ≡ b9F4-rhs-tell
b9F4-check-tell = refl

-- ---------------------------------------------------------------------
-- The genuinely hardest combination: companion discards a real loss
-- (r1 ≠ 0 possible) AND itself reaches a stuck operation (so the pair
-- becomes a node regardless of the ambient), COMBINED with a nonzero-r
-- step (R4) for the hole. e2Frule4's companion sidestepped this (it
-- reached decide() but never discarded anything, so r1 stayed 0
-- throughout -- not a real test of the dirty-companion defect).
-- e2Frule5 := snd(pair(loss(7), snd(pair(decide(), 5))))
-- ---------------------------------------------------------------------

e2Frule5 : ∅ ⊢ Loss ! εop
e2Frule5 = snd (pair (lossE (val (vgnd 7)))
                      (snd (pair (opE mop Example.decide (val (vgnd tt))) (val (vgnd 5)))))

fFrule5 : Frame ∅ UnitTy εop (UnitTy `× Loss) εop
fFrule5 = F-pairL e2Frule5

gOuterFrule5 : LC ∅ (UnitTy `× Loss) εop
gOuterFrule5 = vabs (val (vgnd 0#))

ρ0Frule5 : Env ∅
ρ0Frule5 ()

gStar5 : LC ∅ UnitTy εop
gStar5 = vabs (thenE ⊆ᵉ-refl (plugF (weaken1F fFrule5) (val (vvar Z))) (weaken1V gOuterFrule5))

step5 : gStar5 ⊢ e4 -[ 3 ]→ e4'
step5 = R4 3

plug5 plug5' : ∅ ⊢ UnitTy `× Loss ! εop
plug5  = plugF fFrule5 e4
plug5' = plugF fFrule5 e4'

fruleStep5 : gOuterFrule5 ⊢ plug5 -[ 3 ]→ plug5'
fruleStep5 = F-rule ⊆ᵉ-refl fFrule5 step5

gamma5 : ⟦ UnitTy `× Loss ⟧ → Ŵ εop ⊤
gamma5 = λ a → widenŴ ⊆ᵉ-refl (Lsem gOuterFrule5 ρ0Frule5 a)

b9F5-lhs b9F5-rhs : Ŵ εop ⟦ UnitTy `× Loss ⟧
b9F5-lhs = Esem plug5 ρ0Frule5 gamma5
b9F5-rhs = tell 3 (Esem plug5' ρ0Frule5 gamma5)

b9F5-isNode : Ŵ εop ⟦ UnitTy `× Loss ⟧ → Set
b9F5-isNode (leaf r x)     = ⊥
  where open import Data.Empty using (⊥)
b9F5-isNode (node m op r o κ) = ⊤

b9F5-lhs-isNode : b9F5-isNode b9F5-lhs
b9F5-lhs-isNode = tt

b9F5-check : b9F5-lhs ≡ b9F5-rhs
b9F5-check = refl

-- ---------------------------------------------------------------------
-- The OTHER hard combination: the AMBIENT g itself (not the companion)
-- discards a real loss and reaches a stuck operation. Hand-derivation of
-- mini-B7's own auxiliary equation for F-pairL (unfolding Lsem(g*) via
-- the thenE clause, lemma-B6, and bind̂ˢ's definition) shows it reduces,
-- at its base leaf case, to EXACTLY collapseMapGen-refuted's counter-
-- example -- collapse(mapŴ(r+_)(widenŴ sub(V x))) vs tell r(collapse
-- (widenŴ sub(V x))) -- but ONLY when V x = Vsem g ρ (a,b) δ' (the
-- AMBIENT g applied to the companion's eventual value) is node-shaped
-- AND that leaf is actually reached with the continuation genuinely
-- invoked -- which requires the COMPANION itself to reach an operation
-- (a "clean"/pure companion never calls its own continuation at all, so
-- a dirty ambient is inert against it -- confirmed by hand below: with
-- a clean e2New, γ is simply never consulted and the tree comes out
-- leaf-shaped regardless of the ambient, which is NOT a real test).
-- So: reuse e2Frule5 (loss 7, THEN decide(), discarding the choice,
-- THEN report 5 -- exactly the shape that reaches a leaf with r0=7
-- AFTER an operation, so γ genuinely gets called there) as the
-- companion, but swap the ambient from const-zero to one that ITSELF
-- calls decide() -- the shape the hand-derivation identifies as the
-- real fault line for mini-B7.
-- ---------------------------------------------------------------------

fFrule6 : Frame ∅ UnitTy εop (UnitTy `× Loss) εop
fFrule6 = F-pairL e2Frule5

gOuterFrule6 : LC ∅ (UnitTy `× Loss) εop
gOuterFrule6 = vabs (snd (pair (opE mop Example.decide (val (vgnd tt))) (val (vgnd 5))))

ρ0Frule6 : Env ∅
ρ0Frule6 ()

gStar6 : LC ∅ UnitTy εop
gStar6 = vabs (thenE ⊆ᵉ-refl (plugF (weaken1F fFrule6) (val (vvar Z))) (weaken1V gOuterFrule6))

step6 : gStar6 ⊢ e4 -[ 3 ]→ e4'
step6 = R4 3

plug6 plug6' : ∅ ⊢ UnitTy `× Loss ! εop
plug6  = plugF fFrule6 e4
plug6' = plugF fFrule6 e4'

fruleStep6 : gOuterFrule6 ⊢ plug6 -[ 3 ]→ plug6'
fruleStep6 = F-rule ⊆ᵉ-refl fFrule6 step6

gamma6 : ⟦ UnitTy `× Loss ⟧ → Ŵ εop ⊤
gamma6 = λ a → widenŴ ⊆ᵉ-refl (Lsem gOuterFrule6 ρ0Frule6 a)

b9F6-lhs b9F6-rhs : Ŵ εop ⟦ UnitTy `× Loss ⟧
b9F6-lhs = Esem plug6 ρ0Frule6 gamma6
b9F6-rhs = tell 3 (Esem plug6' ρ0Frule6 gamma6)

b9F6-isNode : Ŵ εop ⟦ UnitTy `× Loss ⟧ → Set
b9F6-isNode (leaf r x)     = ⊥
  where open import Data.Empty using (⊥)
b9F6-isNode (node m op r o κ) = ⊤

b9F6-lhs-isNode : b9F6-isNode b9F6-lhs
b9F6-lhs-isNode = tt

b9F6-check : b9F6-lhs ≡ b9F6-rhs
b9F6-check = refl

-- ---------------------------------------------------------------------
-- theorem-B9-R5-gen soundness check (ORIGINAL FINDING, then FIXED):
-- EffCxt is explicitly a MULTISET (Domains.agda's own comment on `_,ℓ_`:
-- "extend ε by one further (freshly introduced, 'outermost') copy of
-- ℓ" -- nested handlers for the SAME effect label are a legitimate,
-- intended scenario, not an edge case to rule out). R5's own OpSem rule
-- is universally quantified over m : ℓ ∈ εop with NO side-condition
-- pinning m to the freshly-introduced (outermost/appended) copy
-- specifically. theorem-B9-R5-gen's stated RHS (subE(...)(clause h op))
-- doesn't depend on WHICH m was used either -- so for the theorem to
-- hold, the LHS (Esem of the handleE term) must not depend on it either.
-- It ORIGINALLY did: handlerΨ dispatched via `∈-++⁻ ε m` (does the
-- WITNESS's own position land in the old prefix or the freshly-appended
-- slot?), which disagreed between m1/m2 below (a stuck NODE vs a LEAF)
-- even though R5's own OPERATIONAL rule never inspected m's structure at
-- all (only `¬ Handles k ℓ`, itself already witness-independent) --
-- confirmed as a genuine, machine-checked counterexample via
-- r5-lhs-old-isNode (no longer valid, see below) refuting r5-lhs-new-
-- check's implied equality. FIXED (Denotational.agda's handlerΨ) by
-- dispatching on LABEL EQUALITY (ℓ1 ≟ᵉ ℓ) instead of witness position --
-- bringing the denotational semantics back in line with the (already
-- correct) operational one, exactly as the mapŴ fix did for (R7). Handler
-- hInner for ndet, with OUTER effect εOuter = [ndet] (ndet already
-- present OUTSIDE hInner too) -- so εInOp := (εOuter,ℓ ndet) = [ndet,
-- ndet] has TWO distinct membership witnesses, m1 (the OLD, εOuter-side
-- occurrence) and m2 (the NEW, hInner's own, appended occurrence) --
-- r5-fixed-check now confirms BOTH route identically to clause hInner
-- decide (a LEAF), regardless of which witness was supplied.
-- ---------------------------------------------------------------------

open import Data.List.Relation.Unary.Any using (there)
open import Relation.Nullary using (¬_)

εOuterR5 : EffCxt
εOuterR5 = Example.ndet ∷ []

εInOpR5 : EffCxt
εInOpR5 = εOuterR5 ,ℓ Example.ndet

hInner : Handler ∅ Example.ndet unit (gnd (in′ Example.decide)) UnitTy εOuterR5
clause hInner Example.decide = val (vgnd tt)
ret    hInner                = val (vgnd tt)

v1R5 : Val ∅ (gnd unit)
v1R5 = vgnd tt

v2R5 : Val ∅ (gnd (out Example.decide))
v2R5 = vgnd tt

m1R5 m2R5 : Example.ndet ∈ εInOpR5
m1R5 = here refl
m2R5 = there (here refl)

kR5 : ContCxt ∅ (gnd (in′ Example.decide)) εInOpR5 (gnd (in′ Example.decide)) εInOpR5
kR5 = ▫

nhR5 : ¬ Handles kR5 Example.ndet
nhR5 ()

ρ0R5 : Env ∅
ρ0R5 ()

γ0R5 : ⟦ UnitTy ⟧ → Ŵ εOuterR5 ⊤
γ0R5 = λ _ → η̂ tt

r5-lhs-old r5-lhs-new : Ŵ εOuterR5 ⟦ UnitTy ⟧
r5-lhs-old = Esem (handleE hInner (val v1R5) (opE m1R5 Example.decide (val v2R5))) ρ0R5 γ0R5
r5-lhs-new = Esem (handleE hInner (val v1R5) (opE m2R5 Example.decide (val v2R5))) ρ0R5 γ0R5

-- POST-FIX (handlerΨ now dispatches by label equality, not witness
-- position): r5-lhs-old and r5-lhs-new are now BOTH leaf 0# tt, regardless
-- of which of the two distinct membership witnesses (m1R5, the old/outer
-- occurrence, vs m2R5, the fresh/inner one) was used to build the
-- operation -- confirming the fix actually closes the counterexample, not
-- just relocates it.
r5-lhs-old-check r5-lhs-new-check : Ŵ εOuterR5 ⟦ UnitTy ⟧
r5-lhs-old-check = r5-lhs-old
r5-lhs-new-check = r5-lhs-new

r5-fixed-check : r5-lhs-old ≡ r5-lhs-new
r5-fixed-check = refl

r5-fixed-check-value : r5-lhs-old ≡ leaf 0# tt
r5-fixed-check-value = refl

-- (Historical note: before the fix, m := m1R5 made r5-lhs-old a stuck
-- NODE, while theorem-B9-R5-gen's RHS -- tell 0# (Esem (subE (...)
-- (clause hInner decide)) ρ0R5 γ0R5) -- is unconditionally a LEAF
-- regardless of m (clause hInner decide = val (vgnd tt) is a bare value
-- with no embedded operations, so subE of it is still a bare value) --
-- node ≠ leaf, a genuine contradiction. r5-fixed-check above confirms
-- that no longer happens.)

-- ---------------------------------------------------------------------
-- Does theorem-B9-R5-gen's own proof strategy (substitute Vsem fk ρ / Vsem
-- fl ρ for handlerΨ's own l1v/k1v continuations, then use congruence)
-- actually work? That strategy needs Vsem fk ρ (p'',a) ≡ k1v (p'',a) as a
-- FULL function of p'' -- not just at p''=Vsem v1 ρ. handlerSem h ρ p G γ
-- uses its own parameter p TWICE: once buried inside D (the "what happens
-- once G resolves" continuation fed to G), once at the very final
-- application. k1v is built from the OUTER p inside D, but only
-- substitutes p'' at the final step -- a genuinely different construction
-- from a FRESH handlerSem call at p'' (which would vary p in both places
-- together). This section tests concretely whether that difference is
-- ever observable.
--
-- Handler: par := Loss, so p is a bare R value, directly reportable via
-- ret h = lossE(vvar p) -- no comparison primitive needed (mySig has
-- none), just report WHICH p got used and see if the recorded loss
-- differs between the "outer D" route and a "fresh call at p''" route.
-- k contains one nested (same-label) decide() call so that κ a := Esem
-- (plugK (weaken1K k) (val (vvar Z))) (ρ ,, a) actually reaches a point
-- where D gets consulted (a bare k = ▫ never would: η̂ˢ ignores its own
-- continuation entirely, so the discrepancy can't surface there).
-- ---------------------------------------------------------------------

module PLeakCheck where
  open import Data.Bool using (Bool; true; false)
  open import Data.List.Relation.Unary.Any using (here)
  open import Data.Empty using (⊥)

  εpl : EffCxt
  εpl = Example.ndet ∷ []

  mpl : Example.ndet ∈ εpl
  mpl = here refl

  σpl : Ty
  σpl = gnd (in′ Example.decide) `× gnd (in′ Example.decide)

  -- ret ignores the resumed pair (Z) entirely, reports p (SZ, a Loss/R
  -- value) directly as the recorded loss.
  hLeak : Handler ∅ Example.ndet loss σpl UnitTy []
  clause hLeak Example.decide = app (val (vvar Z)) (pair (val (vvar (S (S (S Z))))) (val (vgnd true)))
  ret    hLeak                = lossE (val (vvar (S Z)))

  -- k = F∘ ▫ (F-pairL (nested decide())): resume the outer op with a,
  -- pair it with a FRESH decide() call for the SAME label.
  kpl : ContCxt ∅ (gnd (in′ Example.decide)) εpl σpl εpl
  kpl = F∘ ▫ (F-pairL (opE mpl Example.decide (val (vgnd tt))))

  nhpl : ¬ Handles kpl Example.ndet
  nhpl ()

  ρpl : Env ∅
  ρpl ()

  γpl : ⟦ UnitTy ⟧ → Ŵ [] ⊤
  γpl _ = η̂ tt

  v1pl : Val ∅ (gnd loss)
  v1pl = vgnd 5

  v1''pl : Val ∅ (gnd loss)
  v1''pl = vgnd 7

  κpl : ⟦ in′ Example.decide ⟧ᴳ → Ŝ εpl ⟦ σpl ⟧
  κpl a = Esem (plugK (weaken1K kpl) (val (vvar Z))) (ρpl ,, a)

  -- D built from the OUTER p (=5): "what happens once G resolves".
  Dpl : ⟦ σpl ⟧ → Ŵ εpl ⊤
  Dpl a' = widenŴ ⊆ᵉ-,ℓ (ext̂ Ŵ-alg γpl (handlerRet hLeak ρpl γpl a' (Vsem v1pl ρpl)))

  -- k1v(p'',a) as handlerΨ-yes-eq's own formula literally builds it:
  -- apply the OUTER-D-built tree, walked via ext̂, AT p''.
  k1v-at : ⟦ gnd loss ⟧ → ⟦ in′ Example.decide ⟧ᴳ → Ŵ [] ⟦ UnitTy ⟧
  k1v-at p'' a = ext̂ (handlerAlg hLeak ρpl γpl) (handlerRet hLeak ρpl γpl) (κpl a Dpl) p''

  -- a FRESH handlerSem call at p'' (matching what Vsem fk ρ (p'',a) γ
  -- actually reduces to, via renH-coh + fk-match).
  fresh-at : ⟦ gnd loss ⟧ → ⟦ in′ Example.decide ⟧ᴳ → Ŵ [] ⟦ UnitTy ⟧
  fresh-at p'' a = handlerSem hLeak ρpl p'' (κpl a) γpl

  -- Both computed at a = true, p'' = 7 (≠ outer p = 5).
  k1v-result fresh-result : Ŵ [] ⟦ UnitTy ⟧
  k1v-result   = k1v-at 7 true
  fresh-result = fresh-at 7 true

  -- If theorem-B9-R5-gen's substitution strategy were sound, these two
  -- would have to agree (Vsem fk ρ reduces to fresh-at, and k1v to
  -- k1v-at). Check by refl: does Agda accept it, or do the two sides
  -- reduce to visibly different Ŵ-values (different recorded loss)?
  pleak-check : k1v-result ≡ fresh-result
  pleak-check = refl

  -- Sanity: confirm this test is non-vacuous -- fresh-at genuinely
  -- reports WHATEVER p'' it's given (not some constant), and k1v-at
  -- likewise genuinely reports p'' (not silently falling back to the
  -- outer p=5 baked into Dpl). If both of these hold AND pleak-check
  -- holds, the p''-genericity worry is refuted concretely, not just by
  -- assumption.
  fresh-reports-p'' : fresh-at 7 true ≡ leaf 7 tt
  fresh-reports-p'' = refl

  fresh-reports-p''-5 : fresh-at 5 true ≡ leaf 5 tt
  fresh-reports-p''-5 = refl

  k1v-reports-p'' : k1v-at 7 true ≡ leaf 7 tt
  k1v-reports-p'' = refl

  k1v-does-NOT-report-outer-p : (k1v-at 7 true ≡ leaf 5 tt) → ⊥
  k1v-does-NOT-report-outer-p ()

-- ---------------------------------------------------------------------
-- Follow-up to PLeakCheck: that test's k only ever used l1v/k1v via k1
-- (immediate resumption). What if a NESTED handler's own clause instead
-- "leaks" its l1's own reported loss -- via lossE(app l1 (pair p true))
-- -- discarding l1's VALUE but keeping its accumulated LOSS? l1 is
-- documented (Denotational.agda) as "collect(γ†Ŵε(k(a)(p)))", explicitly
-- exposing whatever the ambient continuation γ would report -- exactly
-- the mechanism the whole selection-monad framework exists for. Does
-- THIS let handlerSem's own "D built from an outer p" vs "a fresh call
-- at p''" discrepancy actually surface, unlike the immediate-resumption
-- case? Tested directly (bypassing the ContCxt/fk-match machinery):
-- build D, D'' the way PLeakCheck's own Dpl reduces (constant functions
-- reporting 5 vs 7), and check handlerSem h ρ p G D vs ...D'' for a
-- handler h whose clause leaks l1's own loss this way.
module PLeakCheck2 where
  open import Data.Bool using (Bool; true; false)
  open import Data.List.Relation.Unary.Any using (here)

  εpl2 : EffCxt
  εpl2 = Example.ndet ∷ []

  mpl2 : Example.ndet ∈ εpl2
  mpl2 = here refl

  -- h's own clause: report l1(p',true)'s own accumulated loss (via
  -- lossE, discarding l1's Loss-typed VALUE but keeping what it reports),
  -- THEN resume via k1(p',true), keeping k1's own value as the result.
  hLeak2 : Handler ∅ Example.ndet loss (gnd (in′ Example.decide)) UnitTy []
  clause hLeak2 Example.decide =
    snd (pair (lossE (app (val (vvar (S Z))) (pair (val (vvar (S (S (S Z))))) (val (vgnd true)))))
              (app (val (vvar Z)) (pair (val (vvar (S (S (S Z))))) (val (vgnd true)))))
  ret hLeak2 = val (vgnd tt)

  ρpl2 : Env ∅
  ρpl2 ()

  -- G: a bare stuck decide(), resumed immediately (η̂ˢ) -- the simplest
  -- possible "body" for hLeak2 to catch, no ContCxt/fk-match needed.
  Gpl2 : Ŝ εpl2 ⟦ gnd (in′ Example.decide) ⟧
  Gpl2 = φ̂ˢ mpl2 Example.decide tt η̂ˢ

  -- D/D'': exactly the shape PLeakCheck's own Dpl reduces to (a constant
  -- function reporting the outer p directly), for p := 5 vs p'' := 7.
  Dpl2 D''pl2 : ⟦ UnitTy ⟧ → Ŵ [] ⊤
  Dpl2   _ = leaf 5 tt
  D''pl2 _ = leaf 7 tt

  p2 : ⟦ gnd loss ⟧
  p2 = 0

  leak-D leak-D'' : Ŵ [] ⟦ UnitTy ⟧
  leak-D   = handlerSem hLeak2 ρpl2 p2 Gpl2 Dpl2
  leak-D'' = handlerSem hLeak2 ρpl2 p2 Gpl2 D''pl2

  -- Does the discrepancy between "D built from p" and "D'' built from
  -- p''" survive being leaked into the recorded loss via l1, unlike the
  -- immediate-resumption case in PLeakCheck? Concrete values first.
  leak-D-value : leak-D ≡ leaf 5 tt
  leak-D-value = refl

  leak-D''-value : leak-D'' ≡ leaf 7 tt
  leak-D''-value = refl

  leak-differs : leak-D ≡ leak-D'' → (5 ≡ 7)
  leak-differs eq = cong (λ { (leaf r _) → r ; (node _ _ r _ _) → r }) eq

-- ---------------------------------------------------------------------
-- PLeakCheck2 refuted theorem-B9-R5-GEN specifically (γ fully arbitrary,
-- independent of the ambient loss continuation g). But theorem-B9 itself
-- (Proofs.agda) never actually CALLS theorem-B9-R5-gen at an arbitrary
-- γ -- it only ever uses theorem-B9-R5, which is theorem-B9-R5-gen
-- specialised to γ := ⌊g⌋[sub,ρ] (a ONE-LINE corollary, same pattern as
-- theorem-B9-R7 / theorem-B9-R7-gen). This section tests directly
-- whether the SAME "leaking" handler that broke -gen still breaks the
-- non-generalised theorem-B9-R5, now using the SAME "leaking" clause as
-- PLeakCheck2 but with par := unit (so there is no separate p-vs-p''
-- axis left at all -- k1v-match is trivial), and γ tied to g via
-- ⌊g⌋[sub,ρ] as the master theorem actually requires.
-- ---------------------------------------------------------------------

module R5NonGenCheck where
  open import Data.Bool using (Bool; true; false)
  open import Data.List.Relation.Unary.Any using (here)
  open import Relation.Nullary using (¬_)

  εpl3 : EffCxt
  εpl3 = Example.ndet ∷ []

  mpl3 : Example.ndet ∈ εpl3
  mpl3 = here refl

  σpl3 : Ty
  σpl3 = gnd (in′ Example.decide) `× gnd (in′ Example.decide)

  -- SAME leaking clause as PLeakCheck2.hLeak2, now with par := unit.
  h3 : Handler ∅ Example.ndet unit σpl3 UnitTy []
  clause h3 Example.decide =
    snd (pair (lossE (app (val (vvar (S Z))) (pair (val (vvar (S (S (S Z))))) (val (vgnd true)))))
              (app (val (vvar Z)) (pair (val (vvar (S (S (S Z))))) (val (vgnd true)))))
  ret h3 = val (vgnd tt)

  -- SAME nested-decide k as PLeakCheck.kpl.
  k3 : ContCxt ∅ (gnd (in′ Example.decide)) εpl3 σpl3 εpl3
  k3 = F∘ ▫ (F-pairL (opE mpl3 Example.decide (val (vgnd tt))))

  nh3 : ¬ Handles k3 Example.ndet
  nh3 ()

  v1pl3 : Val ∅ (gnd unit)
  v1pl3 = vgnd tt

  v2pl3 : Val ∅ (gnd (out Example.decide))
  v2pl3 = vgnd tt

  ρpl3 : Env ∅
  ρpl3 ()

  -- A nontrivial ambient g (reports 3 unconditionally) -- if fl really
  -- matches l1v only via g (not via an unrelated, arbitrary γ), this
  -- value should show up in both lhs3 and rhs3 alike.
  g3 : LC ∅ UnitTy []
  g3 = vabs (val (vgnd 3))

  sub3 : [] ⊆ᵉ []
  sub3 = ⊆ᵉ-refl

  -- γ := ⌊g⌋[sub,ρ], inlined (matches Proofs.agda's ⌊_⌋[_,_] exactly).
  γ3 : ⟦ UnitTy ⟧ → Ŵ [] ⊤
  γ3 a = widenŴ sub3 (Lsem g3 ρpl3 a)

  -- R5's own construction (Proofs.agda's theorem-B9-R5-gen), instantiated
  -- concretely.
  h3' : Handler (∅ , (gnd unit `× gnd (in′ Example.decide))) Example.ndet unit σpl3 UnitTy []
  h3' = renH S h3

  g3' : LC (∅ , (gnd unit `× gnd (in′ Example.decide))) UnitTy []
  g3' = renV S g3

  k3' : ContCxt (∅ , (gnd unit `× gnd (in′ Example.decide))) (gnd (in′ Example.decide)) εpl3 σpl3 εpl3
  k3' = weaken1K k3

  handled3 : (∅ , (gnd unit `× gnd (in′ Example.decide))) ⊢ UnitTy ! []
  handled3 = handleE h3' (fst (val (vvar Z))) (plugK k3' (snd (val (vvar Z))))

  fk3 : Val ∅ ((gnd unit `× gnd (in′ Example.decide)) ⇒ UnitTy ! [])
  fk3 = vabs (glocalE sub3 ⊆ᵉ-refl handled3 g3')

  fl3 : Val ∅ ((gnd unit `× gnd (in′ Example.decide)) ⇒ Loss ! [])
  fl3 = vabs (thenE sub3 handled3 g3')

  lhs3 rhs3 : Ŵ [] ⟦ UnitTy ⟧
  lhs3 = Esem (handleE h3 (val v1pl3) (plugK k3 (opE mpl3 Example.decide (val v2pl3)))) ρpl3 γ3
  rhs3 = tell 0# (Esem (subE (cons fk3 (cons fl3 (cons v2pl3 (cons v1pl3 idSub)))) (clause h3 Example.decide)) ρpl3 γ3)

  -- Does theorem-B9-R5 (NOT -gen) survive the same leaking clause that
  -- refuted -gen, now that γ is tied to g rather than arbitrary?
  r5-nongen-check : lhs3 ≡ rhs3
  r5-nongen-check = refl

  -- Sanity: confirm g's own report (3) actually shows up in the result,
  -- non-vacuously (g gets consulted three times along this path: once
  -- via l1's own leak inside handled3, once via thenE's own Lsem-fed
  -- continuation, once via thenE's own mapŴ combine step -- 3+3+3=9).
  r5-nongen-value : lhs3 ≡ leaf 9 tt
  r5-nongen-value = refl

  -- Same check with a DIFFERENT g (reports 5, not 3), to confirm the
  -- match isn't a coincidence specific to one number.
  g3b : LC ∅ UnitTy []
  g3b = vabs (val (vgnd 5))

  γ3b : ⟦ UnitTy ⟧ → Ŵ [] ⊤
  γ3b a = widenŴ sub3 (Lsem g3b ρpl3 a)

  h3b' : Handler (∅ , (gnd unit `× gnd (in′ Example.decide))) Example.ndet unit σpl3 UnitTy []
  h3b' = renH S h3

  g3b' : LC (∅ , (gnd unit `× gnd (in′ Example.decide))) UnitTy []
  g3b' = renV S g3b

  handled3b : (∅ , (gnd unit `× gnd (in′ Example.decide))) ⊢ UnitTy ! []
  handled3b = handleE h3b' (fst (val (vvar Z))) (plugK k3' (snd (val (vvar Z))))

  fk3b : Val ∅ ((gnd unit `× gnd (in′ Example.decide)) ⇒ UnitTy ! [])
  fk3b = vabs (glocalE sub3 ⊆ᵉ-refl handled3b g3b')

  fl3b : Val ∅ ((gnd unit `× gnd (in′ Example.decide)) ⇒ Loss ! [])
  fl3b = vabs (thenE sub3 handled3b g3b')

  lhs3b rhs3b : Ŵ [] ⟦ UnitTy ⟧
  lhs3b = Esem (handleE h3 (val v1pl3) (plugK k3 (opE mpl3 Example.decide (val v2pl3)))) ρpl3 γ3b
  rhs3b = tell 0# (Esem (subE (cons fk3b (cons fl3b (cons v2pl3 (cons v1pl3 idSub)))) (clause h3 Example.decide)) ρpl3 γ3b)

  r5-nongen-check-b : lhs3b ≡ rhs3b
  r5-nongen-check-b = refl

  r5-nongen-value-b : lhs3b ≡ leaf 15 tt
  r5-nongen-value-b = refl

-- ---------------------------------------------------------------------
-- Re-examining what PLeakCheck2 actually tested: it varied handlerSem's
-- own OUTER γ argument directly (Dpl2/D''pl2 were fed as handlerSem's
-- LAST argument, with p2 fixed at 0 throughout) -- i.e. the "arbitrary
-- γ1 vs γ2" axis that theorem-B9-R5-gen needs and theorem-B9-R5 (γ tied
-- to g) sidesteps entirely (only ONE γ is ever in play for the non-gen
-- theorem). That is NOT the same as PLeakCheck's own "p vs p''" axis
-- (fixed γ throughout, varying which p is baked into D vs used at the
-- final application) -- the one k1v-match / the substitution proof for
-- the NON-gen theorem actually needs, and which PLeakCheck (the
-- immediate-resumption clause) already confirmed holds. Does the
-- "p vs p''" axis ALSO survive when the clause is the "leaking" one
-- (PLeakCheck2's hLeak2), rather than the well-behaved, immediate-
-- resumption one (PLeakCheck's hLeak)?
-- ---------------------------------------------------------------------

module PCheckLeakingPvsP'' where
  open import Data.Bool using (Bool; true; false)
  open import Data.List.Relation.Unary.Any using (here)
  open import Data.Empty using (⊥)

  εplL : EffCxt
  εplL = Example.ndet ∷ []

  mplL : Example.ndet ∈ εplL
  mplL = here refl

  σplL : Ty
  σplL = gnd (in′ Example.decide) `× gnd (in′ Example.decide)

  -- The LEAKING clause (PLeakCheck2's hLeak2), now with par := loss
  -- (nontrivial) so p is genuinely observable, and ret reporting p
  -- directly, exactly as PLeakCheck's own hLeak.
  hLeakL : Handler ∅ Example.ndet loss σplL UnitTy []
  clause hLeakL Example.decide =
    snd (pair (lossE (app (val (vvar (S Z))) (pair (val (vvar (S (S (S Z))))) (val (vgnd true)))))
              (app (val (vvar Z)) (pair (val (vvar (S (S (S Z))))) (val (vgnd true)))))
  ret hLeakL = lossE (val (vvar (S Z)))

  -- SAME nested-decide k as PLeakCheck.kpl.
  kplL : ContCxt ∅ (gnd (in′ Example.decide)) εplL σplL εplL
  kplL = F∘ ▫ (F-pairL (opE mplL Example.decide (val (vgnd tt))))

  nhplL : ¬ Handles kplL Example.ndet
  nhplL ()

  ρplL : Env ∅
  ρplL ()

  -- γ is FIXED throughout (NOT varied) -- this tests the p-vs-p'' axis
  -- only, matching what theorem-B9-R5 (γ tied to g) actually needs.
  γplL : ⟦ UnitTy ⟧ → Ŵ [] ⊤
  γplL _ = leaf 11 tt

  κplL : ⟦ in′ Example.decide ⟧ᴳ → Ŝ εplL ⟦ σplL ⟧
  κplL a = Esem (plugK (weaken1K kplL) (val (vvar Z))) (ρplL ,, a)

  -- D built from the OUTER p (= 5).
  DplL : ⟦ σplL ⟧ → Ŵ εplL ⊤
  DplL a' = widenŴ ⊆ᵉ-,ℓ (ext̂ Ŵ-alg γplL (handlerRet hLeakL ρplL γplL a' 5))

  k1v-atL : ⟦ gnd loss ⟧ → ⟦ in′ Example.decide ⟧ᴳ → Ŵ [] ⟦ UnitTy ⟧
  k1v-atL p'' a = ext̂ (handlerAlg hLeakL ρplL γplL) (handlerRet hLeakL ρplL γplL) (κplL a DplL) p''

  fresh-atL : ⟦ gnd loss ⟧ → ⟦ in′ Example.decide ⟧ᴳ → Ŵ [] ⟦ UnitTy ⟧
  fresh-atL p'' a = handlerSem hLeakL ρplL p'' (κplL a) γplL

  -- Both at p'' = 7 (≠ outer p = 5), a = true, WITH the leaking clause
  -- and γ FIXED (not varied) -- does the p-vs-p'' match still hold?
  k1v-resultL fresh-resultL : Ŵ [] ⟦ UnitTy ⟧
  k1v-resultL   = k1v-atL 7 true
  fresh-resultL = fresh-atL 7 true

  pleakL-check : k1v-resultL ≡ fresh-resultL
  pleakL-check = refl

  -- Sanity: is this non-vacuous -- does the result actually depend on
  -- p''=7 (not silently reducing to something using the outer p=5
  -- instead, which would make the match meaningless)?
  fresh-atL-p5 : Ŵ [] ⟦ UnitTy ⟧
  fresh-atL-p5 = fresh-atL 5 true

  fresh-atL-differs-by-p'' : fresh-resultL ≡ fresh-atL-p5 → ⊥
  fresh-atL-differs-by-p'' ()
