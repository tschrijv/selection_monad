-- Tests k1v-match's own S-handleB case specifically: does the "p vs
-- p''" match (PLeakCheck / PCheckLeakingPvsP'' both confirmed it for k
-- embedding a RECURSIVE, same-label operation) still hold when k
-- instead embeds a DIFFERENT handler h2 via S-handleB, with h2's own
-- clause "leaking" its own l1's reported loss? Needs two distinct
-- effect labels (R5's own ¬ Handles k ℓ precondition forbids h2 from
-- sharing the outer handler's label), hence Example2.mySig2.
module B5Core2 where

open import Domains
open import Example2 using (mySig2)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Axiom.Extensionality.Propositional using (Extensionality)

postulate
  funext : ∀ {a b} → Extensionality a b

open Sig mySig2
open import Syntax mySig2
open import Subst mySig2
open import OpSem mySig2
open import Denotational mySig2
import Example2

-- h2's own outer effect is [ndetA] (what's left once h2 handles
-- ndetB -- ndetA remains outstanding, for h to catch). So k's own
-- hole/result effect must be ([ndetA] ,ℓ ndetB) = [ndetA, ndetB].
εB : EffCxt
εB = Example2.ndetA ∷ Example2.ndetB ∷ []

mB : Example2.ndetB ∈ εB
mB = there (here refl)

σB : Ty
σB = gnd (in′ Example2.decideB) `× gnd (in′ Example2.decideB)

-- h2: nested handler, embedded within k via S-handleB. LEAKING clause,
-- same shape as PLeakCheck2/PCheckLeakingPvsP''. Its own ε is [ndetA]
-- (ndetA still outstanding for the OUTER h to catch).
h2 : Handler ∅ Example2.ndetB unit σB UnitTy (Example2.ndetA ∷ [])
clause h2 Example2.decideB =
  snd (pair (lossE (app (val (vvar (S Z))) (pair (val (vvar (S (S (S Z))))) (val (vgnd true)))))
            (app (val (vvar Z)) (pair (val (vvar (S (S (S Z))))) (val (vgnd true)))))
ret h2 = val (vgnd tt)

w2 : Val ∅ (gnd unit)
w2 = vgnd tt

-- k' embeds a FRESH decideB() call (h2's own operation), at effect εB.
k' : ContCxt ∅ (gnd (in′ Example2.decideB)) εB σB εB
k' = F∘ ▫ (F-pairL (opE mB Example2.decideB (val (vgnd tt))))

-- k := S∘ k' (S-handleB h2 w2): embeds h2 via S-handleB, NOT via
-- recursive same-label handling. Result effect = h2's own ε = [ndetA].
k : ContCxt ∅ (gnd (in′ Example2.decideB)) εB UnitTy (Example2.ndetA ∷ [])
k = S∘ k' (S-handleB h2 w2)

-- h: the OUTER handler k1v-match is about. par := loss (nontrivial, so
-- p is observable). label ndetA -- DIFFERENT from h2's ndetB, exactly
-- what k1v-match's own statement needs. Its own clause is irrelevant
-- here: κ a (built from k) never contains an ndetA-node (k only ever
-- produces ndetB-nodes, all caught by h2 internally), so ext̂'s own walk
-- (via handlerAlg h ρ γ) never actually invokes h's own clause at all --
-- only h's own ret matters.
h : Handler ∅ Example2.ndetA loss UnitTy UnitTy []
clause h Example2.decideA = val (vgnd tt)
ret h = lossE (val (vvar (S Z)))

ρB : Env ∅
ρB ()

γB : ⟦ UnitTy ⟧ → Ŵ [] ⊤
γB _ = leaf 11 tt

κB : ⟦ in′ Example2.decideB ⟧ᴳ → Ŝ (Example2.ndetA ∷ []) ⟦ UnitTy ⟧
κB a = Esem (plugK (weaken1K k) (val (vvar Z))) (ρB ,, a)

-- D built from the OUTER p (= 5).
DB : ⟦ UnitTy ⟧ → Ŵ (Example2.ndetA ∷ []) ⊤
DB a' = widenŴ ⊆ᵉ-,ℓ (ext̂ Ŵ-alg γB (handlerRet h ρB γB a' 5))

k1v-atB : ⟦ gnd loss ⟧ → ⟦ in′ Example2.decideB ⟧ᴳ → Ŵ [] ⟦ UnitTy ⟧
k1v-atB p'' a = ext̂ (handlerAlg h ρB γB) (handlerRet h ρB γB) (κB a DB) p''

fresh-atB : ⟦ gnd loss ⟧ → ⟦ in′ Example2.decideB ⟧ᴳ → Ŵ [] ⟦ UnitTy ⟧
fresh-atB p'' a = handlerSem h ρB p'' (κB a) γB

-- p = 5 (baked into DB), p'' = 7 (fresh call), γ FIXED (=γB throughout),
-- h2 (embedded via S-handleB, DIFFERENT label from h) LEAKS via l1.
-- Does k1v-match's own claim still hold?
k1v-resultB fresh-resultB : Ŵ [] ⟦ UnitTy ⟧
k1v-resultB   = k1v-atB 7 true
fresh-resultB = fresh-atB 7 true

-- Under the OLD, buggy handlerSem these were leaf 23 tt / leaf 25 tt
-- (a genuine discrepancy). fresh-resultB (which calls the FIXED
-- handlerSem) now reports p''=7 directly, matching the operational
-- semantics' own fresh-call behaviour.
fresh-resultB-value : fresh-resultB ≡ leaf 7 tt
fresh-resultB-value = refl

-- k1v-match-Shandle-check compares k1v-atB (a HAND-BUILT construction
-- using DB, the OLD "outer-p-baked-in" continuation style) against
-- fresh-atB (which now calls the FIXED handlerSem). DB's construction no
-- longer corresponds to anything the real handlerSem/fk-match machinery
-- builds -- it was only ever a standalone stand-in for "what R5's fk
-- construction was suspected to compute", superseded by the actual
-- fk-match lemma (Proofs.agda, proven unconditionally) and by
-- r5-ill-check below (which uses the REAL Esem/subE construction). Left
-- unproven/unchecked deliberately; see r5-ill-check for the real test.
-- k1v-match-Shandle-check : k1v-resultB ≡ fresh-resultB
-- k1v-match-Shandle-check = refl

-- Sanity: non-vacuous (genuinely depends on p''=7, not the outer p=5).
fresh-atB-p5 : Ŵ [] ⟦ UnitTy ⟧
fresh-atB-p5 = fresh-atB 5 true

fresh-atB-differs-by-p'' : fresh-resultB ≡ fresh-atB-p5 → ⊥
fresh-atB-differs-by-p'' ()

-- ---------------------------------------------------------------------
-- k1v-match (as a fully general lemma) is now confirmed false. But a
-- "well-behaved" clause only ever calls k1/l1 at its OWN bound p, which
-- becomes the SAME as the outer v1 upon substitution -- so p'' never
-- actually differs from p for such a clause, sidestepping the failing
-- case entirely. Does theorem-B9-R5 ITSELF still fail, if the clause is
-- instead "ill-behaved" -- calling k1 at a SYNTACTICALLY-CONSTRUCTED
-- CONSTANT (7), independent of its own bound p -- combined with the
-- SAME adversarial, S-handleB-embedded h2?
-- ---------------------------------------------------------------------

-- Same shape as h, but the clause calls k1 at a FIXED constant (7),
-- ignoring its own bound p entirely -- perfectly well-typed (Loss values
-- are always embeddable as syntactic constants, no PrimFun needed).
hIll : Handler ∅ Example2.ndetA loss UnitTy UnitTy []
clause hIll Example2.decideA = app (val (vvar Z)) (pair (val (vgnd 7)) (val (vgnd true)))
ret hIll = lossE (val (vvar (S Z)))

-- R5's own "εop" (the outer opE's own effect) must equal k's own hole
-- effect, εB.
mopB : Example2.ndetA ∈ εB
mopB = here refl

v1B : Val ∅ (gnd loss)
v1B = vgnd 5

v2B : Val ∅ (gnd (out Example2.decideA))
v2B = vgnd tt

-- g reports 11 directly -- chosen so ⌊g⌋[sub,ρ] ≡ γB exactly.
gIll : LC ∅ UnitTy []
gIll = vabs (val (vgnd 11))

subIll : [] ⊆ᵉ []
subIll = ⊆ᵉ-refl

hIll' : Handler (∅ , (gnd loss `× gnd (in′ Example2.decideA))) Example2.ndetA loss UnitTy UnitTy []
hIll' = renH S hIll

gIll' : LC (∅ , (gnd loss `× gnd (in′ Example2.decideA))) UnitTy []
gIll' = renV S gIll

kB' : ContCxt (∅ , (gnd loss `× gnd (in′ Example2.decideA))) (gnd (in′ Example2.decideB)) εB UnitTy (Example2.ndetA ∷ [])
kB' = weaken1K k

handledIll : (∅ , (gnd loss `× gnd (in′ Example2.decideA))) ⊢ UnitTy ! []
handledIll = handleE hIll' (fst (val (vvar Z))) (plugK kB' (snd (val (vvar Z))))

fkIll : Val ∅ ((gnd loss `× gnd (in′ Example2.decideA)) ⇒ UnitTy ! [])
fkIll = vabs (glocalE subIll ⊆ᵉ-refl handledIll gIll')

flIll : Val ∅ ((gnd loss `× gnd (in′ Example2.decideA)) ⇒ Loss ! [])
flIll = vabs (thenE subIll handledIll gIll')

lhsIll rhsIll : Ŵ [] ⟦ UnitTy ⟧
lhsIll = Esem (handleE hIll (val v1B) (plugK k (opE mopB Example2.decideA (val v2B)))) ρB γB
rhsIll = tell 0# (Esem (subE (cons fkIll (cons flIll (cons v2B (cons v1B idSub)))) (clause hIll Example2.decideA)) ρB γB)

-- Does theorem-B9-R5 itself survive this "ill-behaved clause + leaking
-- nested handler" combination, under the FIXED handlerSem? YES -- both
-- sides now agree (leaf 7 tt), matching fresh-resultB above. (Under the
-- OLD, buggy handlerSem this was confirmed false: 23 vs 25.)
r5-ill-check : lhsIll ≡ rhsIll
r5-ill-check = refl

r5-ill-value : lhsIll ≡ leaf 7 tt
r5-ill-value = refl

-- ---------------------------------------------------------------------
-- gIll's own body is a BARE VALUE (val (vgnd 11)) -- its Vsem, at ANY
-- argument and ANY continuation, is a LEAF with root-loss EXACTLY 0#
-- (Esem(val v)ρ = η̂ˢ(Vsem v ρ), which ignores its own γ entirely). Does
-- theorem-B9-R5 still hold when g's OWN body accumulates genuine,
-- NONZERO internal loss before reporting its final value (a "fl"/l1
-- construction has to reproduce this internal accounting exactly, not
-- just g's *final* reported number) -- i.e. is the match still exact
-- when g is NOT of this trivial "root always 0#" shape?
-- g2 ignores its argument, first reports loss 7 via lossE (a
-- self-contained, already-resolved side effect -- no operations left
-- stuck), THEN returns literal value 11 as its own final Loss/R value.
-- So Vsem g2 ρ _ (λ_→η̂tt) = leaf 7 11 (root 7, payload 11) -- NONZERO
-- root, unlike gIll's leaf 0# 11.
g2Ill : LC ∅ UnitTy []
g2Ill = vabs (app (val (vabs (val (vgnd 11)))) (lossE (val (vgnd 7))))

γB2 : ⟦ UnitTy ⟧ → Ŵ [] ⊤
γB2 a = widenŴ subIll (Lsem g2Ill ρB a)

-- Sanity: ⌊g2⌋[sub,ρ] still collapses to leaf 11 tt (collapse discards
-- g's own internal root-loss unconditionally), i.e. γB2 ≡ γB -- the
-- TOP-level ambient continuation genuinely can't tell gIll and g2Ill
-- apart. Any discrepancy below must come from fl/l1's OWN internal use
-- of Vsem g ρ directly (not through collapse), inside the clause match.
γB2-same-as-γB : γB2 ≡ γB
γB2-same-as-γB = refl

g2Ill' : LC (∅ , (gnd loss `× gnd (in′ Example2.decideA))) UnitTy []
g2Ill' = renV S g2Ill

handledIll2 : (∅ , (gnd loss `× gnd (in′ Example2.decideA))) ⊢ UnitTy ! []
handledIll2 = handleE hIll' (fst (val (vvar Z))) (plugK kB' (snd (val (vvar Z))))

fkIll2 : Val ∅ ((gnd loss `× gnd (in′ Example2.decideA)) ⇒ UnitTy ! [])
fkIll2 = vabs (glocalE subIll ⊆ᵉ-refl handledIll2 g2Ill')

flIll2 : Val ∅ ((gnd loss `× gnd (in′ Example2.decideA)) ⇒ Loss ! [])
flIll2 = vabs (thenE subIll handledIll2 g2Ill')

lhsIll2 rhsIll2 : Ŵ [] ⟦ UnitTy ⟧
lhsIll2 = Esem (handleE hIll (val v1B) (plugK k (opE mopB Example2.decideA (val v2B)))) ρB γB2
rhsIll2 = tell 0# (Esem (subE (cons fkIll2 (cons flIll2 (cons v2B (cons v1B idSub)))) (clause hIll Example2.decideA)) ρB γB2)

r5-ill-check2 : lhsIll2 ≡ rhsIll2
r5-ill-check2 = refl

-- ---------------------------------------------------------------------
-- r5-ill-check(2) both use hIll, whose clause calls ONLY fk (via
-- `vvar Z`), never fl (`vvar (S Z)`) -- so neither test actually
-- exercises fl's own construction against l1v at all, only fk-match's
-- (already unconditionally proven) k1v-side. A clause that LEAKS its own
-- fl(p'',a)'s reported loss (PLeakCheck2/hLeak2's own pattern) is needed
-- to test the l1v/fl side directly. Combined with g2Ill (a g whose OWN
-- body accumulates genuine, nonzero internal loss via lossE before
-- reporting its final value -- unlike gIll/g2Ill's shared top-level
-- report of 11, which collapse makes indistinguishable at the OUTER
-- ambient γ) this tests whether fl's construction matches l1v even when
-- g's own internal accounting is nontrivial.
hLeakIll : Handler ∅ Example2.ndetA loss UnitTy UnitTy []
clause hLeakIll Example2.decideA =
  snd (pair (lossE (app (val (vvar (S Z))) (pair (val (vgnd 7)) (val (vgnd true)))))
            (app (val (vvar Z)) (pair (val (vgnd 7)) (val (vgnd true)))))
ret hLeakIll = lossE (val (vvar (S Z)))

hLeakIll' : Handler (∅ , (gnd loss `× gnd (in′ Example2.decideA))) Example2.ndetA loss UnitTy UnitTy []
hLeakIll' = renH S hLeakIll

handledLeakIll : (∅ , (gnd loss `× gnd (in′ Example2.decideA))) ⊢ UnitTy ! []
handledLeakIll = handleE hLeakIll' (fst (val (vvar Z))) (plugK kB' (snd (val (vvar Z))))

fkLeakIll : Val ∅ ((gnd loss `× gnd (in′ Example2.decideA)) ⇒ UnitTy ! [])
fkLeakIll = vabs (glocalE subIll ⊆ᵉ-refl handledLeakIll gIll')

flLeakIll : Val ∅ ((gnd loss `× gnd (in′ Example2.decideA)) ⇒ Loss ! [])
flLeakIll = vabs (thenE subIll handledLeakIll gIll')

-- Sanity first, with the TRIVIAL gIll (root always 0#) -- should still
-- match, consistent with everything checked so far.
lhsLeak rhsLeak : Ŵ [] ⟦ UnitTy ⟧
lhsLeak = Esem (handleE hLeakIll (val v1B) (plugK k (opE mopB Example2.decideA (val v2B)))) ρB γB
rhsLeak = tell 0# (Esem (subE (cons fkLeakIll (cons flLeakIll (cons v2B (cons v1B idSub)))) (clause hLeakIll Example2.decideA)) ρB γB)

r5-leak-check : lhsLeak ≡ rhsLeak
r5-leak-check = refl

-- Now with g2Ill (NONTRIVIAL internal root-loss = 7, same final report
-- 11 as gIll) -- does the leaking clause's fl-side match survive?
fkLeakIll2 : Val ∅ ((gnd loss `× gnd (in′ Example2.decideA)) ⇒ UnitTy ! [])
fkLeakIll2 = vabs (glocalE subIll ⊆ᵉ-refl handledLeakIll g2Ill')

flLeakIll2 : Val ∅ ((gnd loss `× gnd (in′ Example2.decideA)) ⇒ Loss ! [])
flLeakIll2 = vabs (thenE subIll handledLeakIll g2Ill')

lhsLeak2 rhsLeak2 : Ŵ [] ⟦ UnitTy ⟧
lhsLeak2 = Esem (handleE hLeakIll (val v1B) (plugK k (opE mopB Example2.decideA (val v2B)))) ρB γB2
rhsLeak2 = tell 0# (Esem (subE (cons fkLeakIll2 (cons flLeakIll2 (cons v2B (cons v1B idSub)))) (clause hLeakIll Example2.decideA)) ρB γB2)

-- Still fails, exactly as it must: g2Ill is built via `app` directly,
-- NOT via the thenE/glocalE-wrapping theorem-B9's own induction actually
-- uses to rebuild g -- so it genuinely lacks RootZero, and Proofs.agda's
-- theorem-B9-R5-WF (the now fully PROVEN, postulate-free version of this
-- theorem, taking an explicit RootZero(g) hypothesis) correctly excludes
-- it. This is no longer an open mystery -- see gWF/r5-leak-checkWF below
-- for the SAME clause combined with a g that IS RootZero (built the way
-- the real induction builds one), which now holds by refl, matching
-- theorem-B9-R5-WF exactly.
-- r5-leak-check2 : lhsLeak2 ≡ rhsLeak2
-- r5-leak-check2 = refl  -- FAILS: 25 != 32 (expected: g2Ill lacks RootZero)

-- CONFIRMED, SECOND, DISTINCT bug (present even after the handlerSem
-- fix): lhsLeak2 is UNCHANGED from lhsLeak (25 either way) -- the direct
-- (handleE-based) evaluation only ever consults g THROUGH the collapsed
-- ambient γB2, which (since `collapse` unconditionally discards a Ŵ ε R
-- tree's own root field, see Denotational.agda) is IDENTICAL to γB
-- regardless of g's internal accounting (γB2-same-as-γB above). But
-- rhsLeak2 = 32 = 25 + 7, i.e. R5's own `fl := (...)▶g` (thenE-based)
-- reification picks up an EXTRA +7, EXACTLY g2Ill's own internal
-- root-loss (7, from its internal `lossE(val(vgnd7))`) -- because
-- Esem(thenE...)'s final combine step (mapŴ(r1+_) applied to the RAW,
-- un-collapsed `Vsem g ρ a(λ_→η̂tt)`) genuinely re-runs g and folds in
-- g's OWN real report, whereas l1v (Denotational.agda's handlerΨ "yes"
-- branch, matching the paper's own §5.3 formula l1(p,a)=λγ1.δ_ε(γ†Ŵε
-- (kap))) only ever consults the ALREADY-COLLAPSED outer γ, never g's
-- raw internal loss at all. These are genuinely different quantities
-- whenever g has nonzero internal accounting -- unlike the `fk`/k1v side
-- (fk-match, proven unconditionally), R5's `fl` construction does NOT
-- faithfully reify l1v in general. This is a DISTINCT issue from the
-- paper's own documented erratum (paper.tex §"An Error in the Original
-- Appendix B.4", about the necessity of fk's ⟨·⟩ᵍ wrapper specifically)
-- -- that erratum is about fk/k1v only and does not address fl/l1v.
lhsLeak2-probe : lhsLeak2 ≡ leaf 25 tt
lhsLeak2-probe = refl

rhsLeak2-probe : rhsLeak2 ≡ leaf 32 tt
rhsLeak2-probe = refl

lhsLeak-value : lhsLeak ≡ leaf 25 tt
lhsLeak-value = refl

-- ---------------------------------------------------------------------
-- Does the discrepancy require g to be a genuinely ARBITRARY expression
-- (g2Ill was built via `app`, which Esem/thenE's own "real semantics"
-- never actually produces for the ambient loss continuation), or does it
-- survive even for a g built the ONLY way theorem-B9's own induction
-- ever builds one -- by repeatedly wrapping zeroLC via thenE/glocalE
-- (OpSem.agda's S1/F/S2/R7 rules all construct their "new g" hypothesis
-- this way, never via `app`/handleE/opE directly)?
--
-- gWF ("well-formed"): built via thenE from zeroLC, exactly matching the
-- SHAPE retApplied/S1 produces (e1 = lossE(val(vgnd7)), a NONTRIVIAL
-- internal loss report, THEN sequenced with zeroLC). By hand: Esem e1's
-- own leaf is `leaf 7 tt` (root=7); but thenE's OWN combine step folds
-- e1's root into collectX's SECOND component (r1), then mapŴ(r1+_)
-- bumps only the FINAL LEAF's PAYLOAD (never the root) -- so
-- Vsem gWF ρ x (λ_→η̂tt) = leaf 0# 7: ROOT IS 0#, regardless of e1's own
-- internal lossE report. (Confirmed below, gWF-root-zero.)
gWF : LC ∅ UnitTy []
gWF = vabs (thenE ⊆ᵉ-refl (lossE (val (vgnd 7))) zeroLC)

gWF-root-zero : Vsem gWF ρB tt (λ _ → η̂ tt) ≡ leaf 0# 7
gWF-root-zero = refl

γBWF : ⟦ UnitTy ⟧ → Ŵ [] ⊤
γBWF a = widenŴ subIll (Lsem gWF ρB a)

-- ⌊gWF⌋ reports 7 (gWF's own payload, matching gIll/g2Ill's shared 11 in
-- shape but a different concrete number here) -- NOT the same as γB, but
-- that is expected and irrelevant; what matters is whether lhs/rhs still
-- AGREE with EACH OTHER for this g, the way they did for gIll/g2Ill's
-- shared top-level report.
gWF' : LC (∅ , (gnd loss `× gnd (in′ Example2.decideA))) UnitTy []
gWF' = renV S gWF

fkLeakWF : Val ∅ ((gnd loss `× gnd (in′ Example2.decideA)) ⇒ UnitTy ! [])
fkLeakWF = vabs (glocalE subIll ⊆ᵉ-refl handledLeakIll gWF')

flLeakWF : Val ∅ ((gnd loss `× gnd (in′ Example2.decideA)) ⇒ Loss ! [])
flLeakWF = vabs (thenE subIll handledLeakIll gWF')

lhsLeakWF rhsLeakWF : Ŵ [] ⟦ UnitTy ⟧
lhsLeakWF = Esem (handleE hLeakIll (val v1B) (plugK k (opE mopB Example2.decideA (val v2B)))) ρB γBWF
rhsLeakWF = tell 0# (Esem (subE (cons fkLeakWF (cons flLeakWF (cons v2B (cons v1B idSub)))) (clause hLeakIll Example2.decideA)) ρB γBWF)

-- Does the "leaking" clause survive against a g of the REAL, induction-
-- produced shape, even though its body still directly contains a
-- nontrivial internal lossE report (7)?
r5-leak-checkWF : lhsLeakWF ≡ rhsLeakWF
r5-leak-checkWF = refl
