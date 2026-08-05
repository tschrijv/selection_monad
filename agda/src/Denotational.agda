-- The denotational semantics of expressions and handlers (paper.tex §4-5:
-- the "hat" redo of Fig. 9/10 and the handler formula, in terms of the
-- Ŵ_ε/Ŝ_ε construction from Domains.agda) for the core fragment of
-- Syntax.agda.
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
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ---------------------------------------------------------------------
-- Environments.
-- ---------------------------------------------------------------------

Env : Cxt → Set
Env Γ = ∀ {σ} → Γ ∋ σ → ⟦ σ ⟧

_,,_ : ∀ {Γ σ} → Env Γ → ⟦ σ ⟧ → Env (Γ , σ)
(ρ ,, a) Z     = a
(ρ ,, a) (S x) = ρ x

-- ---------------------------------------------------------------------
-- Fig. 10 (unchanged by the swap): semantics of values.
-- ---------------------------------------------------------------------

mutual
  Vsem : ∀ {Γ σ} → Val Γ σ → Env Γ → ⟦ σ ⟧
  Vsem (vvar x)    ρ = ρ x
  Vsem (vgnd x)    ρ = x
  Vsem (vpair v w) ρ = Vsem v ρ , Vsem w ρ
  Vsem (vabs e)    ρ = λ a → Esem e (ρ ,, a)

  -- §4's auxiliary loss-function semantics ℒ, stated generically for any
  -- (semantic value of a) loss continuation g : σ → loss ! ε, not just a
  -- syntactic λ-abstraction -- matching how the source states it.
  Lsem : ∀ {Γ σ ε} → LC Γ σ ε → Env Γ → ⟦ σ ⟧ → R̂ ε
  -- γ0, the canonical "zero" continuation at any type, inlined at each use
  -- site (see the note at Esem's loss/then clauses below for why: the
  -- source reuses whatever continuation is ambient even where the type
  -- doesn't literally match, e.g. loss(e)'s "Ssem(e)(ρ)(γ)" against a
  -- γ:Unit→Ŵε(Unit) when e:loss!ε needs Ŝε(R); we read every such reuse as
  -- this canonical zero continuation at the type actually needed).
  Lsem g ρ a =  Vsem g ρ a (λ _ → η̂ 0#)

  -- ---------------------------------------------------------------------
  -- Fig. 9 (hat-version, §4): semantics of expressions.
  -- ---------------------------------------------------------------------

  Esem : ∀ {Γ σ ε} → Γ ⊢ σ ! ε → Env Γ → Ŝ ε ⟦ σ ⟧
  Esem (val v) ρ          = η̂ˢ (Vsem v ρ)
  Esem (fun f e) ρ        = bind̂ˢ (λ a → η̂ˢ (⟦ f ⟧f a)) (Esem e ρ)
  Esem (pair e1 e2) ρ     = bind̂ˢ (λ a → bind̂ˢ (λ b → η̂ˢ (a , b)) (Esem e2 ρ)) (Esem e1 ρ)
  Esem (fst e) ρ          = bind̂ˢ (λ{ (a , b) → η̂ˢ a }) (Esem e ρ)
  Esem (snd e) ρ          = bind̂ˢ (λ{ (a , b) → η̂ˢ b }) (Esem e ρ)
  Esem (app e1 e2) ρ      = bind̂ˢ (λ φ → bind̂ˢ (λ a → φ a) (Esem e2 ρ)) (Esem e1 ρ)
  Esem (opE m op e) ρ     = bind̂ˢ (λ a → φ̂ˢ m op a η̂ˢ) (Esem e ρ)
  Esem (lossE e) ρ        = λ γ → bind̂ (Esem e ρ (λ a → γ tt)) (λ a → tell a (η̂ tt))

  -- Ssem(e1 ▶ g)(ρ)(γ) = let (a,r1) be collectX(Ssem e1 ρ (Lsem g ρ)) in
  --                       let (r3,r2) be collectX(Vsem g ρ a γ0) in
  --                       tell r2 (η(r1+r3))
  -- (constant in γ, matching "▶ disregards g"). Lsem g ρ has codomain
  -- R̂_{εg} for g's own (possibly smaller) effect; e1 needs a continuation
  -- into R̂_ε -- another of the sub-effecting inclusions §5 calls "left
  -- implicit", made explicit here via widenŴ along THEN's own `sub`.
  -- EXPERIMENTAL VARIANT (see B5Core.agda/R7Counterexample.hs writeup):
  -- g's own report is now combined via a plain mapŴ bump instead of a
  -- second collectX+bind̂+tell cycle -- the latter redistributes g's own
  -- accumulated root-loss down past any stuck operation it reaches,
  -- which is exactly what broke theorem-B9-R7. mapŴ preserves g's own
  -- Ŵ-shape (including any stuck node) untouched, only bumping the
  -- eventual leaf value by r1.
  Esem (thenE sub e1 g) ρ = λ γ →
    bind̂ (collectX (Esem e1 ρ (λ a → widenŴ sub (Lsem g ρ a)))) (λ{ (a , r1) →
    mapŴ (r1 +_) (widenŴ sub (Vsem g ρ a (λ _ → η̂ 0#))) })

  -- Ssem(⟨e⟩^ε₁_g)(ρ)(γ) = Ssem e ρ (Lsem g ρ); two implicit widenings
  -- here -- one for Lsem g ρ along GLOCAL's ε₂⊆ε₁ (`sub1`), and one for
  -- the overall result along ε₁⊆ε (`sub2`), since e's evaluation lives at
  -- its own ε₁ but the whole ⟨e⟩^ε₁_g expression is declared at ε.
  Esem (glocalE sub1 sub2 e g) ρ = λ γ → widenŴ sub2 (Esem e ρ (λ a → widenŴ sub1 (Lsem g ρ a)))
  Esem (resetE e) ρ              = λ γ → censor (Esem e ρ γ)
  Esem (handleE h e1 e2) ρ       = bind̂ˢ (λ p → handlerSem h ρ p (Esem e2 ρ)) (Esem e1 ρ)

  -- ---------------------------------------------------------------------
  -- §5 (hat-version): semantics of handlers. Fix ρ and (implicitly, via
  -- the final γ argument) the ambient loss continuation, and build the
  -- layered ε ℓ-algebra on A = Ŵ_ε(⟦σ'⟧)^⟦par⟧ (over ε, *not* εℓ -- the
  -- one place the swap strictly simplifies the original, since the writer
  -- layer is already threaded by Ŵ itself, needing no separate R× pairing).
  -- ---------------------------------------------------------------------

  -- s(a) = λp. Ssem(er)(ρ[(p,a)/z])(γ)   (no ×R needed, cf. the swap).
  -- Top-level (not handlerSem-local) so Proofs.agda can name it directly.
  handlerRet : ∀ {Γ ℓ par σ σ' ε} → Handler Γ ℓ par σ σ' ε → Env Γ → (⟦ σ' ⟧ → Ŵ ε R) → ⟦ σ ⟧ → ⟦ gnd par ⟧ → Ŵ ε ⟦ σ' ⟧
  handlerRet h ρ γ a p' = Esem (ret h) ((ρ ,, p') ,, a) γ

  -- ℓ1 ≠ ℓ rules out m pointing at the freshly-appended slot of (ε ,ℓ ℓ)
  -- (the only element there IS ℓ), so ∈-++⁻ is forced into its inj₁ case.
  -- Top-level (not a handlerΨ-local `where`) so that Proofs.agda's own
  -- coherence proofs (renH-coh/subH-coh's ψEq) can name EXACTLY the same
  -- term handlerΨ itself uses on both sides of an equation, rather than
  -- two `where`-local reconstructions that close over different (though
  -- ultimately irrelevant) outer arguments and so aren't syntactically
  -- the same term to Agda's unifier.
  demoteMem : ∀ {ℓ ℓ1 ε} → ℓ1 ∈ (ε ,ℓ ℓ) → ¬ (ℓ1 ≡ ℓ) → ℓ1 ∈ ε
  demoteMem {ε = ε} m neq with ∈-++⁻ ε m
  ... | inj₁ x          = x
  ... | inj₂ (here eq)  = ⊥-elim (neq eq)
  ... | inj₂ (there ())

  -- ψ dispatches SOLELY on whether ℓ1 (the stuck operation's own label) is
  -- h's own label ℓ -- NOT on which specific witness m : ℓ1 ∈ (ε ,ℓ ℓ) was
  -- supplied. EffCxt is an explicit multiset (Domains.agda's own comment
  -- on `_,ℓ_`: nested handlers for the SAME label are intentional), so
  -- ℓ ∈ (ε ,ℓ ℓ) can have several, position-distinct witnesses when ε
  -- already contains ℓ -- dispatching on the WITNESS's position (the
  -- original `∈-++⁻ ε m` split) let two different, otherwise-identical
  -- derivations disagree on whether THIS handler catches the operation,
  -- which is exactly what made theorem-B9-R5-gen false (B5Core.agda's
  -- r5-lhs-old/r5-lhs-new counterexample). OpSem.agda's own (R5) step-
  -- relation rule never inspected m's structure either -- only `¬ Handles
  -- k ℓ`, itself already witness-independent -- so this brings the
  -- denotational semantics back in line with the (already correct)
  -- operational one, exactly as the mapŴ fix did for (R7).
  handlerΨ : ∀ {Γ ℓ par σ σ' ε} → Handler Γ ℓ par σ σ' ε → Env Γ → (⟦ σ' ⟧ → Ŵ ε R)
           → ∀ {ℓ1} → ℓ1 ∈ (ε ,ℓ ℓ) → (op : Op ℓ1) → ⟦ out op ⟧ᴳ → (⟦ in′ op ⟧ᴳ → (⟦ gnd par ⟧ → Ŵ ε ⟦ σ' ⟧)) → (⟦ gnd par ⟧ → Ŵ ε ⟦ σ' ⟧)
  handlerΨ {ℓ = ℓ} {par = par} {σ' = σ'} {ε = ε} h ρ γ {ℓ1} m op o k with ℓ1 ≟ᵉ ℓ
  ... | yes eq with eq
  ...   | refl = λ p' →
      Esem (clause h op) ((((ρ ,, p') ,, o) ,, l1v) ,, k1v) γ
    where
    -- the choice continuation l1(p,a) = λγ1. δ_ε(γ†Ŵε(k(a)(p))), ignoring
    -- its own γ1 (matching Haskell's `hoist`). δ_ε read via `collectX`
    -- (mapŴ π₂ ∘ collectX), not `collect`: `collect` PRESERVES a stuck
    -- node's own root untouched while `collapse` (used to build the
    -- ambient γ, in Lsem) ZEROES it unconditionally, so a stuck
    -- operation inside the ambient loss continuation g would have its
    -- own recorded loss silently discarded by `collect` but correctly
    -- REDISTRIBUTED down to g's own eventual leaves by `collectX` (via
    -- `bump`) -- exactly the mapŴ/collectX-vs-naive-tell distinction
    -- that (R7) already needed fixing for. See Proofs.agda's
    -- RootZero-collect-via-collectX / lemma-fl-l1v-match, and the
    -- "FIFTH FINDING" comment above theorem-B9-R5-gen's postulate.
    l1v : ⟦ gnd par `× gnd (in′ op) ⟧ → Ŝ ε R
    l1v (p'' , a) γ1 = mapŴ (λ { (_ , r1) → r1 }) (collectX (ext̂ Ŵ-alg γ (k a p'')))
    -- the delimited continuation k1(p,a) = k(a)(p), likewise promoted to
    -- a (γ-independent) selection function.
    k1v : ⟦ gnd par `× gnd (in′ op) ⟧ → Ŝ ε ⟦ σ' ⟧
    k1v (p'' , a) γ' = k a p''
  handlerΨ {ℓ = ℓ} {ε = ε} h ρ γ {ℓ1} m op o k | no neq = λ p' → node (demoteMem m neq) op 0# o (λ a → k a p')

  -- handlerΨ's own "no" branch, exposed as a standalone equation so
  -- CALLERS can invoke it directly rather than relying on Agda unifying
  -- their own, separately-elaborated `ℓ1 ≟ᵉ ℓ` match against handlerΨ's
  -- internal one (which it won't -- two `with`-clauses on the same
  -- computation, in different functions, don't share their reduction).
  -- Well-typed for ANY proof neq : ¬(ℓ1≡ℓ), not just the one handlerΨ's
  -- own internal match happens to produce, since demoteMem's own value
  -- never actually depends on WHICH proof of the negation it's given
  -- (only the impossible ⊥-elim branch mentions it at all).
  handlerΨ-no-eq : ∀ {Γ ℓ1 par σ σ' ε ℓ} (h : Handler Γ ℓ par σ σ' ε) (ρ : Env Γ) (γ : ⟦ σ' ⟧ → Ŵ ε R)
                 (m : ℓ1 ∈ (ε ,ℓ ℓ)) (neq : ¬ (ℓ1 ≡ ℓ)) (op : Op ℓ1) (o : ⟦ out op ⟧ᴳ) (k : ⟦ in′ op ⟧ᴳ → (⟦ gnd par ⟧ → Ŵ ε ⟦ σ' ⟧))
               → handlerΨ h ρ γ m op o k ≡ (λ p' → node (demoteMem m neq) op 0# o (λ a → k a p'))
  handlerΨ-no-eq {ℓ1 = ℓ1} {ℓ = ℓ} h ρ γ m neq op o k with ℓ1 ≟ᵉ ℓ
  ... | yes eq   = ⊥-elim (neq eq)
  ... | no neq'  = refl

  -- The symmetric "yes" case -- used at theorem-B9-R5-gen, where the
  -- operation's own label IS h's own label (op : Op ℓ, h : Handler _ ℓ
  -- _ _ _ _, matching exactly), so handlerΨ's dispatch always takes this
  -- branch, unconditionally, regardless of which witness m was supplied
  -- -- exactly the fix's point.
  handlerΨ-yes-eq : ∀ {Γ ℓ par σ σ' ε} (h : Handler Γ ℓ par σ σ' ε) (ρ : Env Γ) (γ : ⟦ σ' ⟧ → Ŵ ε R)
                  (m : ℓ ∈ (ε ,ℓ ℓ)) (op : Op ℓ) (o : ⟦ out op ⟧ᴳ) (k : ⟦ in′ op ⟧ᴳ → (⟦ gnd par ⟧ → Ŵ ε ⟦ σ' ⟧))
                → handlerΨ h ρ γ m op o k
                ≡ (λ p' → Esem (clause h op) ((((ρ ,, p') ,, o) ,, (λ{ (p'' , a) γ1 → mapŴ (λ { (_ , r1) → r1 }) (collectX (ext̂ Ŵ-alg γ (k a p''))) })) ,, (λ{ (p'' , a) γ' → k a p'' })) γ)
  handlerΨ-yes-eq {ℓ = ℓ} h ρ γ m op o k with ℓ ≟ᵉ ℓ
  handlerΨ-yes-eq {ℓ = ℓ} h ρ γ m op o k | yes eq with eq
  handlerΨ-yes-eq {ℓ = ℓ} h ρ γ m op o k | yes eq | refl = refl
  handlerΨ-yes-eq {ℓ = ℓ} h ρ γ m op o k | no neq = ⊥-elim (neq refl)

  handlerAlg : ∀ {Γ ℓ par σ σ' ε} → Handler Γ ℓ par σ σ' ε → Env Γ → (⟦ σ' ⟧ → Ŵ ε R) → LayeredAlg (ε ,ℓ ℓ) (⟦ gnd par ⟧ → Ŵ ε ⟦ σ' ⟧)
  handlerAlg h ρ γ = record { ψ = handlerΨ h ρ γ ; act = λ r f p' → tell r (f p') }

  -- CORRECTED (see paper.tex §5.3): G is fed the CANONICAL ZERO
  -- continuation (the same (λ_→η̂tt) pattern Lsem/etc. already use
  -- elsewhere in this file), NOT a continuation with the outer p baked
  -- in. ext̂'s own leaf case already applies handlerRet h ρ γ (as the
  -- homomorphism's own leaf-function) AT WHATEVER VALUE G's tree
  -- produces, giving an A-valued (⟦gndpar⟧→Ŵε⟦σ'⟧) result that's
  -- threaded generically through act -- exactly matching the paper's
  -- own algebra carrier A = W_ε(S[[σ']])^{S[[par]]}, resolved only at
  -- the FINAL `p` application here, not baked in early. The PREVIOUS
  -- version built a separate "D" continuation using the outer p ahead
  -- of time, which is what B5Core2.agda's counterexamples exploited
  -- (an outer handler resuming its own delimited continuation at a
  -- DIFFERENT parameter than its own bound one, combined with a nested
  -- handler leaking its own choice-continuation's value) -- a porting
  -- bug against the paper's own construction, not a bug in the paper.
  handlerSem : ∀ {Γ ℓ par σ σ' ε} → Handler Γ ℓ par σ σ' ε → Env Γ → ⟦ gnd par ⟧ → Ŝ (ε ,ℓ ℓ) ⟦ σ ⟧ → Ŝ ε ⟦ σ' ⟧
  handlerSem h ρ p G γ =
    ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (G (λ _ → η̂ 0#)) p
