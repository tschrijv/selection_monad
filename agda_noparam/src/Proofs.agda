-- Porting paper.tex §7 ("Porting Appendix B: Correctness Proofs") to the
-- Agda encoding, lemma by lemma, in the source's own order. Each lemma
-- below is labelled with its name in paper.tex (which is itself "hat-Lemma
-- B.n" of the arXiv paper's Appendix B) so the two can be read side by
-- side.
open import Domains using (Sig)
import Domains

module Proofs (Sg : Sig) where

open Sig Sg
open Domains.ŴMonad Sg
open Domains.ŜMonad Sg
open import Syntax Sg
open import Subst Sg
open import OpSem Sg
open import Denotational Sg

open import Data.List using (_∷_; [])
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Nullary using (¬_; yes; no; Dec)

-- ---------------------------------------------------------------------
-- Lemma A.1 / B.1 (Substitution).
-- "Suppose Γ⊢v:σ and Γ,x:σ⊢e:τ!ε. Then Γ⊢e[v/x]:τ!ε."
--
-- This is a *typing* fact, and with intrinsically typed & scoped syntax it
-- is not a lemma to prove at all: `_[_] : (Γ,σ)⊢τ!ε → Val Γ σ → Γ⊢τ!ε`
-- (Subst.agda) already has exactly this type, so every substitution
-- instance is well-typed by construction. We record the operation itself
-- as the "proof".
-- ---------------------------------------------------------------------

lemma-B1 : ∀ {Γ σ τ ε} → Val Γ σ → (Γ , σ) ⊢ τ ! ε → Γ ⊢ τ ! ε
lemma-B1 v e = e [ v ]

-- ---------------------------------------------------------------------
-- Lemma 7.2 (hat-Lemma B.2): values denote units.
-- "For any value Γ⊢v:σ!ε: Ssem(v)(ρ) = η^Ŝε(Vsem(v)(ρ))."
--
-- In the source, this is proved by structural induction on v (Lemma B.2 of
-- the appendix), one case per value form. Here it is *definitional*: our
-- architecture routes every value through a single `val` embedding, and
-- Esem's very first clause is `Esem (val v) ρ = η̂ˢ (Vsem v ρ)` -- so the
-- induction on v's shape that the original proof performs is absorbed into
-- Vsem's own (likewise structural) definition instead, and this lemma
-- becomes reflexivity.
-- ---------------------------------------------------------------------

lemma-B2 : ∀ {Γ σ ε} (v : Val Γ σ) (ρ : Env Γ) → Esem {ε = ε} (val v) ρ ≡ η̂ˢ (Vsem v ρ)
lemma-B2 v ρ = refl

-- ---------------------------------------------------------------------
-- Lemma 7.3 (hat-Lemma B.3): the action law simplifies.
--
-- Consider A = P → Ŵ_ε(Y) for an arbitrary index type P, the shape a
-- layered εℓ-algebra's carrier takes whenever its action is "tell,
-- applied pointwise": act r f = λp. tell r (f p). (In this parameter-
-- free development handlerAlg's own carrier is just Ŵ_ε(⟦σ'⟧) directly,
-- P-free, with act = tell outright -- handlerAlg-tell-comm below proves
-- the analogous fact for THAT shape directly, mirroring Ŵ-alg's own
-- tell-bind̂-comm; this lemma is kept as the general P-indexed statement,
-- standalone.) The lemma is: s†Ŵεℓ ∘ tell(r) = tell(r)^P ∘ s†Ŵεℓ, i.e.
-- extending any s : X → A over a tell(r)-prefixed tree agrees with
-- tell(r)ing the result pointwise. The source's proof of the analogous
-- (original) fact needs a
-- uniqueness-of-extension argument, because there r·(-) acts on every leaf
-- of F_ε(R×X) simultaneously and one must invoke commutativity of the
-- action with ψ; here tell only ever touches the *root* loss slot, so the
-- fact is immediate from tell's own additivity (Domains.ŴMonad's tell-+,
-- opened above), with no commutation needed anywhere -- exactly as the
-- source remarks.
-- ---------------------------------------------------------------------

-- The "pointwise tell" layered algebra pattern used by handlerSem's own
-- `algebra` -- extracted so Lemma 7.3 can be stated and proved once,
-- generically, rather than only inline inside Denotational.agda.
pointwiseTellAlg : ∀ {ε P Y}
  → (∀ {ℓ1} → ℓ1 ∈ ε → (op : Op ℓ1) → ⟦ out op ⟧ᴳ → (⟦ in′ op ⟧ᴳ → (P → Ŵ ε Y)) → (P → Ŵ ε Y))
  → LayeredAlg ε (P → Ŵ ε Y)
pointwiseTellAlg ψ' = record { ψ = ψ' ; act = λ r f p → tell r (f p) }

lemma-B3 : ∀ {ε P Y X} (ψ' : ∀ {ℓ1} → ℓ1 ∈ ε → (op : Op ℓ1) → ⟦ out op ⟧ᴳ → (⟦ in′ op ⟧ᴳ → (P → Ŵ ε Y)) → (P → Ŵ ε Y))
           (s : X → P → Ŵ ε Y) (r : R) (w : Ŵ ε X) (p : P)
         → ext̂ (pointwiseTellAlg ψ') s (tell r w) p ≡ tell r (ext̂ (pointwiseTellAlg ψ') s w p)
lemma-B3 ψ' s r (leaf r₀ x) p        = tell-+ r r₀ (s x p)
lemma-B3 ψ' s r (node m op r₀ o κ) p = tell-+ r r₀ (ψ' m op o (λ a → ext̂ (pointwiseTellAlg ψ') s (κ a)) p)

-- Ŝ's monad laws (bindˢ-unitˡ, bindˢ-unitʳ, bindˢ-assoc) now live in
-- Domains.ŜMonad, opened above. bindˢ-unitˡ is what Lemma B.4's proof
-- below invokes ("the unit law for let_Sε").

-- ---------------------------------------------------------------------
-- bump/collectX algebra, needed later for Theorem B.9's THEN case (S2).
-- bump-fusion/bump-collectX-comm/bump-shift/bump-0/tell-mapŴ-comm/
-- mapŴ-∘/bind̂-mapŴ-after/collectX-bind̂-fusion(-gen) now live in
-- Domains.ŴMonad, opened above (moved there since bindˢ-assoc needs them
-- too, now that R̂-of routes through collectX/mapŴ).
-- ---------------------------------------------------------------------

-- RootZero: a Ŵ-tree never has any nonzero "tell"-accumulated loss
-- sitting in a root/node-r field -- only mapŴ-style leaf-payload bumps
-- are allowed to carry information (used below by Lemma 7.5/B.5(2)'s
-- RootZero hypothesis, and by theorem-B9-R5-WF further down).
RootZero : ∀ {ε X} → Ŵ ε X → Set
RootZero (leaf r x)        = r ≡ 0#
RootZero (node m op r o κ) = (r ≡ 0#) × (∀ a → RootZero (κ a))

-- widenŴ only ever relabels a node's own membership witness -- it never
-- touches any r field at all, at leaves or nodes.
RootZero-widenŴ : ∀ {ε ε' X} (sub : ε ⊆ᵉ ε') (W : Ŵ ε X) → RootZero W → RootZero (widenŴ sub W)
RootZero-widenŴ sub (leaf r x)        rz = rz
RootZero-widenŴ sub (node m op r o κ) (rz , rzκ) = rz , (λ a → RootZero-widenŴ sub (κ a) (rzκ a))

-- mapŴ only ever touches the final leaf payload -- root/node-r fields
-- are carried through completely unchanged.
RootZero-mapŴ : ∀ {ε X Y} (f : X → Y) (W : Ŵ ε X) → RootZero W → RootZero (mapŴ f W)
RootZero-mapŴ f (leaf r x)        rz = rz
RootZero-mapŴ f (node m op r o κ) (rz , rzκ) = rz , (λ a → RootZero-mapŴ f (κ a) (rzκ a))

-- collectX unconditionally zeroes every root/node-r field along the way
-- (redistributing what it finds into the paired R component instead) --
-- so its own output ALWAYS has RootZero, regardless of the input.
RootZero-collectX : ∀ {ε X} (T : Ŵ ε X) → RootZero (collectX T)
RootZero-collectX (leaf r x)        = refl
RootZero-collectX (node m op r o κ) = refl , (λ a → RootZero-bump r (collectX (κ a)) (RootZero-collectX (κ a)))
  where
  -- bump only ever touches the PAIRED R component, never a root/node-r
  -- field, so it preserves RootZero unconditionally too.
  RootZero-bump : ∀ {ε X} (s : R) (D : Ŵ ε (X × R)) → RootZero D → RootZero (bump s D)
  RootZero-bump s (leaf r (x , y))        rz = rz
  RootZero-bump s (node m op r o κ') (rz , rzκ) = rz , (λ a → RootZero-bump s (κ' a) (rzκ a))

-- The homomorphic extension of a RootZero tree, over any leaf-function
-- that itself only ever produces RootZero results, is RootZero -- act's
-- own "tell r" at each level is applied at r≡0# (from D's own RootZero),
-- so it never actually adds anything (tell-0), leaving whatever RootZero
-- structure ψ/f already produced untouched.
RootZero-bind̂ : ∀ {ε X Y} (D : Ŵ ε X) (F : X → Ŵ ε Y)
              → RootZero D → (∀ x → RootZero (F x)) → RootZero (bind̂ D F)
RootZero-bind̂ (leaf r x) F rz rzF = subst RootZero (sym eq) (rzF x)
  where
  eq : tell r (F x) ≡ F x
  eq = trans (cong (λ z → tell z (F x)) rz) (tell-0 (F x))
RootZero-bind̂ (node m op r o κ) F (rz , rzκ) rzF = subst RootZero (sym eq) rzNode
  where
  κ'' : _ → _
  κ'' = λ a → bind̂ (κ a) F
  eq : tell r (node m op 0# o κ'') ≡ node m op 0# o κ''
  eq = trans (cong (λ z → tell z (node m op 0# o κ'')) rz) (tell-0 (node m op 0# o κ''))
  rzNode : RootZero (node m op 0# o κ'')
  rzNode = refl , (λ a → RootZero-bind̂ (κ a) F (rzκ a) rzF)

-- theorem-B9's own induction NEVER builds a "new" ambient loss
-- continuation except via (F-rule)/(S1), both of which construct exactly
-- vabs(thenE sub e (weaken1V g)) for some e. This lemma shows that
-- construction ALWAYS yields a RootZero result, for ANY e whatsoever
-- (even one that reports nonzero loss via lossE, e.g. retApplied h v
-- when h's own ret uses lossE, the ordinary and expected case) --
-- PROVIDED the tail g already has RootZero at every value it's applied
-- to.
RootZero-thenE-wrap : ∀ {Γ σ α ε₁ ε} (sub : ε₁ ⊆ᵉ ε) (e1 : (Γ , σ) ⊢ α ! ε) (g' : LC (Γ , σ) α ε₁)
                    (ρ : Env Γ) (x : ⟦ σ ⟧) (γ0 : ⟦ Loss ⟧ → Ŵ ε R)
                  → (∀ a → RootZero (Vsem g' (ρ ,, x) a (λ _ → η̂ 0#)))
                  → RootZero (Vsem (vabs (thenE sub e1 g')) ρ x γ0)
RootZero-thenE-wrap {ε = ε} sub e1 g' ρ x γ0 rzg' =
  RootZero-bind̂ (collectX (Esem e1 (ρ ,, x) (λ a → widenŴ sub (Lsem g' (ρ ,, x) a))))
                      (λ { (a , r1) → mapŴ (r1 +_) (widenŴ sub (Vsem g' (ρ ,, x) a (λ _ → η̂ 0#))) })
                      (RootZero-collectX (Esem e1 (ρ ,, x) (λ a → widenŴ sub (Lsem g' (ρ ,, x) a))))
                      (λ { (a , r1) → RootZero-mapŴ (r1 +_) (widenŴ sub (Vsem g' (ρ ,, x) a (λ _ → η̂ 0#)))
                                        (RootZero-widenŴ sub (Vsem g' (ρ ,, x) a (λ _ → η̂ 0#)) (rzg' a)) })

-- ---------------------------------------------------------------------
-- Lemma 7.4 (hat-Lemma B.4): pairing and application.
-- (1) For Γ⊢v:σ and Γ⊢e:τ!ε: Ssem((v,e))(ρ) = let b be Ssem(e)(ρ) in η(Vsem(v)(ρ),b).
-- (2) For Γ⊢v:σ→τ!ε and Γ⊢e:σ!ε: Ssem(v e)(ρ) = let a be Ssem(e)(ρ) in Vsem(v)(ρ)(a).
-- Both are immediate from the generic (pair)/(app) clauses of Esem plus
-- the Ŝ unit law above, replacing Ssem(val v)(ρ) by η̂ˢ(Vsem v ρ) (Lemma
-- 7.2/B.2, definitional here) -- neither touches Ŵ_ε's internal shape.
-- ---------------------------------------------------------------------

lemma-B4-1 : ∀ {Γ σ τ ε} (v : Val Γ σ) (e : Γ ⊢ τ ! ε) (ρ : Env Γ)
           → Esem (pair (val v) e) ρ ≡ bind̂ˢ (λ b → η̂ˢ (Vsem v ρ , b)) (Esem e ρ)
lemma-B4-1 v e ρ = bindˢ-unitˡ (λ a → bind̂ˢ (λ b → η̂ˢ (a , b)) (Esem e ρ)) (Vsem v ρ)

lemma-B4-2 : ∀ {Γ σ τ ε} (v : Val Γ (σ ⇒ τ ! ε)) (e : Γ ⊢ σ ! ε) (ρ : Env Γ)
           → Esem (app (val v) e) ρ ≡ bind̂ˢ (λ a → Vsem v ρ a) (Esem e ρ)
lemma-B4-2 v e ρ = bindˢ-unitˡ (λ φ → bind̂ˢ (λ a → φ a) (Esem e ρ)) (Vsem v ρ)

-- ---------------------------------------------------------------------
-- Lemma 7.5 (hat-Lemma B.5): loss continuations and THEN.
--
-- Statement (for e:Γ⊢σ!ε, g:LC Γ σ εg with sub:εg⊆ε):
--   (1) Esem(thenE sub e g)(ρ) = λγ1. R̂-of(Esem e ρ)(λa. widenŴ sub (Lsem g ρ a))
--   (2) Lsem g ρ = λa. Vsem g ρ a γ0, for the canonical zero continuation γ0
--   (3) Lsem(vabs(thenE sub e g))(ρ) = λa. R̂-of(Esem e (ρ,,a))(λb. widenŴ sub (Lsem g (ρ,,a) b))
--
-- Proved below (lemma-B5-1/2/3-RootZero) with an explicit RootZero(g)
-- hypothesis to match the paper's own statement shape, but each reduces
-- to `refl`: R̂-of and Lsem are defined (Domains.agda/Denotational.agda)
-- to compute exactly these formulas directly, so no induction on e or g
-- is needed. Lemma B.7 (loss continuations threaded through frames) is
-- not formalised as its own lemma -- Theorem 7.9/B.9's harder frame
-- cases (F-rule, S1-S4, R5, R7) are independent postulates in their own
-- right, not built from B.7.
-- ---------------------------------------------------------------------
-- Renaming coherence: Vsem/Lsem/Esem/handlerSem commute with a coherent
-- renaming of the environment. This is unstated background infrastructure
-- in the source (implicit in how it silently moves between contexts, e.g.
-- "F[x]" for fresh x, or R5's captured continuations), needed here to
-- make Lemma B.6 (and beyond) precise: plugging a fresh variable into a
-- weakened frame and evaluating under an extended environment must agree
-- with evaluating the frame's original contents.
-- ---------------------------------------------------------------------

-- A congruence principle for ext̂: if two layered algebras have equal
-- `act` fields and pointwise-agreeing `ψ` fields (on pointwise-equal
-- continuations), and f,g agree pointwise, then the homomorphic
-- extensions agree on every tree. General-purpose (not paper.tex
-- material as such), but exactly what's needed to compare the two
-- `algebra`s that handlerSem builds for a term and its renaming.
ext̂-cong : ∀ {ε X Y} (A1 A2 : LayeredAlg ε Y)
         → LayeredAlg.act A1 ≡ LayeredAlg.act A2
         → (∀ {ℓ1} (m : ℓ1 ∈ ε) (op : Op ℓ1) (o : ⟦ out op ⟧ᴳ) (κ κ' : ⟦ in′ op ⟧ᴳ → Y)
              → (∀ b → κ b ≡ κ' b) → LayeredAlg.ψ A1 m op o κ ≡ LayeredAlg.ψ A2 m op o κ')
         → (f g : X → Y) → (∀ x → f x ≡ g x)
         → (w : Ŵ ε X) → ext̂ A1 f w ≡ ext̂ A2 g w
ext̂-cong A1 A2 actEq ψEq f g feq (leaf r x) =
  trans (cong (λ act → act r (f x)) actEq) (cong (LayeredAlg.act A2 r) (feq x))
ext̂-cong A1 A2 actEq ψEq f g feq (node m op r o κ) =
  trans (cong (λ act → act r (LayeredAlg.ψ A1 m op o (λ b → ext̂ A1 f (κ b)))) actEq)
        (cong (LayeredAlg.act A2 r)
              (ψEq m op o (λ b → ext̂ A1 f (κ b)) (λ b → ext̂ A2 g (κ b))
                   (λ b → ext̂-cong A1 A2 actEq ψEq f g feq (κ b))))

RenCoh : ∀ {Γ Γ'} → Ren Γ Γ' → Env Γ → Env Γ' → Set
RenCoh {Γ} ren ρ ρ' = ∀ {σ} (x : Γ ∋ σ) → ρ' (ren x) ≡ ρ x

extR-coh : ∀ {Γ Γ'} (τ : Ty) (ren : Ren Γ Γ') (ρ : Env Γ) (ρ' : Env Γ') → RenCoh ren ρ ρ' → (a : ⟦ τ ⟧)
         → ∀ {σ} (x : (Γ , τ) ∋ σ) → (ρ' ,, a) (extR ren x) ≡ (ρ ,, a) x
extR-coh τ ren ρ ρ' coh a Z     = refl
extR-coh τ ren ρ ρ' coh a (S x) = coh x

-- Variant of extR-coh extending by two values a, a' related by a'≡a
-- (rather than the very same value on both sides), needed when the
-- extending value is itself something that first has to be shown equal
-- (e.g. handlerSem's l1v/k1v continuations, built from a κ that's only
-- known pointwise-equal, not syntactically identical, to κ').
extR-coh' : ∀ {Γ Γ'} (τ : Ty) (ren : Ren Γ Γ') (ρ : Env Γ) (ρ' : Env Γ') → RenCoh ren ρ ρ'
          → (a a' : ⟦ τ ⟧) → a' ≡ a
          → ∀ {σ} (x : (Γ , τ) ∋ σ) → (ρ' ,, a') (extR ren x) ≡ (ρ ,, a) x
extR-coh' τ ren ρ ρ' coh a a' eq Z     = eq
extR-coh' τ ren ρ ρ' coh a a' eq (S x) = coh x

mutual
  renV-coh : ∀ {Γ Γ' σ} (ren : Ren Γ Γ') (ρ : Env Γ) (ρ' : Env Γ') → RenCoh ren ρ ρ' → (v : Val Γ σ)
           → Vsem (renV ren v) ρ' ≡ Vsem v ρ
  renV-coh ren ρ ρ' coh (vvar x)    = coh x
  renV-coh ren ρ ρ' coh (vgnd x)    = refl
  renV-coh ren ρ ρ' coh (vpair v w) = cong₂ _,_ (renV-coh ren ρ ρ' coh v) (renV-coh ren ρ ρ' coh w)
  renV-coh {σ = σ ⇒ τ ! ε} ren ρ ρ' coh (vabs e) =
    funext (λ a → renE-coh (extR ren) (ρ ,, a) (ρ' ,, a) (extR-coh σ ren ρ ρ' coh a) e)

  renLsem-coh : ∀ {Γ Γ' σ ε} (ren : Ren Γ Γ') (ρ : Env Γ) (ρ' : Env Γ') → RenCoh ren ρ ρ' → (g : LC Γ σ ε) (a : ⟦ σ ⟧)
              → Lsem (renV ren g) ρ' a ≡ Lsem g ρ a
  renLsem-coh ren ρ ρ' coh g a = cong (λ F → F a (λ _ → η̂ 0#)) (renV-coh ren ρ ρ' coh g)

  renH-coh : ∀ {Γ Γ' ℓ σ σ' ε} (ren : Ren Γ Γ') (ρ : Env Γ) (ρ' : Env Γ') → RenCoh ren ρ ρ' → (h : Handler Γ ℓ σ σ' ε) (G : Ŝ (ε ,ℓ ℓ) ⟦ σ ⟧) (γ : ⟦ σ' ⟧ → Ŵ ε R)
           → handlerSem (renH ren h) ρ' G γ ≡ handlerSem h ρ G γ
  renH-coh {Γ} {Γ'} {ℓ} {σ} {σ'} {ε} ren ρ ρ' coh h G γ =
    trans (ext̂-cong (handlerAlg (renH ren h) ρ' γ) (handlerAlg h ρ γ) actEq ψEq
                     (handlerRet (renH ren h) ρ' γ) (handlerRet h ρ γ) sEq (G contRen))
          (cong (ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ)) GEq)
    where
    sEq : ∀ a → handlerRet (renH ren h) ρ' γ a ≡ handlerRet h ρ γ a
    sEq a = cong (λ F → F γ) (renE-coh (extR ren) (ρ ,, a) (ρ' ,, a)
                         (extR-coh σ ren ρ ρ' coh a) (ret h))

    -- G's own continuation bakes in a full evaluation of `ret h`, so
    -- unlike a hypothetical continuation-independent version, it's no
    -- longer literally the SAME term on the renamed and unrenamed sides
    -- -- bridge that first (via the same renE-coh already used for sEq,
    -- but kept at the Ŝ level rather than pre-applied to γ), then let
    -- ext̂-cong's existing machinery handle the matched tree.
    contRen contH : ⟦ σ ⟧ → Ŵ (ε ,ℓ ℓ) R
    contRen a = widenŴ ⊆ᵉ-,ℓ (R̂-of (Esem (ret (renH ren h)) (ρ' ,, a)) γ)
    contH   a = widenŴ ⊆ᵉ-,ℓ (R̂-of (Esem (ret h) (ρ ,, a)) γ)

    sEq' : ∀ a → Esem (ret (renH ren h)) (ρ' ,, a) ≡ Esem (ret h) (ρ ,, a)
    sEq' a = renE-coh (extR ren) (ρ ,, a) (ρ' ,, a) (extR-coh σ ren ρ ρ' coh a) (ret h)

    GEq : G contRen ≡ G contH
    GEq = cong G (funext (λ a → cong (λ F → widenŴ ⊆ᵉ-,ℓ (R̂-of F γ)) (sEq' a)))

    actEq : LayeredAlg.act (handlerAlg (renH ren h) ρ' γ) ≡ LayeredAlg.act (handlerAlg h ρ γ)
    actEq = refl

    ψEq : ∀ {ℓ1} (m : ℓ1 ∈ (ε ,ℓ ℓ)) (op : Op ℓ1) (o : ⟦ out op ⟧ᴳ) (κ κ' : ⟦ in′ op ⟧ᴳ → Ŵ ε ⟦ σ' ⟧)
        → (∀ b → κ b ≡ κ' b) → handlerΨ (renH ren h) ρ' γ m op o κ ≡ handlerΨ h ρ γ m op o κ'
    ψEq {ℓ1} m op o κ κ' κeq with ℓ1 ≟ᵉ ℓ
    ... | no neq = cong (λ z → node (demoteMem m neq) op 0# o z) (funext κeq)
    ... | yes eq with eq
    -- ψ' m op o κ uses κ for its own local l1v/k1v (call them l1vκ/k1vκ,
    -- the "target"/renamed side); ψ m op o κ' uses κ' the same way (call
    -- them l1vκ'/k1vκ', the "source"/original side).
    ...   | refl = cong (λ F → F γ) (renE-coh (extR (extR (extR ren)))
                     (((ρ ,, o) ,, l1vκ') ,, k1vκ') (((ρ' ,, o) ,, l1vκ) ,, k1vκ)
                     (extR-coh' (gnd (in′ op) ⇒ σ' ! ε) (extR (extR ren))
                       ((ρ ,, o) ,, l1vκ') ((ρ' ,, o) ,, l1vκ)
                       (extR-coh' (gnd (in′ op) ⇒ Loss ! ε) (extR ren)
                         (ρ ,, o) (ρ' ,, o) (extR-coh (gnd (out op)) ren ρ ρ' coh o)
                         l1vκ' l1vκ l1vEq)
                       k1vκ' k1vκ k1vEq)
                     (clause h op))
      where
      l1vκ l1vκ' : ⟦ in′ op ⟧ᴳ → Ŝ ε R
      l1vκ  a γ1 = mapŴ (λ { (r1 , r2) → r1 + r2 }) (collectX (ext̂ Ŵ-alg γ (κ  a)))
      l1vκ' a γ1 = mapŴ (λ { (r1 , r2) → r1 + r2 }) (collectX (ext̂ Ŵ-alg γ (κ' a)))
      k1vκ k1vκ' : ⟦ in′ op ⟧ᴳ → Ŝ ε ⟦ σ' ⟧
      k1vκ  a γ' = κ  a
      k1vκ' a γ' = κ' a
      l1vEq : l1vκ ≡ l1vκ'
      l1vEq = funext (λ a → funext (λ γ1 → cong (λ w → mapŴ (λ { (r1 , r2) → r1 + r2 }) (collectX (ext̂ Ŵ-alg γ w))) (κeq a)))
      k1vEq : k1vκ ≡ k1vκ'
      k1vEq = funext (λ a → funext (λ γ' → κeq a))

  renE-coh : ∀ {Γ Γ' σ ε} (ren : Ren Γ Γ') (ρ : Env Γ) (ρ' : Env Γ') → RenCoh ren ρ ρ' → (e : Γ ⊢ σ ! ε)
           → Esem (renE ren e) ρ' ≡ Esem e ρ
  renE-coh ren ρ ρ' coh (val v)   = cong η̂ˢ (renV-coh ren ρ ρ' coh v)
  renE-coh ren ρ ρ' coh (fun f e) = cong (bind̂ˢ (λ a → η̂ˢ (⟦ f ⟧f a))) (renE-coh ren ρ ρ' coh e)
  renE-coh ren ρ ρ' coh (pair e1 e2) =
    cong₂ (λ F1 F2 → bind̂ˢ (λ a → bind̂ˢ (λ b → η̂ˢ (a , b)) F2) F1) (renE-coh ren ρ ρ' coh e1) (renE-coh ren ρ ρ' coh e2)
  renE-coh ren ρ ρ' coh (fst e) = cong (bind̂ˢ (λ{ (a , b) → η̂ˢ a })) (renE-coh ren ρ ρ' coh e)
  renE-coh ren ρ ρ' coh (snd e) = cong (bind̂ˢ (λ{ (a , b) → η̂ˢ b })) (renE-coh ren ρ ρ' coh e)
  renE-coh ren ρ ρ' coh (app e1 e2) =
    cong₂ (λ F1 F2 → bind̂ˢ (λ φ → bind̂ˢ (λ a → φ a) F2) F1) (renE-coh ren ρ ρ' coh e1) (renE-coh ren ρ ρ' coh e2)
  renE-coh ren ρ ρ' coh (opE m op σeq e) = cong (subst (λ σ' → Ŝ _ ⟦ σ' ⟧) (sym σeq)) (cong (bind̂ˢ (λ a → φ̂ˢ m op a η̂ˢ)) (renE-coh ren ρ ρ' coh e))
  renE-coh ren ρ ρ' coh (lossE e) =
    funext (λ γ → cong (λ F → bind̂ (F (λ a → mapŴ (a +_) (γ tt))) (λ a → tell a (η̂ tt))) (renE-coh ren ρ ρ' coh e))
  renE-coh ren ρ ρ' coh (thenE sub e1 g) = funext (λ γ → cong₂
    (λ w1 f2 → bind̂ (collectX w1) (λ{ (a , r1) → mapŴ (r1 +_) (f2 a) }))
    e1treeEq innerEq)
    where
    contEq : (λ a → widenŴ sub (Lsem (renV ren g) ρ' a)) ≡ (λ a → widenŴ sub (Lsem g ρ a))
    contEq = funext (λ a → cong (widenŴ sub) (renLsem-coh ren ρ ρ' coh g a))
    e1treeEq : Esem (renE ren e1) ρ' (λ a → widenŴ sub (Lsem (renV ren g) ρ' a)) ≡ Esem e1 ρ (λ a → widenŴ sub (Lsem g ρ a))
    e1treeEq = trans (cong (λ F → F (λ a → widenŴ sub (Lsem (renV ren g) ρ' a))) (renE-coh ren ρ ρ' coh e1))
                      (cong (Esem e1 ρ) contEq)
    innerEq : (λ a → widenŴ sub (Vsem (renV ren g) ρ' a (λ _ → η̂ 0#))) ≡ (λ a → widenŴ sub (Vsem g ρ a (λ _ → η̂ 0#)))
    innerEq = funext (λ a → cong (λ F → widenŴ sub (F a (λ _ → η̂ 0#))) (renV-coh ren ρ ρ' coh g))

  renE-coh ren ρ ρ' coh (glocalE sub1 sub2 e g) = funext (λ γ →
    cong (widenŴ sub2) (trans (cong (λ F → F (λ a → widenŴ sub1 (Lsem (renV ren g) ρ' a))) (renE-coh ren ρ ρ' coh e))
                               (cong (Esem e ρ) (funext (λ a → cong (widenŴ sub1) (renLsem-coh ren ρ ρ' coh g a))))))

  renE-coh ren ρ ρ' coh (resetE e) = funext (λ γ → cong censor (cong (λ F → F γ) (renE-coh ren ρ ρ' coh e)))

  renE-coh ren ρ ρ' coh (handleE h e) = funext (λ γ →
    trans (cong (λ F → handlerSem (renH ren h) ρ' F γ) (renE-coh ren ρ ρ' coh e))
          (renH-coh ren ρ ρ' coh h (Esem e ρ) γ))

-- Weakening by exactly one variable is the special case ren := S,
-- coh := λ x → refl (immediate from `,,`'s own S-clause).
weaken1-coh : ∀ {Γ σ ε} (τ : Ty) (e : Γ ⊢ σ ! ε) (ρ : Env Γ) (a : ⟦ τ ⟧) → Esem (weaken1 e) (ρ ,, a) ≡ Esem e ρ
weaken1-coh τ e ρ a = renE-coh (S {τ = τ}) ρ (ρ ,, a) (λ x → refl) e

weaken1V-coh : ∀ {Γ σ} (τ : Ty) (v : Val Γ σ) (ρ : Env Γ) (a : ⟦ τ ⟧) → Vsem (weaken1V v) (ρ ,, a) ≡ Vsem v ρ
weaken1V-coh τ v ρ a = renV-coh (S {τ = τ}) ρ (ρ ,, a) (λ x → refl) v

weaken1H-coh : ∀ {Γ ℓ σ σ' ε} (τ : Ty) (h : Handler Γ ℓ σ σ' ε) (ρ : Env Γ) (a : ⟦ τ ⟧) (G : Ŝ (ε ,ℓ ℓ) ⟦ σ ⟧) (γ : ⟦ σ' ⟧ → Ŵ ε R)
              → handlerSem (renH (S {τ = τ}) h) (ρ ,, a) G γ ≡ handlerSem h ρ G γ
weaken1H-coh τ h ρ a G γ = renH-coh (S {τ = τ}) ρ (ρ ,, a) (λ x → refl) h G γ

-- ---------------------------------------------------------------------
-- Substitution coherence: the Sub-based analogue of renaming coherence
-- above (same shape of proof throughout, including the handlerSem case).
-- Needed from Theorem B.9 onward, where reduction rules substitute values
-- for variables (β-reduction, handler return/clause instantiation, ...).
-- ---------------------------------------------------------------------

SubCoh : ∀ {Γ Γ'} → Sub Γ Γ' → Env Γ' → Env Γ → Set
SubCoh {Γ} σs ρ' ρ = ∀ {σ} (x : Γ ∋ σ) → Vsem (σs x) ρ' ≡ ρ x

mutual
  extS-coh : ∀ {Γ Γ'} (τ : Ty) (σs : Sub Γ Γ') (ρ' : Env Γ') (ρ : Env Γ) → SubCoh σs ρ' ρ → (a : ⟦ τ ⟧)
           → ∀ {σ} (x : (Γ , τ) ∋ σ) → Vsem (extS σs x) (ρ' ,, a) ≡ (ρ ,, a) x
  extS-coh τ σs ρ' ρ coh a Z     = refl
  extS-coh τ σs ρ' ρ coh a (S x) = trans (weaken1V-coh τ (σs x) ρ' a) (coh x)

  -- Variant extending by two values a, a' related by a≡a' (mirroring
  -- extR-coh'), needed for handlerSem's l1v/k1v continuations.
  extS-coh' : ∀ {Γ Γ'} (τ : Ty) (σs : Sub Γ Γ') (ρ' : Env Γ') (ρ : Env Γ) → SubCoh σs ρ' ρ
            → (a a' : ⟦ τ ⟧) → a' ≡ a
            → ∀ {σ} (x : (Γ , τ) ∋ σ) → Vsem (extS σs x) (ρ' ,, a') ≡ (ρ ,, a) x
  extS-coh' τ σs ρ' ρ coh a a' eq Z     = eq
  extS-coh' τ σs ρ' ρ coh a a' eq (S x) = trans (weaken1V-coh τ (σs x) ρ' a') (coh x)

  subV-coh : ∀ {Γ Γ' σ} (σs : Sub Γ Γ') (ρ' : Env Γ') (ρ : Env Γ) → SubCoh σs ρ' ρ → (v : Val Γ σ)
           → Vsem (subV σs v) ρ' ≡ Vsem v ρ
  subV-coh σs ρ' ρ coh (vvar x)    = coh x
  subV-coh σs ρ' ρ coh (vgnd x)    = refl
  subV-coh σs ρ' ρ coh (vpair v w) = cong₂ _,_ (subV-coh σs ρ' ρ coh v) (subV-coh σs ρ' ρ coh w)
  subV-coh {σ = σ ⇒ τ ! ε} σs ρ' ρ coh (vabs e) =
    funext (λ a → subE-coh (extS σs) (ρ' ,, a) (ρ ,, a) (extS-coh σ σs ρ' ρ coh a) e)

  subLsem-coh : ∀ {Γ Γ' σ ε} (σs : Sub Γ Γ') (ρ' : Env Γ') (ρ : Env Γ) → SubCoh σs ρ' ρ → (g : LC Γ σ ε) (a : ⟦ σ ⟧)
              → Lsem (subV σs g) ρ' a ≡ Lsem g ρ a
  subLsem-coh σs ρ' ρ coh g a = cong (λ F → F a (λ _ → η̂ 0#)) (subV-coh σs ρ' ρ coh g)

  subH-coh : ∀ {Γ Γ' ℓ σ σ' ε} (σs : Sub Γ Γ') (ρ' : Env Γ') (ρ : Env Γ) → SubCoh σs ρ' ρ → (h : Handler Γ ℓ σ σ' ε) (G : Ŝ (ε ,ℓ ℓ) ⟦ σ ⟧) (γ : ⟦ σ' ⟧ → Ŵ ε R)
           → handlerSem (subH σs h) ρ' G γ ≡ handlerSem h ρ G γ
  subH-coh {Γ} {Γ'} {ℓ} {σ} {σ'} {ε} σs ρ' ρ coh h G γ =
    trans (ext̂-cong (handlerAlg (subH σs h) ρ' γ) (handlerAlg h ρ γ) actEq ψEq
                     (handlerRet (subH σs h) ρ' γ) (handlerRet h ρ γ) sEq (G contSub))
          (cong (ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ)) GEq)
    where
    sEq : ∀ a → handlerRet (subH σs h) ρ' γ a ≡ handlerRet h ρ γ a
    sEq a = cong (λ F → F γ) (subE-coh (extS σs) (ρ' ,, a) (ρ ,, a)
                         (extS-coh σ σs ρ' ρ coh a) (ret h))

    contSub contH : ⟦ σ ⟧ → Ŵ (ε ,ℓ ℓ) R
    contSub a = widenŴ ⊆ᵉ-,ℓ (R̂-of (Esem (ret (subH σs h)) (ρ' ,, a)) γ)
    contH   a = widenŴ ⊆ᵉ-,ℓ (R̂-of (Esem (ret h) (ρ ,, a)) γ)

    sEq' : ∀ a → Esem (ret (subH σs h)) (ρ' ,, a) ≡ Esem (ret h) (ρ ,, a)
    sEq' a = subE-coh (extS σs) (ρ' ,, a) (ρ ,, a)
                       (extS-coh σ σs ρ' ρ coh a) (ret h)

    GEq : G contSub ≡ G contH
    GEq = cong G (funext (λ a → cong (λ F → widenŴ ⊆ᵉ-,ℓ (R̂-of F γ)) (sEq' a)))

    actEq : LayeredAlg.act (handlerAlg (subH σs h) ρ' γ) ≡ LayeredAlg.act (handlerAlg h ρ γ)
    actEq = refl

    ψEq : ∀ {ℓ1} (m : ℓ1 ∈ (ε ,ℓ ℓ)) (op : Op ℓ1) (o : ⟦ out op ⟧ᴳ) (κ κ' : ⟦ in′ op ⟧ᴳ → Ŵ ε ⟦ σ' ⟧)
        → (∀ b → κ b ≡ κ' b) → handlerΨ (subH σs h) ρ' γ m op o κ ≡ handlerΨ h ρ γ m op o κ'
    ψEq {ℓ1} m op o κ κ' κeq with ℓ1 ≟ᵉ ℓ
    ... | no neq = cong (λ z → node (demoteMem m neq) op 0# o z) (funext κeq)
    ... | yes eq with eq
    ...   | refl = cong (λ F → F γ) (subE-coh (extS (extS (extS σs)))
                     (((ρ' ,, o) ,, l1vκ) ,, k1vκ) (((ρ ,, o) ,, l1vκ') ,, k1vκ')
                     (extS-coh' (gnd (in′ op) ⇒ σ' ! ε) (extS (extS σs))
                       ((ρ' ,, o) ,, l1vκ) ((ρ ,, o) ,, l1vκ')
                       (extS-coh' (gnd (in′ op) ⇒ Loss ! ε) (extS σs)
                         (ρ' ,, o) (ρ ,, o)
                         (extS-coh (gnd (out op)) σs ρ' ρ coh o)
                         l1vκ' l1vκ l1vEq)
                       k1vκ' k1vκ k1vEq)
                     (clause h op))
      where
      l1vκ l1vκ' : ⟦ in′ op ⟧ᴳ → Ŝ ε R
      l1vκ  a γ1 = mapŴ (λ { (r1 , r2) → r1 + r2 }) (collectX (ext̂ Ŵ-alg γ (κ  a)))
      l1vκ' a γ1 = mapŴ (λ { (r1 , r2) → r1 + r2 }) (collectX (ext̂ Ŵ-alg γ (κ' a)))
      k1vκ k1vκ' : ⟦ in′ op ⟧ᴳ → Ŝ ε ⟦ σ' ⟧
      k1vκ  a γ' = κ  a
      k1vκ' a γ' = κ' a
      l1vEq : l1vκ ≡ l1vκ'
      l1vEq = funext (λ a → funext (λ γ1 → cong (λ w → mapŴ (λ { (r1 , r2) → r1 + r2 }) (collectX (ext̂ Ŵ-alg γ w))) (κeq a)))
      k1vEq : k1vκ ≡ k1vκ'
      k1vEq = funext (λ a → funext (λ γ' → κeq a))

  subE-coh : ∀ {Γ Γ' σ ε} (σs : Sub Γ Γ') (ρ' : Env Γ') (ρ : Env Γ) → SubCoh σs ρ' ρ → (e : Γ ⊢ σ ! ε)
           → Esem (subE σs e) ρ' ≡ Esem e ρ
  subE-coh σs ρ' ρ coh (val v)   = cong η̂ˢ (subV-coh σs ρ' ρ coh v)
  subE-coh σs ρ' ρ coh (fun f e) = cong (bind̂ˢ (λ a → η̂ˢ (⟦ f ⟧f a))) (subE-coh σs ρ' ρ coh e)
  subE-coh σs ρ' ρ coh (pair e1 e2) =
    cong₂ (λ F1 F2 → bind̂ˢ (λ a → bind̂ˢ (λ b → η̂ˢ (a , b)) F2) F1) (subE-coh σs ρ' ρ coh e1) (subE-coh σs ρ' ρ coh e2)
  subE-coh σs ρ' ρ coh (fst e) = cong (bind̂ˢ (λ{ (a , b) → η̂ˢ a })) (subE-coh σs ρ' ρ coh e)
  subE-coh σs ρ' ρ coh (snd e) = cong (bind̂ˢ (λ{ (a , b) → η̂ˢ b })) (subE-coh σs ρ' ρ coh e)
  subE-coh σs ρ' ρ coh (app e1 e2) =
    cong₂ (λ F1 F2 → bind̂ˢ (λ φ → bind̂ˢ (λ a → φ a) F2) F1) (subE-coh σs ρ' ρ coh e1) (subE-coh σs ρ' ρ coh e2)
  subE-coh σs ρ' ρ coh (opE m op σeq e) = cong (subst (λ σ' → Ŝ _ ⟦ σ' ⟧) (sym σeq)) (cong (bind̂ˢ (λ a → φ̂ˢ m op a η̂ˢ)) (subE-coh σs ρ' ρ coh e))
  subE-coh σs ρ' ρ coh (lossE e) =
    funext (λ γ → cong (λ F → bind̂ (F (λ a → mapŴ (a +_) (γ tt))) (λ a → tell a (η̂ tt))) (subE-coh σs ρ' ρ coh e))
  subE-coh σs ρ' ρ coh (thenE sub e1 g) = funext (λ γ → cong₂
    (λ w1 f2 → bind̂ (collectX w1) (λ{ (a , r1) → mapŴ (r1 +_) (f2 a) }))
    e1treeEq innerEq)
    where
    contEq : (λ a → widenŴ sub (Lsem (subV σs g) ρ' a)) ≡ (λ a → widenŴ sub (Lsem g ρ a))
    contEq = funext (λ a → cong (widenŴ sub) (subLsem-coh σs ρ' ρ coh g a))
    e1treeEq : Esem (subE σs e1) ρ' (λ a → widenŴ sub (Lsem (subV σs g) ρ' a)) ≡ Esem e1 ρ (λ a → widenŴ sub (Lsem g ρ a))
    e1treeEq = trans (cong (λ F → F (λ a → widenŴ sub (Lsem (subV σs g) ρ' a))) (subE-coh σs ρ' ρ coh e1))
                      (cong (Esem e1 ρ) contEq)
    innerEq : (λ a → widenŴ sub (Vsem (subV σs g) ρ' a (λ _ → η̂ 0#))) ≡ (λ a → widenŴ sub (Vsem g ρ a (λ _ → η̂ 0#)))
    innerEq = funext (λ a → cong (λ F → widenŴ sub (F a (λ _ → η̂ 0#))) (subV-coh σs ρ' ρ coh g))

  subE-coh σs ρ' ρ coh (glocalE sub1 sub2 e g) = funext (λ γ →
    cong (widenŴ sub2) (trans (cong (λ F → F (λ a → widenŴ sub1 (Lsem (subV σs g) ρ' a))) (subE-coh σs ρ' ρ coh e))
                               (cong (Esem e ρ) (funext (λ a → cong (widenŴ sub1) (subLsem-coh σs ρ' ρ coh g a))))))

  subE-coh σs ρ' ρ coh (resetE e) = funext (λ γ → cong censor (cong (λ F → F γ) (subE-coh σs ρ' ρ coh e)))

  subE-coh σs ρ' ρ coh (handleE h e) = funext (λ γ →
    trans (cong (λ F → handlerSem (subH σs h) ρ' F γ) (subE-coh σs ρ' ρ coh e))
          (subH-coh σs ρ' ρ coh h (Esem e ρ) γ))

-- Single substitution, e[v] : the special case σs := sub1 v, coh := λ x → refl.
sub1-coh : ∀ {Γ σ τ ε} (e : (Γ , σ) ⊢ τ ! ε) (ρ : Env Γ) (v : Val Γ σ) → Esem (e [ v ]) ρ ≡ Esem e (ρ ,, Vsem v ρ)
sub1-coh e ρ v = subE-coh (sub1 v) ρ (ρ ,, Vsem v ρ) (λ { Z → refl ; (S x) → refl }) e

-- ---------------------------------------------------------------------
-- Lemma 7.6 (hat-Lemma B.6): the context lemma for regular frames.
-- "For e:σ!ε and F[e]:τ!ε where F is a regular frame:
--    Ssem(F[e])(ρ) = let_Sε a∈σ be Ssem(e)(ρ) in Ssem(F[x])(ρ[x/a])"
--
-- Proved case-by-case on F (Fig. 5's eight forms, parameter-free: no
-- F-handleP -- handleE has a single, S-frame-only hole now). Every case except
-- F-loss reduces cleanly to the Ŝ unit law (bindˢ-unitˡ, as in Lemma
-- B.4) plus weakening coherence -- exactly "no case here touches Ŵε's
-- internal structure" as the source states. F-loss is the one frame
-- whose hole is loss-typed, and hand-computation shows its case needs a
-- naturality property of Ŝ's bind w.r.t. tell that traces back to the
-- same unresolved fusion law as Lemma B.5 (§7's THEN lemma) -- both are
-- ultimately about how `tell` commutes with "let"; postponed with it.
-- ---------------------------------------------------------------------

-- Now that R̂-of routes through collectX/mapŴ (Domains.agda) instead of
-- a plain bind̂, it uses the SAME "mapŴ into the payload" injection style
-- lossE's own clause does -- so bind̂ˢ's own naturality machinery and
-- lossE's clause line up directly, with no per-e induction needed at
-- all: both sides reduce to a bind̂ over the SAME two arguments, via
-- R̂-of-eq (below) on the first and tell-0 on the second.
Ŝ-tell-naturality :
  ∀ {Γ ε} (e : Γ ⊢ Loss ! ε) (ρ : Env Γ)
  → Esem (lossE e) ρ ≡ bind̂ˢ (λ a → Esem (lossE {ε = ε} (val (vvar Z))) (ρ ,, a)) (Esem e ρ)
Ŝ-tell-naturality {ε = ε} e ρ = funext lemma
  where
  -- R̂-of (Esem (lossE (val (vvar Z))) (ρ,,x)) γ' unfolds (bind̂-unitˡ,
  -- since Esem (val (vvar Z)) (ρ,,x) is η̂ˢ x, ignoring its own
  -- continuation) to tell 0# (mapŴ ((x+0#)+_) (γ' tt)), matching lossE's
  -- own "mapŴ (x +_) (γ' tt)" injection up to tell-0/+-identityʳ.
  R̂-of-eq : ∀ x γ' → R̂-of (Esem (lossE (val (vvar Z))) (ρ ,, x)) γ' ≡ mapŴ (x +_) (γ' tt)
  R̂-of-eq x γ' =
    trans (cong (λ w → bind̂ (collectX w) (λ { (a , r1) → mapŴ (r1 +_) (γ' a) })) (bind̂-unitˡ x (λ a' → tell a' (η̂ tt))))
          (trans (tell-0 _) (cong (λ z → mapŴ (z +_) (γ' tt)) (+-identityʳ x)))

  lemma : ∀ γ → Esem (lossE e) ρ γ ≡ bind̂ˢ (λ a → Esem (lossE {ε = ε} (val (vvar Z))) (ρ ,, a)) (Esem e ρ) γ
  lemma γ = cong₂ bind̂ (cong (Esem e ρ) (funext (λ x → sym (R̂-of-eq x γ))))
                       (funext (λ x → sym (tell-0 (tell x (η̂ tt)))))

lemma-B6 : ∀ {Γ α ε τ} (f : Frame Γ α ε τ ε) (e : Γ ⊢ α ! ε) (ρ : Env Γ)
         → Esem (plugF f e) ρ ≡ bind̂ˢ (λ a → Esem (plugF (weaken1F f) (val (vvar Z))) (ρ ,, a)) (Esem e ρ)

lemma-B6 {α = α} (F-fun pf) e ρ = cong (λ F → bind̂ˢ F (Esem e ρ)) (funext (λ a →
  sym (bindˢ-unitˡ (λ b → η̂ˢ (⟦ pf ⟧f b)) a)))

lemma-B6 {α = α} (F-pairL e₂) e ρ = cong (λ F → bind̂ˢ F (Esem e ρ)) (funext (λ a → sym (trans
  (bindˢ-unitˡ (λ a' → bind̂ˢ (λ b → η̂ˢ (a' , b)) (Esem (weaken1 e₂) (ρ ,, a))) a)
  (cong (bind̂ˢ (λ b → η̂ˢ (a , b))) (weaken1-coh α e₂ ρ a)))))

lemma-B6 {α = α} {ε = ε} (F-pairR {σ = σ} v) e ρ = trans (lemma-B4-1 v e ρ) (cong (λ F → bind̂ˢ F (Esem e ρ)) (funext per-a))
  where
  per-a : (a : ⟦ α ⟧) → η̂ˢ (Vsem v ρ , a) ≡ Esem (pair (val (weaken1V v)) (val (vvar Z))) (ρ ,, a)
  per-a a = sym step3
    where
    step12 : bind̂ˢ {X = ⟦ σ ⟧} {Y = ⟦ σ `× α ⟧} (λ a' → bind̂ˢ {X = ⟦ α ⟧} (λ b → η̂ˢ (a' , b)) (η̂ˢ a)) (η̂ˢ (Vsem (weaken1V v) (ρ ,, a)))
           ≡ η̂ˢ (Vsem (weaken1V v) (ρ ,, a) , a)
    step12 = trans (bindˢ-unitˡ {X = ⟦ σ ⟧} {Y = ⟦ σ `× α ⟧} (λ a' → bind̂ˢ (λ b → η̂ˢ (a' , b)) (η̂ˢ a)) (Vsem (weaken1V v) (ρ ,, a)))
                   (bindˢ-unitˡ {X = ⟦ α ⟧} {Y = ⟦ σ `× α ⟧} (λ b → η̂ˢ (Vsem (weaken1V v) (ρ ,, a) , b)) a)
    step3 : Esem (pair (val (weaken1V v)) (val (vvar Z))) (ρ ,, a) ≡ η̂ˢ (Vsem v ρ , a)
    step3 = trans step12 (cong (λ w → η̂ˢ (w , a)) (weaken1V-coh α v ρ a))

lemma-B6 (F-fst {σ = σ} {τ = τ}) e ρ = cong (λ F → bind̂ˢ F (Esem e ρ)) (funext (λ (ab : ⟦ σ ⟧ × ⟦ τ ⟧) →
  sym (bindˢ-unitˡ {X = ⟦ σ ⟧ × ⟦ τ ⟧} (λ{ (a' , b') → η̂ˢ a' }) ab)))

lemma-B6 (F-snd {σ = σ} {τ = τ}) e ρ = cong (λ F → bind̂ˢ F (Esem e ρ)) (funext (λ (ab : ⟦ σ ⟧ × ⟦ τ ⟧) →
  sym (bindˢ-unitˡ {X = ⟦ σ ⟧ × ⟦ τ ⟧} (λ{ (a' , b') → η̂ˢ b' }) ab)))

lemma-B6 {α = α} (F-appL e₂) e ρ = cong (λ F → bind̂ˢ F (Esem e ρ)) (funext (λ a → sym (trans
  (bindˢ-unitˡ (λ φ → bind̂ˢ (λ b → φ b) (Esem (weaken1 e₂) (ρ ,, a))) a)
  (cong (bind̂ˢ (λ b → a b)) (weaken1-coh α e₂ ρ a)))))

lemma-B6 {α = α} (F-appR v) e ρ = trans (lemma-B4-2 v e ρ) (cong (λ F → bind̂ˢ F (Esem e ρ)) (funext (λ a → sym (trans
  (lemma-B4-2 {σ = α} (weaken1V v) (val (vvar Z)) (ρ ,, a))
  (trans (bindˢ-unitˡ (Vsem (weaken1V v) (ρ ,, a)) a)
         (cong (λ φ → φ a) (weaken1V-coh α v ρ a)))))))

lemma-B6 (F-op m op refl) e ρ = cong (λ F → bind̂ˢ F (Esem e ρ)) (funext (λ a →
  sym (bindˢ-unitˡ (λ b → φ̂ˢ m op b η̂ˢ) a)))

lemma-B6 F-loss e ρ = Ŝ-tell-naturality e ρ

-- Lemma 7.7 (hat-Lemma B.7), "threading loss continuations through
-- frames", is not formalised as its own lemma here: it is not consumed
-- by anything else in this file -- Theorem 7.9/B.9's harder cases below
-- are independent postulates in their own right -- so it's omitted
-- rather than kept as unconsumed scaffolding.

-- ---------------------------------------------------------------------
-- Lemma 7.8 (hat-Lemma B.8): operations under contexts K.
-- "For K[op(v)]:σ!ε with op∉h_eff(K) and op:out--ℓ→in:
--    Ssem(K[op(v)])(ρ)(γ) = φ̂_{ℓ,op,ε(ℓ)}(Vsem(v)(ρ), λa∈in. Ssem(K[x])(ρ[a/x])(γ))"
--
-- Our ContCxt tracks the hole's own effect εH separately from the outer
-- effect εO (they can differ across an S-handleB for some other label
-- ℓ'≠ℓ), where the source's single "ε" implicitly conflates them. `promote`
-- transports the hole-level membership ℓ∈εH out to the outer ℓ∈εO along K,
-- using ¬Handles at each S-handleB step to rule out ℓ=ℓ'.
-- ---------------------------------------------------------------------

-- Every regular frame constructor happens to preserve the effect context
-- between hole and result (checked when Frame was defined), but the type
-- Frame Γ α β τ ε'' itself doesn't structurally force β≡ε''; recorded here
-- once, by cases, so `promote`'s F∘ case can transport along it.
Frame-effect-eq : ∀ {Γ α β τ ε''} (f : Frame Γ α β τ ε'') → β ≡ ε''
Frame-effect-eq (F-fun _)     = refl
Frame-effect-eq (F-pairL _)   = refl
Frame-effect-eq (F-pairR _)   = refl
Frame-effect-eq F-fst         = refl
Frame-effect-eq F-snd         = refl
Frame-effect-eq (F-appL _)    = refl
Frame-effect-eq (F-appR _)    = refl
Frame-effect-eq (F-op _ _ _)  = refl
Frame-effect-eq F-loss        = refl

promote : ∀ {Γ σ εH τ εO ℓ} (k : ContCxt Γ σ εH τ εO) → ¬ Handles k ℓ → ℓ ∈ εH → ℓ ∈ εO
promote ▫ nh m = m
promote (F∘ {β = β} k f) nh m rewrite Frame-effect-eq f = promote k nh m
promote (S∘ k (S-handleB {ℓ = ℓ'} {ε = εk} h)) nh m with ∈-++⁻ εk {ys = ℓ' ∷ []} (promote k (λ hk → nh (inj₂ hk)) m)
... | inj₁ m-old        = m-old
... | inj₂ (here eq)    = ⊥-elim (nh (inj₁ eq))
... | inj₂ (there ())
promote (S∘ k (S-then _ _)) nh m         = promote k nh m
promote (S∘ k (S-glocal sub1 sub2 _)) nh m = sub2 (promote k nh m)
promote (S∘ k S-reset) nh m              = promote k nh m

-- "Double weakening is a no-op": weakening a frame TWICE (once by some
-- unrelated fresh var υ, then by its own hole-type α) and evaluating
-- under the correspondingly-extended environment agrees with weakening
-- it ONCE (by α directly) and evaluating without the extra υ-binding --
-- since f's own embedded subexpressions never mention that extra var at
-- all. This is exactly the "double weakening commutes" lemma flagged
-- below as unformalised; closed here via renV-coh/renE-coh's already-
-- proven family (weaken1-coh/weaken1V-coh/weaken1H-coh, each just the
-- ren:=S specialisation of renE-coh/renV-coh/renH-coh), applied twice
-- per case to funnel both sides down to a common base at plain ρ.
weaken1F-skip : ∀ {Γ α β τ ε'} (f : Frame Γ α β τ ε') (υ : Ty) (ρ : Env Γ) (c : ⟦ υ ⟧) (a : ⟦ α ⟧)
  → Esem (plugF (weaken1F {υ = α} (weaken1F {υ = υ} f)) (val (vvar Z))) ((ρ ,, c) ,, a) ≡ Esem (plugF (weaken1F {υ = α} f) (val (vvar Z))) (ρ ,, a)
weaken1F-skip (F-fun pf) υ ρ c a = refl
weaken1F-skip {α = α} (F-pairL e₂) υ ρ c a = trans lhsRed (sym rhsRed)
  where
  lhsRed : Esem (pair (val (vvar Z)) (weaken1 (weaken1 e₂))) ((ρ ,, c) ,, a) ≡ bind̂ˢ (λ b → η̂ˢ (a , b)) (Esem e₂ ρ)
  lhsRed = trans (bindˢ-unitˡ (λ a' → bind̂ˢ (λ b → η̂ˢ (a' , b)) (Esem (weaken1 (weaken1 e₂)) ((ρ ,, c) ,, a))) a)
                 (trans (cong (bind̂ˢ (λ b → η̂ˢ (a , b))) (weaken1-coh α (weaken1 e₂) (ρ ,, c) a))
                        (cong (bind̂ˢ (λ b → η̂ˢ (a , b))) (weaken1-coh υ e₂ ρ c)))
  rhsRed : Esem (pair (val (vvar Z)) (weaken1 e₂)) (ρ ,, a) ≡ bind̂ˢ (λ b → η̂ˢ (a , b)) (Esem e₂ ρ)
  rhsRed = trans (bindˢ-unitˡ (λ a' → bind̂ˢ (λ b → η̂ˢ (a' , b)) (Esem (weaken1 e₂) (ρ ,, a))) a)
                 (cong (bind̂ˢ (λ b → η̂ˢ (a , b))) (weaken1-coh α e₂ ρ a))
weaken1F-skip {α = α} (F-pairR v) υ ρ c a = trans lhsRed (sym rhsRed)
  where
  lhsRed : Esem (pair (val (weaken1V (weaken1V v))) (val (vvar Z))) ((ρ ,, c) ,, a) ≡ η̂ˢ (Vsem v ρ , a)
  lhsRed = trans (bindˢ-unitˡ (λ x → bind̂ˢ (λ y → η̂ˢ (x , y)) (η̂ˢ a)) (Vsem (weaken1V (weaken1V v)) ((ρ ,, c) ,, a)))
                 (trans (bindˢ-unitˡ (λ y → η̂ˢ (Vsem (weaken1V (weaken1V v)) ((ρ ,, c) ,, a) , y)) a)
                        (cong (λ x → η̂ˢ (x , a)) (trans (weaken1V-coh α (weaken1V v) (ρ ,, c) a) (weaken1V-coh υ v ρ c))))
  rhsRed : Esem (pair (val (weaken1V v)) (val (vvar Z))) (ρ ,, a) ≡ η̂ˢ (Vsem v ρ , a)
  rhsRed = trans (bindˢ-unitˡ (λ x → bind̂ˢ (λ y → η̂ˢ (x , y)) (η̂ˢ a)) (Vsem (weaken1V v) (ρ ,, a)))
                 (trans (bindˢ-unitˡ (λ y → η̂ˢ (Vsem (weaken1V v) (ρ ,, a) , y)) a)
                        (cong (λ x → η̂ˢ (x , a)) (weaken1V-coh α v ρ a)))
weaken1F-skip F-fst υ ρ c a = refl
weaken1F-skip F-snd υ ρ c a = refl
weaken1F-skip {α = α} (F-appL e₂) υ ρ c a = trans lhsRed (sym rhsRed)
  where
  lhsRed : Esem (app (val (vvar Z)) (weaken1 (weaken1 e₂))) ((ρ ,, c) ,, a) ≡ bind̂ˢ (λ b → a b) (Esem e₂ ρ)
  lhsRed = trans (bindˢ-unitˡ (λ φ → bind̂ˢ (λ b → φ b) (Esem (weaken1 (weaken1 e₂)) ((ρ ,, c) ,, a))) a)
                 (trans (cong (bind̂ˢ (λ b → a b)) (weaken1-coh α (weaken1 e₂) (ρ ,, c) a))
                        (cong (bind̂ˢ (λ b → a b)) (weaken1-coh υ e₂ ρ c)))
  rhsRed : Esem (app (val (vvar Z)) (weaken1 e₂)) (ρ ,, a) ≡ bind̂ˢ (λ b → a b) (Esem e₂ ρ)
  rhsRed = trans (bindˢ-unitˡ (λ φ → bind̂ˢ (λ b → φ b) (Esem (weaken1 e₂) (ρ ,, a))) a)
                 (cong (bind̂ˢ (λ b → a b)) (weaken1-coh α e₂ ρ a))
weaken1F-skip {α = α} (F-appR v) υ ρ c a = trans lhsRed (sym rhsRed)
  where
  lhsRed : Esem (app (val (weaken1V (weaken1V v))) (val (vvar Z))) ((ρ ,, c) ,, a) ≡ Vsem v ρ a
  lhsRed = trans (bindˢ-unitˡ (λ φ → bind̂ˢ (λ b → φ b) (η̂ˢ a)) (Vsem (weaken1V (weaken1V v)) ((ρ ,, c) ,, a)))
                 (trans (bindˢ-unitˡ (λ b → Vsem (weaken1V (weaken1V v)) ((ρ ,, c) ,, a) b) a)
                        (cong (λ φ → φ a) (trans (weaken1V-coh α (weaken1V v) (ρ ,, c) a) (weaken1V-coh υ v ρ c))))
  rhsRed : Esem (app (val (weaken1V v)) (val (vvar Z))) (ρ ,, a) ≡ Vsem v ρ a
  rhsRed = trans (bindˢ-unitˡ (λ φ → bind̂ˢ (λ b → φ b) (η̂ˢ a)) (Vsem (weaken1V v) (ρ ,, a)))
                 (trans (bindˢ-unitˡ (λ b → Vsem (weaken1V v) (ρ ,, a) b) a)
                        (cong (λ φ → φ a) (weaken1V-coh α v ρ a)))
weaken1F-skip (F-op m op refl) υ ρ c a = refl
weaken1F-skip F-loss υ ρ c a = refl

-- Inductive cases (F∘, S-handleB with ℓ≠ℓ', S-then, S-glocal, S-reset):
-- the source's own proof (by induction on the size of K) handles each by
-- combining the regular-frame/special-frame semantics with the induction
-- hypothesis at the appropriate re-weighted loss continuation, exactly as
-- Lemma B.7 combines B.6 with B.5(3). Formalising this cleanly needs a
-- "double weakening commutes" lemma (weaken1F/weaken1K interacting with
-- an *inner* application of Lemma 7.6 at the extended environment ρ,,a,
-- nested inside the outer one) that materially complicates the
-- bookkeeping beyond B.7's single-weakening case; not chased down here.
-- The base case (▫) below is fully proved.

-- Forward-declared so lemma-B8-F∘ (mutually recursive with it, on the
-- structurally smaller k) can call it before its own body (below) is given.
lemma-B8 : ∀ {Γ ℓ εH τ εO} (op : Op ℓ) (v : Val Γ (gnd (out op)))
           (k : ContCxt Γ (gnd (in′ op)) εH τ εO) (mH : ℓ ∈ εH) (nh : ¬ Handles k ℓ)
           (ρ : Env Γ) (γ : ⟦ τ ⟧ → Ŵ εO R)
         → Esem (plugK k (opE mH op refl (val v))) ρ γ
         ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, a)) γ

-- bind̂ˢ H (φ̂ˢ m op o f) ≡ φ̂ˢ m op o (λa → bind̂ˢ H (f a)): a node built by
-- φ̂ˢ survives being fed through an outer bind̂ˢ untouched (only its own
-- branches get bind̂ˢ'd) -- both sides reduce (by direct unfolding of
-- bind̂ˢ/φ̂ˢ/ext̂/bind̂) to the SAME node, wrapped in an extra tell 0# on
-- the LHS only, which tell-0 strips.
bind̂ˢ-φ̂ˢ-fusion : ∀ {ε X Y ℓ} (m : ℓ ∈ ε) (op : Op ℓ) (o : ⟦ out op ⟧ᴳ) (f : ⟦ in′ op ⟧ᴳ → Ŝ ε X) (H : X → Ŝ ε Y)
  → bind̂ˢ H (φ̂ˢ m op o f) ≡ φ̂ˢ m op o (λ a → bind̂ˢ H (f a))
bind̂ˢ-φ̂ˢ-fusion m op o f H = funext (λ γ → tell-0 (φ̂ˢ m op o (λ a → bind̂ˢ H (f a)) γ))

-- (F∘) case of Lemma B.8, stated with k/f's hole and result effects
-- ALREADY MERGED to a single εO -- always valid for a regular frame f
-- (Frame-effect-eq), and this shape is what makes lemma-B6/bind̂ˢ
-- type-check directly (both need a single shared effect throughout,
-- since Ŝ's own γ-argument is threaded at one fixed ε). The general
-- (β≠εO indices, as ContCxt's own type technically allows) statement
-- is recovered as a corollary at lemma-B8's own F∘ dispatch clause
-- below, by pattern-matching Frame-effect-eq f there -- since k,f are
-- BOTH freshly introduced by that SAME F∘kf pattern match (unlike here,
-- where they're separate, already-fixed parameters), unifying their
-- indices doesn't need to re-generalise any OTHER hypothesis's type,
-- avoiding the "ill-typed with-abstraction" failure a whole-clause
-- rewrite/with hits when attempted directly inside a lemma that takes
-- k and f as independent arguments.
--
-- Proof: plugK(F∘kf)e₀ = plugFf(plugKke₀), so lemma-B6 (unconditional,
-- and now type-correct since k/f share εO) turns Esem(plugFf(plugKk
-- e₀))ρ into bind̂ˢH(Esem(plugKke₀)ρ) for a fixed H; the IH (lemma-B8 on
-- the structurally smaller k) rewrites Esem(plugKke₀)ρ into a φ̂ˢ node;
-- bind̂ˢ-φ̂ˢ-fusion pushes H through that node; and weaken1F-skip
-- identifies the resulting per-branch continuation bind̂ˢH(Esem(plugK
-- (weaken1Kk)(val(vvarZ)))(ρ,,a)) with the target Esem(plugK(weaken1K
-- (F∘kf))(val(vvarZ)))(ρ,,a) -- the "double weakening commutes" step
-- the original comment flagged.
-- Frame-effect-eq f, even once β,εO are the same metavariable, is not
-- SYNTACTICALLY refl for an abstract f (it only reduces once f's own
-- constructor is pattern-matched) -- so `promote`'s own F∘ clause
-- (defined via `rewrite Frame-effect-eq f` internally) does not unfold
-- definitionally just because the indices happen to already coincide;
-- this still needs an explicit `with ... | refl` to force the reduction.
promote-F∘-eq : ∀ {Γ ℓ σ εH α εO τ} (k : ContCxt Γ σ εH α εO) (f : Frame Γ α εO τ εO) (nh : ¬ Handles (F∘ k f) ℓ) (mH : ℓ ∈ εH)
  → promote (F∘ k f) nh mH ≡ promote k nh mH
promote-F∘-eq k f nh mH with Frame-effect-eq f
... | refl = refl

lemma-B8-F∘-eq : ∀ {Γ ℓ εH α τ εO} (op : Op ℓ) (v : Val Γ (gnd (out op)))
            (k : ContCxt Γ (gnd (in′ op)) εH α εO) (f : Frame Γ α εO τ εO) (mH : ℓ ∈ εH) (nh : ¬ Handles (F∘ k f) ℓ)
            (ρ : Env Γ) (γ : ⟦ τ ⟧ → Ŵ εO R)
          → Esem (plugK (F∘ k f) (opE mH op refl (val v))) ρ γ
          ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K (F∘ k f)) (val (vvar Z))) (ρ ,, a)) γ
lemma-B8-F∘-eq {α = α} op v k f mH nh ρ γ = trans step1 (trans step2 step3)
  where
  e₀ = plugK k (opE mH op refl (val v))
  H : ⟦ α ⟧ → Ŝ _ _
  H a = Esem (plugF (weaken1F f) (val (vvar Z))) (ρ ,, a)
  ih : Esem e₀ ρ ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, a))
  ih = funext (λ γ' → lemma-B8 op v k mH nh ρ γ')
  step1 : Esem (plugF f (plugK k (opE mH op refl (val v)))) ρ γ ≡ bind̂ˢ H (Esem e₀ ρ) γ
  step1 = cong (λ F → F γ) (lemma-B6 f e₀ ρ)
  step2 : bind̂ˢ H (Esem e₀ ρ) γ
        ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ a → bind̂ˢ H (Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, a))) γ
  step2 = trans (cong (λ F → bind̂ˢ H F γ) ih)
                (cong (λ F → F γ) (bind̂ˢ-φ̂ˢ-fusion (promote k nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, a)) H))
  step3 : φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ a → bind̂ˢ H (Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, a))) γ
        ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K (F∘ k f)) (val (vvar Z))) (ρ ,, a)) γ
  step3 = cong (λ F → F γ) (cong (φ̂ˢ (promote k nh mH) op (Vsem v ρ)) (funext bAeq))
    where
    bAeq : ∀ (a : ⟦ in′ op ⟧ᴳ) → bind̂ˢ H (Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, a)) ≡ Esem (plugK (weaken1K (F∘ k f)) (val (vvar Z))) (ρ ,, a)
    bAeq a = trans (cong (λ F → bind̂ˢ F (Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, a))) (sym (funext (λ b → weaken1F-skip f (gnd (in′ op)) ρ a b))))
                   (sym (lemma-B6 (weaken1F f) (plugK (weaken1K k) (val (vvar Z))) (ρ ,, a)))

-- General (F∘) case, β≠εO as ContCxt's own type technically allows:
-- a thin corollary of lemma-B8-F∘-eq + promote-F∘-eq, via its OWN,
-- self-contained `with Frame-effect-eq f | refl` (matching against
-- THIS function's own stated goal, not a different clause's goal --
-- feeding the merged-effect result across a with-abstraction boundary
-- into a DIFFERENT function's own, separately-elaborated goal is what
-- produced the persistent "stuck vs reduced" mismatch when this was
-- attempted directly inside lemma-B8's own F∘ dispatch clause).
lemma-B8-F∘ : ∀ {Γ ℓ εH α τ β εO} (op : Op ℓ) (v : Val Γ (gnd (out op)))
            (k : ContCxt Γ (gnd (in′ op)) εH α β) (f : Frame Γ α β τ εO) (mH : ℓ ∈ εH) (nh : ¬ Handles (F∘ k f) ℓ)
            (ρ : Env Γ) (γ : ⟦ τ ⟧ → Ŵ εO R)
          → Esem (plugK (F∘ k f) (opE mH op refl (val v))) ρ γ
          ≡ φ̂ˢ (promote (F∘ k f) nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K (F∘ k f)) (val (vvar Z))) (ρ ,, a)) γ
lemma-B8-F∘ {β = β} {εO = εO} op v k f mH nh ρ γ = helper (Frame-effect-eq f)
  where
  helper : (eq : β ≡ εO) → Esem (plugK (F∘ k f) (opE mH op refl (val v))) ρ γ
         ≡ φ̂ˢ (promote (F∘ k f) nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K (F∘ k f)) (val (vvar Z))) (ρ ,, a)) γ
  helper refl = trans (lemma-B8-F∘-eq op v k f mH nh ρ γ)
                       (cong (λ m → φ̂ˢ m op (Vsem v ρ) (λ a → Esem (plugK (weaken1K (F∘ k f)) (val (vvar Z))) (ρ ,, a)) γ)
                             (sym (promote-F∘-eq k f nh mH)))


-- (S∘) case, split on s's four constructors. S-reset has β=εO built
-- into SFrame's own type (promote(S∘k S-reset)nhmH reduces DIRECTLY to
-- promote k nh mH, no Frame-effect-eq-style opacity issue at all -- this
-- is an unconditional delegate clause of `promote`, not a rewrite), so
-- it closes via a direct cong pushing the IH through resetE/censor's
-- own homomorphic behaviour on nodes. S-then ALSO has β=εO built in;
-- Esem(thenE...) is γ-constant, and bridging the IH through its own
-- collectX/bump combine-step needs bump-0/tell-0 (the SAME machinery
-- theorem-B9-S2 needed, but no "shift"-style redistribution issue here
-- since the combine-step only ever bumps by 0# at a node it didn't
-- itself introduce). S-glocal/S-handleB have GENUINELY different β,εO
-- (related by an inclusion witness, not an equality) -- comparable in
-- scope to (S1)/(R5) themselves, postulated below (theorem-B9-R5-gen's
-- own remaining gap).
lemma-B8-S∘-then : ∀ {Γ ℓ εH α εg ε} (op : Op ℓ) (v : Val Γ (gnd (out op)))
            (k : ContCxt Γ (gnd (in′ op)) εH α ε) (sub : εg ⊆ᵉ ε) (g : LC Γ α εg) (mH : ℓ ∈ εH) (nh : ¬ Handles k ℓ)
            (ρ : Env Γ) (γ : ⟦ Loss ⟧ → Ŵ ε R)
          → Esem (thenE sub (plugK k (opE mH op refl (val v))) g) ρ γ
          ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-then sub g))) (val (vvar Z))) (ρ ,, b)) γ
lemma-B8-S∘-then {α = α} {ε = ε} op v k sub g mH nh ρ γ = trans step1 step2
  where
  e₀ = plugK k (opE mH op refl (val v))
  δ1 : ⟦ α ⟧ → Ŵ ε R
  δ1 a = widenŴ sub (Lsem g ρ a)
  K : ⟦ α ⟧ × R → Ŵ ε R
  K (a , r1) = mapŴ (r1 +_) (widenŴ sub (Vsem g ρ a (λ _ → η̂ 0#)))
  κ : ⟦ in′ op ⟧ᴳ → Ŝ ε ⟦ α ⟧
  κ b = Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, b)
  ih : Esem e₀ ρ δ1 ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) κ δ1
  ih = lemma-B8 op v k mH nh ρ δ1
  step1 : Esem (thenE sub e₀ g) ρ γ ≡ bind̂ (collectX (φ̂ˢ (promote k nh mH) op (Vsem v ρ) κ δ1)) K
  step1 = cong (λ w → bind̂ (collectX w) K) ih
  bAeq : ∀ (b : ⟦ in′ op ⟧ᴳ) → bind̂ (collectX (κ b δ1)) K ≡ Esem (plugK (weaken1K (S∘ k (S-then sub g))) (val (vvar Z))) (ρ ,, b) γ
  bAeq b = cong₂ (λ f1 f2 → bind̂ (collectX (κ b f1)) f2) (funext δ1Eq) (funext K'Eq)
    where
    δ1Eq : ∀ a → δ1 a ≡ widenŴ sub (Lsem (weaken1V g) (ρ ,, b) a)
    δ1Eq a = cong (widenŴ sub) (sym (renLsem-coh S ρ (ρ ,, b) (λ _ → refl) g a))
    K'Eq : ∀ (ar1 : ⟦ α ⟧ × R) → K ar1 ≡ mapŴ (proj₂ ar1 +_) (widenŴ sub (Vsem (weaken1V g) (ρ ,, b) (proj₁ ar1) (λ _ → η̂ 0#)))
    K'Eq (a , r1) = cong (λ w → mapŴ (r1 +_) (widenŴ sub w)) (sym (cong (λ f → f a (λ _ → η̂ 0#)) (renV-coh S ρ (ρ ,, b) (λ _ → refl) g)))
  step2 : bind̂ (collectX (φ̂ˢ (promote k nh mH) op (Vsem v ρ) κ δ1)) K
        ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-then sub g))) (val (vvar Z))) (ρ ,, b)) γ
  step2 = trans (tell-0 _)
                (cong (node (promote k nh mH) op 0# (Vsem v ρ))
                      (funext (λ b → trans (cong (λ w → bind̂ w K) (bump-0 (collectX (κ b δ1)))) (bAeq b))))

-- S-glocal: β=ε₁≠εO=ε genuinely (related by sub2:ε₁⊆ᵉε), but promote's
-- own S-glocal clause is a DIRECT application of sub2 (no case-split at
-- all, unlike S-handleB) -- Esem(glocalE...) is likewise γ-constant, and
-- widenŴ's own homomorphism over nodes (widenŴsub(nodemop r oκ)=node
-- (subm)op r o(λa→widenŴsub(κa))) does the rest, no collectX/bump needed.
lemma-B8-S∘-glocal : ∀ {Γ ℓ εH α ε₂ ε₁ ε} (op : Op ℓ) (v : Val Γ (gnd (out op)))
            (k : ContCxt Γ (gnd (in′ op)) εH α ε₁) (sub1 : ε₂ ⊆ᵉ ε₁) (sub2 : ε₁ ⊆ᵉ ε) (g : LC Γ α ε₂) (mH : ℓ ∈ εH) (nh : ¬ Handles k ℓ)
            (ρ : Env Γ) (γ : ⟦ α ⟧ → Ŵ ε R)
          → Esem (glocalE sub1 sub2 (plugK k (opE mH op refl (val v))) g) ρ γ
          ≡ φ̂ˢ (sub2 (promote k nh mH)) op (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-glocal sub1 sub2 g))) (val (vvar Z))) (ρ ,, b)) γ
lemma-B8-S∘-glocal {α = α} {ε₁ = ε₁} op v k sub1 sub2 g mH nh ρ γ = mainStep
  where
  e₀ = plugK k (opE mH op refl (val v))
  δ1 : ⟦ α ⟧ → Ŵ ε₁ R
  δ1 a = widenŴ sub1 (Lsem g ρ a)
  κ : ⟦ in′ op ⟧ᴳ → Ŝ ε₁ ⟦ α ⟧
  κ b = Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, b)
  ih : Esem e₀ ρ δ1 ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) κ δ1
  ih = lemma-B8 op v k mH nh ρ δ1
  bAeq : ∀ (b : ⟦ in′ op ⟧ᴳ) → widenŴ sub2 (κ b δ1) ≡ Esem (plugK (weaken1K (S∘ k (S-glocal sub1 sub2 g))) (val (vvar Z))) (ρ ,, b) γ
  bAeq b = cong (widenŴ sub2) (cong (κ b) (funext δ1Eq))
    where
    δ1Eq : ∀ a → δ1 a ≡ widenŴ sub1 (Lsem (weaken1V g) (ρ ,, b) a)
    δ1Eq a = cong (widenŴ sub1) (sym (renLsem-coh S ρ (ρ ,, b) (λ _ → refl) g a))
  mainStep : widenŴ sub2 (Esem e₀ ρ δ1)
       ≡ φ̂ˢ (sub2 (promote k nh mH)) op (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-glocal sub1 sub2 g))) (val (vvar Z))) (ρ ,, b)) γ
  mainStep = trans (cong (widenŴ sub2) ih) (cong (node (sub2 (promote k nh mH)) op 0# (Vsem v ρ)) (funext bAeq))

-- S-handleB: β=(ε,ℓ ℓ')≠εO=ε genuinely (h's own label ℓ' is DIFFERENT
-- from the operation's label ℓ -- nh's inj₁ component already rules out
-- ℓ≡ℓ', that's exactly promote's own S-handleB clause's own reasoning).
-- Esem(handleE...) goes through the FULL handlerSem/ext̂/handlerΨ
-- machinery, but renH-coh (already proven) supplies exactly the needed
-- "swap the ambient handler for its weakened self" step, and handlerΨ's
-- label-equality dispatch takes the "no" branch here via `neq` (derived
-- directly from nh), landing on
-- EXACTLY `demoteMem`'s own construction -- which promote's own
-- S-handleB clause was ALREADY computing by hand (same ∈-++⁻ split,
-- same nh-derived absurd case), so the two agree definitionally.
-- Bridges promote's own S-handleB clause to demoteMem -- both compute
-- via the SAME `∈-++⁻ ε (promote k nh' mH)` split (nh already rules out
-- the "here" case identically in both), but as separately-elaborated
-- `with`s they don't unify automatically; matching it once, explicitly,
-- here settles both sides at once.
promote-S-handleB-eq : ∀ {Γ ℓ σ εH α ℓ' σ' ε} (k : ContCxt Γ σ εH α (ε ,ℓ ℓ')) (h : Handler Γ ℓ' α σ' ε)
                        (nh : ¬ Handles (S∘ k (S-handleB h)) ℓ) (mH : ℓ ∈ εH)
                     → promote (S∘ k (S-handleB h)) nh mH ≡ demoteMem (promote k (λ hk → nh (inj₂ hk)) mH) (λ eq → nh (inj₁ eq))
promote-S-handleB-eq {ε = ε} k h nh mH with ∈-++⁻ ε (promote k (λ hk → nh (inj₂ hk)) mH)
... | inj₁ m-old       = refl
... | inj₂ (here eq)   = ⊥-elim (nh (inj₁ eq))
... | inj₂ (there ())

lemma-B8-S∘-handleB : ∀ {Γ ℓ εH α ℓ' σ' ε} (op : Op ℓ) (v : Val Γ (gnd (out op)))
            (k : ContCxt Γ (gnd (in′ op)) εH α (ε ,ℓ ℓ')) (h : Handler Γ ℓ' α σ' ε)
            (mH : ℓ ∈ εH) (nh : ¬ Handles (S∘ k (S-handleB h)) ℓ) (ρ : Env Γ) (γ : ⟦ σ' ⟧ → Ŵ ε R)
          → Esem (handleE h (plugK k (opE mH op refl (val v)))) ρ γ
          ≡ φ̂ˢ (promote (S∘ k (S-handleB h)) nh mH) op (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-handleB h))) (val (vvar Z))) (ρ ,, b)) γ
lemma-B8-S∘-handleB {ℓ = ℓ} {α = α} {ℓ' = ℓ'} {ε = ε} op v k h mH nh ρ γ = mainStep
  where
  neq : ¬ (ℓ ≡ ℓ')
  neq eq = nh (inj₁ eq)
  nh' : ¬ Handles k ℓ
  nh' hk = nh (inj₂ hk)
  e₀ = plugK k (opE mH op refl (val v))
  κ : ⟦ in′ op ⟧ᴳ → Ŝ (ε ,ℓ ℓ') ⟦ α ⟧
  κ b = Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, b)
  -- handlerSem's own G-continuation, specialised to THIS call (h, ρ, γ)
  -- -- lemma-B8/φ̂ˢ's node-children need to be instantiated at exactly
  -- this to match what handlerSem h ρ (Esem e₀ ρ) γ actually unfolds to.
  cont0 : ⟦ α ⟧ → Ŵ (ε ,ℓ ℓ') R
  cont0 a = widenŴ ⊆ᵉ-,ℓ (R̂-of (Esem (ret h) (ρ ,, a)) γ)
  ih : Esem e₀ ρ cont0 ≡ φ̂ˢ (promote k nh' mH) op (Vsem v ρ) κ cont0
  ih = lemma-B8 op v k mH nh' ρ cont0
  step1 : Esem (handleE h e₀) ρ γ ≡ ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (φ̂ˢ (promote k nh' mH) op (Vsem v ρ) κ cont0)
  step1 = cong (ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ)) ih
  bAeq : ∀ (b : ⟦ in′ op ⟧ᴳ) → ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (κ b cont0) ≡ Esem (plugK (weaken1K (S∘ k (S-handleB h))) (val (vvar Z))) (ρ ,, b) γ
  bAeq b = sym (renH-coh S ρ (ρ ,, b) (λ _ → refl) h (κ b) γ)
  step3 : ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (φ̂ˢ (promote k nh' mH) op (Vsem v ρ) κ cont0)
        ≡ node (demoteMem (promote k nh' mH) neq) op 0# (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-handleB h))) (val (vvar Z))) (ρ ,, b) γ)
  step3 = trans (tell-0 _)
                (trans (handlerΨ-no-eq h ρ γ (promote k nh' mH) neq op (Vsem v ρ) (λ b → ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (κ b cont0)))
                       (cong (node (demoteMem (promote k nh' mH) neq) op 0# (Vsem v ρ)) (funext bAeq)))
  mainStep : Esem (handleE h e₀) ρ γ
           ≡ φ̂ˢ (promote (S∘ k (S-handleB h)) nh mH) op (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-handleB h))) (val (vvar Z))) (ρ ,, b)) γ
  mainStep = trans (trans step1 step3)
                   (cong (λ m → φ̂ˢ m op (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-handleB h))) (val (vvar Z))) (ρ ,, b)) γ)
                         (sym (promote-S-handleB-eq k h nh mH)))

-- No fk-match: R5's own `fk` construction (below) fills its hole with a
-- bare `val (vvar Z)`, EXACTLY matching lemma-B8's own continuation κ --
-- parameter-free, there is no (par × in) pair to project out of first,
-- so the two constructions that fk-match used to bridge coincide
-- syntactically and need no separate lemma.

lemma-B8-S∘ : ∀ {Γ ℓ εH α β τ εO} (op : Op ℓ) (v : Val Γ (gnd (out op)))
            (k : ContCxt Γ (gnd (in′ op)) εH α β) (s : SFrame Γ α β τ εO) (mH : ℓ ∈ εH) (nh : ¬ Handles (S∘ k s) ℓ)
            (ρ : Env Γ) (γ : ⟦ τ ⟧ → Ŵ εO R)
          → Esem (plugK (S∘ k s) (opE mH op refl (val v))) ρ γ
          ≡ φ̂ˢ (promote (S∘ k s) nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K (S∘ k s)) (val (vvar Z))) (ρ ,, a)) γ
lemma-B8-S∘ op v k S-reset mH nh ρ γ = cong censor (lemma-B8 op v k mH nh ρ γ)
lemma-B8-S∘ op v k (S-then sub g) mH nh ρ γ = lemma-B8-S∘-then op v k sub g mH nh ρ γ
lemma-B8-S∘ op v k (S-glocal sub1 sub2 g) mH nh ρ γ = lemma-B8-S∘-glocal op v k sub1 sub2 g mH nh ρ γ
lemma-B8-S∘ op v k (S-handleB h) mH nh ρ γ = lemma-B8-S∘-handleB op v k h mH nh ρ γ

-- Base case ▫: exactly the (op)(v) clause of Fig. 9, plus the Ŝ unit law.
lemma-B8 op v ▫ mH nh ρ γ = cong (λ F → F γ) (bindˢ-unitˡ (λ a → φ̂ˢ mH op a η̂ˢ) (Vsem v ρ))
lemma-B8 op v (F∘ k f) mH nh ρ γ = lemma-B8-F∘ op v k f mH nh ρ γ
lemma-B8 op v (S∘ k s) mH nh ρ γ = lemma-B8-S∘ op v k s mH nh ρ γ

-- ---------------------------------------------------------------------
-- Theorem 7.9 (hat-Theorem B.9): small-step soundness.
-- "Suppose e:σ!ε and g:σ→loss!ε1 with ε1⊆ε. Then
--    g⊢ε e --r--> e' ⟹ Ssem(e)⌊g⌋ = r·(Ssem(e')⌊g⌋)."
-- By cases on the transition, one clause of Step per source reduction
-- rule. Cases (R1)-(R4),(R6),(R9) never mention Ŵ_ε/Ŝ_ε's internal shape
-- at all (as the source notes) and reduce to η/unit-law manipulation.
-- ---------------------------------------------------------------------

-- ⌊g⌋ abbreviates (the necessarily-widened, since Lsem g ρ : R̂_εg for
-- g's own εg⊆ε, not R̂_ε) loss-continuation γ used throughout: widenŴ
-- sub ∘ Lsem g ρ.
⌊_⌋[_,_] : ∀ {Γ σ ε εg} → LC Γ σ εg → εg ⊆ᵉ ε → Env Γ → ⟦ σ ⟧ → Ŵ ε R
⌊ g ⌋[ sub , ρ ] = λ a → widenŴ sub (Lsem g ρ a)

-- The formalization represents effect contexts as Lists for simplicity,
-- but the source treats them as *sets* of labels: any two witnesses that
-- εg ⊆ᵉ ε are meant to be interchangeable. Several of the Step
-- constructors (F-rule, S1, R5) carry their *own* ⊆ᵉ witness, independent
-- of whatever witness theorem-B9 itself was invoked with for the very same
-- pair (εg, ε) -- provably interchangeable only under a "no duplicate
-- labels in an EffCxt" side-condition the source leaves implicit, so
-- postulated here rather than threading that invariant through the whole
-- development.
postulate
  ⊆ᵉ-irrelevant : ∀ {εg ε X} (sub1 sub2 : εg ⊆ᵉ ε) (w : Ŵ εg X) → widenŴ sub1 w ≡ widenŴ sub2 w

⌊⌋-irrelevant : ∀ {Γ σ ε εg} (g : LC Γ σ εg) (sub1 sub2 : εg ⊆ᵉ ε) (ρ : Env Γ)
              → ⌊ g ⌋[ sub1 , ρ ] ≡ ⌊ g ⌋[ sub2 , ρ ]
⌊⌋-irrelevant g sub1 sub2 ρ = funext (λ a → ⊆ᵉ-irrelevant sub1 sub2 (Lsem g ρ a))

-- WFStep stp ρ: every loss-continuation SYNTACTICALLY introduced
-- anywhere inside stp's own derivation (i.e. every g1 an S2/S3 node
-- carries, at every depth) is RootZero. (F)/(S1)/(S4) just recurse into
-- their own inner step -- they never introduce an INDEPENDENT
-- continuation: (F)/(S1) only ever REBUILD the ambient by wrapping it
-- (RootZero-thenE-wrap already covers that), (S4) reuses the SAME
-- ambient outright. (R1)-(R9)/(R7) have no recursive premise at all, so
-- nothing to require. Needed because S2/S3's own g1 is an INDEPENDENT,
-- arbitrary continuation embedded in the source term via thenE/glocalE
-- -- there is no way to derive RootZero(g1) from RootZero(g) alone, so
-- it has to be supplied as part of what the step derivation carries.
WFStep : ∀ {Γ σ ε εg} {g : LC Γ σ εg} {e e' : Γ ⊢ σ ! ε} {r : R} → g ⊢ e -[ r ]→ e' → Env Γ → Set
WFStep (R1 f x)                   ρ = ⊤
WFStep (R2-pair v w)              ρ = ⊤
WFStep (R2-fst v w)               ρ = ⊤
WFStep (R2-snd v w)               ρ = ⊤
WFStep (R3 e v)                   ρ = ⊤
WFStep (R4 r)                     ρ = ⊤
WFStep (R6 h v2)                  ρ = ⊤
WFStep (R9 v)                     ρ = ⊤
WFStep (R8 sub1 sub2 v g1)        ρ = ⊤
WFStep (R7 sub v e)               ρ = ⊤
WFStep (F-rule sub f stp)         ρ = WFStep stp ρ
WFStep (S1 sub h stp)             ρ = WFStep stp ρ
WFStep (S2 sub g1 stp)            ρ = (∀ a → RootZero (Vsem g1 ρ a (λ _ → η̂ 0#))) × WFStep stp ρ
WFStep (S3 sub1 sub2 g1 stp)      ρ = (∀ a → RootZero (Vsem g1 ρ a (λ _ → η̂ 0#))) × WFStep stp ρ
WFStep (S4 stp)                   ρ = WFStep stp ρ
WFStep (R5 sub h m op v2 k nh)    ρ = ⊤

-- WFBigStep bs ρ: WFStep at every small-step composing the big-step
-- derivation bs. Only meaningful where the big-step derivation is a
-- direct, inspectable argument (Theorem 7.10) -- see the note at
-- theorem-7-11/corollary-7-12 below for why it can't be threaded there.
WFBigStep : ∀ {Γ σ ε εg} {g : LC Γ σ εg} {e w : Γ ⊢ σ ! ε} {r : R} → g ⊢ e ⇒[ r ] w → Env Γ → Set
WFBigStep (done w)      ρ = ⊤
WFBigStep (step stp bs) ρ = WFStep stp ρ × WFBigStep bs ρ

-- Theorem 7.9/B.9's own type, forward-declared so theorem-B9-S3/S4 below
-- can recurse into it directly (on the *given*, structurally smaller step
-- derivation) rather than being separate postulates.
-- RootZero(g) hypothesis added: theorem-B9's own induction is the only
-- place theorem-B9-R5-gen's postulate can be discharged (R5's fl/l1v
-- matching genuinely needs it -- see theorem-B9-R5-WF), so theorem-B9
-- itself now carries it explicitly rather than hiding it behind the
-- postulate. WFStep threads the SAME requirement into (S2)/(S3)'s own
-- independent g1. (F) and (S1) BOTH now recurse into theorem-B9 directly
-- too (not theorem-B9-gen): under the R̂-of-routed handlerSem, (S1)'s own
-- inner continuation is no longer a fixed, g-unrelated constant -- it is
-- (via lemma-B5-3-RootZero, unconditional) exactly ⌊gStar⌋ for
-- gStar = vabs(thenE sub(retApplied h)(weaken1V g)), the SAME g the given
-- step is already indexed by, with RootZero(gStar) following from
-- RootZero(g) via RootZero-thenE-wrap -- so theorem-B9 itself is now
-- ENTIRELY FREE of theorem-B9-R5-gen. The postulate survives only inside
-- theorem-B9-gen's own S2/S3-unrestricted cases (needed for ITS strictly
-- more general, arbitrary-g1 statement -- see the comment above
-- theorem-B9-R5-gen's own postulate) and in the separate
-- theorem-7-10-unrestricted/adequacy path below (a different, harder gap,
-- explicitly out of scope there).
theorem-B9 : ∀ {Γ σ ε εg} (sub : εg ⊆ᵉ ε) {g : LC Γ σ εg} {e e' : Γ ⊢ σ ! ε} {r : R} (stp : g ⊢ e -[ r ]→ e') (ρ : Env Γ)
           → (∀ a → RootZero (Vsem g ρ a (λ _ → η̂ 0#)))
           → WFStep stp ρ
           → Esem e ρ ⌊ g ⌋[ sub , ρ ] ≡ tell r (Esem e' ρ ⌊ g ⌋[ sub , ρ ])

-- (F)'s own type, likewise forward-declared: its body (below, past
-- lemma-B6) recurses into theorem-B9 directly, under the SAME RootZero
-- (g) hypothesis theorem-B9 itself carries.
theorem-B9-F : ∀ {Γ σ ε εg α} (sub : εg ⊆ᵉ ε) {g : LC Γ σ εg} (f : Frame Γ α ε σ ε) {e e' : Γ ⊢ α ! ε} {r : R}
  → (stp : vabs (thenE sub (plugF (weaken1F f) (val (vvar Z))) (weaken1V g)) ⊢ e -[ r ]→ e') → (ρ : Env Γ)
  → (∀ a → RootZero (Vsem g ρ a (λ _ → η̂ 0#))) → WFStep stp ρ
  → Esem (plugF f e) ρ ⌊ g ⌋[ sub , ρ ] ≡ tell r (Esem (plugF f e') ρ ⌊ g ⌋[ sub , ρ ])

-- Two simple facts about how widenŴ/censor commute with tell (both by a
-- direct case split, no induction needed -- neither ever touches a
-- leaf's *payload*, only its root-loss slot).
widenŴ-tell-comm : ∀ {ε ε' X} (sub : ε ⊆ᵉ ε') (r : R) (w : Ŵ ε X) → widenŴ sub (tell r w) ≡ tell r (widenŴ sub w)
widenŴ-tell-comm sub r (leaf r₀ x)        = refl
widenŴ-tell-comm sub r (node m op r₀ o κ) = refl

censor-tell-absorb : ∀ {ε X} (r : R) (w : Ŵ ε X) → censor (tell r w) ≡ censor w
censor-tell-absorb r (leaf r₀ x)        = refl
censor-tell-absorb r (node m op r₀ o κ) = refl

widenŴ-refl : ∀ {ε X} (w : Ŵ ε X) → widenŴ ⊆ᵉ-refl w ≡ w
widenŴ-refl (leaf r x)        = refl
widenŴ-refl (node m op r o κ) = cong (node m op r o) (funext (λ a → widenŴ-refl (κ a)))



-- Lemma 7.5/B.5(1): now purely definitional. R̂-of (Esem e ρ) ⌊g⌋[sub,ρ]
-- unfolds (R̂-of's own new definition) to EXACTLY the same
-- bind̂ (collectX (Esem e ρ γ')) (λ(a,r1)→mapŴ(r1+_)(γ'a)) expression
-- Esem(thenE...)'s own clause computes, since ⌊g⌋[sub,ρ] a and
-- Vsem g ρ a (λ_→η̂0#) already agree via Lsem's own definition -- no
-- RootZero, no induction, no wrapper needed at all.
lemma-B5-1-RootZero : ∀ {Γ σ ε ε₁} (sub : ε₁ ⊆ᵉ ε) (e : Γ ⊢ σ ! ε) (g : LC Γ σ ε₁) (ρ : Env Γ)
                     → Esem (thenE sub e g) ρ ≡ (λ γ1 → R̂-of (Esem e ρ) ⌊ g ⌋[ sub , ρ ])
lemma-B5-1-RootZero sub e g ρ = refl

-- ---------------------------------------------------------------------
-- Lemma 7.5/B.5(2), RootZero-restricted, and read at the canonical zero
-- continuation specifically (`λ_→η̂0#`, exactly what Lsem/Esem(thenE...)
-- ever actually plug into g). The ORIGINAL "for every γ1" phrasing is a SEPARATE,
-- stronger claim -- that a value's own Ŝ-denotation never depends on
-- which continuation it's run at -- which is false in general whenever g
-- reaches a `handleE`: a handler's own clause genuinely inspects its
-- ambient loss continuation (handlerΨ's own `l1v`, Denotational.agda),
-- so a DIFFERENT γ1 can make g's own Vsem pick a structurally different
-- tree. RootZero(g) (a fact about ONE fixed tree) says nothing about
-- that. So only the canonical-continuation instance is proved here --
-- which is also the only instance anything else in this file ever needs.
-- ---------------------------------------------------------------------

-- Lemma 7.5/B.5(2), fixed for the collapse-free semantics. Now that
-- `Lsem g ρ a` is DEFINED as `Vsem g ρ a (λ_→η̂0#)` (Denotational.agda),
-- with no `collapse` roundtrip left to bridge, the equation is
-- definitional -- RootZero(g) isn't even needed for the proof itself
-- (kept as a hypothesis only to match the original B.5(2) shape / in
-- case a future caller wants it documented alongside the fact).
lemma-B5-2-RootZero : ∀ {Γ σ ε} (g : LC Γ σ ε) (ρ : Env Γ) (a : ⟦ σ ⟧)
                     → RootZero (Vsem g ρ a (λ _ → η̂ 0#))
                     → Lsem g ρ a ≡ Vsem g ρ a (λ _ → η̂ 0#)
lemma-B5-2-RootZero g ρ a rz = refl

-- Lemma 7.5/B.5(3): now that R̂-of itself routes through collectX/mapŴ
-- (Domains.agda), lemma-B5-1-RootZero already relates Esem(thenE...) to
-- R̂-of directly, with no wrapper and no RootZero hypothesis needed --
-- and this is the exact same fact, applied at Lsem/Vsem(vabs _)'s own
-- canonical continuation (λ_→η̂0#): Lsem(vabs(thenE sub e g))ρx unfolds
-- definitionally to Esem(thenE sub e g)(ρ,,x)(λ_→η̂0#).
lemma-B5-3-RootZero : ∀ {Γ σ α ε ε₁} (sub : ε₁ ⊆ᵉ ε) (e : (Γ , σ) ⊢ α ! ε) (g : LC (Γ , σ) α ε₁)
                     (ρ : Env Γ) (x : ⟦ σ ⟧)
                   → Lsem (vabs (thenE sub e g)) ρ x ≡ R̂-of (Esem e (ρ ,, x)) ⌊ g ⌋[ sub , (ρ ,, x) ]
lemma-B5-3-RootZero sub e g ρ x = refl

-- (F) is proven directly, uniformly across EVERY regular frame shape (no
-- case-split needed at all, not even the old value-transport/op/
-- companion-bearing split): lemma-B5-3-RootZero is now unconditional
-- (true for ANY e, not just a bare value transport), so combined with
-- Lemma B.6 (likewise unconditional for every Frame constructor) it
-- settles Lemma 7.7/B.7 in full generality. See theorem-B9-F-gen's own
-- proof below (uniform across f already) and theorem-B9-F-companion
-- further down, which specialises it and IS theorem-B9-F's own body.
-- ---------------------------------------------------------------------
-- theorem-B9-gen / theorem-B9-F-gen: theorem-B9's conclusion GENERALISED
-- to hold at an ARBITRARY continuation γ:⟦σ⟧→Ŵε R, not just the specific
-- ⌊g⌋[sub,ρ] built from the given step's own ambient g.
--
-- Motivation: theorem-B9-F's companion-bearing cases (F-pairL etc.) need
-- to relate two continuations for e's own evaluation -- the D built from
-- Esem(pair e e₂)ργ's own bind̂ˢ-unfolding, and δ:=Lsem(g*)ρ (what
-- theorem-B9's IH is stated at). If theorem-B9 holds at ANY γ, we can
-- apply the IH DIRECTLY at γ:=D -- no bridge between D and δ needed, and
-- (as the proof below shows) no case-split on the frame's own shape
-- either: it works identically for every regular frame lemma-B6 covers.
--
-- Every OpSem-*active* clause (thenE, glocalE, lossE) ignores its own λγ
-- argument entirely (ONLY consults its embedded ambient's own Lsem, at
-- a fixed δ'=λ_→η̂0#) -- so (R4), (R7), (S2), (S3) each end up proving
-- an equation between two γ-CONSTANT expressions: the generalisation
-- costs nothing, it's the SAME proof term with γ renamed throughout.
-- (S4) threads the SAME outer γ into its own recursive call unchanged,
-- so it also generalises for free. Only (S1) and (R5) are genuinely
-- γ-dependent, through handleE's own non-thenE-shaped clause (its own
-- bind̂ˢ threads γ down to the SECOND/body argument, not lemma-B6's
-- position) -- kept as (correspondingly generalised) postulates.
-- ---------------------------------------------------------------------

theorem-B9-gen : ∀ {Γ σ ε εg} {g : LC Γ σ εg} {e e' : Γ ⊢ σ ! ε} {r : R}
                → g ⊢ e -[ r ]→ e' → (ρ : Env Γ) (γ : ⟦ σ ⟧ → Ŵ ε R)
                → Esem e ρ γ ≡ tell r (Esem e' ρ γ)

theorem-B9-F-gen : ∀ {Γ σ ε εg α} (sub : εg ⊆ᵉ ε) {g : LC Γ σ εg} (f : Frame Γ α ε σ ε) {e e' : Γ ⊢ α ! ε} {r : R}
  → vabs (thenE sub (plugF (weaken1F f) (val (vvar Z))) (weaken1V g)) ⊢ e -[ r ]→ e' → (ρ : Env Γ) (γ : ⟦ σ ⟧ → Ŵ ε R)
  → Esem (plugF f e) ρ γ ≡ tell r (Esem (plugF f e') ρ γ)

-- handlerAlg h ρ γ's own carrier is Ŵ ε ⟦σ'⟧ directly (parameter-free:
-- no ⟦par⟧-exponent), with act = tell -- exactly Ŵ-alg's own act (which
-- is what makes tell-bind̂-comm hold). Same two-case proof, since neither
-- leaf nor node case of ext̂ ever inspects act beyond this shape, and
-- tell only ever touches a tree's own root-loss field (never m/op/o/κ),
-- so the node case's ψ-built branches are identical on both sides.
handlerAlg-tell-comm : ∀ {Γ ℓ σ σ' ε X} (h : Handler Γ ℓ σ σ' ε) (ρ : Env Γ) (γ : ⟦ σ' ⟧ → Ŵ ε R)
  (f : X → Ŵ ε ⟦ σ' ⟧) (r : R) (W : Ŵ (ε ,ℓ ℓ) X)
  → ext̂ (handlerAlg h ρ γ) f (tell r W) ≡ tell r (ext̂ (handlerAlg h ρ γ) f W)
handlerAlg-tell-comm h ρ γ f r (leaf r₀ x) = tell-+ r r₀ (f x)
handlerAlg-tell-comm h ρ γ f r (node m op r₀ o κ) =
  tell-+ r r₀ (handlerΨ h ρ γ m op o (λ a → ext̂ (handlerAlg h ρ γ) f (κ a)))

-- theorem-B9-S1-gen, PROVEN (not postulated): unfold Esem(handleE h e)ργ
-- (now purely definitional -- handleE has a single hole, no e1 to
-- bindˢ-unitˡ through) down to ext̂(handlerAlghργ)(handlerRethργ)(EsemeρD)
-- for the continuation D e's own evaluation is ALREADY forced by
-- handlerSem's definition to receive -- apply theorem-B9-gen directly at
-- γ:=D (no relation to the given step's own compound ambient
-- vabs(thenE...) needed at all), then push tell r out with
-- handlerAlg-tell-comm instead of tell-bind̂-comm.
theorem-B9-S1-gen : ∀ {Γ ε εamb ℓ σ σ'} (sub : εamb ⊆ᵉ ε) {g : LC Γ σ' εamb} (h : Handler Γ ℓ σ σ' ε)
    {e e' : Γ ⊢ σ ! (ε ,ℓ ℓ)} {r : R}
    → vabs (thenE sub (retApplied h) (weaken1V g)) ⊢ e -[ r ]→ e' → (ρ : Env Γ) (γ : ⟦ σ' ⟧ → Ŵ ε R)
    → Esem (handleE h e) ρ γ ≡ tell r (Esem (handleE h e') ρ γ)
theorem-B9-S1-gen {ε = ε} {ℓ = ℓ} {σ = σ} {σ' = σ'} sub {g} h {e} {e'} {r} stp ρ γ =
  trans step1 (trans step3 step5)
  where
  -- handlerSem's own continuation for the handled body (Denotational.agda):
  -- the loss `ret h` would report on a returned value `a`, run against
  -- the OUTER γ and widened up into the body's own (ε,ℓ ℓ) context.
  cont : ⟦ σ ⟧ → Ŵ (ε ,ℓ ℓ) R
  cont a = widenŴ ⊆ᵉ-,ℓ (R̂-of (Esem (ret h) (ρ ,, a)) γ)
  ih : Esem e ρ cont ≡ tell r (Esem e' ρ cont)
  ih = theorem-B9-gen stp ρ cont
  step1 : Esem (handleE h e) ρ γ ≡ ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (Esem e ρ cont)
  step1 = refl
  step3 : ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (Esem e ρ cont)
        ≡ tell r (ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (Esem e' ρ cont))
  step3 = trans (cong (ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ)) ih)
                (handlerAlg-tell-comm h ρ γ (handlerRet h ρ γ) r (Esem e' ρ cont))
  step5 : tell r (ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (Esem e' ρ cont)) ≡ tell r (Esem (handleE h e') ρ γ)
  step5 = refl

-- Generalised (R5): postulated. EffCxt is explicitly a MULTISET
-- (Domains.agda's own comment on `_,ℓ_`: "extend ε by one further
-- (freshly introduced, 'outermost') copy of ℓ" -- nested handlers for
-- the SAME effect label are a legitimate, intended scenario), and
-- handlerΨ dispatches on the operation's LABEL EQUALITY (ℓ1 ≟ᵉ ℓ) rather
-- than on the membership witness's own position, matching R5's own
-- operational rule (which never inspects the witness beyond
-- `¬ Handles k ℓ`).
--
-- At a fully arbitrary continuation γ (independent of the ambient loss
-- continuation g), this statement is genuinely false: a handler clause
-- that reports its own choice continuation's value via lossE before
-- resuming can make handlerSem's result depend on which of two
-- unrelated continuations it is run against -- not an edge case, but the
-- exact mechanism the selection-monad framework exists for (confirmed by
-- a concrete counterexample in this project's history: a clause leaking
-- through a non-RootZero g gives 25 on one side, 32 on the other). This
-- is NOT a defect in theorem-B9 itself: theorem-B9's own R5 case (below)
-- goes through theorem-B9-R5-WF directly -- a REAL proof, specialised to
-- γ := ⌊g⌋[sub,ρ] with g PROVEN RootZero, matching R5's own reified
-- continuations fk/fl against the handler algebra's k1v/l1v via
-- fk-match/lemma-fl-l1v-match -- and (as of the RootZero-thenE-wrap
-- argument above) neither do theorem-B9-F/theorem-B9-S1 reach this
-- postulate anymore either. It remains needed ONLY for theorem-B9-gen's
-- own S2/S3-unrestricted cases, whose g1 is a genuinely arbitrary,
-- independent continuation with no RootZero obligation available (see
-- the comment above theorem-B9-S2-gen-unrestricted) -- and for the
-- separate theorem-7-10-unrestricted/adequacy path further below.
postulate
  theorem-B9-R5-gen : ∀ {Γ ε εamb ℓ σ σ' εop} (sub : εamb ⊆ᵉ ε) {g : LC Γ σ' εamb}
    (h : Handler Γ ℓ σ σ' ε) (m : ℓ ∈ εop) (op : Op ℓ) (v2 : Val Γ (gnd (out op)))
    (k : ContCxt Γ (gnd (in′ op)) εop σ (ε ,ℓ ℓ)) (nh : ¬ Handles k ℓ) (ρ : Env Γ) (γ : ⟦ σ' ⟧ → Ŵ ε R) → let
      h' = renH S h ; g' = renV S g ; k' = weaken1K k
      handled = handleE h' (plugK k' (val (vvar Z)))
      fk = vabs {σ = gnd (in′ op)} (glocalE sub ⊆ᵉ-refl handled g')
      fl = vabs {σ = gnd (in′ op)} (thenE sub handled g')
    in Esem (handleE h (plugK k (opE m op refl (val v2)))) ρ γ
     ≡ tell 0# (Esem (subE (cons fk (cons fl (cons v2 idSub))) (clause h op)) ρ γ)

-- (R7), generalised: both sides turn out to be γ-CONSTANT (thenE/
-- glocalE both ignore their own λγ, only ever consulting their embedded
-- ambient at δ'=λ_→η̂0#), so the equation reduces, on both sides, to
-- tell0#(widenŴsub(Esem(e[v])ρδ')).
theorem-B9-R7-gen : ∀ {Γ ε εg σ} (sub : εg ⊆ᵉ ε) (v : Val Γ σ) (e : (Γ , σ) ⊢ Loss ! εg) (ρ : Env Γ) (γ : ⟦ Loss ⟧ → Ŵ ε R)
  → Esem (thenE sub (val v) (vabs e)) ρ γ ≡ tell 0# (Esem (glocalE ⊆ᵉ-refl sub (e [ v ]) zeroLC) ρ γ)
theorem-B9-R7-gen sub v e ρ γ = trans lhsEq (sym rhsEq)
  where
  δ' : R → Ŵ _ R
  δ' = λ _ → η̂ 0#

  step0 : Esem (thenE sub (val v) (vabs e)) ρ γ ≡ tell 0# (mapŴ (0# +_) (widenŴ sub (Esem e (ρ ,, Vsem v ρ) δ')))
  step0 = refl

  step1 : tell 0# (mapŴ (0# +_) (widenŴ sub (Esem e (ρ ,, Vsem v ρ) δ'))) ≡ tell 0# (widenŴ sub (Esem e (ρ ,, Vsem v ρ) δ'))
  step1 = cong (tell 0#) (mapŴ-plus-0 (widenŴ sub (Esem e (ρ ,, Vsem v ρ) δ')))

  step2 : tell 0# (widenŴ sub (Esem e (ρ ,, Vsem v ρ) δ')) ≡ tell 0# (widenŴ sub (Esem (e [ v ]) ρ δ'))
  step2 = cong (λ w → tell 0# (widenŴ sub w)) (sym (cong (λ F → F δ') (sub1-coh e ρ v)))

  lhsEq : Esem (thenE sub (val v) (vabs e)) ρ γ ≡ tell 0# (widenŴ sub (Esem (e [ v ]) ρ δ'))
  lhsEq = trans step0 (trans step1 step2)

  γ0-eq : (λ (a : R) → widenŴ ⊆ᵉ-refl (Lsem (zeroLC {σ = Loss}) ρ a)) ≡ δ'
  γ0-eq = funext (λ a → widenŴ-refl (η̂ 0#))

  rhsEq : tell 0# (Esem (glocalE ⊆ᵉ-refl sub (e [ v ]) zeroLC) ρ γ) ≡ tell 0# (widenŴ sub (Esem (e [ v ]) ρ δ'))
  rhsEq = cong (λ F → tell 0# (widenŴ sub (Esem (e [ v ]) ρ F))) γ0-eq

-- theorem-B9-S2-gen, with the added requirement that g1 be RootZero:
-- Gg1 = ⌊g1⌋[sub,ρ] is EXACTLY theorem-B9's own conclusion at g:=g1, so
-- the recursive step needs no bridging at all -- ih is just
-- theorem-B9 sub stp ρ rzg1 directly, bypassing theorem-B9-gen entirely.
-- CONSEQUENCE: theorem-B9-gen's own S2 case can no longer delegate here
-- (it must keep working for an ARBITRARY g1, since g1 is an independent
-- syntactic continuation embedded in the user's own term via thenE --
-- there is no way to establish RootZero(g1) in general, unlike gStar in
-- the (F)/(S4) cases, which is BUILT by wrapping an already-RootZero g).
-- theorem-B9-gen's coverage is repaired below by giving its own S2 case
-- a private copy of the ORIGINAL, unrestricted proof.
theorem-B9-S2-gen : ∀ {Γ ε εg} (sub : εg ⊆ᵉ ε) (g1 : LC Γ Loss εg) {e e' : Γ ⊢ Loss ! ε} {r : R}
  → (stp : g1 ⊢ e -[ r ]→ e') → (ρ : Env Γ) (γ : ⟦ Loss ⟧ → Ŵ ε R)
  → (∀ a → RootZero (Vsem g1 ρ a (λ _ → η̂ 0#))) → WFStep stp ρ
  → Esem (thenE sub e g1) ρ γ
  ≡ tell 0# (Esem (thenE ⊆ᵉ-refl (lossE (val (vgnd r))) (vabs (weaken1 (thenE sub e' g1)))) ρ γ)
theorem-B9-S2-gen sub g1 {e} {e'} {r} stp ρ γ rzg1 wfstp = trans step1 (sym (tell-0 _))
  where
  Gg1 : ⟦ Loss ⟧ → Ŵ _ R
  Gg1 = ⌊ g1 ⌋[ sub , ρ ]

  h : ⟦ Loss ⟧ → R → Ŵ _ R
  h a r1 = mapŴ (r1 +_) (widenŴ sub (Vsem g1 ρ a (λ _ → η̂ 0#)))

  ih : Esem e ρ Gg1 ≡ tell r (Esem e' ρ Gg1)
  ih = theorem-B9 sub stp ρ rzg1 wfstp

  hShift : ∀ a r1 → h a (r + r1) ≡ mapŴ (r +_) (h a r1)
  hShift a r1 = trans (cong (λ f → mapŴ f (widenŴ sub (Vsem g1 ρ a (λ _ → η̂ 0#)))) (funext (+-assoc r r1)))
                       (sym (mapŴ-∘ (r +_) (r1 +_) (widenŴ sub (Vsem g1 ρ a (λ _ → η̂ 0#)))))

  lhsStep : Esem (thenE sub e g1) ρ γ
          ≡ mapŴ (r +_) (bind̂ (collectX (Esem e' ρ Gg1)) (λ { (a , r1) → h a r1 }))
  lhsStep = trans (cong (λ w → bind̂ (collectX w) (λ { (a , r1) → h a r1 })) ih)
                  (trans (cong (λ w → bind̂ w (λ { (a , r1) → h a r1 })) (sym (bump-collectX-comm r (Esem e' ρ Gg1))))
                         (trans (bump-shift r (collectX (Esem e' ρ Gg1)) h)
                                (trans (cong (bind̂ (collectX (Esem e' ρ Gg1))) (funext (λ { (a , r1) → hShift a r1 })))
                                       (bind̂-mapŴ-after (collectX (Esem e' ρ Gg1)) (λ { (a , r1) → h a r1 }) (r +_)))))

  T : Ŵ _ ⟦ Loss ⟧
  T = bind̂ (collectX (Esem e' ρ Gg1)) (λ { (a , r1) → h a r1 })

  H'tt-eq : widenŴ ⊆ᵉ-refl (Esem (weaken1 (thenE sub e' g1)) (ρ ,, tt) (λ _ → η̂ 0#)) ≡ T
  H'tt-eq = trans (cong (λ F → widenŴ ⊆ᵉ-refl (F (λ _ → η̂ 0#))) (weaken1-coh UnitTy (thenE sub e' g1) ρ tt)) (widenŴ-refl T)

  rhsStep : Esem (thenE ⊆ᵉ-refl (lossE (val (vgnd r))) (vabs (weaken1 (thenE sub e' g1)))) ρ γ
          ≡ mapŴ (r +_) T
  rhsStep =
    trans (cong (λ z → tell 0# (mapŴ (z +_) (widenŴ ⊆ᵉ-refl (Esem (weaken1 (thenE sub e' g1)) (ρ ,, tt) (λ _ → η̂ 0#)))))
                (trans (cong (0# +_) (+-identityʳ r)) (+-identityˡ r)))
          (trans (cong (λ w → tell 0# (mapŴ (r +_) w)) H'tt-eq)
                 (tell-0 _))

  step1 : Esem (thenE sub e g1) ρ γ
        ≡ Esem (thenE ⊆ᵉ-refl (lossE (val (vgnd r))) (vabs (weaken1 (thenE sub e' g1)))) ρ γ
  step1 = trans lhsStep (sym rhsStep)

-- theorem-B9-gen's own S2 case: needs the ORIGINAL, unrestricted proof
-- (g1 arbitrary, no RootZero), since it must stay total over every
-- possible g1 the Step type's own S2 constructor could ever carry --
-- an exact copy of theorem-B9-S2-gen's own pre-RootZero body, just
-- recursing via theorem-B9-gen (not theorem-B9) for the arbitrary case.
theorem-B9-S2-gen-unrestricted : ∀ {Γ ε εg} (sub : εg ⊆ᵉ ε) (g1 : LC Γ Loss εg) {e e' : Γ ⊢ Loss ! ε} {r : R}
  → g1 ⊢ e -[ r ]→ e' → (ρ : Env Γ) (γ : ⟦ Loss ⟧ → Ŵ ε R)
  → Esem (thenE sub e g1) ρ γ
  ≡ tell 0# (Esem (thenE ⊆ᵉ-refl (lossE (val (vgnd r))) (vabs (weaken1 (thenE sub e' g1)))) ρ γ)
theorem-B9-S2-gen-unrestricted sub g1 {e} {e'} {r} stp ρ γ = trans step1 (sym (tell-0 _))
  where
  Gg1 : ⟦ Loss ⟧ → Ŵ _ R
  Gg1 = ⌊ g1 ⌋[ sub , ρ ]

  h : ⟦ Loss ⟧ → R → Ŵ _ R
  h a r1 = mapŴ (r1 +_) (widenŴ sub (Vsem g1 ρ a (λ _ → η̂ 0#)))

  ih : Esem e ρ Gg1 ≡ tell r (Esem e' ρ Gg1)
  ih = theorem-B9-gen stp ρ Gg1

  hShift : ∀ a r1 → h a (r + r1) ≡ mapŴ (r +_) (h a r1)
  hShift a r1 = trans (cong (λ f → mapŴ f (widenŴ sub (Vsem g1 ρ a (λ _ → η̂ 0#)))) (funext (+-assoc r r1)))
                       (sym (mapŴ-∘ (r +_) (r1 +_) (widenŴ sub (Vsem g1 ρ a (λ _ → η̂ 0#)))))

  lhsStep : Esem (thenE sub e g1) ρ γ
          ≡ mapŴ (r +_) (bind̂ (collectX (Esem e' ρ Gg1)) (λ { (a , r1) → h a r1 }))
  lhsStep = trans (cong (λ w → bind̂ (collectX w) (λ { (a , r1) → h a r1 })) ih)
                  (trans (cong (λ w → bind̂ w (λ { (a , r1) → h a r1 })) (sym (bump-collectX-comm r (Esem e' ρ Gg1))))
                         (trans (bump-shift r (collectX (Esem e' ρ Gg1)) h)
                                (trans (cong (bind̂ (collectX (Esem e' ρ Gg1))) (funext (λ { (a , r1) → hShift a r1 })))
                                       (bind̂-mapŴ-after (collectX (Esem e' ρ Gg1)) (λ { (a , r1) → h a r1 }) (r +_)))))

  T : Ŵ _ ⟦ Loss ⟧
  T = bind̂ (collectX (Esem e' ρ Gg1)) (λ { (a , r1) → h a r1 })

  H'tt-eq : widenŴ ⊆ᵉ-refl (Esem (weaken1 (thenE sub e' g1)) (ρ ,, tt) (λ _ → η̂ 0#)) ≡ T
  H'tt-eq = trans (cong (λ F → widenŴ ⊆ᵉ-refl (F (λ _ → η̂ 0#))) (weaken1-coh UnitTy (thenE sub e' g1) ρ tt)) (widenŴ-refl T)

  rhsStep : Esem (thenE ⊆ᵉ-refl (lossE (val (vgnd r))) (vabs (weaken1 (thenE sub e' g1)))) ρ γ
          ≡ mapŴ (r +_) T
  rhsStep =
    trans (cong (λ z → tell 0# (mapŴ (z +_) (widenŴ ⊆ᵉ-refl (Esem (weaken1 (thenE sub e' g1)) (ρ ,, tt) (λ _ → η̂ 0#)))))
                (trans (cong (0# +_) (+-identityʳ r)) (+-identityˡ r)))
          (trans (cong (λ w → tell 0# (mapŴ (r +_) w)) H'tt-eq)
                 (tell-0 _))

  step1 : Esem (thenE sub e g1) ρ γ
        ≡ Esem (thenE ⊆ᵉ-refl (lossE (val (vgnd r))) (vabs (weaken1 (thenE sub e' g1)))) ρ γ
  step1 = trans lhsStep (sym rhsStep)

-- theorem-B9-S3-gen, with the added requirement that g1 be RootZero
-- (mirroring theorem-B9-S2-gen above): ⌊g1⌋[sub1,ρ] is exactly
-- theorem-B9's own conclusion at g:=g1, sub:=sub1, so the recursive step
-- goes through theorem-B9 directly rather than theorem-B9-gen.
-- CONSEQUENCE: theorem-B9-gen's own S3 case can no longer delegate here
-- (g1 is an independent, arbitrary continuation embedded via glocalE) --
-- repaired below via a private, unrestricted copy.
theorem-B9-S3-gen : ∀ {Γ ε ε₂ ε₁ σ} (sub1 : ε₂ ⊆ᵉ ε₁) (sub2 : ε₁ ⊆ᵉ ε) (g1 : LC Γ σ ε₂)
    {e e' : Γ ⊢ σ ! ε₁} {r : R}
  → (stp : g1 ⊢ e -[ r ]→ e') → (ρ : Env Γ) (γ : ⟦ σ ⟧ → Ŵ ε R)
  → (∀ a → RootZero (Vsem g1 ρ a (λ _ → η̂ 0#))) → WFStep stp ρ
  → Esem (glocalE sub1 sub2 e g1) ρ γ ≡ tell r (Esem (glocalE sub1 sub2 e' g1) ρ γ)
theorem-B9-S3-gen sub1 sub2 g1 stp ρ γ rzg1 wfstp =
  trans (cong (widenŴ sub2) (theorem-B9 sub1 stp ρ rzg1 wfstp)) (widenŴ-tell-comm sub2 _ _)

theorem-B9-S3-gen-unrestricted : ∀ {Γ ε ε₂ ε₁ σ} (sub1 : ε₂ ⊆ᵉ ε₁) (sub2 : ε₁ ⊆ᵉ ε) (g1 : LC Γ σ ε₂)
    {e e' : Γ ⊢ σ ! ε₁} {r : R}
  → g1 ⊢ e -[ r ]→ e' → (ρ : Env Γ) (γ : ⟦ σ ⟧ → Ŵ ε R)
  → Esem (glocalE sub1 sub2 e g1) ρ γ ≡ tell r (Esem (glocalE sub1 sub2 e' g1) ρ γ)
theorem-B9-S3-gen-unrestricted sub1 sub2 g1 stp ρ γ =
  trans (cong (widenŴ sub2) (theorem-B9-gen stp ρ ⌊ g1 ⌋[ sub1 , ρ ])) (widenŴ-tell-comm sub2 _ _)

theorem-B9-S4-gen : ∀ {Γ ε εg σ} {g : LC Γ σ εg} {e e' : Γ ⊢ σ ! ε} {r : R}
  → g ⊢ e -[ r ]→ e' → (ρ : Env Γ) (γ : ⟦ σ ⟧ → Ŵ ε R)
  → Esem (resetE e) ρ γ ≡ tell 0# (Esem (resetE e') ρ γ)
theorem-B9-S4-gen stp ρ γ =
  trans (cong censor (theorem-B9-gen stp ρ γ)) (trans (censor-tell-absorb _ _) (sym (tell-0 _)))

-- theorem-B9-F-gen's own proof: UNIFORM across every regular frame (no
-- case-split on f at all) -- lemma-B6 (already unconditional for every
-- constructor of Frame) turns Esem(plugFfe)ρ into bind̂ˢH(Esemeρ) for a
-- FIXED H (independent of e/e'/stp); apply the (arbitrary-γ) IH directly
-- at D:=λa→R̂-of(Ha)γ -- the continuation e's own evaluation is ALREADY
-- forced to receive by bind̂ˢ's definition -- then push tell r out with
-- tell-bind̂-comm. No mini-B7-style reasoning needed at all.
theorem-B9-F-gen {σ = σ} {ε = ε} {α = α} sub {g} f {e} {e'} {r} stp ρ γ = trans step1 (trans step2 step3)
  where
  H : ⟦ α ⟧ → Ŝ ε ⟦ σ ⟧
  H a = Esem (plugF (weaken1F f) (val (vvar Z))) (ρ ,, a)
  b6 : Esem (plugF f e) ρ ≡ bind̂ˢ H (Esem e ρ)
  b6 = lemma-B6 f e ρ
  b6' : Esem (plugF f e') ρ ≡ bind̂ˢ H (Esem e' ρ)
  b6' = lemma-B6 f e' ρ
  D : ⟦ α ⟧ → Ŵ ε R
  D a = R̂-of (H a) γ
  ih : Esem e ρ D ≡ tell r (Esem e' ρ D)
  ih = theorem-B9-gen stp ρ D
  step1 : Esem (plugF f e) ρ γ ≡ bind̂ (Esem e ρ D) (λ a → H a γ)
  step1 = cong (λ F → F γ) b6
  step2 : bind̂ (Esem e ρ D) (λ a → H a γ) ≡ tell r (bind̂ (Esem e' ρ D) (λ a → H a γ))
  step2 = trans (cong (λ w → bind̂ w (λ a → H a γ)) ih) (tell-bind̂-comm r (Esem e' ρ D) (λ a → H a γ))
  step3 : tell r (bind̂ (Esem e' ρ D) (λ a → H a γ)) ≡ tell r (Esem (plugF f e') ρ γ)
  step3 = cong (tell r) (sym (cong (λ F → F γ) b6'))

-- theorem-B9-gen's own proof: identical case-by-case content to
-- theorem-B9's below (each case re-derived at an arbitrary γ instead of
-- ⌊g⌋[sub,ρ] -- see the block comment above for why each one generalises
-- for free), delegating the frame/handler/then/glocal/reset cases to the
-- lemmas just proven/postulated above.
theorem-B9-gen (R1 f x) ρ γ = trans
  (cong (λ F → F γ) (bindˢ-unitˡ (λ a → η̂ˢ (⟦ f ⟧f a)) x))
  (sym (tell-0 (leaf 0# (⟦ f ⟧f x))))
theorem-B9-gen (R2-pair v w) ρ γ =
  trans (cong (λ F → F γ) pairEq) (sym (tell-0 (leaf 0# (Vsem v ρ , Vsem w ρ))))
  where
  pairEq : Esem (pair (val v) (val w)) ρ ≡ η̂ˢ (Vsem v ρ , Vsem w ρ)
  pairEq = trans (bindˢ-unitˡ (λ a → bind̂ˢ (λ b → η̂ˢ (a , b)) (η̂ˢ (Vsem w ρ))) (Vsem v ρ))
                 (bindˢ-unitˡ (λ b → η̂ˢ (Vsem v ρ , b)) (Vsem w ρ))
theorem-B9-gen (R2-fst {σ = σ} {τ = τ} v w) ρ γ =
  trans (cong (λ F → F γ) fstEqS) (sym (tell-0 (leaf 0# (Vsem v ρ))))
  where
  fstEqS : Esem (fst (val (vpair v w))) ρ ≡ η̂ˢ (Vsem v ρ)
  fstEqS = bindˢ-unitˡ {X = ⟦ σ ⟧ × ⟦ τ ⟧} (λ{ (a , b) → η̂ˢ a }) (Vsem v ρ , Vsem w ρ)
theorem-B9-gen (R2-snd {σ = σ} {τ = τ} v w) ρ γ =
  trans (cong (λ F → F γ) sndEqS) (sym (tell-0 (leaf 0# (Vsem w ρ))))
  where
  sndEqS : Esem (snd (val (vpair v w))) ρ ≡ η̂ˢ (Vsem w ρ)
  sndEqS = bindˢ-unitˡ {X = ⟦ σ ⟧ × ⟦ τ ⟧} (λ{ (a , b) → η̂ˢ b }) (Vsem v ρ , Vsem w ρ)
theorem-B9-gen (R3 e v) ρ γ = trans step1 (trans step2 (sym (tell-0 (Esem (e [ v ]) ρ γ))))
  where
  step1 : Esem (app (val (vabs e)) (val v)) ρ γ ≡ Esem e (ρ ,, Vsem v ρ) γ
  step1 = trans (cong (λ F → F γ) (bindˢ-unitˡ (λ φ → bind̂ˢ (λ a → φ a) (η̂ˢ (Vsem v ρ))) (Vsem (vabs e) ρ)))
                (cong (λ F → F γ) (bindˢ-unitˡ (λ a → Vsem (vabs e) ρ a) (Vsem v ρ)))
  step2 : Esem e (ρ ,, Vsem v ρ) γ ≡ Esem (e [ v ]) ρ γ
  step2 = sym (cong (λ F → F γ) (sub1-coh e ρ v))
theorem-B9-gen (R4 r) ρ γ = tell-0 (tell r (η̂ tt))
theorem-B9-gen (R6 h v2) ρ γ = trans step1 (sym (tell-0 (Esem (subE (cons v2 idSub) (ret h)) ρ γ)))
  where
  step1 : Esem (handleE h (val v2)) ρ γ ≡ Esem (subE (cons v2 idSub) (ret h)) ρ γ
  step1 = subst2-step
    where
    subst2-step : tell 0# (Esem (ret h) (ρ ,, Vsem v2 ρ) γ) ≡ Esem (subE (cons v2 idSub) (ret h)) ρ γ
    subst2-step = trans (tell-0 _) (sym (cong (λ F → F γ)
      (subE-coh (cons v2 idSub) ρ (ρ ,, Vsem v2 ρ) subcoh (ret h))))
      where
      subcoh : SubCoh (cons v2 idSub) ρ (ρ ,, Vsem v2 ρ)
      subcoh Z     = refl
      subcoh (S x) = refl
theorem-B9-gen (R9 v) ρ γ = sym (tell-0 (leaf 0# (Vsem v ρ)))
theorem-B9-gen (R8 sub1 sub2 v g1) ρ γ = sym (tell-0 (leaf 0# (Vsem v ρ)))
theorem-B9-gen (R7 sub' v e) ρ γ = theorem-B9-R7-gen sub' v e ρ γ
theorem-B9-gen (F-rule sub' f stp) ρ γ = theorem-B9-F-gen sub' f stp ρ γ
theorem-B9-gen (S1 sub' h stp) ρ γ = theorem-B9-S1-gen sub' h stp ρ γ
theorem-B9-gen (S2 sub' g1 stp) ρ γ = theorem-B9-S2-gen-unrestricted sub' g1 stp ρ γ
theorem-B9-gen (S3 sub1 sub2 g1 stp) ρ γ = theorem-B9-S3-gen-unrestricted sub1 sub2 g1 stp ρ γ
theorem-B9-gen (S4 stp) ρ γ = theorem-B9-S4-gen stp ρ γ
theorem-B9-gen (R5 sub' h m op v2 k nh) ρ γ = theorem-B9-R5-gen sub' h m op v2 k nh ρ γ

-- theorem-B9-F, proven directly via the REAL theorem-B9 (not
-- theorem-B9-gen), under the SAME RootZero(g) hypothesis theorem-B9
-- itself now carries. Possible because lemma-B5-3-RootZero is
-- unconditional: gStar's own Lsem, δ, equals R̂-of(H a)γ directly (no
-- bridging assumption needed, unlike the old, deleted miniB7-value/
-- theorem-B9-F-value-transport, which needed H to be a bare value
-- transport specifically). RootZero(g) transfers to RootZero(gStar) via
-- RootZero-thenE-wrap, so the recursive call goes through theorem-B9
-- directly -- theorem-B9-gen/theorem-B9-F-gen (and hence
-- theorem-B9-R5-gen) are no longer needed on this path at all.
theorem-B9-F {σ = σ} {α = α} sub {g} f {e} {e'} {r} stp ρ rzg wfstp = trans step1 (trans step2 step3)
  where
  H : ⟦ α ⟧ → Ŝ _ ⟦ σ ⟧
  H a = Esem (plugF (weaken1F f) (val (vvar Z))) (ρ ,, a)
  γ = ⌊ g ⌋[ sub , ρ ]
  gStar = vabs (thenE sub (plugF (weaken1F f) (val (vvar Z))) (weaken1V g))
  δ = Lsem gStar ρ

  D-eq : ∀ a → δ a ≡ R̂-of (H a) γ
  D-eq a = trans (lemma-B5-3-RootZero sub (plugF (weaken1F f) (val (vvar Z))) (weaken1V g) ρ a)
                 (cong (R̂-of (H a)) γ'-eq)
    where
    γ'-eq : ⌊ weaken1V g ⌋[ sub , (ρ ,, a) ] ≡ γ
    γ'-eq = funext (λ c → cong (widenŴ sub) (renLsem-coh S ρ (ρ ,, a) (λ x → refl) g c))

  rzg' : ∀ a b → RootZero (Vsem (weaken1V g) (ρ ,, a) b (λ _ → η̂ 0#))
  rzg' a b = subst RootZero (sym (cong (λ F → F b (λ _ → η̂ 0#)) (weaken1V-coh _ g ρ a))) (rzg b)

  rzgStar : ∀ a → RootZero (Vsem gStar ρ a (λ _ → η̂ 0#))
  rzgStar a = RootZero-thenE-wrap sub (plugF (weaken1F f) (val (vvar Z))) (weaken1V g) ρ a (λ _ → η̂ 0#) (rzg' a)

  ih : Esem e ρ δ ≡ tell r (Esem e' ρ δ)
  ih = trans (cong (Esem e ρ) (funext (λ a → sym (widenŴ-refl (Lsem gStar ρ a)))))
             (trans (theorem-B9 ⊆ᵉ-refl stp ρ rzgStar wfstp)
                    (cong (λ F → tell r (Esem e' ρ F)) (funext (λ a → widenŴ-refl (Lsem gStar ρ a)))))

  b6 : Esem (plugF f e) ρ ≡ bind̂ˢ H (Esem e ρ)
  b6 = lemma-B6 f e ρ
  b6' : Esem (plugF f e') ρ ≡ bind̂ˢ H (Esem e' ρ)
  b6' = lemma-B6 f e' ρ

  step1 : Esem (plugF f e) ρ γ ≡ bind̂ (Esem e ρ δ) (λ a → H a γ)
  step1 = trans (cong (λ F → F γ) b6) (cong (λ F → bind̂ (Esem e ρ F) (λ a → H a γ)) (sym (funext D-eq)))
  step2 : bind̂ (Esem e ρ δ) (λ a → H a γ) ≡ tell r (bind̂ (Esem e' ρ δ) (λ a → H a γ))
  step2 = trans (cong (λ w → bind̂ w (λ a → H a γ)) ih) (tell-bind̂-comm r (Esem e' ρ δ) (λ a → H a γ))
  step3 : tell r (bind̂ (Esem e' ρ δ) (λ a → H a γ)) ≡ tell r (Esem (plugF f e') ρ γ)
  step3 = cong (tell r) (trans (cong (λ F → bind̂ (Esem e' ρ F) (λ a → H a γ)) (funext D-eq)) (sym (cong (λ F → F γ) b6')))

-- theorem-B9-S2/S3/S4: each recurses on its OWN inner g1 (S2, S3) or the
-- SAME g (S4), via theorem-B9-gen (arbitrary γ) rather than theorem-B9
-- itself -- g1 is independent of the outer g and not known RootZero
-- (thenE/glocalE's own g1 can be any user-written loss-continuation), so
-- only theorem-B9-gen's unconditional generality applies here. Direct
-- corollaries of theorem-B9-S2-gen/-S3-gen/-S4-gen, specialised to
-- γ := ⌊g⌋[subamb,ρ] (S2, S3) or ⌊g⌋[sub,ρ] (S4).
theorem-B9-S2 : ∀ {Γ ε εg εamb} (sub : εg ⊆ᵉ ε) {g : LC Γ Loss εamb} (subamb : εamb ⊆ᵉ ε) (g1 : LC Γ Loss εg) {e e' : Γ ⊢ Loss ! ε} {r : R}
  → (stp : g1 ⊢ e -[ r ]→ e') → (ρ : Env Γ)
  → (∀ a → RootZero (Vsem g1 ρ a (λ _ → η̂ 0#))) → WFStep stp ρ
  → Esem (thenE sub e g1) ρ ⌊ g ⌋[ subamb , ρ ]
  ≡ tell 0# (Esem (thenE ⊆ᵉ-refl (lossE (val (vgnd r))) (vabs (weaken1 (thenE sub e' g1)))) ρ ⌊ g ⌋[ subamb , ρ ])
theorem-B9-S2 sub {g} subamb g1 stp ρ rzg1 wfstp = theorem-B9-S2-gen sub g1 stp ρ ⌊ g ⌋[ subamb , ρ ] rzg1 wfstp

theorem-B9-S3 : ∀ {Γ ε ε₂ ε₁ σ} (sub1 : ε₂ ⊆ᵉ ε₁) (sub2 : ε₁ ⊆ᵉ ε) {εamb} (subamb : εamb ⊆ᵉ ε) {g : LC Γ σ εamb} (g1 : LC Γ σ ε₂)
    {e e' : Γ ⊢ σ ! ε₁} {r : R}
  → (stp : g1 ⊢ e -[ r ]→ e') → (ρ : Env Γ)
  → (∀ a → RootZero (Vsem g1 ρ a (λ _ → η̂ 0#))) → WFStep stp ρ
  → Esem (glocalE sub1 sub2 e g1) ρ ⌊ g ⌋[ subamb , ρ ] ≡ tell r (Esem (glocalE sub1 sub2 e' g1) ρ ⌊ g ⌋[ subamb , ρ ])
theorem-B9-S3 sub1 sub2 subamb {g} g1 stp ρ rzg1 wfstp = theorem-B9-S3-gen sub1 sub2 g1 stp ρ ⌊ g ⌋[ subamb , ρ ] rzg1 wfstp

-- theorem-B9-S4's given step is at the SAME g theorem-B9-S4 itself is
-- stated for (resetE's own step never rebuilds the ambient), so unlike
-- S2/S3 (whose g1 is an independent, arbitrary continuation) this can
-- reuse theorem-B9 directly, no RootZero-thenE-wrap bridging needed.
theorem-B9-S4 : ∀ {Γ ε εg σ} {g : LC Γ σ εg} {e e' : Γ ⊢ σ ! ε} {r : R}
  → (stp : g ⊢ e -[ r ]→ e') → (ρ : Env Γ) (sub : εg ⊆ᵉ ε)
  → (∀ a → RootZero (Vsem g ρ a (λ _ → η̂ 0#))) → WFStep stp ρ
  → Esem (resetE e) ρ ⌊ g ⌋[ sub , ρ ] ≡ tell 0# (Esem (resetE e') ρ ⌊ g ⌋[ sub , ρ ])
theorem-B9-S4 {g = g} stp ρ sub rzg wfstp =
  trans (cong censor (theorem-B9 sub stp ρ rzg wfstp)) (trans (censor-tell-absorb _ _) (sym (tell-0 _)))

-- (F), (S1), (R5), (R7): the remaining frame/context-manipulating cases.
-- Unlike (S2)/(S3)/(S4) above, each of these has its *given* step stated
-- under a captured continuation vabs(thenE sub ...) that is a NEW, more
-- complex continuation than the ambient g theorem-B9 itself is stated
-- for. (R7) is discharged via the arbitrary-γ generalisation above
-- (theorem-B9-R7-gen), specialised here to γ := ⌊g⌋[sub,ρ]. (F) and (S1)
-- are proven DIRECTLY via the real theorem-B9 (not theorem-B9-gen/-F-gen/
-- -S1-gen), exactly like theorem-B9-F above: gStar's own Lsem equals
-- R̂-of(...)γ definitionally (lemma-B5-3-RootZero, unconditional), and
-- RootZero(g) transfers to RootZero(gStar) via RootZero-thenE-wrap, so
-- neither needs theorem-B9-gen (hence theorem-B9-R5-gen) at all. (R5) is
-- the one case that genuinely needs the outer g itself directly (via
-- theorem-B9-R5-WF, below), since fk/fl embed g directly.
theorem-B9-S1 : ∀ {Γ ε εamb ℓ σ σ'} (sub : εamb ⊆ᵉ ε) {g : LC Γ σ' εamb} (h : Handler Γ ℓ σ σ' ε)
    {e e' : Γ ⊢ σ ! (ε ,ℓ ℓ)} {r : R}
  → (stp : vabs (thenE sub (retApplied h) (weaken1V g)) ⊢ e -[ r ]→ e') → (ρ : Env Γ)
  → (∀ a → RootZero (Vsem g ρ a (λ _ → η̂ 0#))) → WFStep stp ρ
  → Esem (handleE h e) ρ ⌊ g ⌋[ sub , ρ ] ≡ tell r (Esem (handleE h e') ρ ⌊ g ⌋[ sub , ρ ])
theorem-B9-S1 {ε = ε} {ℓ = ℓ} {σ = σ} sub {g} h {e} {e'} {r} stp ρ rzg wfstp = trans step1 (trans step3 step5)
  where
  γ = ⌊ g ⌋[ sub , ρ ]
  cont : ⟦ σ ⟧ → Ŵ (ε ,ℓ ℓ) R
  cont a = widenŴ ⊆ᵉ-,ℓ (R̂-of (Esem (ret h) (ρ ,, a)) γ)

  gStar = vabs (thenE sub (retApplied h) (weaken1V g))
  δ = Lsem gStar ρ

  D-eq : ∀ a → δ a ≡ R̂-of (Esem (ret h) (ρ ,, a)) γ
  D-eq a = trans (lemma-B5-3-RootZero sub (retApplied h) (weaken1V g) ρ a)
                 (cong (R̂-of (Esem (ret h) (ρ ,, a))) γ'-eq)
    where
    γ'-eq : ⌊ weaken1V g ⌋[ sub , (ρ ,, a) ] ≡ γ
    γ'-eq = funext (λ c → cong (widenŴ sub) (renLsem-coh S ρ (ρ ,, a) (λ x → refl) g c))

  cont-eq : ∀ a → widenŴ ⊆ᵉ-,ℓ (δ a) ≡ cont a
  cont-eq a = cong (widenŴ ⊆ᵉ-,ℓ) (D-eq a)

  rzg' : ∀ a b → RootZero (Vsem (weaken1V g) (ρ ,, a) b (λ _ → η̂ 0#))
  rzg' a b = subst RootZero (sym (cong (λ F → F b (λ _ → η̂ 0#)) (weaken1V-coh _ g ρ a))) (rzg b)

  rzgStar : ∀ a → RootZero (Vsem gStar ρ a (λ _ → η̂ 0#))
  rzgStar a = RootZero-thenE-wrap sub (retApplied h) (weaken1V g) ρ a (λ _ → η̂ 0#) (rzg' a)

  ih : Esem e ρ cont ≡ tell r (Esem e' ρ cont)
  ih = trans (sym (cong (Esem e ρ) (funext cont-eq)))
             (trans (theorem-B9 ⊆ᵉ-,ℓ stp ρ rzgStar wfstp)
                    (cong (λ F → tell r (Esem e' ρ F)) (funext cont-eq)))

  step1 : Esem (handleE h e) ρ γ ≡ ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (Esem e ρ cont)
  step1 = refl
  step3 : ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (Esem e ρ cont)
        ≡ tell r (ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (Esem e' ρ cont))
  step3 = trans (cong (ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ)) ih)
                (handlerAlg-tell-comm h ρ γ (handlerRet h ρ γ) r (Esem e' ρ cont))
  step5 : tell r (ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (Esem e' ρ cont)) ≡ tell r (Esem (handleE h e') ρ γ)
  step5 = refl

theorem-B9-R7 : ∀ {Γ ε εg εamb σ} (sub : εg ⊆ᵉ ε) {g : LC Γ Loss εamb} (subamb : εamb ⊆ᵉ ε)
  (v : Val Γ σ) (e : (Γ , σ) ⊢ Loss ! εg) (ρ : Env Γ)
  → Esem (thenE sub (val v) (vabs e)) ρ ⌊ g ⌋[ subamb , ρ ]
  ≡ tell 0# (Esem (glocalE ⊆ᵉ-refl sub (e [ v ]) zeroLC) ρ ⌊ g ⌋[ subamb , ρ ])
theorem-B9-R7 sub {g} subamb v e ρ = theorem-B9-R7-gen sub v e ρ ⌊ g ⌋[ subamb , ρ ]

-- theorem-B9-R5-WF: theorem-B9's own R5 case (below) calls this
-- directly, supplying the RootZero(g) hypothesis theorem-B9 itself now
-- carries -- theorem-B9-R5-gen (genuinely false at a fully arbitrary
-- continuation, see the comment above its own postulate) is no longer
-- needed on this path. Provable under RootZero(g) because both matching
-- halves of the fk/fl-vs-k1v/l1v argument close: fkMatch (fk/k1v,
-- unconditional -- parameter-free, fk's own body is syntactically
-- identical to lemma-B8's κ, so no separate bridging lemma is even
-- needed) and flMatch/lemma-fl-l1v-match (fl/l1v, needing RootZero(g))
-- above. theorem-B9-R5-gen remains postulated only for theorem-B9-gen's
-- own S2/S3-unrestricted cases (an arbitrary, independent g1 with no
-- RootZero obligation available -- (F) and (S1) BOTH now recurse into
-- theorem-B9 directly instead, see the comment above theorem-B9's own
-- signature) and for the separate theorem-7-10-unrestricted/adequacy
-- path further below.
RootZero-mapŴ-sum-bump : ∀ {ε} (r1 : R) (D : Ŵ ε R) → RootZero D
  → mapŴ (λ { (x , r2) → x + r2 }) (bump r1 (collectX D)) ≡ mapŴ (r1 +_) D
RootZero-mapŴ-sum-bump r1 (leaf r0 v) rz =
  cong₂ leaf (sym rz) (trans (cong (λ z → v + (r1 + z)) rz)
                             (trans (cong (v +_) (+-identityʳ r1)) (+-comm v r1)))
RootZero-mapŴ-sum-bump r1 (node m op r0 o κ) (rz , rzκ) =
  trans (cong (node m op 0# o) (funext childEq))
        (cong (λ z → node m op z o (λ b → mapŴ (r1 +_) (κ b))) (sym rz))
  where
  h = λ { (x , r2) → x + r2 }
  childEq : ∀ b → mapŴ h (bump r1 (bump r0 (collectX (κ b)))) ≡ mapŴ (r1 +_) (κ b)
  childEq b = trans (cong (mapŴ h) (bump-fusion r1 r0 (collectX (κ b))))
                    (trans (cong (λ z → mapŴ h (bump z (collectX (κ b))))
                                 (trans (cong (r1 +_) rz) (+-identityʳ r1)))
                           (RootZero-mapŴ-sum-bump r1 (κ b) (rzκ b)))

-- bind̂'s own root contribution and collectX's redistribution commute via
-- collectX-bind̂-fusion/bind̂-mapŴ-after (both from Domains.ŴMonad,
-- unconditional); only the final per-leaf step needs g's own leaves to
-- be RootZero (RootZero-mapŴ-sum-bump, above), to sum rather than
-- discard a component.
lemma-fl-l1v-match : ∀ {ε X} (W : Ŵ ε X) (δ' : X → Ŵ ε R) → (∀ x → RootZero (δ' x))
  → mapŴ (λ { (x , r1) → x + r1 }) (collectX (bind̂ W δ'))
  ≡ bind̂ (collectX W) (λ { (x , r1) → mapŴ (r1 +_) (δ' x) })
lemma-fl-l1v-match W δ' rzδ' =
  trans (cong (mapŴ h) (collectX-bind̂-fusion W δ'))
        (trans (sym (bind̂-mapŴ-after (collectX W) (λ { (x , r1) → bump r1 (collectX (δ' x)) }) h))
               (cong (bind̂ (collectX W))
                     (funext (λ { (x , r1) → RootZero-mapŴ-sum-bump r1 (δ' x) (rzδ' x) }))))
  where
  h = λ { (x , r1) → x + r1 }

-- Parameter-free: no more (par × in) pairing, no more "outer p1 vs a
-- fresh resume p''" dimension for fk/fl to diverge on -- fkMatch/flMatch
-- below hold UNCONDITIONALLY (fkMatch previously needed the separate
-- fk-match lemma to bridge R5's pair-projecting `fk` against lemma-B8's
-- unary κ; here they're syntactically the same construction).
theorem-B9-R5-WF : ∀ {Γ ε εamb ℓ σ σ' εop} (sub : εamb ⊆ᵉ ε) {g : LC Γ σ' εamb}
    (h : Handler Γ ℓ σ σ' ε) (m : ℓ ∈ εop) (op : Op ℓ) (v2 : Val Γ (gnd (out op)))
    (k : ContCxt Γ (gnd (in′ op)) εop σ (ε ,ℓ ℓ)) (nh : ¬ Handles k ℓ) (ρ : Env Γ)
    (rzg : ∀ a → RootZero (Vsem g ρ a (λ _ → η̂ 0#))) → let
      h' = renH S h ; g' = renV S g ; k' = weaken1K k
      handled = handleE h' (plugK k' (val (vvar Z)))
      fk = vabs {σ = gnd (in′ op)} (glocalE sub ⊆ᵉ-refl handled g')
      fl = vabs {σ = gnd (in′ op)} (thenE sub handled g')
    in Esem (handleE h (plugK k (opE m op refl (val v2)))) ρ ⌊ g ⌋[ sub , ρ ]
     ≡ tell 0# (Esem (subE (cons fk (cons fl (cons v2 idSub))) (clause h op)) ρ ⌊ g ⌋[ sub , ρ ])
theorem-B9-R5-WF {Γ} {ε} {εamb} {ℓ} {σ} {σ'} {εop} sub {g} h m op v2 k nh ρ rzg =
  trans (trans step1 step2) (trans step3 (sym (tell-0 _)))
  where
  h' = renH S h ; g' = renV S g ; k' = weaken1K k
  handled = handleE h' (plugK k' (val (vvar Z)))
  fk = vabs {σ = gnd (in′ op)} (glocalE sub ⊆ᵉ-refl handled g')
  fl = vabs {σ = gnd (in′ op)} (thenE sub handled g')

  γ : ⟦ σ' ⟧ → Ŵ ε R
  γ = ⌊ g ⌋[ sub , ρ ]
  κ : ⟦ in′ op ⟧ᴳ → Ŝ (ε ,ℓ ℓ) ⟦ σ ⟧
  κ a = Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, a)
  -- handlerSem's own G-continuation, specialised to THIS call (h, ρ, γ)
  -- -- lemma-B8/φ̂ˢ's node-children (and hence K', the k-continuation
  -- handlerΨ's "yes" clause is applied at) need to be instantiated at
  -- exactly this to match what handlerSem h ρ (Esem (plugK k (opE m op
  -- (val v2))) ρ) γ actually unfolds to.
  cont1 : ⟦ σ ⟧ → Ŵ (ε ,ℓ ℓ) R
  cont1 a = widenŴ ⊆ᵉ-,ℓ (R̂-of (Esem (ret h) (ρ ,, a)) γ)
  K' : ⟦ in′ op ⟧ᴳ → Ŵ ε ⟦ σ' ⟧
  K' a = ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (κ a cont1)

  clauseEnv : Env (((Γ , gnd (out op)) , (gnd (in′ op) ⇒ Loss ! ε)) , (gnd (in′ op) ⇒ σ' ! ε))
  clauseEnv = ((ρ ,, Vsem v2 ρ) ,, (λ a γ1 → mapŴ (λ { (r1 , r2) → r1 + r2 }) (collectX (ext̂ Ŵ-alg γ (K' a))))) ,, (λ a γ' → K' a)

  step1 : Esem (handleE h (plugK k (opE m op refl (val v2)))) ρ γ
        ≡ tell 0# (handlerΨ h ρ γ (promote k nh m) op (Vsem v2 ρ) K')
  step1 = cong (ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ)) (lemma-B8 op v2 k m nh ρ cont1)

  step2 : tell 0# (handlerΨ h ρ γ (promote k nh m) op (Vsem v2 ρ) K')
        ≡ Esem (clause h op) clauseEnv γ
  step2 = trans (tell-0 _) (handlerΨ-yes-eq h ρ γ (promote k nh m) op (Vsem v2 ρ) K')

  -- Bridges handled's own evaluation (under ANY ambient γ0) to a fresh
  -- handlerSem call -- a bare weaken1H-coh now, no more fk-match bridge.
  handled-eq : ∀ (a : ⟦ in′ op ⟧ᴳ) (γ0 : ⟦ σ' ⟧ → Ŵ ε R)
             → Esem handled (ρ ,, a) γ0 ≡ handlerSem h ρ (κ a) γ0
  handled-eq a γ0 = weaken1H-coh (gnd (in′ op)) h ρ a (κ a) γ0

  δ-eq : ∀ (a : ⟦ in′ op ⟧ᴳ) → (λ (b : ⟦ σ' ⟧) → widenŴ sub (Lsem g' (ρ ,, a) b)) ≡ γ
  δ-eq a = funext (λ b → cong (widenŴ sub) (cong (λ f → f b (λ _ → η̂ 0#)) (weaken1V-coh (gnd (in′ op)) g ρ a)))

  fkMatch : ∀ (a : ⟦ in′ op ⟧ᴳ) (γ' : ⟦ σ' ⟧ → Ŵ ε R) → Vsem fk ρ a γ' ≡ K' a
  fkMatch a γ' =
    trans (widenŴ-refl (Esem handled (ρ ,, a) (λ b → widenŴ sub (Lsem g' (ρ ,, a) b))))
          (trans (handled-eq a (λ b → widenŴ sub (Lsem g' (ρ ,, a) b)))
                 (cong (λ γ0 → handlerSem h ρ (κ a) γ0) (δ-eq a)))

  Gv : ⟦ σ' ⟧ → Ŵ ε R
  Gv b = widenŴ sub (Vsem g ρ b (λ _ → η̂ 0#))

  Gv-eq : ∀ (a : ⟦ in′ op ⟧ᴳ) (b : ⟦ σ' ⟧)
        → widenŴ sub (Vsem g' (ρ ,, a) b (λ _ → η̂ 0#)) ≡ Gv b
  Gv-eq a b = cong widenŴ' (cong (λ f → f b (λ _ → η̂ 0#)) (weaken1V-coh (gnd (in′ op)) g ρ a))
    where widenŴ' = widenŴ sub

  flMatch : ∀ (a : ⟦ in′ op ⟧ᴳ) (γ1 : ⟦ Loss ⟧ → Ŵ ε R)
          → Vsem fl ρ a γ1 ≡ mapŴ (λ { (r1 , r2) → r1 + r2 }) (collectX (ext̂ Ŵ-alg γ (K' a)))
  flMatch a γ1 = trans (trans stepA (trans stepB stepC)) stepE
    where
    δ : ⟦ σ' ⟧ → Ŵ ε R
    δ b = widenŴ sub (Lsem g' (ρ ,, a) b)
    combine : Ŵ ε ⟦ σ' ⟧ → Ŵ ε R
    combine w = bind̂ (collectX w) (λ { (b , r1) → mapŴ (r1 +_) (widenŴ sub (Vsem g' (ρ ,, a) b (λ _ → η̂ 0#))) })

    stepA : Vsem fl ρ a γ1 ≡ combine (Esem handled (ρ ,, a) δ)
    stepA = refl

    stepB : combine (Esem handled (ρ ,, a) δ) ≡ combine (handlerSem h ρ (κ a) δ)
    stepB = cong combine (handled-eq a δ)

    stepC : combine (handlerSem h ρ (κ a) δ) ≡ bind̂ (collectX (K' a)) (λ { (b , r1) → mapŴ (r1 +_) (Gv b) })
    stepC = trans (cong (λ γ0 → combine (handlerSem h ρ (κ a) γ0)) (δ-eq a))
                  (cong (bind̂ (collectX (K' a))) (funext (λ { (b , r1) → cong (mapŴ (r1 +_)) (Gv-eq a b) })))

    -- γ ≡ Gv definitionally (both unfold to widenŴ sub ∘ Vsem g ρ ∘
    -- (λ_→η̂0#)), so no collapse-based bridging is needed.
    stepE : bind̂ (collectX (K' a)) (λ { (b , r1) → mapŴ (r1 +_) (Gv b) }) ≡ mapŴ (λ { (r1 , r2) → r1 + r2 }) (collectX (ext̂ Ŵ-alg γ (K' a)))
    stepE = sym (lemma-fl-l1v-match (K' a) Gv (λ b → RootZero-widenŴ sub (Vsem g ρ b (λ _ → η̂ 0#)) (rzg b)))

  step3 : Esem (clause h op) clauseEnv γ ≡ Esem (subE (cons fk (cons fl (cons v2 idSub))) (clause h op)) ρ γ
  step3 = sym (cong (λ F → F γ) (subE-coh (cons fk (cons fl (cons v2 idSub))) ρ clauseEnv subcoh (clause h op)))
    where
    subcoh : SubCoh (cons fk (cons fl (cons v2 idSub))) ρ clauseEnv
    subcoh Z             = funext (λ a → funext (fkMatch a))
    subcoh (S Z)         = funext (λ a → funext (flMatch a))
    subcoh (S (S Z))     = refl
    subcoh (S (S (S x))) = refl

-- theorem-B9-R5-WF, but with γ supplied explicitly, together with a
-- proof that it agrees with ⌊g⌋[sub,ρ] -- i.e. exactly the "missing
-- assumption linking γ and Gv" that theorem-B9-R5-gen lacks. A one-line
-- corollary of theorem-B9-R5-WF (rewrite along γ-eq both ways), NOT a
-- new proof. This does NOT let theorem-B9-gen's own R5 case drop the
-- postulate, though: that case is a single proof term valid for every
-- γ theorem-B9-gen might ever be called at, and theorem-B9-F-gen's own
-- call (γ := λa→R̂-of(Ha)γ₀, built from a companion subexpression, not
-- from any loss-continuation's Lsem) has no g to link γ to at all -- no
-- γ-eq could ever be supplied there, linked-hypothesis or not. Recorded
-- here to make precise exactly what's missing, not to close the gap.
theorem-B9-R5-gen-WF : ∀ {Γ ε εamb ℓ σ σ' εop} (sub : εamb ⊆ᵉ ε) {g : LC Γ σ' εamb}
    (h : Handler Γ ℓ σ σ' ε) (m : ℓ ∈ εop) (op : Op ℓ) (v2 : Val Γ (gnd (out op)))
    (k : ContCxt Γ (gnd (in′ op)) εop σ (ε ,ℓ ℓ)) (nh : ¬ Handles k ℓ) (ρ : Env Γ) (γ : ⟦ σ' ⟧ → Ŵ ε R)
    (γ-eq : γ ≡ ⌊ g ⌋[ sub , ρ ]) (rzg : ∀ a → RootZero (Vsem g ρ a (λ _ → η̂ 0#))) → let
      h' = renH S h ; g' = renV S g ; k' = weaken1K k
      handled = handleE h' (plugK k' (val (vvar Z)))
      fk = vabs {σ = gnd (in′ op)} (glocalE sub ⊆ᵉ-refl handled g')
      fl = vabs {σ = gnd (in′ op)} (thenE sub handled g')
    in Esem (handleE h (plugK k (opE m op refl (val v2)))) ρ γ
     ≡ tell 0# (Esem (subE (cons fk (cons fl (cons v2 idSub))) (clause h op)) ρ γ)
theorem-B9-R5-gen-WF sub {g} h m op v2 k nh ρ γ γ-eq rzg =
  trans (cong (λ z → Esem (handleE h (plugK k (opE m op refl (val v2)))) ρ z) γ-eq)
        (trans (theorem-B9-R5-WF sub h m op v2 k nh ρ rzg)
               (cong (λ z → tell 0# (Esem (subE (cons fk (cons fl (cons v2 idSub))) (clause h op)) ρ z)) (sym γ-eq)))
  where
  h' = renH S h ; g' = renV S g ; k' = weaken1K k
  handled = handleE h' (plugK k' (val (vvar Z)))
  fk = vabs {σ = gnd (in′ op)} (glocalE sub ⊆ᵉ-refl handled g')
  fl = vabs {σ = gnd (in′ op)} (thenE sub handled g')

-- (R1) f(v) → v'
theorem-B9 sub {g} (R1 f x) ρ _ _ = trans
  (cong (λ F → F ⌊ g ⌋[ sub , ρ ]) (bindˢ-unitˡ (λ a → η̂ˢ (⟦ f ⟧f a)) x))
  (sym (tell-0 (leaf 0# (⟦ f ⟧f x))))

-- (R2a) (v1,v2) → vpair(v1,v2)
theorem-B9 sub {g} (R2-pair v w) ρ _ _ =
  trans (cong (λ F → F ⌊ g ⌋[ sub , ρ ]) pairEq) (sym (tell-0 (leaf 0# (Vsem v ρ , Vsem w ρ))))
  where
  pairEq : Esem (pair (val v) (val w)) ρ ≡ η̂ˢ (Vsem v ρ , Vsem w ρ)
  pairEq = trans (bindˢ-unitˡ (λ a → bind̂ˢ (λ b → η̂ˢ (a , b)) (η̂ˢ (Vsem w ρ))) (Vsem v ρ))
                 (bindˢ-unitˡ (λ b → η̂ˢ (Vsem v ρ , b)) (Vsem w ρ))

-- (R2) vpair(v1,v2).i → vi
theorem-B9 sub {g} (R2-fst {σ = σ} {τ = τ} v w) ρ _ _ =
  trans (cong (λ F → F ⌊ g ⌋[ sub , ρ ]) fstEqS) (sym (tell-0 (leaf 0# (Vsem v ρ))))
  where
  fstEqS : Esem (fst (val (vpair v w))) ρ ≡ η̂ˢ (Vsem v ρ)
  fstEqS = bindˢ-unitˡ {X = ⟦ σ ⟧ × ⟦ τ ⟧} (λ{ (a , b) → η̂ˢ a }) (Vsem v ρ , Vsem w ρ)

theorem-B9 sub {g} (R2-snd {σ = σ} {τ = τ} v w) ρ _ _ =
  trans (cong (λ F → F ⌊ g ⌋[ sub , ρ ]) sndEqS) (sym (tell-0 (leaf 0# (Vsem w ρ))))
  where
  sndEqS : Esem (snd (val (vpair v w))) ρ ≡ η̂ˢ (Vsem w ρ)
  sndEqS = bindˢ-unitˡ {X = ⟦ σ ⟧ × ⟦ τ ⟧} (λ{ (a , b) → η̂ˢ b }) (Vsem v ρ , Vsem w ρ)

-- (R3) (λ^ε x:σ.e) v → e[v/x]
theorem-B9 sub {g} (R3 e v) ρ _ _ = trans step1 (trans step2 (sym (tell-0 (Esem (e [ v ]) ρ γ))))
  where
  γ = ⌊ g ⌋[ sub , ρ ]
  step1 : Esem (app (val (vabs e)) (val v)) ρ γ ≡ Esem e (ρ ,, Vsem v ρ) γ
  step1 = trans (cong (λ F → F γ) (bindˢ-unitˡ (λ φ → bind̂ˢ (λ a → φ a) (η̂ˢ (Vsem v ρ))) (Vsem (vabs e) ρ)))
                (cong (λ F → F γ) (bindˢ-unitˡ (λ a → Vsem (vabs e) ρ a) (Vsem v ρ)))
  step2 : Esem e (ρ ,, Vsem v ρ) γ ≡ Esem (e [ v ]) ρ γ
  step2 = sym (cong (λ F → F γ) (sub1-coh e ρ v))

-- (R4) loss(r) → ()
theorem-B9 sub (R4 r) ρ _ _ = tell-0 (tell r (η̂ tt))

-- (R6) with h handle v2 → vr(v2)
theorem-B9 sub {g} (R6 h v2) ρ _ _ = trans step1 (sym (tell-0 (Esem (subE (cons v2 idSub) (ret h)) ρ γ)))
  where
  γ = ⌊ g ⌋[ sub , ρ ]
  step1 : Esem (handleE h (val v2)) ρ γ ≡ Esem (subE (cons v2 idSub) (ret h)) ρ γ
  step1 = subst2-step
    where
    -- Esem(handleE h(val v2))ργ = tell 0# (handlerRet h ρ γ (Vsem v2 ρ))
    -- by definition (handlerSem's leaf case), and Esem(ret h)(ρ,,a)γ *is*
    -- handlerRet h ρ γ a by definition, so with a := Vsem v2 ρ, the only
    -- gap to the substitution subE (cons v2 idSub) (ret h) is coherence.
    subst2-step : tell 0# (Esem (ret h) (ρ ,, Vsem v2 ρ) γ) ≡ Esem (subE (cons v2 idSub) (ret h)) ρ γ
    subst2-step = trans (tell-0 _) (sym (cong (λ F → F γ)
      (subE-coh (cons v2 idSub) ρ (ρ ,, Vsem v2 ρ) subcoh (ret h))))
      where
      subcoh : SubCoh (cons v2 idSub) ρ (ρ ,, Vsem v2 ρ)
      subcoh Z     = refl
      subcoh (S x) = refl

-- (R9) reset v → v
theorem-B9 sub {g} (R9 v) ρ _ _ = sym (tell-0 (leaf 0# (Vsem v ρ)))

-- (R8) ⟨v⟩^ε₁_g1 → v
theorem-B9 sub {g} (R8 sub1 sub2 v g1) ρ _ _ = sym (tell-0 (leaf 0# (Vsem v ρ)))

-- (R7) v ▶ λ^εg x:σ.e → ⟨e[v/x]⟩^εg_{λ^εg x:σ.0}
theorem-B9 sub {g} (R7 sub' v e) ρ _ _ = theorem-B9-R7 sub' {g = g} sub v e ρ

theorem-B9 sub {g} {e} {e'} {r} (F-rule sub' f stp) ρ rzg wfstp =
  trans (cong (Esem e ρ) (⌊⌋-irrelevant g sub sub' ρ))
        (trans (theorem-B9-F sub' f stp ρ rzg wfstp)
               (cong (λ F → tell r (Esem e' ρ F)) (sym (⌊⌋-irrelevant g sub sub' ρ))))
theorem-B9 sub {g} {e} {e'} {r} (S1 sub' h stp) ρ rzg wfstp =
  trans (cong (Esem e ρ) (⌊⌋-irrelevant g sub sub' ρ))
        (trans (theorem-B9-S1 sub' h stp ρ rzg wfstp)
               (cong (λ F → tell r (Esem e' ρ F)) (sym (⌊⌋-irrelevant g sub sub' ρ))))
theorem-B9 sub {g} (S2 sub' g1 stp) ρ _ (rzg1 , wfstp) = theorem-B9-S2 sub' {g = g} sub g1 stp ρ rzg1 wfstp
theorem-B9 sub {g} (S3 sub1 sub2 g1 stp) ρ _ (rzg1 , wfstp) = theorem-B9-S3 sub1 sub2 sub {g = g} g1 stp ρ rzg1 wfstp
theorem-B9 sub {g} (S4 stp) ρ rzg wfstp = theorem-B9-S4 {g = g} stp ρ sub rzg wfstp
theorem-B9 sub {g} (R5 sub' h m op v2 k nh) ρ rzg _ =
  trans (cong (Esem (handleE h (plugK k (opE m op refl (val v2)))) ρ) (⌊⌋-irrelevant g sub sub' ρ))
        (trans (theorem-B9-R5-WF sub' h m op v2 k nh ρ rzg)
               (cong (λ F → tell 0# (Esem (subE (cons fk (cons fl (cons v2 idSub))) (clause h op)) ρ F))
                     (sym (⌊⌋-irrelevant g sub sub' ρ))))
  where
  g' = renV S g
  handled = handleE (renH S h) (plugK (weaken1K k) (val (vvar Z)))
  fk = vabs {σ = gnd (in′ op)} (glocalE sub' ⊆ᵉ-refl handled g')
  fl = vabs {σ = gnd (in′ op)} (thenE sub' handled g')

-- ---------------------------------------------------------------------
-- Theorem 7.10 (hat-Theorem B.10): evaluation soundness. "None of Theorems
-- B.10, B.11, Corollary B.12, or Theorem B.13 inspect any deeper structure
-- of Ŵ_ε than [the] top-level pair" (the leaf's (r,x) or a stuck node's
-- (ℓ,op,v,f)) -- so, as the source observes, they transfer essentially
-- verbatim from Theorem 7.9 by induction on the big-step derivation.
-- `Terminal` (the two shapes big-step evaluation can end at: a value, or a
-- term stuck on an unhandled operation call under a context K) now lives
-- in OpSem.agda, alongside Handles/ContCxt, which it's built from.
-- ---------------------------------------------------------------------

-- (base case v, r=0: Lemma 7.2/lemma-B2 -- here just η̂ˢ's own definition,
-- so `done` reduces to `refl`; step case: Theorem 7.9 plus tell's own
-- definitional additivity at a leaf, tell r (leaf s x) = leaf (r+s) x,
-- exactly the "r=r₁+r₂" combination the source spells out via tell-+.)
theorem-7-10-val : ∀ {Γ σ ε εg} (sub : εg ⊆ᵉ ε) {g : LC Γ σ εg} {e : Γ ⊢ σ ! ε} {r : R} (v : Val Γ σ)
  → (bs : g ⊢ e ⇒[ r ] (val v)) → (ρ : Env Γ)
  → (∀ a → RootZero (Vsem g ρ a (λ _ → η̂ 0#))) → WFBigStep bs ρ
  → Esem e ρ ⌊ g ⌋[ sub , ρ ] ≡ leaf r (Vsem v ρ)
theorem-7-10-val sub v (done .(val v)) ρ rzg wfbs = refl
theorem-7-10-val sub v (step {r = r} stp rest) ρ rzg (wfstp , wfrest) =
  trans (theorem-B9 sub stp ρ rzg wfstp) (cong (tell r) (theorem-7-10-val sub v rest ρ rzg wfrest))

-- (base case, r=0: Lemma 7.8/lemma-B8 directly, φ̂ˢ unfolding to exactly
-- this node; step case: as above, using tell's definitional additivity at
-- a node, tell r (node m op s o κ) = node m op (r+s) o κ.)
theorem-7-10-op : ∀ {Γ σ ε εg εop ℓ} (sub : εg ⊆ᵉ ε) {g : LC Γ σ εg} {e : Γ ⊢ σ ! ε} {r : R}
  (m : ℓ ∈ εop) (op : Op ℓ) (v : Val Γ (gnd (out op))) (K : ContCxt Γ (gnd (in′ op)) εop σ ε) (nh : ¬ Handles K ℓ)
  → (bs : g ⊢ e ⇒[ r ] (plugK K (opE m op refl (val v)))) → (ρ : Env Γ)
  → (∀ a → RootZero (Vsem g ρ a (λ _ → η̂ 0#))) → WFBigStep bs ρ
  → Esem e ρ ⌊ g ⌋[ sub , ρ ] ≡
    node (promote K nh m) op r (Vsem v ρ) (λ a → Esem (plugK (weaken1K K) (val (vvar Z))) (ρ ,, a) ⌊ g ⌋[ sub , ρ ])
theorem-7-10-op sub {g} m op v K nh (done .(plugK K (opE m op refl (val v)))) ρ rzg wfbs = lemma-B8 op v K m nh ρ ⌊ g ⌋[ sub , ρ ]
theorem-7-10-op sub {g} m op v K nh (step {r = r} stp rest) ρ rzg (wfstp , wfrest) =
  trans (theorem-B9 sub stp ρ rzg wfstp) (cong (tell r) (theorem-7-10-op sub m op v K nh rest ρ rzg wfrest))

-- ---------------------------------------------------------------------
-- Theorem 7.11 (hat-Theorem B.11): adequacy, the converse direction. The
-- source derives it "from termination (Appendix A, untouched by the
-- swap) plus Theorem 7.10": termination gives *some* evaluation, and 7.10
-- computes what Ŵ-shape it produces, which -- since leaf and node are
-- disjoint, injective constructors of an ordinary (non-quotiented)
-- inductive type -- must be the one the hypothesis names.
--
-- `Terminates` is exactly that external fact: progress plus a
-- termination/size argument for λC, established by the *original* paper's
-- Appendix A and not re-derived here (re-proving type safety and
-- termination for λC is a separate undertaking from porting the swap's
-- own semantics/proofs, and orthogonal to it -- the swap changes nothing
-- about the operational semantics or its metatheory).
-- ---------------------------------------------------------------------

postulate
  Terminates : ∀ {Γ σ ε εg} (g : LC Γ σ εg) (e : Γ ⊢ σ ! ε)
             → Σ R (λ r → Σ (Γ ⊢ σ ! ε) (λ w → (g ⊢ e ⇒[ r ] w) × Terminal w))

-- theorem-7-10-val/op's ORIGINAL, unrestricted forms (no RootZero/WFStep
-- hypothesis at all -- theorem-B9-gen holds at every constructor for a
-- fully arbitrary γ, R5 included, via theorem-B9-R5-gen). Needed because
-- theorem-7-11-val/op below apply Theorem 7.10 to the SPECIFIC big-step
-- derivation `Terminates g e` hands back, whose internal structure is
-- existentially hidden -- there is no way to inspect which S2/S3 nodes
-- (if any) it passes through, hence no way to construct a WFBigStep
-- witness for it from a hypothesis about g alone. Closing that gap for
-- real would need a genuinely new theorem: a syntactic well-formedness
-- invariant on e itself (e.g. "every loss-continuation e embeds via
-- thenE/glocalE is RootZero"), plus a subject-reduction-style lemma that
-- this invariant is preserved by -[r]→ and hence guarantees WFStep along
-- ANY reduction sequence from e, including whichever one Terminates
-- happens to produce. That is out of scope here (it's a new piece of
-- metatheory, not a hypothesis-threading exercise), so this one
-- remaining path keeps relying on theorem-B9-gen/theorem-B9-R5-gen,
-- exactly as it always did.
theorem-7-10-val-unrestricted : ∀ {Γ σ ε εg} (sub : εg ⊆ᵉ ε) {g : LC Γ σ εg} {e : Γ ⊢ σ ! ε} {r : R} (v : Val Γ σ)
  → g ⊢ e ⇒[ r ] (val v) → (ρ : Env Γ)
  → Esem e ρ ⌊ g ⌋[ sub , ρ ] ≡ leaf r (Vsem v ρ)
theorem-7-10-val-unrestricted sub v (done .(val v)) ρ = refl
theorem-7-10-val-unrestricted sub {g = g} v (step {r = r} stp rest) ρ =
  trans (theorem-B9-gen stp ρ ⌊ g ⌋[ sub , ρ ]) (cong (tell r) (theorem-7-10-val-unrestricted sub v rest ρ))

theorem-7-10-op-unrestricted : ∀ {Γ σ ε εg εop ℓ} (sub : εg ⊆ᵉ ε) {g : LC Γ σ εg} {e : Γ ⊢ σ ! ε} {r : R}
  (m : ℓ ∈ εop) (op : Op ℓ) (v : Val Γ (gnd (out op))) (K : ContCxt Γ (gnd (in′ op)) εop σ ε) (nh : ¬ Handles K ℓ)
  → g ⊢ e ⇒[ r ] (plugK K (opE m op refl (val v))) → (ρ : Env Γ)
  → Esem e ρ ⌊ g ⌋[ sub , ρ ] ≡
    node (promote K nh m) op r (Vsem v ρ) (λ a → Esem (plugK (weaken1K K) (val (vvar Z))) (ρ ,, a) ⌊ g ⌋[ sub , ρ ])
theorem-7-10-op-unrestricted sub {g} m op v K nh (done .(plugK K (opE m op refl (val v)))) ρ = lemma-B8 op v K m nh ρ ⌊ g ⌋[ sub , ρ ]
theorem-7-10-op-unrestricted sub {g} m op v K nh (step {r = r} stp rest) ρ =
  trans (theorem-B9-gen stp ρ ⌊ g ⌋[ sub , ρ ]) (cong (tell r) (theorem-7-10-op-unrestricted sub m op v K nh rest ρ))

leaf≢node : ∀ {ε X} {r x} {ℓ} {m : ℓ ∈ ε} {op : Op ℓ} {r' o κ}
          → leaf {ε} {X} r x ≡ node m op r' o κ → ⊥
leaf≢node ()

leaf-inj-r : ∀ {ε X} {r r' : R} {x x' : X} → leaf {ε} r x ≡ leaf r' x' → r ≡ r'
leaf-inj-r refl = refl

leaf-inj-x : ∀ {ε X} {r r' : R} {x x' : X} → leaf {ε} r x ≡ leaf r' x' → x ≡ x'
leaf-inj-x refl = refl

theorem-7-11-val : ∀ {Γ σ ε εg} (sub : εg ⊆ᵉ ε) (g : LC Γ σ εg) (e : Γ ⊢ σ ! ε) (ρ : Env Γ) {r : R} {a : ⟦ σ ⟧}
  → (∀ b → RootZero (Vsem g ρ b (λ _ → η̂ 0#)))
  → Esem e ρ ⌊ g ⌋[ sub , ρ ] ≡ leaf r a
  → Σ (Val Γ σ) (λ v → (g ⊢ e ⇒[ r ] (val v)) × (Vsem v ρ ≡ a))
theorem-7-11-val sub g e ρ {r} {a} rzg heq with Terminates g e
theorem-7-11-val sub g e ρ {r} {a} rzg heq | r' , .(val v') , bigstep , terminalVal v'
  with leaf-inj-r (trans (sym heq) (theorem-7-10-val-unrestricted sub v' bigstep ρ))
     | leaf-inj-x (trans (sym heq) (theorem-7-10-val-unrestricted sub v' bigstep ρ))
... | refl | refl = v' , bigstep , refl
theorem-7-11-val sub g e ρ {r} {a} rzg heq | r' , .(plugK K (opE m op refl (val v'))) , bigstep , terminalOp m op v' K nh
  = ⊥-elim (leaf≢node (trans (sym heq) (theorem-7-10-op-unrestricted sub m op v' K nh bigstep ρ)))

-- The node/op-stuck half of adequacy: same argument shape (Terminates +
-- Theorem 7.10 + Ŵ-injectivity, ruling out the mismatching leaf case
-- exactly as above), but concluding the equality of *two* node terms
-- rather than two leaves. `node`'s own `op` (and hence the type of its
-- `o`,`κ` fields) is indexed by its own `ℓ ∈ ε` witness, but matching the
-- combined equality directly as `refl` (rather than via separate
-- injectivity lemmas, as leaf-inj-r/leaf-inj-x do for the leaf case)
-- lets Agda's own unifier extract ℓ, m, op, o, κ all at once -- ordinary
-- constructor-headed unification, no extra axioms needed.
theorem-7-11-op : ∀ {Γ σ ε εg ℓ} (sub : εg ⊆ᵉ ε) (g : LC Γ σ εg) (e : Γ ⊢ σ ! ε) (ρ : Env Γ)
  {r : R} (m : ℓ ∈ ε) (op : Op ℓ) (o : ⟦ out op ⟧ᴳ) (κ : ⟦ in′ op ⟧ᴳ → Ŵ ε ⟦ σ ⟧)
  → (∀ b → RootZero (Vsem g ρ b (λ _ → η̂ 0#)))
  → Esem e ρ ⌊ g ⌋[ sub , ρ ] ≡ node m op r o κ
  → Σ (Val Γ (gnd (out op))) (λ v →
      Σ EffCxt (λ εop → Σ (ℓ ∈ εop) (λ m' →
      Σ (ContCxt Γ (gnd (in′ op)) εop σ ε) (λ K → Σ (¬ Handles K ℓ) (λ nh →
        (promote K nh m' ≡ m)
        × (g ⊢ e ⇒[ r ] (plugK K (opE m' op refl (val v))))
        × (Vsem v ρ ≡ o)
        × (κ ≡ (λ a → Esem (plugK (weaken1K K) (val (vvar Z))) (ρ ,, a) ⌊ g ⌋[ sub , ρ ])))))))
theorem-7-11-op sub g e ρ m op o κ rzg heq with Terminates g e
theorem-7-11-op sub g e ρ m op o κ rzg heq | r' , .(val v') , bigstep , terminalVal v'
  = ⊥-elim (leaf≢node (trans (sym (theorem-7-10-val-unrestricted sub v' bigstep ρ)) heq))
theorem-7-11-op sub g e ρ m op o κ rzg heq | r' , .(plugK K (opE m' op' refl (val v'))) , bigstep , terminalOp {εop = εop'} m' op' v' K nh
  with trans (sym heq) (theorem-7-10-op-unrestricted sub m' op' v' K nh bigstep ρ)
... | refl = v' , εop' , m' , K , nh , refl , bigstep , refl , refl

-- ---------------------------------------------------------------------
-- Corollary 7.12 (hat-Corollary B.12): first-order adequacy. The forward
-- direction is just Theorem 7.10 (no first-orderness needed at all); the
-- backward direction needs Theorem 7.11 plus "constants interpreted
-- injectively" to turn the *semantic* equality Theorem 7.11 delivers
-- (Vsem v' ρ ≡ Vsem v ρ) into the *syntactic* v' ≡ v the corollary wants
-- (which fails at higher types: distinct λ-terms can denote the same
-- function). Here that injectivity assumption is free: `vgnd` stores its
-- semantic value directly (Vsem (vgnd x) ρ = x, no separate
-- constant-embedding function to be injective about), so Vsem is already
-- injective on closed first-order values by a direct induction -- no
-- extra postulate needed, unlike the source's general setting.
-- ---------------------------------------------------------------------

FirstOrder : Ty → Set
FirstOrder (gnd γ)     = ⊤
FirstOrder (σ `× τ)    = FirstOrder σ × FirstOrder τ
FirstOrder (σ ⇒ τ ! ε) = ⊥

Vsem-inj : ∀ {σ} → FirstOrder σ → (v v' : Val ∅ σ) (ρ : Env ∅) → Vsem v ρ ≡ Vsem v' ρ → v ≡ v'
Vsem-inj {gnd γ}  fo          (vvar ())     v'            ρ eq
Vsem-inj {gnd γ}  fo          (vgnd x)      (vvar ())     ρ eq
Vsem-inj {gnd γ}  fo          (vgnd x)      (vgnd y)      ρ eq = cong vgnd eq
Vsem-inj {σ `× τ} (fo1 , fo2) (vvar ())     v'            ρ eq
Vsem-inj {σ `× τ} (fo1 , fo2) (vpair v1 v2) (vvar ())     ρ eq
Vsem-inj {σ `× τ} (fo1 , fo2) (vpair v1 v2) (vpair v1' v2') ρ eq =
  cong₂ vpair (Vsem-inj fo1 v1 v1' ρ (cong proj₁ eq)) (Vsem-inj fo2 v2 v2' ρ (cong proj₂ eq))

corollary-7-12-fwd : ∀ {σ} (g : LC ∅ σ []) (e : ∅ ⊢ σ ! []) (ρ : Env ∅) {r : R} (v : Val ∅ σ)
  → (bigstep : g ⊢ e ⇒[ r ] (val v)) → (∀ a → RootZero (Vsem g ρ a (λ _ → η̂ 0#))) → WFBigStep bigstep ρ
  → Esem e ρ ⌊ g ⌋[ ⊆ᵉ-refl , ρ ] ≡ leaf r (Vsem v ρ)
corollary-7-12-fwd g e ρ v bigstep rzg wfbs = theorem-7-10-val ⊆ᵉ-refl v bigstep ρ rzg wfbs

corollary-7-12-bwd : ∀ {σ} → FirstOrder σ → (g : LC ∅ σ []) (e : ∅ ⊢ σ ! []) (ρ : Env ∅) {r : R} (v : Val ∅ σ)
  → (∀ a → RootZero (Vsem g ρ a (λ _ → η̂ 0#))) → Esem e ρ ⌊ g ⌋[ ⊆ᵉ-refl , ρ ] ≡ leaf r (Vsem v ρ) → g ⊢ e ⇒[ r ] (val v)
corollary-7-12-bwd fo g e ρ v rzg heq with theorem-7-11-val ⊆ᵉ-refl g e ρ rzg heq
... | v' , bigstep , veq with Vsem-inj fo v' v ρ veq
...   | refl = bigstep

-- ---------------------------------------------------------------------
-- Theorem 7.13 (hat-Theorem B.13): giant-step adequacy -- deliberately
-- not ported.
--
-- The statement relates Eval(e), a *giant-step* evaluator producing an
-- effect-value tree EV, to Ŝsem e Lsem g via a relation ▷ defined "at the
-- leaf level only" against the original's own EV/▷. Both EV and Eval(e)
-- (and the well-founded order the source inducts on) belong to
-- Appendix A of the *original* paper -- machinery the swap explicitly
-- leaves untouched (§5's remark, repeated at the head of this section:
-- "None of Theorems B.10, B.11, Corollary B.12, or Theorem B.13 inspect
-- any deeper structure of Ŵ_ε ... so [they transfer]"). Every other
-- result in this file is a proof *about* the semantics formalised in
-- Domains.agda/Syntax.agda/OpSem.agda/Denotational.agda; Theorem 7.13
-- additionally presupposes a *second, disjoint* semantics (the giant-step
-- evaluator) that was never part of this porting task's scope and has no
-- counterpart anywhere above. Postulating it here with placeholder
-- `EV`/`Eval`/`▷` definitions would misrepresent the gap as "one more
-- bookkeeping postulate" like B.5 or B.9's harder cases, when it is
-- actually "port a whole second appendix first" -- so it is left as this
-- comment rather than a hollow postulate over undefined types.
-- ---------------------------------------------------------------------
