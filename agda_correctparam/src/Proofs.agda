-- Porting agda_noparam/src/Proofs.agda's lemmas, one by one and in the
-- source's own order, to the parameterized object language (Syntax.agda/
-- Subst.agda/OpSem.agda, copied unchanged from agda/) and the new
-- "correct-param" denotational semantics (Domains.agda/Denotational.agda,
-- ported from haskell/SelectionMonad_ParameterSupport2.hs -- see those
-- files' own headers for why: agda/'s layered-algebra/ext̂-based
-- handlerΨ/handlerSem has a known soundness gap at parameterized
-- handlers).
--
-- Each lemma keeps agda_noparam's own name/number, with a note on what
-- changed. Lemmas whose entire subject matter is machinery this
-- construction no longer has (tell, collectX, bump, ext̂, LayeredAlg,
-- R̂-of, censor, handlerΨ/handlerAlg) are SKIPPED, not postulated -- noted
-- inline, in source order, rather than silently dropped.
open import Domains using (Sig)
import Domains

module Proofs (Sg : Sig) where

open Sig Sg
open import Syntax Sg
open import Subst Sg
open import OpSem Sg
open import OpSemProofs Sg using (theorem-A4-4)
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
open import Axiom.Extensionality.Propositional using (Extensionality)

-- Same axiom agda/src/Domains.agda's own ŴMonad module postulates
-- (needed there too, for the very same reason: proving two selection
-- functions/records equal from their fields' pointwise agreement).
postulate
  funext : ∀ {a b} → Extensionality a b

-- ---------------------------------------------------------------------
-- Lemma A.1 / B.1 (Substitution). Unchanged from agda_noparam/src/
-- Proofs.agda: a typing fact absorbed into `_[_]`'s own type by
-- intrinsic typing, independent of which denotational construction is
-- in play.
-- ---------------------------------------------------------------------

lemma-B1 : ∀ {Γ σ τ ε} → Val Γ σ → (Γ , σ) ⊢ τ ! ε → Γ ⊢ τ ! ε
lemma-B1 v e = e [ v ]

-- ---------------------------------------------------------------------
-- Lemma 7.2 (hat-Lemma B.2): values denote units.
-- Unchanged: still definitional -- Esem's very first clause is still
-- `Esem (val v) ρ = η̂ˢ (Vsem v ρ)` in the new construction too (only
-- η̂ˢ's OWN definition changed, not this equation's shape).
-- ---------------------------------------------------------------------

lemma-B2 : ∀ {Γ σ ε} (v : Val Γ σ) (ρ : Env Γ) → Esem {ε = ε} (val v) ρ ≡ η̂ˢ (Vsem v ρ)
lemma-B2 v ρ = refl

-- ---------------------------------------------------------------------
-- Lemma 7.3 (hat-Lemma B.3): SKIPPED. Entirely about `pointwiseTellAlg`/
-- `ext̂`/`tell` -- the layered-algebra homomorphic-extension proof
-- technique agda/'s and agda_noparam's handlerΨ/handlerSem are built on.
-- handlerSem here is a direct structural recursion over Ŝ's own
-- unfolding (Denotational.agda), never builds a LayeredAlg at all, so
-- there is no pointwise-tell algebra for a lemma about it to be stated
-- against.
-- ---------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Foundational infrastructure not literally numbered in agda_noparam's
-- Proofs.agda (its analogues live in Domains.ŴMonad/ŜMonad there,
-- modules this construction doesn't have) but needed from Lemma B.4
-- onward, exactly as RenCoh/SubCoh below are "unstated background
-- infrastructure" needed to make later lemmas precise.
-- ---------------------------------------------------------------------

-- Ŝ is a record with one function field; proving two Ŝ values equal from
-- their runSelWith fields' pointwise agreement needs funext plus
-- destructuring both sides via the sole constructor (not just relying on
-- eta, since Ŝ is self-referential through ŜStep).
Ŝ-eq : ∀ {ε X} {p q : Ŝ ε X} → (∀ γ → runSelWith p γ ≡ runSelWith q γ) → p ≡ q
Ŝ-eq {p = sel f} {q = sel g} eq = cong sel (funext eq)

mapF̂-id : ∀ {ε X} (t : F̂ ε X) → mapF̂ (λ x → x) t ≡ t
mapF̂-id (pure x)       = refl
mapF̂-id (opF̂ m o v κ)  = cong (opF̂ m o v) (funext (λ a → mapF̂-id (κ a)))

mapF̂-cong : ∀ {ε X Y} {f g : X → Y} → (∀ x → f x ≡ g x) → (t : F̂ ε X) → mapF̂ f t ≡ mapF̂ g t
mapF̂-cong feq (pure x)      = cong pure (feq x)
mapF̂-cong feq (opF̂ m o v κ) = cong (opF̂ m o v) (funext (λ a → mapF̂-cong feq (κ a)))

-- bindŜ's own left unit law (Ŝ's analogue of Domains.ŜMonad's
-- bindˢ-unitˡ): needs no induction on p at all, since η̂ˢ's own
-- runSelWith ignores whatever continuation it's given.
bindŜ-unitˡ : ∀ {ε X Y} (k : X → Ŝ ε Y) (x : X) → bindŜ (η̂ˢ x) k ≡ k x
bindŜ-unitˡ k x = Ŝ-eq lemma
  where
  lemma : ∀ γ → runSelWith (bindŜ (η̂ˢ x) k) γ ≡ runSelWith (k x) γ
  lemma γ with runSelWith (k x) γ
  ... | r2 , w2 = cong (λ z → z , w2) (+-identityˡ r2)

-- bindŜ's own right/associativity laws (Ŝ's analogues of bindˢ-unitʳ/
-- bindˢ-assoc) are NOT ported: proving them needs induction on p's own
-- unfolding depth (the node case reduces to "bindŜ (κ a) k ≡ κ a" for a
-- sub-selection-function κ a extracted from runSelWith p's RESULT, not
-- from directly pattern-matching p itself) -- but Ŝ's recursive
-- structure sits behind a function type ((X→R̂ε)→...), invisible to
-- Agda's structural-recursion/termination checker the way Ŵ's direct
-- `node`-recursion was, so this is not just more bookkeeping the way
-- bindˢ-unitˡ's proof was. Not needed by anything ported below (only
-- bindˢ-unitˡ is ever used, matching agda_noparam's own Lemma B.4).

-- ---------------------------------------------------------------------
-- Lemma 7.4 (hat-Lemma B.4): pairing and application. Unchanged shape --
-- bind̂ˢ/bindˢ-unitˡ renamed to bindŜ/bindŜ-unitˡ, otherwise identical to
-- agda_noparam's own proof (neither touches Ŝ/F̂'s internal shape at all).
-- ---------------------------------------------------------------------

lemma-B4-1 : ∀ {Γ σ τ ε} (v : Val Γ σ) (e : Γ ⊢ τ ! ε) (ρ : Env Γ)
           → Esem (pair (val v) e) ρ ≡ bindŜ (Esem e ρ) (λ b → η̂ˢ (Vsem v ρ , b))
lemma-B4-1 v e ρ = bindŜ-unitˡ (λ a → bindŜ (Esem e ρ) (λ b → η̂ˢ (a , b))) (Vsem v ρ)

lemma-B4-2 : ∀ {Γ σ τ ε} (v : Val Γ (σ ⇒ τ ! ε)) (e : Γ ⊢ σ ! ε) (ρ : Env Γ)
           → Esem (app (val v) e) ρ ≡ bindŜ (Esem e ρ) (λ a → Vsem v ρ a)
lemma-B4-2 v e ρ = bindŜ-unitˡ (λ φ → bindŜ (Esem e ρ) (λ a → φ a)) (Vsem v ρ)

-- ---------------------------------------------------------------------
-- Lemma 7.5 (hat-Lemma B.5): SKIPPED. Statement (1) is about R̂-of (gone);
-- (2)/(3) are Lsem unfolding facts that are still definitional here (as
-- in agda_noparam) but aren't consumed by anything below on their own.
--
-- Renaming coherence: Vsem/Lsem/Esem/handlerSem commute with a coherent
-- renaming of the environment -- unstated background infrastructure in
-- the source, needed here too to make Lemma B.6 precise. Same overall
-- shape as agda_noparam's own version; renH-coh's proof is genuinely
-- different (see its own comment) since handlerSem is no longer built
-- via ext̂/LayeredAlg.
-- ---------------------------------------------------------------------

RenCoh : ∀ {Γ Γ'} → Ren Γ Γ' → Env Γ → Env Γ' → Set
RenCoh {Γ} ren ρ ρ' = ∀ {σ} (x : Γ ∋ σ) → ρ' (ren x) ≡ ρ x

extR-coh : ∀ {Γ Γ'} (τ : Ty) (ren : Ren Γ Γ') (ρ : Env Γ) (ρ' : Env Γ') → RenCoh ren ρ ρ' → (a : ⟦ τ ⟧)
         → ∀ {σ} (x : (Γ , τ) ∋ σ) → (ρ' ,, a) (extR ren x) ≡ (ρ ,, a) x
extR-coh τ ren ρ ρ' coh a Z     = refl
extR-coh τ ren ρ ρ' coh a (S x) = coh x

-- Variant of extR-coh extending by two values a, a' related by a'≡a
-- (rather than the very same value on both sides), needed when the
-- extending value is itself something that first has to be shown equal
-- (l1v/k1v below, built from the same κ but a differently-environed h).
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
  renLsem-coh ren ρ ρ' coh g a = cong (thenS pure) (cong (λ F → F a) (renV-coh ren ρ ρ' coh g))

  -- handlerRet's own renaming coherence, factored out since both
  -- renH-coh (leaf case) and handlerStep-coh (leaf/node-yes cases) need
  -- exactly this instance of renE-coh applied to `ret h`.
  handlerRet-ren-eq : ∀ {Γ Γ' ℓ par σ σ' ε} (ren : Ren Γ Γ') (ρ : Env Γ) (ρ' : Env Γ') → RenCoh ren ρ ρ'
                    → (h : Handler Γ ℓ par σ σ' ε) (x : ⟦ σ ⟧) (p : ⟦ gnd par ⟧)
                    → handlerRet (renH ren h) ρ' x p ≡ handlerRet h ρ x p
  handlerRet-ren-eq {par = par} ren ρ ρ' coh h x p =
    renE-coh (extR (extR ren)) ((ρ ,, p) ,, x) ((ρ' ,, p) ,, x)
             (extR-coh _ (extR ren) (ρ ,, p) (ρ' ,, p) (extR-coh (gnd par) ren ρ ρ' coh p) x) (ret h)

  -- renH-coh h's own g-argument is unchanged, so this is an Ŝ-level
  -- (γ-independent) equation, unlike agda_noparam's own version (which
  -- had to fix γ throughout, since its Ŝ was directly callable) -- here
  -- we build it via Ŝ-eq, deferring γ to handlerStep-coh.
  renH-coh : ∀ {Γ Γ' ℓ par σ σ' ε} (ren : Ren Γ Γ') (ρ : Env Γ) (ρ' : Env Γ') → RenCoh ren ρ ρ'
           → (h : Handler Γ ℓ par σ σ' ε) (p : ⟦ gnd par ⟧) (G : Ŝ (ε ,ℓ ℓ) ⟦ σ ⟧)
           → handlerSem (renH ren h) ρ' p G ≡ handlerSem h ρ p G
  renH-coh {ℓ = ℓ} {par = par} {σ = σ} {σ' = σ'} {ε = ε} ren ρ ρ' coh h p G = Ŝ-eq renHstep
    where
    contRen contOrig : (γ : ⟦ σ' ⟧ → R̂ ε) → ⟦ σ ⟧ → R̂ (ε ,ℓ ℓ)
    contRen γ a = widenF̂ ⊆ᵉ-,ℓ (thenS γ (handlerRet (renH ren h) ρ' a p))
    contOrig γ a = widenF̂ ⊆ᵉ-,ℓ (thenS γ (handlerRet h ρ a p))

    contEq : ∀ γ a → contRen γ a ≡ contOrig γ a
    contEq γ a = cong (λ w → widenF̂ ⊆ᵉ-,ℓ (thenS γ w)) (handlerRet-ren-eq ren ρ ρ' coh h a p)

    renHstep : ∀ γ → runSelWith (handlerSem (renH ren h) ρ' p G) γ ≡ runSelWith (handlerSem h ρ p G) γ
    renHstep γ = trans (cong (λ w → handlerStep (renH ren h) ρ' γ p (runSelWith G w)) (funext (contEq γ)))
                       (handlerStep-coh ren ρ ρ' coh h p γ (runSelWith G (contOrig γ)))

  -- The per-step dispatch handlerSem's runSelWith itself delegates to,
  -- proven separately (rather than as a `with`-chain inside renH-coh
  -- directly) so its "same label" case can recurse into renH-coh at a
  -- genuinely different (extracted-from-X, not syntactically smaller)
  -- selection function κ a -- exactly the same shape of recursion
  -- handlerSem/handlerStep's OWN mutual definition already uses, so
  -- accepted by Agda's termination checker the same way.
  handlerStep-coh : ∀ {Γ Γ' ℓ par σ σ' ε} (ren : Ren Γ Γ') (ρ : Env Γ) (ρ' : Env Γ') → RenCoh ren ρ ρ'
                  → (h : Handler Γ ℓ par σ σ' ε) (p : ⟦ gnd par ⟧) (γ : ⟦ σ' ⟧ → R̂ ε)
                  → (X : R × ŜStep (ε ,ℓ ℓ) ⟦ σ ⟧)
                  → handlerStep (renH ren h) ρ' γ p X ≡ handlerStep h ρ γ p X
  handlerStep-coh ren ρ ρ' coh h p γ (r , leaf x) =
    cong (λ{ (r2 , w2) → (r + r2) , w2 }) (cong (λ e → runSelWith e γ) (handlerRet-ren-eq ren ρ ρ' coh h x p))
  handlerStep-coh {ℓ = ℓ} {par = par} {σ' = σ'} ren ρ ρ' coh h p γ (r , node {ℓ = ℓ1} m o v κ) with ℓ1 ≟ᵉ ℓ
  handlerStep-coh {ℓ = ℓ} {par = par} {σ' = σ'} ren ρ ρ' coh h p γ (r , node {ℓ = ℓ1} m o v κ) | yes eq with eq
  handlerStep-coh {ℓ = ℓ} {par = par} {σ' = σ'} ren ρ ρ' coh h p γ (r , node {ℓ = .ℓ} m o v κ) | yes eq | refl =
    cong (λ{ (r2 , w2) → (r + r2) , w2 }) (cong (λ e → runSelWith e γ) clauseEq)
    where
    recEq : ∀ p' a → handlerSem (renH ren h) ρ' p' (κ a) ≡ handlerSem h ρ p' (κ a)
    recEq p' a = renH-coh ren ρ ρ' coh h p' (κ a)
    l1vEq : l1v (renH ren h) ρ' γ o κ ≡ l1v h ρ γ o κ
    l1vEq = funext (λ{ (p' , a) → cong upS (cong (thenS γ) (recEq p' a)) })
    k1vEq : k1v (renH ren h) ρ' γ o κ ≡ k1v h ρ γ o κ
    k1vEq = funext (λ{ (p' , a) → cong (glocalS ⊆ᵉ-refl γ) (recEq p' a) })
    clauseEq : Esem (clause (renH ren h) o) ((((ρ' ,, p) ,, v) ,, l1v (renH ren h) ρ' γ o κ) ,, k1v (renH ren h) ρ' γ o κ)
             ≡ Esem (clause h o) ((((ρ ,, p) ,, v) ,, l1v h ρ γ o κ) ,, k1v h ρ γ o κ)
    clauseEq = renE-coh (extR (extR (extR (extR ren))))
                 (((( ρ ,, p) ,, v) ,, l1v h ρ γ o κ) ,, k1v h ρ γ o κ)
                 (((( ρ' ,, p) ,, v) ,, l1v (renH ren h) ρ' γ o κ) ,, k1v (renH ren h) ρ' γ o κ)
                 (extR-coh' ((gnd par `× gnd (in′ o)) ⇒ σ' ! _) (extR (extR (extR ren)))
                   ((( ρ ,, p) ,, v) ,, l1v h ρ γ o κ) ((( ρ' ,, p) ,, v) ,, l1v (renH ren h) ρ' γ o κ)
                   (extR-coh' ((gnd par `× gnd (in′ o)) ⇒ Loss ! _) (extR (extR ren))
                     ((ρ ,, p) ,, v) ((ρ' ,, p) ,, v)
                     (extR-coh (gnd (out o)) (extR ren) (ρ ,, p) (ρ' ,, p) (extR-coh (gnd par) ren ρ ρ' coh p) v)
                     (l1v h ρ γ o κ) (l1v (renH ren h) ρ' γ o κ) l1vEq)
                   (k1v h ρ γ o κ) (k1v (renH ren h) ρ' γ o κ) k1vEq)
                 (clause h o)
  handlerStep-coh ren ρ ρ' coh h p γ (r , node m o v κ) | no neq =
    cong (λ κ' → r , node (demoteMem m neq) o v κ') (funext (λ a → renH-coh ren ρ ρ' coh h p (κ a)))

  renE-coh : ∀ {Γ Γ' σ ε} (ren : Ren Γ Γ') (ρ : Env Γ) (ρ' : Env Γ') → RenCoh ren ρ ρ' → (e : Γ ⊢ σ ! ε)
           → Esem (renE ren e) ρ' ≡ Esem e ρ
  renE-coh ren ρ ρ' coh (val v)   = cong η̂ˢ (renV-coh ren ρ ρ' coh v)
  renE-coh ren ρ ρ' coh (fun f e) = cong (λ w → bindŜ w (λ a → η̂ˢ (⟦ f ⟧f a))) (renE-coh ren ρ ρ' coh e)
  renE-coh ren ρ ρ' coh (pair e1 e2) =
    cong₂ (λ w1 w2 → bindŜ w1 (λ a → bindŜ w2 (λ b → η̂ˢ (a , b)))) (renE-coh ren ρ ρ' coh e1) (renE-coh ren ρ ρ' coh e2)
  renE-coh ren ρ ρ' coh (fst e) = cong (λ w → bindŜ w (λ{ (a , b) → η̂ˢ a })) (renE-coh ren ρ ρ' coh e)
  renE-coh ren ρ ρ' coh (snd e) = cong (λ w → bindŜ w (λ{ (a , b) → η̂ˢ b })) (renE-coh ren ρ ρ' coh e)
  renE-coh ren ρ ρ' coh (app e1 e2) =
    cong₂ (λ w1 w2 → bindŜ w1 (λ φ → bindŜ w2 φ)) (renE-coh ren ρ ρ' coh e1) (renE-coh ren ρ ρ' coh e2)
  renE-coh ren ρ ρ' coh (opE m op e) = cong (λ w → bindŜ w (λ a → φ̂ˢ m op a η̂ˢ)) (renE-coh ren ρ ρ' coh e)
  renE-coh ren ρ ρ' coh (lossE e) = cong (λ w → bindŜ w (λ r → addLossŜ r (η̂ˢ tt))) (renE-coh ren ρ ρ' coh e)
  renE-coh ren ρ ρ' coh (thenE sub e1 g) =
    cong upS (cong₂ (λ w1 c → thenS c w1) (renE-coh ren ρ ρ' coh e1)
                     (funext (λ a → cong (widenF̂ sub) (renLsem-coh ren ρ ρ' coh g a))))
  renE-coh ren ρ ρ' coh (glocalE sub1 sub2 e g) =
    cong₂ (λ w1 c → glocalS sub2 c w1) (renE-coh ren ρ ρ' coh e)
          (funext (λ a → cong (widenF̂ sub1) (renLsem-coh ren ρ ρ' coh g a)))
  renE-coh ren ρ ρ' coh (resetE e) = cong resetS (renE-coh ren ρ ρ' coh e)
  renE-coh ren ρ ρ' coh (handleE h e1 e2) =
    cong₂ bindŜ (renE-coh ren ρ ρ' coh e1)
                (funext (λ p → trans (cong (handlerSem (renH ren h) ρ' p) (renE-coh ren ρ ρ' coh e2))
                                      (renH-coh ren ρ ρ' coh h p (Esem e2 ρ))))

-- Weakening by exactly one variable is the special case ren := S,
-- coh := λ x → refl (immediate from `,,`'s own S-clause). Unchanged from
-- agda_noparam/src/Proofs.agda.
weaken1-coh : ∀ {Γ σ ε} (τ : Ty) (e : Γ ⊢ σ ! ε) (ρ : Env Γ) (a : ⟦ τ ⟧) → Esem (weaken1 e) (ρ ,, a) ≡ Esem e ρ
weaken1-coh τ e ρ a = renE-coh (S {τ = τ}) ρ (ρ ,, a) (λ x → refl) e

weaken1V-coh : ∀ {Γ σ} (τ : Ty) (v : Val Γ σ) (ρ : Env Γ) (a : ⟦ τ ⟧) → Vsem (weaken1V v) (ρ ,, a) ≡ Vsem v ρ
weaken1V-coh τ v ρ a = renV-coh (S {τ = τ}) ρ (ρ ,, a) (λ x → refl) v

weaken1H-coh : ∀ {Γ ℓ par σ σ' ε} (τ : Ty) (h : Handler Γ ℓ par σ σ' ε) (ρ : Env Γ) (a : ⟦ τ ⟧) (p : ⟦ gnd par ⟧) (G : Ŝ (ε ,ℓ ℓ) ⟦ σ ⟧)
              → handlerSem (renH (S {τ = τ}) h) (ρ ,, a) p G ≡ handlerSem h ρ p G
weaken1H-coh τ h ρ a p G = renH-coh (S {τ = τ}) ρ (ρ ,, a) (λ x → refl) h p G

-- ---------------------------------------------------------------------
-- Substitution coherence: the Sub-based analogue of renaming coherence
-- above -- same shape of proof throughout (including subH-coh, mirroring
-- renH-coh's mutual recursion with a handlerStep-level helper), needed
-- from Theorem B.9 onward where reduction rules substitute values for
-- variables.
-- ---------------------------------------------------------------------

SubCoh : ∀ {Γ Γ'} → Sub Γ Γ' → Env Γ' → Env Γ → Set
SubCoh {Γ} σs ρ' ρ = ∀ {σ} (x : Γ ∋ σ) → Vsem (σs x) ρ' ≡ ρ x

mutual
  extS-coh : ∀ {Γ Γ'} (τ : Ty) (σs : Sub Γ Γ') (ρ' : Env Γ') (ρ : Env Γ) → SubCoh σs ρ' ρ → (a : ⟦ τ ⟧)
           → ∀ {σ} (x : (Γ , τ) ∋ σ) → Vsem (extS σs x) (ρ' ,, a) ≡ (ρ ,, a) x
  extS-coh τ σs ρ' ρ coh a Z     = refl
  extS-coh τ σs ρ' ρ coh a (S x) = trans (weaken1V-coh τ (σs x) ρ' a) (coh x)

  -- Variant extending by two values a, a' related by a≡a' (mirroring
  -- extR-coh'), needed for l1v/k1v below.
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
  subLsem-coh σs ρ' ρ coh g a = cong (thenS pure) (cong (λ F → F a) (subV-coh σs ρ' ρ coh g))

  handlerRet-sub-eq : ∀ {Γ Γ' ℓ par σ σ' ε} (σs : Sub Γ Γ') (ρ' : Env Γ') (ρ : Env Γ) → SubCoh σs ρ' ρ
                    → (h : Handler Γ ℓ par σ σ' ε) (x : ⟦ σ ⟧) (p : ⟦ gnd par ⟧)
                    → handlerRet (subH σs h) ρ' x p ≡ handlerRet h ρ x p
  handlerRet-sub-eq {par = par} σs ρ' ρ coh h x p =
    subE-coh (extS (extS σs)) ((ρ' ,, p) ,, x) ((ρ ,, p) ,, x)
             (extS-coh _ (extS σs) (ρ' ,, p) (ρ ,, p) (extS-coh (gnd par) σs ρ' ρ coh p) x) (ret h)

  subH-coh : ∀ {Γ Γ' ℓ par σ σ' ε} (σs : Sub Γ Γ') (ρ' : Env Γ') (ρ : Env Γ) → SubCoh σs ρ' ρ
           → (h : Handler Γ ℓ par σ σ' ε) (p : ⟦ gnd par ⟧) (G : Ŝ (ε ,ℓ ℓ) ⟦ σ ⟧)
           → handlerSem (subH σs h) ρ' p G ≡ handlerSem h ρ p G
  subH-coh {ℓ = ℓ} {par = par} {σ = σ} {σ' = σ'} {ε = ε} σs ρ' ρ coh h p G = Ŝ-eq subHstep
    where
    contSub contOrig : (γ : ⟦ σ' ⟧ → R̂ ε) → ⟦ σ ⟧ → R̂ (ε ,ℓ ℓ)
    contSub γ a = widenF̂ ⊆ᵉ-,ℓ (thenS γ (handlerRet (subH σs h) ρ' a p))
    contOrig γ a = widenF̂ ⊆ᵉ-,ℓ (thenS γ (handlerRet h ρ a p))

    contEq : ∀ γ a → contSub γ a ≡ contOrig γ a
    contEq γ a = cong (λ w → widenF̂ ⊆ᵉ-,ℓ (thenS γ w)) (handlerRet-sub-eq σs ρ' ρ coh h a p)

    subHstep : ∀ γ → runSelWith (handlerSem (subH σs h) ρ' p G) γ ≡ runSelWith (handlerSem h ρ p G) γ
    subHstep γ = trans (cong (λ w → handlerStep (subH σs h) ρ' γ p (runSelWith G w)) (funext (contEq γ)))
                       (handlerStep-sub-coh σs ρ' ρ coh h p γ (runSelWith G (contOrig γ)))

  handlerStep-sub-coh : ∀ {Γ Γ' ℓ par σ σ' ε} (σs : Sub Γ Γ') (ρ' : Env Γ') (ρ : Env Γ) → SubCoh σs ρ' ρ
                      → (h : Handler Γ ℓ par σ σ' ε) (p : ⟦ gnd par ⟧) (γ : ⟦ σ' ⟧ → R̂ ε)
                      → (X : R × ŜStep (ε ,ℓ ℓ) ⟦ σ ⟧)
                      → handlerStep (subH σs h) ρ' γ p X ≡ handlerStep h ρ γ p X
  handlerStep-sub-coh σs ρ' ρ coh h p γ (r , leaf x) =
    cong (λ{ (r2 , w2) → (r + r2) , w2 }) (cong (λ e → runSelWith e γ) (handlerRet-sub-eq σs ρ' ρ coh h x p))
  handlerStep-sub-coh {ℓ = ℓ} {par = par} {σ' = σ'} σs ρ' ρ coh h p γ (r , node {ℓ = ℓ1} m o v κ) with ℓ1 ≟ᵉ ℓ
  handlerStep-sub-coh {ℓ = ℓ} {par = par} {σ' = σ'} σs ρ' ρ coh h p γ (r , node {ℓ = ℓ1} m o v κ) | yes eq with eq
  handlerStep-sub-coh {ℓ = ℓ} {par = par} {σ' = σ'} σs ρ' ρ coh h p γ (r , node {ℓ = .ℓ} m o v κ) | yes eq | refl =
    cong (λ{ (r2 , w2) → (r + r2) , w2 }) (cong (λ e → runSelWith e γ) clauseEq)
    where
    recEq : ∀ p' a → handlerSem (subH σs h) ρ' p' (κ a) ≡ handlerSem h ρ p' (κ a)
    recEq p' a = subH-coh σs ρ' ρ coh h p' (κ a)
    l1vEq : l1v (subH σs h) ρ' γ o κ ≡ l1v h ρ γ o κ
    l1vEq = funext (λ{ (p' , a) → cong upS (cong (thenS γ) (recEq p' a)) })
    k1vEq : k1v (subH σs h) ρ' γ o κ ≡ k1v h ρ γ o κ
    k1vEq = funext (λ{ (p' , a) → cong (glocalS ⊆ᵉ-refl γ) (recEq p' a) })
    clauseEq : Esem (clause (subH σs h) o) ((((ρ' ,, p) ,, v) ,, l1v (subH σs h) ρ' γ o κ) ,, k1v (subH σs h) ρ' γ o κ)
             ≡ Esem (clause h o) ((((ρ ,, p) ,, v) ,, l1v h ρ γ o κ) ,, k1v h ρ γ o κ)
    clauseEq = subE-coh (extS (extS (extS (extS σs))))
                 (((( ρ' ,, p) ,, v) ,, l1v (subH σs h) ρ' γ o κ) ,, k1v (subH σs h) ρ' γ o κ)
                 (((( ρ ,, p) ,, v) ,, l1v h ρ γ o κ) ,, k1v h ρ γ o κ)
                 (extS-coh' ((gnd par `× gnd (in′ o)) ⇒ σ' ! _) (extS (extS (extS σs)))
                   ((( ρ' ,, p) ,, v) ,, l1v (subH σs h) ρ' γ o κ) ((( ρ ,, p) ,, v) ,, l1v h ρ γ o κ)
                   (extS-coh' ((gnd par `× gnd (in′ o)) ⇒ Loss ! _) (extS (extS σs))
                     ((ρ' ,, p) ,, v) ((ρ ,, p) ,, v)
                     (extS-coh (gnd (out o)) (extS σs) (ρ' ,, p) (ρ ,, p) (extS-coh (gnd par) σs ρ' ρ coh p) v)
                     (l1v h ρ γ o κ) (l1v (subH σs h) ρ' γ o κ) l1vEq)
                   (k1v h ρ γ o κ) (k1v (subH σs h) ρ' γ o κ) k1vEq)
                 (clause h o)
  handlerStep-sub-coh σs ρ' ρ coh h p γ (r , node m o v κ) | no neq =
    cong (λ κ' → r , node (demoteMem m neq) o v κ') (funext (λ a → subH-coh σs ρ' ρ coh h p (κ a)))

  subE-coh : ∀ {Γ Γ' σ ε} (σs : Sub Γ Γ') (ρ' : Env Γ') (ρ : Env Γ) → SubCoh σs ρ' ρ → (e : Γ ⊢ σ ! ε)
           → Esem (subE σs e) ρ' ≡ Esem e ρ
  subE-coh σs ρ' ρ coh (val v)   = cong η̂ˢ (subV-coh σs ρ' ρ coh v)
  subE-coh σs ρ' ρ coh (fun f e) = cong (λ w → bindŜ w (λ a → η̂ˢ (⟦ f ⟧f a))) (subE-coh σs ρ' ρ coh e)
  subE-coh σs ρ' ρ coh (pair e1 e2) =
    cong₂ (λ w1 w2 → bindŜ w1 (λ a → bindŜ w2 (λ b → η̂ˢ (a , b)))) (subE-coh σs ρ' ρ coh e1) (subE-coh σs ρ' ρ coh e2)
  subE-coh σs ρ' ρ coh (fst e) = cong (λ w → bindŜ w (λ{ (a , b) → η̂ˢ a })) (subE-coh σs ρ' ρ coh e)
  subE-coh σs ρ' ρ coh (snd e) = cong (λ w → bindŜ w (λ{ (a , b) → η̂ˢ b })) (subE-coh σs ρ' ρ coh e)
  subE-coh σs ρ' ρ coh (app e1 e2) =
    cong₂ (λ w1 w2 → bindŜ w1 (λ φ → bindŜ w2 φ)) (subE-coh σs ρ' ρ coh e1) (subE-coh σs ρ' ρ coh e2)
  subE-coh σs ρ' ρ coh (opE m op e) = cong (λ w → bindŜ w (λ a → φ̂ˢ m op a η̂ˢ)) (subE-coh σs ρ' ρ coh e)
  subE-coh σs ρ' ρ coh (lossE e) = cong (λ w → bindŜ w (λ r → addLossŜ r (η̂ˢ tt))) (subE-coh σs ρ' ρ coh e)
  subE-coh σs ρ' ρ coh (thenE sub e1 g) =
    cong upS (cong₂ (λ w1 c → thenS c w1) (subE-coh σs ρ' ρ coh e1)
                     (funext (λ a → cong (widenF̂ sub) (subLsem-coh σs ρ' ρ coh g a))))
  subE-coh σs ρ' ρ coh (glocalE sub1 sub2 e g) =
    cong₂ (λ w1 c → glocalS sub2 c w1) (subE-coh σs ρ' ρ coh e)
          (funext (λ a → cong (widenF̂ sub1) (subLsem-coh σs ρ' ρ coh g a)))
  subE-coh σs ρ' ρ coh (resetE e) = cong resetS (subE-coh σs ρ' ρ coh e)
  subE-coh σs ρ' ρ coh (handleE h e1 e2) =
    cong₂ bindŜ (subE-coh σs ρ' ρ coh e1)
                (funext (λ p → trans (cong (handlerSem (subH σs h) ρ' p) (subE-coh σs ρ' ρ coh e2))
                                      (subH-coh σs ρ' ρ coh h p (Esem e2 ρ))))

-- Single substitution, e[v] : the special case σs := sub1 v, coh := λ x → refl.
sub1-coh : ∀ {Γ σ τ ε} (e : (Γ , σ) ⊢ τ ! ε) (ρ : Env Γ) (v : Val Γ σ) → Esem (e [ v ]) ρ ≡ Esem e (ρ ,, Vsem v ρ)
sub1-coh e ρ v = subE-coh (sub1 v) ρ (ρ ,, Vsem v ρ) (λ { Z → refl ; (S x) → refl }) e

-- ---------------------------------------------------------------------
-- Lemma 7.6 (hat-Lemma B.6): the context lemma for regular frames.
-- "For e:σ!ε and F[e]:τ!ε where F is a regular frame:
--    Ssem(F[e])(ρ) = let_Sε a∈σ be Ssem(e)(ρ) in Ssem(F[x])(ρ[x/a])"
--
-- Proved case-by-case on F (Fig. 5's NINE forms -- the parameterized
-- Frame from agda/'s OpSem.agda, including F-handleP, which
-- agda_noparam's own version doesn't have). Every case reduces cleanly
-- to the Ŝ unit law (bindŜ-unitˡ) plus weaken1-coh/weaken1V-coh/
-- weaken1H-coh -- INCLUDING F-loss, unlike agda_noparam: lossE's own
-- semantics (Denotational.agda) is now a direct `bindŜ ... addLossŜ`,
-- no R̂-of/collectX/tell routing to reconcile, so the "Ŝ-tell-naturality"
-- detour agda_noparam needed isn't necessary here at all.
-- ---------------------------------------------------------------------

lemma-B6 : ∀ {Γ α ε τ} (f : Frame Γ α ε τ ε) (e : Γ ⊢ α ! ε) (ρ : Env Γ)
         → Esem (plugF f e) ρ ≡ bindŜ (Esem e ρ) (λ a → Esem (plugF (weaken1F f) (val (vvar Z))) (ρ ,, a))

lemma-B6 (F-fun pf) e ρ = cong (bindŜ (Esem e ρ)) (funext (λ a →
  sym (bindŜ-unitˡ (λ b → η̂ˢ (⟦ pf ⟧f b)) a)))

lemma-B6 {α = α} (F-pairL e₂) e ρ = cong (bindŜ (Esem e ρ)) (funext (λ a → sym (trans
  (bindŜ-unitˡ (λ a' → bindŜ (Esem (weaken1 e₂) (ρ ,, a)) (λ b → η̂ˢ (a' , b))) a)
  (cong (λ w → bindŜ w (λ b → η̂ˢ (a , b))) (weaken1-coh α e₂ ρ a)))))

lemma-B6 {α = α} (F-pairR {σ = σ} v) e ρ = trans (lemma-B4-1 v e ρ) (cong (bindŜ (Esem e ρ)) (funext per-a))
  where
  per-a : (a : ⟦ α ⟧) → η̂ˢ (Vsem v ρ , a) ≡ Esem (pair (val (weaken1V v)) (val (vvar Z))) (ρ ,, a)
  per-a a = sym step3
    where
    step12 : bindŜ (η̂ˢ (Vsem (weaken1V v) (ρ ,, a))) (λ a' → bindŜ (η̂ˢ a) (λ b → η̂ˢ (a' , b)))
           ≡ η̂ˢ (Vsem (weaken1V v) (ρ ,, a) , a)
    step12 = trans (bindŜ-unitˡ {X = ⟦ σ ⟧} {Y = ⟦ σ `× α ⟧} (λ a' → bindŜ (η̂ˢ a) (λ b → η̂ˢ (a' , b))) (Vsem (weaken1V v) (ρ ,, a)))
                   (bindŜ-unitˡ {X = ⟦ α ⟧} {Y = ⟦ σ `× α ⟧} (λ b → η̂ˢ (Vsem (weaken1V v) (ρ ,, a) , b)) a)
    step3 : Esem (pair (val (weaken1V v)) (val (vvar Z))) (ρ ,, a) ≡ η̂ˢ (Vsem v ρ , a)
    step3 = trans step12 (cong (λ w → η̂ˢ (w , a)) (weaken1V-coh α v ρ a))

lemma-B6 (F-fst {σ = σ} {τ = τ}) e ρ = cong (bindŜ (Esem e ρ)) (funext (λ (ab : ⟦ σ ⟧ × ⟦ τ ⟧) →
  sym (bindŜ-unitˡ {X = ⟦ σ ⟧ × ⟦ τ ⟧} (λ{ (a' , b') → η̂ˢ a' }) ab)))

lemma-B6 (F-snd {σ = σ} {τ = τ}) e ρ = cong (bindŜ (Esem e ρ)) (funext (λ (ab : ⟦ σ ⟧ × ⟦ τ ⟧) →
  sym (bindŜ-unitˡ {X = ⟦ σ ⟧ × ⟦ τ ⟧} (λ{ (a' , b') → η̂ˢ b' }) ab)))

lemma-B6 {α = α} (F-appL e₂) e ρ = cong (bindŜ (Esem e ρ)) (funext (λ a → sym (trans
  (bindŜ-unitˡ (λ φ → bindŜ (Esem (weaken1 e₂) (ρ ,, a)) φ) a)
  (cong (λ w → bindŜ w a) (weaken1-coh α e₂ ρ a)))))

lemma-B6 {α = α} (F-appR v) e ρ = trans (lemma-B4-2 v e ρ) (cong (bindŜ (Esem e ρ)) (funext (λ a → sym (trans
  (lemma-B4-2 {σ = α} (weaken1V v) (val (vvar Z)) (ρ ,, a))
  (trans (bindŜ-unitˡ (Vsem (weaken1V v) (ρ ,, a)) a)
         (cong (λ φ → φ a) (weaken1V-coh α v ρ a)))))))

lemma-B6 (F-op m op) e ρ = cong (bindŜ (Esem e ρ)) (funext (λ a →
  sym (bindŜ-unitˡ (λ b → φ̂ˢ m op b η̂ˢ) a)))

lemma-B6 F-loss e ρ = cong (bindŜ (Esem e ρ)) (funext (λ a →
  sym (bindŜ-unitˡ (λ r → addLossŜ r (η̂ˢ tt)) a)))

-- F-handleP: NEW case, absent from agda_noparam's own lemma-B6 (its
-- Frame has no parameter-evaluation frame at all -- handleE there has a
-- single, S-frame-only hole). Reduces via bindŜ-unitˡ (peeling the val
-- (vvar Z) hole) plus weaken1-coh/weaken1H-coh (bridging the weakened
-- handler/body back to the unweakened ones), mirroring F-appR's shape.
lemma-B6 {α = α} (F-handleP h b) e ρ = cong (bindŜ (Esem e ρ)) (funext (λ a → sym (stepH a)))
  where
  stepH : ∀ a → Esem (handleE (renH S h) (val (vvar Z)) (weaken1 b)) (ρ ,, a) ≡ handlerSem h ρ a (Esem b ρ)
  stepH a = trans (bindŜ-unitˡ (λ p → handlerSem (renH S h) (ρ ,, a) p (Esem (weaken1 b) (ρ ,, a))) a)
                  (trans (cong (handlerSem (renH S h) (ρ ,, a) a) (weaken1-coh α b ρ a))
                         (weaken1H-coh α h ρ a a (Esem b ρ)))

-- Lemma 7.7 (hat-Lemma B.7): not formalised as its own lemma, matching
-- agda_noparam -- not consumed by anything else here.

-- ---------------------------------------------------------------------
-- Lemma 7.8 (hat-Lemma B.8): operations under contexts K.
-- "For K[op(v)]:σ!ε with op∉h_eff(K) and op:out--ℓ→in:
--    Ssem(K[op(v)])(ρ) = φ̂_{ℓ,op,ε(ℓ)}(Vsem(v)(ρ), λa∈in. Ssem(K[x])(ρ[a/x]))"
--
-- ContCxt/Frame/SFrame here are the PARAMETERIZED ones (agda/'s OpSem.agda,
-- copied unchanged): F-op has no extra τ≡gnd(in′op) field (agda_noparam's
-- own variant adds one; not needed here), and there is a ninth Frame case
-- (F-handleP) plus S-handleB carries the handler's running parameter
-- value. promote/Frame-effect-eq are pure syntax, unchanged from
-- agda_noparam.
-- ---------------------------------------------------------------------

-- Every regular frame constructor happens to preserve the effect context
-- between hole and result; recorded here once, by cases, so `promote`'s
-- F∘ case can transport along it.
Frame-effect-eq : ∀ {Γ α β τ ε''} (f : Frame Γ α β τ ε'') → β ≡ ε''
Frame-effect-eq (F-fun _)     = refl
Frame-effect-eq (F-pairL _)   = refl
Frame-effect-eq (F-pairR _)   = refl
Frame-effect-eq F-fst         = refl
Frame-effect-eq F-snd         = refl
Frame-effect-eq (F-appL _)    = refl
Frame-effect-eq (F-appR _)    = refl
Frame-effect-eq (F-op _ _)    = refl
Frame-effect-eq F-loss        = refl
Frame-effect-eq (F-handleP _ _) = refl

promote : ∀ {Γ σ εH τ εO ℓ} (k : ContCxt Γ σ εH τ εO) → ¬ Handles k ℓ → ℓ ∈ εH → ℓ ∈ εO
promote ▫ nh m = m
promote (F∘ {β = β} k f) nh m rewrite Frame-effect-eq f = promote k nh m
promote (S∘ k (S-handleB {ℓ = ℓ'} {ε = εk} h v)) nh m with ∈-++⁻ εk {ys = ℓ' ∷ []} (promote k (λ hk → nh (inj₂ hk)) m)
... | inj₁ m-old        = m-old
... | inj₂ (here eq)    = ⊥-elim (nh (inj₁ eq))
... | inj₂ (there ())
promote (S∘ k (S-then _ _)) nh m           = promote k nh m
promote (S∘ k (S-glocal sub1 sub2 _)) nh m = sub2 (promote k nh m)
promote (S∘ k S-reset) nh m                = promote k nh m

-- bindŜ H (φ̂ˢ m op o κ) ≡ φ̂ˢ m op o (λa → bindŜ H (κ a)): a node built by
-- φ̂ˢ survives being fed through an outer bindŜ untouched. Simpler than
-- agda_noparam's own version (needs no tell-0 at all): φ̂ˢ's own
-- runSelWith already ignores whatever continuation it's given, so both
-- sides reduce to the SAME node by refl -- no embedded root-loss to
-- reconcile, since (unlike Ŵ) nothing is embedded in ŜStep's node case.
bindŜ-φ̂ˢ-fusion : ∀ {ε X Y ℓ} (m : ℓ ∈ ε) (op : Op ℓ) (o : ⟦ out op ⟧ᴳ) (κ : ⟦ in′ op ⟧ᴳ → Ŝ ε X) (H : X → Ŝ ε Y)
  → bindŜ (φ̂ˢ m op o κ) H ≡ φ̂ˢ m op o (λ a → bindŜ (κ a) H)
bindŜ-φ̂ˢ-fusion m op o κ H = refl

-- "Double weakening is a no-op": weakening a frame TWICE (once by some
-- unrelated fresh var υ, then by its own hole-type α) and evaluating
-- under the correspondingly-extended environment agrees with weakening
-- it ONCE (by α directly) and evaluating without the extra υ-binding.
-- Same proof shape as agda_noparam's own version (via weaken1-coh/
-- weaken1V-coh/weaken1H-coh applied twice per case), just bindŜ/
-- bindŜ-unitˡ's flipped argument order, plus a new F-handleP case.
weaken1F-skip : ∀ {Γ α β τ ε'} (f : Frame Γ α β τ ε') (υ : Ty) (ρ : Env Γ) (c : ⟦ υ ⟧) (a : ⟦ α ⟧)
  → Esem (plugF (weaken1F {υ = α} (weaken1F {υ = υ} f)) (val (vvar Z))) ((ρ ,, c) ,, a) ≡ Esem (plugF (weaken1F {υ = α} f) (val (vvar Z))) (ρ ,, a)
weaken1F-skip (F-fun pf) υ ρ c a = refl
weaken1F-skip {α = α} (F-pairL e₂) υ ρ c a = trans lhsRed (sym rhsRed)
  where
  lhsRed : Esem (pair (val (vvar Z)) (weaken1 (weaken1 e₂))) ((ρ ,, c) ,, a) ≡ bindŜ (Esem e₂ ρ) (λ b → η̂ˢ (a , b))
  lhsRed = trans (bindŜ-unitˡ (λ a' → bindŜ (Esem (weaken1 (weaken1 e₂)) ((ρ ,, c) ,, a)) (λ b → η̂ˢ (a' , b))) a)
                 (trans (cong (λ w → bindŜ w (λ b → η̂ˢ (a , b))) (weaken1-coh α (weaken1 e₂) (ρ ,, c) a))
                        (cong (λ w → bindŜ w (λ b → η̂ˢ (a , b))) (weaken1-coh υ e₂ ρ c)))
  rhsRed : Esem (pair (val (vvar Z)) (weaken1 e₂)) (ρ ,, a) ≡ bindŜ (Esem e₂ ρ) (λ b → η̂ˢ (a , b))
  rhsRed = trans (bindŜ-unitˡ (λ a' → bindŜ (Esem (weaken1 e₂) (ρ ,, a)) (λ b → η̂ˢ (a' , b))) a)
                 (cong (λ w → bindŜ w (λ b → η̂ˢ (a , b))) (weaken1-coh α e₂ ρ a))
weaken1F-skip {α = α} (F-pairR v) υ ρ c a = trans lhsRed (sym rhsRed)
  where
  lhsRed : Esem (pair (val (weaken1V (weaken1V v))) (val (vvar Z))) ((ρ ,, c) ,, a) ≡ η̂ˢ (Vsem v ρ , a)
  lhsRed = trans (bindŜ-unitˡ (λ x → bindŜ (η̂ˢ a) (λ y → η̂ˢ (x , y))) (Vsem (weaken1V (weaken1V v)) ((ρ ,, c) ,, a)))
                 (trans (bindŜ-unitˡ (λ y → η̂ˢ (Vsem (weaken1V (weaken1V v)) ((ρ ,, c) ,, a) , y)) a)
                        (cong (λ x → η̂ˢ (x , a)) (trans (weaken1V-coh α (weaken1V v) (ρ ,, c) a) (weaken1V-coh υ v ρ c))))
  rhsRed : Esem (pair (val (weaken1V v)) (val (vvar Z))) (ρ ,, a) ≡ η̂ˢ (Vsem v ρ , a)
  rhsRed = trans (bindŜ-unitˡ (λ x → bindŜ (η̂ˢ a) (λ y → η̂ˢ (x , y))) (Vsem (weaken1V v) (ρ ,, a)))
                 (trans (bindŜ-unitˡ (λ y → η̂ˢ (Vsem (weaken1V v) (ρ ,, a) , y)) a)
                        (cong (λ x → η̂ˢ (x , a)) (weaken1V-coh α v ρ a)))
weaken1F-skip F-fst υ ρ c a = refl
weaken1F-skip F-snd υ ρ c a = refl
weaken1F-skip {α = α} (F-appL e₂) υ ρ c a = trans lhsRed (sym rhsRed)
  where
  lhsRed : Esem (app (val (vvar Z)) (weaken1 (weaken1 e₂))) ((ρ ,, c) ,, a) ≡ bindŜ (Esem e₂ ρ) a
  lhsRed = trans (bindŜ-unitˡ (λ φ → bindŜ (Esem (weaken1 (weaken1 e₂)) ((ρ ,, c) ,, a)) φ) a)
                 (trans (cong (λ w → bindŜ w a) (weaken1-coh α (weaken1 e₂) (ρ ,, c) a))
                        (cong (λ w → bindŜ w a) (weaken1-coh υ e₂ ρ c)))
  rhsRed : Esem (app (val (vvar Z)) (weaken1 e₂)) (ρ ,, a) ≡ bindŜ (Esem e₂ ρ) a
  rhsRed = trans (bindŜ-unitˡ (λ φ → bindŜ (Esem (weaken1 e₂) (ρ ,, a)) φ) a)
                 (cong (λ w → bindŜ w a) (weaken1-coh α e₂ ρ a))
weaken1F-skip {α = α} (F-appR v) υ ρ c a = trans lhsRed (sym rhsRed)
  where
  lhsRed : Esem (app (val (weaken1V (weaken1V v))) (val (vvar Z))) ((ρ ,, c) ,, a) ≡ Vsem v ρ a
  lhsRed = trans (bindŜ-unitˡ (λ φ → bindŜ (η̂ˢ a) φ) (Vsem (weaken1V (weaken1V v)) ((ρ ,, c) ,, a)))
                 (trans (bindŜ-unitˡ (λ b → Vsem (weaken1V (weaken1V v)) ((ρ ,, c) ,, a) b) a)
                        (cong (λ φ → φ a) (trans (weaken1V-coh α (weaken1V v) (ρ ,, c) a) (weaken1V-coh υ v ρ c))))
  rhsRed : Esem (app (val (weaken1V v)) (val (vvar Z))) (ρ ,, a) ≡ Vsem v ρ a
  rhsRed = trans (bindŜ-unitˡ (λ φ → bindŜ (η̂ˢ a) φ) (Vsem (weaken1V v) (ρ ,, a)))
                 (trans (bindŜ-unitˡ (λ b → Vsem (weaken1V v) (ρ ,, a) b) a)
                        (cong (λ φ → φ a) (weaken1V-coh α v ρ a)))
weaken1F-skip (F-op m op) υ ρ c a = refl
weaken1F-skip F-loss υ ρ c a = refl
weaken1F-skip {α = α} (F-handleP h b) υ ρ c a = trans lhsRed (sym rhsRed)
  where
  lhsRed : Esem (handleE (renH S (renH S h)) (val (vvar Z)) (weaken1 (weaken1 b))) ((ρ ,, c) ,, a) ≡ handlerSem h ρ a (Esem b ρ)
  lhsRed = trans (bindŜ-unitˡ (λ p → handlerSem (renH S (renH S h)) ((ρ ,, c) ,, a) p (Esem (weaken1 (weaken1 b)) ((ρ ,, c) ,, a))) a)
                 (trans (cong (handlerSem (renH S (renH S h)) ((ρ ,, c) ,, a) a)
                              (trans (weaken1-coh α (weaken1 b) (ρ ,, c) a) (weaken1-coh υ b ρ c)))
                        (trans (weaken1H-coh α (renH S h) (ρ ,, c) a a (Esem b ρ))
                               (weaken1H-coh υ h ρ c a (Esem b ρ))))
  rhsRed : Esem (handleE (renH S h) (val (vvar Z)) (weaken1 b)) (ρ ,, a) ≡ handlerSem h ρ a (Esem b ρ)
  rhsRed = trans (bindŜ-unitˡ (λ p → handlerSem (renH S h) (ρ ,, a) p (Esem (weaken1 b) (ρ ,, a))) a)
                 (trans (cong (handlerSem (renH S h) (ρ ,, a) a) (weaken1-coh α b ρ a))
                        (weaken1H-coh α h ρ a a (Esem b ρ)))

-- ---------------------------------------------------------------------
-- plugK-fst-snd-coh: a bespoke bridging lemma, needed for Theorem B.9's
-- (R5) case (see theorem-B9-R5 below), specific to this construction's
-- PARAMETERIZED handlers. R5's own fk/fl are built from k weakened by a
-- PAIR type (gnd par `× gnd δ, δ := in′ op) and immediately projected
-- (via `snd`) to recover the operation's own argument -- whereas
-- lemma-B8's own κ weakens k by δ ALONE, directly. These are two
-- DIFFERENT single-variable weakenings of the very same k (different
-- fresh types), so no renaming relates them (a Ren is type-preserving);
-- what relates them is that projecting the pair BACK OUT reconstructs
-- exactly the δ-value the un-paired weakening would have bound. Proven
-- by induction on k, exactly mirroring lemma-B8's own (F∘)/(S∘)
-- structure -- lemma-B6 + weaken1F-skip cover (F∘) uniformly (both
-- sides' own outer frame becomes independent of the pair-vs-bare
-- weakening once its own hole-continuation's leading variable is
-- discarded, which is exactly what weaken1F-skip already shows); (S∘)
-- needs one case per SFrame constructor, mirroring lemma-B8-S∘-*.
-- ---------------------------------------------------------------------

plugK-fst-snd-coh : ∀ {Γ par δ εH τ εO} (k : ContCxt Γ (gnd δ) εH τ εO) (ρ : Env Γ) (p' : ⟦ gnd par ⟧) (a : ⟦ gnd δ ⟧)
  → Esem (plugK (weaken1K {υ = gnd par `× gnd δ} k) (snd (val (vvar Z)))) (ρ ,, (p' , a))
  ≡ Esem (plugK (weaken1K {υ = gnd δ} k) (val (vvar Z))) (ρ ,, a)
plugK-fst-snd-coh {par = par} {δ = δ} ▫ ρ p' a =
  bindŜ-unitˡ {X = ⟦ gnd par ⟧ × ⟦ gnd δ ⟧} (λ{ (x , y) → η̂ˢ y }) (p' , a)
plugK-fst-snd-coh {εO = εO} (F∘ {β = β} k₀ f) ρ p' a = helper (Frame-effect-eq f)
  where
  helper : β ≡ εO
         → Esem (plugK (weaken1K (F∘ k₀ f)) (snd (val (vvar Z)))) (ρ ,, (p' , a))
         ≡ Esem (plugK (weaken1K (F∘ k₀ f)) (val (vvar Z))) (ρ ,, a)
  helper refl =
    trans (lemma-B6 (weaken1F f) (plugK (weaken1K k₀) (snd (val (vvar Z)))) (ρ ,, (p' , a)))
          (trans (cong₂ bindŜ (plugK-fst-snd-coh k₀ ρ p' a) (funext contEq))
                 (sym (lemma-B6 (weaken1F f) (plugK (weaken1K k₀) (val (vvar Z))) (ρ ,, a))))
    where
    contEq : ∀ x → Esem (plugF (weaken1F (weaken1F f)) (val (vvar Z))) ((ρ ,, (p' , a)) ,, x)
                 ≡ Esem (plugF (weaken1F (weaken1F f)) (val (vvar Z))) ((ρ ,, a) ,, x)
    contEq x = trans (weaken1F-skip f _ ρ (p' , a) x) (sym (weaken1F-skip f _ ρ a x))
plugK-fst-snd-coh (S∘ k₀ S-reset) ρ p' a =
  cong resetS (plugK-fst-snd-coh k₀ ρ p' a)
plugK-fst-snd-coh (S∘ k₀ (S-then sub g)) ρ p' a =
  cong upS (cong₂ thenS (funext contEq) (plugK-fst-snd-coh k₀ ρ p' a))
  where
  contEq : ∀ b → widenF̂ sub (Lsem (weaken1V g) (ρ ,, (p' , a)) b) ≡ widenF̂ sub (Lsem (weaken1V g) (ρ ,, a) b)
  contEq b = cong (widenF̂ sub) (trans (renLsem-coh S ρ (ρ ,, (p' , a)) (λ x → refl) g b)
                                       (sym (renLsem-coh S ρ (ρ ,, a) (λ x → refl) g b)))
plugK-fst-snd-coh (S∘ k₀ (S-glocal sub1 sub2 g)) ρ p' a =
  cong₂ (glocalS sub2) (funext contEq) (plugK-fst-snd-coh k₀ ρ p' a)
  where
  contEq : ∀ b → widenF̂ sub1 (Lsem (weaken1V g) (ρ ,, (p' , a)) b) ≡ widenF̂ sub1 (Lsem (weaken1V g) (ρ ,, a) b)
  contEq b = cong (widenF̂ sub1) (trans (renLsem-coh S ρ (ρ ,, (p' , a)) (λ x → refl) g b)
                                        (sym (renLsem-coh S ρ (ρ ,, a) (λ x → refl) g b)))
plugK-fst-snd-coh (S∘ k₀ (S-handleB h w)) ρ p' a =
  trans stepP (trans (cong (handlerSem h ρ (Vsem w ρ)) (plugK-fst-snd-coh k₀ ρ p' a)) (sym stepW))
  where
  eP = plugK (weaken1K k₀) (snd (val (vvar Z)))
  eW = plugK (weaken1K k₀) (val (vvar Z))
  stepP : Esem (handleE (renH S h) (val (renV S w)) eP) (ρ ,, (p' , a))
        ≡ handlerSem h ρ (Vsem w ρ) (Esem eP (ρ ,, (p' , a)))
  stepP = trans (bindŜ-unitˡ (λ p2 → handlerSem (renH S h) (ρ ,, (p' , a)) p2 (Esem eP (ρ ,, (p' , a)))) (Vsem (renV S w) (ρ ,, (p' , a))))
                (trans (cong (λ p2 → handlerSem (renH S h) (ρ ,, (p' , a)) p2 (Esem eP (ρ ,, (p' , a)))) (weaken1V-coh _ w ρ (p' , a)))
                       (weaken1H-coh _ h ρ (p' , a) (Vsem w ρ) (Esem eP (ρ ,, (p' , a)))))
  stepW : Esem (handleE (renH S h) (val (renV S w)) eW) (ρ ,, a)
        ≡ handlerSem h ρ (Vsem w ρ) (Esem eW (ρ ,, a))
  stepW = trans (bindŜ-unitˡ (λ p2 → handlerSem (renH S h) (ρ ,, a) p2 (Esem eW (ρ ,, a))) (Vsem (renV S w) (ρ ,, a)))
                (trans (cong (λ p2 → handlerSem (renH S h) (ρ ,, a) p2 (Esem eW (ρ ,, a))) (weaken1V-coh _ w ρ a))
                       (weaken1H-coh _ h ρ a (Vsem w ρ) (Esem eW (ρ ,, a))))

-- Forward-declared so lemma-B8-F∘-eq (mutually recursive with it, on the
-- structurally smaller k) can call it before its own body (below) is given.
lemma-B8 : ∀ {Γ ℓ εH τ εO} (op : Op ℓ) (v : Val Γ (gnd (out op)))
           (k : ContCxt Γ (gnd (in′ op)) εH τ εO) (mH : ℓ ∈ εH) (nh : ¬ Handles k ℓ)
           (ρ : Env Γ)
         → Esem (plugK k (opE mH op (val v))) ρ
         ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, a))

-- (F∘) case of Lemma B.8, k/f's hole and result effects ALREADY MERGED to
-- a single εO -- always valid for a regular frame f (Frame-effect-eq).
-- Proof: plugK(F∘kf)e₀ = plugFf(plugKke₀), so lemma-B6 turns
-- Esem(plugFf(plugKke₀))ρ into bindŜ(Esem(plugKke₀)ρ)H for a fixed H; the
-- IH (lemma-B8 on the structurally smaller k) rewrites Esem(plugKke₀)ρ
-- into a φ̂ˢ node; bindŜ-φ̂ˢ-fusion pushes H through that node; and
-- weaken1F-skip identifies the resulting per-branch continuation with the
-- target.
promote-F∘-eq : ∀ {Γ ℓ σ εH α εO τ} (k : ContCxt Γ σ εH α εO) (f : Frame Γ α εO τ εO) (nh : ¬ Handles (F∘ k f) ℓ) (mH : ℓ ∈ εH)
  → promote (F∘ k f) nh mH ≡ promote k nh mH
promote-F∘-eq k f nh mH with Frame-effect-eq f
... | refl = refl

lemma-B8-F∘-eq : ∀ {Γ ℓ εH α τ εO} (op : Op ℓ) (v : Val Γ (gnd (out op)))
            (k : ContCxt Γ (gnd (in′ op)) εH α εO) (f : Frame Γ α εO τ εO) (mH : ℓ ∈ εH) (nh : ¬ Handles (F∘ k f) ℓ)
            (ρ : Env Γ)
          → Esem (plugK (F∘ k f) (opE mH op (val v))) ρ
          ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K (F∘ k f)) (val (vvar Z))) (ρ ,, a))
lemma-B8-F∘-eq {α = α} op v k f mH nh ρ = trans step1 step2
  where
  e₀ = plugK k (opE mH op (val v))
  H : ⟦ α ⟧ → Ŝ _ _
  H a = Esem (plugF (weaken1F f) (val (vvar Z))) (ρ ,, a)
  ih : Esem e₀ ρ ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, a))
  ih = lemma-B8 op v k mH nh ρ
  step1 : Esem (plugF f e₀) ρ ≡ bindŜ (Esem e₀ ρ) H
  step1 = lemma-B6 f e₀ ρ
  bAeq : ∀ (a : ⟦ in′ op ⟧ᴳ) → bindŜ (Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, a)) H ≡ Esem (plugK (weaken1K (F∘ k f)) (val (vvar Z))) (ρ ,, a)
  bAeq a = trans (cong (bindŜ (Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, a)))
                       (sym (funext (λ b → weaken1F-skip f (gnd (in′ op)) ρ a b))))
                 (sym (lemma-B6 (weaken1F f) (plugK (weaken1K k) (val (vvar Z))) (ρ ,, a)))
  step2 : bindŜ (Esem e₀ ρ) H
        ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K (F∘ k f)) (val (vvar Z))) (ρ ,, a))
  step2 = trans (cong (λ w → bindŜ w H) ih)
                (trans (bindŜ-φ̂ˢ-fusion (promote k nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, a)) H)
                       (cong (φ̂ˢ (promote k nh mH) op (Vsem v ρ)) (funext bAeq)))

-- General (F∘) case, β≠εO as ContCxt's own type technically allows: a
-- thin corollary of lemma-B8-F∘-eq + promote-F∘-eq, via its own
-- `with Frame-effect-eq f | refl`.
lemma-B8-F∘ : ∀ {Γ ℓ εH α τ β εO} (op : Op ℓ) (v : Val Γ (gnd (out op)))
            (k : ContCxt Γ (gnd (in′ op)) εH α β) (f : Frame Γ α β τ εO) (mH : ℓ ∈ εH) (nh : ¬ Handles (F∘ k f) ℓ)
            (ρ : Env Γ)
          → Esem (plugK (F∘ k f) (opE mH op (val v))) ρ
          ≡ φ̂ˢ (promote (F∘ k f) nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K (F∘ k f)) (val (vvar Z))) (ρ ,, a))
lemma-B8-F∘ {β = β} {εO = εO} op v k f mH nh ρ = helper (Frame-effect-eq f)
  where
  helper : (eq : β ≡ εO) → Esem (plugK (F∘ k f) (opE mH op (val v))) ρ
         ≡ φ̂ˢ (promote (F∘ k f) nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K (F∘ k f)) (val (vvar Z))) (ρ ,, a))
  helper refl = trans (lemma-B8-F∘-eq op v k f mH nh ρ)
                       (cong (λ m → φ̂ˢ m op (Vsem v ρ) (λ a → Esem (plugK (weaken1K (F∘ k f)) (val (vvar Z))) (ρ ,, a)))
                             (sym (promote-F∘-eq k f nh mH)))

-- (S∘) case, split on s's four constructors.
--
-- S-reset: resetS ∘ φ̂ˢ = φ̂ˢ ∘ (resetS on each branch) definitionally (no
-- embedded root-loss to reconcile, unlike agda_noparam's censor-over-Ŵ
-- version), so this is a direct `cong resetS` of the IH.
lemma-B8-S∘-reset : ∀ {Γ ℓ εH α ε} (op : Op ℓ) (v : Val Γ (gnd (out op)))
            (k : ContCxt Γ (gnd (in′ op)) εH α ε) (mH : ℓ ∈ εH) (nh : ¬ Handles k ℓ) (ρ : Env Γ)
          → Esem (resetE (plugK k (opE mH op (val v)))) ρ
          ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K (S∘ k S-reset)) (val (vvar Z))) (ρ ,, a))
lemma-B8-S∘-reset op v k mH nh ρ = cong resetS (lemma-B8 op v k mH nh ρ)

-- S-then: thenS/upS commute with φ̂ˢ definitionally too (φ̂ˢ's own
-- runSelWith ignores whatever continuation it is run against), leaving
-- only a mempty-loss mapF̂ (mapF̂-id/mapF̂-cong) and a renLsem-coh bridge
-- (g's own semantics, unweakened vs weakened) to reconcile per branch --
-- no collectX/bump/tell needed at all, unlike agda_noparam.
lemma-B8-S∘-then : ∀ {Γ ℓ εH α εg ε} (op : Op ℓ) (v : Val Γ (gnd (out op)))
            (k : ContCxt Γ (gnd (in′ op)) εH α ε) (sub : εg ⊆ᵉ ε) (g : LC Γ α εg) (mH : ℓ ∈ εH) (nh : ¬ Handles k ℓ)
            (ρ : Env Γ)
          → Esem (thenE sub (plugK k (opE mH op (val v))) g) ρ
          ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-then sub g))) (val (vvar Z))) (ρ ,, b))
lemma-B8-S∘-then {α = α} {ε = ε} op v k sub g mH nh ρ = trans step1 step2
  where
  e₀ = plugK k (opE mH op (val v))
  g1 : ⟦ α ⟧ → R̂ ε
  g1 a = widenF̂ sub (Lsem g ρ a)
  κ : ⟦ in′ op ⟧ᴳ → Ŝ ε ⟦ α ⟧
  κ b = Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, b)
  ih : Esem e₀ ρ ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) κ
  ih = lemma-B8 op v k mH nh ρ
  step1 : Esem (thenE sub e₀ g) ρ
        ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ b → upS (mapF̂ (0# +_) (thenS g1 (κ b))))
  step1 = cong (λ w → upS (thenS g1 w)) ih
  bAeq : ∀ b → upS (mapF̂ (0# +_) (thenS g1 (κ b))) ≡ Esem (plugK (weaken1K (S∘ k (S-then sub g))) (val (vvar Z))) (ρ ,, b)
  bAeq b = trans (cong upS (trans (mapF̂-cong (λ r → +-identityˡ r) (thenS g1 (κ b))) (mapF̂-id (thenS g1 (κ b)))))
                 (cong (λ c → upS (thenS c (κ b))) (funext (λ a → cong (widenF̂ sub) (sym (renLsem-coh (S {τ = gnd (in′ op)}) ρ (ρ ,, b) (λ x → refl) g a)))))
  step2 : φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ b → upS (mapF̂ (0# +_) (thenS g1 (κ b))))
        ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-then sub g))) (val (vvar Z))) (ρ ,, b))
  step2 = cong (φ̂ˢ (promote k nh mH) op (Vsem v ρ)) (funext bAeq)

-- S-glocal: glocalS commutes with φ̂ˢ definitionally (widening the
-- membership witness by sub2 along the way); only the renLsem-coh bridge
-- remains, no collectX/bump/widenŴ-over-nodes reasoning needed.
lemma-B8-S∘-glocal : ∀ {Γ ℓ εH α ε₂ ε₁ ε} (op : Op ℓ) (v : Val Γ (gnd (out op)))
            (k : ContCxt Γ (gnd (in′ op)) εH α ε₁) (sub1 : ε₂ ⊆ᵉ ε₁) (sub2 : ε₁ ⊆ᵉ ε) (g : LC Γ α ε₂) (mH : ℓ ∈ εH) (nh : ¬ Handles k ℓ)
            (ρ : Env Γ)
          → Esem (glocalE sub1 sub2 (plugK k (opE mH op (val v))) g) ρ
          ≡ φ̂ˢ (sub2 (promote k nh mH)) op (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-glocal sub1 sub2 g))) (val (vvar Z))) (ρ ,, b))
lemma-B8-S∘-glocal {α = α} {ε₁ = ε₁} op v k sub1 sub2 g mH nh ρ = trans step1 step2
  where
  e₀ = plugK k (opE mH op (val v))
  g2 : ⟦ α ⟧ → R̂ ε₁
  g2 a = widenF̂ sub1 (Lsem g ρ a)
  κ : ⟦ in′ op ⟧ᴳ → Ŝ ε₁ ⟦ α ⟧
  κ b = Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, b)
  ih : Esem e₀ ρ ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) κ
  ih = lemma-B8 op v k mH nh ρ
  step1 : Esem (glocalE sub1 sub2 e₀ g) ρ ≡ φ̂ˢ (sub2 (promote k nh mH)) op (Vsem v ρ) (λ b → glocalS sub2 g2 (κ b))
  step1 = cong (glocalS sub2 g2) ih
  bAeq : ∀ b → glocalS sub2 g2 (κ b) ≡ Esem (plugK (weaken1K (S∘ k (S-glocal sub1 sub2 g))) (val (vvar Z))) (ρ ,, b)
  bAeq b = cong (λ c → glocalS sub2 c (κ b)) (funext (λ a → cong (widenF̂ sub1) (sym (renLsem-coh (S {τ = gnd (in′ op)}) ρ (ρ ,, b) (λ x → refl) g a))))
  step2 : φ̂ˢ (sub2 (promote k nh mH)) op (Vsem v ρ) (λ b → glocalS sub2 g2 (κ b))
        ≡ φ̂ˢ (sub2 (promote k nh mH)) op (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-glocal sub1 sub2 g))) (val (vvar Z))) (ρ ,, b))
  step2 = cong (φ̂ˢ (sub2 (promote k nh mH)) op (Vsem v ρ)) (funext bAeq)

-- S-handleB: h's own label ℓ' is DIFFERENT from the operation's label ℓ
-- (nh's inj₁ component rules out ℓ≡ℓ' -- promote's own S-handleB clause's
-- own reasoning). handlerStep's "different label" branch is a direct
-- pattern-match equation (no ext̂/handlerΨ-no-eq detour needed: it IS
-- exactly "pass through, demote the witness, recurse"), modulo bridging
-- Sig's own abstract `_≟ᵉ_` decision against our own hypothesis (both
-- rule out the same equality, but aren't the SAME proof TERM) --
-- demoteMem-irr below settles that: demoteMem only ever inspects its ¬_
-- argument in an already-absurd branch, so its result never actually
-- depends on which proof was supplied.
demoteMem-irr : ∀ {ℓ ℓ1 ε} (m : ℓ1 ∈ (ε ,ℓ ℓ)) (neq1 neq2 : ¬ (ℓ1 ≡ ℓ)) → demoteMem m neq1 ≡ demoteMem m neq2
demoteMem-irr {ε = ε} m neq1 neq2 with ∈-++⁻ ε m
... | inj₁ x         = refl
... | inj₂ (here eq) = ⊥-elim (neq1 eq)
... | inj₂ (there ())

promote-S-handleB-eq : ∀ {Γ ℓ σ εH α ℓ' par σ' ε} (k : ContCxt Γ σ εH α (ε ,ℓ ℓ')) (h : Handler Γ ℓ' par α σ' ε) (w : Val Γ (gnd par))
                        (nh : ¬ Handles (S∘ k (S-handleB h w)) ℓ) (mH : ℓ ∈ εH)
                     → promote (S∘ k (S-handleB h w)) nh mH ≡ demoteMem (promote k (λ hk → nh (inj₂ hk)) mH) (λ eq → nh (inj₁ eq))
promote-S-handleB-eq {ε = ε} k h w nh mH with ∈-++⁻ ε (promote k (λ hk → nh (inj₂ hk)) mH)
... | inj₁ m-old       = refl
... | inj₂ (here eq)   = ⊥-elim (nh (inj₁ eq))
... | inj₂ (there ())

lemma-B8-S∘-handleB : ∀ {Γ ℓ εH α ℓ' par σ' ε} (op : Op ℓ) (v : Val Γ (gnd (out op)))
            (k : ContCxt Γ (gnd (in′ op)) εH α (ε ,ℓ ℓ')) (h : Handler Γ ℓ' par α σ' ε) (w : Val Γ (gnd par))
            (mH : ℓ ∈ εH) (nh : ¬ Handles (S∘ k (S-handleB h w)) ℓ) (ρ : Env Γ)
          → Esem (handleE h (val w) (plugK k (opE mH op (val v)))) ρ
          ≡ φ̂ˢ (promote (S∘ k (S-handleB h w)) nh mH) op (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-handleB h w))) (val (vvar Z))) (ρ ,, b))
lemma-B8-S∘-handleB {ℓ = ℓ} {ℓ' = ℓ'} op v k h w mH nh ρ = mainStep
  where
  neq : ¬ (ℓ ≡ ℓ')
  neq eq = nh (inj₁ eq)
  nh' : ¬ Handles k ℓ
  nh' hk = nh (inj₂ hk)
  e₀ = plugK k (opE mH op (val v))
  κ : ⟦ in′ op ⟧ᴳ → Ŝ _ _
  κ b = Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, b)
  ih : Esem e₀ ρ ≡ φ̂ˢ (promote k nh' mH) op (Vsem v ρ) κ
  ih = lemma-B8 op v k mH nh' ρ
  step1 : Esem (handleE h (val w) e₀) ρ ≡ handlerSem h ρ (Vsem w ρ) (φ̂ˢ (promote k nh' mH) op (Vsem v ρ) κ)
  step1 = trans (bindŜ-unitˡ (λ p → handlerSem h ρ p (Esem e₀ ρ)) (Vsem w ρ))
                (cong (handlerSem h ρ (Vsem w ρ)) ih)
  -- handlerStep's own "no" branch fires -- but ℓ ≟ᵉ ℓ' is Sig's own
  -- abstract decision procedure, so its "no neq'" isn't the SAME proof
  -- term as our own `neq` (only propositionally equal in what it rules
  -- out) -- demoteMem-irr bridges the two (demoteMem only ever consults
  -- its ¬_ argument in an already-absurd branch, so it never actually
  -- depends on WHICH proof is supplied).
  step3 : handlerSem h ρ (Vsem w ρ) (φ̂ˢ (promote k nh' mH) op (Vsem v ρ) κ)
        ≡ φ̂ˢ (demoteMem (promote k nh' mH) neq) op (Vsem v ρ) (λ b → handlerSem h ρ (Vsem w ρ) (κ b))
  step3 = Ŝ-eq step3γ
    where
    step3γ : ∀ γ → runSelWith (handlerSem h ρ (Vsem w ρ) (φ̂ˢ (promote k nh' mH) op (Vsem v ρ) κ)) γ
                 ≡ runSelWith (φ̂ˢ (demoteMem (promote k nh' mH) neq) op (Vsem v ρ) (λ b → handlerSem h ρ (Vsem w ρ) (κ b))) γ
    step3γ γ with ℓ ≟ᵉ ℓ'
    ... | yes eq  = ⊥-elim (neq eq)
    ... | no neq' = cong (λ z → 0# , node z op (Vsem v ρ) (λ b → handlerSem h ρ (Vsem w ρ) (κ b)))
                          (demoteMem-irr (promote k nh' mH) neq' neq)
  bAeq : ∀ b → handlerSem h ρ (Vsem w ρ) (κ b) ≡ Esem (plugK (weaken1K (S∘ k (S-handleB h w))) (val (vvar Z))) (ρ ,, b)
  bAeq b = sym (trans (bindŜ-unitˡ (λ p → handlerSem (renH S h) (ρ ,, b) p (κ b)) (Vsem (weaken1V w) (ρ ,, b)))
                       (trans (cong (λ p → handlerSem (renH S h) (ρ ,, b) p (κ b)) (weaken1V-coh _ w ρ b))
                              (weaken1H-coh _ h ρ b (Vsem w ρ) (κ b))))
  mainStep : Esem (handleE h (val w) e₀) ρ
           ≡ φ̂ˢ (promote (S∘ k (S-handleB h w)) nh mH) op (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-handleB h w))) (val (vvar Z))) (ρ ,, b))
  mainStep = trans (trans step1 step3)
                   (trans (cong (λ m → φ̂ˢ m op (Vsem v ρ) (λ b → handlerSem h ρ (Vsem w ρ) (κ b))) (sym (promote-S-handleB-eq k h w nh mH)))
                          (cong (φ̂ˢ (promote (S∘ k (S-handleB h w)) nh mH) op (Vsem v ρ)) (funext bAeq)))

lemma-B8-S∘ : ∀ {Γ ℓ εH α β τ εO} (op : Op ℓ) (v : Val Γ (gnd (out op)))
            (k : ContCxt Γ (gnd (in′ op)) εH α β) (s : SFrame Γ α β τ εO) (mH : ℓ ∈ εH) (nh : ¬ Handles (S∘ k s) ℓ)
            (ρ : Env Γ)
          → Esem (plugK (S∘ k s) (opE mH op (val v))) ρ
          ≡ φ̂ˢ (promote (S∘ k s) nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K (S∘ k s)) (val (vvar Z))) (ρ ,, a))
lemma-B8-S∘ op v k S-reset mH nh ρ = lemma-B8-S∘-reset op v k mH nh ρ
lemma-B8-S∘ op v k (S-then sub g) mH nh ρ = lemma-B8-S∘-then op v k sub g mH nh ρ
lemma-B8-S∘ op v k (S-glocal sub1 sub2 g) mH nh ρ = lemma-B8-S∘-glocal op v k sub1 sub2 g mH nh ρ
lemma-B8-S∘ op v k (S-handleB h w) mH nh ρ = lemma-B8-S∘-handleB op v k h w mH nh ρ

-- Base case ▫: exactly the (op)(v) clause of Fig. 9, plus the Ŝ unit law.
lemma-B8 op v ▫ mH nh ρ = bindŜ-unitˡ (λ a → φ̂ˢ mH op a η̂ˢ) (Vsem v ρ)
lemma-B8 op v (F∘ k f) mH nh ρ = lemma-B8-F∘ op v k f mH nh ρ
lemma-B8 op v (S∘ k s) mH nh ρ = lemma-B8-S∘ op v k s mH nh ρ

-- ---------------------------------------------------------------------
-- Theorem 7.9 (hat-Theorem B.9): small-step soundness.
-- "Suppose e:σ!ε and g:σ→loss!ε1 with ε1⊆ε. Then
--    g⊢ε e --r--> e' ⟹ Ssem(e)⌊g⌋ = r·(Ssem(e')⌊g⌋)."
--
-- RESTATED FOR THIS CONSTRUCTION. agda_noparam's own version states this
-- via `tell`, Ŵ_ε's own loss-at-every-node embedding -- machinery this
-- construction does not have (Domains.agda's header: loss is tracked
-- SEPARATELY from the tree, a plain R × ŜStep pair). The direct analogue
-- of "tell r" at the (R × ŜStep) level is simply adding r to the FIRST
-- component and leaving the tree-shape (second component) untouched --
-- `addR` below. Because loss and tree-shape are decoupled by
-- construction, this formulation needs NEITHER `RootZero` NOR `WFStep`:
-- agda_noparam's own versions of both exist only to police an embedded-
-- loss invariant (every node's own root-loss field must be 0# before two
-- Ŵ-trees built at different loss-continuations can be safely compared/
-- combined) that simply has no counterpart here -- a value's own ŜStep
-- shape never carries a loss field to begin with. This is exactly why
-- Domains.agda's header motivates this construction in the first place.
-- ---------------------------------------------------------------------

addR : ∀ {ε X} → R → R × ŜStep ε X → R × ŜStep ε X
addR r (r0 , s) = (r + r0) , s

-- ⌊g⌋[sub,ρ] abbreviates the (necessarily widened, since Lsem g ρ : R̂ εg
-- for g's own εg⊆ε, not R̂ ε) loss-continuation used throughout.
⌊_⌋[_,_] : ∀ {Γ σ ε εg} → LC Γ σ εg → εg ⊆ᵉ ε → Env Γ → ⟦ σ ⟧ → R̂ ε
⌊ g ⌋[ sub , ρ ] a = widenF̂ sub (Lsem g ρ a)

-- ---------------------------------------------------------------------
-- Small helper facts about F̂/Ŝ's own combinators, needed below (none of
-- these have agda_noparam analogues -- they are about F̂'s plain-tree
-- shape and Ŝ's pair-valued runSelWith, both new to this construction).
-- ---------------------------------------------------------------------

mapF̂-fusion : ∀ {ε X Y Z} (f : Y → Z) (g : X → Y) (t : F̂ ε X) → mapF̂ f (mapF̂ g t) ≡ mapF̂ (λ x → f (g x)) t
mapF̂-fusion f g (pure x)      = refl
mapF̂-fusion f g (opF̂ m o v κ) = cong (opF̂ m o v) (funext (λ a → mapF̂-fusion f g (κ a)))

widenF̂-refl : ∀ {ε X} (t : F̂ ε X) → widenF̂ ⊆ᵉ-refl t ≡ t
widenF̂-refl (pure x)      = refl
widenF̂-refl (opF̂ m o v κ) = cong (opF̂ m o v) (funext (λ a → widenF̂-refl (κ a)))

-- thenS g1'(upS W) ≡ bindF̂ W g1': running upS's own γ-independent report
-- W through thenS at continuation g1' just re-binds every LEAF of W via
-- g1' (F̂'s own bind) -- upS's own always-0# accumulated loss at every
-- step contributes nothing once stripped via +-identityˡ. By induction on
-- W (upS/thenS both recurse in lock-step on W's shape); each level
-- contributes its own "+0#" independently, so +-identityˡ has to be
-- applied afresh at every level (not just once at the root).
mapF̂-0+-elim : ∀ {ε} (t : F̂ ε R) → mapF̂ (0# +_) t ≡ t
mapF̂-0+-elim t = trans (mapF̂-cong (λ y → +-identityˡ y) t) (mapF̂-id t)

thenS-upS : ∀ {ε X} (g1' : X → R̂ ε) (W : F̂ ε X) → thenS g1' (upS W) ≡ bindF̂ W g1'
thenS-upS g1' (pure x)      = mapF̂-0+-elim (g1' x)
thenS-upS g1' (opF̂ m o v κ) = cong (opF̂ m o v) (funext (λ a →
  trans (cong (mapF̂ (0# +_)) (thenS-upS g1' (κ a))) (mapF̂-0+-elim (bindF̂ (κ a) g1')) ))

-- bindŜ-addR: if P,P' agree up to a uniform r-shift SPECIFICALLY at
-- γ' := λx→thenS γ(D x) (the one bindŜ's own definition feeds P/P'
-- through -- its own proof, below, never needs the hypothesis at any
-- OTHER continuation, so this is stated at exactly that one point, not
-- universally), then so do bindŜ P D and bindŜ P' D at γ. Needed for
-- (F-rule) below, whose own IH (theorem-B9 itself, fixed at one
-- particular γ) can only ever supply a fact at one continuation too.
bindŜ-addR : ∀ {ε X Y} (r : R) (P P' : Ŝ ε X) (D : X → Ŝ ε Y) (γ : Y → R̂ ε)
           → runSelWith P (λ x → thenS γ (D x)) ≡ addR r (runSelWith P' (λ x → thenS γ (D x)))
           → runSelWith (bindŜ P D) γ ≡ addR r (runSelWith (bindŜ P' D) γ)
bindŜ-addR r P P' D γ hyp
  with runSelWith P' (λ x → thenS γ (D x)) | hyp
... | r1 , leaf x       | eq rewrite eq = let (r2 , w) = runSelWith (D x) γ in cong (λ z → z , w) (+-assoc r r1 r2)
... | r1 , node m o v κ | eq rewrite eq = refl

-- glocalS-addR: same shape of fact for glocalS -- simpler than bindŜ's
-- own version (no arithmetic at all: glocalS's leaf case passes the
-- accumulated loss straight through unchanged, and its node case doesn't
-- touch the loss component either).
glocalS-addR : ∀ {ε₁ ε X} (r : R) (sub : ε₁ ⊆ᵉ ε) (P P' : Ŝ ε₁ X) (g1' : X → R̂ ε₁) (γ : X → R̂ ε)
             → runSelWith P g1' ≡ addR r (runSelWith P' g1')
             → runSelWith (glocalS sub g1' P) γ ≡ addR r (runSelWith (glocalS sub g1' P') γ)
glocalS-addR r sub P P' g1' γ eq with runSelWith P' g1' | eq
... | r1 , leaf x       | eq' rewrite eq' = refl
... | r1 , node m o v κ | eq' rewrite eq' = refl

-- handlerStep-addR: same shape of fact for handlerStep's own dispatch
-- (needed for (S1) below). The clause-evaluation branch (same label)
-- looks the most delicate -- it calls out to `Esem (clause h o) (...)`,
-- built from l1v/k1v -- but l1v/k1v only ever close over γ/κ/o/p, never
-- over the incoming accumulated loss (r/r1 here), so the SAME clause
-- evaluation (same r2,w2) occurs on both sides regardless of the shift;
-- only +-assoc is needed, exactly as in bindŜ-addR's leaf case.
handlerStep-addR : ∀ {Γ ε ℓ par σ σ'} (r : R) (h : Handler Γ ℓ par σ σ' ε) (ρ : Env Γ) (γ : ⟦ σ' ⟧ → R̂ ε) (p : ⟦ gnd par ⟧)
                    (X X' : R × ŜStep (ε ,ℓ ℓ) ⟦ σ ⟧)
                  → X ≡ addR r X'
                  → handlerStep h ρ γ p X ≡ addR r (handlerStep h ρ γ p X')
handlerStep-addR {ℓ = ℓ} r h ρ γ p X X'@(r1 , leaf x) eq rewrite eq =
  let (r2 , w2) = runSelWith (handlerRet h ρ x p) γ in cong (λ z → z , w2) (+-assoc r r1 r2)
handlerStep-addR {ℓ = ℓ} r h ρ γ p X X'@(r1 , node {ℓ = ℓ1} m o v κ) eq rewrite eq with ℓ1 ≟ᵉ ℓ
... | yes eqℓ with eqℓ
...   | refl = let (r2 , w2) = runSelWith (Esem (clause h o) (((( ρ ,, p) ,, v) ,, l1v h ρ γ o κ) ,, k1v h ρ γ o κ)) γ
               in cong (λ z → z , w2) (+-assoc r r1 r2)
handlerStep-addR {ℓ = ℓ} r h ρ γ p X X'@(r1 , node {ℓ = ℓ1} m o v κ) eq | no neq = refl

-- thenS-addR: thenS's own version -- if P,P' agree up to an r-shift at
-- g1' (the FIXED continuation thenS itself collapses through), their
-- reports agree up to a mapF̂(r+_) wrap. Needed for (S2) below. No
-- recursion on P's own structure: the hypothesis already pins down
-- P's whole (loss,shape) pair at g1' in terms of P''s, so a single case
-- split (mirroring thenS's own definition) plus mapF̂-fusion/-cong
-- (+-assoc) suffices -- the SAME recursive subterm `thenS g1' (κ a)`
-- appears on both sides of the node case, untouched.
thenS-addR : ∀ {ε X} (r : R) (g1' : X → R̂ ε) (P P' : Ŝ ε X)
           → runSelWith P g1' ≡ addR r (runSelWith P' g1')
           → thenS g1' P ≡ mapF̂ (r +_) (thenS g1' P')
thenS-addR r g1' P P' eq with runSelWith P' g1' | eq
... | r1 , leaf x       | eq' rewrite eq' =
  trans (mapF̂-cong (λ y → +-assoc r r1 y) (g1' x)) (sym (mapF̂-fusion (r +_) (r1 +_) (g1' x)))
... | r1 , node m o v κ | eq' rewrite eq' =
  cong (opF̂ m o v) (funext (λ a →
    trans (mapF̂-cong (λ y → +-assoc r r1 y) (thenS g1' (κ a))) (sym (mapF̂-fusion (r +_) (r1 +_) (thenS g1' (κ a))))))

-- bindF̂-unitʳ: F̂'s own right unit law (bindF̂ W pure ≡ W) -- needed for
-- (S2) below, to show a NESTED thenE's own report, re-collapsed through
-- Lsem's canonical `pure` continuation, is unchanged.
bindF̂-unitʳ : ∀ {ε X} (W : F̂ ε X) → bindF̂ W pure ≡ W
bindF̂-unitʳ (pure x)      = refl
bindF̂-unitʳ (opF̂ m o v κ) = cong (opF̂ m o v) (funext (λ a → bindF̂-unitʳ (κ a)))

-- resetS-eq: if P,P' agree up to an r-shift at γ, resetS discards the
-- shift entirely -- resetS P and resetS P' agree EXACTLY (not merely up
-- to a further shift) at every continuation.
resetS-eq : ∀ {ε X} (r : R) (P P' : Ŝ ε X) (γ : X → R̂ ε)
          → runSelWith P γ ≡ addR r (runSelWith P' γ)
          → runSelWith (resetS P) γ ≡ runSelWith (resetS P') γ
resetS-eq r P P' γ eq with runSelWith P' γ | eq
... | r1 , leaf x       | eq' rewrite eq' = refl
... | r1 , node m o v κ | eq' rewrite eq' = refl

addR-0 : ∀ {ε X} (p : R × ŜStep ε X) → addR 0# p ≡ p
addR-0 (r , s) = cong (λ z → z , s) (+-identityˡ r)

-- ---------------------------------------------------------------------
-- WFG/WFE: a syntactic well-formedness restriction on loss-continuations
-- (and, recursively, on the expressions embedding them), needed to close
-- (R7)'s gap. WFG g restricts g to the "canonical" continuations built by
-- repeatedly wrapping the base zero continuation via thenE -- the
-- grammar g ::= (λx→0) | thenE e g. Every such g's OWN Vsem is, by
-- construction, upS-wrapped (η̂ˢ for zeroLC; upS(...) directly for the
-- thenE case, per Denotational.agda's own `Esem (thenE ...)` clause),
-- hence γ-INDEPENDENT -- exactly what (R7)'s gap needed: relating
-- Esem(e[v]) queried at Lsem's own `pure` continuation (used by thenE)
-- against the SAME e[v] queried at glocalE's own (differently-shaped,
-- but ALSO γ-independent once its own driving g is WFG) continuation.
--
-- WFG does NOT require its own embedded e (thenE's first argument --
-- "the rest of g's body", never reached by a SINGLE step of theorem-B9's
-- own induction, since no reduction rule here steps under a binder
-- without first substituting) to itself be WFE: upS-wrapping makes g's
-- own top-level Vsem γ-independent unconditionally, regardless of e.
--
-- WFE lifts WFG to expressions: every thenE/glocalE subterm's own
-- g/g1-argument, at the top level of each subexpression theorem-B9's own
-- congruence-based induction can reach within a SINGLE step, must be
-- WFG. Values (wf-val) are left unconstrained -- their own vabs bodies
-- are, likewise, not reached within a single step.
-- ---------------------------------------------------------------------

-- WFV/WFH extend WFE's own reach INTO value/handler bodies (vabs's own
-- expression, a handler's own clause/ret bodies) -- exactly the pieces
-- WFE alone (see above) never needed for theorem-B9's single-step
-- scope, but which DO get exposed once a value/handler is actually
-- substituted into (R3's e[v], R5/R6's clause/ret instantiation, S1's
-- retApplied), i.e. exactly the extra invariant preservation-across-
-- steps (needed for the big-step theorems, B10a/B10b) requires. Declared
-- mutually with WFE/WFG since Val/Handler/_⊢_!_ themselves are.
mutual
  data WFV {Γ} : ∀ {σ} → Val Γ σ → Set
  data WFH {Γ} : ∀ {ℓ par σ σ' ε} → Handler Γ ℓ par σ σ' ε → Set
  data WFE {Γ} : ∀ {σ ε} → Γ ⊢ σ ! ε → Set
  data WFG {Γ ε} : ∀ {σ} → LC Γ σ ε → Set

  data WFV {Γ} where
    wf-vvar  : ∀ {σ} (x : Γ ∋ σ) → WFV (vvar x)
    wf-vgnd  : ∀ {γ} (x : ⟦ γ ⟧ᴳ) → WFV (vgnd {γ = γ} x)
    wf-vpair : ∀ {σ τ} {v : Val Γ σ} {w : Val Γ τ} → WFV v → WFV w → WFV (vpair v w)
    wf-vabs  : ∀ {σ τ ε} {e : (Γ , σ) ⊢ τ ! ε} → WFE e → WFV (vabs e)

  data WFH {Γ} where
    wf-handler : ∀ {ℓ par σ σ' ε} {h : Handler Γ ℓ par σ σ' ε}
               → (∀ op → WFE (clause h op)) → WFE (ret h) → WFH h

  data WFE {Γ} where
    wf-val    : ∀ {σ ε} {v : Val Γ σ} → WFV v → WFE {ε = ε} (val v)
    wf-fun    : ∀ {γ δ ε} {f : PrimFun γ δ} {e : Γ ⊢ gnd γ ! ε} → WFE e → WFE (fun f e)
    wf-pair   : ∀ {σ τ ε} {e1 : Γ ⊢ σ ! ε} {e2 : Γ ⊢ τ ! ε} → WFE e1 → WFE e2 → WFE (pair e1 e2)
    wf-fst    : ∀ {σ τ ε} {e : Γ ⊢ (σ `× τ) ! ε} → WFE e → WFE (fst e)
    wf-snd    : ∀ {σ τ ε} {e : Γ ⊢ (σ `× τ) ! ε} → WFE e → WFE (snd e)
    wf-app    : ∀ {σ τ ε} {e1 : Γ ⊢ (σ ⇒ τ ! ε) ! ε} {e2 : Γ ⊢ σ ! ε} → WFE e1 → WFE e2 → WFE (app e1 e2)
    wf-op     : ∀ {ℓ ε} {m : ℓ ∈ ε} {op : Op ℓ} {e : Γ ⊢ gnd (out op) ! ε} → WFE e → WFE (opE m op e)
    wf-loss   : ∀ {ε} {e : Γ ⊢ Loss ! ε} → WFE e → WFE (lossE e)
    wf-then   : ∀ {σ ε ε₁} {sub : ε₁ ⊆ᵉ ε} {e1 : Γ ⊢ σ ! ε} {g : LC Γ σ ε₁} → WFE e1 → WFG g → WFE (thenE sub e1 g)
    wf-glocal : ∀ {σ ε₂ ε₁ ε} {sub1 : ε₂ ⊆ᵉ ε₁} {sub2 : ε₁ ⊆ᵉ ε} {e : Γ ⊢ σ ! ε₁} {g : LC Γ σ ε₂} → WFE e → WFG g → WFE (glocalE sub1 sub2 e g)
    wf-reset  : ∀ {σ ε} {e : Γ ⊢ σ ! ε} → WFE e → WFE (resetE e)
    wf-handle : ∀ {ℓ par σ σ' ε} {h : Handler Γ ℓ par σ σ' ε} {e1 : Γ ⊢ gnd par ! ε} {e2 : Γ ⊢ σ ! (ε ,ℓ ℓ)}
              → WFH h → WFE e1 → WFE e2 → WFE (handleE h e1 e2)

  data WFG {Γ ε} where
    wf-zero : ∀ {σ} → WFG {σ = σ} zeroLC
    wf-then : ∀ {σ σ' εg} {sub : εg ⊆ᵉ ε} {e : (Γ , σ) ⊢ σ' ! ε} {g' : LC (Γ , σ) σ' εg}
            → WFE e → WFG g' → WFG (vabs (thenE sub e g'))

-- WFV-renV/WFH-renH/WFE-renE/WFG-renV: renaming preserves well-formedness
-- (mutually, mirroring renV/renH/renE's own mutual structure) -- a
-- building block for WFsub-ext below (extS's own S-case weakens an
-- existing value via renV).
mutual
  WFV-renV : ∀ {Γ Γ' σ} (ρ : Ren Γ Γ') {v : Val Γ σ} → WFV v → WFV (renV ρ v)
  WFV-renV ρ (wf-vvar x)    = wf-vvar (ρ x)
  WFV-renV ρ (wf-vgnd x)    = wf-vgnd x
  WFV-renV ρ (wf-vpair v w) = wf-vpair (WFV-renV ρ v) (WFV-renV ρ w)
  WFV-renV ρ (wf-vabs e)    = wf-vabs (WFE-renE (extR ρ) e)

  WFH-renH : ∀ {Γ Γ' ℓ par σ σ' ε} (ρ : Ren Γ Γ') {h : Handler Γ ℓ par σ σ' ε} → WFH h → WFH (renH ρ h)
  WFH-renH ρ (wf-handler wfc wfr) =
    wf-handler (λ op → WFE-renE (extR (extR (extR (extR ρ)))) (wfc op)) (WFE-renE (extR (extR ρ)) wfr)

  WFE-renE : ∀ {Γ Γ' σ ε} (ρ : Ren Γ Γ') {e : Γ ⊢ σ ! ε} → WFE e → WFE (renE ρ e)
  WFE-renE ρ (wf-val v)          = wf-val (WFV-renV ρ v)
  WFE-renE ρ (wf-fun wfe)        = wf-fun (WFE-renE ρ wfe)
  WFE-renE ρ (wf-pair wfe1 wfe2) = wf-pair (WFE-renE ρ wfe1) (WFE-renE ρ wfe2)
  WFE-renE ρ (wf-fst wfe)        = wf-fst (WFE-renE ρ wfe)
  WFE-renE ρ (wf-snd wfe)        = wf-snd (WFE-renE ρ wfe)
  WFE-renE ρ (wf-app wfe1 wfe2)  = wf-app (WFE-renE ρ wfe1) (WFE-renE ρ wfe2)
  WFE-renE ρ (wf-op wfe)         = wf-op (WFE-renE ρ wfe)
  WFE-renE ρ (wf-loss wfe)       = wf-loss (WFE-renE ρ wfe)
  WFE-renE ρ (wf-then wfe wfg)   = wf-then (WFE-renE ρ wfe) (WFG-renV ρ wfg)
  WFE-renE ρ (wf-glocal wfe wfg) = wf-glocal (WFE-renE ρ wfe) (WFG-renV ρ wfg)
  WFE-renE ρ (wf-reset wfe)      = wf-reset (WFE-renE ρ wfe)
  WFE-renE ρ (wf-handle wfh wfe1 wfe2) = wf-handle (WFH-renH ρ wfh) (WFE-renE ρ wfe1) (WFE-renE ρ wfe2)

  WFG-renV : ∀ {Γ Γ' σ ε} (ρ : Ren Γ Γ') {g : LC Γ σ ε} → WFG g → WFG (renV ρ g)
  WFG-renV ρ wf-zero            = wf-zero
  WFG-renV ρ (wf-then wfe wfg') = wf-then (WFE-renE (extR ρ) wfe) (WFG-renV (extR ρ) wfg')

-- WFsub: a substitution σs : Sub Γ Γ' is well-formed if every value it
-- sends a variable to is itself WFV -- exactly the hypothesis
-- WFV/WFH/WFE-subV/subH/subE need below, mirroring subV/subH/subE's own
-- mutual structure.
WFsub : ∀ {Γ Γ'} → Sub Γ Γ' → Set
WFsub {Γ} σs = ∀ {σ} (x : Γ ∋ σ) → WFV (σs x)

WFsub-ext : ∀ {Γ Γ' τ} {σs : Sub Γ Γ'} → WFsub σs → WFsub (extS {τ = τ} σs)
WFsub-ext wfσs Z     = wf-vvar Z
WFsub-ext wfσs (S x) = WFV-renV S (wfσs x)

mutual
  WFV-subV : ∀ {Γ Γ' σ} {σs : Sub Γ Γ'} → WFsub σs → {v : Val Γ σ} → WFV v → WFV (subV σs v)
  WFV-subV wfσs (wf-vvar x)    = wfσs x
  WFV-subV wfσs (wf-vgnd x)    = wf-vgnd x
  WFV-subV wfσs (wf-vpair v w) = wf-vpair (WFV-subV wfσs v) (WFV-subV wfσs w)
  WFV-subV wfσs (wf-vabs e)    = wf-vabs (WFE-subE (WFsub-ext wfσs) e)

  WFH-subH : ∀ {Γ Γ' ℓ par σ σ' ε} {σs : Sub Γ Γ'} → WFsub σs → {h : Handler Γ ℓ par σ σ' ε} → WFH h → WFH (subH σs h)
  WFH-subH wfσs (wf-handler wfc wfr) =
    wf-handler (λ op → WFE-subE (WFsub-ext (WFsub-ext (WFsub-ext (WFsub-ext wfσs)))) (wfc op))
               (WFE-subE (WFsub-ext (WFsub-ext wfσs)) wfr)

  WFE-subE : ∀ {Γ Γ' σ ε} {σs : Sub Γ Γ'} → WFsub σs → {e : Γ ⊢ σ ! ε} → WFE e → WFE (subE σs e)
  WFE-subE wfσs (wf-val v)          = wf-val (WFV-subV wfσs v)
  WFE-subE wfσs (wf-fun wfe)        = wf-fun (WFE-subE wfσs wfe)
  WFE-subE wfσs (wf-pair wfe1 wfe2) = wf-pair (WFE-subE wfσs wfe1) (WFE-subE wfσs wfe2)
  WFE-subE wfσs (wf-fst wfe)        = wf-fst (WFE-subE wfσs wfe)
  WFE-subE wfσs (wf-snd wfe)        = wf-snd (WFE-subE wfσs wfe)
  WFE-subE wfσs (wf-app wfe1 wfe2)  = wf-app (WFE-subE wfσs wfe1) (WFE-subE wfσs wfe2)
  WFE-subE wfσs (wf-op wfe)         = wf-op (WFE-subE wfσs wfe)
  WFE-subE wfσs (wf-loss wfe)       = wf-loss (WFE-subE wfσs wfe)
  WFE-subE wfσs (wf-then wfe wfg)   = wf-then (WFE-subE wfσs wfe) (WFG-subV wfσs wfg)
  WFE-subE wfσs (wf-glocal wfe wfg) = wf-glocal (WFE-subE wfσs wfe) (WFG-subV wfσs wfg)
  WFE-subE wfσs (wf-reset wfe)      = wf-reset (WFE-subE wfσs wfe)
  WFE-subE wfσs (wf-handle wfh wfe1 wfe2) = wf-handle (WFH-subH wfσs wfh) (WFE-subE wfσs wfe1) (WFE-subE wfσs wfe2)

  WFG-subV : ∀ {Γ Γ' σ ε} {σs : Sub Γ Γ'} → WFsub σs → {g : LC Γ σ ε} → WFG g → WFG (subV σs g)
  WFG-subV wfσs wf-zero            = wf-zero
  WFG-subV wfσs (wf-then wfe wfg') = wf-then (WFE-subE (WFsub-ext wfσs) wfe) (WFG-subV (WFsub-ext wfσs) wfg')

-- WFsub-idSub/WFsub-cons: the two building blocks every concrete
-- substitution used by R3/R5/R6/R7/S1 (_[_], sub1, and the explicit
-- cons-chains) is assembled from.
WFsub-idSub : ∀ {Γ} → WFsub (idSub {Γ})
WFsub-idSub x = wf-vvar x

WFsub-cons : ∀ {Γ Γ' τ} {v : Val Γ' τ} {σs : Sub Γ Γ'} → WFV v → WFsub σs → WFsub (cons v σs)
WFsub-cons wfv wfσs Z     = wfv
WFsub-cons wfv wfσs (S x) = wfσs x

WFsub-sub1 : ∀ {Γ σ} {v : Val Γ σ} → WFV v → WFsub (sub1 v)
WFsub-sub1 wfv = WFsub-cons wfv WFsub-idSub

WFsub-wkSub : ∀ {Γ τ} → WFsub (wkSub {Γ} {τ})
WFsub-wkSub x = wf-vvar (S x)

-- WFE-[]: the R3/R7-specific substitution instance -- e[v] is WFE
-- whenever e and v both are.
WFE-[] : ∀ {Γ σ τ ε} {e : (Γ , σ) ⊢ τ ! ε} {v : Val Γ σ} → WFE e → WFV v → WFE (e [ v ])
WFE-[] wfe wfv = WFE-subE (WFsub-sub1 wfv) wfe

-- WFE-plugF: (F-rule)'s own extraction lemma -- the hole's own WFE-ness,
-- read off WFE(plugF f e) by cases on f (matching WFE's own constructor
-- for each of the nine regular-frame shapes exactly).
WFE-plugF : ∀ {Γ α ε τ} (f : Frame Γ α ε τ ε) {e : Γ ⊢ α ! ε} → WFE (plugF f e) → WFE e
WFE-plugF (F-fun pf)     (wf-fun wfe)      = wfe
WFE-plugF (F-pairL e₂)   (wf-pair wfe _)   = wfe
WFE-plugF (F-pairR v)    (wf-pair _ wfe)   = wfe
WFE-plugF F-fst          (wf-fst wfe)      = wfe
WFE-plugF F-snd          (wf-snd wfe)      = wfe
WFE-plugF (F-appL e₂)    (wf-app wfe _)    = wfe
WFE-plugF (F-appR v)     (wf-app _ wfe)    = wfe
WFE-plugF (F-op m op)    (wf-op wfe)       = wfe
WFE-plugF F-loss         (wf-loss wfe)     = wfe
WFE-plugF (F-handleP h b) (wf-handle _ wfe _) = wfe

-- WFE-plugS: WFE-plugF's own analogue for the four SFrame shapes.
WFE-plugS : ∀ {Γ α ε τ ε'} (s : SFrame Γ α ε τ ε') {e : Γ ⊢ α ! ε} → WFE (plugS s e) → WFE e
WFE-plugS (S-handleB h v)      (wf-handle _ _ wfe)   = wfe
WFE-plugS (S-then sub g)       (wf-then wfe _)       = wfe
WFE-plugS (S-glocal sub1 sub2 g) (wf-glocal wfe _)   = wfe
WFE-plugS S-reset               (wf-reset wfe)       = wfe

-- WFE-plugK: WFE-plugF/WFE-plugS's own analogue for a whole ContCxt,
-- recursing outside-in exactly as plugK itself is built.
WFE-plugK : ∀ {Γ σ ε τ ε'} (k : ContCxt Γ σ ε τ ε') {e : Γ ⊢ σ ! ε} → WFE (plugK k e) → WFE e
WFE-plugK ▫        wfe  = wfe
WFE-plugK (F∘ {β = β} k f) wfpe with Frame-effect-eq f
... | refl = WFE-plugK k (WFE-plugF f wfpe)
WFE-plugK (S∘ k s) wfpe = WFE-plugK k (WFE-plugS s wfpe)

-- WFE-plugF-fill/WFE-plugS-fill: the REVERSE direction of WFE-plugF/
-- WFE-plugS -- given the ORIGINAL hole's WFE-ness just to read off the
-- frame's own embedded data (v/h/b), swap in a DIFFERENT WFE hole e'
-- (same Γ, no renaming) and conclude the whole plugged expression is
-- still WFE. Used by (F-rule)/(S1)/(S2)/(S3)/(S4)'s own OUTER
-- conclusion, once the INNER premise's own e' has been produced.
WFE-plugF-fill : ∀ {Γ α ε τ} (f : Frame Γ α ε τ ε) {e e' : Γ ⊢ α ! ε} → WFE (plugF f e) → WFE e' → WFE (plugF f e')
WFE-plugF-fill (F-fun pf)      (wf-fun _)             wfe' = wf-fun wfe'
WFE-plugF-fill (F-pairL e₂)    (wf-pair _ wfe2)       wfe' = wf-pair wfe' wfe2
WFE-plugF-fill (F-pairR v)     (wf-pair wfv _)        wfe' = wf-pair wfv wfe'
WFE-plugF-fill F-fst           (wf-fst _)             wfe' = wf-fst wfe'
WFE-plugF-fill F-snd           (wf-snd _)             wfe' = wf-snd wfe'
WFE-plugF-fill (F-appL e₂)     (wf-app _ wfe2)        wfe' = wf-app wfe' wfe2
WFE-plugF-fill (F-appR v)      (wf-app wfv _)         wfe' = wf-app wfv wfe'
WFE-plugF-fill (F-op m op)     (wf-op _)              wfe' = wf-op wfe'
WFE-plugF-fill F-loss          (wf-loss _)            wfe' = wf-loss wfe'
WFE-plugF-fill (F-handleP h b) (wf-handle wfh _ wfb)  wfe' = wf-handle wfh wfe' wfb

-- WFE-frame-fill: F-rule's own need -- fill a WEAKENED frame (its own
-- embedded data renamed via S) with an ARBITRARY WFE hole e' at the
-- extended context, reading the frame's own embedded data off the
-- ORIGINAL (unweakened) hole's WFE-ness. Specializing e' to
-- val(vvar Z) gives exactly F-rule's own synthesized-continuation body
-- plugF(weaken1F f)(val(vvar Z)); the general e' form is what R5's own
-- k'/yArg construction (via WFE-plugK-ren-fill below) needs instead.
WFE-frame-fill : ∀ {Γ α ε τ υ} (f : Frame Γ α ε τ ε) {e : Γ ⊢ α ! ε} {e' : (Γ , υ) ⊢ α ! ε}
                → WFE (plugF f e) → WFE e' → WFE (plugF (weaken1F f) e')
WFE-frame-fill (F-fun pf)      _                        wfe' = wf-fun wfe'
WFE-frame-fill (F-pairL e₂)    (wf-pair _ wfe2)         wfe' = wf-pair wfe' (WFE-renE S wfe2)
WFE-frame-fill (F-pairR v)     (wf-pair (wf-val wfv) _) wfe' = wf-pair (wf-val (WFV-renV S wfv)) wfe'
WFE-frame-fill F-fst           _                        wfe' = wf-fst wfe'
WFE-frame-fill F-snd           _                        wfe' = wf-snd wfe'
WFE-frame-fill (F-appL e₂)     (wf-app _ wfe2)          wfe' = wf-app wfe' (WFE-renE S wfe2)
WFE-frame-fill (F-appR v)      (wf-app (wf-val wfv) _)  wfe' = wf-app (wf-val (WFV-renV S wfv)) wfe'
WFE-frame-fill (F-op m op)     _                        wfe' = wf-op wfe'
WFE-frame-fill F-loss          _                        wfe' = wf-loss wfe'
WFE-frame-fill (F-handleP h b) (wf-handle wfh _ wfb)    wfe' = wf-handle (WFH-renH S wfh) wfe' (WFE-renE S wfb)

-- WFE-sframe-fill: WFE-frame-fill's own analogue for SFrame, needed by
-- WFE-plugK-ren-fill below (R5's own k'/yArg construction weakens EVERY
-- frame along k, regular or special, via weaken1K = renK S).
WFE-sframe-fill : ∀ {Γ α ε τ ε' υ} (s : SFrame Γ α ε τ ε') {e : Γ ⊢ α ! ε} {e' : (Γ , υ) ⊢ α ! ε}
                 → WFE (plugS s e) → WFE e' → WFE (plugS (renS S s) e')
WFE-sframe-fill (S-handleB h v)      (wf-handle wfh (wf-val wfv) _) wfe' = wf-handle (WFH-renH S wfh) (wf-val (WFV-renV S wfv)) wfe'
WFE-sframe-fill (S-then sub g)       (wf-then _ wfg)        wfe' = wf-then wfe' (WFG-renV S wfg)
WFE-sframe-fill (S-glocal sub1 sub2 g) (wf-glocal _ wfg)    wfe' = wf-glocal wfe' (WFG-renV S wfg)
WFE-sframe-fill S-reset               (wf-reset _)          wfe' = wf-reset wfe'

-- WFE-plugK-ren-fill: R5's own need -- fill plugK's weakened context
-- (weaken1K k, at the FRESH z-context) with an arbitrary WFE hole e',
-- reading k's own embedded frame data off the ORIGINAL hole's WFE-ness,
-- recursing exactly as WFE-plugK/plugK itself does.
WFE-plugK-ren-fill : ∀ {Γ σ ε τ ε' υ} (k : ContCxt Γ σ ε τ ε') {e : Γ ⊢ σ ! ε} {e' : (Γ , υ) ⊢ σ ! ε}
                    → WFE (plugK k e) → WFE e' → WFE (plugK (weaken1K k) e')
WFE-plugK-ren-fill ▫        wfpe wfe' = wfe'
WFE-plugK-ren-fill (F∘ {β = β} k f) wfpe wfe' with Frame-effect-eq f
... | refl = WFE-frame-fill f wfpe (WFE-plugK-ren-fill k (WFE-plugF f wfpe) wfe')
WFE-plugK-ren-fill (S∘ k s) wfpe wfe' = WFE-sframe-fill s wfpe (WFE-plugK-ren-fill k (WFE-plugS s wfpe) wfe')

-- WFG-e[v]: R7's own need -- if g = vabs e is WFG, then substituting a
-- WFV value v into e's own body is WFE. Case on WFG's own two possible
-- shapes: zeroLC (e ≡ val(vgnd 0#), substitution is a no-op) or
-- vabs(thenE sub e' g') (e ≡ thenE sub e' g', WFE-[]/WFG-subV push the
-- substitution through each component).
WFG-e[v] : ∀ {Γ σ ε} {e : (Γ , σ) ⊢ Loss ! ε} → WFG (vabs e) → {v : Val Γ σ} → WFV v → WFE (e [ v ])
WFG-e[v] wf-zero              wfv = wf-val (wf-vgnd _)
WFG-e[v] (wf-then wfe' wfg')  wfv = wf-then (WFE-[] wfe' wfv) (WFG-subV (WFsub-sub1 wfv) wfg')

-- retApplied-wf: S1's own need -- retApplied h v = ret h with z bound to
-- (v, the fresh var), so its WFE-ness follows from WFH h's own WFE(ret
-- h) via WFE-subE, given the specific substitution retApplied itself
-- uses (cons (vvar Z) (cons (weaken1V v) wkSub)).
retApplied-wf : ∀ {Γ ℓ par σ σ' ε} {h : Handler Γ ℓ par σ σ' ε} {v : Val Γ (gnd par)} → WFH h → WFV v → WFE (retApplied h v)
retApplied-wf (wf-handler wfc wfr) wfv =
  WFE-subE (WFsub-cons (wf-vvar Z) (WFsub-cons (WFV-renV S wfv) WFsub-wkSub)) wfr

-- WFG-upS: a WFG continuation's own Vsem is ALWAYS upS-wrapped -- exactly
-- η̂ˢ's/thenE's OWN `Esem` clauses, unfolding directly by cases on the
-- WFG derivation (no induction on the embedded e needed at all, per
-- WFG's own header comment).
WFG-upS : ∀ {Γ σ ε} {g : LC Γ σ ε} → WFG g → (ρ : Env Γ) (a : ⟦ σ ⟧) → Σ (F̂ ε R) (λ W → Vsem g ρ a ≡ upS W)
WFG-upS wf-zero ρ a = pure 0# , refl
WFG-upS (wf-then {sub = sub} {e = e} {g' = g'} _ wfg') ρ a =
  thenS (λ b → widenF̂ sub (Lsem g' (ρ ,, a) b)) (Esem e (ρ ,, a)) , refl

-- R7-core: the general, WFG-free fact underlying (R7) -- for ANY F̂
-- report W, wrapping it via glocalE's own (zeroLC-driven) route agrees,
-- AS Ŝ VALUES (not merely at one continuation), with re-wrapping it via
-- thenE's own route. `thenS pure (upS W) ≡ W` (thenS-upS + bindF̂-unitʳ,
-- already proven) collapses thenE's own extra `thenS pure` roundtrip
-- away entirely BEFORE this lemma is even invoked (see
-- theorem-B9-R7's own `Lsem-eq` below), which is what keeps the
-- induction here from re-accumulating an extra "+0#" layer at every
-- level the way thenS-upS itself has to. The recursive node case needs
-- the node's own continuation to ALSO be upS-wrapped, which holds
-- unconditionally, at every depth, by upS's own definition
-- (`upS(opF̂ m o v κ)`'s own continuation is literally `λa→upS(κ a)`) --
-- not by any further use of WFG.
R7-core : ∀ {εg ε} (sub : εg ⊆ᵉ ε) (W : F̂ εg R)
        → upS (mapF̂ (0# +_) (widenF̂ sub W)) ≡ glocalS sub (λ (_ : R) → pure (0# + 0#)) (upS W)
R7-core sub (pure y)      = Ŝ-eq (λ γ → cong (λ z → 0# , leaf z) (+-identityˡ y))
R7-core sub (opF̂ m o v κ) = Ŝ-eq (λ γ → cong (λ f → 0# , node (sub m) o v f) (funext (λ a → R7-core sub (κ a))))

-- Forward-declared: theorem-B9-S1/-S2/-R5/-R7 (below) each recurse into
-- theorem-B9 itself, at ITS OWN specific γ:=⌊g⌋[sub,ρ] -- unlike an
-- earlier version of this development, which routed everything through a
-- separate, arbitrary-γ theorem-B9-gen (see git history). That
-- generalisation is exactly what made (R5) unprovable in general (its
-- own fk/fl embed the AMBIENT g directly, only meaningfully matching
-- l1v/k1v's own γ when γ IS ⌊g⌋ -- see theorem-B9-R5's own comment) --
-- and once (R5) needed a specific-γ escape hatch anyway, keeping every
-- OTHER case routed through the general theorem-B9-gen bought nothing:
-- any (R5) buried under an (F)/(S1)/(S2)/(S3)/(S4) congruence would still
-- hit the arbitrary-γ postulate on the way back out. theorem-B9 below is
-- instead a single, direct, self-contained induction, so a nested (R5)
-- is handled by theorem-B9-R5 at every depth, not just at the top.
-- Each recursive case needs its own one-off bridge relating theorem-B9's
-- own output at the INNER step's own ⌊newg⌋[sub*,ρ] to whatever
-- continuation that case's own combinator (bindŜ/glocalS/handlerStep/
-- thenS) actually needs -- (S3)/(S4) get this for free (⌊g1⌋[sub1,ρ]/
-- ⌊g⌋[sub,ρ] literally ARE the needed continuation, by definition); (F)/
-- (S1)/(S2) need one genuine calculation each (thenS-upS + bindF̂-unitʳ
-- collapsing the newly-built ambient's own upS-wrapped report back down,
-- exactly as in (R7)'s own derivation above).
theorem-B9 : ∀ {Γ σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} {e e' : Γ ⊢ σ ! ε} {r : R}
           → _⊢_-[_]→_ {sub = sub} g e r e' → WFE e → (ρ : Env Γ)
           → runSelWith (Esem e ρ) ⌊ g ⌋[ sub , ρ ] ≡ addR r (runSelWith (Esem e' ρ) ⌊ g ⌋[ sub , ρ ])

-- (S1): unfold Esem(handleE h(val v)_)ρ to handlerSem h ρ p_
-- (bindŜ-unitˡ), then push the r-shift out with handlerStep-addR, fed
-- theorem-B9's own IH on stp (at ITS OWN ⌊newg⌋[⊆ᵉ-,ℓ,ρ]) transported,
-- via `bridge`, along its own agreement with `cont` (the continuation
-- handlerSem's own runSelWith definition actually feeds e/e' through).
-- `bridge` needs one extra ingredient beyond (F)'s own version below:
-- retApplied-eq, bridging Esem(retApplied h v) back to handlerRet
-- directly (retApplied's own substitution is exactly the one that makes
-- this hold, cons-by-cons).
theorem-B9-S1 : ∀ {Γ ε εamb ℓ par σ σ'} (sub : εamb ⊆ᵉ ε) {g : LC Γ σ' εamb}
                     (h : Handler Γ ℓ par σ σ' ε) (v : Val Γ (gnd par)) {e e' : Γ ⊢ σ ! (ε ,ℓ ℓ)} {r : R}
                   → _⊢_-[_]→_ {sub = ⊆ᵉ-,ℓ} (vabs (thenE sub (retApplied h v) (weaken1V g))) e r e'
                   → WFE (handleE h (val v) e) → (ρ : Env Γ)
                   → runSelWith (Esem (handleE h (val v) e) ρ) ⌊ g ⌋[ sub , ρ ] ≡ addR r (runSelWith (Esem (handleE h (val v) e') ρ) ⌊ g ⌋[ sub , ρ ])
theorem-B9-S1 {ℓ = ℓ} {par = par} {σ = σ} sub {g} h v {e} {e'} {r} stp (wf-handle _ _ wfe) ρ = trans step1 (trans step2 step3)
  where
  γ = ⌊ g ⌋[ sub , ρ ]
  p : ⟦ gnd par ⟧
  p = Vsem v ρ
  cont : ⟦ σ ⟧ → R̂ (_ ,ℓ ℓ)
  cont a = widenF̂ ⊆ᵉ-,ℓ (thenS γ (handlerRet h ρ a p))
  newg = vabs (thenE sub (retApplied h v) (weaken1V g))
  retApplied-eq : ∀ a → Esem (retApplied h v) (ρ ,, a) ≡ handlerRet h ρ a p
  retApplied-eq a = subE-coh (cons (vvar Z) (cons (weaken1V v) wkSub)) (ρ ,, a) ((ρ ,, p) ,, a)
                              (λ{ Z → refl ; (S Z) → weaken1V-coh _ v ρ a ; (S (S y)) → refl }) (ret h)
  bridge : ∀ a → ⌊ newg ⌋[ ⊆ᵉ-,ℓ , ρ ] a ≡ cont a
  bridge a = cong (widenF̂ ⊆ᵉ-,ℓ) inner
    where
    mid : Vsem newg ρ a ≡ upS (thenS γ (handlerRet h ρ a p))
    mid = cong upS (cong₂ thenS (funext (λ b → cong (widenF̂ sub) (renLsem-coh S ρ (ρ ,, a) (λ x → refl) g b))) (retApplied-eq a))
    inner : Lsem newg ρ a ≡ thenS γ (handlerRet h ρ a p)
    inner = trans (cong (thenS pure) mid) (trans (thenS-upS pure (thenS γ (handlerRet h ρ a p))) (bindF̂-unitʳ (thenS γ (handlerRet h ρ a p))))
  ihFixed : runSelWith (Esem e ρ) cont ≡ addR r (runSelWith (Esem e' ρ) cont)
  ihFixed = subst (λ c → runSelWith (Esem e ρ) c ≡ addR r (runSelWith (Esem e' ρ) c)) (funext bridge) (theorem-B9 stp wfe ρ)
  step1 : runSelWith (Esem (handleE h (val v) e) ρ) γ ≡ runSelWith (handlerSem h ρ p (Esem e ρ)) γ
  step1 = cong (λ w → runSelWith w γ) (bindŜ-unitˡ (λ p' → handlerSem h ρ p' (Esem e ρ)) p)
  step2 : runSelWith (handlerSem h ρ p (Esem e ρ)) γ ≡ addR r (runSelWith (handlerSem h ρ p (Esem e' ρ)) γ)
  step2 = handlerStep-addR r h ρ γ p (runSelWith (Esem e ρ) cont) (runSelWith (Esem e' ρ) cont) ihFixed
  step3 : addR r (runSelWith (handlerSem h ρ p (Esem e' ρ)) γ) ≡ addR r (runSelWith (Esem (handleE h (val v) e') ρ) γ)
  step3 = cong (λ w → addR r (runSelWith w γ)) (sym (bindŜ-unitˡ (λ p' → handlerSem h ρ p' (Esem e' ρ)) p))

-- (S2): Esem(thenE...) is always upS-wrapped (hence γ-independent), so
-- this reduces to a fact purely about F̂-reports: thenS g1'(Esem e ρ)
-- shifts by mapF̂(r+_) relative to thenS g1'(Esem e'ρ) (thenS-addR, fed
-- theorem-B9's own IH on stp -- no bridge needed here at all, since
-- ⌊g1⌋[sub,ρ] literally IS g1' by definition), and separately, the NEW
-- ambient loss-continuation g2 := vabs(weaken1(thenE sub e' g1)) -- read
-- via Lsem's canonical `pure` collapse -- reduces (thenS-upS +
-- bindF̂-unitʳ) back to EXACTLY thenS g1'(Esem e' ρ). The two
-- `mapF̂(_+_)`-shifted reports these produce (by r vs by r+0#) agree via
-- a single mapF̂-cong/+-assoc rewrite. The outer γ (⌊g⌋[subamb,ρ], for
-- the DISREGARDED ambient g) never actually matters, exactly as when
-- this was stated at an arbitrary γ.
theorem-B9-S2 : ∀ {Γ ε εg εamb σ} (sub : εg ⊆ᵉ ε) {subamb : εamb ⊆ᵉ ε} {g : LC Γ Loss εamb} (g1 : LC Γ σ εg) {e e' : Γ ⊢ σ ! ε} {r : R}
                   → _⊢_-[_]→_ {sub = sub} g1 e r e'
                   → WFE (thenE sub e g1) → (ρ : Env Γ)
                   → runSelWith (Esem (thenE sub e g1) ρ) ⌊ g ⌋[ subamb , ρ ]
                   ≡ addR 0# (runSelWith (Esem (thenE ⊆ᵉ-refl (lossE (val (vgnd r))) (vabs (weaken1 (thenE sub e' g1)))) ρ) ⌊ g ⌋[ subamb , ρ ])
theorem-B9-S2 {Γ} {ε} {σ = σ} sub {subamb} {g} g1 {e} {e'} {r} stp (wf-then wfe _) ρ =
  trans (cong (λ W → runSelWith (upS W) γ) (trans eqLHS mapEq))
        (trans (sym (addR-0 (runSelWith (upS (mapF̂ ((r + 0#) +_) D)) γ)))
               (cong (λ w → addR 0# (runSelWith w γ)) (sym eqRHS-Esem)))
  where
  γ = ⌊ g ⌋[ subamb , ρ ]
  g1' : ⟦ σ ⟧ → R̂ ε
  g1' a = widenF̂ sub (Lsem g1 ρ a)
  D : R̂ ε
  D = thenS g1' (Esem e' ρ)
  eqLHS : thenS g1' (Esem e ρ) ≡ mapF̂ (r +_) D
  eqLHS = thenS-addR r g1' (Esem e ρ) (Esem e' ρ) (theorem-B9 stp wfe ρ)
  mapEq : mapF̂ (r +_) D ≡ mapF̂ ((r + 0#) +_) D
  mapEq = mapF̂-cong (λ y → sym (trans (+-assoc r 0# y) (cong (r +_) (+-identityˡ y)))) D
  g2 : LC Γ UnitTy ε
  g2 = vabs (weaken1 (thenE sub e' g1))
  step-a : Lsem g2 ρ tt ≡ D
  step-a = trans (cong (thenS pure) (weaken1-coh UnitTy (thenE sub e' g1) ρ tt)) (trans (thenS-upS pure D) (bindF̂-unitʳ D))
  g2'tt-eq : widenF̂ ⊆ᵉ-refl (Lsem g2 ρ tt) ≡ D
  g2'tt-eq = trans (cong (widenF̂ ⊆ᵉ-refl) step-a) (widenF̂-refl D)
  thenSg2'-eq : thenS (λ tt' → widenF̂ ⊆ᵉ-refl (Lsem g2 ρ tt')) (Esem (lossE (val (vgnd r))) ρ) ≡ mapF̂ ((r + 0#) +_) D
  thenSg2'-eq = trans (cong (thenS (λ tt' → widenF̂ ⊆ᵉ-refl (Lsem g2 ρ tt'))) (bindŜ-unitˡ (λ r' → addLossŜ r' (η̂ˢ tt)) r))
                      (cong (mapF̂ ((r + 0#) +_)) g2'tt-eq)
  eqRHS-Esem : Esem (thenE ⊆ᵉ-refl (lossE (val (vgnd r))) g2) ρ ≡ upS (mapF̂ ((r + 0#) +_) D)
  eqRHS-Esem = cong upS thenSg2'-eq

-- theorem-B9-R5: PROVEN, at the specific γ := ⌊g⌋[sub,ρ] -- mirroring
-- agda_noparam's own theorem-B9-R5-WF (see its own comment for why the
-- specific γ is essential: fl/fk embed g directly, via renV S g, and it
-- is ONLY at γ = ⌊g⌋[sub,ρ] that this collapses back to γ itself,
-- bridged below by `γEq`, via renV-coh -- exactly the "missing
-- assumption linking γ and Gv" the arbitrary-γ postulate lacks). Unlike
-- the source, no RootZero-style side condition is needed at all: this
-- construction's handlerStep is a direct structural recursion (no
-- ext̂/collectX/bump layer to reconcile), so fkMatch/flMatch close
-- unconditionally, using plugK-fst-snd-coh to bridge the
-- parameter-pairing gap described above it.
theorem-B9-R5 : ∀ {Γ ε εamb ℓ par σ σ' εop} (sub : εamb ⊆ᵉ ε) {g : LC Γ σ' εamb}
    (h : Handler Γ ℓ par σ σ' ε) (v1 : Val Γ (gnd par))
    (m : ℓ ∈ εop) (op : Op ℓ) (v2 : Val Γ (gnd (out op)))
    (k : ContCxt Γ (gnd (in′ op)) εop σ (ε ,ℓ ℓ)) (nh : ¬ Handles k ℓ) (ρ : Env Γ)
  → let Γz  : Cxt
        Γz  = Γ , (gnd par `× gnd (in′ op))
        h'  : Handler Γz ℓ par σ σ' ε
        h'  = renH S h
        g'  : LC Γz σ' εamb
        g'  = renV S g
        k'  : ContCxt Γz (gnd (in′ op)) εop σ (ε ,ℓ ℓ)
        k'  = weaken1K k
        handled : Γz ⊢ σ' ! ε
        handled = handleE h' pArg (plugK k' yArg)
        fk  = vabs {σ = gnd par `× gnd (in′ op)} (glocalE sub ⊆ᵉ-refl handled g')
        fl  = vabs {σ = gnd par `× gnd (in′ op)} (thenE sub handled g')
    in runSelWith (Esem (handleE h (val v1) (plugK k (opE m op (val v2)))) ρ) ⌊ g ⌋[ sub , ρ ]
     ≡ addR 0# (runSelWith (Esem (subE (cons fk (cons fl (cons v2 (cons v1 idSub)))) (clause h op)) ρ) ⌊ g ⌋[ sub , ρ ])
theorem-B9-R5 {Γ = Γ} {ε = ε} {ℓ = ℓ} {par = par} {σ = σ} {σ' = σ'} sub {g} h v1 m op v2 k nh ρ =
  trans step1 (trans step2 (cong (λ w → addR 0# (runSelWith w γ)) (sym step3)))
  where
  γ = ⌊ g ⌋[ sub , ρ ]
  p1 = Vsem v1 ρ
  v2val = Vsem v2 ρ
  mH' = promote k nh m
  κ : ⟦ in′ op ⟧ᴳ → Ŝ (ε ,ℓ ℓ) ⟦ σ ⟧
  κ b = Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, b)

  step1 : runSelWith (Esem (handleE h (val v1) (plugK k (opE m op (val v2)))) ρ) γ
        ≡ runSelWith (handlerSem h ρ p1 (φ̂ˢ mH' op v2val κ)) γ
  step1 = cong (λ w → runSelWith w γ) (trans (bindŜ-unitˡ (λ p → handlerSem h ρ p (Esem (plugK k (opE m op (val v2))) ρ)) p1)
                                              (cong (handlerSem h ρ p1) (lemma-B8 op v2 k m nh ρ)))

  -- handled = renH S h; g' = renV S g; k' = weaken1K k
  handled : (Γ , (gnd par `× gnd (in′ op))) ⊢ σ' ! ε
  handled = handleE (renH S h) pArg (plugK (weaken1K k) yArg)
  fk : Val Γ ((gnd par `× gnd (in′ op)) ⇒ σ' ! ε)
  fk = vabs {σ = gnd par `× gnd (in′ op)} (glocalE sub ⊆ᵉ-refl handled (renV S g))
  fl : Val Γ ((gnd par `× gnd (in′ op)) ⇒ Loss ! ε)
  fl = vabs {σ = gnd par `× gnd (in′ op)} (thenE sub handled (renV S g))

  handledEq : ∀ p' a → Esem handled (ρ ,, (p' , a)) ≡ handlerSem h ρ p' (κ a)
  handledEq p' a =
    trans (cong (λ w → bindŜ w K2)
                (bindŜ-unitˡ {X = ⟦ gnd par ⟧ × ⟦ in′ op ⟧ᴳ} {Y = ⟦ gnd par ⟧} (λ{ (x , y) → η̂ˢ x }) (p' , a)))
          (trans (bindŜ-unitˡ {X = ⟦ gnd par ⟧} K2 p')
                 (trans (renH-coh S ρ (ρ ,, (p' , a)) (λ x → refl) h p' (Esem (plugK (weaken1K k) yArg) (ρ ,, (p' , a))))
                        (cong (handlerSem h ρ p') (plugK-fst-snd-coh k ρ p' a))))
    where
    K2 : ⟦ gnd par ⟧ → Ŝ ε ⟦ σ' ⟧
    K2 p2 = handlerSem (renH S h) (ρ ,, (p' , a)) p2 (Esem (plugK (weaken1K k) yArg) (ρ ,, (p' , a)))

  γEq : ∀ p' a b → widenF̂ sub (Lsem (renV S g) (ρ ,, (p' , a)) b) ≡ γ b
  γEq p' a b = cong (widenF̂ sub) (cong (thenS pure) (cong (λ F → F b) (renV-coh S ρ (ρ ,, (p' , a)) (λ x → refl) g)))

  fkMatch : ∀ p' a → Vsem fk ρ (p' , a) ≡ k1v h ρ γ op κ (p' , a)
  fkMatch p' a = cong₂ (glocalS ⊆ᵉ-refl) (funext (γEq p' a)) (handledEq p' a)

  flMatch : ∀ p' a → Vsem fl ρ (p' , a) ≡ l1v h ρ γ op κ (p' , a)
  flMatch p' a = cong upS (cong₂ thenS (funext (γEq p' a)) (handledEq p' a))

  step2 : runSelWith (handlerSem h ρ p1 (φ̂ˢ mH' op v2val κ)) γ
        ≡ addR 0# (runSelWith (Esem (clause h op) ((((ρ ,, p1) ,, v2val) ,, l1v h ρ γ op κ) ,, k1v h ρ γ op κ)) γ)
  step2 with ℓ ≟ᵉ ℓ
  ... | no neq  = ⊥-elim (neq refl)
  ... | yes eq with eq
  ...   | refl = refl

  step3 : Esem (subE (cons fk (cons fl (cons v2 (cons v1 idSub)))) (clause h op)) ρ
        ≡ Esem (clause h op) ((((ρ ,, p1) ,, v2val) ,, l1v h ρ γ op κ) ,, k1v h ρ γ op κ)
  step3 = subE-coh (cons fk (cons fl (cons v2 (cons v1 idSub)))) ρ
                    ((((ρ ,, p1) ,, v2val) ,, l1v h ρ γ op κ) ,, k1v h ρ γ op κ)
                    (λ{ Z → funext (λ{ (p' , a) → fkMatch p' a })
                      ; (S Z) → funext (λ{ (p' , a) → flMatch p' a })
                      ; (S (S Z)) → refl
                      ; (S (S (S Z))) → refl
                      ; (S (S (S (S x)))) → refl })
                    (clause h op)

-- (R7): PROVEN directly, given WFG(vabs e) (extracted, at the call site
-- below, from the wf-then case of theorem-B9's own WFE hypothesis). No
-- recursion at all (a base case), so this stays generic over γ exactly
-- as before -- theorem-B9's own R7 clause just calls it at γ:=⌊g⌋[sub,ρ].
-- WFG-upS gives e's own denotation the shape `upS W`; substituting that
-- into thenE's own Lsem/pure collapse (Lsem-eq, via thenS-upS +
-- bindF̂-unitʳ) and into glocalE's own semantics (rhsEq, via sub1-coh)
-- reduces both sides to R7-core's own two forms.
theorem-B9-R7 : ∀ {Γ σ ε εg εamb} (sub : εg ⊆ᵉ ε) {g : LC Γ Loss εamb} (v : Val Γ σ) (e : (Γ , σ) ⊢ Loss ! εg)
                   → WFG (vabs e) → (ρ : Env Γ) (γ : R → R̂ ε)
                   → runSelWith (Esem (thenE sub (val v) (vabs e)) ρ) γ
                   ≡ addR 0# (runSelWith (Esem (glocalE ⊆ᵉ-refl sub (e [ v ]) zeroLC) ρ) γ)
theorem-B9-R7 {σ = σ} {εg = εg} sub {g} v e wfg ρ γ =
  trans (cong (λ S → runSelWith S γ) LHSeq)
        (trans (cong (λ S → runSelWith S γ) (R7-core sub W))
               (trans (sym (addR-0 (runSelWith (glocalS sub (λ _ → pure (0# + 0#)) (upS W)) γ)))
                      (cong (λ w → addR 0# (runSelWith w γ)) (sym rhsEq'))))
  where
  x : ⟦ σ ⟧
  x = Vsem v ρ
  W : F̂ εg R
  W = proj₁ (WFG-upS wfg ρ x)
  Beq : Vsem (vabs e) ρ x ≡ upS W
  Beq = proj₂ (WFG-upS wfg ρ x)
  Lsem-eq : Lsem (vabs e) ρ x ≡ W
  Lsem-eq = trans (cong (thenS pure) Beq) (trans (thenS-upS pure W) (bindF̂-unitʳ W))
  LHSeq : Esem (thenE sub (val v) (vabs e)) ρ ≡ upS (mapF̂ (0# +_) (widenF̂ sub W))
  LHSeq = cong (λ w → upS (mapF̂ (0# +_) (widenF̂ sub w))) Lsem-eq
  rhsEq : Esem (e [ v ]) ρ ≡ upS W
  rhsEq = trans (sub1-coh e ρ v) Beq
  rhsEq' : Esem (glocalE ⊆ᵉ-refl sub (e [ v ]) zeroLC) ρ ≡ glocalS sub (λ _ → pure (0# + 0#)) (upS W)
  rhsEq' = cong (glocalS sub (λ _ → pure (0# + 0#))) rhsEq

-- ---------------------------------------------------------------------
-- theorem-B9's own 15 cases, dispatching directly (no separate -gen
-- lemma). (R1)-(R4),(R6),(R8),(R9): pure value reductions -- Esem on
-- both sides reduces to η̂ˢ (or a one-step unfolding of it) via
-- bindŜ-unitˡ alone, with r=0# (except R4, whose own r IS the loss
-- reported) making the addR-shift trivial via +-identityˡ; γ:=⌊g⌋[sub,ρ]
-- is bound in a `where` clause per case, purely so each proof body can
-- keep referring to it as `γ` unchanged.
-- ---------------------------------------------------------------------

theorem-B9 (R1 {sub = sub} {g = g} f x) _ ρ =
  trans (cong (λ w → runSelWith w γ) (bindŜ-unitˡ (λ a → η̂ˢ (⟦ f ⟧f a)) x))
        (cong (λ z → z , leaf (⟦ f ⟧f x)) (sym (+-identityˡ 0#)))
  where γ = ⌊ g ⌋[ sub , ρ ]

theorem-B9 (R2-pair {sub = sub} {g = g} v w) _ ρ =
  trans (cong (λ z → runSelWith z γ)
              (trans (bindŜ-unitˡ (λ a → bindŜ (η̂ˢ (Vsem w ρ)) (λ b → η̂ˢ (a , b))) (Vsem v ρ))
                     (bindŜ-unitˡ (λ b → η̂ˢ (Vsem v ρ , b)) (Vsem w ρ))))
        (cong (λ z → z , leaf (Vsem v ρ , Vsem w ρ)) (sym (+-identityˡ 0#)))
  where γ = ⌊ g ⌋[ sub , ρ ]

theorem-B9 (R2-fst {σ = σ} {τ = τ} {sub = sub} {g = g} v w) _ ρ =
  trans (cong (λ z → runSelWith z γ) (bindŜ-unitˡ {X = ⟦ σ ⟧ × ⟦ τ ⟧} (λ{ (a , b) → η̂ˢ a }) (Vsem v ρ , Vsem w ρ)))
        (cong (λ z → z , leaf (Vsem v ρ)) (sym (+-identityˡ 0#)))
  where γ = ⌊ g ⌋[ sub , ρ ]

theorem-B9 (R2-snd {σ = σ} {τ = τ} {sub = sub} {g = g} v w) _ ρ =
  trans (cong (λ z → runSelWith z γ) (bindŜ-unitˡ {X = ⟦ σ ⟧ × ⟦ τ ⟧} (λ{ (a , b) → η̂ˢ b }) (Vsem v ρ , Vsem w ρ)))
        (cong (λ z → z , leaf (Vsem w ρ)) (sym (+-identityˡ 0#)))
  where γ = ⌊ g ⌋[ sub , ρ ]

theorem-B9 (R3 {sub = sub} {g = g} e v) _ ρ =
  trans (cong (λ w → runSelWith w γ)
              (trans (bindŜ-unitˡ (λ φ → bindŜ (η̂ˢ (Vsem v ρ)) φ) (Vsem (vabs e) ρ))
                     (bindŜ-unitˡ (Vsem (vabs e) ρ) (Vsem v ρ))))
        (trans (sym (addR-0 (runSelWith (Esem e (ρ ,, Vsem v ρ)) γ)))
               (cong (λ w → addR 0# (runSelWith w γ)) (sym (sub1-coh e ρ v))))
  where γ = ⌊ g ⌋[ sub , ρ ]

theorem-B9 (R4 {sub = sub} {g = g} r) _ ρ =
  cong (λ w → runSelWith w γ) (bindŜ-unitˡ (λ r' → addLossŜ r' (η̂ˢ tt)) r)
  where γ = ⌊ g ⌋[ sub , ρ ]

theorem-B9 (R6 {sub = sub} {g = g} h v1 v2) _ ρ =
  trans (cong (λ w → runSelWith w γ) (bindŜ-unitˡ (λ p → handlerSem h ρ p (η̂ˢ (Vsem v2 ρ))) (Vsem v1 ρ)))
        (cong (λ w → addR 0# (runSelWith w γ)) (sym eqSub))
  where
  γ = ⌊ g ⌋[ sub , ρ ]
  eqSub : Esem (subE (cons v2 (cons v1 idSub)) (ret h)) ρ ≡ Esem (ret h) ((ρ ,, Vsem v1 ρ) ,, Vsem v2 ρ)
  eqSub = subE-coh (cons v2 (cons v1 idSub)) ρ ((ρ ,, Vsem v1 ρ) ,, Vsem v2 ρ)
                    (λ{ Z → refl ; (S Z) → refl ; (S (S y)) → refl }) (ret h)

theorem-B9 (R8 sub1 sub2 {sub = sub} {g = g} v g1) _ ρ =
  cong (λ z → z , leaf (Vsem v ρ)) (sym (+-identityˡ 0#))
  where γ = ⌊ g ⌋[ sub , ρ ]

theorem-B9 (R9 {sub = sub} {g = g} v) _ ρ =
  cong (λ z → z , leaf (Vsem v ρ)) (sym (+-identityˡ 0#))
  where γ = ⌊ g ⌋[ sub , ρ ]

-- (F): regular-frame congruence. lemma-B6 rewrites both plugF f e and
-- plugF f e' into the SAME bindŜ-with-D shape; bindŜ-addR then lifts the
-- IH across it, fed by `ihFixed` -- theorem-B9's OWN IH on the smaller
-- stp (indexed at ⊆ᵉ-refl, since newg=vabs(thenE...) lives at the SAME ε
-- as e), transported along `bridge` to the ONE continuation bindŜ-addR
-- actually needs (λx→thenSγ(Dx)). `bridge` itself: unfold newg's own
-- Vsem down to an upS-wrapped report (mirroring (R7)'s own derivation,
-- via renLsem-coh identifying the inner thenE's own loss-continuation
-- with the outer γ), then collapse the extra `thenS pure` roundtrip away
-- via thenS-upS + bindF̂-unitʳ. WFE(plugF f e)'s own hole is extracted
-- via WFE-plugF.
theorem-B9 (F-rule {α = α} sub {g = g} f {e} {e'} {r} stp) wfe ρ =
  trans (cong (λ w → runSelWith w γ) (lemma-B6 f e ρ))
        (trans (bindŜ-addR r (Esem e ρ) (Esem e' ρ) D γ ihFixed)
               (cong (λ w → addR r (runSelWith w γ)) (sym (lemma-B6 f e' ρ))))
  where
  γ = ⌊ g ⌋[ sub , ρ ]
  D : ⟦ α ⟧ → Ŝ _ _
  D a = Esem (plugF (weaken1F f) (val (vvar Z))) (ρ ,, a)
  newg = vabs (thenE sub (plugF (weaken1F f) (val (vvar Z))) (weaken1V g))
  bridge : ∀ a → ⌊ newg ⌋[ ⊆ᵉ-refl , ρ ] a ≡ thenS γ (D a)
  bridge a = trans (widenF̂-refl _) inner
    where
    mid : Vsem newg ρ a ≡ upS (thenS γ (D a))
    mid = cong upS (cong (λ c → thenS c (D a)) (funext (λ b → cong (widenF̂ sub) (renLsem-coh S ρ (ρ ,, a) (λ x → refl) g b))))
    inner : Lsem newg ρ a ≡ thenS γ (D a)
    inner = trans (cong (thenS pure) mid) (trans (thenS-upS pure (thenS γ (D a))) (bindF̂-unitʳ (thenS γ (D a))))
  ihFixed : runSelWith (Esem e ρ) (λ x → thenS γ (D x)) ≡ addR r (runSelWith (Esem e' ρ) (λ x → thenS γ (D x)))
  ihFixed = subst (λ c → runSelWith (Esem e ρ) c ≡ addR r (runSelWith (Esem e' ρ) c)) (funext bridge) (theorem-B9 stp (WFE-plugF f wfe) ρ)

-- (S3): ⟨e⟩^ε₁_g1 congruence -- Esem(glocalE...)ρ is LITERALLY glocalS
-- sub2 g1' (Esem e ρ) already (no lemma-B6-style rewrite needed, unlike
-- (F)), so glocalS-addR applies directly to theorem-B9's own IH on stp --
-- no bridge needed at all, since ⌊g1⌋[sub1,ρ] literally IS g1' by
-- definition (matching exactly the continuation stp's own index ties it
-- to). WFE(glocalE...)'s own hole is extracted via wf-glocal's first
-- component.
theorem-B9 (S3 {ε = ε} {ε₂ = ε₂} {ε₁ = ε₁} {σ = σ} sub1 sub2 {sub = sub} {g = g} g1 {e} {e'} {r} stp) (wf-glocal wfe _) ρ =
  glocalS-addR r sub2 (Esem e ρ) (Esem e' ρ) g1' γ (theorem-B9 stp wfe ρ)
  where
  γ = ⌊ g ⌋[ sub , ρ ]
  g1' : ⟦ σ ⟧ → R̂ ε₁
  g1' a = widenF̂ sub1 (Lsem g1 ρ a)

-- (S4): reset congruence -- resetS-eq shows resetS(Esem e ρ) and
-- resetS(Esem e' ρ) agree EXACTLY at γ (resetS discards whatever loss
-- shift the IH reports), matching (S4)'s own r=0# conclusion via addR-0.
-- No bridge needed: the inner stp shares the SAME sub/g as the outer
-- conclusion, so theorem-B9's own IH is already at the right γ.
theorem-B9 (S4 {sub = sub} {g = g} {e = e} {e' = e'} {r = r} stp) (wf-reset wfe) ρ =
  trans (resetS-eq r (Esem e ρ) (Esem e' ρ) γ (theorem-B9 stp wfe ρ))
        (sym (addR-0 (runSelWith (resetS (Esem e' ρ)) γ)))
  where γ = ⌊ g ⌋[ sub , ρ ]

theorem-B9 (S1 sub {g} h v stp) wfe ρ = theorem-B9-S1 sub {g} h v stp wfe ρ
theorem-B9 (S2 sub {g = g} g1 stp) wfe ρ = theorem-B9-S2 sub {g = g} g1 stp wfe ρ
theorem-B9 (R5 sub h v1 m op v2 k nh) wfe ρ = theorem-B9-R5 sub h v1 m op v2 k nh ρ
theorem-B9 (R7 sub {subamb = subamb} {g = g} v e) (wf-then _ wfg) ρ = theorem-B9-R7 sub {g} v e wfg ρ ⌊ g ⌋[ subamb , ρ ]

-- ---------------------------------------------------------------------
-- WFE-preserved: a single small-step preserves both WFE(e) and WFG(g)
-- -- the invariant theorem-B9 alone (single-step scope) never needed to
-- re-establish, but that chaining theorem-B9 across a whole big-step
-- derivation (theorem-B10a below) does. Case on the 16 step
-- constructors:
--  * R1/R2-pair/R2-fst/R2-snd/R4/R8/R9 are trivial -- their own output
--    is always wf-val of data already extracted from the input (or, for
--    R1/R4, a fresh wf-vgnd, no dependency at all).
--  * R3/R7 expose a previously-opaque value/loss-continuation body via
--    substitution -- WFE-[]/WFG-e[v] (above) are exactly built for this.
--  * R6/R5 substitute into a handler's own ret/clause body -- WFH's own
--    two fields, fed through WFE-subE with the rule's own concrete
--    substitution (WFsub-cons chains). R5 additionally needs fk/fl's own
--    WFV-ness, built from WFE-plugK-ren-fill (k's own weakened+refilled
--    WFE-ness) and WFH-renH/WFG-renV (h/g's own weakened WFE/WFG-ness).
--  * F-rule/S1 synthesize a NEW ambient continuation embedding the
--    ambient g (WFG-renV) plus an administrative wrapper expression
--    (WFE-frame-fill / retApplied-wf) -- recurse under THAT continuation.
--  * S2/S3 disregard the ambient g entirely, recursing directly under
--    their own g1 instead (S2's own output additionally wraps a fresh
--    lossE/thenE administrative shell, all trivially WFE/WFG).
--  * S4 recurses under the SAME ambient g (reset shares it unchanged).
-- ---------------------------------------------------------------------

WFE-preserved : ∀ {Γ σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} {e e' : Γ ⊢ σ ! ε} {r : R}
              → _⊢_-[_]→_ {sub = sub} g e r e' → WFG g → WFE e → WFE e'
WFE-preserved (R1 f x) wfg (wf-fun (wf-val (wf-vgnd _))) = wf-val (wf-vgnd _)
WFE-preserved (R2-pair v w) wfg (wf-pair (wf-val wfv) (wf-val wfw)) = wf-val (wf-vpair wfv wfw)
WFE-preserved (R2-fst v w) wfg (wf-fst (wf-val (wf-vpair wfv wfw))) = wf-val wfv
WFE-preserved (R2-snd v w) wfg (wf-snd (wf-val (wf-vpair wfv wfw))) = wf-val wfw
WFE-preserved (R3 e v) wfg (wf-app (wf-val (wf-vabs wfe)) (wf-val wfv)) = WFE-[] wfe wfv
WFE-preserved (R4 r) wfg (wf-loss (wf-val (wf-vgnd _))) = wf-val (wf-vgnd _)
WFE-preserved (R6 h v1 v2) wfg (wf-handle (wf-handler wfc wfr) (wf-val wfv1) (wf-val wfv2)) =
  WFE-subE (WFsub-cons wfv2 (WFsub-cons wfv1 WFsub-idSub)) wfr
WFE-preserved (R7 sub v e) wfg (wf-then (wf-val wfv) wfge) = wf-glocal (WFG-e[v] wfge wfv) wf-zero
WFE-preserved (R8 sub1 sub2 v g1) wfg (wf-glocal (wf-val wfv) wfg1) = wf-val wfv
WFE-preserved (R9 v) wfg (wf-reset (wf-val wfv)) = wf-val wfv
WFE-preserved (F-rule sub f stp) wfg wfpe =
  WFE-plugF-fill f wfpe (WFE-preserved stp newg-wfg (WFE-plugF f wfpe))
  where
  newg-wfg = wf-then (WFE-frame-fill f wfpe (wf-val (wf-vvar Z))) (WFG-renV S wfg)
WFE-preserved (S1 sub h v stp) wfg (wf-handle wfh (wf-val wfv) wfe) =
  wf-handle wfh (wf-val wfv) (WFE-preserved stp newg-wfg wfe)
  where
  newg-wfg = wf-then (retApplied-wf wfh wfv) (WFG-renV S wfg)
WFE-preserved (S2 sub g1 stp) wfg (wf-then wfe wfg1) =
  wf-then (wf-loss (wf-val (wf-vgnd _))) (wf-then (WFE-renE S (WFE-preserved stp wfg1 wfe)) (WFG-renV S wfg1))
WFE-preserved (S3 sub1 sub2 g1 stp) wfg (wf-glocal wfe wfg1) =
  wf-glocal (WFE-preserved stp wfg1 wfe) wfg1
WFE-preserved (S4 stp) wfg (wf-reset wfe) =
  wf-reset (WFE-preserved stp wfg wfe)
WFE-preserved (R5 sub h v1 m op v2 k nh) wfg (wf-handle (wf-handler wfc wfr) (wf-val wfv1) wfb) with WFE-plugK k wfb
... | wf-op (wf-val wfv2) = WFE-subE wfsub (wfc op)
  where
  wfh'      = WFH-renH S (wf-handler wfc wfr)
  wfg'      = WFG-renV S wfg
  wfpArg    = wf-fst (wf-val (wf-vvar Z))
  wfyArg    = wf-snd (wf-val (wf-vvar Z))
  wfkArg    = WFE-plugK-ren-fill k wfb wfyArg
  wfhandled = wf-handle wfh' wfpArg wfkArg
  wffk      = wf-vabs (wf-glocal wfhandled wfg')
  wffl      = wf-vabs (wf-then wfhandled wfg')
  wfsub     = WFsub-cons wffk (WFsub-cons wffl (WFsub-cons wfv2 (WFsub-cons wfv1 WFsub-idSub)))

-- ---------------------------------------------------------------------
-- Theorem B.10a: adequacy of Esem against the big-step judgment. If e
-- big-steps to a value v with total loss r under loss-continuation g,
-- then e's denotational meaning, run against g's own denotation, is
-- exactly that -- the reported loss r paired with a leaf carrying v's
-- own denotation. Esem(val v)ρ = η̂ˢ(Vsem v ρ), whose own runSelWith is
-- (0#, leaf(Vsem v ρ)) (Domains.agda's own η̂ˢ clause) -- so this is
-- what theorem-B9's per-step addR-shift accumulates to once the whole
-- big-step chain (_⊢_⇒[_]_, OpSem.agda) has run down to `done`.
-- Proved by induction on the big-step derivation, chaining theorem-B9
-- across each step and WFE-preserved to re-establish WFE(e)/WFG(g) for
-- the next one. Γ is fixed to ∅ (unlike theorem-B9, fully Γ-generic):
-- this is meant to combine with theorem-A4-3/corollary-3-3, both of
-- which are closed-term-only, so stating it generically in Γ here would
-- outrun what it can actually be composed with. Also carries WFG(g) --
-- absent from the original formulation -- since WFE-preserved (needed
-- to chain across more than one step) genuinely needs it: R5's own
-- fk/fl embed the ambient g directly, so g's own well-formedness has to
-- be threaded through exactly like e's.
-- ---------------------------------------------------------------------

theorem-B10a : ∀ {σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC ∅ σ εg} {e : ∅ ⊢ σ ! ε} {r : R} {v : Val ∅ σ}
             → _⊢_⇒[_]_ {sub = sub} g e r (val v) → WFG g → WFE e → (ρ : Env ∅)
             → runSelWith (Esem e ρ) ⌊ g ⌋[ sub , ρ ] ≡ (r , leaf (Vsem v ρ))
theorem-B10a (done _)       wfg wfe ρ = refl
theorem-B10a (step stp d')  wfg wfe ρ =
  trans (theorem-B9 stp wfe ρ) (cong (addR _) (theorem-B10a d' wfg (WFE-preserved stp wfg wfe) ρ))

-- ---------------------------------------------------------------------
-- Theorem B.10b: adequacy of Esem against the big-step judgment, for
-- the OTHER shape Terminal allows (OpSem.agda's own terminalOp) -- a
-- stuck, unhandled operation call plugK K (opE m op (val v)), rather
-- than a plain value. Mirrors theorem-B10a exactly, but the "leaf"
-- endpoint is replaced by a "node": lemma-B8 (already proven, above)
-- already computes Esem(plugK K(opE m op(val v)))ρ as exactly
-- φ̂ˢ(promote K nh m)op(Vsem v ρ)(...), whose own runSelWith is
-- (0#, node(promote K nh m)op(Vsem v ρ)(...)) (Domains.agda's own φ̂ˢ
-- clause) -- the base case this accumulates to, via theorem-B9's
-- per-step addR-shift, once the big-step chain runs down to `done` at
-- this stuck configuration. `promote` (Proofs.agda, above) is exactly
-- what widens m's own membership at the hole's εop out to K's own
-- outer ε, using nh (¬ Handles K ℓ) the same way terminalOp itself
-- does. Proved by induction on the big-step derivation, exactly as
-- theorem-B10a.
-- ---------------------------------------------------------------------

theorem-B10b : ∀ {σ ε εg ℓ εop} {sub : εg ⊆ᵉ ε} {g : LC ∅ σ εg} {e : ∅ ⊢ σ ! ε} {r : R}
               (m : ℓ ∈ εop) (op : Op ℓ) (v : Val ∅ (gnd (out op))) (K : ContCxt ∅ (gnd (in′ op)) εop σ ε) (nh : ¬ Handles K ℓ)
             → _⊢_⇒[_]_ {sub = sub} g e r (plugK K (opE m op (val v))) → WFG g → WFE e → (ρ : Env ∅)
             → runSelWith (Esem e ρ) ⌊ g ⌋[ sub , ρ ]
             ≡ (r , node (promote K nh m) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K K) (val (vvar Z))) (ρ ,, a)))
theorem-B10b {sub = sub} {g = g} m op v K nh (done _) wfg wfe ρ =
  cong (λ w → runSelWith w ⌊ g ⌋[ sub , ρ ]) (lemma-B8 op v K m nh ρ)
theorem-B10b m op v K nh (step stp d') wfg wfe ρ =
  trans (theorem-B9 stp wfe ρ) (cong (addR _) (theorem-B10b m op v K nh d' wfg (WFE-preserved stp wfg wfe) ρ))

-- ---------------------------------------------------------------------
-- Theorem B.11a: the converse of theorem-B10a. If e's denotational
-- meaning, run against g's own denotation, is a leaf -- (r, leaf a),
-- NOT a node -- then e big-steps (under g) to SOME value v with EXACTLY
-- that loss r, whose own denotation IS a.
--
-- Unlike theorem-B10a/B10b (whose own proof is a direct induction on an
-- ALREADY-GIVEN big-step derivation), this direction has to PRODUCE
-- one: theorem-A4-4 (termination, closed terms) gives SOME big-step
-- derivation reaching SOME Terminal w -- either a value (terminalVal)
-- or a stuck op-call (terminalOp). theorem-B10a/B10b then compute w's
-- own denotation exactly (leaf vs. node respectively); comparing that
-- against the leaf hypothesis rules the terminalOp case out entirely
-- (a leaf can never equal a node -- disjoint ŜStep shapes) and, in the
-- terminalVal case, identifies r and a directly.
-- ---------------------------------------------------------------------

leaf-inj : ∀ {ε X} {x y : X} → leaf {ε} x ≡ leaf y → x ≡ y
leaf-inj refl = refl

leaf≠node : ∀ {ε X} {x : X} {ℓ} {m : ℓ ∈ ε} {o : Op ℓ} {v : ⟦ out o ⟧ᴳ} {κ : ⟦ in′ o ⟧ᴳ → Ŝ ε X}
          → leaf x ≡ node m o v κ → ⊥
leaf≠node ()

theorem-B11a : ∀ {σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC ∅ σ εg} {e : ∅ ⊢ σ ! ε} {r : R} {a : ⟦ σ ⟧}
              → WFG g → WFE e → (ρ : Env ∅)
              → runSelWith (Esem e ρ) ⌊ g ⌋[ sub , ρ ] ≡ (r , leaf a)
              → Σ (Val ∅ σ) (λ v → _⊢_⇒[_]_ {sub = sub} g e r (val v) × Vsem v ρ ≡ a)
theorem-B11a {sub = sub} {g = g} wfg wfe ρ hyp with theorem-A4-4 {sub = sub} {g = g} _
theorem-B11a {sub = sub} {g = g} wfg wfe ρ hyp | (r' , _ , stp' , terminalVal v') =
  v' , subst (λ x → _⊢_⇒[_]_ {sub = sub} g _ x (val v')) rEq stp' , leaf-inj leafEq
  where
  pEq    = trans (sym (theorem-B10a stp' wfg wfe ρ)) hyp
  rEq    = cong proj₁ pEq
  leafEq = cong proj₂ pEq
theorem-B11a {sub = sub} {g = g} wfg wfe ρ hyp | (r' , _ , stp' , terminalOp m op v K nh) =
  ⊥-elim (leaf≠node (cong proj₂ (trans (sym hyp) (theorem-B10b m op v K nh stp' wfg wfe ρ))))

-- ---------------------------------------------------------------------
-- Theorem B.11b: theorem-B11a's own counterpart for the OTHER Terminal
-- shape -- if e's denotation is a node (r, node m' op a κ), NOT a leaf,
-- then e big-steps (under g) to SOME stuck, unhandled operation call
-- plugK K (opE m op (val v)) with EXACTLY that loss r, where m' is K's
-- own promoted membership witness, a is v's own denotation, and κ is
-- (extensionally) the denotation of K's own delimited continuation.
--
-- Existentially quantifies over εop/m/v/K/nh (K's own hole effect
-- context and everything terminalOp packages, Terminal's own
-- constructor being indexed by exactly these) -- unlike theorem-B11a,
-- there is no single fixed "shape" (val v) to quote in the conclusion's
-- own type the way theorem-B10a's v/theorem-B11a's v could. Combines
-- theorem-A4-4/theorem-B10a/theorem-B10b exactly as theorem-B11a does
-- (progress rules out the leaf case here, the leaf and node cases being
-- symmetric mirror images of each other): the two proof obligations
-- pEq (the r-and-node equality) get discharged by ONE `refl` match --
-- since node's own arguments (m/op/v/κ, all still-open metas at that
-- point in theorem-B11b's own implicit telescope) get unified
-- simultaneously with theorem-B10b's own output, rather than needing
-- individual per-argument injectivity lemmas the way leaf's single
-- argument did. κ's own equality is stated pointwise (∀ b → ...) rather
-- than via funext, to avoid baking that axiom into the statement
-- itself -- discharged here by `λ b → refl`, the SAME unification.
-- ---------------------------------------------------------------------

theorem-B11b : ∀ {σ ε εg ℓ} {sub : εg ⊆ᵉ ε} {g : LC ∅ σ εg} {e : ∅ ⊢ σ ! ε} {r : R}
               {m' : ℓ ∈ ε} {op : Op ℓ} {a : ⟦ out op ⟧ᴳ} {κ : ⟦ in′ op ⟧ᴳ → Ŝ ε ⟦ σ ⟧}
              → WFG g → WFE e → (ρ : Env ∅)
              → runSelWith (Esem e ρ) ⌊ g ⌋[ sub , ρ ] ≡ (r , node m' op a κ)
              → Σ EffCxt (λ εop → Σ (ℓ ∈ εop) (λ m → Σ (Val ∅ (gnd (out op))) (λ v →
                  Σ (ContCxt ∅ (gnd (in′ op)) εop σ ε) (λ K → Σ (¬ Handles K ℓ) (λ nh →
                    _⊢_⇒[_]_ {sub = sub} g e r (plugK K (opE m op (val v)))
                  × promote K nh m ≡ m'
                  × Vsem v ρ ≡ a
                  × (∀ b → Esem (plugK (weaken1K K) (val (vvar Z))) (ρ ,, b) ≡ κ b))))))
theorem-B11b {sub = sub} {g = g} {e = e} wfg wfe ρ hyp with theorem-A4-4 {sub = sub} {g = g} e
theorem-B11b {sub = sub} {g = g} {e = e} wfg wfe ρ hyp | (r' , _ , stp' , terminalVal v') =
  ⊥-elim (leaf≠node (cong proj₂ (trans (sym (theorem-B10a stp' wfg wfe ρ)) hyp)))
theorem-B11b {sub = sub} {g = g} {e = e} wfg wfe ρ hyp | (r' , _ , stp' , terminalOp m op₀ v K nh)
  with trans (sym (theorem-B10b m op₀ v K nh stp' wfg wfe ρ)) hyp
... | refl = _ , m , v , K , nh , stp' , refl , refl , (λ b → refl)

-- ---------------------------------------------------------------------
-- Corollary B.12 (first-order adequacy): fixing v (rather than
-- existentially quantifying it, as theorem-B11a does) and taking
-- a := Vsem v ρ, e's denotational meaning is (r, leaf a) exactly when e
-- big-steps to THIS v with loss r.
--
-- (⇒) weakened to existential form (a fresh a, concluding SOME v' with
-- e ⇒[r] (val v') and Vsem v' ρ ≡ a) -- this is exactly theorem-B11a
-- restated, and is genuinely as far as this direction can go: pinning
-- the SAME v used by (⇐) would need Vsem injective on closed values,
-- which is FALSE in general (two syntactically different closed
-- function values can denote the same semantic function -- e.g.
-- vabs(val(vvar Z)) and vabs(fst(pair(val(vvar Z))(val(vvar Z)))), both
-- λx.x denotationally). (⇐) is theorem-B10a directly, for the ORIGINAL
-- fixed v.
-- ---------------------------------------------------------------------

corollary-B12 : ∀ {σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC ∅ σ εg} {e : ∅ ⊢ σ ! ε} {v : Val ∅ σ}
               → WFG g → WFE e → (ρ : Env ∅)
               → (∀ {r a} → runSelWith (Esem e ρ) ⌊ g ⌋[ sub , ρ ] ≡ (r , leaf a)
                    → Σ (Val ∅ σ) (λ v' → _⊢_⇒[_]_ {sub = sub} g e r (val v') × Vsem v' ρ ≡ a))
               × (∀ {r} → _⊢_⇒[_]_ {sub = sub} g e r (val v) → runSelWith (Esem e ρ) ⌊ g ⌋[ sub , ρ ] ≡ (r , leaf (Vsem v ρ)))
corollary-B12 wfg wfe ρ = theorem-B11a wfg wfe ρ , (λ stp → theorem-B10a stp wfg wfe ρ)
