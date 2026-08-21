-- Renaming and (value-)substitution for the core fragment. This is
-- standard de-Bruijn plumbing (as in PLFA's "DeBruijn" chapter), needed to
-- even *state* beta-reduction (R3), the loss-continuation substitution in
-- R7/THEN, and the delimited/choice continuations captured by R5 (which
-- weaken a captured continuation context K into a bigger context before
-- plugging a fresh variable into it). It is exactly the machinery behind
-- Lemma A.1 / B.1 (Substitution) of the source papers, which we do not yet
-- state or prove as a lemma -- we only need the *operation*, not (yet) its
-- correctness properties.
open import Domains using (Sig)

module Subst (Sg : Sig) where

open Sig Sg
open import Syntax Sg

-- ---------------------------------------------------------------------
-- Renaming.
-- ---------------------------------------------------------------------

Ren : Cxt → Cxt → Set
Ren Γ Γ' = ∀ {σ} → Γ ∋ σ → Γ' ∋ σ

extR : ∀ {Γ Γ' τ} → Ren Γ Γ' → Ren (Γ , τ) (Γ' , τ)
extR ρ Z     = Z
extR ρ (S x) = S (ρ x)

mutual
  renV : ∀ {Γ Γ' σ} → Ren Γ Γ' → Val Γ σ → Val Γ' σ
  renV ρ (vvar x)    = vvar (ρ x)
  renV ρ (vgnd x)    = vgnd x
  renV ρ (vpair v w) = vpair (renV ρ v) (renV ρ w)
  renV ρ (vabs e)    = vabs (renE (extR ρ) e)

  renH : ∀ {Γ Γ' ℓ par σ σ' ε} → Ren Γ Γ' → Handler Γ ℓ par σ σ' ε → Handler Γ' ℓ par σ σ' ε
  clause (renH ρ h) op = renE (extR (extR (extR (extR ρ)))) (clause h op)
  ret    (renH ρ h)    = renE (extR (extR ρ)) (ret h)

  renE : ∀ {Γ Γ' σ ε} → Ren Γ Γ' → Γ ⊢ σ ! ε → Γ' ⊢ σ ! ε
  renE ρ (val v)          = val (renV ρ v)
  renE ρ (fun f e)        = fun f (renE ρ e)
  renE ρ (pair e e₁)      = pair (renE ρ e) (renE ρ e₁)
  renE ρ (fst e)          = fst (renE ρ e)
  renE ρ (snd e)          = snd (renE ρ e)
  renE ρ (app e e₁)       = app (renE ρ e) (renE ρ e₁)
  renE ρ (opE m op e)     = opE m op (renE ρ e)
  renE ρ (lossE e)        = lossE (renE ρ e)
  renE ρ (thenE s e g)    = thenE s (renE ρ e) (renV ρ g)
  renE ρ (plusE e1 e2)    = plusE (renE ρ e1) (renE ρ e2)
  renE ρ (glocalE s₁ s₂ e g) = glocalE s₁ s₂ (renE ρ e) (renV ρ g)
  renE ρ (resetE e)       = resetE (renE ρ e)
  renE ρ (handleE h e e₁) = handleE (renH ρ h) (renE ρ e) (renE ρ e₁)

weaken1 : ∀ {Γ σ τ ε} → Γ ⊢ σ ! ε → (Γ , τ) ⊢ σ ! ε
weaken1 = renE S

weaken1V : ∀ {Γ σ τ} → Val Γ σ → Val (Γ , τ) σ
weaken1V = renV S

-- ---------------------------------------------------------------------
-- Substitution (of values for variables).
-- ---------------------------------------------------------------------

Sub : Cxt → Cxt → Set
Sub Γ Γ' = ∀ {σ} → Γ ∋ σ → Val Γ' σ

extS : ∀ {Γ Γ' τ} → Sub Γ Γ' → Sub (Γ , τ) (Γ' , τ)
extS σs Z     = vvar Z
extS σs (S x) = weaken1V (σs x)

mutual
  subV : ∀ {Γ Γ' σ} → Sub Γ Γ' → Val Γ σ → Val Γ' σ
  subV σs (vvar x)    = σs x
  subV σs (vgnd x)    = vgnd x
  subV σs (vpair v w) = vpair (subV σs v) (subV σs w)
  subV σs (vabs e)    = vabs (subE (extS σs) e)

  subH : ∀ {Γ Γ' ℓ par σ σ' ε} → Sub Γ Γ' → Handler Γ ℓ par σ σ' ε → Handler Γ' ℓ par σ σ' ε
  clause (subH σs h) op = subE (extS (extS (extS (extS σs)))) (clause h op)
  ret    (subH σs h)    = subE (extS (extS σs)) (ret h)

  subE : ∀ {Γ Γ' σ ε} → Sub Γ Γ' → Γ ⊢ σ ! ε → Γ' ⊢ σ ! ε
  subE σs (val v)          = val (subV σs v)
  subE σs (fun f e)        = fun f (subE σs e)
  subE σs (pair e e₁)      = pair (subE σs e) (subE σs e₁)
  subE σs (fst e)          = fst (subE σs e)
  subE σs (snd e)          = snd (subE σs e)
  subE σs (app e e₁)       = app (subE σs e) (subE σs e₁)
  subE σs (opE m op e)     = opE m op (subE σs e)
  subE σs (lossE e)        = lossE (subE σs e)
  subE σs (thenE s e g)    = thenE s (subE σs e) (subV σs g)
  subE σs (plusE e1 e2)    = plusE (subE σs e1) (subE σs e2)
  subE σs (glocalE s₁ s₂ e g) = glocalE s₁ s₂ (subE σs e) (subV σs g)
  subE σs (resetE e)       = resetE (subE σs e)
  subE σs (handleE h e e₁) = handleE (subH σs h) (subE σs e) (subE σs e₁)

-- The identity substitution, and extending a substitution by one more
-- value for the newly bound (innermost) variable -- the building blocks
-- for simultaneous multi-variable substitution (needed by R5's clause
-- instantiation z := (v1,v2,fl,fk) and R6's return-clause instantiation
-- z := (v1,v2)).
idSub : ∀ {Γ} → Sub Γ Γ
idSub = vvar

cons : ∀ {Γ Γ' τ} → Val Γ' τ → Sub Γ Γ' → Sub (Γ , τ) Γ'
cons v σs Z     = v
cons v σs (S x) = σs x

-- Single substitution, e[v/x] : the base case Sub (Γ,σ) Γ that sends the
-- newly bound variable to v and leaves the rest of Γ alone.
sub1 : ∀ {Γ σ} → Val Γ σ → Sub (Γ , σ) Γ
sub1 v = cons v idSub

_[_] : ∀ {Γ σ τ ε} → (Γ , σ) ⊢ τ ! ε → Val Γ σ → Γ ⊢ τ ! ε
e [ v ] = subE (sub1 v) e

-- Embed Γ into Γ,τ by weakening every variable by one (a substitution
-- version of `weaken1`, used when a value from Γ needs to sit alongside a
-- freshly bound variable of a *different* context extension).
wkSub : ∀ {Γ τ} → Sub Γ (Γ , τ)
wkSub x = vvar (S x)
