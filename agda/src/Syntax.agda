-- Intrinsically typed & scoped syntax of the core λC fragment: variables,
-- constants, tuples, projection, abstraction, application, operation
-- calls, loss, then (▶), the local construct (⟨e⟩ᵍ), reset, and handling.
-- Following paper.tex §7 (and the original paper's own restriction when
-- porting Appendix B), we omit sum types, nat, and list -- called "routine"
-- extensions there, orthogonal to everything the companion note is about.
--
-- Using de Bruijn indices means every expression constructed below is, by
-- construction, well-typed (Fig. 4 / Appendix A.2) -- there is no separate
-- typing relation to state or keep in sync.
open import Domains using (Sig)

module Syntax (Sg : Sig) where

open Sig Sg

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)

-- ---------------------------------------------------------------------
-- Typing contexts and variables.
-- ---------------------------------------------------------------------

data Cxt : Set where
  ∅   : Cxt
  _,_ : Cxt → Ty → Cxt

data _∋_ : Cxt → Ty → Set where
  Z : ∀ {Γ σ}     → (Γ , σ) ∋ σ
  S : ∀ {Γ σ τ}   → Γ ∋ σ → (Γ , τ) ∋ σ

infix 3 _⊢_!_

-- Values, handlers, and expressions are all mutually recursive: a value
-- may be a λ-abstraction whose body is an expression (Fig. 5's
-- `value ::= ... | λ^ε x:σ.e`), and expressions/handlers embed values and
-- (for handling) handlers.
mutual

  -- Values (Fig. 5's `value` syntactic class). Values can be typed at
  -- *any* effect (VAR/CONST/PRD/ABS in Fig. 4), so they form their own,
  -- effect-independent syntactic category, exactly as the paper's own
  -- operational-semantics grammar does.
  data Val (Γ : Cxt) : Ty → Set where
    vvar  : ∀ {σ}     → Γ ∋ σ → Val Γ σ
    vgnd  : ∀ {γ}     → ⟦ γ ⟧ᴳ → Val Γ (gnd γ)                    -- constants c : b, r : loss, ()
    vpair : ∀ {σ τ}   → Val Γ σ → Val Γ τ → Val Γ (σ `× τ)
    vabs  : ∀ {σ τ ε} → (Γ , σ) ⊢ τ ! ε → Val Γ (σ ⇒ τ ! ε)

  -- A loss continuation g : σ → loss ! ε is *not* a separate syntactic
  -- category: THEN's own typing rule (Fig. 4) types its body as a fully
  -- general expression, Γ,x:σ⊢e2:loss!ε2 -- unrestricted. (Appendix A.1's
  -- narrower grammar "g ::= λx.0 | λx.e▶g" describes the shapes that
  -- *arise* as artifacts of evaluation, not a restriction on source
  -- syntax; §4's loss-function semantics ℒ is likewise stated for a fully
  -- general body.) So we just reuse the ordinary function-valued value.
  LC : Cxt → Ty → EffCxt → Set
  LC Γ σ ε = Val Γ (σ ⇒ Loss ! ε)

  -- A handler for effect ℓ: a σ',par-indexed clause for every operation of
  -- ℓ (HANDLER rule), plus a return clause. Each clause/return is written
  -- with its parameters as nested context extensions rather than as one
  -- literal tuple-typed variable z : (par,out,...) -- an inessential,
  -- de-Bruijn-friendly repackaging of the same information.
  --
  -- NB both clause and return are annotated λ^ε (not λ^εℓ): the "!εℓ" in
  -- the HANDLER typing rule is the *ambient* effect at which the clause
  -- value itself is written (values being effect-polymorphic, cf. ABS),
  -- not the effect of its body once applied -- exactly as paper.tex's own
  -- handler construction writes each clause "λ^ε z:(...).eᵢ" (§5).
  record Handler (Γ : Cxt) (ℓ : Effect) (par : GTy) (σ σ' : Ty) (ε : EffCxt) : Set where
    inductive
    field
      clause : (op : Op ℓ)
             → (((Γ , gnd par) , gnd (out op))
                 , ((gnd par `× gnd (in′ op)) ⇒ Loss ! ε))
                 , ((gnd par `× gnd (in′ op)) ⇒ σ' ! ε)
               ⊢ σ' ! ε
      ret    : (Γ , gnd par) , σ ⊢ σ' ! ε

  -- Core expressions Γ ⊢ σ ! ε (Fig. 4 / Appendix A.1-A.2, core fragment).
  data _⊢_!_ (Γ : Cxt) : Ty → EffCxt → Set where
    val     : ∀ {σ ε}       → Val Γ σ → Γ ⊢ σ ! ε
    fun     : ∀ {γ δ ε}     → PrimFun γ δ → Γ ⊢ gnd γ ! ε → Γ ⊢ gnd δ ! ε
    pair    : ∀ {σ τ ε}     → Γ ⊢ σ ! ε → Γ ⊢ τ ! ε → Γ ⊢ (σ `× τ) ! ε
    fst     : ∀ {σ τ ε}     → Γ ⊢ (σ `× τ) ! ε → Γ ⊢ σ ! ε
    snd     : ∀ {σ τ ε}     → Γ ⊢ (σ `× τ) ! ε → Γ ⊢ τ ! ε
    app     : ∀ {σ τ ε}     → Γ ⊢ (σ ⇒ τ ! ε) ! ε → Γ ⊢ σ ! ε → Γ ⊢ τ ! ε
    opE     : ∀ {ℓ ε}       → ℓ ∈ ε → (op : Op ℓ) → Γ ⊢ gnd (out op) ! ε → Γ ⊢ gnd (in′ op) ! ε
    lossE   : ∀ {ε}         → Γ ⊢ Loss ! ε → Γ ⊢ UnitTy ! ε
    thenE   : ∀ {σ ε ε₁}     → ε₁ ⊆ᵉ ε → Γ ⊢ σ ! ε → LC Γ σ ε₁ → Γ ⊢ Loss ! ε
    -- GLOCAL: Γ⊢g:σ→loss!ε₂  Γ⊢e:σ!ε₁  (ε₂⊆ε₁⊆ε) ⟹ Γ⊢⟨e⟩^ε₁_g:σ!ε -- note
    -- *two* separate inclusions (g's own effect can be smaller than e's,
    -- which in turn can be smaller than the ambient ε the whole
    -- expression is used at), not one -- easy to conflate since THEN only
    -- has one.
    glocalE : ∀ {σ ε₂ ε₁ ε}  → ε₂ ⊆ᵉ ε₁ → ε₁ ⊆ᵉ ε → Γ ⊢ σ ! ε₁ → LC Γ σ ε₂ → Γ ⊢ σ ! ε
    resetE  : ∀ {σ ε}       → Γ ⊢ σ ! ε → Γ ⊢ σ ! ε
    handleE : ∀ {ℓ par σ σ' ε} → Handler Γ ℓ par σ σ' ε → Γ ⊢ gnd par ! ε → Γ ⊢ σ ! (ε ,ℓ ℓ) → Γ ⊢ σ' ! ε

open Handler public

-- The zero loss continuation λ^ε x:σ.0.
zeroLC : ∀ {Γ σ ε} → LC Γ σ ε
zeroLC = vabs (val (vgnd 0#))
