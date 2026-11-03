-- Intrinsically typed & scoped syntax of the full λC language: variables,
-- constants, tuples, projection, abstraction, application, operation
-- calls, loss, then (▶), the local construct (⟨e⟩ᵍ), reset, handling, and
-- (PHASE 1 EXTENSION) sum types, nat, and list -- cases/injections,
-- zero/succ/iter, and nil/cons/fold, following
-- jfp/sections/core_language.tex's Fig. "Syntax of expressions and
-- handlers" and the fuller grammar in jfp/appendix/appendixv3.tex.
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
    -- PHASE 1 EXTENSION: value forms of the sum/nat/list introduction
    -- forms, exactly paralleling vpair's relationship to the expression
    -- former `pair` (and vgnd's to constants). The paper's own value
    -- grammar (appendixv3.tex) is `v ::= ... | inl_{σ,τ}(v) | inr_{σ,τ}(v)
    -- | zero | succ(v) | nil_σ | cons(v1,v2) | ...`; these six
    -- constructors transcribe exactly that, one-for-one.
    vinl  : ∀ {σ τ}   → Val Γ σ → Val Γ (σ `+ τ)
    vinr  : ∀ {σ τ}   → Val Γ τ → Val Γ (σ `+ τ)
    vzero :             Val Γ nat
    vsucc :             Val Γ nat → Val Γ nat
    vnil  : ∀ {σ}     → Val Γ (list σ)
    vcons : ∀ {σ}     → Val Γ σ → Val Γ (list σ) → Val Γ (list σ)

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
    -- PHASE 1 EXTENSION: sum types. `inl`/`inr` parallel `pair` (a
    -- general sub-expression under an introduction form); there is no
    -- expression-level `vinl`/`vinr` *analogue* needed beyond these, since
    -- values are already embedded into expressions via `val` (cf. how
    -- there is no separate expression constructor for constants beyond
    -- `val (vgnd x)`). Unlike `pair`, the co-domain's OTHER summand (τ for
    -- inl, σ for inr) is not determined by the sub-expression's own type
    -- -- exactly as the paper's own annotated `inl_{σ,τ}(e)`/`inr_{σ,τ}(e)`
    -- make explicit -- so here it is recovered the usual way for this
    -- intrinsically-typed style: as an implicit argument, solved from the
    -- expected/ambient type at each use site rather than written out.
    inl     : ∀ {σ τ ε}     → Γ ⊢ σ ! ε → Γ ⊢ (σ `+ τ) ! ε
    inr     : ∀ {σ τ ε}     → Γ ⊢ τ ! ε → Γ ⊢ (σ `+ τ) ! ε
    -- `cases e of x1:σ.e1 | x2:τ.e2` (CASES rule): e is a general
    -- scrutinee expression; e1/e2 are typed under Γ extended by the
    -- respective bound variable, exactly like a Handler clause/return
    -- extends Γ by its own bound parameters (Fig. 4's rule: both branches
    -- share the scrutinee's own effect ε and the result type ρ).
    cases   : ∀ {σ τ ρ ε}   → Γ ⊢ (σ `+ τ) ! ε → (Γ , σ) ⊢ ρ ! ε → (Γ , τ) ⊢ ρ ! ε → Γ ⊢ ρ ! ε
    -- PHASE 1 EXTENSION: nat. `zero` needs no expression-level
    -- constructor (same reasoning as inl/inr above: `val vzero` already
    -- covers it). `succ` parallels `fst`/`snd`: one general sub-expression
    -- under an elimination-free, "wrapping" introduction form.
    succ    : ∀ {ε}         → Γ ⊢ nat ! ε → Γ ⊢ nat ! ε
    -- `iter(e1,e2,e3)` (ITER rule): e1 the nat being iterated over, e2 the
    -- base case (of the result type σ), e3 the step function, of type
    -- (σ ⇒ σ ! ε) ! ε -- a plain *value-level* function (the current
    -- grammar, per appendixv3.tex, has no extra variable binder on iter
    -- itself; an older, commented-out version of the typing rules
    -- (jfp/rules.tex's e-iter2/e-iter3) *did* write iter's step argument
    -- with its own explicit binder `(x:σ)e3`, but that shape is
    -- superseded by the current Fig. "Syntax of expressions and handlers"
    -- grammar, which has plain `iter(e1,e2,e3)` with e3 an ordinary
    -- expression of function type -- confirmed against (R13)'s own
    -- reduction `iter(succ(v1),v2,v3) --0--> v3 iter(v1,v2,v3)`, an
    -- ordinary *application* of v3, not a substitution into some bound
    -- body). All three sub-expressions share ambient effect ε, and the
    -- step function's own result effect is likewise ε (ITER's typing rule
    -- in rules.tex: e3 : (σ → σ!ε)!ε).
    iter    : ∀ {σ ε}       → Γ ⊢ nat ! ε → Γ ⊢ σ ! ε → Γ ⊢ (σ ⇒ σ ! ε) ! ε → Γ ⊢ σ ! ε
    -- PHASE 1 EXTENSION: list. `nil_σ` needs no expression-level
    -- constructor either (again, `val vnil` suffices). `consE` parallels
    -- `pair`: two general sub-expressions. (Named `consE`, not plain
    -- `cons` -- unlike inl/inr/cases/succ/iter/fold, which have no clash
    -- -- because Subst.agda already defines its OWN top-level `cons`, the
    -- substitution-extension helper `Val Γ' τ → Sub Γ Γ' → Sub (Γ,τ) Γ'`;
    -- since Subst.agda opens this module unqualified, the two would
    -- otherwise clash, exactly the reason opE/lossE are already suffixed
    -- in this file.)
    consE   : ∀ {σ ε}       → Γ ⊢ σ ! ε → Γ ⊢ (list σ) ! ε → Γ ⊢ (list σ) ! ε
    -- `fold(e1,e2,e3)` (FOLD rule): e1 the list, e2 the base case (of
    -- result type τ), e3 the step function. Unlike iter's step function,
    -- fold's takes a *pair* -- the list's head (type σ) and the
    -- accumulated result (type τ) -- reflecting (R15)'s reduction
    -- `fold(cons(v1,v2),v3,v4) --0--> v4(v1,fold(v2,v3,v4))`, an
    -- application of v4 to the PAIR (v1, fold(v2,v3,v4)); we realise that
    -- pairing using the already-existing `_`×_` Ty-former, exactly as the
    -- paper's own typing rule does: e3 : ((σ,τ) ⇒ τ!ε)!ε.
    fold    : ∀ {σ τ ε}     → Γ ⊢ (list σ) ! ε → Γ ⊢ τ ! ε → Γ ⊢ ((σ `× τ) ⇒ τ ! ε) ! ε → Γ ⊢ τ ! ε
    app     : ∀ {σ τ ε}     → Γ ⊢ (σ ⇒ τ ! ε) ! ε → Γ ⊢ σ ! ε → Γ ⊢ τ ! ε
    opE     : ∀ {ℓ ε}       → ℓ ∈ ε → (op : Op ℓ) → Γ ⊢ gnd (out op) ! ε → Γ ⊢ gnd (in′ op) ! ε
    lossE   : ∀ {ε}         → Γ ⊢ Loss ! ε → Γ ⊢ UnitTy ! ε
    thenE   : ∀ {σ ε ε₁}     → ε₁ ⊆ᵉ ε → Γ ⊢ σ ! ε → LC Γ σ ε₁ → Γ ⊢ Loss ! ε
    -- "e1 + e2" (Fig. 6's own admissible notation "r + e", S2's
    -- conclusion): a runtime-only artifact, never written by a source
    -- program, that hoists a known loss out in front of whatever e2
    -- itself later reports. Both operands are ordinary expressions
    -- (symmetric with pair, fst/snd), NOT one baked-in raw R constant
    -- plus one expression -- realised here as its own regular-frame-
    -- shaped constructor (rather than desugared via thenE/lossE, which
    -- loops: see OpSem.agda's S2 comment), so that e1+e2's only
    -- reduction, once BOTH operands are values v1 v2 : loss, is the
    -- LOSS TYPE's own _+_ (a Sig field) applied directly to v1 and v2.
    plusE   : ∀ {ε}         → Γ ⊢ Loss ! ε → Γ ⊢ Loss ! ε → Γ ⊢ Loss ! ε
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
