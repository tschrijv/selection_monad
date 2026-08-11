-- The operational semantics of λC (Fig. 5-7 of the arXiv paper / Appendix
-- A.3), for the core fragment of Syntax.agda. This is *unchanged* by the
-- swap paper.tex performs -- it is the common ground the original
-- denotational semantics and the "hat" one are both proved sound and
-- adequate against -- so it is transcribed directly from the source, not
-- derived from anything in Domains.agda.
open import Domains using (Sig)

module OpSem (Sg : Sig) where

open Sig Sg
open import Syntax Sg
open import Subst Sg

open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ---------------------------------------------------------------------
-- Fig. 5: frames, special frames, and continuation contexts.
--
-- `Frame Γ σ ε τ ε'` / `SFrame Γ σ ε τ ε'` : a one-hole context expecting a
-- hole of type σ!ε, producing an expression of type τ!ε' when filled.
-- Every *regular* frame preserves the effect context (ε' = ε): none of
-- F-fun .. F-handleP change what effects are available at the hole versus
-- at the result, which is exactly why rule (F) below can reuse a single g.
-- ---------------------------------------------------------------------

data Frame (Γ : Cxt) : Ty → EffCxt → Ty → EffCxt → Set where
  F-fun     : ∀ {γ δ ε}         → PrimFun γ δ → Frame Γ (gnd γ) ε (gnd δ) ε
  F-pairL   : ∀ {σ τ ε}         → Γ ⊢ τ ! ε → Frame Γ σ ε (σ `× τ) ε
  F-pairR   : ∀ {σ τ ε}         → Val Γ σ → Frame Γ τ ε (σ `× τ) ε
  F-fst     : ∀ {σ τ ε}         → Frame Γ (σ `× τ) ε σ ε
  F-snd     : ∀ {σ τ ε}         → Frame Γ (σ `× τ) ε τ ε
  F-appL    : ∀ {σ τ ε}         → Γ ⊢ σ ! ε → Frame Γ (σ ⇒ τ ! ε) ε τ ε
  F-appR    : ∀ {σ τ ε}         → Val Γ (σ ⇒ τ ! ε) → Frame Γ σ ε τ ε
  F-op      : ∀ {ℓ ε τ}         → ℓ ∈ ε → (op : Op ℓ) → τ ≡ gnd (in′ op) → Frame Γ (gnd (out op)) ε τ ε
  F-loss    : ∀ {ε}             → Frame Γ Loss ε UnitTy ε
  -- No F-handleP: parameter-free handleE has a single hole (the body,
  -- at effect ε,ℓ ℓ), which changes the effect context on the way out --
  -- exactly what makes it an SFrame (S-handleB below), not a regular
  -- (effect-preserving) Frame. There is no longer a separate "parameter"
  -- hole to evaluate first.

data SFrame (Γ : Cxt) : Ty → EffCxt → Ty → EffCxt → Set where
  S-handleB : ∀ {ℓ σ σ' ε} → Handler Γ ℓ σ σ' ε → SFrame Γ σ (ε ,ℓ ℓ) σ' ε
  S-then    : ∀ {σ ε εg}       → εg ⊆ᵉ ε → LC Γ σ εg → SFrame Γ σ ε Loss ε
  S-glocal  : ∀ {σ ε₂ ε₁ ε}    → ε₂ ⊆ᵉ ε₁ → ε₁ ⊆ᵉ ε → LC Γ σ ε₂ → SFrame Γ σ ε₁ σ ε
  S-reset   : ∀ {σ ε}          → SFrame Γ σ ε σ ε

-- K ::= □ | F[K] | S[K], built "outside-in" (the hole is innermost).
data ContCxt (Γ : Cxt) (σ : Ty) (ε : EffCxt) : Ty → EffCxt → Set where
  ▫  : ContCxt Γ σ ε σ ε
  F∘ : ∀ {α β τ ε''} → ContCxt Γ σ ε α β → Frame Γ α β τ ε'' → ContCxt Γ σ ε τ ε''
  S∘ : ∀ {α β τ ε''} → ContCxt Γ σ ε α β → SFrame Γ α β τ ε'' → ContCxt Γ σ ε τ ε''

plugF : ∀ {Γ σ ε τ ε'} → Frame Γ σ ε τ ε' → Γ ⊢ σ ! ε → Γ ⊢ τ ! ε'
plugF (F-fun f)       e = fun f e
plugF (F-pairL e₂)    e = pair e e₂
plugF (F-pairR v)     e = pair (val v) e
plugF F-fst           e = fst e
plugF F-snd           e = snd e
plugF (F-appL e₂)     e = app e e₂
plugF (F-appR v)      e = app (val v) e
plugF (F-op m op τeq) e = opE m op τeq e
plugF F-loss          e = lossE e

plugS : ∀ {Γ σ ε τ ε'} → SFrame Γ σ ε τ ε' → Γ ⊢ σ ! ε → Γ ⊢ τ ! ε'
plugS (S-handleB h) e       = handleE h e
plugS (S-then sub g) e      = thenE sub e g
plugS (S-glocal sub1 sub2 g) e = glocalE sub1 sub2 e g
plugS S-reset e             = resetE e

plugK : ∀ {Γ σ ε τ ε'} → ContCxt Γ σ ε τ ε' → Γ ⊢ σ ! ε → Γ ⊢ τ ! ε'
plugK ▫        e = e
plugK (F∘ k f) e = plugF f (plugK k e)
plugK (S∘ k s) e = plugS s (plugK k e)

-- Weakening of frames/contexts (needed to move a captured continuation
-- context K into the extended context of a handler clause's body, cf. R5).
renF : ∀ {Γ Γ' σ ε τ ε'} → Ren Γ Γ' → Frame Γ σ ε τ ε' → Frame Γ' σ ε τ ε'
renF ρ (F-fun f)       = F-fun f
renF ρ (F-pairL e)     = F-pairL (renE ρ e)
renF ρ (F-pairR v)     = F-pairR (renV ρ v)
renF ρ F-fst           = F-fst
renF ρ F-snd           = F-snd
renF ρ (F-appL e)      = F-appL (renE ρ e)
renF ρ (F-appR v)      = F-appR (renV ρ v)
renF ρ (F-op m op τeq) = F-op m op τeq
renF ρ F-loss          = F-loss

renS : ∀ {Γ Γ' σ ε τ ε'} → Ren Γ Γ' → SFrame Γ σ ε τ ε' → SFrame Γ' σ ε τ ε'
renS ρ (S-handleB h)    = S-handleB (renH ρ h)
renS ρ (S-then sub g)   = S-then sub (renV ρ g)
renS ρ (S-glocal sub1 sub2 g) = S-glocal sub1 sub2 (renV ρ g)
renS ρ S-reset          = S-reset

renK : ∀ {Γ Γ' σ ε τ ε'} → Ren Γ Γ' → ContCxt Γ σ ε τ ε' → ContCxt Γ' σ ε τ ε'
renK ρ ▫        = ▫
renK ρ (F∘ k f) = F∘ (renK ρ k) (renF ρ f)
renK ρ (S∘ k s) = S∘ (renK ρ k) (renS ρ s)

weaken1K : ∀ {Γ σ ε τ ε' υ} → ContCxt Γ σ ε τ ε' → ContCxt (Γ , υ) σ ε τ ε'
weaken1K = renK S

weaken1F : ∀ {Γ σ ε τ ε' υ} → Frame Γ σ ε τ ε' → Frame (Γ , υ) σ ε τ ε'
weaken1F = renF S

-- h_eff(K) as a Set-valued predicate: whether K already handles ℓ anywhere
-- along its (outer) chain of special frames. Used for R5's side condition
-- op ∉ h_op(K), stated there as ¬ Handles k ℓ for op : Op ℓ.
Handles : ∀ {Γ σ ε τ ε'} → ContCxt Γ σ ε τ ε' → Effect → Set
Handles ▫ ℓ                             = ⊥
Handles (F∘ k f) ℓ                      = Handles k ℓ
Handles (S∘ k (S-handleB {ℓ = ℓ'} h)) ℓ  = (ℓ ≡ ℓ') ⊎ Handles k ℓ
Handles (S∘ k (S-then _ _)) ℓ           = Handles k ℓ
Handles (S∘ k (S-glocal _ _ _)) ℓ       = Handles k ℓ
Handles (S∘ k S-reset) ℓ                = Handles k ℓ

-- ---------------------------------------------------------------------
-- Helpers for building the substitutions/continuations used by R5 and S1.
-- ---------------------------------------------------------------------

-- The return clause, ready to be plugged in wherever a value emerges
-- from a handled body: v_r(x) : (Γ,σ) ⊢ σ' ! ε. Parameter-free, ret h's
-- own context (Γ,σ) already matches exactly -- no substitution needed.
retApplied : ∀ {Γ ℓ σ σ' ε} → Handler Γ ℓ σ σ' ε → (Γ , σ) ⊢ σ' ! ε
retApplied h = ret h

-- ---------------------------------------------------------------------
-- Fig. 6 / Fig. 11: the small-step judgment g ⊢_ε e --r--> e'.
--
-- σ, ε (of e,e') and ε_g (of g) are kept as separate indices: the paper's
-- own statements (e.g. Theorem 3.2) only ever relate them via a *side
-- hypothesis* ε_g ⊆ ε, never bake it into the judgment itself.
-- ---------------------------------------------------------------------

infix 3 _⊢_-[_]→_

data _⊢_-[_]→_ {Γ} : ∀ {σ ε εg} → LC Γ σ εg → Γ ⊢ σ ! ε → R → Γ ⊢ σ ! ε → Set where

  -- (R1) g ⊢ f(v) --0--> v'   (f(v) → v')
  R1 : ∀ {ε εg γ δ} {g : LC Γ (gnd δ) εg} (f : PrimFun γ δ) (x : ⟦ γ ⟧ᴳ)
     → g ⊢ fun {ε = ε} f (val (vgnd x)) -[ 0# ]→ val (vgnd (⟦ f ⟧f x))

  -- (R2a) g ⊢ (v1,v2) --0--> vpair(v1,v2)   (pair values coalesce; this is
  -- what makes the *expression*-former `pair` reach a genuine value, so
  -- that a value-level product built via `pair e1 e2` can flow through a
  -- variable -- e.g. after R3 substitutes it in -- and still be
  -- projectable below, exactly as R5's own construction (fst/snd of a
  -- freshly bound z) needs.)
  R2-pair : ∀ {ε εg σ τ} {g : LC Γ (σ `× τ) εg} (v : Val Γ σ) (w : Val Γ τ)
          → g ⊢ pair {ε = ε} (val v) (val w) -[ 0# ]→ val (vpair v w)

  -- (R2) g ⊢ vpair(v1,v2).i --0--> vi
  R2-fst : ∀ {ε εg σ τ} {g : LC Γ σ εg} (v : Val Γ σ) (w : Val Γ τ)
         → g ⊢ fst {ε = ε} (val (vpair v w)) -[ 0# ]→ val v
  R2-snd : ∀ {ε εg σ τ} {g : LC Γ τ εg} (v : Val Γ σ) (w : Val Γ τ)
         → g ⊢ snd {ε = ε} (val (vpair v w)) -[ 0# ]→ val w

  -- (R3) g ⊢ (λ^ε x:σ.e) v --0--> e[v/x]
  R3 : ∀ {ε εg σ τ} {g : LC Γ τ εg} (e : (Γ , σ) ⊢ τ ! ε) (v : Val Γ σ)
     → g ⊢ app (val (vabs e)) (val v) -[ 0# ]→ (e [ v ])

  -- (R4) g ⊢ loss(r) --r--> ()
  R4 : ∀ {ε εg} {g : LC Γ UnitTy εg} (r : R)
     → g ⊢ lossE {ε = ε} (val (vgnd r)) -[ r ]→ val (vgnd _)

  -- (R6) g ⊢ with h handle v2 --0--> v_r(v2)   (return ↦ vr ∈ h)
  R6 : ∀ {ε εg ℓ σ σ'} {g : LC Γ σ' εg} (h : Handler Γ ℓ σ σ' ε) (v2 : Val Γ σ)
     → g ⊢ handleE h (val v2) -[ 0# ]→ subE (cons v2 idSub) (ret h)

  -- (R7) g ⊢ v ▶ λ^εg x:σ.e --0--> ⟨e[v/x]⟩^εg_{λ^εg x:σ.0}
  -- (GLOCAL's own natural effect ε₁ is taken to be εg itself here, so its
  -- ε₂⊆ε₁ obligation for the fresh zero-continuation is reflexivity, and
  -- its ε₁⊆ε obligation is exactly THEN's own `sub`.)
  R7 : ∀ {ε εg εamb σ} (sub : εg ⊆ᵉ ε) {g : LC Γ Loss εamb} (v : Val Γ σ) (e : (Γ , σ) ⊢ Loss ! εg)
     → g ⊢ thenE sub (val v) (vabs e) -[ 0# ]→ glocalE ⊆ᵉ-refl sub (e [ v ]) zeroLC

  -- (R8) g ⊢ ⟨v⟩^ε₁_g1 --0--> v
  R8 : ∀ {ε ε₂ ε₁ εamb σ} (sub1 : ε₂ ⊆ᵉ ε₁) (sub2 : ε₁ ⊆ᵉ ε) {g : LC Γ σ εamb} (v : Val Γ σ) (g1 : LC Γ σ ε₂)
     → g ⊢ glocalE sub1 sub2 (val v) g1 -[ 0# ]→ val v

  -- (R9) g ⊢ reset v --0--> v
  R9 : ∀ {ε εg σ} {g : LC Γ σ εg} (v : Val Γ σ)
     → g ⊢ resetE {ε = ε} (val v) -[ 0# ]→ val v

  -- (F) regular-frame congruence, adjusting the loss continuation to
  -- λ^ε x:α.(F[x]▶g) exactly as the source rule does.
  F-rule : ∀ {ε εg α σ} (sub : εg ⊆ᵉ ε) {g : LC Γ σ εg} (f : Frame Γ α ε σ ε) {e e' : Γ ⊢ α ! ε} {r : R}
         → vabs (thenE sub (plugF (weaken1F f) (val (vvar Z))) (weaken1V g)) ⊢ e -[ r ]→ e'
         → g ⊢ plugF f e -[ r ]→ plugF f e'

  -- (S1) operation-under-handler congruence: switch to the return-clause
  -- continuation λ^ε x:σ.(vr(x)▶g) while evaluating the handled body.
  S1 : ∀ {ε εamb ℓ σ σ'} (sub : εamb ⊆ᵉ ε) {g : LC Γ σ' εamb} (h : Handler Γ ℓ σ σ' ε)
       {e e' : Γ ⊢ σ ! (ε ,ℓ ℓ)} {r : R}
     → vabs (thenE sub (retApplied h) (weaken1V g)) ⊢ e -[ r ]→ e'
     → g ⊢ handleE h e -[ r ]→ handleE h e'

  -- (S2) g₁ ⊢ e --r--> e' ⟹ g ⊢ (e▶g₁) --0--> r + (e'▶g₁); ▶ disregards
  -- the ambient g entirely and evaluates under its own g₁ instead. "r + e"
  -- (a runtime-only artifact, not source syntax) is realised as
  -- loss(r) ▶ (λ_:().e) -- run loss(r) (which immediately reports r, R4),
  -- then continue as e.
  S2 : ∀ {ε εg εamb} (sub : εg ⊆ᵉ ε) {g : LC Γ Loss εamb} (g1 : LC Γ Loss εg) {e e' : Γ ⊢ Loss ! ε} {r : R}
     → g1 ⊢ e -[ r ]→ e'
     → g ⊢ thenE sub e g1 -[ 0# ]→ thenE ⊆ᵉ-refl (lossE (val (vgnd r))) (vabs (weaken1 (thenE sub e' g1)))

  -- (S3) ⟨e⟩^ε₁_g1 evaluates e under g1 (disregarding the ambient g),
  -- keeping the frame's own effect ε₁, and re-wraps the result.
  S3 : ∀ {ε ε₂ ε₁ σ} (sub1 : ε₂ ⊆ᵉ ε₁) (sub2 : ε₁ ⊆ᵉ ε) {g : LC Γ σ ε} (g1 : LC Γ σ ε₂) {e e' : Γ ⊢ σ ! ε₁} {r : R}
     → g1 ⊢ e -[ r ]→ e'
     → g ⊢ glocalE sub1 sub2 e g1 -[ r ]→ glocalE sub1 sub2 e' g1

  -- (S4) reset evaluates its body under the *same* ambient g, but
  -- contributes no loss of its own (whatever loss e produced is discarded
  -- once evaluation completes, matching censor at the value level).
  S4 : ∀ {ε εg σ} {g : LC Γ σ εg} {e e' : Γ ⊢ σ ! ε} {r : R}
     → g ⊢ e -[ r ]→ e'
     → g ⊢ resetE e -[ 0# ]→ resetE e'

  -- (R5) operation call under a handler that does not yet handle it:
  -- jump directly to h's clause, applied to (arg, choice-cont,
  -- delimited-cont). fk is wrapped in the local construct ⟨·⟩ᵍ -- this
  -- wrapper is essential (paper.tex §8 / the arXiv paper's own erratum
  -- discussion) so that the reified delimited continuation denotes a
  -- single, γ-independent element rather than depending on whatever loss
  -- continuation it is later supplied with.
  R5 : ∀ {ε εamb ℓ σ σ' εop} (sub : εamb ⊆ᵉ ε) {g : LC Γ σ' εamb}
       (h : Handler Γ ℓ σ σ' ε)
       (m : ℓ ∈ εop) (op : Op ℓ) (v2 : Val Γ (gnd (out op)))
       (k : ContCxt Γ (gnd (in′ op)) εop σ (ε ,ℓ ℓ))
     → ¬ Handles k ℓ
     → let Γz  = Γ , gnd (in′ op)
           h'  = renH S h
           g'  = renV S g
           k'  = weaken1K k
           handled = handleE h' (plugK k' (val (vvar Z)))
           fk  = vabs {σ = gnd (in′ op)} (glocalE sub ⊆ᵉ-refl handled g')
           fl  = vabs {σ = gnd (in′ op)} (thenE sub handled g')
       in g ⊢ handleE h (plugK k (opE m op refl (val v2)))
            -[ 0# ]→ subE (cons fk (cons fl (cons v2 idSub))) (clause h op)

-- ---------------------------------------------------------------------
-- Fig. 7: the big-step judgment g ⊢ e ⇒r w.
-- ---------------------------------------------------------------------

infix 3 _⊢_⇒[_]_

data _⊢_⇒[_]_ {Γ} : ∀ {σ ε εg} → LC Γ σ εg → Γ ⊢ σ ! ε → R → Γ ⊢ σ ! ε → Set where
  done : ∀ {σ ε εg} {g : LC Γ σ εg} (w : Γ ⊢ σ ! ε)
       → g ⊢ w ⇒[ 0# ] w
  step : ∀ {σ ε εg} {g : LC Γ σ εg} {e1 e2 w : Γ ⊢ σ ! ε} {r s : R}
       → g ⊢ e1 -[ r ]→ e2 → g ⊢ e2 ⇒[ s ] w → g ⊢ e1 ⇒[ r + s ] w

-- ---------------------------------------------------------------------
-- Terminal expressions: the two shapes a well-typed big-step evaluation
-- (_⊢_⇒[_]_ above) can terminate at, since -[_]→ has no further rule to
-- apply from either. A plain value is (trivially) terminal; the
-- interesting case is a term of the form K[op(v)] -- an operation call,
-- plugged into a continuation context K, none of whose special frames
-- (S-handleB's) handle op's own label ℓ anywhere along K, i.e.
-- ¬ Handles K ℓ.
-- ---------------------------------------------------------------------

data Terminal : ∀ {Γ σ ε} → Γ ⊢ σ ! ε → Set where
  terminalVal : ∀ {Γ σ ε} (v : Val Γ σ) → Terminal {Γ} {σ} {ε} (val v)
  terminalOp  : ∀ {Γ σ ε εop ℓ} (m : ℓ ∈ εop) (op : Op ℓ) (v : Val Γ (gnd (out op)))
                (K : ContCxt Γ (gnd (in′ op)) εop σ ε) (nh : ¬ Handles K ℓ)
              → Terminal (plugK K (opE m op refl (val v)))

