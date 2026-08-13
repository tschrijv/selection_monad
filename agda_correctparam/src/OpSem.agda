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
open import Relation.Binary.PropositionalEquality using (_≡_)

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
  F-op      : ∀ {ℓ ε}           → ℓ ∈ ε → (op : Op ℓ) → Frame Γ (gnd (out op)) ε (gnd (in′ op)) ε
  F-loss    : ∀ {ε}             → Frame Γ Loss ε UnitTy ε
  F-handleP : ∀ {ℓ par σ σ' ε}  → Handler Γ ℓ par σ σ' ε → Γ ⊢ σ ! (ε ,ℓ ℓ) → Frame Γ (gnd par) ε σ' ε

data SFrame (Γ : Cxt) : Ty → EffCxt → Ty → EffCxt → Set where
  S-handleB : ∀ {ℓ par σ σ' ε} → Handler Γ ℓ par σ σ' ε → Val Γ (gnd par) → SFrame Γ σ (ε ,ℓ ℓ) σ' ε
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
plugF (F-op m op)     e = opE m op e
plugF F-loss          e = lossE e
plugF (F-handleP h b) e = handleE h e b

plugS : ∀ {Γ σ ε τ ε'} → SFrame Γ σ ε τ ε' → Γ ⊢ σ ! ε → Γ ⊢ τ ! ε'
plugS (S-handleB h v) e     = handleE h (val v) e
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
renF ρ (F-op m op)     = F-op m op
renF ρ F-loss          = F-loss
renF ρ (F-handleP h b) = F-handleP (renH ρ h) (renE ρ b)

renS : ∀ {Γ Γ' σ ε τ ε'} → Ren Γ Γ' → SFrame Γ σ ε τ ε' → SFrame Γ' σ ε τ ε'
renS ρ (S-handleB h v)  = S-handleB (renH ρ h) (renV ρ v)
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
Handles (S∘ k (S-handleB {ℓ = ℓ'} h v)) ℓ = (ℓ ≡ ℓ') ⊎ Handles k ℓ
Handles (S∘ k (S-then _ _)) ℓ           = Handles k ℓ
Handles (S∘ k (S-glocal _ _ _)) ℓ       = Handles k ℓ
Handles (S∘ k S-reset) ℓ                = Handles k ℓ

-- ---------------------------------------------------------------------
-- Helpers for building the substitutions/continuations used by R5 and S1.
-- ---------------------------------------------------------------------

-- The return clause applied to (v, x), x the freshly bound σ-variable:
-- v_r(v,x) : (Γ,σ) ⊢ σ' ! ε.
retApplied : ∀ {Γ ℓ par σ σ' ε} → Handler Γ ℓ par σ σ' ε → Val Γ (gnd par) → (Γ , σ) ⊢ σ' ! ε
retApplied h v = subE (cons (vvar Z) (cons (weaken1V v) wkSub)) (ret h)

-- z : (par × in), destructured.
zP : ∀ {Γ γ δ} → Val (Γ , (gnd γ `× gnd δ)) (gnd γ `× gnd δ)
zP = vvar Z

pArg : ∀ {Γ γ δ ε} → (Γ , (gnd γ `× gnd δ)) ⊢ gnd γ ! ε
pArg = fst (val zP)

yArg : ∀ {Γ γ δ ε} → (Γ , (gnd γ `× gnd δ)) ⊢ gnd δ ! ε
yArg = snd (val zP)

-- ---------------------------------------------------------------------
-- Fig. 6 / Fig. 11: the small-step judgment g ⊢_ε e --r--> e'.
--
-- Unlike the source (and unlike agda/, agda_noparam), εg⊆ᵉε is carried
-- HERE as its own (implicit) INDEX of the family, rather than only ever
-- being supplied separately, downstream, as a side hypothesis (the
-- paper's own Theorem 3.2 does the latter). The payoff: whenever a proof
-- pattern-matches a step derivation, unification forces its OWN εg⊆ᵉε
-- witness to coincide with whichever witness that same derivation
-- carries internally (e.g. R5's own `sub`, used to build fk/fl) --
-- eliminating the need for an ⊆ᵉ-irrelevant-style postulate to bridge
-- two independently-supplied witnesses after the fact (see
-- Proofs.agda's own theorem-B9). The cost: since this new index isn't
-- otherwise determined by any rule's own explicit arguments, EVERY
-- constructor's conclusion must tie it in explicitly via named-implicit
-- application (`_⊢_-[_]→_ {sub = ...} g e r e'`) -- plain infix
-- application leaves it an unsolved meta, even where the rule doesn't
-- otherwise care what it is (confirmed by direct experiment: Agda does
-- not auto-unify an implicit against an in-scope variable merely because
-- they share a name).
-- ---------------------------------------------------------------------

infix 3 _⊢_-[_]→_

data _⊢_-[_]→_ {Γ} : ∀ {σ ε εg} {sub : εg ⊆ᵉ ε} → LC Γ σ εg → Γ ⊢ σ ! ε → R → Γ ⊢ σ ! ε → Set where

  -- (R1) g ⊢ f(v) --0--> v'   (f(v) → v'). εg⊆ᵉε plays no role in this
  -- rule (nor in R2-*/R3/R4/R6/R8/R9/S2/S4/R7 below) -- its own `sub` is
  -- left universally quantified and unused, purely to satisfy the
  -- family's own indexing.
  R1 : ∀ {ε εg γ δ} {sub : εg ⊆ᵉ ε} {g : LC Γ (gnd δ) εg} (f : PrimFun γ δ) (x : ⟦ γ ⟧ᴳ)
     → _⊢_-[_]→_ {sub = sub} g (fun {ε = ε} f (val (vgnd x))) 0# (val (vgnd (⟦ f ⟧f x)))

  -- (R2a) g ⊢ (v1,v2) --0--> vpair(v1,v2)   (pair values coalesce; this is
  -- what makes the *expression*-former `pair` reach a genuine value, so
  -- that a value-level product built via `pair e1 e2` can flow through a
  -- variable -- e.g. after R3 substitutes it in -- and still be
  -- projectable below, exactly as R5's own pArg/yArg construction
  -- (fst/snd of a freshly bound z) needs.)
  R2-pair : ∀ {ε εg σ τ} {sub : εg ⊆ᵉ ε} {g : LC Γ (σ `× τ) εg} (v : Val Γ σ) (w : Val Γ τ)
          → _⊢_-[_]→_ {sub = sub} g (pair {ε = ε} (val v) (val w)) 0# (val (vpair v w))

  -- (R2) g ⊢ vpair(v1,v2).i --0--> vi
  R2-fst : ∀ {ε εg σ τ} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} (v : Val Γ σ) (w : Val Γ τ)
         → _⊢_-[_]→_ {sub = sub} g (fst {ε = ε} (val (vpair v w))) 0# (val v)
  R2-snd : ∀ {ε εg σ τ} {sub : εg ⊆ᵉ ε} {g : LC Γ τ εg} (v : Val Γ σ) (w : Val Γ τ)
         → _⊢_-[_]→_ {sub = sub} g (snd {ε = ε} (val (vpair v w))) 0# (val w)

  -- (R3) g ⊢ (λ^ε x:σ.e) v --0--> e[v/x]
  R3 : ∀ {ε εg σ τ} {sub : εg ⊆ᵉ ε} {g : LC Γ τ εg} (e : (Γ , σ) ⊢ τ ! ε) (v : Val Γ σ)
     → _⊢_-[_]→_ {sub = sub} g (app (val (vabs e)) (val v)) 0# (e [ v ])

  -- (R4) g ⊢ loss(r) --r--> ()
  R4 : ∀ {ε εg} {sub : εg ⊆ᵉ ε} {g : LC Γ UnitTy εg} (r : R)
     → _⊢_-[_]→_ {sub = sub} g (lossE {ε = ε} (val (vgnd r))) r (val (vgnd _))

  -- (R6) g ⊢ with h from v1 handle v2 --0--> v_r(v1,v2)   (return ↦ vr ∈ h)
  R6 : ∀ {ε εg ℓ par σ σ'} {sub : εg ⊆ᵉ ε} {g : LC Γ σ' εg} (h : Handler Γ ℓ par σ σ' ε) (v1 : Val Γ (gnd par)) (v2 : Val Γ σ)
     → _⊢_-[_]→_ {sub = sub} g (handleE h (val v1) (val v2)) 0# (subE (cons v2 (cons v1 idSub)) (ret h))

  -- (R7) g ⊢ v ▶ λ^εg x:σ.e --0--> ⟨e[v/x]⟩^εg_{λ^εg x:σ.0}
  -- (GLOCAL's own natural effect ε₁ is taken to be εg itself here, so its
  -- ε₂⊆ε₁ obligation for the fresh zero-continuation is reflexivity, and
  -- its ε₁⊆ε obligation is exactly THEN's own `sub`.) NOTE: this `sub`
  -- relates e's OWN εg to ε -- the AMBIENT g's own εamb (hence the
  -- family's own new index, for THIS rule) remains unconstrained, since
  -- R7 disregards the ambient g entirely.
  R7 : ∀ {ε εg εamb σ} (sub : εg ⊆ᵉ ε) {subamb : εamb ⊆ᵉ ε} {g : LC Γ Loss εamb} (v : Val Γ σ) (e : (Γ , σ) ⊢ Loss ! εg)
     → _⊢_-[_]→_ {sub = subamb} g (thenE sub (val v) (vabs e)) 0# (glocalE ⊆ᵉ-refl sub (e [ v ]) zeroLC)

  -- (R8) g ⊢ ⟨v⟩^ε₁_g1 --0--> v
  R8 : ∀ {ε ε₂ ε₁ εamb σ} (sub1 : ε₂ ⊆ᵉ ε₁) (sub2 : ε₁ ⊆ᵉ ε) {sub : εamb ⊆ᵉ ε} {g : LC Γ σ εamb} (v : Val Γ σ) (g1 : LC Γ σ ε₂)
     → _⊢_-[_]→_ {sub = sub} g (glocalE sub1 sub2 (val v) g1) 0# (val v)

  -- (R9) g ⊢ reset v --0--> v
  R9 : ∀ {ε εg σ} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} (v : Val Γ σ)
     → _⊢_-[_]→_ {sub = sub} g (resetE {ε = ε} (val v)) 0# (val v)

  -- (F) regular-frame congruence, adjusting the loss continuation to
  -- λ^ε x:α.(F[x]▶g) exactly as the source rule does. Ties the family's
  -- own index to F-rule's OWN `sub` directly -- it already plays exactly
  -- this role (relating the ambient g's εg to ε), used internally to
  -- build the premise's own rewritten continuation.
  F-rule : ∀ {ε εg α σ} (sub : εg ⊆ᵉ ε) {g : LC Γ σ εg} (f : Frame Γ α ε σ ε) {e e' : Γ ⊢ α ! ε} {r : R}
         → _⊢_-[_]→_ {sub = ⊆ᵉ-refl} (vabs (thenE sub (plugF (weaken1F f) (val (vvar Z))) (weaken1V g))) e r e'
         → _⊢_-[_]→_ {sub = sub} g (plugF f e) r (plugF f e')

  -- (S1) operation-under-handler congruence: switch to the return-clause
  -- continuation λ^ε x:σ.(vr(v,x)▶g) while evaluating the handled body.
  -- Ties the index to S1's own `sub`, same reasoning as (F).
  S1 : ∀ {ε εamb ℓ par σ σ'} (sub : εamb ⊆ᵉ ε) {g : LC Γ σ' εamb} (h : Handler Γ ℓ par σ σ' ε) (v : Val Γ (gnd par))
       {e e' : Γ ⊢ σ ! (ε ,ℓ ℓ)} {r : R}
     → _⊢_-[_]→_ {sub = ⊆ᵉ-,ℓ} (vabs (thenE sub (retApplied h v) (weaken1V g))) e r e'
     → _⊢_-[_]→_ {sub = sub} g (handleE h (val v) e) r (handleE h (val v) e')

  -- (S2) g₁ ⊢ e --r--> e' ⟹ g ⊢ (e▶g₁) --0--> r + (e'▶g₁); ▶ disregards
  -- the ambient g entirely and evaluates under its own g₁ instead. "r + e"
  -- (a runtime-only artifact, not source syntax) is realised as
  -- loss(r) ▶ (λ_:().e) -- run loss(r) (which immediately reports r, R4),
  -- then continue as e. `sub` relates g1's OWN εg to ε, not the ambient
  -- g's εamb (unconstrained, per R7's own note above).
  S2 : ∀ {ε εg εamb} (sub : εg ⊆ᵉ ε) {subamb : εamb ⊆ᵉ ε} {g : LC Γ Loss εamb} (g1 : LC Γ Loss εg) {e e' : Γ ⊢ Loss ! ε} {r : R}
     → _⊢_-[_]→_ {sub = sub} g1 e r e'
     → _⊢_-[_]→_ {sub = subamb} g (thenE sub e g1) 0# (thenE ⊆ᵉ-refl (lossE (val (vgnd r))) (vabs (weaken1 (thenE sub e' g1))))

  -- (S3) ⟨e⟩^ε₁_g1 evaluates e under g1 (disregarding the ambient g),
  -- keeping the frame's own effect ε₁, and re-wraps the result. The
  -- ambient g : LC Γ σ ε already lives at ε directly (no separate εg),
  -- so the family's own index is trivially ⊆ᵉ-refl here.
  S3 : ∀ {ε ε₂ ε₁ σ} (sub1 : ε₂ ⊆ᵉ ε₁) (sub2 : ε₁ ⊆ᵉ ε) {g : LC Γ σ ε} (g1 : LC Γ σ ε₂) {e e' : Γ ⊢ σ ! ε₁} {r : R}
     → _⊢_-[_]→_ {sub = sub1} g1 e r e'
     → _⊢_-[_]→_ {sub = ⊆ᵉ-refl} g (glocalE sub1 sub2 e g1) r (glocalE sub1 sub2 e' g1)

  -- (S4) reset evaluates its body under the *same* ambient g, but
  -- contributes no loss of its own (whatever loss e produced is discarded
  -- once evaluation completes, matching censor at the value level).
  S4 : ∀ {ε εg σ} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} {e e' : Γ ⊢ σ ! ε} {r : R}
     → _⊢_-[_]→_ {sub = sub} g e r e'
     → _⊢_-[_]→_ {sub = sub} g (resetE e) 0# (resetE e')

  -- (R5) operation call under a handler that does not yet handle it:
  -- jump directly to h's clause, applied to (param, arg, choice-cont,
  -- delimited-cont). fk is wrapped in the local construct ⟨·⟩ᵍ -- this
  -- wrapper is essential (paper.tex §8 / the arXiv paper's own erratum
  -- discussion) so that the reified delimited continuation denotes a
  -- single, γ-independent element rather than depending on whatever loss
  -- continuation it is later supplied with. Ties the index to R5's own
  -- `sub` directly -- fk/fl are built from exactly this witness.
  R5 : ∀ {ε εamb ℓ par σ σ' εop} (sub : εamb ⊆ᵉ ε) {g : LC Γ σ' εamb}
       (h : Handler Γ ℓ par σ σ' ε) (v1 : Val Γ (gnd par))
       (m : ℓ ∈ εop) (op : Op ℓ) (v2 : Val Γ (gnd (out op)))
       (k : ContCxt Γ (gnd (in′ op)) εop σ (ε ,ℓ ℓ))
     → ¬ Handles k ℓ
     → let Γz  = Γ , (gnd par `× gnd (in′ op))
           h'  = renH S h
           g'  = renV S g
           k'  = weaken1K k
           handled = handleE h' pArg (plugK k' yArg)
           fk  = vabs {σ = gnd par `× gnd (in′ op)} (glocalE sub ⊆ᵉ-refl handled g')
           fl  = vabs {σ = gnd par `× gnd (in′ op)} (thenE sub handled g')
       in _⊢_-[_]→_ {sub = sub} g (handleE h (val v1) (plugK k (opE m op (val v2))))
            0# (subE (cons fk (cons fl (cons v2 (cons v1 idSub)))) (clause h op))

-- ---------------------------------------------------------------------
-- Fig. 7: the big-step judgment g ⊢ e ⇒r w.
-- ---------------------------------------------------------------------

infix 3 _⊢_⇒[_]_

data _⊢_⇒[_]_ {Γ} : ∀ {σ ε εg} → LC Γ σ εg → Γ ⊢ σ ! ε → R → Γ ⊢ σ ! ε → Set where
  done : ∀ {σ ε εg} {g : LC Γ σ εg} (w : Γ ⊢ σ ! ε)
       → g ⊢ w ⇒[ 0# ] w
  step : ∀ {σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} {e1 e2 w : Γ ⊢ σ ! ε} {r s : R}
       → _⊢_-[_]→_ {sub = sub} g e1 r e2 → g ⊢ e2 ⇒[ s ] w → g ⊢ e1 ⇒[ r + s ] w
