-- Theorem A.4.1 of the arXiv paper's Appendix A.4 (progress's easy
-- direction): a terminal expression (Terminal, OpSem.agda) can make no
-- small-step transition. Untouched by the swap paper.tex performs -- it
-- is a fact about the operational semantics alone -- so, like OpSem.agda
-- itself, it is not derived from anything in Domains.agda.
open import Domains using (Sig)

module OpSemProofs (Sg : Sig) where

open Sig Sg
open import Syntax Sg
open import Subst Sg
open import OpSem Sg

open import Data.List.Membership.Propositional using (_∈_)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Product.Properties using (Σ-≡,≡←≡)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Binary.HeterogeneousEquality using (_≅_)

-- ---------------------------------------------------------------------
-- Shape lemmas: no Frame/SFrame ever plugs into a `val` at the top.
-- ---------------------------------------------------------------------

plugF-not-val : ∀ {Γ α β τ ε''} (f : Frame Γ α β τ ε'') (e : Γ ⊢ α ! β) (v : Val Γ τ) → plugF f e ≡ val v → ⊥
plugF-not-val (F-fun _)   e v ()
plugF-not-val (F-pairL _) e v ()
plugF-not-val (F-pairR _) e v ()
plugF-not-val F-fst       e v ()
plugF-not-val F-snd       e v ()
plugF-not-val (F-appL _)  e v ()
plugF-not-val (F-appR _)  e v ()
plugF-not-val (F-op _ _ _)  e v ()
plugF-not-val F-loss      e v ()

plugS-not-val : ∀ {Γ σ ε τ ε'} (s : SFrame Γ σ ε τ ε') (e : Γ ⊢ σ ! ε) (v : Val Γ τ) → plugS s e ≡ val v → ⊥
plugS-not-val (S-handleB _)   e v ()
plugS-not-val (S-then _ _)    e v ()
plugS-not-val (S-glocal _ _ _) e v ()
plugS-not-val S-reset         e v ()

-- K's hole type is now the SAME generic σ that opE itself carries
-- (tied to gnd (in′ op) only via σeq, not syntactically) -- this is
-- exactly what lets the comparisons below go through without Agda's
-- coverage checker getting stuck on the opaque `in′`.
plugK-op-not-val : ∀ {Γ εop ℓ τ ε σ} {m : ℓ ∈ εop} {op : Op ℓ} {σeq : σ ≡ gnd (in′ op)} {v : Val Γ (gnd (out op))}
                    (K : ContCxt Γ σ εop τ ε) (w : Val Γ τ)
                  → plugK K (opE m op σeq (val v)) ≡ val w → ⊥
plugK-op-not-val ▫       w ()
plugK-op-not-val (F∘ k f) w eq = plugF-not-val f _ w eq
plugK-op-not-val (S∘ k s) w eq = plugS-not-val s _ w eq

pair-inj1 : ∀ {Γ σ τ ε} {x1 y1 : Γ ⊢ σ ! ε} {x2 y2 : Γ ⊢ τ ! ε} → pair x1 x2 ≡ pair y1 y2 → x1 ≡ y1
pair-inj1 refl = refl

pair-inj2 : ∀ {Γ σ τ ε} {x1 y1 : Γ ⊢ σ ! ε} {x2 y2 : Γ ⊢ τ ! ε} → pair x1 x2 ≡ pair y1 y2 → x2 ≡ y2
pair-inj2 refl = refl

plugK-op-not-pairvv : ∀ {Γ εop ℓ τ1 τ2 ε σ} {m : ℓ ∈ εop} {op : Op ℓ} {σeq : σ ≡ gnd (in′ op)} {v : Val Γ (gnd (out op))}
                       (K : ContCxt Γ σ εop (τ1 `× τ2) ε) (v1 : Val Γ τ1) (v2 : Val Γ τ2)
                     → plugK K (opE m op σeq (val v)) ≡ pair (val v1) (val v2) → ⊥
plugK-op-not-pairvv (F∘ k (F-pairL _)) v1 v2 eq = plugK-op-not-val k v1 (pair-inj1 eq)
plugK-op-not-pairvv (F∘ k (F-pairR _)) v1 v2 eq = plugK-op-not-val k v2 (pair-inj2 eq)
plugK-op-not-pairvv (F∘ k F-fst)       v1 v2 ()
plugK-op-not-pairvv (F∘ k F-snd)       v1 v2 ()
plugK-op-not-pairvv (F∘ k (F-appL _))  v1 v2 ()
plugK-op-not-pairvv (F∘ k (F-appR _))  v1 v2 ()
plugK-op-not-pairvv (S∘ k (S-handleB _))    v1 v2 ()
plugK-op-not-pairvv (S∘ k (S-glocal _ _ _)) v1 v2 ()
plugK-op-not-pairvv (S∘ k S-reset)          v1 v2 ()

-- Injectivity for the other one-argument-recursive-position expression
-- formers, needed to peel a matching Rn/F-rule layer off both sides of
-- an equation at once.
fun-inj2 : ∀ {Γ γ δ ε} {f1 f2 : PrimFun γ δ} {e1 e2 : Γ ⊢ gnd γ ! ε} → fun f1 e1 ≡ fun f2 e2 → e1 ≡ e2
fun-inj2 refl = refl

-- `fun`'s own domain γ is a *hidden* parameter -- it appears in `f`'s and
-- `e`'s types but not in `fun f e`'s own conclusion type (gnd δ). So an
-- R1-conclusion `fun f (val (vgnd x))`, compared against `fun pf (plugK
-- K (opE ...))` for an INDEPENDENTLY-fresh f, cannot be split via
-- ordinary injectivity (fun-inj2 needs f,pf to already share γ, which
-- Agda cannot derive from the types alone). Proving the combined
-- statement directly by induction on K sidesteps this: `plugK K (opE
-- ...)`'s own outermost shape is always concretely determined by K's
-- outermost frame/sframe constructor (never `val`), so the *argument*
-- position of the outer `fun` always clashes with `val (vgnd x)`
-- regardless of what the (still-opaque) hidden domains are -- `()` only
-- needs ONE definite conflict, not full unification. (F-pairL/F-pairR
-- are dropped outright: their codomain σ`×τ can never unify with the
-- ground type gnd γ0 that K's own codomain is fixed to here.)
plugK-op-not-funval : ∀ {Γ εop ℓ ε σ γ0 δ0} {m : ℓ ∈ εop} {op : Op ℓ} {σeq : σ ≡ gnd (in′ op)} {v : Val Γ (gnd (out op))}
                       (K : ContCxt Γ σ εop (gnd γ0) ε) (pf : PrimFun γ0 δ0) {γ1} (f : PrimFun γ1 δ0) (x : ⟦ γ1 ⟧ᴳ)
                     → fun f (val (vgnd x)) ≡ fun pf (plugK K (opE m op σeq (val v))) → ⊥
plugK-op-not-funval ▫                     pf f x ()
plugK-op-not-funval (F∘ k (F-fun pf'))    pf f x ()
plugK-op-not-funval (F∘ k F-fst)          pf f x ()
plugK-op-not-funval (F∘ k F-snd)          pf f x ()
plugK-op-not-funval (F∘ k (F-appL _))     pf f x ()
plugK-op-not-funval (F∘ k (F-appR _))     pf f x ()
plugK-op-not-funval (F∘ k (F-op _ _ _))     pf f x ()
plugK-op-not-funval (F∘ k F-loss)         pf f x ()
plugK-op-not-funval (S∘ k (S-handleB _))    pf f x ()
plugK-op-not-funval (S∘ k (S-then _ _))     pf f x ()
plugK-op-not-funval (S∘ k (S-glocal _ _ _)) pf f x ()
plugK-op-not-funval (S∘ k S-reset)          pf f x ()

fst-inj : ∀ {Γ σ τ ε} {e1 e2 : Γ ⊢ (σ `× τ) ! ε} → fst {σ = σ} {τ = τ} e1 ≡ fst e2 → e1 ≡ e2
fst-inj refl = refl

snd-inj : ∀ {Γ σ τ ε} {e1 e2 : Γ ⊢ (σ `× τ) ! ε} → snd {σ = σ} {τ = τ} e1 ≡ snd e2 → e1 ≡ e2
snd-inj refl = refl

-- fst's domain (σ`×τ) hides τ from its own codomain σ, so an
-- R2-fst-conclusion's `w1` (of independently-fresh type) can't be
-- compared against K's own (pinned) second component via ordinary
-- injectivity (fst-inj alone would need that hidden τ to already
-- coincide with K's pinned one). `unfst-arg` sidesteps this via
-- Σ-packing (mirroring unapp-fn below): it recovers BOTH fst's hidden τ
-- and its (now single, vpair-carrying) argument at once, `nothing`
-- standing in for "wasn't fst-shaped at all" wherever the fallback branch
-- is never actually exercised.
unfst-arg : ∀ {Γ σ0 ε} → Γ ⊢ σ0 ! ε → Maybe (Σ Ty (λ τ → Γ ⊢ (σ0 `× τ) ! ε))
unfst-arg (fst {τ = τ} e) = just (τ , e)
unfst-arg _               = nothing

-- subst doesn't reduce through constructors unless the equality is
-- literally refl, so extracting a `val`-shaped witness after a subst
-- (as the two Σ-second-component fixes below need) goes through these
-- explicit commutation lemmas instead.
subst-val : ∀ {Γ τ1 τ2 ε} (eq : τ1 ≡ τ2) (w : Val Γ τ1) → subst (λ τ → Γ ⊢ τ ! ε) eq (val w) ≡ val (subst (λ τ → Val Γ τ) eq w)
subst-val refl w = refl

subst-val-pair-snd : ∀ {Γ σ0 τ1 τ2 ε} (eq : τ1 ≡ τ2) (v1 : Val Γ σ0) (w1 : Val Γ τ1)
                    → subst (λ τ → Γ ⊢ (σ0 `× τ) ! ε) eq (val (vpair v1 w1)) ≡ val (vpair v1 (subst (λ τ → Val Γ τ) eq w1))
subst-val-pair-snd refl v1 w1 = refl

subst-val-pair-fst : ∀ {Γ τ0 σ1 σ2 ε} (eq : σ1 ≡ σ2) (v1 : Val Γ σ1) (w1 : Val Γ τ0)
                    → subst (λ σ → Γ ⊢ (σ `× τ0) ! ε) eq (val (vpair v1 w1)) ≡ val (vpair (subst (λ σ → Val Γ σ) eq v1) w1)
subst-val-pair-fst refl v1 w1 = refl

-- Extracts app's own FIRST (function-position) argument via Σ-packing,
-- since (unlike fst) its type varies with what's packed -- needed for
-- theorem-A4-1-op's F-appL clause (F-appR sub-case), mirroring the
-- fstpair/sndpair fix.
unapp-fn : ∀ {Γ τ0 ε} → Γ ⊢ τ0 ! ε → Σ Ty (λ σδ → Γ ⊢ σδ ! ε)
unapp-fn {τ0 = τ0} (app fn arg) = _ , fn
unapp-fn {τ0 = τ0} t             = τ0 , t

-- fst's argument is now a single (vpair-carrying) value rather than two
-- separately-recursed pieces glued by `pair`, so there's no more K-shape
-- to case-split on at all: `eq` itself, via unfst-arg's Σ-packing, already
-- pins down both K's hidden τ0 and its whole opE-headed payload in one
-- shot, leaving just a `plugK-op-not-val` call.
plugK-op-not-fstpair : ∀ {Γ εop ℓ ε σ σ0 τ0} {m : ℓ ∈ εop} {op : Op ℓ} {σeq : σ ≡ gnd (in′ op)} {v : Val Γ (gnd (out op))}
                        (K : ContCxt Γ σ εop (σ0 `× τ0) ε) {τ1} (v1 : Val Γ σ0) (w1 : Val Γ τ1)
                      → fst (val (vpair v1 w1)) ≡ fst (plugK K (opE m op σeq (val v))) → ⊥
plugK-op-not-fstpair K v1 w1 eq =
  plugK-op-not-val K (vpair v1 (subst (λ τ → Val _ τ) τeq w1)) (sym (trans (sym (subst-val-pair-snd τeq v1 w1)) weq))
  where
  packed = just-injective (cong unfst-arg eq)
  τeq = proj₁ (Σ-≡,≡←≡ packed)
  weq = proj₂ (Σ-≡,≡←≡ packed)

-- Same Σ-packing treatment as unfst-arg, for `snd`'s hidden first
-- component.
unsnd-arg : ∀ {Γ τ0 ε} → Γ ⊢ τ0 ! ε → Maybe (Σ Ty (λ σ → Γ ⊢ (σ `× τ0) ! ε))
unsnd-arg (snd {σ = σ} e) = just (σ , e)
unsnd-arg _               = nothing

plugK-op-not-sndpair : ∀ {Γ εop ℓ ε σ σ0 τ0} {m : ℓ ∈ εop} {op : Op ℓ} {σeq : σ ≡ gnd (in′ op)} {v : Val Γ (gnd (out op))}
                        (K : ContCxt Γ σ εop (σ0 `× τ0) ε) {σ1} (v1 : Val Γ σ1) (w1 : Val Γ τ0)
                      → snd (val (vpair v1 w1)) ≡ snd (plugK K (opE m op σeq (val v))) → ⊥
plugK-op-not-sndpair K v1 w1 eq =
  plugK-op-not-val K (vpair (subst (λ σ → Val _ σ) σeq' v1) w1) (sym (trans (sym (subst-val-pair-fst σeq' v1 w1)) veq))
  where
  packed = just-injective (cong unsnd-arg eq)
  σeq' = proj₁ (Σ-≡,≡←≡ packed)
  veq  = proj₂ (Σ-≡,≡←≡ packed)

app-inj1 : ∀ {Γ σ τ ε} {x1 y1 : Γ ⊢ (σ ⇒ τ ! ε) ! ε} {x2 y2 : Γ ⊢ σ ! ε} → app x1 x2 ≡ app y1 y2 → x1 ≡ y1
app-inj1 refl = refl

app-inj2 : ∀ {Γ σ τ ε} {x1 y1 : Γ ⊢ (σ ⇒ τ ! ε) ! ε} {x2 y2 : Γ ⊢ σ ! ε} → app x1 x2 ≡ app y1 y2 → x2 ≡ y2
app-inj2 refl = refl

-- Same hidden-index treatment as plugK-op-not-funval, for `app`'s
-- function-position argument (R3's `val (vabs e1)` vs K's own, opaque
-- second component): the argument-level conflict (val vs never-val)
-- suffices regardless of the hidden domain σ1/σ0.
plugK-op-not-appvalL : ∀ {Γ εop ℓ ε σ σ0 τ0} {m : ℓ ∈ εop} {op : Op ℓ} {σeq : σ ≡ gnd (in′ op)} {v : Val Γ (gnd (out op))}
                        (K : ContCxt Γ σ εop (σ0 ⇒ τ0 ! ε) ε) {σ1} (e1 : (Γ , σ1) ⊢ τ0 ! ε) (v1 : Val Γ σ1) (e2 : Γ ⊢ σ0 ! ε)
                      → app (val (vabs e1)) (val v1) ≡ app (plugK K (opE m op σeq (val v))) e2 → ⊥
plugK-op-not-appvalL ▫                     e1 v1 e2 ()
plugK-op-not-appvalL (F∘ k (F-appL _))     e1 v1 e2 ()
plugK-op-not-appvalL (F∘ k (F-appR _))     e1 v1 e2 ()
plugK-op-not-appvalL (F∘ k F-fst)          e1 v1 e2 ()
plugK-op-not-appvalL (F∘ k F-snd)          e1 v1 e2 ()
plugK-op-not-appvalL (S∘ k (S-handleB _))    e1 v1 e2 ()
plugK-op-not-appvalL (S∘ k (S-glocal _ _ _)) e1 v1 e2 ()
plugK-op-not-appvalL (S∘ k S-reset)          e1 v1 e2 ()

-- Same, for `app`'s argument-position (R3's `val vv` vs K's opaque
-- second component, when K sits under F-appR).
plugK-op-not-appvalR : ∀ {Γ εop ℓ ε σ σ0 τ0} {m : ℓ ∈ εop} {op : Op ℓ} {σeq : σ ≡ gnd (in′ op)} {v : Val Γ (gnd (out op))}
                        (K : ContCxt Γ σ εop σ0 ε) (v1 : Val Γ (σ0 ⇒ τ0 ! ε)) {σ1} (e1 : (Γ , σ1) ⊢ τ0 ! ε) (vv : Val Γ σ1)
                      → app (val (vabs e1)) (val vv) ≡ app (val v1) (plugK K (opE m op σeq (val v))) → ⊥
plugK-op-not-appvalR ▫                     v1 e1 vv ()
plugK-op-not-appvalR (F∘ k (F-appL _))     v1 e1 vv ()
plugK-op-not-appvalR (F∘ k (F-appR _))     v1 e1 vv ()
plugK-op-not-appvalR (F∘ k F-fst)          v1 e1 vv ()
plugK-op-not-appvalR (F∘ k F-snd)          v1 e1 vv ()
plugK-op-not-appvalR (S∘ k (S-handleB _))    v1 e1 vv ()
plugK-op-not-appvalR (S∘ k (S-glocal _ _ _)) v1 e1 vv ()
plugK-op-not-appvalR (S∘ k S-reset)          v1 e1 vv ()

-- Same treatment, for `glocalE`: its own "natural effect" ε₁ (between
-- sub1's target and sub2's source) is hidden from its codomain σ, so
-- R8's independently-fresh ε₁ can't be compared via ordinary
-- injectivity. Proven directly by induction on K instead.
plugK-op-not-glocalval : ∀ {Γ εop ℓ σ σ0 ε2 ε1 ε} {m : ℓ ∈ εop} {op : Op ℓ} {σeq : σ ≡ gnd (in′ op)} {v : Val Γ (gnd (out op))}
                          (K : ContCxt Γ σ εop σ0 ε1) (sub1 : ε2 ⊆ᵉ ε1) (sub2 : ε1 ⊆ᵉ ε) (g1 : LC Γ σ0 ε2)
                          {ε2' ε1'} (sub1' : ε2' ⊆ᵉ ε1') (sub2' : ε1' ⊆ᵉ ε) (v1 : Val Γ σ0) {g1' : LC Γ σ0 ε2'}
                        → glocalE sub1' sub2' (val v1) g1' ≡ glocalE sub1 sub2 (plugK K (opE m op σeq (val v))) g1 → ⊥
plugK-op-not-glocalval ▫                     sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k (F-fun _))      sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k (F-pairL _))    sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k (F-pairR _))    sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k F-fst)          sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k F-snd)          sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k (F-appL _))     sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k (F-appR _))     sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k (F-op _ _ _))     sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k F-loss)         sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (S∘ k (S-handleB _))    sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (S∘ k (S-then _ _))     sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (S∘ k S-reset)          sub1 sub2 g1 sub1' sub2' v1 ()

lossE-inj : ∀ {Γ ε} {e1 e2 : Γ ⊢ Loss ! ε} → lossE e1 ≡ lossE e2 → e1 ≡ e2
lossE-inj refl = refl

-- opE's own argument injectivity (its result type/witnesses/proof are
-- all shared, homogeneous on both sides here, so this is ordinary
-- constructor injectivity, no dependent-index issue).
opE-arg-inj : ∀ {Γ ℓ ε σ} {m1 m2 : ℓ ∈ ε} {op : Op ℓ} {σeq1 σeq2 : σ ≡ gnd (in′ op)} {e1 e2 : Γ ⊢ gnd (out op) ! ε}
            → opE m1 op σeq1 e1 ≡ opE m2 op σeq2 e2 → e1 ≡ e2
opE-arg-inj refl = refl

handleE-arg-inj : ∀ {Γ ℓ σ σ' ε} {h : Handler Γ ℓ σ σ' ε} {e1 e2 : Γ ⊢ σ ! (ε ,ℓ ℓ)} → handleE h e1 ≡ handleE h e2 → e1 ≡ e2
handleE-arg-inj refl = refl

thenE-arg-inj : ∀ {Γ σ ε ε₁} {sub : ε₁ ⊆ᵉ ε} {e1 e2 : Γ ⊢ σ ! ε} {g1 : LC Γ σ ε₁} → thenE sub e1 g1 ≡ thenE sub e2 g1 → e1 ≡ e2
thenE-arg-inj refl = refl

-- Same hidden-index treatment as plugK-op-not-appvalL, for `thenE`: its
-- own "with" continuation g1 (and the ⊆ᵉ witness `sub`) are independent
-- of K's own (pinned) g0, so R7's independently-fresh `sub1,v1,e1` can't
-- be compared against K's own components via ordinary injectivity.
-- Proven directly by induction on K instead.
plugK-op-not-thenval : ∀ {Γ εop ℓ ε σ σ0 εg0} {m : ℓ ∈ εop} {op : Op ℓ} {σeq : σ ≡ gnd (in′ op)} {v : Val Γ (gnd (out op))}
                        (K : ContCxt Γ σ εop σ0 ε) (sub0 : εg0 ⊆ᵉ ε) (g0 : LC Γ σ0 εg0)
                        {σ1 εg1} (sub1 : εg1 ⊆ᵉ ε) (v1 : Val Γ σ1) {e1 : (Γ , σ1) ⊢ Loss ! εg1}
                      → thenE sub1 (val v1) (vabs e1) ≡ thenE sub0 (plugK K (opE m op σeq (val v))) g0 → ⊥
plugK-op-not-thenval ▫                     sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k (F-fun _))      sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k (F-pairL _))    sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k (F-pairR _))    sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k F-fst)          sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k F-snd)          sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k (F-appL _))     sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k (F-appR _))     sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k (F-op _ _ _))   sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k F-loss)         sub0 g0 sub1 v1 ()
plugK-op-not-thenval (S∘ k (S-handleB _))    sub0 g0 sub1 v1 ()
plugK-op-not-thenval (S∘ k (S-glocal _ _ _)) sub0 g0 sub1 v1 ()
plugK-op-not-thenval (S∘ k S-reset)          sub0 g0 sub1 v1 ()

glocalE-arg-inj : ∀ {Γ σ ε₂ ε₁ ε} {sub1 : ε₂ ⊆ᵉ ε₁} {sub2 : ε₁ ⊆ᵉ ε} {e1 e2 : Γ ⊢ σ ! ε₁} {g1 : LC Γ σ ε₂} → glocalE sub1 sub2 e1 g1 ≡ glocalE sub1 sub2 e2 g1 → e1 ≡ e2
glocalE-arg-inj refl = refl

resetE-inj : ∀ {Γ σ ε} {e1 e2 : Γ ⊢ σ ! ε} → resetE e1 ≡ resetE e2 → e1 ≡ e2
resetE-inj refl = refl

-- Rewrite a step derivation's own source along a propositional equality.
subst-src : ∀ {Γ σ ε εg} {g : LC Γ σ εg} {e1 e2 e' : Γ ⊢ σ ! ε} {r : R} → e1 ≡ e2 → g ⊢ e1 -[ r ]→ e' → g ⊢ e2 -[ r ]→ e'
subst-src refl stp = stp

-- ---------------------------------------------------------------------
-- Forward-declared: theorem-A4-1-op-handleB below recurses back into
-- theorem-A4-1-op (S1's own continuation), while theorem-A4-1-op's own
-- S-handleB clause (further down) delegates to theorem-A4-1-op-handleB
-- -- genuine mutual recursion, so only the type signature is needed here.
theorem-A4-1-op : ∀ {Γ σ ε εg εop ℓ} {g : LC Γ σ εg} (m : ℓ ∈ εop) (op : Op ℓ) (v : Val Γ (gnd (out op)))
                   (K : ContCxt Γ (gnd (in′ op)) εop σ ε) → ¬ Handles K ℓ
                 → ∀ {e' : Γ ⊢ σ ! ε} {r : R} → g ⊢ plugK K (opE m op refl (val v)) -[ r ]→ e' → ⊥

-- The S-handleB sub-case (R6/S1/R5 competing for a handleE-headed
-- target with a possibly-different handler). R5's own handler h and its
-- own operation m,op share ONE label (R5 only fires once an operation
-- reaches its own handler), so ruling out R5 needs: h ≡ (our handler) ⟹
-- (R5's operation's label) ≡ (our handler's label) ⟹ contradiction with
-- our own `nh`, which already says our OWN operation's label differs
-- from our handler's. That's not a "some argument conflicts" situation
-- like the fun/fst/app/F-op fixes -- it needs the label of the
-- INNERMOST operation actually extracted from an opaque, K-wrapped
-- term. `opLabelOf` does this: a fixed-codomain (Maybe Effect)
-- projection that recurses toward whichever sub-expression is the
-- "hole" position (falling back to `just ℓ` only once it reaches an
-- opE it can't recurse past), so `cong opLabelOf` can extract the same
-- label from two independently-fresh K-wrapped terms without needing
-- their K's own shapes to line up at all.
-- ---------------------------------------------------------------------

opLabelOf : ∀ {Γ σ ε} → Γ ⊢ σ ! ε → Maybe Effect
opLabelOf (val _)                  = nothing
opLabelOf (fun _ e)                = opLabelOf e
opLabelOf (pair e1 e2)             = opLabelOf e1 <∣> opLabelOf e2
opLabelOf (fst e)                  = opLabelOf e
opLabelOf (snd e)                  = opLabelOf e
opLabelOf (app e1 e2)              = opLabelOf e1 <∣> opLabelOf e2
opLabelOf (opE {ℓ = ℓ} m op σeq e) = opLabelOf e <∣> just ℓ
opLabelOf (lossE e)                = opLabelOf e
opLabelOf (thenE sub e g)          = opLabelOf e
opLabelOf (glocalE sub1 sub2 e g)  = opLabelOf e
opLabelOf (resetE e)               = opLabelOf e
opLabelOf (handleE h e)            = opLabelOf e

opLabelOf-plugK : ∀ {Γ εop ℓ ε σ τ} {m : ℓ ∈ εop} {op : Op ℓ} {σeq : σ ≡ gnd (in′ op)} {v : Val Γ (gnd (out op))}
                  (K : ContCxt Γ σ εop τ ε) → opLabelOf (plugK K (opE m op σeq (val v))) ≡ just ℓ
opLabelOf-plugK ▫                        = refl
opLabelOf-plugK (F∘ k (F-fun _))         = opLabelOf-plugK k
opLabelOf-plugK (F∘ k (F-pairL e₂))      = cong (_<∣> opLabelOf e₂) (opLabelOf-plugK k)
opLabelOf-plugK (F∘ k (F-pairR _))       = opLabelOf-plugK k
opLabelOf-plugK (F∘ k F-fst)             = opLabelOf-plugK k
opLabelOf-plugK (F∘ k F-snd)             = opLabelOf-plugK k
opLabelOf-plugK (F∘ k (F-appL e₂))       = cong (_<∣> opLabelOf e₂) (opLabelOf-plugK k)
opLabelOf-plugK (F∘ k (F-appR _))        = opLabelOf-plugK k
opLabelOf-plugK (F∘ k (F-op _ _ _))      = cong (_<∣> just _) (opLabelOf-plugK k)
opLabelOf-plugK (F∘ k F-loss)            = opLabelOf-plugK k
opLabelOf-plugK (S∘ k (S-handleB _))     = opLabelOf-plugK k
opLabelOf-plugK (S∘ k (S-then _ _))      = opLabelOf-plugK k
opLabelOf-plugK (S∘ k (S-glocal _ _ _))  = opLabelOf-plugK k
opLabelOf-plugK (S∘ k S-reset)           = opLabelOf-plugK k

-- Extracts a handleE's OWN handler label directly (no recursion into
-- the hole) -- fixed codomain again, so it works across the two
-- independently-fresh handlers (ours vs R5's own) without needing them
-- to already coincide.
handlerLabelOf : ∀ {Γ σ ε} → Γ ⊢ σ ! ε → Maybe Effect
handlerLabelOf (handleE {ℓ = ℓ} h e) = just ℓ
handlerLabelOf _                     = nothing

-- Same hidden-index treatment as plugK-op-not-appvalL/thenval, for
-- `handleE`: its own hole type (the handler's domain σh2) is hidden
-- from its codomain σh', so R6's independently-fresh h2,v2 can't be
-- compared against our own (pinned) h,K via ordinary injectivity.
plugK-op-not-handleval : ∀ {Γ εop ℓop ε σ ℓh σh σh'} {m : ℓop ∈ εop} {op : Op ℓop} {σeq : σ ≡ gnd (in′ op)} {v : Val Γ (gnd (out op))}
                          (K : ContCxt Γ σ εop σh (ε ,ℓ ℓh)) (h : Handler Γ ℓh σh σh' ε)
                          {ℓ2 σh2} (h2 : Handler Γ ℓ2 σh2 σh' ε) (v2 : Val Γ σh2)
                        → handleE h2 (val v2) ≡ handleE h (plugK K (opE m op σeq (val v))) → ⊥
plugK-op-not-handleval ▫                        h h2 v2 ()
plugK-op-not-handleval (F∘ k (F-fun _))         h h2 v2 ()
plugK-op-not-handleval (F∘ k (F-pairL _))       h h2 v2 ()
plugK-op-not-handleval (F∘ k (F-pairR _))       h h2 v2 ()
plugK-op-not-handleval (F∘ k F-fst)             h h2 v2 ()
plugK-op-not-handleval (F∘ k F-snd)             h h2 v2 ()
plugK-op-not-handleval (F∘ k (F-appL _))        h h2 v2 ()
plugK-op-not-handleval (F∘ k (F-appR _))        h h2 v2 ()
plugK-op-not-handleval (F∘ k (F-op _ _ _))      h h2 v2 ()
plugK-op-not-handleval (F∘ k F-loss)            h h2 v2 ()
plugK-op-not-handleval (S∘ k (S-handleB _))     h h2 v2 ()
plugK-op-not-handleval (S∘ k (S-then _ _))      h h2 v2 ()
plugK-op-not-handleval (S∘ k (S-glocal _ _ _))  h h2 v2 ()
plugK-op-not-handleval (S∘ k S-reset)           h h2 v2 ()

theorem-A4-1-op-handleB : ∀ {Γ σh σh' ε εg εop ℓ ℓh} {g : LC Γ σh' εg} (m : ℓ ∈ εop) (op : Op ℓ) (v : Val Γ (gnd (out op)))
                           (k : ContCxt Γ (gnd (in′ op)) εop σh (ε ,ℓ ℓh)) (h : Handler Γ ℓh σh σh' ε)
                         → ¬ Handles (S∘ k (S-handleB h)) ℓ
                         → ∀ {e' : Γ ⊢ σh' ! ε} {r : R} → g ⊢ handleE h (plugK k (opE m op refl (val v))) -[ r ]→ e' → ⊥
theorem-A4-1-op-handleB {Γ} {σh' = σh'} {ε = ε} {ℓ = ℓ} {ℓh = ℓh} m op v k h nh stp = helper stp refl
  where
    nh-eq : ¬ (ℓ ≡ ℓh)
    nh-eq ℓ≡ℓh = nh (inj₁ ℓ≡ℓh)
    nh-k : ¬ Handles k ℓ
    nh-k hk = nh (inj₂ hk)

    helper : ∀ {εg'} {g' : LC Γ σh' εg'} {e e' : Γ ⊢ σh' ! ε} {r : R}
           → g' ⊢ e -[ r ]→ e' → e ≡ handleE h (plugK k (opE m op refl (val v))) → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()

    helper (R2-pair v w)             ()
    helper (R3 e v)                 ()
    helper (R4 r)                   ()
    helper (R6 h2 v2)                eq = plugK-op-not-handleval k h h2 v2 eq
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h2 stp)          refl = theorem-A4-1-op m op v k nh-k stp
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 {ℓ = ℓ5} sub h5 m5 op5 v25 k5 nh5) eq =
      let ℓ5≡ℓh : just ℓ5 ≡ just ℓh
          ℓ5≡ℓh = cong handlerLabelOf eq
          ℓ5≡ℓ : just ℓ5 ≡ just ℓ
          ℓ5≡ℓ = trans (sym (opLabelOf-plugK k5)) (trans (cong opLabelOf eq) (opLabelOf-plugK k))
      in nh-eq (trans (sym (just-injective ℓ5≡ℓ)) (just-injective ℓ5≡ℓh))
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub (F-pairL _) stp) ()
    helper (F-rule sub (F-pairR _) stp) ()
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()
    helper (F-rule sub (F-op _ _ _) stp) ()
    helper (F-rule sub F-loss      stp) ()

-- ---------------------------------------------------------------------
-- Theorem A.4.1, value case.
-- ---------------------------------------------------------------------

theorem-A4-1-val : ∀ {Γ σ ε εg} {g : LC Γ σ εg} {v : Val Γ σ} {e' : Γ ⊢ σ ! ε} {r : R}
                  → g ⊢ val v -[ r ]→ e' → ⊥
theorem-A4-1-val stp = helper stp refl
  where
    helper : ∀ {Γ σ ε εg} {g : LC Γ σ εg} {v : Val Γ σ} {e e' : Γ ⊢ σ ! ε} {r : R}
           → g ⊢ e -[ r ]→ e' → e ≡ val v → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()

    helper (R2-pair v w)             ()
    helper (R3 e v)                 ()
    helper (R4 r)                   ()
    helper (R6 h v2)                ()
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h stp)           ()
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h m op v2 k nh)  ()
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub (F-pairL _) stp) ()
    helper (F-rule sub (F-pairR _) stp) ()
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()
    helper (F-rule sub (F-op _ _ _)  stp) ()
    helper (F-rule sub F-loss      stp) ()

-- ---------------------------------------------------------------------
-- Theorem A.4.1, operation case.
-- ---------------------------------------------------------------------

-- K = ▫. Note the helper below re-quantifies m,op,σeq,v (and g) as its
-- OWN fresh implicits, with `e` sharing EXACTLY opE's own σ,ε -- this is
-- what lets every Rn/F-rule unify against it cleanly (no opaque `in′ op`
-- tangled into a separately-declared, disconnected type variable).
theorem-A4-1-op {Γ} m op v ▫ nh stp = helper stp refl
  where
    helper : ∀ {ℓ' εop' σ'} {m' : ℓ' ∈ εop'} {op' : Op ℓ'} {σeq' : σ' ≡ gnd (in′ op')} {v' : Val Γ (gnd (out op'))}
               {εg'} {g' : LC Γ σ' εg'} {e e' : Γ ⊢ σ' ! εop'} {r : R}
           → g' ⊢ e -[ r ]→ e' → e ≡ opE m' op' σeq' (val v') → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()

    helper (R2-pair v w)             ()
    helper (R3 e v)                 ()
    helper (R4 r)                   ()
    helper (R6 h v2)                ()
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h stp)           ()
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h m op v2 k nh)  ()
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub (F-pairL _) stp) ()
    helper (F-rule sub (F-pairR _) stp) ()
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()
    helper (F-rule sub (F-op m'' op'' σeq'') stp) refl = theorem-A4-1-val stp
    helper (F-rule sub F-loss      stp) ()

-- K = F∘ k (F-fun pf). Outer wrapper is `fun`, whose type doesn't depend
-- on any opaque `in′`/`out` computation, so m,op,v,k are simply closed
-- over here (no re-quantification needed) -- only opE-headed targets
-- (the F-op sub-case below) need that treatment.
theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k (F-fun {δ = δ0} pf)) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {g' : LC Γ (gnd δ0) εg'} {e e' : Γ ⊢ gnd δ0 ! ε} {r : R}
           → g' ⊢ e -[ r ]→ e' → e ≡ fun pf (plugK k (opE m op refl (val v))) → ⊥
    helper (R1 f x)                 eq   = plugK-op-not-funval k pf f x eq
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()
    helper (R3 e v)                 ()
    helper (R4 r)                   ()
    helper (R6 h v2)                ()
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h stp)           ()
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h m op v2 k nh)  ()
    helper (F-rule sub (F-fun pf'') stp) refl = theorem-A4-1-op m op v k nh stp
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()
    helper (F-rule sub (F-op _ _ _)  stp) ()
    helper (F-rule sub F-loss      stp) ()

theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k (F-pairL {σ = σ0} {τ = τ0} e₂)) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {g' : LC Γ (σ0 `× τ0) εg'} {e e' : Γ ⊢ (σ0 `× τ0) ! ε} {r : R}
           → g' ⊢ e -[ r ]→ e' → e ≡ pair (plugK k (opE m op refl (val v))) e₂ → ⊥
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()
    helper (R2-pair v w)             eq = plugK-op-not-val k v (sym (pair-inj1 eq))
    helper (R3 e v)                 ()
    helper (R6 h v2)                ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h stp)           ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h m op v2 k nh)  ()
    helper (F-rule sub (F-pairL _) stp) eq = theorem-A4-1-op m op v k nh (subst-src (pair-inj1 eq) stp)
    helper (F-rule sub (F-pairR v1') stp) eq = plugK-op-not-val k v1' (sym (pair-inj1 eq))
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()

theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k (F-pairR {σ = σ0} {τ = τ0} v1)) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {g' : LC Γ (σ0 `× τ0) εg'} {e e' : Γ ⊢ (σ0 `× τ0) ! ε} {r : R}
           → g' ⊢ e -[ r ]→ e' → e ≡ pair (val v1) (plugK k (opE m op refl (val v))) → ⊥
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()
    helper (R2-pair v w)             eq = plugK-op-not-val k w (sym (pair-inj2 eq))
    helper (R3 e v)                 ()
    helper (R6 h v2)                ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h stp)           ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h m op v2 k nh)  ()
    helper (F-rule sub (F-pairL _) stp) eq = theorem-A4-1-val (subst-src (pair-inj1 eq) stp)
    helper (F-rule sub (F-pairR _) stp) eq = theorem-A4-1-op m op v k nh (subst-src (pair-inj2 eq) stp)
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()

theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k (F-fst {σ = σ0} {τ = τ0})) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {g' : LC Γ σ0 εg'} {e e' : Γ ⊢ σ0 ! ε} {r : R}
           → g' ⊢ e -[ r ]→ e' → e ≡ fst (plugK k (opE m op refl (val v))) → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             eq = plugK-op-not-fstpair k v w eq
    helper (R2-snd v w)             ()

    helper (R2-pair v w)             ()
    helper (R3 e v)                 ()
    helper (R4 r)                   ()
    helper (R6 h v2)                ()
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h stp)           ()
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h m op v2 k nh)  ()
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub (F-pairL _) stp) ()
    helper (F-rule sub (F-pairR _) stp) ()
    helper (F-rule sub F-fst       stp) refl = theorem-A4-1-op m op v k nh stp
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()
    helper (F-rule sub (F-op _ _ _)  stp) ()
    helper (F-rule sub F-loss      stp) ()

theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k (F-snd {σ = σ0} {τ = τ0})) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {g' : LC Γ τ0 εg'} {e e' : Γ ⊢ τ0 ! ε} {r : R}
           → g' ⊢ e -[ r ]→ e' → e ≡ snd (plugK k (opE m op refl (val v))) → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             eq = plugK-op-not-sndpair k v w eq
    helper (R3 e v)                 ()
    helper (R4 r)                   ()
    helper (R6 h v2)                ()
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h stp)           ()
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h m op v2 k nh)  ()
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub (F-pairL _) stp) ()
    helper (F-rule sub (F-pairR _) stp) ()
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) refl = theorem-A4-1-op m op v k nh stp
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()
    helper (F-rule sub (F-op _ _ _)  stp) ()
    helper (F-rule sub F-loss      stp) ()

theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k (F-appL {σ = σ0} {τ = τ0} e₂)) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {g' : LC Γ τ0 εg'} {e e' : Γ ⊢ τ0 ! ε} {r : R}
           → g' ⊢ e -[ r ]→ e' → e ≡ app (plugK k (opE m op refl (val v))) e₂ → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()

    helper (R2-pair v w)             ()
    helper (R3 e v')                eq = plugK-op-not-appvalL k e v' e₂ eq
    helper (R4 r)                   ()
    helper (R6 h v2)                ()
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h stp)           ()
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h m op v2 k nh)  ()
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub (F-pairL _) stp) ()
    helper (F-rule sub (F-pairR _) stp) ()
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) refl = theorem-A4-1-op m op v k nh stp
    helper (F-rule sub (F-appR v1'') stp) eq =
      let σδeq = proj₁ (Σ-≡,≡←≡ (cong unapp-fn eq))
          feq  = proj₂ (Σ-≡,≡←≡ (cong unapp-fn eq))
      in plugK-op-not-val k (subst (λ σδ → Val Γ σδ) σδeq v1'') (trans (sym feq) (subst-val σδeq v1''))
    helper (F-rule sub (F-op _ _ _)  stp) ()
    helper (F-rule sub F-loss      stp) ()

theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k (F-appR {σ = σ0} {τ = τ0} v1)) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {g' : LC Γ τ0 εg'} {e e' : Γ ⊢ τ0 ! ε} {r : R}
           → g' ⊢ e -[ r ]→ e' → e ≡ app (val v1) (plugK k (opE m op refl (val v))) → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()

    helper (R2-pair v w)             ()
    helper (R3 e v')                eq = plugK-op-not-appvalR k v1 e v' eq
    helper (R4 r)                   ()
    helper (R6 h v2)                ()
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h stp)           ()
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h m op v2 k nh)  ()
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub (F-pairL _) stp) ()
    helper (F-rule sub (F-pairR _) stp) ()
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) refl = theorem-A4-1-val stp
    helper (F-rule sub (F-appR _)  stp) refl = theorem-A4-1-op m op v k nh stp
    helper (F-rule sub (F-op _ _ _)  stp) ()
    helper (F-rule sub F-loss      stp) ()

-- K = F∘ k (F-op m'' op'' σeq''). Now that F-op itself carries its
-- result type generically (mirroring the opE fix), this needs exactly
-- the same fresh-re-quantification treatment as the ▫ case: τ0 (F-op's
-- own hole/target type) and σeq'' are bound fresh here, not forced to
-- `refl`, so every Rn/F-rule comparison against the opE-headed target
-- unifies cleanly instead of getting stuck on the opaque `in′ op''`.
theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k (F-op {τ = τ0} m'' op'' σeq'')) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {g' : LC Γ τ0 εg'} {e e' : Γ ⊢ τ0 ! ε} {r : R}
           → g' ⊢ e -[ r ]→ e' → e ≡ opE m'' op'' σeq'' (plugK k (opE m op refl (val v))) → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()

    helper (R2-pair v w)             ()
    helper (R3 e v)                 ()
    helper (R4 r)                   ()
    helper (R6 h v2)                ()
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h stp)           ()
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h m op v2 k nh)  ()
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub (F-pairL _) stp) ()
    helper (F-rule sub (F-pairR _) stp) ()
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()
    helper (F-rule sub (F-op m3 op3 σeq3) stp) refl = theorem-A4-1-op m op v k nh stp
    helper (F-rule sub F-loss      stp) ()

theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k F-loss) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {g' : LC Γ UnitTy εg'} {e e' : Γ ⊢ UnitTy ! ε} {r : R}
           → g' ⊢ e -[ r ]→ e' → e ≡ lossE (plugK k (opE m op refl (val v))) → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()
    helper (R3 e v)                 ()
    helper (R4 r)                   eq = plugK-op-not-val k (vgnd r) (sym (lossE-inj eq))
    helper (R6 h v2)                ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h stp)           ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h m op v2 k nh)  ()
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()
    helper (F-rule sub (F-op _ _ _) stp) ()
    helper (F-rule sub F-loss      stp) eq = theorem-A4-1-op m op v k nh (subst-src (lossE-inj eq) stp)

-- K = S∘ k (S-handleB h): delegates wholesale to theorem-A4-1-op-handleB
-- (see comment above it, and above opLabelOf/handlerLabelOf).
theorem-A4-1-op m op v (S∘ k (S-handleB h)) nh stp = theorem-A4-1-op-handleB m op v k h nh stp

theorem-A4-1-op {Γ} {ε = ε} m op v (S∘ k (S-then sub g0)) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {g' : LC Γ Loss εg'} {e e' : Γ ⊢ Loss ! ε} {r : R}
           → g' ⊢ e -[ r ]→ e' → e ≡ thenE sub (plugK k (opE m op refl (val v))) g0 → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()
    helper (R3 e v)                 ()
    helper (R6 h v2)                ()
    helper (R7 sub' v' e')          eq = plugK-op-not-thenval k sub g0 sub' v' eq
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h stp)           ()
    helper (S2 sub' g1 stp)         refl = theorem-A4-1-op m op v k nh stp
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h m op v2 k nh)  ()
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()
    helper (F-rule sub (F-op _ _ _) stp) ()

theorem-A4-1-op {Γ} {σ = σ'} {ε = ε} m op v (S∘ k (S-glocal sub1 sub2 g0)) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {g' : LC Γ σ' εg'} {e e' : Γ ⊢ σ' ! ε} {r : R}
           → g' ⊢ e -[ r ]→ e' → e ≡ glocalE sub1 sub2 (plugK k (opE m op refl (val v))) g0 → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()

    helper (R2-pair v w)             ()
    helper (R3 e v)                 ()
    helper (R4 r)                   ()
    helper (R6 h v2)                ()
    helper (R7 sub v e)             ()
    helper (R8 sub1' sub2' v' g1)   eq = plugK-op-not-glocalval k sub1 sub2 g0 sub1' sub2' v' eq
    helper (R9 v)                   ()
    helper (S1 sub h stp)           ()
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1' sub2' g1 stp)  refl = theorem-A4-1-op m op v k nh stp
    helper (S4 stp)                 ()
    helper (R5 sub h m op v2 k nh)  ()
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub (F-pairL _) stp) ()
    helper (F-rule sub (F-pairR _) stp) ()
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()
    helper (F-rule sub (F-op _ _ _)  stp) ()
    helper (F-rule sub F-loss      stp) ()

theorem-A4-1-op {Γ} {σ = σ'} {ε = ε} m op v (S∘ k S-reset) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {g' : LC Γ σ' εg'} {e e' : Γ ⊢ σ' ! ε} {r : R}
           → g' ⊢ e -[ r ]→ e' → e ≡ resetE (plugK k (opE m op refl (val v))) → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()

    helper (R2-pair v w)             ()
    helper (R3 e v)                 ()
    helper (R4 r)                   ()
    helper (R6 h v2)                ()
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v')                  eq = plugK-op-not-val k v' (sym (resetE-inj eq))
    helper (S1 sub h stp)           ()
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 refl = theorem-A4-1-op m op v k nh stp
    helper (R5 sub h m op v2 k nh)  ()
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub (F-pairL _) stp) ()
    helper (F-rule sub (F-pairR _) stp) ()
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()
    helper (F-rule sub (F-op _ _ _)  stp) ()
    helper (F-rule sub F-loss      stp) ()

-- ---------------------------------------------------------------------
-- Theorem A.4.1, combined.
-- ---------------------------------------------------------------------

theorem-A4-1 : ∀ {Γ σ ε εg} {g : LC Γ σ εg} {e e' : Γ ⊢ σ ! ε} {r : R}
             → Terminal e → g ⊢ e -[ r ]→ e' → ⊥
theorem-A4-1 (terminalVal v)          stp = theorem-A4-1-val stp
theorem-A4-1 (terminalOp m op v K nh) stp = theorem-A4-1-op m op v K nh stp

-- ---------------------------------------------------------------------
-- Theorem A.4.2 (determinism): if an expression takes a small step in
-- two different ways, those two ways are the same. Stated as a single
-- heterogeneous equality between the two derivations themselves (not
-- just their results r,e') -- since stp1 : g⊢e-[r1]→e1' and stp2 :
-- g⊢e-[r2]→e2' don't share a type until r1≡r2 and e1'≡e2' are already
-- known, ordinary `_≡_` can't even be stated between them directly, and
-- `stp1 ≅ stp2` already forces both index equalities as a consequence
-- of being inhabited (by refl) at all, so it is the whole statement:
-- no need for r1≡r2/e1'≡e2' as separate conjuncts.
--
-- Formulated only, not proved here.
-- ---------------------------------------------------------------------

postulate
  theorem-A4-2 : ∀ {Γ σ ε εg} {g : LC Γ σ εg} {e : Γ ⊢ σ ! ε} {r1 r2 : R} {e1' e2' : Γ ⊢ σ ! ε}
                 (stp1 : g ⊢ e -[ r1 ]→ e1') (stp2 : g ⊢ e -[ r2 ]→ e2')
               → stp1 ≅ stp2
