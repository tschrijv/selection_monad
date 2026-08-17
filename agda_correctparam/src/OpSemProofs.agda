-- Theorem A.4.1 of the arXiv paper's Appendix A.4 (progress's easy
-- direction): a terminal expression (Terminal, OpSem.agda) can make no
-- small-step transition. Untouched by the swap paper.tex performs -- it
-- is a fact about the operational semantics alone -- so, like OpSem.agda
-- itself, it is not derived from anything in Domains.agda.
--
-- Ported from agda_noparam/src/OpSemProofs.agda, adjusted for three
-- structural differences in this construction's own OpSem.agda: (1)
-- handlers now carry an explicit parameter (Handler Γ ℓ par σ σ' ε; R6/
-- S1/R5/S-handleB/handleE all gained an extra `Val Γ (gnd par)`
-- argument/hole), (2) F-op/opE no longer carry a σeq proof (F-op's own
-- codomain is directly `gnd (in′ op)`, not tied in via an equation --
-- simplifying every plugK-op-not-* lemma below, none of which need the
-- old "fresh re-quantification of σeq" workaround anymore), and (3) a
-- brand-new regular frame F-handleP (evaluating a handler's own
-- parameter position, ahead of its body -- parameter-free handlers had
-- no such hole) needs a case everywhere a "generic codomain" K-shape is
-- enumerated, plus its own dedicated congruence case in theorem-A4-1-op.
open import Domains using (Sig)

module OpSemProofs (Sg : Sig) where

open Sig Sg
open import Syntax Sg
open import Subst Sg
open import OpSem Sg

open import Data.List.Membership.Propositional using (_∈_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing; _<∣>_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Product.Properties using (Σ-≡,≡←≡)
open import Relation.Nullary using (¬_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Binary.HeterogeneousEquality using (_≅_; ≡-to-≅) renaming (refl to ≅-refl; sym to ≅-sym; trans to ≅-trans)

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
plugF-not-val (F-op _ _)  e v ()
plugF-not-val F-loss      e v ()
plugF-not-val (F-handleP _ _) e v ()

plugS-not-val : ∀ {Γ σ ε τ ε'} (s : SFrame Γ σ ε τ ε') (e : Γ ⊢ σ ! ε) (v : Val Γ τ) → plugS s e ≡ val v → ⊥
plugS-not-val (S-handleB _ _) e v ()
plugS-not-val (S-then _ _)    e v ()
plugS-not-val (S-glocal _ _ _) e v ()
plugS-not-val S-reset         e v ()

-- K's hole type is now the SAME generic σ that opE itself carries
-- (tied to gnd (in′ op) only via its own conclusion type, not via a
-- separate σeq proof -- opE no longer carries one at all) -- this is
-- exactly what lets the comparisons below go through without Agda's
-- coverage checker getting stuck on the opaque `in′`.
plugK-op-not-val : ∀ {Γ εop ℓ τ ε} {m : ℓ ∈ εop} {op : Op ℓ} {v : Val Γ (gnd (out op))}
                    (K : ContCxt Γ (gnd (in′ op)) εop τ ε) (w : Val Γ τ)
                  → plugK K (opE m op (val v)) ≡ val w → ⊥
plugK-op-not-val ▫       w ()
plugK-op-not-val (F∘ k f) w eq = plugF-not-val f _ w eq
plugK-op-not-val (S∘ k s) w eq = plugS-not-val s _ w eq

val-inj : ∀ {Γ σ ε} {v1 v2 : Val Γ σ} → val {ε = ε} v1 ≡ val v2 → v1 ≡ v2
val-inj refl = refl

pair-inj1 : ∀ {Γ σ τ ε} {x1 y1 : Γ ⊢ σ ! ε} {x2 y2 : Γ ⊢ τ ! ε} → pair x1 x2 ≡ pair y1 y2 → x1 ≡ y1
pair-inj1 refl = refl

pair-inj2 : ∀ {Γ σ τ ε} {x1 y1 : Γ ⊢ σ ! ε} {x2 y2 : Γ ⊢ τ ! ε} → pair x1 x2 ≡ pair y1 y2 → x2 ≡ y2
pair-inj2 refl = refl

plugK-op-not-pairvv : ∀ {Γ εop ℓ τ1 τ2 ε} {m : ℓ ∈ εop} {op : Op ℓ} {v : Val Γ (gnd (out op))}
                       (K : ContCxt Γ (gnd (in′ op)) εop (τ1 `× τ2) ε) (v1 : Val Γ τ1) (v2 : Val Γ τ2)
                     → plugK K (opE m op (val v)) ≡ pair (val v1) (val v2) → ⊥
plugK-op-not-pairvv (F∘ k (F-pairL _)) v1 v2 eq = plugK-op-not-val k v1 (pair-inj1 eq)
plugK-op-not-pairvv (F∘ k (F-pairR _)) v1 v2 eq = plugK-op-not-val k v2 (pair-inj2 eq)
plugK-op-not-pairvv (F∘ k F-fst)       v1 v2 ()
plugK-op-not-pairvv (F∘ k F-snd)       v1 v2 ()
plugK-op-not-pairvv (F∘ k (F-appL _))  v1 v2 ()
plugK-op-not-pairvv (F∘ k (F-appR _))  v1 v2 ()
plugK-op-not-pairvv (F∘ k (F-handleP _ _)) v1 v2 ()
plugK-op-not-pairvv (S∘ k (S-handleB _ _))    v1 v2 ()
plugK-op-not-pairvv (S∘ k (S-glocal _ _ _)) v1 v2 ()
plugK-op-not-pairvv (S∘ k S-reset)          v1 v2 ()

-- Injectivity for the other one-argument-recursive-position expression
-- formers, needed to peel a matching Rn/F-rule layer off both sides of
-- an equation at once.
fun-inj2 : ∀ {Γ γ δ ε} {f1 f2 : PrimFun γ δ} {e1 e2 : Γ ⊢ gnd γ ! ε} → fun f1 e1 ≡ fun f2 e2 → e1 ≡ e2
fun-inj2 refl = refl

-- fun-inj1/handleE-inj: fully generalized companions (extracting EVERY
-- component, not just one, unlike the "one shared/one varying" lemmas
-- above) -- needed by R5-cont-unique's own same-shape K-pairings below,
-- where BOTH sides' fixed components (PrimFun, Handler, ...) are
-- independently fresh per side, not already known equal. Safe to use
-- `refl` directly here (unlike fun-inj2's own comment above about R1-
-- vs-F-op): by the time these are called, go's own clause head has
-- ALREADY unified the surrounding σ1≡σ2/β1≡β2 (hence e.g. γ,δ here) via
-- the same "refl refl refl refl" reduction confirmed safe throughout
-- go's induction. (thenE/glocalE don't need an analogous fully-
-- generalized version: their own ⊆ᵉ-witnesses get unified up front, by
-- go's own unthen-key/unglocal-key Σ-packing, before the EXISTING
-- single-sub thenE-arg-inj/glocalE-arg-inj are used at all.)
fun-inj1 : ∀ {Γ γ δ ε} {f1 f2 : PrimFun γ δ} {e1 e2 : Γ ⊢ gnd γ ! ε} → fun f1 e1 ≡ fun f2 e2 → f1 ≡ f2
fun-inj1 refl = refl

handleE-inj : ∀ {Γ ℓ par σ σ' ε} {h1 h2 : Handler Γ ℓ par σ σ' ε} {p1 p2 : Γ ⊢ gnd par ! ε} {b1 b2 : Γ ⊢ σ ! (ε ,ℓ ℓ)}
            → handleE h1 p1 b1 ≡ handleE h2 p2 b2 → h1 ≡ h2 × p1 ≡ p2 × b1 ≡ b2
handleE-inj refl = refl , refl , refl

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
plugK-op-not-funval : ∀ {Γ εop ℓ ε γ0 δ0} {m : ℓ ∈ εop} {op : Op ℓ} {v : Val Γ (gnd (out op))}
                       (K : ContCxt Γ (gnd (in′ op)) εop (gnd γ0) ε) (pf : PrimFun γ0 δ0) {γ1} (f : PrimFun γ1 δ0) (x : ⟦ γ1 ⟧ᴳ)
                     → fun f (val (vgnd x)) ≡ fun pf (plugK K (opE m op (val v))) → ⊥
plugK-op-not-funval ▫                     pf f x ()
plugK-op-not-funval (F∘ k (F-fun pf'))    pf f x ()
plugK-op-not-funval (F∘ k F-fst)          pf f x ()
plugK-op-not-funval (F∘ k F-snd)          pf f x ()
plugK-op-not-funval (F∘ k (F-appL _))     pf f x ()
plugK-op-not-funval (F∘ k (F-appR _))     pf f x ()
plugK-op-not-funval (F∘ k (F-op _ _))     pf f x ()
plugK-op-not-funval (F∘ k F-loss)         pf f x ()
plugK-op-not-funval (F∘ k (F-handleP _ _)) pf f x ()
plugK-op-not-funval (S∘ k (S-handleB _ _))    pf f x ()
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

-- unfun-key: Σ-packages fun's hidden domain γ together with its PrimFun
-- ONLY (dropping the argument entirely) -- ε/Γ-independent, so its own
-- commutation is trivial homogeneous equality (no generic-atE dance
-- needed). Used by R5-cont-unique's own F-fun case: since γ isn't part
-- of F-fun's own visible codomain (only δ is), it survives as a
-- genuinely independent hidden type on each side -- but, unlike the
-- gnd(in′op1) vs gnd(in′op2) case earlier, γA/γB here are NOT tied to
-- any outer, rigid value (they're fresh per this clause's own F-fun
-- pattern), so γAeq itself can be pattern-matched to refl directly
-- (safe: a single, homogeneous GTy equality) -- once done, kA/kB share
-- the exact same type and go recurses on them with no further casting
-- at all, sidestepping the whole wrapF∘-fst-style machinery.
unfun-key : ∀ {Γ δ0 ε} → Γ ⊢ gnd δ0 ! ε → Maybe (Σ GTy (λ γ → PrimFun γ δ0))
unfun-key (fun {γ = γ} pf e) = just (γ , pf)
unfun-key _                  = nothing

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

-- app's own hidden argument type σ (shared between the function
-- position's own σ⇒τ0!ε and the argument position's own σ, but not
-- part of app's own codomain τ0) -- same "hidden, but genuinely fresh
-- per this clause's own pattern" situation as unfun-key's γ above, so
-- σAeq can likewise be pattern-matched to refl directly, after which
-- app-inj1/app-inj2 apply to `eq` normally.
unapp-key : ∀ {Γ τ0 ε} → Γ ⊢ τ0 ! ε → Maybe (Σ Ty (λ σ → Γ ⊢ (σ ⇒ τ0 ! ε) ! ε))
unapp-key (app {σ = σ} fn arg) = just (σ , fn)
unapp-key _                    = nothing

-- handleE's own hidden ℓ/par/σ (not part of its own codomain σ0',
-- which is all F-handleP/S-handleB's own outer wrapping exposes) --
-- packaged as ONE combined, Γ/ε-independent-except-for-h key, so the
-- WHOLE thing (including h itself) can be pattern-matched to refl in
-- one shot, exactly like unfun-key's (γ,pf) pair above.
unhandle-key : ∀ {Γ σ0' ε} → Γ ⊢ σ0' ! ε → Maybe (Σ Effect (λ ℓ → Σ GTy (λ par → Σ Ty (λ σ → Handler Γ ℓ par σ σ0' ε))))
unhandle-key (handleE {ℓ = ℓ} {par = par} {σ = σ} h p b) = just (ℓ , par , σ , h)
unhandle-key _                                           = nothing

-- thenE's codomain is ALWAYS Loss (no σ dependency at all), so its own
-- hole type σ and its LC body's own effect context ε₁ are both hidden
-- from the outer match, same situation as unfun-key's γ. Kept GENERIC
-- in its own input's type σ0 (rather than fixing it to Loss directly)
-- -- fixing it gets Agda's coverage checker stuck the same way
-- opE-absurd's own comment above describes (Loss, like UnitTy, is
-- gnd-headed too, so comparing it against an opE clause's own opaque
-- gnd(in′op) is undecidable) -- confirmed by direct experiment.
unthen-key : ∀ {Γ σ0 ε} → Γ ⊢ σ0 ! ε → Maybe (Σ Ty (λ σ → Σ EffCxt (λ ε₁ → Σ (ε₁ ⊆ᵉ ε) (λ sub → LC Γ σ ε₁))))
unthen-key (thenE {σ = σ} {ε₁ = ε₁} sub e g) = just (σ , ε₁ , sub , g)
unthen-key _                                 = nothing

-- glocalE's codomain shares its own σ with the hole's domain (so σ IS
-- visible via the outer match), but its own domain ε₁ (the hole's
-- ambient effect context) and the LC body's own ε₂ are both hidden.
unglocal-key : ∀ {Γ σ0 ε} → Γ ⊢ σ0 ! ε → Maybe (Σ EffCxt (λ ε₁ → Σ EffCxt (λ ε₂ → Σ (ε₂ ⊆ᵉ ε₁) (λ sub1 → Σ (ε₁ ⊆ᵉ ε) (λ sub2 → LC Γ σ0 ε₂)))))
unglocal-key (glocalE {ε₂ = ε₂} {ε₁ = ε₁} sub1 sub2 e g) = just (ε₁ , ε₂ , sub1 , sub2 , g)
unglocal-key _                                           = nothing

-- fst's argument is now a single (vpair-carrying) value rather than two
-- separately-recursed pieces glued by `pair`, so there's no more K-shape
-- to case-split on at all: `eq` itself, via unfst-arg's Σ-packing, already
-- pins down both K's hidden τ0 and its whole opE-headed payload in one
-- shot, leaving just a `plugK-op-not-val` call.
plugK-op-not-fstpair : ∀ {Γ εop ℓ ε σ0 τ0} {m : ℓ ∈ εop} {op : Op ℓ} {v : Val Γ (gnd (out op))}
                        (K : ContCxt Γ (gnd (in′ op)) εop (σ0 `× τ0) ε) {τ1} (v1 : Val Γ σ0) (w1 : Val Γ τ1)
                      → fst (val (vpair v1 w1)) ≡ fst (plugK K (opE m op (val v))) → ⊥
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

plugK-op-not-sndpair : ∀ {Γ εop ℓ ε σ0 τ0} {m : ℓ ∈ εop} {op : Op ℓ} {v : Val Γ (gnd (out op))}
                        (K : ContCxt Γ (gnd (in′ op)) εop (σ0 `× τ0) ε) {σ1} (v1 : Val Γ σ1) (w1 : Val Γ τ0)
                      → snd (val (vpair v1 w1)) ≡ snd (plugK K (opE m op (val v))) → ⊥
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
plugK-op-not-appvalL : ∀ {Γ εop ℓ ε σ0 τ0} {m : ℓ ∈ εop} {op : Op ℓ} {v : Val Γ (gnd (out op))}
                        (K : ContCxt Γ (gnd (in′ op)) εop (σ0 ⇒ τ0 ! ε) ε) {σ1} (e1 : (Γ , σ1) ⊢ τ0 ! ε) (v1 : Val Γ σ1) (e2 : Γ ⊢ σ0 ! ε)
                      → app (val (vabs e1)) (val v1) ≡ app (plugK K (opE m op (val v))) e2 → ⊥
plugK-op-not-appvalL (F∘ k (F-appL _))     e1 v1 e2 ()
plugK-op-not-appvalL (F∘ k (F-appR _))     e1 v1 e2 ()
plugK-op-not-appvalL (F∘ k F-fst)          e1 v1 e2 ()
plugK-op-not-appvalL (F∘ k F-snd)          e1 v1 e2 ()
plugK-op-not-appvalL (F∘ k (F-handleP _ _)) e1 v1 e2 ()
plugK-op-not-appvalL (S∘ k (S-handleB _ _))    e1 v1 e2 ()
plugK-op-not-appvalL (S∘ k (S-glocal _ _ _)) e1 v1 e2 ()
plugK-op-not-appvalL (S∘ k S-reset)          e1 v1 e2 ()

-- Same, for `app`'s argument-position (R3's `val vv` vs K's opaque
-- second component, when K sits under F-appR).
plugK-op-not-appvalR : ∀ {Γ εop ℓ ε σ0 τ0} {m : ℓ ∈ εop} {op : Op ℓ} {v : Val Γ (gnd (out op))}
                        (K : ContCxt Γ (gnd (in′ op)) εop σ0 ε) (v1 : Val Γ (σ0 ⇒ τ0 ! ε)) {σ1} (e1 : (Γ , σ1) ⊢ τ0 ! ε) (vv : Val Γ σ1)
                      → app (val (vabs e1)) (val vv) ≡ app (val v1) (plugK K (opE m op (val v))) → ⊥
plugK-op-not-appvalR ▫                     v1 e1 vv ()
plugK-op-not-appvalR (F∘ k (F-appL _))     v1 e1 vv ()
plugK-op-not-appvalR (F∘ k (F-appR _))     v1 e1 vv ()
plugK-op-not-appvalR (F∘ k F-fst)          v1 e1 vv ()
plugK-op-not-appvalR (F∘ k F-snd)          v1 e1 vv ()
plugK-op-not-appvalR (F∘ k (F-handleP _ _)) v1 e1 vv ()
plugK-op-not-appvalR (S∘ k (S-handleB _ _))    v1 e1 vv ()
plugK-op-not-appvalR (S∘ k (S-glocal _ _ _)) v1 e1 vv ()
plugK-op-not-appvalR (S∘ k S-reset)          v1 e1 vv ()

-- Same treatment, for `glocalE`: its own "natural effect" ε₁ (between
-- sub1's target and sub2's source) is hidden from its codomain σ, so
-- R8's independently-fresh ε₁ can't be compared via ordinary
-- injectivity. Proven directly by induction on K instead.
plugK-op-not-glocalval : ∀ {Γ εop ℓ σ0 ε2 ε1 ε} {m : ℓ ∈ εop} {op : Op ℓ} {v : Val Γ (gnd (out op))}
                          (K : ContCxt Γ (gnd (in′ op)) εop σ0 ε1) (sub1 : ε2 ⊆ᵉ ε1) (sub2 : ε1 ⊆ᵉ ε) (g1 : LC Γ σ0 ε2)
                          {ε2' ε1'} (sub1' : ε2' ⊆ᵉ ε1') (sub2' : ε1' ⊆ᵉ ε) (v1 : Val Γ σ0) {g1' : LC Γ σ0 ε2'}
                        → glocalE sub1' sub2' (val v1) g1' ≡ glocalE sub1 sub2 (plugK K (opE m op (val v))) g1 → ⊥
plugK-op-not-glocalval ▫                     sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k (F-fun _))      sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k (F-pairL _))    sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k (F-pairR _))    sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k F-fst)          sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k F-snd)          sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k (F-appL _))     sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k (F-appR _))     sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k (F-op _ _))     sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k F-loss)         sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (F∘ k (F-handleP _ _)) sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (S∘ k (S-handleB _ _))    sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (S∘ k (S-then _ _))     sub1 sub2 g1 sub1' sub2' v1 ()
plugK-op-not-glocalval (S∘ k S-reset)          sub1 sub2 g1 sub1' sub2' v1 ()

lossE-inj : ∀ {Γ ε} {e1 e2 : Γ ⊢ Loss ! ε} → lossE e1 ≡ lossE e2 → e1 ≡ e2
lossE-inj refl = refl

-- opE's own argument injectivity (its result type/witnesses are all
-- shared, homogeneous on both sides here, so this is ordinary
-- constructor injectivity, no dependent-index issue).
opE-arg-inj : ∀ {Γ ℓ ε} {m1 m2 : ℓ ∈ ε} {op : Op ℓ} {e1 e2 : Γ ⊢ gnd (out op) ! ε}
            → opE m1 op e1 ≡ opE m2 op e2 → e1 ≡ e2
opE-arg-inj refl = refl

handleE-arg-inj : ∀ {Γ ℓ par σ σ' ε} {h : Handler Γ ℓ par σ σ' ε} {vp : Val Γ (gnd par)} {e1 e2 : Γ ⊢ σ ! (ε ,ℓ ℓ)}
                → handleE h (val vp) e1 ≡ handleE h (val vp) e2 → e1 ≡ e2
handleE-arg-inj refl = refl

thenE-arg-inj : ∀ {Γ σ ε ε₁} {sub : ε₁ ⊆ᵉ ε} {e1 e2 : Γ ⊢ σ ! ε} {g1 : LC Γ σ ε₁} → thenE sub e1 g1 ≡ thenE sub e2 g1 → e1 ≡ e2
thenE-arg-inj refl = refl

-- Same hidden-index treatment as plugK-op-not-appvalL, for `thenE`: its
-- own "with" continuation g1 (and the ⊆ᵉ witness `sub`) are independent
-- of K's own (pinned) g0, so R7's independently-fresh `sub1,v1,e1` can't
-- be compared against K's own components via ordinary injectivity.
-- Proven directly by induction on K instead.
plugK-op-not-thenval : ∀ {Γ εop ℓ ε σ0 εg0} {m : ℓ ∈ εop} {op : Op ℓ} {v : Val Γ (gnd (out op))}
                        (K : ContCxt Γ (gnd (in′ op)) εop σ0 ε) (sub0 : εg0 ⊆ᵉ ε) (g0 : LC Γ σ0 εg0)
                        {σ1 εg1} (sub1 : εg1 ⊆ᵉ ε) (v1 : Val Γ σ1) {e1 : (Γ , σ1) ⊢ Loss ! εg1}
                      → thenE sub1 (val v1) (vabs e1) ≡ thenE sub0 (plugK K (opE m op (val v))) g0 → ⊥
plugK-op-not-thenval ▫                     sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k (F-fun _))      sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k (F-pairL _))    sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k (F-pairR _))    sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k F-fst)          sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k F-snd)          sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k (F-appL _))     sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k (F-appR _))     sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k (F-op _ _))     sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k F-loss)         sub0 g0 sub1 v1 ()
plugK-op-not-thenval (F∘ k (F-handleP _ _)) sub0 g0 sub1 v1 ()
plugK-op-not-thenval (S∘ k (S-handleB _ _))    sub0 g0 sub1 v1 ()
plugK-op-not-thenval (S∘ k (S-glocal _ _ _)) sub0 g0 sub1 v1 ()
plugK-op-not-thenval (S∘ k S-reset)          sub0 g0 sub1 v1 ()

glocalE-arg-inj : ∀ {Γ σ ε₂ ε₁ ε} {sub1 : ε₂ ⊆ᵉ ε₁} {sub2 : ε₁ ⊆ᵉ ε} {e1 e2 : Γ ⊢ σ ! ε₁} {g1 : LC Γ σ ε₂} → glocalE sub1 sub2 e1 g1 ≡ glocalE sub1 sub2 e2 g1 → e1 ≡ e2
glocalE-arg-inj refl = refl

resetE-inj : ∀ {Γ σ ε} {e1 e2 : Γ ⊢ σ ! ε} → resetE e1 ≡ resetE e2 → e1 ≡ e2
resetE-inj refl = refl

-- Rewrite a step derivation's own source along a propositional equality.
subst-src : ∀ {Γ σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} {e1 e2 e' : Γ ⊢ σ ! ε} {r : R}
          → e1 ≡ e2 → _⊢_-[_]→_ {sub = sub} g e1 r e' → _⊢_-[_]→_ {sub = sub} g e2 r e'
subst-src refl stp = stp

-- ---------------------------------------------------------------------
-- Rn-dispatch machinery for theorem-A4-1-op's own ▫/F-op cases below.
-- Both need to compare EVERY one of the 15 rules' own (varying)
-- conclusion type against a FIXED opaque target gnd(in′op) -- fixing the
-- target type directly (as plugK-op-not-* above safely does) does NOT
-- work here: Agda's coverage checker gets IRRECOVERABLY stuck trying to
-- decide e.g. UnitTy≟gnd(in′op) (R4's own conclusion) BEFORE ever
-- reaching a value-level comparison, since `in′` is abstract (confirmed
-- by direct experiment). agda_noparam's own opE sidestepped this by
-- carrying its σeq proof AS A CONSTRUCTOR ARGUMENT (keeping its own
-- result type σ genuinely free) -- agda_correctparam's opE no longer
-- does, so `opE-at` reintroduces that flexibility LOCALLY, via `subst`.
-- The cost: a `subst`-wrapped term is opaque to Agda's OWN automatic `()`
-- absurd-pattern check (confirmed by experiment: even an outright
-- constructor clash like lossE vs a subst-wrapped opE fails `()`
-- outright) -- so absurdity has to be derived MANUALLY below, via a
-- type-uniform (subst-transparent, proven by a dedicated commutation
-- lemma in each case) discriminator + cong, rather than relying on `()`.
opE-at : ∀ {Γ ℓ ε τ} (m : ℓ ∈ ε) (op : Op ℓ) (τeq : τ ≡ gnd (in′ op)) → Γ ⊢ gnd (out op) ! ε → Γ ⊢ τ ! ε
opE-at m op τeq e = subst (λ τ' → _ ⊢ τ' ! _) (sym τeq) (opE m op e)

-- isOpE/isOpE-subst: the Bool-valued (hence type-uniform, subst-
-- transparent) discriminator used to rule out all 14 non-matching
-- rules below, uniformly, via opE-absurd.
isOpE : ∀ {Γ σ ε} → Γ ⊢ σ ! ε → Bool
isOpE (opE _ _ _) = true
isOpE _         = false

isOpE-subst : ∀ {Γ ε τ1 τ2} (eq : τ1 ≡ τ2) (e : Γ ⊢ τ2 ! ε) → isOpE (subst (λ τ → Γ ⊢ τ ! ε) (sym eq) e) ≡ isOpE e
isOpE-subst refl e = refl

true≢false : true ≡ false → ⊥
true≢false ()

opE-absurd : ∀ {Γ σ ε ℓ} {m' : ℓ ∈ ε} {op' : Op ℓ} (τeq : σ ≡ gnd (in′ op')) (arg' : Γ ⊢ gnd (out op') ! ε) {e : Γ ⊢ σ ! ε}
           → isOpE e ≡ false → e ≡ opE-at m' op' τeq arg' → ⊥
opE-absurd {m' = m'} {op' = op'} τeq arg' neq eq =
  true≢false (trans (sym (trans (cong isOpE eq) (isOpE-subst τeq (opE m' op' arg')))) neq)

-- unOpE/unOpE-subst: the one MATCHING case (another F-op/opE call)
-- needs, instead, to recover op'''s own identity and inner argument.
-- Σ-packed exactly like unfst-arg/unhandle-param above, so that
-- pattern-matching the resulting `just`-equality directly as `refl`
-- (rather than manually splitting it via Σ-≡,≡←≡) unifies every
-- component -- op, its ∈-witness, and the inner argument -- AT ONCE,
-- confirmed by direct experiment to work through the same subst-
-- transparency issue as isOpE above (unOpE-subst is the commutation
-- lemma that makes this transparent).
unOpE : ∀ {Γ σ ε} → Γ ⊢ σ ! ε → Maybe (Σ (Σ Effect Op) (λ p → Γ ⊢ gnd (out (proj₂ p)) ! ε))
unOpE (opE {ℓ = ℓ} m op e) = just ((ℓ , op) , e)
unOpE _                    = nothing

unOpE-subst : ∀ {Γ ε τ1 τ2} (eq : τ1 ≡ τ2) (e : Γ ⊢ τ2 ! ε) → unOpE (subst (λ τ → Γ ⊢ τ ! ε) (sym eq) e) ≡ unOpE e
unOpE-subst refl e = refl

-- Discharges unOpE's own success case: given `packed` (unOpE applied to
-- both sides of the F-op-vs-F-op comparison, Σ-packed), rewrites a step
-- derivation's source from the ORIGINAL rule's own (op3-typed) source to
-- the TARGET's own (op2-typed) one -- in two stages, since packed's own
-- key/payload split needs one extra subst-∘-style bridge (subst-opOut)
-- to line the two different motives (unOpE's own Σ-indexed one vs the
-- simpler Ty-indexed one subst-src/subst-stp-σ use) up before subst-src
-- can apply. (Pattern-matching `packed` directly as `refl` also unifies
-- everything at once in isolation, but does not propagate reliably
-- through theorem-A4-1-op's own cross-referencing implicits in its
-- recursive call below -- confirmed by direct experiment -- so this
-- explicit route is used instead.)
subst-stp-σ : ∀ {Γ σ1 σ2 ε εg} {sub : εg ⊆ᵉ ε} (σeq : σ1 ≡ σ2) {gg : LC Γ σ1 εg} {e1 e1' : Γ ⊢ σ1 ! ε} {r : R}
            → _⊢_-[_]→_ {sub = sub} gg e1 r e1'
            → _⊢_-[_]→_ {sub = sub} (subst (λ σ → LC Γ σ εg) σeq gg) (subst (λ σ → Γ ⊢ σ ! ε) σeq e1) r (subst (λ σ → Γ ⊢ σ ! ε) σeq e1')
subst-stp-σ refl stp = stp

subst-opOut : ∀ {Γ ε} {p1 p2 : Σ Effect Op} (keyeq : p1 ≡ p2) (e : Γ ⊢ gnd (out (proj₂ p1)) ! ε)
            → subst (λ p → Γ ⊢ gnd (out (proj₂ p)) ! ε) keyeq e ≡ subst (λ τ → Γ ⊢ τ ! ε) (cong (λ p → gnd (out (proj₂ p))) keyeq) e
subst-opOut refl e = refl

unOpE-success : ∀ {Γ ε ℓ2 ℓ3} {op2 : Op ℓ2} {op3 : Op ℓ3} {arg2 : Γ ⊢ gnd (out op2) ! ε} {einner : Γ ⊢ gnd (out op3) ! ε}
                {εg} {sub : εg ⊆ᵉ ε} {g : LC Γ (gnd (out op3)) εg} {r : R} {e' : Γ ⊢ gnd (out op3) ! ε}
              → just ((ℓ3 , op3) , einner) ≡ just ((ℓ2 , op2) , arg2)
              → _⊢_-[_]→_ {sub = sub} g einner r e'
              → Σ (LC Γ (gnd (out op2)) εg) (λ g2 → Σ (Γ ⊢ (gnd (out op2)) ! ε) (λ e'2 → _⊢_-[_]→_ {sub = sub} g2 arg2 r e'2))
unOpE-success {einner = einner} just-eq stp =
  _ , _ , subst-src (trans (sym (subst-opOut keyeq einner)) payload-eq) (subst-stp-σ (cong (λ p → gnd (out (proj₂ p))) keyeq) stp)
  where
  packed = just-injective just-eq
  keyeq = proj₁ (Σ-≡,≡←≡ packed)
  payload-eq = proj₂ (Σ-≡,≡←≡ packed)

-- ---------------------------------------------------------------------
-- General-purpose shape-clash machinery, needed wherever a rule's OWN
-- conclusion (e.g. F-rule wrapping an F-op frame, whose own codomain
-- gnd(in′op) is opaque) is compared against a FIXED, concrete target
-- type (UnitTy for the F-loss K-shape case below, Loss for S-then's) --
-- same underlying issue as opE-absurd above (Agda's coverage checker
-- gets stuck comparing two gnd-headed-but-differently-payloaded types),
-- generalised here to work for ANY target constructor, not just opE,
-- via a full 12-way tag (one per _⊢_!_ constructor) rather than the
-- Bool isOpE used above.
data ExprTag : Set where
  tVal tFun tPair tFst tSnd tApp tOp tLoss tThen tGlocal tReset tHandle : ExprTag

exprTag : ∀ {Γ σ ε} → Γ ⊢ σ ! ε → ExprTag
exprTag (val _)         = tVal
exprTag (fun _ _)       = tFun
exprTag (pair _ _)      = tPair
exprTag (fst _)         = tFst
exprTag (snd _)         = tSnd
exprTag (app _ _)       = tApp
exprTag (opE _ _ _)     = tOp
exprTag (lossE _)       = tLoss
exprTag (thenE _ _ _)   = tThen
exprTag (glocalE _ _ _ _) = tGlocal
exprTag (resetE _)      = tReset
exprTag (handleE _ _ _) = tHandle

exprTag-subst : ∀ {Γ ε τ1 τ2} (eq : τ1 ≡ τ2) (e : Γ ⊢ τ2 ! ε) → exprTag (subst (λ τ → Γ ⊢ τ ! ε) (sym eq) e) ≡ exprTag e
exprTag-subst refl e = refl

-- Reintroduces, for an ARBITRARY target constructor's own shape Xty
-- (not just opE's gnd(in′op)), the same σeq-carrying flexibility
-- discussed above opE-at.
generic-at : ∀ {Γ ε τ Xty} (τeq : τ ≡ Xty) → Γ ⊢ Xty ! ε → Γ ⊢ τ ! ε
generic-at τeq X = subst (λ τ' → _ ⊢ τ' ! _) (sym τeq) X

generic-at-tag : ∀ {Γ ε τ Xty} (τeq : τ ≡ Xty) (X : Γ ⊢ Xty ! ε) → exprTag (generic-at τeq X) ≡ exprTag X
generic-at-tag refl X = refl

shape-absurd : ∀ {Γ σ ε Xty} (τeq : σ ≡ Xty) (X : Γ ⊢ Xty ! ε) {e : Γ ⊢ σ ! ε}
             → e ≡ generic-at τeq X → (exprTag e ≡ exprTag X → ⊥) → ⊥
shape-absurd τeq X eq neq = neq (trans (cong exprTag eq) (generic-at-tag τeq X))

-- Two-sided version, needed for R5-cont-unique below (below, BOTH sides
-- of the comparison are generic-at-wrapped, since NEITHER K1's nor K2's
-- own codomain can be allowed to unify DIRECTLY against the other's --
-- confirmed by direct experiment: even the K1=K2=▫ base case gets
-- Agda's coverage checker stuck if their codomains are compared
-- directly, since ContCxt's own HOLE type (σ,ε, e.g. gnd(in′op1) here)
-- is a PARAMETER (shared, unchanging, across a whole continuation), NOT
-- an index -- so it is NEVER "re-examined" while peeling frames, but
-- their shared CODOMAIN (R5's own σ) genuinely is, and comparing two
-- independently-opaque candidates for it is exactly opE-at's own
-- original problem, just on both sides at once here).
shape-absurd2 : ∀ {Γ σ ε Xty1 Xty2} (τeq1 : σ ≡ Xty1) (X1 : Γ ⊢ Xty1 ! ε) (τeq2 : σ ≡ Xty2) (X2 : Γ ⊢ Xty2 ! ε)
              → generic-at τeq1 X1 ≡ generic-at τeq2 X2 → (exprTag X1 ≡ exprTag X2 → ⊥) → ⊥
shape-absurd2 τeq1 X1 τeq2 X2 eq neq = neq (trans (sym (generic-at-tag τeq1 X1)) (trans (cong exprTag eq) (generic-at-tag τeq2 X2)))

-- Effect-generalizing variants, needed because ContCxt's own codomain
-- is a PAIR (Ty, EffCxt) that varies together -- unlike theorem-A4-1-
-- op's own use of generic-at, where only the Ty-index ever moved (the
-- ambient EffCxt was always shared/fixed there). Here, peeling S-
-- handleB/S-glocal off a ContCxt genuinely changes the outer EffCxt
-- too (they add/remove effect labels), so R5-cont-unique's own
-- induction needs both indices kept independently free per side.
generic-atE : ∀ {Γ τ Xty ε Xε} (τeq : τ ≡ Xty) (εeq : ε ≡ Xε) → Γ ⊢ Xty ! Xε → Γ ⊢ τ ! ε
generic-atE refl refl X = X

generic-atE-tag : ∀ {Γ τ Xty ε Xε} (τeq : τ ≡ Xty) (εeq : ε ≡ Xε) (X : Γ ⊢ Xty ! Xε) → exprTag (generic-atE τeq εeq X) ≡ exprTag X
generic-atE-tag refl refl X = refl

-- generic-atE-fst-cast/-snd-cast: bridges unfst-arg/unsnd-arg's own raw
-- `subst` (along the PROJECTED τ/σ motive) directly to generic-atE's
-- own shape, needed to feed go's own recursive call -- proven directly
-- via τeq's own refl-match (single-sided, safe, mirroring every other
-- commutation lemma above) rather than by trying to unfold generic-atE
-- itself (which, for an OPAQUE τeq/εeq, never reduces to a raw subst
-- form at all -- confirmed by direct experiment).
generic-atE-fst-cast : ∀ {Γ σ0 τ1 τ2 ε} (τeq : τ1 ≡ τ2) (e : Γ ⊢ (σ0 `× τ1) ! ε)
                      → generic-atE (sym (cong (λ τ → σ0 `× τ) τeq)) refl e ≡ subst (λ τ → Γ ⊢ (σ0 `× τ) ! ε) τeq e
generic-atE-fst-cast refl e = refl

generic-atE-snd-cast : ∀ {Γ τ0 σ1 σ2 ε} (σeq : σ1 ≡ σ2) (e : Γ ⊢ (σ1 `× τ0) ! ε)
                      → generic-atE (sym (cong (λ σ → σ `× τ0) σeq)) refl e ≡ subst (λ σ → Γ ⊢ (σ `× τ0) ! ε) σeq e
generic-atE-snd-cast refl e = refl

generic-atE-fst-cast2 : ∀ {Γ σ0 τ1 τ2 ε} (τeq : τ1 ≡ τ2) (e : Γ ⊢ (σ0 `× τ2) ! ε)
                       → generic-atE (cong (λ τ → σ0 `× τ) τeq) refl e ≡ subst (λ τ → Γ ⊢ (σ0 `× τ) ! ε) (sym τeq) e
generic-atE-fst-cast2 refl e = refl

generic-atE-snd-cast2 : ∀ {Γ τ0 σ1 σ2 ε} (σeq : σ1 ≡ σ2) (e : Γ ⊢ (σ2 `× τ0) ! ε)
                       → generic-atE (cong (λ σ → σ `× τ0) σeq) refl e ≡ subst (λ σ → Γ ⊢ (σ `× τ0) ! ε) (sym σeq) e
generic-atE-snd-cast2 refl e = refl

subst-sym-cancel : ∀ {A : Set} (P : A → Set) {a b : A} (eq : a ≡ b) (x : P a) → subst P (sym eq) (subst P eq x) ≡ x
subst-sym-cancel P refl x = refl

-- Single-sided version, used throughout R5-cont-unique's own induction
-- below (go's own clauses always pattern-match τeq1/εeq1 to refl in the
-- clause head -- safe, since resultTy/resultEff are go's own fresh
-- metas at that point, unconstrained except via τeq1/εeq1 themselves --
-- confirmed by direct experiment. This reduces `eq` to `X1 ≡ generic-
-- atE τeq2 εeq2 X2` with X1 fully concrete, sidestepping the need to
-- ever compare K1'/K2''s own codomains as TWO independent opaque
-- proofs at once).
shape-absurdE : ∀ {Γ σ ε Xty Xε} (τeq : σ ≡ Xty) (εeq : ε ≡ Xε) (X : Γ ⊢ Xty ! Xε) {e : Γ ⊢ σ ! ε}
              → e ≡ generic-atE τeq εeq X → (exprTag e ≡ exprTag X → ⊥) → ⊥
shape-absurdE τeq εeq X eq neq = neq (trans (cong exprTag eq) (generic-atE-tag τeq εeq X))

-- pack2: Σ-packages an expression's own (Ty, EffCxt, expression) triple
-- into ONE, CLOSED type, independent of any external σ/ε -- unlike a
-- direct `_≡_`/`_≅_` comparison of two K-shape-dependent expressions
-- (which gets Agda's unifier stuck deciding TYPE-level equality first,
-- e.g. gnd(in′op1) ≟ gnd(in′op2)), comparing two pack2-VALUES is an
-- ordinary, homogeneous `_≡_` -- Agda accepts refl on it via ordinary
-- constructor injectivity (confirmed by direct experiment: this
-- correctly recovers op1≡op2 even though `in′` is abstract, AS LONG AS
-- the two sides' own "rest" (the recursively-varying sub-expression)
-- is fully atomic on both sides -- e.g. both `val`-headed. When one or
-- both sides embed a further plugK-wrapped sub-continuation at the
-- point of comparison, pack2's own refl-match gets stuck too (plugK
-- isn't a constructor, so Agda can't peel through an unmatched k) --
-- confirmed by direct experiment -- so those cases instead peel ONE
-- matching outer constructor via ordinary injectivity (fun-inj2, pair-
-- inj1/2, opE-arg-inj, etc. -- ALL of which DO work through an
-- unmatched plugK-wrapped sub-term, since the OUTER constructor's own
-- injectivity doesn't require reducing its argument) and recurse.
pack2 : ∀ {Γ σ ε} → Γ ⊢ σ ! ε → Σ Ty (λ σ' → Σ EffCxt (λ ε' → Γ ⊢ σ' ! ε'))
pack2 {σ = σ} {ε = ε} e = σ , ε , e

pack2-substE : ∀ {Γ τ Xty ε Xε} (τeq : τ ≡ Xty) (εeq : ε ≡ Xε) (e : Γ ⊢ Xty ! Xε)
             → pack2 (generic-atE τeq εeq e) ≡ pack2 e
pack2-substE refl refl e = refl

-- unOpEShallow: like unOpE, but drops the argument entirely (keeping
-- only ℓ, op, the ambient EffCxt, and the ∈-witness, ALL Σ-packaged so
-- the codomain never mentions any external ε) -- needed for the tOp
-- cases (S1/S9), where the argument itself may be a further plugK-
-- wrapped sub-continuation (S9) that a FULL pack2/unOpE-style match
-- can't safely unify (see comment on pack2 above) -- unOpEShallow lets
-- us recover op-identity (and εop-identity) WITHOUT ever touching the
-- argument, homogeneously.
unOpEShallow : ∀ {Γ σ ε} → Γ ⊢ σ ! ε → Maybe (Σ Effect (λ ℓ' → Σ (Op ℓ') (λ op' → Σ EffCxt (λ ε' → ℓ' ∈ ε'))))
unOpEShallow (opE {ℓ = ℓ'} {ε = ε'} m' op' _) = just (ℓ' , op' , ε' , m')
unOpEShallow _                                = nothing

unOpEShallow-substE : ∀ {Γ τ Xty ε Xε} (τeq : τ ≡ Xty) (εeq : ε ≡ Xε) (e : Γ ⊢ Xty ! Xε)
                     → unOpEShallow (generic-atE τeq εeq e) ≡ unOpEShallow e
unOpEShallow-substE refl refl e = refl

-- generic-atK: the ContCxt analogue of generic-atE, casting along its
-- own "hole" (domain) parameters -- used to thread op1≡op2/εop1≡εop2
-- (established once, at go's own base case) upward through its
-- induction as ORDINARY `_≡_` facts, sidestepping the need to combine
-- heterogeneous ≅ values across recursive calls (confirmed by direct
-- experiment that lifting kA≅kB to (F∘ kA f)≅(F∘ kB f) directly, via
-- icong or similar, needs an index equality that isn't otherwise
-- available at that point -- generic-atK avoids ever needing it: go's
-- own recursion works entirely in `_≡_` until R5-cont-unique's own
-- top-level wrapper converts to `_≅_` exactly once, at the very end).
generic-atK : ∀ {Γ dty ddty deff ddeff σ ε} (dtyeq : dty ≡ ddty) (deffeq : deff ≡ ddeff) → ContCxt Γ ddty ddeff σ ε → ContCxt Γ dty deff σ ε
generic-atK refl refl K = K

generic-atK-≅ : ∀ {Γ dty ddty deff ddeff σ ε} (dtyeq : dty ≡ ddty) (deffeq : deff ≡ ddeff) (K : ContCxt Γ ddty ddeff σ ε)
              → generic-atK dtyeq deffeq K ≅ K
generic-atK-≅ refl refl K = ≅-refl

-- generic-atK2: casts BOTH the domain (dty,deff) AND codomain (σ,ε)
-- parameters at once -- needed for go's own TYPE DECLARATION (as
-- opposed to its individual clause bodies), since σ1/σ2 (K1'/K2''s own
-- codomains) are only unified per-clause (once both are pattern-
-- matched to a matching shape) -- generically, before any clause is
-- picked, they're independent. Within a same-shape clause matching
-- τeq1,εeq1 to refl, the codomain-cast arguments (trans (sym τeq1)
-- τeq2, trans (sym εeq1) εeq2) become τeq2,εeq2 themselves; even where
-- those stay opaque (S1,S1's own pack2-mediated match, which doesn't
-- pattern-match τeq2/εeq2 directly), their type becomes `X ≡ X` post-
-- unification, so Axiom K makes them definitionally refl anyway.
generic-atK2 : ∀ {Γ dty ddty deff ddeff σ dσ ε dε} (dtyeq : dty ≡ ddty) (deffeq : deff ≡ ddeff) (σeq : σ ≡ dσ) (εeq : ε ≡ dε)
             → ContCxt Γ ddty ddeff dσ dε → ContCxt Γ dty deff σ ε
generic-atK2 refl refl refl refl K = K

generic-atK2-≅ : ∀ {Γ dty ddty deff ddeff σ dσ ε dε} (dtyeq : dty ≡ ddty) (deffeq : deff ≡ ddeff) (σeq : σ ≡ dσ) (εeq : ε ≡ dε) (K : ContCxt Γ ddty ddeff dσ dε)
               → generic-atK2 dtyeq deffeq σeq εeq K ≅ K
generic-atK2-≅ refl refl refl refl K = ≅-refl

generic-atK2-refl-refl : ∀ {Γ dty ddty deff ddeff σ ε} (dtyeq : dty ≡ ddty) (deffeq : deff ≡ ddeff) (K : ContCxt Γ ddty ddeff σ ε)
                        → generic-atK2 dtyeq deffeq refl refl K ≡ generic-atK dtyeq deffeq K
generic-atK2-refl-refl refl refl K = refl

generic-atK-F∘ : ∀ {Γ dty ddty deff ddeff α β σ ε} (dtyeq : dty ≡ ddty) (deffeq : deff ≡ ddeff) (k : ContCxt Γ ddty ddeff α β) (f : Frame Γ α β σ ε)
                → generic-atK dtyeq deffeq (F∘ k f) ≡ F∘ (generic-atK dtyeq deffeq k) f
generic-atK-F∘ refl refl k f = refl

generic-atK-S∘ : ∀ {Γ dty ddty deff ddeff α β σ ε} (dtyeq : dty ≡ ddty) (deffeq : deff ≡ ddeff) (k : ContCxt Γ ddty ddeff α β) (s : SFrame Γ α β σ ε)
                → generic-atK dtyeq deffeq (S∘ k s) ≡ S∘ (generic-atK dtyeq deffeq k) s
generic-atK-S∘ refl refl k s = refl

-- wrapF∘/wrapS∘: the "wrap-up" step of go's own peel-and-recurse
-- pattern -- given the recursive call's own result (kB, cast down to
-- kA's domain, equals kA), lifts this ONE F∘/S∘ layer, producing
-- exactly the shape go's own type declaration expects at the OUTER
-- level (generic-atK2 ... refl refl (F∘/S∘ kB f/s) ≡ F∘/S∘ kA f/s).
wrapF∘ : ∀ {Γ dty ddty deff ddeff α β σ ε} (X : dty ≡ ddty) (Y : deff ≡ ddeff)
       {kA : ContCxt Γ dty deff α β} {kB : ContCxt Γ ddty ddeff α β} (f : Frame Γ α β σ ε)
     → generic-atK X Y kB ≡ kA
     → generic-atK2 X Y refl refl (F∘ kB f) ≡ F∘ kA f
wrapF∘ X Y {kB = kB} f keq = trans (generic-atK2-refl-refl X Y (F∘ kB f)) (trans (generic-atK-F∘ X Y kB f) (cong (λ k → F∘ k f) keq))

wrapS∘ : ∀ {Γ dty ddty deff ddeff α β σ ε} (X : dty ≡ ddty) (Y : deff ≡ ddeff)
       {kA : ContCxt Γ dty deff α β} {kB : ContCxt Γ ddty ddeff α β} (s : SFrame Γ α β σ ε)
     → generic-atK X Y kB ≡ kA
     → generic-atK2 X Y refl refl (S∘ kB s) ≡ S∘ kA s
wrapS∘ X Y {kB = kB} s keq = trans (generic-atK2-refl-refl X Y (S∘ kB s)) (trans (generic-atK-S∘ X Y kB s) (cong (λ k → S∘ k s) keq))

-- Bridges an all-refl recursive go call's own return shape
-- (generic-atK2 X Y refl refl kB ≡ kA, since go's own return type
-- literally mentions generic-atK2 even when the extra σ/ε casts
-- collapse to refl syntactically -- trans (sym refl) refl reduces to
-- refl computationally, but generic-atK2 itself stays stuck on the
-- still-opaque domain casts X,Y) down to wrapF∘/wrapS∘'s own expected
-- generic-atK (2-param) shape.
generic-atK2-refl-refl-inv : ∀ {Γ dty ddty deff ddeff σ ε} (X : dty ≡ ddty) (Y : deff ≡ ddeff) {kA : ContCxt Γ dty deff σ ε} {kB : ContCxt Γ ddty ddeff σ ε}
                            → generic-atK2 X Y refl refl kB ≡ kA → generic-atK X Y kB ≡ kA
generic-atK2-refl-refl-inv X Y {kB = kB} keq = trans (sym (generic-atK2-refl-refl X Y kB)) keq

-- F-fst/F-snd's own wrap-up: unlike every other Frame, their hidden
-- second/first component isn't pinned by the outer refl refl refl refl
-- match at all (F-fst/F-snd forget it entirely from their own
-- codomain), so the recursive call's own comparison of kA,kB genuinely
-- needs an extra codomain-level cast (τeq) that the plain wrapF∘ above
-- doesn't carry -- but since F-fst/F-snd discard that component in
-- their OWN codomain too, the cast becomes irrelevant again exactly
-- one layer up, which is what these two lemmas capture.
generic-atK-fst-forget : ∀ {Γ dty ddty deff ddeff ρ τ1 τ2 ε} (X : dty ≡ ddty) (Y : deff ≡ ddeff) (τeq : τ1 ≡ τ2) (k : ContCxt Γ ddty ddeff (ρ `× τ2) ε)
                        → generic-atK X Y (F∘ k F-fst) ≡ F∘ (generic-atK2 X Y (cong (λ τ → ρ `× τ) τeq) refl k) F-fst
generic-atK-fst-forget refl refl refl k = refl

wrapF∘-fst : ∀ {Γ dty ddty deff ddeff ρ τ1 τ2 ε} (X : dty ≡ ddty) (Y : deff ≡ ddeff) (τeq : τ1 ≡ τ2)
           {kA : ContCxt Γ dty deff (ρ `× τ1) ε} {kB : ContCxt Γ ddty ddeff (ρ `× τ2) ε}
         → generic-atK2 X Y (cong (λ τ → ρ `× τ) τeq) refl kB ≡ kA
         → generic-atK2 X Y refl refl (F∘ kB F-fst) ≡ F∘ kA F-fst
wrapF∘-fst X Y τeq {kB = kB} keq =
  trans (generic-atK2-refl-refl X Y (F∘ kB F-fst)) (trans (generic-atK-fst-forget X Y τeq kB) (cong (λ k → F∘ k F-fst) keq))

generic-atK-snd-forget : ∀ {Γ dty ddty deff ddeff τ0 σ1 σ2 ε} (X : dty ≡ ddty) (Y : deff ≡ ddeff) (σeq : σ1 ≡ σ2) (k : ContCxt Γ ddty ddeff (σ2 `× τ0) ε)
                        → generic-atK X Y (F∘ k F-snd) ≡ F∘ (generic-atK2 X Y (cong (λ σ → σ `× τ0) σeq) refl k) F-snd
generic-atK-snd-forget refl refl refl k = refl

wrapF∘-snd : ∀ {Γ dty ddty deff ddeff τ0 σ1 σ2 ε} (X : dty ≡ ddty) (Y : deff ≡ ddeff) (σeq : σ1 ≡ σ2)
           {kA : ContCxt Γ dty deff (σ1 `× τ0) ε} {kB : ContCxt Γ ddty ddeff (σ2 `× τ0) ε}
         → generic-atK2 X Y (cong (λ σ → σ `× τ0) σeq) refl kB ≡ kA
         → generic-atK2 X Y refl refl (F∘ kB F-snd) ≡ F∘ kA F-snd
wrapF∘-snd X Y σeq {kB = kB} keq =
  trans (generic-atK2-refl-refl X Y (F∘ kB F-snd)) (trans (generic-atK-snd-forget X Y σeq kB) (cong (λ k → F∘ k F-snd) keq))

-- unLossE/unLossE-subst: lossE's own argument extraction, needed by
-- BOTH R4 (whose own conclusion is ALSO lossE-headed, matching the F-
-- loss K-shape case's own target shape below) and that same case's own
-- F-rule/F-loss success sub-case. Unlike opE, lossE's argument type
-- doesn't depend on any "key" (its domain is always Loss), so this
-- needs no Σ-packing at all -- a direct Maybe extraction suffices.
unLossE : ∀ {Γ σ ε} → Γ ⊢ σ ! ε → Maybe (Γ ⊢ Loss ! ε)
unLossE (lossE X) = just X
unLossE _         = nothing

unLossE-subst : ∀ {Γ ε τ1 τ2} (eq : τ1 ≡ τ2) (e : Γ ⊢ τ2 ! ε) → unLossE (subst (λ τ → Γ ⊢ τ ! ε) (sym eq) e) ≡ unLossE e
unLossE-subst refl e = refl

-- unThenE/unThenE-subst: same idea as unLossE, for thenE -- since we
-- only ever need the WHOLE (unwrapped) thenE application back (never
-- its individual sub/e/g1 components separately: R7 feeds it straight
-- into plugK-op-not-thenval, S2 pattern-matches it directly as refl,
-- both below), no Σ-packing of thenE's own hidden σ/ε₁ is needed at
-- all -- unlike unOpE, which had to recover op's own identity
-- separately for its own recursive theorem-A4-1-op call.
unThenE : ∀ {Γ σ ε} → Γ ⊢ σ ! ε → Maybe (Γ ⊢ Loss ! ε)
unThenE e@(thenE _ _ _) = just e
unThenE _               = nothing

unThenE-subst : ∀ {Γ ε τ1 τ2} (eq : τ1 ≡ τ2) (e : Γ ⊢ τ2 ! ε) → unThenE (subst (λ τ → Γ ⊢ τ ! ε) (sym eq) e) ≡ unThenE e
unThenE-subst refl e = refl

-- ---------------------------------------------------------------------
-- Forward-declared: theorem-A4-1-op-handleB below recurses back into
-- theorem-A4-1-op (S1's own continuation), while theorem-A4-1-op's own
-- S-handleB clause (further down) delegates to theorem-A4-1-op-handleB
-- -- genuine mutual recursion, so only the type signature is needed here.
theorem-A4-1-op : ∀ {Γ σ ε εg εop ℓ} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} (m : ℓ ∈ εop) (op : Op ℓ) (v : Val Γ (gnd (out op)))
                   (K : ContCxt Γ (gnd (in′ op)) εop σ ε) → ¬ Handles K ℓ
                 → ∀ {e' : Γ ⊢ σ ! ε} {r : R} → _⊢_-[_]→_ {sub = sub} g (plugK K (opE m op (val v))) r e' → ⊥

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
opLabelOf (opE {ℓ = ℓ} m op e)     = opLabelOf e <∣> just ℓ
opLabelOf (lossE e)                = opLabelOf e
opLabelOf (thenE sub e g)          = opLabelOf e
opLabelOf (glocalE sub1 sub2 e g)  = opLabelOf e
opLabelOf (resetE e)               = opLabelOf e
opLabelOf (handleE h e1 e2)        = opLabelOf e1 <∣> opLabelOf e2

opLabelOf-plugK : ∀ {Γ εop ℓ ε τ} {m : ℓ ∈ εop} {op : Op ℓ} {v : Val Γ (gnd (out op))}
                  (K : ContCxt Γ (gnd (in′ op)) εop τ ε) → opLabelOf (plugK K (opE m op (val v))) ≡ just ℓ
opLabelOf-plugK ▫                        = refl
opLabelOf-plugK (F∘ k (F-fun _))         = opLabelOf-plugK k
opLabelOf-plugK (F∘ k (F-pairL e₂))      = cong (_<∣> opLabelOf e₂) (opLabelOf-plugK k)
opLabelOf-plugK (F∘ k (F-pairR _))       = opLabelOf-plugK k
opLabelOf-plugK (F∘ k F-fst)             = opLabelOf-plugK k
opLabelOf-plugK (F∘ k F-snd)             = opLabelOf-plugK k
opLabelOf-plugK (F∘ k (F-appL e₂))       = cong (_<∣> opLabelOf e₂) (opLabelOf-plugK k)
opLabelOf-plugK (F∘ k (F-appR _))        = opLabelOf-plugK k
opLabelOf-plugK (F∘ k (F-op _ _))        = cong (_<∣> just _) (opLabelOf-plugK k)
opLabelOf-plugK (F∘ k F-loss)            = opLabelOf-plugK k
opLabelOf-plugK (F∘ k (F-handleP _ b))   = cong (_<∣> opLabelOf b) (opLabelOf-plugK k)
opLabelOf-plugK (S∘ k (S-handleB _ _))   = opLabelOf-plugK k
opLabelOf-plugK (S∘ k (S-then _ _))      = opLabelOf-plugK k
opLabelOf-plugK (S∘ k (S-glocal _ _ _))  = opLabelOf-plugK k
opLabelOf-plugK (S∘ k S-reset)           = opLabelOf-plugK k

-- Extracts a handleE's OWN handler label directly (no recursion into
-- either hole) -- fixed codomain again, so it works across the two
-- independently-fresh handlers (ours vs R5's own) without needing them
-- to already coincide.
handlerLabelOf : ∀ {Γ σ ε} → Γ ⊢ σ ! ε → Maybe Effect
handlerLabelOf (handleE {ℓ = ℓ} h e1 e2) = just ℓ
handlerLabelOf _                        = nothing

-- Same hidden-index treatment as plugK-op-not-appvalL/thenval, for
-- `handleE`: its own hole type (the handler's domain σh2) is hidden
-- from its codomain σh', so R6's independently-fresh h2,v2 can't be
-- compared against our own (pinned) h,K via ordinary injectivity. Here
-- K sits under the BODY hole (S-handleB, param already evaluated), so
-- the parameter position is a fixed value vp on the left and h's own
-- (independently-fresh) v2p on the right.
plugK-op-not-handleval : ∀ {Γ εop ℓop ε ℓh σh σh'} {m : ℓop ∈ εop} {op : Op ℓop} {v : Val Γ (gnd (out op))}
                          (K : ContCxt Γ (gnd (in′ op)) εop σh (ε ,ℓ ℓh)) {parh} (h : Handler Γ ℓh parh σh σh' ε) (vp : Val Γ (gnd parh))
                          {ℓ2 σh2 par2} (h2 : Handler Γ ℓ2 par2 σh2 σh' ε) (v2p : Val Γ (gnd par2)) (v2 : Val Γ σh2)
                        → handleE h2 (val v2p) (val v2) ≡ handleE h (val vp) (plugK K (opE m op (val v))) → ⊥
plugK-op-not-handleval ▫                        h vp h2 v2p v2 ()
plugK-op-not-handleval (F∘ k (F-fun _))         h vp h2 v2p v2 ()
plugK-op-not-handleval (F∘ k (F-pairL _))       h vp h2 v2p v2 ()
plugK-op-not-handleval (F∘ k (F-pairR _))       h vp h2 v2p v2 ()
plugK-op-not-handleval (F∘ k F-fst)             h vp h2 v2p v2 ()
plugK-op-not-handleval (F∘ k F-snd)             h vp h2 v2p v2 ()
plugK-op-not-handleval (F∘ k (F-appL _))        h vp h2 v2p v2 ()
plugK-op-not-handleval (F∘ k (F-appR _))        h vp h2 v2p v2 ()
plugK-op-not-handleval (F∘ k (F-op _ _))        h vp h2 v2p v2 ()
plugK-op-not-handleval (F∘ k F-loss)            h vp h2 v2p v2 ()
plugK-op-not-handleval (F∘ k (F-handleP _ _))   h vp h2 v2p v2 ()
plugK-op-not-handleval (S∘ k (S-handleB _ _))   h vp h2 v2p v2 ()
plugK-op-not-handleval (S∘ k (S-then _ _))      h vp h2 v2p v2 ()
plugK-op-not-handleval (S∘ k (S-glocal _ _ _))  h vp h2 v2p v2 ()
plugK-op-not-handleval (S∘ k S-reset)           h vp h2 v2p v2 ()

-- Same Σ-packing treatment as unfst-arg/unsnd-arg, for `handleE`'s own
-- hidden PARAMETER type (par is exposed in neither handleE's own
-- codomain σ' nor, independently, on the two sides being compared below
-- -- R6/S1/R5 each bind their own fresh par2, needing recovery before
-- plugK-op-not-val can even be stated).
unhandle-param : ∀ {Γ σ0 ε} → Γ ⊢ σ0 ! ε → Maybe (Σ GTy (λ par → Γ ⊢ gnd par ! ε))
unhandle-param (handleE {par = par} h e1 e2) = just (par , e1)
unhandle-param _                             = nothing

subst-val-gnd : ∀ {Γ par1 par2 ε} (eq : par1 ≡ par2) (w : Val Γ (gnd par1))
              → subst (λ par → Γ ⊢ gnd par ! ε) eq (val w) ≡ val (subst (λ par → Val Γ (gnd par)) eq w)
subst-val-gnd refl w = refl

-- Used for the F-handleP case of theorem-A4-1-op below: any rule whose
-- own conclusion is handleE-headed with an ALREADY-EVALUATED (val v1')
-- parameter -- R6, S1, R5 -- clashes with F-handleP's own hole sitting
-- in exactly that parameter position (filled, there, by the necessarily
-- non-val plugK K (opE ...)).
plugK-op-not-handleparam : ∀ {Γ εop ℓ ε ℓh0 par0 σh0 σh0'} {m : ℓ ∈ εop} {op : Op ℓ} {v : Val Γ (gnd (out op))}
                            (K : ContCxt Γ (gnd (in′ op)) εop (gnd par0) ε) (h : Handler Γ ℓh0 par0 σh0 σh0' ε) (b : Γ ⊢ σh0 ! (ε ,ℓ ℓh0))
                            {ℓ2 par2 σh2} (h2 : Handler Γ ℓ2 par2 σh2 σh0' ε) (v1' : Val Γ (gnd par2)) (body2 : Γ ⊢ σh2 ! (ε ,ℓ ℓ2))
                          → handleE h2 (val v1') body2 ≡ handleE h (plugK K (opE m op (val v))) b → ⊥
plugK-op-not-handleparam K h b h2 v1' body2 eq =
  plugK-op-not-val K (subst (λ par → Val _ (gnd par)) pareq v1') (sym (trans (sym (subst-val-gnd pareq v1')) veq))
  where
  packed = just-injective (cong unhandle-param eq)
  pareq = proj₁ (Σ-≡,≡←≡ packed)
  veq   = proj₂ (Σ-≡,≡←≡ packed)

-- ---------------------------------------------------------------------
-- Theorem A.4.1, value case. Moved ahead of theorem-A4-1-op-handleB
-- (unlike agda_noparam) since the new F-handleP case below now needs it
-- (parameter-free handlers never had a parameter-position hole to step
-- under, so agda_noparam's own theorem-A4-1-op-handleB never called it).
-- ---------------------------------------------------------------------

theorem-A4-1-val : ∀ {Γ σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} {v : Val Γ σ} {e' : Γ ⊢ σ ! ε} {r : R}
                  → _⊢_-[_]→_ {sub = sub} g (val v) r e' → ⊥
theorem-A4-1-val stp = helper stp refl
  where
    helper : ∀ {Γ σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} {v : Val Γ σ} {e e' : Γ ⊢ σ ! ε} {r : R}
           → _⊢_-[_]→_ {sub = sub} g e r e' → e ≡ val v → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()

    helper (R2-pair v w)             ()
    helper (R3 e v)                 ()
    helper (R4 r)                   ()
    helper (R6 h v1 v2)             ()
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h v stp)         ()
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h v1 m op v2 k nh) ()
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub (F-pairL _) stp) ()
    helper (F-rule sub (F-pairR _) stp) ()
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()
    helper (F-rule sub (F-op _ _)  stp) ()
    helper (F-rule sub F-loss      stp) ()
    helper (F-rule sub (F-handleP h b) stp) ()

theorem-A4-1-op-handleB : ∀ {Γ σh par σh' ε εg εop ℓ ℓh} {g : LC Γ σh' εg} (m : ℓ ∈ εop) (op : Op ℓ) (v : Val Γ (gnd (out op)))
                           (k : ContCxt Γ (gnd (in′ op)) εop σh (ε ,ℓ ℓh)) (h : Handler Γ ℓh par σh σh' ε) (vp : Val Γ (gnd par))
                         → ¬ Handles (S∘ k (S-handleB h vp)) ℓ
                         → ∀ {e' : Γ ⊢ σh' ! ε} {r : R} {sub : εg ⊆ᵉ ε} → _⊢_-[_]→_ {sub = sub} g (handleE h (val vp) (plugK k (opE m op (val v)))) r e' → ⊥
theorem-A4-1-op-handleB {Γ} {σh' = σh'} {ε = ε} {ℓ = ℓ} {ℓh = ℓh} m op v k h vp nh stp = helper stp refl
  where
    nh-eq : ¬ (ℓ ≡ ℓh)
    nh-eq ℓ≡ℓh = nh (inj₁ ℓ≡ℓh)
    nh-k : ¬ Handles k ℓ
    nh-k hk = nh (inj₂ hk)

    helper : ∀ {εg'} {g' : LC Γ σh' εg'} {e e' : Γ ⊢ σh' ! ε} {r : R} {sub : εg' ⊆ᵉ ε}
           → _⊢_-[_]→_ {sub = sub} g' e r e' → e ≡ handleE h (val vp) (plugK k (opE m op (val v))) → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()

    helper (R2-pair v w)             ()
    helper (R3 e v)                 ()
    helper (R4 r)                   ()
    helper (R6 h2 v1' v2)           eq = plugK-op-not-handleval k h vp h2 v1' v2 eq
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h2 v1' stp)      refl = theorem-A4-1-op m op v k nh-k stp
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 {ℓ = ℓ5} sub h5 v15 m5 op5 v25 k5 nh5) eq =
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
    helper (F-rule sub (F-op _ _)  stp) ()
    helper (F-rule sub F-loss      stp) ()
    -- (F-handleP h' b): F-rule's own frame here steps the SAME parameter
    -- position our target's own S-handleB already fixed to `val vp`.
    -- Extract einner≡val(...) via unhandle-param's Σ-packing (h'/par'
    -- are independently fresh, mirroring the fstpair/sndpair fix), then
    -- theorem-A4-1-val directly refutes stp once its own source is
    -- rewritten to that value.
    helper (F-rule sub (F-handleP h' b) stp) eq =
      theorem-A4-1-val (subst-src (sym e-eq) stp)
      where
      packed = just-injective (cong unhandle-param (sym eq))
      pareq = proj₁ (Σ-≡,≡←≡ packed)
      veq   = proj₂ (Σ-≡,≡←≡ packed)
      e-eq : val (subst (λ par'' → Val _ (gnd par'')) pareq vp) ≡ _
      e-eq = trans (sym (subst-val-gnd pareq vp)) veq

-- ---------------------------------------------------------------------
-- Theorem A.4.1, operation case.
-- ---------------------------------------------------------------------

-- K = ▫. `helper` below re-quantifies m,op,v (and g) as its OWN fresh
-- implicits, with e's own type kept a genuinely FREE σ' (tied to
-- gnd(in′op') only via the separate τeq' proof, exactly mirroring
-- agda_noparam's own σeq-carrying opE) -- fixing e's type directly to
-- gnd(in′op') instead gets Agda's coverage checker IRRECOVERABLY stuck
-- on rules whose own conclusion is ALSO gnd-headed but with a different,
-- concrete GTy payload (R4/UnitTy, R7&S2/Loss) -- see opE-at's own
-- comment above. Every absurd case below goes through opE-absurd
-- uniformly (bare () does not work through opE-at's subst-wrapping,
-- confirmed by direct experiment); the one matching case (F-op) goes
-- through unOpE, whose Σ-packed `just`-equality, pattern-matched
-- directly as `refl` (rather than manually split via Σ-≡,≡←≡), unifies
-- op''≡op' and e''≡val v' at once, exactly as a plain refl-match would
-- for two directly-comparable opE applications.
theorem-A4-1-op {Γ} m op v ▫ nh stp = helper {m' = m} {op' = op} {τeq' = refl} {v' = v} stp refl
  where
    helper : ∀ {ℓ' εop' σ'} {m' : ℓ' ∈ εop'} {op' : Op ℓ'} {τeq' : σ' ≡ gnd (in′ op')} {v' : Val Γ (gnd (out op'))}
               {εg'} {sub : εg' ⊆ᵉ εop'} {g' : LC Γ σ' εg'} {e e' : Γ ⊢ σ' ! εop'} {r : R}
           → _⊢_-[_]→_ {sub = sub} g' e r e' → e ≡ opE-at m' op' τeq' (val v') → ⊥
    helper (R1 f x)                 eq = opE-absurd _ _ refl eq
    helper (R2-fst v w)             eq = opE-absurd _ _ refl eq
    helper (R2-snd v w)             eq = opE-absurd _ _ refl eq
    helper (R2-pair v w)            eq = opE-absurd _ _ refl eq
    helper (R3 e v)                 eq = opE-absurd _ _ refl eq
    helper (R4 r)                   eq = opE-absurd _ _ refl eq
    helper (R6 h v1 v2)             eq = opE-absurd _ _ refl eq
    helper (R7 sub v e)             eq = opE-absurd _ _ refl eq
    helper (R8 sub1 sub2 v g1)      eq = opE-absurd _ _ refl eq
    helper (R9 v)                   eq = opE-absurd _ _ refl eq
    helper (S1 sub h v stp)         eq = opE-absurd _ _ refl eq
    helper (S2 sub g1 stp)          eq = opE-absurd _ _ refl eq
    helper (S3 sub1 sub2 g1 stp)    eq = opE-absurd _ _ refl eq
    helper (S4 stp)                 eq = opE-absurd _ _ refl eq
    helper (R5 sub h v1 m op v2 k nh) eq = opE-absurd _ _ refl eq
    helper (F-rule sub (F-fun _)   stp) eq = opE-absurd _ _ refl eq
    helper (F-rule sub (F-pairL _) stp) eq = opE-absurd _ _ refl eq
    helper (F-rule sub (F-pairR _) stp) eq = opE-absurd _ _ refl eq
    helper (F-rule sub F-fst       stp) eq = opE-absurd _ _ refl eq
    helper (F-rule sub F-snd       stp) eq = opE-absurd _ _ refl eq
    helper (F-rule sub (F-appL _)  stp) eq = opE-absurd _ _ refl eq
    helper (F-rule sub (F-appR _)  stp) eq = opE-absurd _ _ refl eq
    helper {τeq' = τeq'} {v' = v'} (F-rule sub (F-op m'' op'') stp) eq =
      theorem-A4-1-val (proj₂ (proj₂ (unOpE-success (trans (cong unOpE eq) (unOpE-subst τeq' (opE _ _ (val v')))) stp)))
    helper (F-rule sub F-loss      stp) eq = opE-absurd _ _ refl eq
    helper (F-rule sub (F-handleP h b) stp) eq = opE-absurd _ _ refl eq

-- K = F∘ k (F-fun pf). Outer wrapper is `fun`, whose type doesn't depend
-- on any opaque `in′`/`out` computation, so m,op,v,k are simply closed
-- over here (no re-quantification needed) -- only opE-headed targets
-- (the F-op sub-case below) need that treatment.
theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k (F-fun {δ = δ0} pf)) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {sub : εg' ⊆ᵉ ε} {g' : LC Γ (gnd δ0) εg'} {e e' : Γ ⊢ gnd δ0 ! ε} {r : R}
           → _⊢_-[_]→_ {sub = sub} g' e r e' → e ≡ fun pf (plugK k (opE m op (val v))) → ⊥
    helper (R1 f x)                 eq   = plugK-op-not-funval k pf f x eq
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()
    helper (R3 e v)                 ()
    helper (R4 r)                   ()
    helper (R6 h v1 v2)             ()
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h v stp)         ()
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h v1 m op v2 k nh) ()
    helper (F-rule sub (F-fun pf'') stp) refl = theorem-A4-1-op m op v k nh stp
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()
    helper (F-rule sub (F-op _ _)  stp) ()
    helper (F-rule sub F-loss      stp) ()
    helper (F-rule sub (F-handleP h b) stp) ()

theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k (F-pairL {σ = σ0} {τ = τ0} e₂)) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {sub : εg' ⊆ᵉ ε} {g' : LC Γ (σ0 `× τ0) εg'} {e e' : Γ ⊢ (σ0 `× τ0) ! ε} {r : R}
           → _⊢_-[_]→_ {sub = sub} g' e r e' → e ≡ pair (plugK k (opE m op (val v))) e₂ → ⊥
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()
    helper (R2-pair v w)             eq = plugK-op-not-val k v (sym (pair-inj1 eq))
    helper (R3 e v)                 ()
    helper (R6 h v1 v2)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h v stp)         ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h v1 m op v2 k nh) ()
    helper (F-rule sub (F-pairL _) stp) eq = theorem-A4-1-op m op v k nh (subst-src (pair-inj1 eq) stp)
    helper (F-rule sub (F-pairR v1') stp) eq = plugK-op-not-val k v1' (sym (pair-inj1 eq))
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()

theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k (F-pairR {σ = σ0} {τ = τ0} v1)) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {sub : εg' ⊆ᵉ ε} {g' : LC Γ (σ0 `× τ0) εg'} {e e' : Γ ⊢ (σ0 `× τ0) ! ε} {r : R}
           → _⊢_-[_]→_ {sub = sub} g' e r e' → e ≡ pair (val v1) (plugK k (opE m op (val v))) → ⊥
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()
    helper (R2-pair v w)             eq = plugK-op-not-val k w (sym (pair-inj2 eq))
    helper (R3 e v)                 ()
    helper (R6 h v1' v2)            ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h v stp)         ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h v1' m op v2 k nh) ()
    helper (F-rule sub (F-pairL _) stp) eq = theorem-A4-1-val (subst-src (pair-inj1 eq) stp)
    helper (F-rule sub (F-pairR _) stp) eq = theorem-A4-1-op m op v k nh (subst-src (pair-inj2 eq) stp)
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()

theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k (F-fst {σ = σ0} {τ = τ0})) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {sub : εg' ⊆ᵉ ε} {g' : LC Γ σ0 εg'} {e e' : Γ ⊢ σ0 ! ε} {r : R}
           → _⊢_-[_]→_ {sub = sub} g' e r e' → e ≡ fst (plugK k (opE m op (val v))) → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             eq = plugK-op-not-fstpair k v w eq
    helper (R2-snd v w)             ()

    helper (R2-pair v w)             ()
    helper (R3 e v)                 ()
    helper (R4 r)                   ()
    helper (R6 h v1 v2)             ()
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h v stp)         ()
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h v1 m op v2 k nh) ()
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub (F-pairL _) stp) ()
    helper (F-rule sub (F-pairR _) stp) ()
    helper (F-rule sub F-fst       stp) refl = theorem-A4-1-op m op v k nh stp
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()
    helper (F-rule sub (F-op _ _)  stp) ()
    helper (F-rule sub F-loss      stp) ()
    helper (F-rule sub (F-handleP h b) stp) ()

theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k (F-snd {σ = σ0} {τ = τ0})) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {sub : εg' ⊆ᵉ ε} {g' : LC Γ τ0 εg'} {e e' : Γ ⊢ τ0 ! ε} {r : R}
           → _⊢_-[_]→_ {sub = sub} g' e r e' → e ≡ snd (plugK k (opE m op (val v))) → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             eq = plugK-op-not-sndpair k v w eq
    helper (R3 e v)                 ()
    helper (R4 r)                   ()
    helper (R6 h v1 v2)             ()
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h v stp)         ()
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h v1 m op v2 k nh) ()
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub (F-pairL _) stp) ()
    helper (F-rule sub (F-pairR _) stp) ()
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) refl = theorem-A4-1-op m op v k nh stp
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()
    helper (F-rule sub (F-op _ _)  stp) ()
    helper (F-rule sub F-loss      stp) ()
    helper (F-rule sub (F-handleP h b) stp) ()

theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k (F-appL {σ = σ0} {τ = τ0} e₂)) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {sub : εg' ⊆ᵉ ε} {g' : LC Γ τ0 εg'} {e e' : Γ ⊢ τ0 ! ε} {r : R}
           → _⊢_-[_]→_ {sub = sub} g' e r e' → e ≡ app (plugK k (opE m op (val v))) e₂ → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()

    helper (R2-pair v w)             ()
    helper (R3 e v')                eq = plugK-op-not-appvalL k e v' e₂ eq
    helper (R4 r)                   ()
    helper (R6 h v1 v2)             ()
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h v stp)         ()
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h v1 m op v2 k nh) ()
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
    helper (F-rule sub (F-op _ _)  stp) ()
    helper (F-rule sub F-loss      stp) ()
    helper (F-rule sub (F-handleP h b) stp) ()

theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k (F-appR {σ = σ0} {τ = τ0} v1)) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {sub : εg' ⊆ᵉ ε} {g' : LC Γ τ0 εg'} {e e' : Γ ⊢ τ0 ! ε} {r : R}
           → _⊢_-[_]→_ {sub = sub} g' e r e' → e ≡ app (val v1) (plugK k (opE m op (val v))) → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()

    helper (R2-pair v w)             ()
    helper (R3 e v')                eq = plugK-op-not-appvalR k v1 e v' eq
    helper (R4 r)                   ()
    helper (R6 h v1' v2)            ()
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h v stp)         ()
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h v1' m op v2 k nh) ()
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub (F-pairL _) stp) ()
    helper (F-rule sub (F-pairR _) stp) ()
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) refl = theorem-A4-1-val stp
    helper (F-rule sub (F-appR _)  stp) refl = theorem-A4-1-op m op v k nh stp
    helper (F-rule sub (F-op _ _)  stp) ()
    helper (F-rule sub F-loss      stp) ()
    helper (F-rule sub (F-handleP h b) stp) ()

-- K = F∘ k (F-op m'' op''). Same treatment as the ▫ case above for the
-- same reason (e's own type kept genuinely free, σ2, to avoid Agda's
-- coverage checker getting stuck on R4/R7/S2) -- but UNLIKE the ▫ case,
-- m'',op'' (and m,op,v,k) here are theorem-A4-1-op's OWN, already-
-- CLOSED-OVER values from this very clause's own K-shape pattern, not
-- re-quantified fresh: this case's own success branch makes a
-- RECURSIVE theorem-A4-1-op call using the SPECIFIC, fixed `k`, so the
-- target needs to be expressed concretely in terms of it -- a freshly
-- re-quantified "generic arg2" (which worked fine for the ▫ case, since
-- theorem-A4-1-val there doesn't care what its own source specifically
-- is) cannot, since `helper` is itself a separately-typed function that
-- must type-check for ANY value its own implicits allow, and theorem-
-- A4-1-op's fixed k cannot produce a term whose source is an arbitrary,
-- unconstrained arg2 (confirmed by direct experiment: Agda reports a
-- genuine, unresolvable index mismatch, not a display artifact).
theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k (F-op m'' op'')) nh stp = helper {τeq2 = refl} stp refl
  where
    helper : ∀ {σ2} {τeq2 : σ2 ≡ gnd (in′ op'')}
               {εg'} {sub : εg' ⊆ᵉ ε} {g' : LC Γ σ2 εg'} {e e' : Γ ⊢ σ2 ! ε} {r : R}
           → _⊢_-[_]→_ {sub = sub} g' e r e' → e ≡ opE-at m'' op'' τeq2 (plugK k (opE m op (val v))) → ⊥
    helper (R1 f x)                 eq = opE-absurd _ _ refl eq
    helper (R2-fst v w)             eq = opE-absurd _ _ refl eq
    helper (R2-snd v w)             eq = opE-absurd _ _ refl eq
    helper (R2-pair v w)            eq = opE-absurd _ _ refl eq
    helper (R3 e v)                 eq = opE-absurd _ _ refl eq
    helper (R4 r)                   eq = opE-absurd _ _ refl eq
    helper (R6 h v1 v2)             eq = opE-absurd _ _ refl eq
    helper (R7 sub v e)             eq = opE-absurd _ _ refl eq
    helper (R8 sub1 sub2 v g1)      eq = opE-absurd _ _ refl eq
    helper (R9 v)                   eq = opE-absurd _ _ refl eq
    helper (S1 sub h v stp)         eq = opE-absurd _ _ refl eq
    helper (S2 sub g1 stp)          eq = opE-absurd _ _ refl eq
    helper (S3 sub1 sub2 g1 stp)    eq = opE-absurd _ _ refl eq
    helper (S4 stp)                 eq = opE-absurd _ _ refl eq
    helper (R5 sub h v1 m op v2 k nh) eq = opE-absurd _ _ refl eq
    helper (F-rule sub (F-fun _)   stp) eq = opE-absurd _ _ refl eq
    helper (F-rule sub (F-pairL _) stp) eq = opE-absurd _ _ refl eq
    helper (F-rule sub (F-pairR _) stp) eq = opE-absurd _ _ refl eq
    helper (F-rule sub F-fst       stp) eq = opE-absurd _ _ refl eq
    helper (F-rule sub F-snd       stp) eq = opE-absurd _ _ refl eq
    helper (F-rule sub (F-appL _)  stp) eq = opE-absurd _ _ refl eq
    helper (F-rule sub (F-appR _)  stp) eq = opE-absurd _ _ refl eq
    helper {τeq2 = τeq2} (F-rule sub (F-op m3 op3) stp) eq
      with unOpE-success (trans (cong unOpE eq) (unOpE-subst τeq2 (opE m'' op'' (plugK k (opE m op (val v)))))) stp
    ... | _ , _ , stp2 = theorem-A4-1-op m op v k nh stp2
    helper (F-rule sub F-loss      stp) eq = opE-absurd _ _ refl eq
    helper (F-rule sub (F-handleP h b) stp) eq = opE-absurd _ _ refl eq

-- K = F∘ k F-loss. Same treatment as the F-op case above and for the
-- same reason: F-loss's OWN K-shape isn't the problem (its codomain,
-- UnitTy, is already concrete) -- the problem is the SAME F-rule/(F-op _
-- _) sub-case reappearing INSIDE this helper's own F-rule enumeration
-- (F-op's own codomain, gnd(in′op), is opaque, so comparing it against
-- ANY fixed target -- UnitTy here -- gets Agda's coverage checker stuck
-- exactly as with R4/R7/S2 earlier). So e's own type is kept genuinely
-- free (σ2) here too, tied to UnitTy only via τeq2, with EVERY case
-- (not just F-op) routed through shape-absurd/generic-at accordingly --
-- bare () does not work through generic-at's subst-wrapping for ANY of
-- them, confirmed by direct experiment, matching opE-at's own case
-- above exactly.
theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k F-loss) nh stp = helper {τeq2 = refl} stp refl
  where
    -- Bound OUTSIDE helper's own clauses, deliberately: several Rn
    -- patterns below (R2-fst/R2-snd/R3/R8/R9/S1, and R5 which rebinds
    -- m/op/k too) introduce their OWN fresh v/m/op/k, which would
    -- otherwise SHADOW theorem-A4-1-op's own closed-over v/m/op/k if
    -- this were written inline in each clause (confirmed by direct
    -- experiment: R2-fst's own v was silently substituted in for
    -- theorem-A4-1-op's own v, producing a bogus type error).
    target : Γ ⊢ UnitTy ! ε
    target = lossE (plugK k (opE m op (val v)))
    helper : ∀ {σ2} {τeq2 : σ2 ≡ UnitTy} {εg'} {sub : εg' ⊆ᵉ ε} {g' : LC Γ σ2 εg'} {e e' : Γ ⊢ σ2 ! ε} {r : R}
           → _⊢_-[_]→_ {sub = sub} g' e r e' → e ≡ generic-at τeq2 (target) → ⊥
    helper {τeq2 = τeq2} (R1 f x)                 eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (R2-fst v w)             eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (R2-snd v w)             eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (R3 e v)                 eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (R4 r)     eq = plugK-op-not-val k (vgnd r) (sym packed)
      where packed = just-injective (trans (cong unLossE eq) (unLossE-subst τeq2 (target)))
    helper {τeq2 = τeq2} (R6 h v1 v2)             eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (R8 sub1 sub2 v g1)      eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (R9 v)                   eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (S1 sub h v stp)         eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (S3 sub1 sub2 g1 stp)    eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (S4 stp)                 eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (R5 sub h v1 m op v2 k nh) eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (F-rule sub (F-fun _)   stp) eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (F-rule sub F-fst       stp) eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (F-rule sub F-snd       stp) eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (F-rule sub (F-appL _)  stp) eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (F-rule sub (F-appR _)  stp) eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (F-rule sub (F-op _ _)  stp) eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (F-rule sub F-loss stp) eq =
      theorem-A4-1-op m op v k nh (subst-src packed stp)
      where packed = just-injective (trans (cong unLossE eq) (unLossE-subst τeq2 (target)))
    helper {τeq2 = τeq2} (F-rule sub (F-handleP h b) stp) eq = shape-absurd τeq2 (target) eq (λ ())

-- K = F∘ k (F-handleP h b): a brand-new case, absent from agda_noparam
-- (parameter-free handlers had no parameter-position hole at all).
-- F-handleP's own hole sits in handleE's FIRST argument (the parameter),
-- with the body b closed over unevaluated -- exactly mirroring F-appL's
-- own treatment of app's function-position hole, just one level up
-- (handleE h _ b instead of app _ e₂). Any rule whose own conclusion is
-- handleE-headed with an ALREADY-EVALUATED parameter (R6, S1, R5) clashes
-- via plugK-op-not-handleparam; (F-rule sub (F-handleP h' b') stp) (the
-- matching congruence layer) is the one genuine success case; every
-- other rule's own conclusion has a different top-level former entirely.
theorem-A4-1-op {Γ} {ε = ε} m op v (F∘ k (F-handleP {par = par0} {σ' = σ0'} h b)) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {sub : εg' ⊆ᵉ ε} {g' : LC Γ σ0' εg'} {e e' : Γ ⊢ σ0' ! ε} {r : R}
           → _⊢_-[_]→_ {sub = sub} g' e r e' → e ≡ handleE h (plugK k (opE m op (val v))) b → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()
    helper (R2-pair v w)            ()
    helper (R3 e v)                 ()
    helper (R4 r)                   ()
    helper (R6 h2 v1' v2)           eq = plugK-op-not-handleparam k h b h2 v1' (val v2) eq
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v)                   ()
    helper (S1 sub h2 v1' stp)      eq = plugK-op-not-handleparam k h b h2 v1' _ eq
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 ()
    helper (R5 sub h2 v1' m2 op2 v2 k2 nh2) eq = plugK-op-not-handleparam k h b h2 v1' _ eq
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub (F-pairL _) stp) ()
    helper (F-rule sub (F-pairR _) stp) ()
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()
    helper (F-rule sub (F-op _ _)  stp) ()
    helper (F-rule sub F-loss      stp) ()
    helper (F-rule sub (F-handleP h2 b2) stp) refl = theorem-A4-1-op m op v k nh stp

-- K = S∘ k (S-handleB h vp): delegates wholesale to
-- theorem-A4-1-op-handleB (see comment above it, and above
-- opLabelOf/handlerLabelOf).
theorem-A4-1-op m op v (S∘ k (S-handleB h vp)) nh stp = theorem-A4-1-op-handleB m op v k h vp nh stp

-- K = S∘ k (S-then sub g0). Same underlying issue and fix as F-loss's
-- own case above (F-rule/(F-op _ _) getting stuck against a fixed
-- target), transplanted to a thenE-headed target -- e's own type is
-- kept genuinely free (σ2) here too. Note this REOPENS several cases
-- that used to be excludable outright under the old, FIXED-Loss target
-- (R2-pair/F-pairL/F-pairR via a provably-different type FORMER; R4/F-
-- loss via unit≠loss, both concrete GTy constructors, decidably
-- distinct) -- with σ2 free, Agda's coverage checker can no longer rule
-- these out at the type level either, so they need an explicit
-- shape-absurd case each, same as everything else here.
theorem-A4-1-op {Γ} {ε = ε} m op v (S∘ k (S-then sub g0)) nh stp = helper {τeq2 = refl} stp refl
  where
    -- Bound OUTSIDE helper's own clauses -- same shadowing hazard as
    -- F-loss's own case above (R5 here ALSO rebinds sub/m/op/k, and S1
    -- rebinds sub, so writing this inline per-clause would silently
    -- pick up the WRONG, locally-bound variable in several cases).
    target : Γ ⊢ Loss ! ε
    target = thenE sub (plugK k (opE m op (val v))) g0
    helper : ∀ {σ2} {τeq2 : σ2 ≡ Loss} {εg'} {subg' : εg' ⊆ᵉ ε} {g' : LC Γ σ2 εg'} {e e' : Γ ⊢ σ2 ! ε} {r : R}
           → _⊢_-[_]→_ {sub = subg'} g' e r e' → e ≡ generic-at τeq2 target → ⊥
    helper {τeq2 = τeq2} (R1 f x)                 eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (R2-pair v w)            eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (R2-fst v w)             eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (R2-snd v w)             eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (R3 e v)                 eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (R4 r)                   eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (R6 h v1 v2)             eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (R7 sub' v' e') eq =
      plugK-op-not-thenval k sub g0 sub' v' (just-injective (trans (cong unThenE eq) (unThenE-subst τeq2 (target))))
    helper {τeq2 = τeq2} (R8 sub1 sub2 v g1)      eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (R9 v)                   eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (S1 sub h v stp)         eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (S2 sub' g1 stp)  eq
      with just-injective (trans (cong unThenE eq) (unThenE-subst τeq2 (target)))
    ... | refl = theorem-A4-1-op m op v k nh stp
    helper {τeq2 = τeq2} (S3 sub1 sub2 g1 stp)    eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (S4 stp)                 eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (R5 sub h v1 m op v2 k nh) eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (F-rule sub (F-fun _)   stp) eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (F-rule sub (F-pairL _) stp) eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (F-rule sub (F-pairR _) stp) eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (F-rule sub F-fst       stp) eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (F-rule sub F-snd       stp) eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (F-rule sub (F-appL _)  stp) eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (F-rule sub (F-appR _)  stp) eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (F-rule sub (F-op _ _)  stp) eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (F-rule sub F-loss      stp) eq = shape-absurd τeq2 (target) eq (λ ())
    helper {τeq2 = τeq2} (F-rule sub (F-handleP h b) stp) eq = shape-absurd τeq2 (target) eq (λ ())

theorem-A4-1-op {Γ} {σ = σ'} {ε = ε} m op v (S∘ k (S-glocal sub1 sub2 g0)) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {subg' : εg' ⊆ᵉ ε} {g' : LC Γ σ' εg'} {e e' : Γ ⊢ σ' ! ε} {r : R}
           → _⊢_-[_]→_ {sub = subg'} g' e r e' → e ≡ glocalE sub1 sub2 (plugK k (opE m op (val v))) g0 → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()

    helper (R2-pair v w)             ()
    helper (R3 e v)                 ()
    helper (R4 r)                   ()
    helper (R6 h v1 v2)             ()
    helper (R7 sub v e)             ()
    helper (R8 sub1' sub2' v' g1)   eq = plugK-op-not-glocalval k sub1 sub2 g0 sub1' sub2' v' eq
    helper (R9 v)                   ()
    helper (S1 sub h v stp)         ()
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1' sub2' g1 stp)  refl = theorem-A4-1-op m op v k nh stp
    helper (S4 stp)                 ()
    helper (R5 sub h v1 m op v2 k nh) ()
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub (F-pairL _) stp) ()
    helper (F-rule sub (F-pairR _) stp) ()
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()
    helper (F-rule sub (F-op _ _)  stp) ()
    helper (F-rule sub F-loss      stp) ()
    helper (F-rule sub (F-handleP h b) stp) ()

theorem-A4-1-op {Γ} {σ = σ'} {ε = ε} m op v (S∘ k S-reset) nh stp = helper stp refl
  where
    helper : ∀ {εg'} {subg' : εg' ⊆ᵉ ε} {g' : LC Γ σ' εg'} {e e' : Γ ⊢ σ' ! ε} {r : R}
           → _⊢_-[_]→_ {sub = subg'} g' e r e' → e ≡ resetE (plugK k (opE m op (val v))) → ⊥
    helper (R1 f x)                 ()
    helper (R2-fst v w)             ()
    helper (R2-snd v w)             ()

    helper (R2-pair v w)             ()
    helper (R3 e v)                 ()
    helper (R4 r)                   ()
    helper (R6 h v1 v2)             ()
    helper (R7 sub v e)             ()
    helper (R8 sub1 sub2 v g1)      ()
    helper (R9 v')                  eq = plugK-op-not-val k v' (sym (resetE-inj eq))
    helper (S1 sub h v stp)         ()
    helper (S2 sub g1 stp)          ()
    helper (S3 sub1 sub2 g1 stp)    ()
    helper (S4 stp)                 refl = theorem-A4-1-op m op v k nh stp
    helper (R5 sub h v1 m op v2 k nh) ()
    helper (F-rule sub (F-fun _)   stp) ()
    helper (F-rule sub (F-pairL _) stp) ()
    helper (F-rule sub (F-pairR _) stp) ()
    helper (F-rule sub F-fst       stp) ()
    helper (F-rule sub F-snd       stp) ()
    helper (F-rule sub (F-appL _)  stp) ()
    helper (F-rule sub (F-appR _)  stp) ()
    helper (F-rule sub (F-op _ _)  stp) ()
    helper (F-rule sub F-loss      stp) ()
    helper (F-rule sub (F-handleP h b) stp) ()

-- ---------------------------------------------------------------------
-- Theorem A.4.1, combined.
-- ---------------------------------------------------------------------

theorem-A4-1 : ∀ {Γ σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} {e e' : Γ ⊢ σ ! ε} {r : R}
             → Terminal e → _⊢_-[_]→_ {sub = sub} g e r e' → ⊥
theorem-A4-1 (terminalVal v)          stp = theorem-A4-1-val stp
theorem-A4-1 (terminalOp m op v K nh) stp = theorem-A4-1-op m op v K nh stp

-- ---------------------------------------------------------------------
-- R5-cont-unique: the one genuinely new lemma theorem-A4-2 needs beyond
-- what theorem-A4-1 already built. R5 dispatches to whichever operation
-- call is innermost-and-unhandled inside its own K; determinism's R5-
-- vs-R5 case needs that this choice is UNIQUE -- given two (K,op,m,v2)
-- triples whose plugK-wrapped forms coincide, and NEITHER K handles its
-- own op's label, the triples themselves coincide.
--
-- Note ℓ is SHARED here (not separately quantified per side): R5's own
-- `m : ℓ ∈ εop`/`op : Op ℓ` sit at the SAME ℓ as the ambient handler h
-- (R5 fires when a further-out handler for h's own ℓ is needed), so by
-- the time theorem-A4-2's own R5-vs-R5 case reaches this lemma, ℓ is
-- already pinned by h1≡h2 (ordinary handleE-arg-inj-style injectivity,
-- no opacity involved -- h is a direct argument, not buried inside a
-- plugK application). Only op's OWN identity is what genuinely needs
-- recovering here.
--
-- Proof sketch (not yet carried out below -- this is the formulation):
-- induction on K1, case-split on K2 within each shape.
--   • K1 = K2 = ▫: both sides reduce DEFINITIONALLY to a direct,
--     unwrapped opE application (no subst-wrapping at all, unlike
--     opE-at's own situation in theorem-A4-1) -- op1,m1,v2-1 vs
--     op2,m2,v2-2 should unify via a single `refl` pattern-match on the
--     hypothesis directly, the same mechanism confirmed to work for
--     opE-vs-opE comparisons throughout theorem-A4-1 (e.g. unOpE-
--     success's own `packed | refl` step) -- genuinely the easy case.
--   • K1 = ▫, K2 = F∘k2 f2 (or S∘k2 s2) and vice versa: need
--     `val v2-1 ≠ plugK k2 (opE m2 op2 (val v2-2))` when f2 = F-op
--     (via opE-arg-inj + the EXISTING plugK-op-not-val), or an outright
--     shape clash otherwise (opE vs fun/pair/fst/snd/app/lossE/
--     handleE/thenE/glocalE/resetE) -- EASY when the colliding
--     constructor's own codomain is free (F-fun's gnd δ, F-fst's σ,
--     etc.), but reproduces theorem-A4-1's own STUCK issue whenever it
--     is concrete (F-loss/UnitTy, any S-then-rooted branch/Loss) --
--     same fix, shape-absurd/generic-at, expected to carry over
--     directly.
--   • K1 = F∘k1 f1, K2 = F∘k2 f2 (both non-empty, same top-level
--     family F∘ or S∘): need f1's own "family" (which of the 10 Frame/
--     4 SFrame constructors) to match f2's, via the SAME shape
--     discrimination as above, THEN recurse via the inductive
--     hypothesis on k1,k2 once f1≡f2 is established (reusing weaken1F/
--     weaken1K-style reasoning is NOT needed here, unlike F-rule's own
--     construction -- K1/K2 are compared directly, not rewritten).
--
-- The output is packaged as a flat conjunction (rather than nested Σ)
-- since `_≅_`'s own inhabitation ALREADY forces the underlying type
-- indices (εop1≡εop2 from m1≅m2, the codomain gnd(in′op1)≡gnd(in′op2)
-- from K1≅K2) as a consequence, mirroring theorem-A4-2's own top-level
-- statement -- no need to state those separately.
R5-cont-unique :
  ∀ {Γ σ ε ℓ} {εop1 εop2} {op1 op2 : Op ℓ}
    {m1 : ℓ ∈ εop1} {m2 : ℓ ∈ εop2}
    {v2-1 : Val Γ (gnd (out op1))} {v2-2 : Val Γ (gnd (out op2))}
    (K1 : ContCxt Γ (gnd (in′ op1)) εop1 σ (ε ,ℓ ℓ))
    (K2 : ContCxt Γ (gnd (in′ op2)) εop2 σ (ε ,ℓ ℓ))
  → ¬ Handles K1 ℓ → ¬ Handles K2 ℓ
  → plugK K1 (opE m1 op1 (val v2-1)) ≡ plugK K2 (opE m2 op2 (val v2-2))
  → op1 ≡ op2 × K1 ≅ K2 × m1 ≅ m2 × v2-1 ≅ v2-2
R5-cont-unique {Γ} {σ} {ε} {ℓ} {εop1} {εop2} {op1} {op2} {m1} {m2} {v2-1} {v2-2} K1 K2 nh1 nh2 eq = final
  where
    -- go's own return type threads op1≡op2/εop1≡εop2 as ORDINARY,
    -- explicit `_≡_` facts (rather than folding straight into K1'≅K2'),
    -- letting the induction cast K2' down to K1's own (op1,εop1)-typed
    -- "hole" via generic-atK and compare HOMOGENEOUSLY at every level --
    -- confirmed by direct experiment that lifting a recursively-obtained
    -- kA≅kB straight to (F∘ kA f)≅(F∘ kB f) needs an index equality
    -- that isn't otherwise available; this sidesteps that entirely,
    -- only converting to `_≅_` once, here, at the very top.
    go : ∀ {resultTy resultEff σ1 β1 σ2 β2}
           (K1' : ContCxt Γ (gnd (in′ op1)) εop1 σ1 β1) (τeq1 : resultTy ≡ σ1) (εeq1 : resultEff ≡ β1)
           (K2' : ContCxt Γ (gnd (in′ op2)) εop2 σ2 β2) (τeq2 : resultTy ≡ σ2) (εeq2 : resultEff ≡ β2)
        → ¬ Handles K1' ℓ → ¬ Handles K2' ℓ
        → generic-atE τeq1 εeq1 (plugK K1' (opE m1 op1 (val v2-1))) ≡ generic-atE τeq2 εeq2 (plugK K2' (opE m2 op2 (val v2-2)))
        → Σ (op1 ≡ op2) (λ opeq → Σ (εop1 ≡ εop2) (λ εopeq →
            generic-atK2 (cong (λ o → gnd (in′ o)) opeq) εopeq (trans (sym τeq1) τeq2) (trans (sym εeq1) εeq2) K2' ≡ K1' × m1 ≅ m2 × v2-1 ≅ v2-2))
    go (▫) refl refl (▫) τeq2 εeq2 nh1 nh2 eq
      with trans (cong pack2 eq) (pack2-substE τeq2 εeq2 (opE m2 op2 (val v2-2)))
    ... | refl with τeq2 | εeq2
    ...   | refl | refl = refl , refl , refl , ≅-refl , ≅-refl
    go (▫) refl refl (F∘ kB (F-fun pfB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (▫) refl refl (F∘ kB (F-pairL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (▫) refl refl (F∘ kB (F-pairR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (▫) refl refl (F∘ kB F-fst) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (▫) refl refl (F∘ kB F-snd) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (▫) refl refl (F∘ kB (F-appL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (▫) refl refl (F∘ kB (F-appR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (▫) refl refl (F∘ kB (F-op mB opB)) τeq2 εeq2 nh1 nh2 eq
      with just-injective (trans (cong unOpEShallow eq) (unOpEShallow-substE τeq2 εeq2 (opE mB opB (plugK kB (opE m2 op2 (val v2-2))))))
    ... | refl
      with τeq2 | εeq2
    ...   | refl | refl = ⊥-elim (plugK-op-not-val kB v2-1 (sym (opE-arg-inj eq)))
    go (▫) refl refl (F∘ kB F-loss) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (▫) refl refl (F∘ kB (F-handleP hB bB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (▫) refl refl (S∘ kB (S-handleB hB vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (▫) refl refl (S∘ kB (S-then subB gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (▫) refl refl (S∘ kB (S-glocal sub1B sub2B gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (▫) refl refl (S∘ kB S-reset) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-fun pfA)) refl refl (▫) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-fun pfA)) refl refl (F∘ kB (F-fun pfB)) refl refl nh1 nh2 eq
      with Σ-≡,≡←≡ (just-injective (cong unfun-key eq))
    ... | (γAeq , pfEq)
      with γAeq | pfEq
    ...   | refl | refl
      with go kA refl refl kB refl refl nh1 nh2 (fun-inj2 eq)
    ...     | (opeq , εopeq , keq , meq , veq) =
      opeq , εopeq , wrapF∘ (cong (λ o → gnd (in′ o)) opeq) εopeq (F-fun pfA) (generic-atK2-refl-refl-inv (cong (λ o → gnd (in′ o)) opeq) εopeq keq) , meq , veq
    go (F∘ kA (F-fun pfA)) refl refl (F∘ kB (F-pairL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-fun pfA)) refl refl (F∘ kB (F-pairR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-fun pfA)) refl refl (F∘ kB F-fst) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-fun pfA)) refl refl (F∘ kB F-snd) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-fun pfA)) refl refl (F∘ kB (F-appL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-fun pfA)) refl refl (F∘ kB (F-appR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-fun pfA)) refl refl (F∘ kB (F-op mB opB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-fun pfA)) refl refl (F∘ kB F-loss) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-fun pfA)) refl refl (F∘ kB (F-handleP hB bB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-fun pfA)) refl refl (S∘ kB (S-handleB hB vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-fun pfA)) refl refl (S∘ kB (S-then subB gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-fun pfA)) refl refl (S∘ kB (S-glocal sub1B sub2B gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-fun pfA)) refl refl (S∘ kB S-reset) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairL e2A)) refl refl (▫) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairL e2A)) refl refl (F∘ kB (F-fun pfB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairL e2A)) refl refl (F∘ kB (F-pairL e2B)) refl refl nh1 nh2 eq
      with pair-inj2 eq
    ... | refl
      with go kA refl refl kB refl refl nh1 nh2 (pair-inj1 eq)
    ... | (opeq , εopeq , keq , meq , veq) =
      opeq , εopeq , wrapF∘ (cong (λ o → gnd (in′ o)) opeq) εopeq (F-pairL e2A) (generic-atK2-refl-refl-inv (cong (λ o → gnd (in′ o)) opeq) εopeq keq) , meq , veq
    go (F∘ kA (F-pairL e2A)) refl refl (F∘ kB (F-pairR vB)) refl refl nh1 nh2 eq = ⊥-elim (plugK-op-not-val kA vB (pair-inj1 eq))
    go (F∘ kA (F-pairL e2A)) refl refl (F∘ kB F-fst) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairL e2A)) refl refl (F∘ kB F-snd) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairL e2A)) refl refl (F∘ kB (F-appL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairL e2A)) refl refl (F∘ kB (F-appR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairL e2A)) refl refl (F∘ kB (F-op mB opB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairL e2A)) refl refl (F∘ kB F-loss) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairL e2A)) refl refl (F∘ kB (F-handleP hB bB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairL e2A)) refl refl (S∘ kB (S-handleB hB vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairL e2A)) refl refl (S∘ kB (S-then subB gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairL e2A)) refl refl (S∘ kB (S-glocal sub1B sub2B gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairL e2A)) refl refl (S∘ kB S-reset) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairR vA)) refl refl (▫) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairR vA)) refl refl (F∘ kB (F-fun pfB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairR vA)) refl refl (F∘ kB (F-pairL e2B)) refl refl nh1 nh2 eq = ⊥-elim (plugK-op-not-val kB vA (sym (pair-inj1 eq)))
    go (F∘ kA (F-pairR vA)) refl refl (F∘ kB (F-pairR vB)) refl refl nh1 nh2 eq
      with val-inj (pair-inj1 eq)
    ... | refl
      with go kA refl refl kB refl refl nh1 nh2 (pair-inj2 eq)
    ... | (opeq , εopeq , keq , meq , veq) =
      opeq , εopeq , wrapF∘ (cong (λ o → gnd (in′ o)) opeq) εopeq (F-pairR vA) (generic-atK2-refl-refl-inv (cong (λ o → gnd (in′ o)) opeq) εopeq keq) , meq , veq
    go (F∘ kA (F-pairR vA)) refl refl (F∘ kB F-fst) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairR vA)) refl refl (F∘ kB F-snd) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairR vA)) refl refl (F∘ kB (F-appL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairR vA)) refl refl (F∘ kB (F-appR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairR vA)) refl refl (F∘ kB (F-op mB opB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairR vA)) refl refl (F∘ kB F-loss) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairR vA)) refl refl (F∘ kB (F-handleP hB bB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairR vA)) refl refl (S∘ kB (S-handleB hB vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairR vA)) refl refl (S∘ kB (S-then subB gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairR vA)) refl refl (S∘ kB (S-glocal sub1B sub2B gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-pairR vA)) refl refl (S∘ kB S-reset) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-fst) refl refl (▫) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-fst) refl refl (F∘ kB (F-fun pfB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-fst) refl refl (F∘ kB (F-pairL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-fst) refl refl (F∘ kB (F-pairR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-fst) refl refl (F∘ kB F-fst) refl refl nh1 nh2 eq
      with Σ-≡,≡←≡ (just-injective (cong unfst-arg eq))
    ... | (τAeq , restEq)
      with go kA refl refl kB (cong (λ τ → _ `× τ) τAeq) refl nh1 nh2
             (trans (trans (sym (subst-sym-cancel (λ τ → _ ⊢ (_ `× τ) ! _) τAeq (plugK kA (opE m1 op1 (val v2-1))))) (cong (subst (λ τ → _ ⊢ (_ `× τ) ! _) (sym τAeq)) restEq)) (sym (generic-atE-fst-cast2 τAeq (plugK kB (opE m2 op2 (val v2-2))))))
    ... | (opeq , εopeq , keq , meq , veq) =
      opeq , εopeq , wrapF∘-fst (cong (λ o → gnd (in′ o)) opeq) εopeq τAeq keq , meq , veq
    go (F∘ kA F-fst) refl refl (F∘ kB F-snd) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-fst) refl refl (F∘ kB (F-appL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-fst) refl refl (F∘ kB (F-appR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-fst) refl refl (F∘ kB (F-op mB opB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-fst) refl refl (F∘ kB F-loss) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-fst) refl refl (F∘ kB (F-handleP hB bB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-fst) refl refl (S∘ kB (S-handleB hB vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-fst) refl refl (S∘ kB (S-then subB gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-fst) refl refl (S∘ kB (S-glocal sub1B sub2B gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-fst) refl refl (S∘ kB S-reset) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-snd) refl refl (▫) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-snd) refl refl (F∘ kB (F-fun pfB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-snd) refl refl (F∘ kB (F-pairL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-snd) refl refl (F∘ kB (F-pairR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-snd) refl refl (F∘ kB F-fst) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-snd) refl refl (F∘ kB F-snd) refl refl nh1 nh2 eq
      with Σ-≡,≡←≡ (just-injective (cong unsnd-arg eq))
    ... | (σAeq , restEq)
      with go kA refl refl kB (cong (λ σ → σ `× _) σAeq) refl nh1 nh2
             (trans (trans (sym (subst-sym-cancel (λ σ → _ ⊢ (σ `× _) ! _) σAeq (plugK kA (opE m1 op1 (val v2-1))))) (cong (subst (λ σ → _ ⊢ (σ `× _) ! _) (sym σAeq)) restEq)) (sym (generic-atE-snd-cast2 σAeq (plugK kB (opE m2 op2 (val v2-2))))))
    ... | (opeq , εopeq , keq , meq , veq) =
      opeq , εopeq , wrapF∘-snd (cong (λ o → gnd (in′ o)) opeq) εopeq σAeq keq , meq , veq
    go (F∘ kA F-snd) refl refl (F∘ kB (F-appL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-snd) refl refl (F∘ kB (F-appR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-snd) refl refl (F∘ kB (F-op mB opB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-snd) refl refl (F∘ kB F-loss) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-snd) refl refl (F∘ kB (F-handleP hB bB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-snd) refl refl (S∘ kB (S-handleB hB vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-snd) refl refl (S∘ kB (S-then subB gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-snd) refl refl (S∘ kB (S-glocal sub1B sub2B gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-snd) refl refl (S∘ kB S-reset) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appL e2A)) refl refl (▫) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appL e2A)) refl refl (F∘ kB (F-fun pfB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appL e2A)) refl refl (F∘ kB (F-pairL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appL e2A)) refl refl (F∘ kB (F-pairR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appL e2A)) refl refl (F∘ kB F-fst) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appL e2A)) refl refl (F∘ kB F-snd) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appL e2A)) refl refl (F∘ kB (F-appL e2B)) refl refl nh1 nh2 eq
      with Σ-≡,≡←≡ (just-injective (cong unapp-key eq))
    ... | (σAeq , fnEq)
      with σAeq
    ...   | refl
      with app-inj2 eq
    ...     | refl
      with go kA refl refl kB refl refl nh1 nh2 (app-inj1 eq)
    ...       | (opeq , εopeq , keq , meq , veq) =
      opeq , εopeq , wrapF∘ (cong (λ o → gnd (in′ o)) opeq) εopeq (F-appL e2A) (generic-atK2-refl-refl-inv (cong (λ o → gnd (in′ o)) opeq) εopeq keq) , meq , veq
    go (F∘ kA (F-appL e2A)) refl refl (F∘ kB (F-appR vB)) refl refl nh1 nh2 eq
      with Σ-≡,≡←≡ (just-injective (cong unapp-key eq))
    ... | (σAeq , fnEq)
      with σAeq
    ...   | refl = ⊥-elim (plugK-op-not-val kA vB (app-inj1 eq))
    go (F∘ kA (F-appL e2A)) refl refl (F∘ kB (F-op mB opB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appL e2A)) refl refl (F∘ kB F-loss) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appL e2A)) refl refl (F∘ kB (F-handleP hB bB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appL e2A)) refl refl (S∘ kB (S-handleB hB vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appL e2A)) refl refl (S∘ kB (S-then subB gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appL e2A)) refl refl (S∘ kB (S-glocal sub1B sub2B gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appL e2A)) refl refl (S∘ kB S-reset) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appR vA)) refl refl (▫) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appR vA)) refl refl (F∘ kB (F-fun pfB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appR vA)) refl refl (F∘ kB (F-pairL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appR vA)) refl refl (F∘ kB (F-pairR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appR vA)) refl refl (F∘ kB F-fst) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appR vA)) refl refl (F∘ kB F-snd) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appR vA)) refl refl (F∘ kB (F-appL e2B)) refl refl nh1 nh2 eq
      with Σ-≡,≡←≡ (just-injective (cong unapp-key eq))
    ... | (σAeq , fnEq)
      with σAeq
    ...   | refl = ⊥-elim (plugK-op-not-val kB vA (sym (app-inj1 eq)))
    go (F∘ kA (F-appR vA)) refl refl (F∘ kB (F-appR vB)) refl refl nh1 nh2 eq
      with Σ-≡,≡←≡ (just-injective (cong unapp-key eq))
    ... | (σAeq , fnEq)
      with σAeq
    ...   | refl
      with val-inj (app-inj1 eq)
    ... | refl
      with go kA refl refl kB refl refl nh1 nh2 (app-inj2 eq)
    ... | (opeq , εopeq , keq , meq , veq) =
      opeq , εopeq , wrapF∘ (cong (λ o → gnd (in′ o)) opeq) εopeq (F-appR vA) (generic-atK2-refl-refl-inv (cong (λ o → gnd (in′ o)) opeq) εopeq keq) , meq , veq
    go (F∘ kA (F-appR vA)) refl refl (F∘ kB (F-op mB opB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appR vA)) refl refl (F∘ kB F-loss) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appR vA)) refl refl (F∘ kB (F-handleP hB bB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appR vA)) refl refl (S∘ kB (S-handleB hB vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appR vA)) refl refl (S∘ kB (S-then subB gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appR vA)) refl refl (S∘ kB (S-glocal sub1B sub2B gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-appR vA)) refl refl (S∘ kB S-reset) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-op mA opA)) refl refl (▫) τeq2 εeq2 nh1 nh2 eq
      with just-injective (trans (cong unOpEShallow eq) (unOpEShallow-substE τeq2 εeq2 (opE m2 op2 (val v2-2))))
    ... | refl
      with τeq2 | εeq2
    ...   | refl | refl = ⊥-elim (plugK-op-not-val kA v2-2 (opE-arg-inj eq))
    go (F∘ kA (F-op mA opA)) refl refl (F∘ kB (F-fun pfB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-op mA opA)) refl refl (F∘ kB (F-pairL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-op mA opA)) refl refl (F∘ kB (F-pairR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-op mA opA)) refl refl (F∘ kB F-fst) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-op mA opA)) refl refl (F∘ kB F-snd) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-op mA opA)) refl refl (F∘ kB (F-appL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-op mA opA)) refl refl (F∘ kB (F-appR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-op mA opA)) refl refl (F∘ kB (F-op mB opB)) τeq2 εeq2 nh1 nh2 eq
      with just-injective (trans (cong unOpEShallow eq) (unOpEShallow-substE τeq2 εeq2 (opE mB opB (plugK kB (opE m2 op2 (val v2-2))))))
    ... | refl
      with τeq2 | εeq2
    ...   | refl | refl
        with go kA refl refl kB refl refl nh1 nh2 (opE-arg-inj eq)
    ...     | (opeq , εopeq , keq , meq , veq) =
      opeq , εopeq , wrapF∘ (cong (λ o → gnd (in′ o)) opeq) εopeq (F-op mA opA) (generic-atK2-refl-refl-inv (cong (λ o → gnd (in′ o)) opeq) εopeq keq) , meq , veq
    go (F∘ kA (F-op mA opA)) refl refl (F∘ kB F-loss) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-op mA opA)) refl refl (F∘ kB (F-handleP hB bB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-op mA opA)) refl refl (S∘ kB (S-handleB hB vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-op mA opA)) refl refl (S∘ kB (S-then subB gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-op mA opA)) refl refl (S∘ kB (S-glocal sub1B sub2B gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-op mA opA)) refl refl (S∘ kB S-reset) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-loss) refl refl (▫) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-loss) refl refl (F∘ kB (F-fun pfB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-loss) refl refl (F∘ kB (F-pairL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-loss) refl refl (F∘ kB (F-pairR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-loss) refl refl (F∘ kB F-fst) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-loss) refl refl (F∘ kB F-snd) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-loss) refl refl (F∘ kB (F-appL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-loss) refl refl (F∘ kB (F-appR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-loss) refl refl (F∘ kB (F-op mB opB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-loss) refl refl (F∘ kB F-loss) refl refl nh1 nh2 eq
      with go kA refl refl kB refl refl nh1 nh2 (lossE-inj eq)
    ... | (opeq , εopeq , keq , meq , veq) =
      opeq , εopeq , wrapF∘ (cong (λ o → gnd (in′ o)) opeq) εopeq F-loss (generic-atK2-refl-refl-inv (cong (λ o → gnd (in′ o)) opeq) εopeq keq) , meq , veq
    go (F∘ kA F-loss) refl refl (F∘ kB (F-handleP hB bB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-loss) refl refl (S∘ kB (S-handleB hB vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-loss) refl refl (S∘ kB (S-then subB gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-loss) refl refl (S∘ kB (S-glocal sub1B sub2B gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA F-loss) refl refl (S∘ kB S-reset) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-handleP hA bA)) refl refl (▫) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-handleP hA bA)) refl refl (F∘ kB (F-fun pfB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-handleP hA bA)) refl refl (F∘ kB (F-pairL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-handleP hA bA)) refl refl (F∘ kB (F-pairR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-handleP hA bA)) refl refl (F∘ kB F-fst) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-handleP hA bA)) refl refl (F∘ kB F-snd) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-handleP hA bA)) refl refl (F∘ kB (F-appL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-handleP hA bA)) refl refl (F∘ kB (F-appR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-handleP hA bA)) refl refl (F∘ kB (F-op mB opB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-handleP hA bA)) refl refl (F∘ kB F-loss) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-handleP hA bA)) refl refl (F∘ kB (F-handleP hB bB)) refl refl nh1 nh2 eq
      with just-injective (cong unhandle-key eq)
    ... | refl
      with handleE-inj eq
    ...   | (_ , pEq , bEq)
        with bEq
    ...     | refl
          with go kA refl refl kB refl refl nh1 nh2 pEq
    ...       | (opeq , εopeq , keq , meq , veq) =
      opeq , εopeq , wrapF∘ (cong (λ o → gnd (in′ o)) opeq) εopeq (F-handleP hA bA) (generic-atK2-refl-refl-inv (cong (λ o → gnd (in′ o)) opeq) εopeq keq) , meq , veq
    go (F∘ kA (F-handleP hA bA)) refl refl (S∘ kB (S-handleB hB vB)) refl refl nh1 nh2 eq
      with just-injective (cong unhandle-key eq)
    ... | refl
      with handleE-inj eq
    ...   | (_ , pEq , bEq) = ⊥-elim (plugK-op-not-val kA vB pEq)
    go (F∘ kA (F-handleP hA bA)) refl refl (S∘ kB (S-then subB gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-handleP hA bA)) refl refl (S∘ kB (S-glocal sub1B sub2B gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (F∘ kA (F-handleP hA bA)) refl refl (S∘ kB S-reset) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-handleB hA vA)) refl refl (▫) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-handleB hA vA)) refl refl (F∘ kB (F-fun pfB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-handleB hA vA)) refl refl (F∘ kB (F-pairL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-handleB hA vA)) refl refl (F∘ kB (F-pairR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-handleB hA vA)) refl refl (F∘ kB F-fst) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-handleB hA vA)) refl refl (F∘ kB F-snd) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-handleB hA vA)) refl refl (F∘ kB (F-appL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-handleB hA vA)) refl refl (F∘ kB (F-appR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-handleB hA vA)) refl refl (F∘ kB (F-op mB opB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-handleB hA vA)) refl refl (F∘ kB F-loss) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-handleB hA vA)) refl refl (F∘ kB (F-handleP hB bB)) refl refl nh1 nh2 eq
      with just-injective (cong unhandle-key eq)
    ... | refl
      with handleE-inj eq
    ...   | (_ , pEq , bEq) = ⊥-elim (plugK-op-not-val kB vA (sym pEq))
    go (S∘ kA (S-handleB hA vA)) refl refl (S∘ kB (S-handleB hB vB)) refl refl nh1 nh2 eq
      with just-injective (cong unhandle-key eq)
    ... | refl
      with handleE-inj eq
    ...   | (_ , pEq , bEq)
        with val-inj pEq
    ...     | refl
          with go kA refl refl kB refl refl (nh1 ∘ inj₂) (nh2 ∘ inj₂) bEq
    ...       | (opeq , εopeq , keq , meq , veq) =
      opeq , εopeq , wrapS∘ (cong (λ o → gnd (in′ o)) opeq) εopeq (S-handleB hA vA) (generic-atK2-refl-refl-inv (cong (λ o → gnd (in′ o)) opeq) εopeq keq) , meq , veq
    go (S∘ kA (S-handleB hA vA)) refl refl (S∘ kB (S-then subB gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-handleB hA vA)) refl refl (S∘ kB (S-glocal sub1B sub2B gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-handleB hA vA)) refl refl (S∘ kB S-reset) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-then subA gA)) refl refl (▫) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-then subA gA)) refl refl (F∘ kB (F-fun pfB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-then subA gA)) refl refl (F∘ kB (F-pairL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-then subA gA)) refl refl (F∘ kB (F-pairR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-then subA gA)) refl refl (F∘ kB F-fst) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-then subA gA)) refl refl (F∘ kB F-snd) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-then subA gA)) refl refl (F∘ kB (F-appL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-then subA gA)) refl refl (F∘ kB (F-appR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-then subA gA)) refl refl (F∘ kB (F-op mB opB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-then subA gA)) refl refl (F∘ kB F-loss) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-then subA gA)) refl refl (F∘ kB (F-handleP hB bB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-then subA gA)) refl refl (S∘ kB (S-handleB hB vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-then subA gA)) refl refl (S∘ kB (S-then subB gB)) refl refl nh1 nh2 eq
      with just-injective (cong unthen-key eq)
    ... | refl
      with go kA refl refl kB refl refl nh1 nh2 (thenE-arg-inj eq)
    ...   | (opeq , εopeq , keq , meq , veq) =
      opeq , εopeq , wrapS∘ (cong (λ o → gnd (in′ o)) opeq) εopeq (S-then subA gA) (generic-atK2-refl-refl-inv (cong (λ o → gnd (in′ o)) opeq) εopeq keq) , meq , veq
    go (S∘ kA (S-then subA gA)) refl refl (S∘ kB (S-glocal sub1B sub2B gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-then subA gA)) refl refl (S∘ kB S-reset) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-glocal sub1A sub2A gA)) refl refl (▫) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-glocal sub1A sub2A gA)) refl refl (F∘ kB (F-fun pfB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-glocal sub1A sub2A gA)) refl refl (F∘ kB (F-pairL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-glocal sub1A sub2A gA)) refl refl (F∘ kB (F-pairR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-glocal sub1A sub2A gA)) refl refl (F∘ kB F-fst) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-glocal sub1A sub2A gA)) refl refl (F∘ kB F-snd) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-glocal sub1A sub2A gA)) refl refl (F∘ kB (F-appL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-glocal sub1A sub2A gA)) refl refl (F∘ kB (F-appR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-glocal sub1A sub2A gA)) refl refl (F∘ kB (F-op mB opB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-glocal sub1A sub2A gA)) refl refl (F∘ kB F-loss) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-glocal sub1A sub2A gA)) refl refl (F∘ kB (F-handleP hB bB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-glocal sub1A sub2A gA)) refl refl (S∘ kB (S-handleB hB vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-glocal sub1A sub2A gA)) refl refl (S∘ kB (S-then subB gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA (S-glocal sub1A sub2A gA)) refl refl (S∘ kB (S-glocal sub1B sub2B gB)) refl refl nh1 nh2 eq
      with just-injective (cong unglocal-key eq)
    ... | refl
      with go kA refl refl kB refl refl nh1 nh2 (glocalE-arg-inj eq)
    ...   | (opeq , εopeq , keq , meq , veq) =
      opeq , εopeq , wrapS∘ (cong (λ o → gnd (in′ o)) opeq) εopeq (S-glocal sub1A sub2A gA) (generic-atK2-refl-refl-inv (cong (λ o → gnd (in′ o)) opeq) εopeq keq) , meq , veq
    go (S∘ kA (S-glocal sub1A sub2A gA)) refl refl (S∘ kB S-reset) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA S-reset) refl refl (▫) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA S-reset) refl refl (F∘ kB (F-fun pfB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA S-reset) refl refl (F∘ kB (F-pairL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA S-reset) refl refl (F∘ kB (F-pairR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA S-reset) refl refl (F∘ kB F-fst) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA S-reset) refl refl (F∘ kB F-snd) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA S-reset) refl refl (F∘ kB (F-appL e2B)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA S-reset) refl refl (F∘ kB (F-appR vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA S-reset) refl refl (F∘ kB (F-op mB opB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA S-reset) refl refl (F∘ kB F-loss) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA S-reset) refl refl (F∘ kB (F-handleP hB bB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA S-reset) refl refl (S∘ kB (S-handleB hB vB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA S-reset) refl refl (S∘ kB (S-then subB gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA S-reset) refl refl (S∘ kB (S-glocal sub1B sub2B gB)) τeq2 εeq2 nh1 nh2 eq = ⊥-elim (shape-absurdE τeq2 εeq2 _ eq (λ ()))
    go (S∘ kA S-reset) refl refl (S∘ kB S-reset) refl refl nh1 nh2 eq
      with go kA refl refl kB refl refl nh1 nh2 (resetE-inj eq)
    ... | (opeq , εopeq , keq , meq , veq) =
      opeq , εopeq , wrapS∘ (cong (λ o → gnd (in′ o)) opeq) εopeq S-reset (generic-atK2-refl-refl-inv (cong (λ o → gnd (in′ o)) opeq) εopeq keq) , meq , veq

    final : op1 ≡ op2 × K1 ≅ K2 × m1 ≅ m2 × v2-1 ≅ v2-2
    final with go K1 refl refl K2 refl refl nh1 nh2 eq
    ... | (opeq , εopeq , Keq , meq , veq) =
      opeq , ≅-trans (≅-sym (≡-to-≅ Keq)) (generic-atK2-≅ (cong (λ o → gnd (in′ o)) opeq) εopeq refl refl K2) , meq , veq

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
  theorem-A4-2 : ∀ {Γ σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} {e : Γ ⊢ σ ! ε} {r1 r2 : R} {e1' e2' : Γ ⊢ σ ! ε}
                 (stp1 : _⊢_-[_]→_ {sub = sub} g e r1 e1') (stp2 : _⊢_-[_]→_ {sub = sub} g e r2 e2')
               → stp1 ≅ stp2

-- ---------------------------------------------------------------------
-- Partial progress toward theorem-A4-2, proved for real (not postulated)
-- for the "tFun" group: the two rules whose conclusion is `fun`-headed
-- (R1, and F-rule wrapping F-fun). theorem-A4-2 itself is left untouched
-- above; this lemma has the exact same signature and, for every OTHER
-- top-level shape of stp1 (the other 10 groups), simply defers to the
-- theorem-A4-2 postulate directly -- since that already returns `_≅_`,
-- no conversion is needed for those 23 delegating clauses. Only the two
-- tFun clauses are genuine, hole-free proof content.
--
-- Two hard-won techniques made this tractable, confirmed via extensive
-- standalone experiments (see conversation history / a42t.agda, since
-- removed):
--
-- 1. Matching stp2 (or any second step derivation sharing e with stp1)
--    against F-rule (or S1-S4) needs e itself to stay a GENERIC, fresh
--    implicit in the sub-helper's own signature, with the concrete
--    shape carried by a SEPARATE `e ≡ concrete-shape` hypothesis
--    (mirroring theorem-A4-1-op's own established "helper stp refl"
--    idiom throughout this file) -- fixing e concretely in the
--    sub-helper's own type makes Agda's coverage checker get
--    permanently "stuck" trying to unify `plugF f e` (f still unknown)
--    against the fixed target, long before it can even look at which
--    frame shape f has. This ALSO requires full local coverage of the
--    sub-helper's own 25 leaf shapes (even the type-incompatible ones
--    that could otherwise be omitted) once F-rule/S1-S4 appear anywhere
--    among them -- Agda's coverage checker needs the complete sibling
--    set to resolve any individual clause when a plugF/plugK-opaque
--    constructor is present, confirmed by direct experiment.
--
-- 2. Once two step derivations of possibly-different index (r1/e1' vs
--    r2/e2') need to be related, NEVER try to pattern-match a `_≅_`
--    hypothesis between them directly (e.g. via `with rec-call | ≅-refl`
--    for a recursive call `rec-call : stp1' ≅ stp2'`) -- Agda's coverage
--    checker gets stuck trying to unify the two (still-independent)
--    index metavariables, confirmed as a GENERAL Agda limitation via a
--    minimal standalone repro completely unrelated to this codebase (an
--    indexed family Fam : Nat → Nat → Set with a `wrap` constructor).
--    Instead, bundle (e, r, e', stp) into a single, non-indexed Σ-value
--    via `pack`, and do ALL recursive reasoning in ordinary `_≡_` on
--    packed values (which Agda's coverage checker handles just fine,
--    confirmed via the same repro) -- `_≡_` is converted to `_≅_` only
--    ONCE, via `pack-≡-to-≅`, at the very outermost call.
-- ---------------------------------------------------------------------

-- Bundles (e, r, e', stp) into a plain Σ-quadruple, crucially including
-- e itself in the bundle (rather than as an external index) -- so that
-- `pack`'s own return TYPE never depends on the specific value of e,
-- letting `pack (R1 f x) ≡ pack s` type-check even when s's own e is
-- still a generic, unconstrained implicit (as technique 1 above needs).
pack : ∀ {Γ σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} {e : Γ ⊢ σ ! ε} {r : R} {e' : Γ ⊢ σ ! ε}
     → _⊢_-[_]→_ {sub = sub} g e r e'
     → Σ (Γ ⊢ σ ! ε) (λ e → Σ R (λ r → Σ (Γ ⊢ σ ! ε) (λ e' → _⊢_-[_]→_ {sub = sub} g e r e')))
pack {e = e} {r = r} {e' = e'} stp = e , r , e' , stp

pack-≡-to-≅ : ∀ {Γ σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} {e : Γ ⊢ σ ! ε} {r1 r2 : R} {e1' e2' : Γ ⊢ σ ! ε}
                {stp1 : _⊢_-[_]→_ {sub = sub} g e r1 e1'} {stp2 : _⊢_-[_]→_ {sub = sub} g e r2 e2'}
              → pack stp1 ≡ pack stp2 → stp1 ≅ stp2
pack-≡-to-≅ refl = ≅-refl

-- Logically equivalent restatement of theorem-A4-2 itself, in packed
-- form -- NOT a weaker assumption, just a different phrasing of the same
-- not-yet-proven fact. Needed because theorem-A4-2-core's own
-- recursive diagonal (technique 2 above) forces it to have a fully
-- generic `e`, hence its own full 25-shape top-level coverage; its 23
-- non-tFun clauses need SOMETHING of type `pack stp1 ≡ pack stp2` to
-- delegate to, and deriving that from theorem-A4-2 itself would require
-- pattern-matching a `_≅_` value with still-independent indices -- the
-- exact limitation this whole file works around (confirmed as a general,
-- codebase-independent Agda limitation via a minimal standalone repro).
-- Once every one of the 25 shapes has a real proof, both this postulate
-- and theorem-A4-2 itself become derivable from that proof and can be
-- deleted.
postulate
  theorem-A4-2-pack : ∀ {Γ σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} {e : Γ ⊢ σ ! ε} {r1 r2 : R} {e1' e2' : Γ ⊢ σ ! ε}
                       (stp1 : _⊢_-[_]→_ {sub = sub} g e r1 e1') (stp2 : _⊢_-[_]→_ {sub = sub} g e r2 e2')
                     → pack stp1 ≡ pack stp2

-- fun's own domain γ is hidden from its codomain (gnd δ only shows δ),
-- so two fun-headed terms with independently-fresh PrimFuns can't be
-- compared via ordinary injectivity until γ itself is known shared --
-- `refl`-matching this directly (rather than applying a fixed-γ lemma
-- like fun-inj1/fun-inj2 to an abstract hypothesis) is what lets Agda's
-- dependent pattern matcher discover γ1≡γ2 as a byproduct.
fun-inj0 : ∀ {Γ γ1 γ2 δ ε} {f1 : PrimFun γ1 δ} {f2 : PrimFun γ2 δ} {e1 : Γ ⊢ gnd γ1 ! ε} {e2 : Γ ⊢ gnd γ2 ! ε}
         → fun f1 e1 ≡ fun f2 e2 → γ1 ≡ γ2
fun-inj0 refl = refl

-- Same role as fun-inj0, for fst's own hidden τ (fst : Γ⊢(σ`×τ)!ε →
-- Γ⊢σ!ε -- τ vanishes from the codomain).
fst-inj0 : ∀ {Γ σ τ1 τ2 ε} {e1 : Γ ⊢ (σ `× τ1) ! ε} {e2 : Γ ⊢ (σ `× τ2) ! ε}
         → fst {τ = τ1} e1 ≡ fst {τ = τ2} e2 → τ1 ≡ τ2
fst-inj0 refl = refl

-- Same role, for snd's own hidden σ.
snd-inj0 : ∀ {Γ σ1 σ2 τ ε} {e1 : Γ ⊢ (σ1 `× τ) ! ε} {e2 : Γ ⊢ (σ2 `× τ) ! ε}
         → snd {σ = σ1} e1 ≡ snd {σ = σ2} e2 → σ1 ≡ σ2
snd-inj0 refl = refl

-- Core of theorem-A4-2-proved, working entirely in ordinary `_≡_` on
-- packed values (technique 2 above) -- converted to `_≅_` exactly once,
-- by theorem-A4-2-proved itself below.
theorem-A4-2-core : ∀ {Γ σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} {e : Γ ⊢ σ ! ε} {r1 r2 : R} {e1' e2' : Γ ⊢ σ ! ε}
                          (stp1 : _⊢_-[_]→_ {sub = sub} g e r1 e1') (stp2 : _⊢_-[_]→_ {sub = sub} g e r2 e2')
                        → pack stp1 ≡ pack stp2
theorem-A4-2-core {Γ} {ε = ε} {sub = sub} {g = g} (R1 f x) stp2 = helper stp2 refl
  where
  helper : ∀ {e r2 e2'} (s : _⊢_-[_]→_ {sub = sub} g e r2 e2') → e ≡ fun {ε = ε} f (val (vgnd x))
         → pack (R1 {sub = sub} {g = g} f x) ≡ pack s
  helper (R1 .f .x) refl = refl
  helper (R2-fst v w) ()
  helper (R2-snd v w) ()
  helper (R3 e v) ()
  helper (R4 r) ()
  helper (R6 h v1 v2) ()
  helper (R7 sub' v e) ()
  helper (R8 sub1 sub2 v g1) ()
  helper (R9 v) ()
  helper (S1 sub' h v stp) ()
  helper (S2 sub' g1 stp) ()
  helper (S3 sub1 sub2 g1 stp) ()
  helper (S4 stp) ()
  helper (R5 sub' h v1 m op v2 k nh) ()
  helper (F-rule sub2 (F-fun pf2) stp2) refl = ⊥-elim (theorem-A4-1-val stp2)
  helper (F-rule sub2 F-fst       stp) ()
  helper (F-rule sub2 F-snd       stp) ()
  helper (F-rule sub2 (F-appL _)  stp) ()
  helper (F-rule sub2 (F-appR _)  stp) ()
  helper (F-rule sub2 (F-op _ _)  stp) ()
  helper (F-rule sub2 F-loss      stp) ()
  helper (F-rule sub2 (F-handleP h b) stp) ()
theorem-A4-2-core {Γ} {ε = ε} {sub = sub} {g = g} (F-rule sub1 (F-fun pf) {e = eh} {e' = eh'} stp1) stp2 = helper stp2 refl
  where
  helper : ∀ {e r2 e2'} (s : _⊢_-[_]→_ {sub = sub} g e r2 e2') → e ≡ fun pf eh
         → pack (F-rule sub1 (F-fun pf) stp1) ≡ pack s
  helper (R1 pf' x) eq with fun-inj0 eq
  ... | refl = ⊥-elim (theorem-A4-1-val (subst (λ □ → _⊢_-[_]→_ _ □ _ _) (sym (fun-inj2 eq)) stp1))
  helper (R2-fst v w) ()
  helper (R2-snd v w) ()
  helper (R3 e v) ()
  helper (R4 r) ()
  helper (R6 h v1 v2) ()
  helper (R7 sub' v e) ()
  helper (R8 sub1' sub2 v g1) ()
  helper (R9 v) ()
  helper (S1 sub' h v stp) ()
  helper (S2 sub' g1 stp) ()
  helper (S3 sub1' sub2 g1 stp) ()
  helper (S4 stp) ()
  helper (R5 sub' h v1 m op v2 k nh) ()
  -- recursive diagonal: stp1,stp2' are themselves stepping the SAME hole
  -- eh under the SAME rewritten continuation, so theorem-A4-2-core
  -- applies to them directly -- genuine, terminating structural
  -- recursion (stp1,stp2' are F-rule's own premises, strictly smaller).
  helper (F-rule sub2 (F-fun pf2) stp2') eq with fun-inj0 eq
  ... | refl with fun-inj1 eq | fun-inj2 eq
  ...   | refl | refl with theorem-A4-2-core stp1 stp2'
  ...     | inner-eq = cong (λ { (e , r , e' , t) → (fun pf e , r , fun pf e' , F-rule sub1 (F-fun pf) t) }) inner-eq
  helper (F-rule sub2 F-fst       stp) ()
  helper (F-rule sub2 F-snd       stp) ()
  helper (F-rule sub2 (F-appL _)  stp) ()
  helper (F-rule sub2 (F-appR _)  stp) ()
  helper (F-rule sub2 (F-op _ _)  stp) ()
  helper (F-rule sub2 F-loss      stp) ()
  helper (F-rule sub2 (F-handleP h b) stp) ()

-- tFst group: R2-fst / F-rule-F-fst. Mirrors tFun exactly, with fst-inj0
-- playing fun-inj0's role for the hidden τ.
theorem-A4-2-core {Γ} {ε = ε} {sub = sub} {g = g} (R2-fst v w) stp2 = helper stp2 refl
  where
  helper : ∀ {e r2 e2'} (s : _⊢_-[_]→_ {sub = sub} g e r2 e2') → e ≡ fst {ε = ε} (val (vpair v w))
         → pack (R2-fst {sub = sub} {g = g} v w) ≡ pack s
  helper (R2-fst .v .w) refl = refl
  helper (R1 f x) ()
  helper (R2-pair v' w') ()
  helper (R2-snd v' w') ()
  helper (R3 e v') ()
  helper (R4 r) ()
  helper (R6 h v1 v2) ()
  helper (R7 sub' v' e) ()
  helper (R8 sub1 sub2 v' g1) ()
  helper (R9 v') ()
  helper (S1 sub' h v' stp) ()
  helper (S2 sub' g1 stp) ()
  helper (S3 sub1 sub2 g1 stp) ()
  helper (S4 stp) ()
  helper (R5 sub' h v1 m op v2 k nh) ()
  helper (F-rule sub2 (F-fun _) stp) ()
  helper (F-rule sub2 (F-pairL _) stp) ()
  helper (F-rule sub2 (F-pairR _) stp) ()
  helper (F-rule sub2 F-fst stp2) refl = ⊥-elim (theorem-A4-1-val stp2)
  helper (F-rule sub2 F-snd stp) ()
  helper (F-rule sub2 (F-appL _) stp) ()
  helper (F-rule sub2 (F-appR _) stp) ()
  helper (F-rule sub2 (F-op _ _) stp) ()
  helper (F-rule sub2 F-loss stp) ()
  helper (F-rule sub2 (F-handleP h b) stp) ()
theorem-A4-2-core {Γ} {ε = ε} {sub = sub} {g = g} (F-rule sub1 F-fst {e = eh} {e' = eh'} stp1) stp2 = helper stp2 refl
  where
  helper : ∀ {e r2 e2'} (s : _⊢_-[_]→_ {sub = sub} g e r2 e2') → e ≡ fst eh
         → pack (F-rule sub1 F-fst stp1) ≡ pack s
  helper (R2-fst v w) eq with fst-inj0 eq
  ... | refl = ⊥-elim (theorem-A4-1-val (subst (λ □ → _⊢_-[_]→_ _ □ _ _) (sym (fst-inj eq)) stp1))
  helper (R1 f x) ()
  helper (R2-pair v' w') ()
  helper (R2-snd v' w') ()
  helper (R3 e v') ()
  helper (R4 r) ()
  helper (R6 h v1 v2) ()
  helper (R7 sub' v' e) ()
  helper (R8 sub1' sub2 v' g1) ()
  helper (R9 v') ()
  helper (S1 sub' h v' stp) ()
  helper (S2 sub' g1 stp) ()
  helper (S3 sub1' sub2 g1 stp) ()
  helper (S4 stp) ()
  helper (R5 sub' h v1 m op v2 k nh) ()
  helper (F-rule sub2 (F-fun _) stp) ()
  helper (F-rule sub2 (F-pairL _) stp) ()
  helper (F-rule sub2 (F-pairR _) stp) ()
  -- recursive diagonal, same shape as tFun's own.
  helper (F-rule sub2 F-fst stp2') eq with fst-inj0 eq
  ... | refl with fst-inj eq
  ...   | refl with theorem-A4-2-core stp1 stp2'
  ...     | inner-eq = cong (λ { (e , r , e' , t) → (fst e , r , fst e' , F-rule sub1 F-fst t) }) inner-eq
  helper (F-rule sub2 F-snd stp) ()
  helper (F-rule sub2 (F-appL _) stp) ()
  helper (F-rule sub2 (F-appR _) stp) ()
  helper (F-rule sub2 (F-op _ _) stp) ()
  helper (F-rule sub2 F-loss stp) ()
  helper (F-rule sub2 (F-handleP h b) stp) ()

-- tSnd group: R2-snd / F-rule-F-snd. Symmetric to tFst.
theorem-A4-2-core {Γ} {ε = ε} {sub = sub} {g = g} (R2-snd v w) stp2 = helper stp2 refl
  where
  helper : ∀ {e r2 e2'} (s : _⊢_-[_]→_ {sub = sub} g e r2 e2') → e ≡ snd {ε = ε} (val (vpair v w))
         → pack (R2-snd {sub = sub} {g = g} v w) ≡ pack s
  helper (R2-snd .v .w) refl = refl
  helper (R1 f x) ()
  helper (R2-pair v' w') ()
  helper (R2-fst v' w') ()
  helper (R3 e v') ()
  helper (R4 r) ()
  helper (R6 h v1 v2) ()
  helper (R7 sub' v' e) ()
  helper (R8 sub1 sub2 v' g1) ()
  helper (R9 v') ()
  helper (S1 sub' h v' stp) ()
  helper (S2 sub' g1 stp) ()
  helper (S3 sub1 sub2 g1 stp) ()
  helper (S4 stp) ()
  helper (R5 sub' h v1 m op v2 k nh) ()
  helper (F-rule sub2 (F-fun _) stp) ()
  helper (F-rule sub2 (F-pairL _) stp) ()
  helper (F-rule sub2 (F-pairR _) stp) ()
  helper (F-rule sub2 F-fst stp) ()
  helper (F-rule sub2 F-snd stp2) refl = ⊥-elim (theorem-A4-1-val stp2)
  helper (F-rule sub2 (F-appL _) stp) ()
  helper (F-rule sub2 (F-appR _) stp) ()
  helper (F-rule sub2 (F-op _ _) stp) ()
  helper (F-rule sub2 F-loss stp) ()
  helper (F-rule sub2 (F-handleP h b) stp) ()
theorem-A4-2-core {Γ} {ε = ε} {sub = sub} {g = g} (F-rule sub1 F-snd {e = eh} {e' = eh'} stp1) stp2 = helper stp2 refl
  where
  helper : ∀ {e r2 e2'} (s : _⊢_-[_]→_ {sub = sub} g e r2 e2') → e ≡ snd eh
         → pack (F-rule sub1 F-snd stp1) ≡ pack s
  helper (R2-snd v w) eq with snd-inj0 eq
  ... | refl = ⊥-elim (theorem-A4-1-val (subst (λ □ → _⊢_-[_]→_ _ □ _ _) (sym (snd-inj eq)) stp1))
  helper (R1 f x) ()
  helper (R2-pair v' w') ()
  helper (R2-fst v' w') ()
  helper (R3 e v') ()
  helper (R4 r) ()
  helper (R6 h v1 v2) ()
  helper (R7 sub' v' e) ()
  helper (R8 sub1' sub2 v' g1) ()
  helper (R9 v') ()
  helper (S1 sub' h v' stp) ()
  helper (S2 sub' g1 stp) ()
  helper (S3 sub1' sub2 g1 stp) ()
  helper (S4 stp) ()
  helper (R5 sub' h v1 m op v2 k nh) ()
  helper (F-rule sub2 (F-fun _) stp) ()
  helper (F-rule sub2 (F-pairL _) stp) ()
  helper (F-rule sub2 (F-pairR _) stp) ()
  helper (F-rule sub2 F-fst stp) ()
  helper (F-rule sub2 F-snd stp2') eq with snd-inj0 eq
  ... | refl with snd-inj eq
  ...   | refl with theorem-A4-2-core stp1 stp2'
  ...     | inner-eq = cong (λ { (e , r , e' , t) → (snd e , r , snd e' , F-rule sub1 F-snd t) }) inner-eq
  helper (F-rule sub2 (F-appL _) stp) ()
  helper (F-rule sub2 (F-appR _) stp) ()
  helper (F-rule sub2 (F-op _ _) stp) ()
  helper (F-rule sub2 F-loss stp) ()
  helper (F-rule sub2 (F-handleP h b) stp) ()

-- tLoss (R4 / F-rule-F-loss) and tThen (R7 / S2) both have a CONCRETE
-- ground-type target (UnitTy, Loss respectively), unlike every group
-- proved so far (whose target was either fully generic or a non-`gnd`
-- type constructor). This makes their F-op sibling-refutation clause
-- get stuck the same way OpSem's own theorem-A4-1-op battled (Agda
-- can't decide `gnd(in′op) ≟ gnd unit` since `in′` is abstract) --
-- confirmed by direct experiment. theorem-A4-1-op's own fix (generic-atE
-- + shape-absurdE, keeping the target type itself a fresh, re-quantified
-- variable rather than the closed-over concrete one) doesn't integrate
-- cleanly with this file's own `pack`-based recursion without also
-- bundling σ/g/sub into pack's own Σ-chain. Deferred until tOp itself is
-- built (where this exact machinery is unavoidable anyway) so it can be
-- built once and reused here.
theorem-A4-2-core stp1@(R4 _) stp2 = theorem-A4-2-pack stp1 stp2

-- tGlocal group: R8 / S3. glocalE hides both ε₁ and ε₂ from its own
-- codomain σ, plus carries two opaque ⊆ᵉ-witnesses (sub1,sub2) -- rather
-- than a chain of fun-inj0-style extractions, this reuses R5-cont-
-- unique's own unglocal-key (Σ-packages ε₁,ε₂,sub1,sub2,g1 all at once)
-- + glocalE-arg-inj (the hole content) exactly as R5-cont-unique's own
-- S-glocal/S-glocal case does. Target here is σ itself (test's own top
-- implicit, fully generic -- unlike tLoss/tThen, never a concrete `gnd`
-- constant), so F-op needs no special opacity handling, same as tFst/
-- tSnd.
theorem-A4-2-core {Γ} {ε = ε} {sub = sub} {g = g} (R8 sub1 sub2 v g1) stp2 = helper stp2 refl
  where
  helper : ∀ {e r2 e2'} (s : _⊢_-[_]→_ {sub = sub} g e r2 e2') → e ≡ glocalE sub1 sub2 (val v) g1
         → pack (R8 sub1 sub2 {sub = sub} {g = g} v g1) ≡ pack s
  helper (R8 sub1' sub2' v' g1') eq with just-injective (cong unglocal-key eq)
  ... | refl with val-inj (glocalE-arg-inj eq)
  ...   | refl = refl
  helper (R1 f x) ()
  helper (R2-pair v' w') ()
  helper (R2-fst v' w') ()
  helper (R2-snd v' w') ()
  helper (R3 e v') ()
  helper (R4 r) ()
  helper (R6 h v1 v2) ()
  helper (R7 sub' v' e) ()
  helper (R9 v') ()
  helper (S1 sub' h v' stp) ()
  helper (S2 sub' g1' stp) ()
  helper (S3 sub1' sub2' g1' {e = eh2} {e' = eh2'} stp') eq with just-injective (cong unglocal-key eq)
  ... | refl with glocalE-arg-inj eq
  ...   | eq2 = ⊥-elim (theorem-A4-1-val (subst (λ □ → _⊢_-[_]→_ _ □ _ _) eq2 stp'))
  helper (S4 stp) ()
  helper (R5 sub' h v1 m op v2 k nh) ()
  helper (F-rule sub2' (F-fun _) stp) ()
  helper (F-rule sub2' (F-pairL _) stp) ()
  helper (F-rule sub2' (F-pairR _) stp) ()
  helper (F-rule sub2' F-fst stp) ()
  helper (F-rule sub2' F-snd stp) ()
  helper (F-rule sub2' (F-appL _) stp) ()
  helper (F-rule sub2' (F-appR _) stp) ()
  helper (F-rule sub2' (F-op _ _) stp) ()
  helper (F-rule sub2' F-loss stp) ()
  helper (F-rule sub2' (F-handleP h b) stp) ()
theorem-A4-2-core {Γ} {ε = ε} {g = g} (S3 sub1 sub2 g1 {e = eh} {e' = eh'} stp1') stp2 = helper stp2 refl
  where
  helper : ∀ {e r2 e2'} (s : _⊢_-[_]→_ {sub = ⊆ᵉ-refl} g e r2 e2') → e ≡ glocalE sub1 sub2 eh g1
         → pack (S3 sub1 sub2 g1 stp1') ≡ pack s
  helper (R8 sub1' sub2' v' g1') eq with just-injective (cong unglocal-key eq)
  ... | refl with glocalE-arg-inj eq
  ...   | eq2 = ⊥-elim (theorem-A4-1-val (subst (λ □ → _⊢_-[_]→_ _ □ _ _) (sym eq2) stp1'))
  helper (R1 f x) ()
  helper (R2-pair v w) ()
  helper (R2-fst v w) ()
  helper (R2-snd v w) ()
  helper (R3 e v) ()
  helper (R4 r) ()
  helper (R6 h v1 v2) ()
  helper (R7 sub' v e) ()
  helper (R9 v) ()
  helper (S1 sub' h v stp) ()
  helper (S2 sub' g1' stp) ()
  helper (S3 sub1' sub2' g1' stp2') eq with just-injective (cong unglocal-key eq)
  ... | refl with glocalE-arg-inj eq
  ...   | refl with theorem-A4-2-core stp1' stp2'
  ...     | inner-eq = cong (λ { (e , r , e' , t) → (glocalE sub1 sub2 e g1 , r , glocalE sub1 sub2 e' g1 , S3 sub1 sub2 g1 t) }) inner-eq
  helper (S4 stp) ()
  helper (R5 sub' h v1 m op v2 k nh) ()
  helper (F-rule sub2' (F-fun _) stp) ()
  helper (F-rule sub2' (F-pairL _) stp) ()
  helper (F-rule sub2' (F-pairR _) stp) ()
  helper (F-rule sub2' F-fst stp) ()
  helper (F-rule sub2' F-snd stp) ()
  helper (F-rule sub2' (F-appL _) stp) ()
  helper (F-rule sub2' (F-appR _) stp) ()
  helper (F-rule sub2' (F-op _ _) stp) ()
  helper (F-rule sub2' F-loss stp) ()
  helper (F-rule sub2' (F-handleP h b) stp) ()

-- tReset group: R9 / S4. resetE hides no type parameter (Γ⊢σ!ε→Γ⊢σ!ε,
-- σ visible on both sides), and S4 keeps the ambient sub/g unchanged
-- (unlike S3), so this is the simplest recursive group so far --
-- resetE-inj applies directly, no "-inj0" extraction needed. Target is
-- σ (generic), so F-op needs no special handling either.
theorem-A4-2-core {Γ} {ε = ε} {sub = sub} {g = g} (R9 v) stp2 = helper stp2 refl
  where
  helper : ∀ {e r2 e2'} (s : _⊢_-[_]→_ {sub = sub} g e r2 e2') → e ≡ resetE {ε = ε} (val v)
         → pack (R9 {sub = sub} {g = g} v) ≡ pack s
  helper (R9 .v) refl = refl
  helper (R1 f x) ()
  helper (R2-pair v' w') ()
  helper (R2-fst v' w') ()
  helper (R2-snd v' w') ()
  helper (R3 e v') ()
  helper (R4 r) ()
  helper (R6 h v1 v2) ()
  helper (R7 sub' v' e) ()
  helper (R8 sub1 sub2 v' g1) ()
  helper (S1 sub' h v' stp) ()
  helper (S2 sub' g1 stp) ()
  helper (S3 sub1 sub2 g1 stp) ()
  helper (S4 stp2) refl = ⊥-elim (theorem-A4-1-val stp2)
  helper (R5 sub' h v1 m op v2 k nh) ()
  helper (F-rule sub2' (F-fun _) stp) ()
  helper (F-rule sub2' (F-pairL _) stp) ()
  helper (F-rule sub2' (F-pairR _) stp) ()
  helper (F-rule sub2' F-fst stp) ()
  helper (F-rule sub2' F-snd stp) ()
  helper (F-rule sub2' (F-appL _) stp) ()
  helper (F-rule sub2' (F-appR _) stp) ()
  helper (F-rule sub2' (F-op _ _) stp) ()
  helper (F-rule sub2' F-loss stp) ()
  helper (F-rule sub2' (F-handleP h b) stp) ()
theorem-A4-2-core {Γ} {ε = ε} {sub = sub} {g = g} (S4 {e = eh} {e' = eh'} stp1') stp2 = helper stp2 refl
  where
  helper : ∀ {e r2 e2'} (s : _⊢_-[_]→_ {sub = sub} g e r2 e2') → e ≡ resetE eh
         → pack (S4 {sub = sub} {g = g} stp1') ≡ pack s
  helper (R9 v) eq with resetE-inj eq
  ... | eq2 = ⊥-elim (theorem-A4-1-val (subst (λ □ → _⊢_-[_]→_ _ □ _ _) (sym eq2) stp1'))
  helper (R1 f x) ()
  helper (R2-pair v w) ()
  helper (R2-fst v w) ()
  helper (R2-snd v w) ()
  helper (R3 e v) ()
  helper (R4 r) ()
  helper (R6 h v1 v2) ()
  helper (R7 sub' v e) ()
  helper (R8 sub1 sub2 v g1) ()
  helper (S1 sub' h v stp) ()
  helper (S2 sub' g1 stp) ()
  helper (S3 sub1 sub2 g1 stp) ()
  helper (S4 stp2') eq with resetE-inj eq
  ... | refl with theorem-A4-2-core stp1' stp2'
  ...   | inner-eq = cong (λ { (e , r , e' , t) → (resetE e , 0# , resetE e' , S4 t) }) inner-eq
  helper (R5 sub' h v1 m op v2 k nh) ()
  helper (F-rule sub2' (F-fun _) stp) ()
  helper (F-rule sub2' (F-pairL _) stp) ()
  helper (F-rule sub2' (F-pairR _) stp) ()
  helper (F-rule sub2' F-fst stp) ()
  helper (F-rule sub2' F-snd stp) ()
  helper (F-rule sub2' (F-appL _) stp) ()
  helper (F-rule sub2' (F-appR _) stp) ()
  helper (F-rule sub2' (F-op _ _) stp) ()
  helper (F-rule sub2' F-loss stp) ()
  helper (F-rule sub2' (F-handleP h b) stp) ()

-- tPair group: R2-pair / F-pairL / F-pairR -- the first 3-member group.
-- pair hides no type parameter (σ,τ both visible in σ`×τ), so pair-
-- inj1/pair-inj2 apply directly, no "-inj0" step. Target is σ0`×τ0 (a
-- *different* Ty constructor from `gnd`, `_⇒_!_`), so every gnd-headed
-- rule (R1,R4,R7,S2,F-fun,F-op,F-loss) is auto-omittable via type-level
-- clash alone, mirroring tFun's own omission of R2-pair/F-pairL/F-pairR
-- -- everything else still needs an explicit `()`.
theorem-A4-2-core {Γ} {ε = ε} {sub = sub} {g = g} (R2-pair v w) stp2 = helper stp2 refl
  where
  helper : ∀ {e r2 e2'} (s : _⊢_-[_]→_ {sub = sub} g e r2 e2') → e ≡ pair {ε = ε} (val v) (val w)
         → pack (R2-pair {sub = sub} {g = g} v w) ≡ pack s
  helper (R2-pair .v .w) refl = refl
  helper (R2-fst v' w') ()
  helper (R2-snd v' w') ()
  helper (R3 e v') ()
  helper (R6 h v1 v2) ()
  helper (R8 sub1 sub2 v' g1) ()
  helper (R9 v') ()
  helper (S1 sub' h v' stp) ()
  helper (S3 sub1 sub2 g1 stp) ()
  helper (S4 stp) ()
  helper (R5 sub' h v1 m op v2 k nh) ()
  helper (F-rule sub2' (F-pairL _) stp) eq with pair-inj1 eq
  ... | eq2 = ⊥-elim (theorem-A4-1-val (subst (λ □ → _⊢_-[_]→_ _ □ _ _) eq2 stp))
  helper (F-rule sub2' (F-pairR _) stp) eq with pair-inj2 eq
  ... | eq2 = ⊥-elim (theorem-A4-1-val (subst (λ □ → _⊢_-[_]→_ _ □ _ _) eq2 stp))
  helper (F-rule sub2' F-fst stp) ()
  helper (F-rule sub2' F-snd stp) ()
  helper (F-rule sub2' (F-appL _) stp) ()
  helper (F-rule sub2' (F-appR _) stp) ()
  helper (F-rule sub2' (F-handleP h b) stp) ()
theorem-A4-2-core {Γ} {ε = ε} {sub = sub} {g = g} (F-rule sub1 (F-pairL e₂) {e = eh} {e' = eh'} stp1') stp2 = helper stp2 refl
  where
  helper : ∀ {e r2 e2'} (s : _⊢_-[_]→_ {sub = sub} g e r2 e2') → e ≡ pair eh e₂
         → pack (F-rule sub1 (F-pairL e₂) stp1') ≡ pack s
  helper (R2-pair v' w') eq with pair-inj1 eq
  ... | eq2 = ⊥-elim (theorem-A4-1-val (subst (λ □ → _⊢_-[_]→_ _ □ _ _) (sym eq2) stp1'))
  helper (R2-fst v w) ()
  helper (R2-snd v w) ()
  helper (R3 e v) ()
  helper (R6 h v1 v2) ()
  helper (R8 sub1' sub2 v g1) ()
  helper (R9 v) ()
  helper (S1 sub' h v stp) ()
  helper (S3 sub1' sub2 g1 stp) ()
  helper (S4 stp) ()
  helper (R5 sub' h v1 m op v2 k nh) ()
  helper (F-rule sub2' (F-pairL e₂') stp2') eq with pair-inj1 eq | pair-inj2 eq
  ... | eq2 | eq3 with eq2 | eq3
  ...   | refl | refl with theorem-A4-2-core stp1' stp2'
  ...     | inner-eq = cong (λ { (e , r , e' , t) → (pair e e₂ , r , pair e' e₂ , F-rule sub1 (F-pairL e₂) t) }) inner-eq
  helper (F-rule sub2' (F-pairR _) stp) eq with pair-inj1 eq
  ... | eq2 = ⊥-elim (theorem-A4-1-val (subst (λ □ → _⊢_-[_]→_ _ □ _ _) (sym eq2) stp1'))
  helper (F-rule sub2' F-fst stp) ()
  helper (F-rule sub2' F-snd stp) ()
  helper (F-rule sub2' (F-appL _) stp) ()
  helper (F-rule sub2' (F-appR _) stp) ()
  helper (F-rule sub2' (F-handleP h b) stp) ()
theorem-A4-2-core {Γ} {ε = ε} {sub = sub} {g = g} (F-rule sub1 (F-pairR v1) {e = eh} {e' = eh'} stp1') stp2 = helper stp2 refl
  where
  helper : ∀ {e r2 e2'} (s : _⊢_-[_]→_ {sub = sub} g e r2 e2') → e ≡ pair (val v1) eh
         → pack (F-rule sub1 (F-pairR v1) stp1') ≡ pack s
  helper (R2-pair v' w') eq with pair-inj2 eq
  ... | eq2 = ⊥-elim (theorem-A4-1-val (subst (λ □ → _⊢_-[_]→_ _ □ _ _) (sym eq2) stp1'))
  helper (R2-fst v w) ()
  helper (R2-snd v w) ()
  helper (R3 e v) ()
  helper (R6 h v1' v2) ()
  helper (R8 sub1' sub2 v g1) ()
  helper (R9 v) ()
  helper (S1 sub' h v stp) ()
  helper (S3 sub1' sub2 g1 stp) ()
  helper (S4 stp) ()
  helper (R5 sub' h v1' m op v2 k nh) ()
  helper (F-rule sub2' (F-pairL _) stp) eq with pair-inj1 eq
  ... | eq2 = ⊥-elim (theorem-A4-1-val (subst (λ □ → _⊢_-[_]→_ _ □ _ _) eq2 stp))
  helper (F-rule sub2' (F-pairR v1'') stp2') eq with val-inj (pair-inj1 eq) | pair-inj2 eq
  ... | eq2 | eq3 with eq2 | eq3
  ...   | refl | refl with theorem-A4-2-core stp1' stp2'
  ...     | inner-eq = cong (λ { (e , r , e' , t) → (pair (val v1) e , r , pair (val v1) e' , F-rule sub1 (F-pairR v1) t) }) inner-eq
  helper (F-rule sub2' F-fst stp) ()
  helper (F-rule sub2' F-snd stp) ()
  helper (F-rule sub2' (F-appL _) stp) ()
  helper (F-rule sub2' (F-appR _) stp) ()
  helper (F-rule sub2' (F-handleP h b) stp) ()

-- The remaining 9 top-level shapes still aren't proved -- delegate to
-- theorem-A4-2-pack (see its own comment above for why this, rather than
-- theorem-A4-2 itself, is what a fully-generic-`e` function like this
-- one needs to call).
theorem-A4-2-core stp1@(R3 _ _) stp2 = theorem-A4-2-pack stp1 stp2
theorem-A4-2-core stp1@(R6 _ _ _) stp2 = theorem-A4-2-pack stp1 stp2
theorem-A4-2-core stp1@(R7 _ _ _) stp2 = theorem-A4-2-pack stp1 stp2
theorem-A4-2-core stp1@(S1 _ _ _ _) stp2 = theorem-A4-2-pack stp1 stp2
theorem-A4-2-core stp1@(S2 _ _ _) stp2 = theorem-A4-2-pack stp1 stp2
theorem-A4-2-core stp1@(R5 _ _ _ _ _ _ _ _) stp2 = theorem-A4-2-pack stp1 stp2
theorem-A4-2-core stp1@(F-rule _ (F-appL _) _) stp2 = theorem-A4-2-pack stp1 stp2
theorem-A4-2-core stp1@(F-rule _ (F-appR _) _) stp2 = theorem-A4-2-pack stp1 stp2
theorem-A4-2-core stp1@(F-rule _ (F-op _ _) _) stp2 = theorem-A4-2-pack stp1 stp2
theorem-A4-2-core stp1@(F-rule _ F-loss _) stp2 = theorem-A4-2-pack stp1 stp2
theorem-A4-2-core stp1@(F-rule _ (F-handleP _ _) _) stp2 = theorem-A4-2-pack stp1 stp2

theorem-A4-2-proved : ∀ {Γ σ ε εg} {sub : εg ⊆ᵉ ε} {g : LC Γ σ εg} {e : Γ ⊢ σ ! ε} {r1 r2 : R} {e1' e2' : Γ ⊢ σ ! ε}
                     (stp1 : _⊢_-[_]→_ {sub = sub} g e r1 e1') (stp2 : _⊢_-[_]→_ {sub = sub} g e r2 e2')
                   → stp1 ≅ stp2
theorem-A4-2-proved stp1 stp2 = pack-≡-to-≅ (theorem-A4-2-core stp1 stp2)
