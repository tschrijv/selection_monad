-- Porting paper.tex §7 ("Porting Appendix B: Correctness Proofs") to the
-- Agda encoding, lemma by lemma, in the source's own order. Each lemma
-- below is labelled with its name in paper.tex (which is itself "hat-Lemma
-- B.n" of the arXiv paper's Appendix B) so the two can be read side by
-- side.
open import Domains using (Sig)

module Proofs (Sg : Sig) where

open Sig Sg
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
open import Axiom.Extensionality.Propositional using (Extensionality)

-- Function extensionality. Needed because Ŵ's `node` case, Env, Ŝ, and A
-- (in the handler algebra) are all genuinely function-typed, so many
-- equations between them are not provable by mere computation. This is a
-- standard, widely-used postulate (consistent with Agda's theory) -- the
-- source papers work in ordinary set theory, where it holds for free.
postulate
  funext  : ∀ {a b} → Extensionality a b
  ifunext : ∀ {a b} {A : Set a} {B : A → Set b} {f g : ∀ {x} → B x}
          → (∀ x → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})

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
-- Fix a handler h, ρ, γ as in §5, and consider A = ⟦par⟧ → Ŵ_ε(⟦σ'⟧), the
-- carrier of the layered εℓ-algebra `algebra` built in handlerSem, whose
-- action is exactly "tell, applied pointwise": act r f = λp. tell r (f p).
-- The lemma is: s†Ŵεℓ ∘ tell(r) = tell(r)^P ∘ s†Ŵεℓ, i.e. extending any
-- s : X → A over a tell(r)-prefixed tree agrees with tell(r)ing the result
-- pointwise. The source's proof of the analogous (original) fact needs a
-- uniqueness-of-extension argument, because there r·(-) acts on every leaf
-- of F_ε(R×X) simultaneously and one must invoke commutativity of the
-- action with ψ; here tell only ever touches the *root* loss slot, so the
-- fact is immediate from tell's own additivity (tell-+ below), with no
-- commutation needed anywhere -- exactly as the source remarks.
-- ---------------------------------------------------------------------

-- tell(r) then tell(s) is tell(r+s) (needs +-assoc; this is the "additive
-- action law" 0·y=y, r·(s·y)=(r+s)·y of §3.2, specialised to Ŵ's own
-- native action).
tell-+ : ∀ {ε X} (r s : R) (w : Ŵ ε X) → tell (r + s) w ≡ tell r (tell s w)
tell-+ r s (leaf r₀ x)        = cong (λ z → leaf z x) (+-assoc r s r₀)
tell-+ r s (node m op r₀ o κ) = cong (λ z → node m op z o κ) (+-assoc r s r₀)

-- tell commutes with bind̂'s own binding: tell r only ever touches the
-- root, so bind̂'s ext̂ and tell's root-update commute regardless of what
-- K does with the leaf value.
tell-bind̂-comm : ∀ {ε X Y} (r : R) (w : Ŵ ε X) (K : X → Ŵ ε Y) → bind̂ (tell r w) K ≡ tell r (bind̂ w K)
tell-bind̂-comm r (leaf r₀ x) K        = tell-+ r r₀ (K x)
tell-bind̂-comm r (node m op r₀ o κ) K = tell-+ r r₀ (node m op 0# o (λ a → bind̂ (κ a) K))

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

-- ---------------------------------------------------------------------
-- Ŝ's left unit law, bind̂ˢ f (η̂ˢ x) = f x: not itself one of the
-- numbered lemmas, but the monad law Lemma B.4's proof invokes directly
-- ("the unit law for let_Sε"), so we prove it once here.
-- ---------------------------------------------------------------------

tell-0 : ∀ {ε X} (w : Ŵ ε X) → tell 0# w ≡ w
tell-0 (leaf r x)        = cong (λ z → leaf z x) (+-identityˡ r)
tell-0 (node m op r o κ) = cong (λ z → node m op z o κ) (+-identityˡ r)

bindˢ-unitˡ : ∀ {ε X Y} (f : X → Ŝ ε Y) (x : X) → bind̂ˢ f (η̂ˢ x) ≡ f x
bindˢ-unitˡ f x = funext (λ γ → tell-0 (f x γ))

-- ---------------------------------------------------------------------
-- bump/collectX algebra, needed later for Theorem B.9's THEN case (S2).
-- ---------------------------------------------------------------------

-- bump_r ∘ bump_s = bump_{r+s} (paper's own stated fact, paper.tex line 288).
bump-fusion : ∀ {ε X} (r s : R) (T : Ŵ ε (X × R)) → bump r (bump s T) ≡ bump (r + s) T
bump-fusion r s (leaf r₀ (x , y))  = cong (λ z → leaf r₀ (x , z)) (sym (+-assoc r s y))
bump-fusion r s (node m op r₀ o κ) = cong (node m op r₀ o) (funext (λ a → bump-fusion r s (κ a)))

-- bump r (collectX S) ≡ collectX (tell r S): the accumulated-loss field
-- collectX pairs onto every leaf is exactly what bump adds to.
bump-collectX-comm : ∀ {ε X} (r : R) (S : Ŵ ε X) → bump r (collectX S) ≡ collectX (tell r S)
bump-collectX-comm r (leaf r₀ x)        = refl
bump-collectX-comm r (node m op r₀ o κ) = cong (node m op 0# o) (funext (λ a → bump-fusion r r₀ (collectX (κ a))))

-- Bumping a collectX-paired tree before feeding it through a continuation
-- that only ever *adds* the accumulated-loss component into something is
-- the same as not bumping and adding the bump amount directly at the use
-- site. (This is the correct shape of "push a bump past a bind̂" -- an
-- earlier attempt that instead tried to pull the bump amount OUT as a
-- separate outer `tell` was genuinely false, see B5Core.agda's
-- bump-outside-refuted; this one holds unconditionally, since it never
-- has to relate two DIFFERENT trees the way collapse/Lsem did.)
bump-shift : ∀ {ε X Y} (bumpAmt : R) (T : Ŵ ε (X × R)) (h : X → R → Ŵ ε Y)
  → bind̂ (bump bumpAmt T) (λ { (a , r1) → h a r1 }) ≡ bind̂ T (λ { (a , r1) → h a (bumpAmt + r1) })
bump-shift bumpAmt (leaf r₀ (x , y)) h = refl
bump-shift bumpAmt (node m op r₀ o κ) h =
  cong (tell r₀) (cong (node m op 0# o) (funext (λ a → bump-shift bumpAmt (κ a) h)))

-- bump 0# is the identity.
bump-0 : ∀ {ε X} (T : Ŵ ε (X × R)) → bump 0# T ≡ T
bump-0 (leaf r₀ (x , y))  = cong (λ z → leaf r₀ (x , z)) (+-identityˡ y)
bump-0 (node m op r₀ o κ) = cong (node m op r₀ o) (funext (λ a → bump-0 (κ a)))

-- bind̂ after mapŴ is bind̂ with the composed continuation (standard
-- functor/monad law).
bind̂-mapŴ : ∀ {ε X Y Z} (g : X → Y) (w : Ŵ ε X) (f : Y → Ŵ ε Z) → bind̂ (mapŴ g w) f ≡ bind̂ w (λ x → f (g x))
bind̂-mapŴ g (leaf r x)        f = refl
bind̂-mapŴ g (node m op r o κ) f = cong (tell r) (cong (node m op 0# o) (funext (λ a → bind̂-mapŴ g (κ a) f)))

-- tell and mapŴ commute unconditionally (tell only ever touches a
-- root-loss slot; mapŴ only ever touches leaf payloads -- the two are
-- structurally independent, unlike tell/collapse or mapŴ/shift).
tell-mapŴ-comm : ∀ {ε X Y} (r : R) (f : X → Y) (W : Ŵ ε X) → tell r (mapŴ f W) ≡ mapŴ f (tell r W)
tell-mapŴ-comm r f (leaf r₀ x)        = refl
tell-mapŴ-comm r f (node m op r₀ o κ) = refl

-- mapŴ is functorial (standard law).
mapŴ-∘ : ∀ {ε X Y Z} (f : Y → Z) (g : X → Y) (W : Ŵ ε X) → mapŴ f (mapŴ g W) ≡ mapŴ (λ x → f (g x)) W
mapŴ-∘ f g (leaf r x)        = refl
mapŴ-∘ f g (node m op r o κ) = cong (node m op r o) (funext (λ a → mapŴ-∘ f g (κ a)))

-- Consequently mapŴ can be pulled out from inside a bind̂'s own
-- continuation to wrap the whole bind̂ instead (needed for the
-- EXPERIMENTAL mapŴ-based Esem(thenE) variant: unlike the collectX-based
-- `shift`, mapŴ commutes past bind̂ cleanly, with no root-loss
-- redistribution subtlety at all).
bind̂-mapŴ-after : ∀ {ε X Y Z} (T : Ŵ ε X) (k : X → Ŵ ε Y) (f : Y → Z) → bind̂ T (λ x → mapŴ f (k x)) ≡ mapŴ f (bind̂ T k)
bind̂-mapŴ-after (leaf r x) k f = tell-mapŴ-comm r f (k x)
bind̂-mapŴ-after (node m op r o κ) k f =
  trans (cong (tell r) (cong (node m op 0# o) (funext (λ a → bind̂-mapŴ-after (κ a) k f))))
        (tell-mapŴ-comm r f (node m op 0# o (λ a → bind̂ (κ a) k)))

-- bind̂ associativity (standard monad law).
bind̂-assoc : ∀ {ε X Y Z} (w : Ŵ ε X) (f : X → Ŵ ε Y) (g : Y → Ŵ ε Z)
           → bind̂ (bind̂ w f) g ≡ bind̂ w (λ x → bind̂ (f x) g)
bind̂-assoc (leaf r x)        f g = tell-bind̂-comm r (f x) g
bind̂-assoc (node m op r o κ) f g =
  trans (tell-bind̂-comm r (node m op 0# o (λ a → bind̂ (κ a) f)) g)
        (cong (tell r) (trans (tell-0 _) (cong (node m op 0# o) (funext (λ a → bind̂-assoc (κ a) f g)))))

-- collectX distributes over bind̂, generalised with an additive offset
-- threaded through the accumulator (needed for the node case, same
-- pattern as bump-shift/bump-collectX-comm above).
collectX-bind̂-fusion-gen : ∀ {ε X Y} (off : R) (w : Ŵ ε X) (f : X → Ŵ ε Y)
  → bind̂ (collectX w) (λ { (a , r1) → bump (off + r1) (collectX (f a)) }) ≡ bump off (collectX (bind̂ w f))
collectX-bind̂-fusion-gen off (leaf r x) f =
  trans (tell-0 _) (trans (sym (bump-fusion off r (collectX (f x)))) (cong (bump off) (bump-collectX-comm r (f x))))
collectX-bind̂-fusion-gen off (node m op r o κ) f = trans lhsEq (sym rhsEq)
  where
  lhsEq : bind̂ (collectX (node m op r o κ)) (λ { (a , r1) → bump (off + r1) (collectX (f a)) })
        ≡ node m op 0# o (λ a → bump (off + r) (collectX (bind̂ (κ a) f)))
  lhsEq = trans (tell-0 _)
                (cong (node m op 0# o) (funext (λ a →
                  trans (bump-shift r (collectX (κ a)) (λ a' r1 → bump (off + r1) (collectX (f a'))))
                        (trans (cong (bind̂ (collectX (κ a)))
                                     (funext (λ { (a' , r1) → cong (λ z → bump z (collectX (f a'))) (sym (+-assoc off r r1)) })))
                               (collectX-bind̂-fusion-gen (off + r) (κ a) f)))))
  rhsEq : bump off (collectX (bind̂ (node m op r o κ) f))
        ≡ node m op 0# o (λ a → bump (off + r) (collectX (bind̂ (κ a) f)))
  rhsEq = trans (cong (bump off) (sym (bump-collectX-comm r (node m op 0# o (λ a → bind̂ (κ a) f)))))
                (cong (node m op 0# o) (funext (λ a →
                  trans (cong (bump off) (bump-fusion r 0# (collectX (bind̂ (κ a) f))))
                        (trans (bump-fusion off (r + 0#) (collectX (bind̂ (κ a) f)))
                               (cong (λ z → bump z (collectX (bind̂ (κ a) f))) (cong (off +_) (+-identityʳ r)))))))

collectX-bind̂-fusion : ∀ {ε X Y} (w : Ŵ ε X) (f : X → Ŵ ε Y)
  → collectX (bind̂ w f) ≡ bind̂ (collectX w) (λ { (a , r1) → bump r1 (collectX (f a)) })
collectX-bind̂-fusion w f =
  trans (sym (bump-0 _))
        (trans (sym (collectX-bind̂-fusion-gen 0# w f))
               (cong (bind̂ (collectX w)) (funext (λ { (a , r1) → cong (λ z → bump z (collectX (f a))) (+-identityˡ r1) }))))

-- mapŴ's "tack on 0#" combinator commutes past bump the same way it
-- commutes past everything else that only touches the accumulator slot.
map-bump-comm : ∀ {ε X} (off r0 : R) (T : Ŵ ε (X × R))
  → mapŴ {Y = (X × R) × R} (λ { (x , r) → (x , off + r) , 0# }) (bump r0 T)
  ≡ mapŴ {Y = (X × R) × R} (λ { (x , r) → (x , (off + r0) + r) , 0# }) T
map-bump-comm off r0 (leaf r₀ (x , y))  = cong (λ z → leaf r₀ ((x , z) , 0#)) (sym (+-assoc off r0 y))
map-bump-comm off r0 (node m op r₀ o κ) = cong (node m op r₀ o) (funext (λ a → map-bump-comm off r0 (κ a)))

-- collectX (bump off (collectX S)) simplifies to a plain mapŴ, since
-- collectX S is already fully flat (every internal root 0#) and bump
-- never touches roots -- so a further collectX has nothing left to
-- redistribute beyond adding off into the accumulator it finds.
collectX-bump-collectX : ∀ {ε X} (off : R) (S : Ŵ ε X)
  → collectX (bump off (collectX S)) ≡ mapŴ (λ { (x , r) → (x , off + r) , 0# }) (collectX S)
collectX-bump-collectX off (leaf r₀ x)  = refl
collectX-bump-collectX off (node m op r₀ o κ) =
  cong (node m op 0# o) (funext (λ a →
    trans (bump-0 (collectX (bump off (bump r₀ (collectX (κ a))))))
          (trans (cong collectX (bump-fusion off r₀ (collectX (κ a))))
                 (trans (collectX-bump-collectX (off + r₀) (κ a))
                        (sym (map-bump-comm off r₀ (collectX (κ a))))))))

-- collectX applied twice: once collectX has pushed all accumulated loss
-- down to the leaves (zeroing every node's own root along the way), a
-- second pass has nothing left to redistribute -- it just tacks on a
-- trivial extra 0# accumulator at each leaf.
collectX-idem : ∀ {ε X} (W : Ŵ ε X) → collectX (collectX W) ≡ mapŴ (λ { (x , r) → (x , r) , 0# }) (collectX W)
collectX-idem (leaf r x)        = refl
collectX-idem {ε} {X} (node m op r o κ) = trans lhsEq (sym rhsEq)
  where
  target : Ŵ ε ((X × R) × R)
  target = node m op 0# o (λ a → mapŴ (λ { (x , r') → (x , r + r') , 0# }) (collectX (κ a)))

  lhsEq : collectX (collectX (node m op r o κ)) ≡ target
  lhsEq = cong (node m op 0# o) (funext (λ a →
            trans (bump-0 (collectX (bump r (collectX (κ a)))))
                  (collectX-bump-collectX r (κ a))))

  rhsEq : mapŴ (λ { (x , r') → (x , r') , 0# }) (collectX (node m op r o κ)) ≡ target
  rhsEq = cong (node m op 0# o) (funext (λ a →
            trans (cong (λ h → mapŴ h (bump r (collectX (κ a))))
                        (funext (λ { (x , r') → cong (λ z → (x , z) , 0#) (sym (+-identityˡ r')) })))
                  (trans (map-bump-comm 0# r (collectX (κ a)))
                         (cong (λ h → mapŴ h (collectX (κ a)))
                               (funext (λ { (x , r') → cong (λ z → (x , z) , 0#) (cong (_+ r') (+-identityˡ r)) }))))))

-- shift r T: run T, add r into whatever loss it ultimately reports at
-- each leaf, keeping any tell-loss already accumulated along the way
-- (built via collectX, so unlike collapse it never discards anything).
shift : ∀ {ε} → R → Ŵ ε R → Ŵ ε R
shift r T = bind̂ (collectX T) (λ { (r3 , r2) → tell r2 (η̂ (r + r3)) })

-- shift(r+s) ≡ shift r ∘ shift s. Proved via collectX-bind̂-fusion +
-- collectX-idem rather than by direct induction on T -- the direct
-- induction gets stuck because shift (built from collectX) redistributes
-- a node's own accumulated loss down into its leaves, so "match the
-- root, cong on the children" does not apply the way it did for
-- bump-shift; going through collectX-idem sidesteps that entirely by
-- never re-examining T's own node structure.
shift-fusion : ∀ {ε} (r s : R) (T : Ŵ ε R) → shift (r + s) T ≡ shift r (shift s T)
shift-fusion r s T = trans lhsEq (sym rhsEq)
  where
  k : R × R → Ŵ _ R
  k (r3 , r2) = tell r2 (η̂ (s + r3))

  -- collectX(shift s T), reduced down to a single bind̂ over collectX T.
  collectX-shift-s : collectX (shift s T) ≡ bind̂ (collectX T) (λ { (r3 , r2) → leaf 0# ((s + r3) , (r2 + 0#)) })
  collectX-shift-s =
    trans (collectX-bind̂-fusion (collectX T) k)
          (trans (cong (bind̂ (collectX (collectX T))) (funext (λ { ((r3 , r2) , r1') → refl })))
                 (trans (cong (λ w → bind̂ w (λ { ((r3 , r2) , r1') → bump r1' (collectX (k (r3 , r2))) })) (collectX-idem T))
                        (trans (bind̂-mapŴ (λ { (x , r) → (x , r) , 0# }) (collectX T)
                                          (λ { ((r3 , r2) , r1') → bump r1' (collectX (k (r3 , r2))) }))
                               (cong (bind̂ (collectX T)) (funext (λ { (r3 , r2) →
                                 trans (bump-0 (collectX (k (r3 , r2))))
                                       (sym (bump-collectX-comm r2 (η̂ (s + r3)))) }))))))

  rhsEq : shift r (shift s T) ≡ bind̂ (collectX T) (λ { (r3 , r2) → leaf ((r2 + 0#) + 0#) (r + (s + r3)) })
  rhsEq = trans (cong (λ w → bind̂ w (λ { (r3' , r2') → tell r2' (η̂ (r + r3')) })) collectX-shift-s)
                (trans (bind̂-assoc (collectX T) (λ { (r3 , r2) → leaf 0# ((s + r3) , (r2 + 0#)) })
                                                 (λ { (r3' , r2') → tell r2' (η̂ (r + r3')) }))
                       (cong (bind̂ (collectX T)) (funext (λ { (r3 , r2) → tell-0 _ }))))

  lhsEq : shift (r + s) T ≡ bind̂ (collectX T) (λ { (r3 , r2) → leaf ((r2 + 0#) + 0#) (r + (s + r3)) })
  lhsEq = cong (bind̂ (collectX T)) (funext (λ { (r3 , r2) →
            cong₂ leaf (sym (+-identityʳ _)) (+-assoc r s r3) }))

-- shift commutes with THEN's own "bind̂ over collectX" shape: shifting
-- each branch's own contribution by r before combining is the same as
-- combining first and shifting the whole result by r. This -- not a
-- fully general "shift commutes with an arbitrary bind̂" (which is false,
-- since an arbitrary w's own accumulated loss would need separate
-- bookkeeping) -- is exactly the fact Theorem B.9's (S2) case needs.
shift-thenE-comm : ∀ {ε X} (r : R) (W' : Ŵ ε X) (h : X → R → Ŵ ε R)
  → bind̂ (collectX W') (λ { (a , r1) → shift r (h a r1) }) ≡ shift r (bind̂ (collectX W') (λ { (a , r1) → h a r1 }))
shift-thenE-comm r W' h =
  sym (trans (cong (λ w → bind̂ w (λ { (r3' , r2') → tell r2' (η̂ (r + r3')) })) collectXStep)
             (bind̂-assoc (collectX W') (λ { (a , r1) → collectX (h a r1) }) (λ { (r3' , r2') → tell r2' (η̂ (r + r3')) })))
  where
  collectXStep : collectX (bind̂ (collectX W') (λ { (a , r1) → h a r1 })) ≡ bind̂ (collectX W') (λ { (a , r1) → collectX (h a r1) })
  collectXStep =
    trans (collectX-bind̂-fusion (collectX W') (λ { (a , r1) → h a r1 }))
          (trans (cong (λ w → bind̂ w (λ { ((a , r1) , r1') → bump r1' (collectX (h a r1)) })) (collectX-idem W'))
                 (trans (bind̂-mapŴ (λ { (x , r) → (x , r) , 0# }) (collectX W')
                                   (λ { ((a , r1) , r1') → bump r1' (collectX (h a r1)) }))
                        (cong (bind̂ (collectX W')) (funext (λ { (a , r1) → bump-0 (collectX (h a r1)) })))))

-- ---------------------------------------------------------------------
-- RootZero: a Ŵ-tree never has any nonzero "tell"-accumulated loss
-- sitting in a root/node-r field -- only mapŴ-style leaf-payload bumps
-- are allowed to carry information. This is the invariant identified
-- while investigating theorem-B9-R5's fl/l1v mismatch (see the comment
-- above theorem-B9-R5-gen's postulate, "FOURTH FINDING"): R5's own
-- fl := (with h from p handle K[y]) ▶ g reification and the handler
-- algebra's own l1 formula (which only ever consults g through `collapse`,
-- discarding any root loss) provably disagree whenever the AMBIENT loss
-- continuation g's own semantic value has nonzero root loss -- but g is
-- NEVER actually arbitrary in theorem-B9's real induction: it starts as
-- zeroLC and is rebuilt ONLY via (F-rule)/(S1)'s own vabs(thenE...)
-- construction, which (below) provably PRESERVES RootZero regardless of
-- what the wrapped expression itself reports via lossE.
-- ---------------------------------------------------------------------

RootZero : ∀ {ε X} → Ŵ ε X → Set
RootZero (leaf r x)        = r ≡ 0#
RootZero (node m op r o κ) = (r ≡ 0#) × (∀ a → RootZero (κ a))

-- widenŴ only ever relabels a node's own membership witness -- it never
-- touches any r field at all, at leaves or nodes.
RootZero-widenŴ : ∀ {ε ε' X} (sub : ε ⊆ᵉ ε') (W : Ŵ ε X) → RootZero W → RootZero (widenŴ sub W)
RootZero-widenŴ sub (leaf r x)        rz = rz
RootZero-widenŴ sub (node m op r o κ) (rz , rzκ) = rz , (λ a → RootZero-widenŴ sub (κ a) (rzκ a))

-- mapŴ only ever touches the final leaf payload -- root/node-r fields are
-- carried through completely unchanged.
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

-- Same statement, top-level (Denotational.agda's handlerΨ node-case
-- construction and lemma-B8's φ̂ˢ-shaped nodes both need it directly, not
-- just as a `where`-local helper of RootZero-collectX).
RootZero-bump : ∀ {ε X} (s : R) (D : Ŵ ε (X × R)) → RootZero D → RootZero (bump s D)
RootZero-bump s (leaf r (x , y))        rz = rz
RootZero-bump s (node m op r o κ) (rz , rzκ) = rz , (λ a → RootZero-bump s (κ a) (rzκ a))

-- The homomorphic extension of a RootZero tree, over any leaf-function
-- that itself only ever produces RootZero results, is RootZero -- act's
-- own "tell r" at each level is applied at r≡0# (from D's own RootZero),
-- so it never actually adds anything (tell-0), leaving whatever RootZero
-- structure ψ/f already produced untouched.
RootZero-ext̂-Ŵ-alg : ∀ {ε X Y} (D : Ŵ ε X) (F : X → Ŵ ε Y)
                   → RootZero D → (∀ x → RootZero (F x)) → RootZero (ext̂ Ŵ-alg F D)
RootZero-ext̂-Ŵ-alg (leaf r x) F rz rzF = subst RootZero (sym eq) (rzF x)
  where
  eq : tell r (F x) ≡ F x
  eq = trans (cong (λ z → tell z (F x)) rz) (tell-0 (F x))
RootZero-ext̂-Ŵ-alg (node m op r o κ) F (rz , rzκ) rzF = subst RootZero (sym eq) rzNode
  where
  κ'' : _ → _
  κ'' = λ a → ext̂ Ŵ-alg F (κ a)
  eq : tell r (node m op 0# o κ'') ≡ node m op 0# o κ''
  eq = trans (cong (λ z → tell z (node m op 0# o κ'')) rz) (tell-0 (node m op 0# o κ''))
  rzNode : RootZero (node m op 0# o κ'')
  rzNode = refl , (λ a → RootZero-ext̂-Ŵ-alg (κ a) F (rzκ a) rzF)

-- ---------------------------------------------------------------------
-- The invariant-preservation half: theorem-B9's own induction NEVER
-- builds a "new" ambient loss continuation except via (F-rule)/(S1),
-- both of which construct exactly vabs(thenE sub e (weaken1V g)) for
-- some e (S2/S3/S4 reuse a SEPARATE, already-given g1 without deriving
-- it from the outer g at all; R5 is a one-step axiom with no recursive
-- premise). This lemma shows that construction ALWAYS yields a RootZero
-- result, for ANY e whatsoever (even one that reports nonzero loss via
-- lossE, e.g. retApplied h v when h's own ret uses lossE, the ordinary
-- and expected case) -- PROVIDED the tail g already has RootZero at
-- every value it's applied to. zeroLC (the base case every derivation
-- actually starts from) trivially has RootZero (its body is a bare
-- value, Esem(val v)ρ = η̂ˢ(Vsem v ρ), ignoring its own γ entirely).
-- ---------------------------------------------------------------------

RootZero-thenE-wrap : ∀ {Γ σ α ε₁ ε} (sub : ε₁ ⊆ᵉ ε) (e1 : (Γ , σ) ⊢ α ! ε) (g' : LC (Γ , σ) α ε₁)
                    (ρ : Env Γ) (x : ⟦ σ ⟧) (γ0 : ⟦ Loss ⟧ → Ŵ ε ⊤)
                  → (∀ a → RootZero (Vsem g' (ρ ,, x) a (λ _ → η̂ tt)))
                  → RootZero (Vsem (vabs (thenE sub e1 g')) ρ x γ0)
RootZero-thenE-wrap {ε = ε} sub e1 g' ρ x γ0 rzg' =
  RootZero-ext̂-Ŵ-alg (collectX (Esem e1 (ρ ,, x) (λ a → widenŴ sub (Lsem g' (ρ ,, x) a))))
                      (λ { (a , r1) → mapŴ (r1 +_) (widenŴ sub (Vsem g' (ρ ,, x) a (λ _ → η̂ tt))) })
                      (RootZero-collectX (Esem e1 (ρ ,, x) (λ a → widenŴ sub (Lsem g' (ρ ,, x) a))))
                      (λ { (a , r1) → RootZero-mapŴ (r1 +_) (widenŴ sub (Vsem g' (ρ ,, x) a (λ _ → η̂ tt)))
                                        (RootZero-widenŴ sub (Vsem g' (ρ ,, x) a (λ _ → η̂ tt)) (rzg' a)) })

-- zeroLC's own body is a bare value, so its Vsem is γ0-constant and
-- trivially RootZero (root 0# by construction, no computation at all).
RootZero-zeroLC : ∀ {Γ σ ε} (ρ : Env Γ) (x : ⟦ σ ⟧) (γ0 : ⟦ Loss ⟧ → Ŵ ε ⊤)
                → RootZero (Vsem (zeroLC {σ = σ}) ρ x γ0)
RootZero-zeroLC ρ x γ0 = refl

-- ---------------------------------------------------------------------
-- The stuck-node fix: handlerΨ's own l1 formula uses `collect`, which
-- PRESERVES a node's own root untouched while `collapse` (used to build
-- it) ZEROES a node's root unconditionally -- so wrapping a stuck D in
-- an outer `tell r` (from ext̂'s own act) re-introduces r at the root,
-- which `collect` then carries through as the FINAL root, disagreeing
-- with `mapŴ (r +_) D` (thenE/fl's own combine step), which never
-- touches a node's root at all, only the eventual leaf payload
-- (RootZeroSubLemmaCheck.agda's sub-lemma-check is a concrete refutation
-- of this mismatch). `collectX`, unlike `collect`, REDISTRIBUTES an
-- outer bump down to every leaf via `bump` -- exactly matching mapŴ's
-- own "hold the bump in reserve until a leaf is reached" behaviour. This
-- lemma confirms that replacing `collect W` with `mapŴ proj₂ (collectX
-- W)` (semantically forced to agree only where it matters, at RootZero
-- trees) fixes the previously-refuted case, using EXACTLY
-- bump-collectX-comm (already proven, no new axioms) to make the
-- induction go through.
RootZero-collect-via-collectX : ∀ {ε} (r : R) (D : Ŵ ε R) → RootZero D
  → mapŴ (λ { (_ , r1) → r1 }) (collectX (tell r (collapse D))) ≡ mapŴ (r +_) D
RootZero-collect-via-collectX r (leaf r0 v) rz =
  cong (λ z → leaf z (r + v)) (sym rz)
RootZero-collect-via-collectX r (node m op r0 o κ) (rz , rzκ) =
  trans (cong (node m op 0# o) (funext childEq))
        (cong (λ z → node m op z o (λ a → mapŴ (r +_) (κ a))) (sym rz))
  where
  π₂ = λ { (_ , r1) → r1 }
  childEq : ∀ a → mapŴ π₂ (bump (r + 0#) (collectX (collapse (κ a)))) ≡ mapŴ (r +_) (κ a)
  childEq a = trans (cong (λ z → mapŴ π₂ (bump z (collectX (collapse (κ a))))) (+-identityʳ r))
                    (trans (cong (mapŴ π₂) (bump-collectX-comm r (collapse (κ a))))
                           (RootZero-collect-via-collectX r (κ a) (rzκ a)))

-- The full fl/l1v matching argument ("Lemma L"), closing the gap the
-- FOURTH/FIFTH findings above left open: with l1 read via `collectX`
-- (mapŴ π₂ ∘ collectX) instead of `collect`, R5's own `fl := (...)▶g`
-- reification (whose Esem unfolds to exactly the RHS below, via
-- collectX/mapŴ) and the handler algebra's own choice-continuation
-- (whose "yes"-branch value is exactly the LHS below, via ext̂/bind̂)
-- agree UNCONDITIONALLY on W's own shape (no RootZero on W itself is
-- needed -- W may get stuck on any operation whatsoever), needing
-- RootZero ONLY of δ' itself (g's own semantic value) -- exactly the
-- invariant RootZero-thenE-wrap proves is maintained throughout
-- theorem-B9's real induction. Proved via collectX-bind̂-fusion/
-- bind̂-mapŴ-after (both already established, standard collectX/bind̂/
-- mapŴ interchange laws) composed with RootZero-collect-via-collectX
-- above -- no new axioms.
lemma-fl-l1v-match : ∀ {ε X} (W : Ŵ ε X) (δ' : X → Ŵ ε R) → (∀ x → RootZero (δ' x))
  → mapŴ (λ { (_ , r1) → r1 }) (collectX (bind̂ W (λ x → collapse (δ' x))))
  ≡ bind̂ (collectX W) (λ { (x , r1) → mapŴ (r1 +_) (δ' x) })
lemma-fl-l1v-match W δ' rzδ' =
  trans (cong (mapŴ π₂) (collectX-bind̂-fusion W (λ x → collapse (δ' x))))
        (trans (sym (bind̂-mapŴ-after (collectX W) (λ { (x , r1) → bump r1 (collectX (collapse (δ' x))) }) π₂))
               (cong (bind̂ (collectX W))
                     (funext (λ { (x , r1) → trans (cong (mapŴ π₂) (bump-collectX-comm r1 (collapse (δ' x))))
                                                    (RootZero-collect-via-collectX r1 (δ' x) (rzδ' x)) }))))
  where
  π₂ = λ { (_ , r1) → r1 }

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
-- Lemma 7.5 (hat-Lemma B.5): loss continuations and THEN. NOT PORTED.
--
-- Statement (for e:Γ⊢σ!ε, g:LC Γ σ εg with sub:εg⊆ε):
--   (1) Esem(thenE sub e g)(ρ) = λγ1. collect(R̂-of(Esem e ρ)(λa. widenŴ sub (Lsem g ρ a)))
--   (2) collect ∘ (Lsem g ρ) = λa. Vsem g ρ a γ1, for every γ1
--   (3) Lsem(vabs(thenE sub e g))(ρ) = λa. R̂-of(Esem e (ρ,,a))(λb. widenŴ sub (Lsem g (ρ,,a) b))
--
-- Two dedicated attempts (both machine-checked, not just hand-waved) found
-- part (1) genuinely FALSE for arbitrary g -- B5Counterexample.agda, using
-- e := val v and g := λ_. snd(pair(loss(vgnd k), vgnd r₀)): `Lsem g ρ a =
-- collapse(Vsem g ρ a γ0)` discards whatever loss accumulated before its
-- argument's own leaf (replacing the leaf's root with the payload), so
-- the two sides disagree in exactly the root-loss slot whenever k ≠ 0#.
--
-- The natural fix -- restrict to a "canonical" class of continuations
-- (zeroLC, or ▶-chains over it, matching what S2/R7 ever actually
-- construct at runtime) and prove part (3) for that class by the paper's
-- own mutual induction -- was also tried (B5Core.agda) and does not
-- close the gap either: testing part (3) directly (no restriction on g's
-- shape, using Example.agda's real `decide` operation so g can genuinely
-- get stuck on an operation) found the true boundary is about e, not g:
--   * e clean (r1 = 0) + g stuck on an operation:      HOLDS (b53-check)
--   * e dirty (r1 ≠ 0) + g reaches a value:             HOLDS (b53-check3)
--   * e dirty (r1 ≠ 0) + g stuck on an operation:       FAILS (b53-refuted2)
-- So the real requirement is "no subterm anywhere -- in either the
-- frame's hole-filling role or the continuation role -- discards a
-- nonzero loss while its own evaluation also reaches a stuck operation",
-- a global claim about the whole program, not a restriction on g alone.
-- Establishing that (e.g. by a logical-relations argument over all of
-- `Esem`) is substantially more work than this porting pass attempts.
--
-- Consequently B.5 is not formalised as a lemma here at all. Its only
-- would-be consumer in this file was a proof of Lemma 7.7/B.7, and Lemma
-- B.7 itself is not, in turn, consumed by anything else here: Theorem
-- 7.9/B.9's harder frame cases (F-rule, S1-S4, R5, R7) are independent
-- postulates in their own right (see below), not built from B.7. So
-- B.5/B.7 were removed rather than kept as unconsumed scaffolding. (B.6's
-- own F-loss case has its own, separate postulate, `postulate-Ŝ-tell-
-- naturality` below, related in spirit but not literally B.5 -- B.6
-- otherwise stands on its own, 9/10 cases fully proven, and is kept.) The
-- machine-checked counterexamples remain in B5Counterexample.agda and
-- B5Core.agda for anyone picking this back up.
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
  renLsem-coh ren ρ ρ' coh g a = cong (λ F → collapse (F a (λ _ → η̂ tt))) (renV-coh ren ρ ρ' coh g)

  renH-coh : ∀ {Γ Γ' ℓ par σ σ' ε} (ren : Ren Γ Γ') (ρ : Env Γ) (ρ' : Env Γ') → RenCoh ren ρ ρ' → (h : Handler Γ ℓ par σ σ' ε) (p : ⟦ gnd par ⟧) (G : Ŝ (ε ,ℓ ℓ) ⟦ σ ⟧) (γ : ⟦ σ' ⟧ → Ŵ ε ⊤)
           → handlerSem (renH ren h) ρ' p G γ ≡ handlerSem h ρ p G γ
  renH-coh {Γ} {Γ'} {ℓ} {par} {σ} {σ'} {ε} ren ρ ρ' coh h p G γ =
    cong (λ F → F p) (ext̂-cong (handlerAlg (renH ren h) ρ' γ) (handlerAlg h ρ γ) actEq ψEq
                                (handlerRet (renH ren h) ρ' γ) (handlerRet h ρ γ) (λ a → funext (sEq a)) (G (λ _ → η̂ tt)))
    where
    s s' : ⟦ σ ⟧ → ⟦ gnd par ⟧ → Ŵ ε ⟦ σ' ⟧
    s  = handlerRet h ρ γ
    s' = handlerRet (renH ren h) ρ' γ

    sEq : ∀ a p' → s' a p' ≡ s a p'
    sEq a p' = cong (λ F → F γ) (renE-coh (extR (extR ren)) ((ρ ,, p') ,, a) ((ρ' ,, p') ,, a)
                         (extR-coh σ (extR ren) (ρ ,, p') (ρ' ,, p') (extR-coh (gnd par) ren ρ ρ' coh p') a) (ret h))

    actEq : LayeredAlg.act (handlerAlg (renH ren h) ρ' γ) ≡ LayeredAlg.act (handlerAlg h ρ γ)
    actEq = refl

    ψEq : ∀ {ℓ1} (m : ℓ1 ∈ (ε ,ℓ ℓ)) (op : Op ℓ1) (o : ⟦ out op ⟧ᴳ) (κ κ' : ⟦ in′ op ⟧ᴳ → (⟦ gnd par ⟧ → Ŵ ε ⟦ σ' ⟧))
        → (∀ b → κ b ≡ κ' b) → handlerΨ (renH ren h) ρ' γ m op o κ ≡ handlerΨ h ρ γ m op o κ'
    ψEq {ℓ1} m op o κ κ' κeq with ℓ1 ≟ᵉ ℓ
    ... | no neq = funext (λ p' → cong (λ z → node (demoteMem m neq) op 0# o z) (funext (λ a → cong (λ f → f p') (κeq a))))
    ... | yes eq with eq
    -- ψ' m op o κ uses κ for its own local l1v/k1v (call them l1vκ/k1vκ,
    -- the "target"/renamed side); ψ m op o κ' uses κ' the same way (call
    -- them l1vκ'/k1vκ', the "source"/original side).
    ...   | refl = funext (λ p' → cong (λ F → F γ) (renE-coh (extR (extR (extR (extR ren))))
                     ((((ρ ,, p') ,, o) ,, l1vκ') ,, k1vκ') ((((ρ' ,, p') ,, o) ,, l1vκ) ,, k1vκ)
                     (extR-coh' ((gnd par `× gnd (in′ op)) ⇒ σ' ! ε) (extR (extR (extR ren)))
                       (((ρ ,, p') ,, o) ,, l1vκ') (((ρ' ,, p') ,, o) ,, l1vκ)
                       (extR-coh' ((gnd par `× gnd (in′ op)) ⇒ Loss ! ε) (extR (extR ren))
                         ((ρ ,, p') ,, o) ((ρ' ,, p') ,, o) (extR-coh (gnd (out op)) (extR ren) (ρ ,, p') (ρ' ,, p') (extR-coh (gnd par) ren ρ ρ' coh p') o)
                         l1vκ' l1vκ l1vEq)
                       k1vκ' k1vκ k1vEq)
                     (clause h op)))
      where
      l1vκ l1vκ' : ⟦ gnd par `× gnd (in′ op) ⟧ → Ŝ ε R
      l1vκ  (p'' , a) γ1 = mapŴ (λ { (_ , r1) → r1 }) (collectX (ext̂ Ŵ-alg γ (κ  a p'')))
      l1vκ' (p'' , a) γ1 = mapŴ (λ { (_ , r1) → r1 }) (collectX (ext̂ Ŵ-alg γ (κ' a p'')))
      k1vκ k1vκ' : ⟦ gnd par `× gnd (in′ op) ⟧ → Ŝ ε ⟦ σ' ⟧
      k1vκ  (p'' , a) γ' = κ  a p''
      k1vκ' (p'' , a) γ' = κ' a p''
      l1vEq : l1vκ ≡ l1vκ'
      l1vEq = funext (λ{ (p'' , a) → funext (λ γ1 → cong (λ w → mapŴ (λ { (_ , r1) → r1 }) (collectX (ext̂ Ŵ-alg γ w))) (cong (λ f → f p'') (κeq a))) })
      k1vEq : k1vκ ≡ k1vκ'
      k1vEq = funext (λ{ (p'' , a) → funext (λ γ' → cong (λ f → f p'') (κeq a)) })

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
  renE-coh ren ρ ρ' coh (opE m op e) = cong (bind̂ˢ (λ a → φ̂ˢ m op a η̂ˢ)) (renE-coh ren ρ ρ' coh e)
  renE-coh ren ρ ρ' coh (lossE e) =
    funext (λ γ → cong (λ w → bind̂ w (λ a → tell a (η̂ tt))) (cong (λ F → F (λ _ → η̂ tt)) (renE-coh ren ρ ρ' coh e)))
  renE-coh ren ρ ρ' coh (thenE sub e1 g) = funext (λ γ → cong₂
    (λ w1 f2 → bind̂ (collectX w1) (λ{ (a , r1) → mapŴ (r1 +_) (f2 a) }))
    e1treeEq innerEq)
    where
    contEq : (λ a → widenŴ sub (Lsem (renV ren g) ρ' a)) ≡ (λ a → widenŴ sub (Lsem g ρ a))
    contEq = funext (λ a → cong (widenŴ sub) (renLsem-coh ren ρ ρ' coh g a))
    e1treeEq : Esem (renE ren e1) ρ' (λ a → widenŴ sub (Lsem (renV ren g) ρ' a)) ≡ Esem e1 ρ (λ a → widenŴ sub (Lsem g ρ a))
    e1treeEq = trans (cong (λ F → F (λ a → widenŴ sub (Lsem (renV ren g) ρ' a))) (renE-coh ren ρ ρ' coh e1))
                      (cong (Esem e1 ρ) contEq)
    innerEq : (λ a → widenŴ sub (Vsem (renV ren g) ρ' a (λ _ → η̂ tt))) ≡ (λ a → widenŴ sub (Vsem g ρ a (λ _ → η̂ tt)))
    innerEq = funext (λ a → cong (λ F → widenŴ sub (F a (λ _ → η̂ tt))) (renV-coh ren ρ ρ' coh g))

  renE-coh ren ρ ρ' coh (glocalE sub1 sub2 e g) = funext (λ γ →
    cong (widenŴ sub2) (trans (cong (λ F → F (λ a → widenŴ sub1 (Lsem (renV ren g) ρ' a))) (renE-coh ren ρ ρ' coh e))
                               (cong (Esem e ρ) (funext (λ a → cong (widenŴ sub1) (renLsem-coh ren ρ ρ' coh g a))))))

  renE-coh ren ρ ρ' coh (resetE e) = funext (λ γ → cong censor (cong (λ F → F γ) (renE-coh ren ρ ρ' coh e)))

  renE-coh ren ρ ρ' coh (handleE h e1 e2) = cong₂ bind̂ˢ pFunEq (renE-coh ren ρ ρ' coh e1)
    where
    pFunEq : (λ p → handlerSem (renH ren h) ρ' p (Esem (renE ren e2) ρ')) ≡ (λ p → handlerSem h ρ p (Esem e2 ρ))
    pFunEq = funext (λ p → trans (cong (handlerSem (renH ren h) ρ' p) (renE-coh ren ρ ρ' coh e2))
                                  (funext (λ γ → renH-coh ren ρ ρ' coh h p (Esem e2 ρ) γ)))

-- Weakening by exactly one variable is the special case ren := S,
-- coh := λ x → refl (immediate from `,,`'s own S-clause).
weaken1-coh : ∀ {Γ σ ε} (τ : Ty) (e : Γ ⊢ σ ! ε) (ρ : Env Γ) (a : ⟦ τ ⟧) → Esem (weaken1 e) (ρ ,, a) ≡ Esem e ρ
weaken1-coh τ e ρ a = renE-coh (S {τ = τ}) ρ (ρ ,, a) (λ x → refl) e

weaken1V-coh : ∀ {Γ σ} (τ : Ty) (v : Val Γ σ) (ρ : Env Γ) (a : ⟦ τ ⟧) → Vsem (weaken1V v) (ρ ,, a) ≡ Vsem v ρ
weaken1V-coh τ v ρ a = renV-coh (S {τ = τ}) ρ (ρ ,, a) (λ x → refl) v

weaken1H-coh : ∀ {Γ ℓ par σ σ' ε} (τ : Ty) (h : Handler Γ ℓ par σ σ' ε) (ρ : Env Γ) (a : ⟦ τ ⟧) (p : ⟦ gnd par ⟧) (G : Ŝ (ε ,ℓ ℓ) ⟦ σ ⟧) (γ : ⟦ σ' ⟧ → Ŵ ε ⊤)
              → handlerSem (renH (S {τ = τ}) h) (ρ ,, a) p G γ ≡ handlerSem h ρ p G γ
weaken1H-coh τ h ρ a p G γ = renH-coh (S {τ = τ}) ρ (ρ ,, a) (λ x → refl) h p G γ

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
  subLsem-coh σs ρ' ρ coh g a = cong (λ F → collapse (F a (λ _ → η̂ tt))) (subV-coh σs ρ' ρ coh g)

  subH-coh : ∀ {Γ Γ' ℓ par σ σ' ε} (σs : Sub Γ Γ') (ρ' : Env Γ') (ρ : Env Γ) → SubCoh σs ρ' ρ → (h : Handler Γ ℓ par σ σ' ε) (p : ⟦ gnd par ⟧) (G : Ŝ (ε ,ℓ ℓ) ⟦ σ ⟧) (γ : ⟦ σ' ⟧ → Ŵ ε ⊤)
           → handlerSem (subH σs h) ρ' p G γ ≡ handlerSem h ρ p G γ
  subH-coh {Γ} {Γ'} {ℓ} {par} {σ} {σ'} {ε} σs ρ' ρ coh h p G γ =
    cong (λ F → F p) (ext̂-cong (handlerAlg (subH σs h) ρ' γ) (handlerAlg h ρ γ) actEq ψEq
                                (handlerRet (subH σs h) ρ' γ) (handlerRet h ρ γ) (λ a → funext (sEq a)) (G (λ _ → η̂ tt)))
    where
    s s' : ⟦ σ ⟧ → ⟦ gnd par ⟧ → Ŵ ε ⟦ σ' ⟧
    s  = handlerRet h ρ γ
    s' = handlerRet (subH σs h) ρ' γ

    sEq : ∀ a p' → s' a p' ≡ s a p'
    sEq a p' = cong (λ F → F γ) (subE-coh (extS (extS σs)) ((ρ' ,, p') ,, a) ((ρ ,, p') ,, a)
                         (extS-coh σ (extS σs) (ρ' ,, p') (ρ ,, p') (extS-coh (gnd par) σs ρ' ρ coh p') a) (ret h))

    actEq : LayeredAlg.act (handlerAlg (subH σs h) ρ' γ) ≡ LayeredAlg.act (handlerAlg h ρ γ)
    actEq = refl

    ψEq : ∀ {ℓ1} (m : ℓ1 ∈ (ε ,ℓ ℓ)) (op : Op ℓ1) (o : ⟦ out op ⟧ᴳ) (κ κ' : ⟦ in′ op ⟧ᴳ → (⟦ gnd par ⟧ → Ŵ ε ⟦ σ' ⟧))
        → (∀ b → κ b ≡ κ' b) → handlerΨ (subH σs h) ρ' γ m op o κ ≡ handlerΨ h ρ γ m op o κ'
    ψEq {ℓ1} m op o κ κ' κeq with ℓ1 ≟ᵉ ℓ
    ... | no neq = funext (λ p' → cong (λ z → node (demoteMem m neq) op 0# o z) (funext (λ a → cong (λ f → f p') (κeq a))))
    ... | yes eq with eq
    ...   | refl = funext (λ p' → cong (λ F → F γ) (subE-coh (extS (extS (extS (extS σs))))
                     ((((ρ' ,, p') ,, o) ,, l1vκ) ,, k1vκ) ((((ρ ,, p') ,, o) ,, l1vκ') ,, k1vκ')
                     (extS-coh' ((gnd par `× gnd (in′ op)) ⇒ σ' ! ε) (extS (extS (extS σs)))
                       (((ρ' ,, p') ,, o) ,, l1vκ) (((ρ ,, p') ,, o) ,, l1vκ')
                       (extS-coh' ((gnd par `× gnd (in′ op)) ⇒ Loss ! ε) (extS (extS σs))
                         ((ρ' ,, p') ,, o) ((ρ ,, p') ,, o)
                         (extS-coh (gnd (out op)) (extS σs) (ρ' ,, p') (ρ ,, p') (extS-coh (gnd par) σs ρ' ρ coh p') o)
                         l1vκ' l1vκ l1vEq)
                       k1vκ' k1vκ k1vEq)
                     (clause h op)))
      where
      l1vκ l1vκ' : ⟦ gnd par `× gnd (in′ op) ⟧ → Ŝ ε R
      l1vκ  (p'' , a) γ1 = mapŴ (λ { (_ , r1) → r1 }) (collectX (ext̂ Ŵ-alg γ (κ  a p'')))
      l1vκ' (p'' , a) γ1 = mapŴ (λ { (_ , r1) → r1 }) (collectX (ext̂ Ŵ-alg γ (κ' a p'')))
      k1vκ k1vκ' : ⟦ gnd par `× gnd (in′ op) ⟧ → Ŝ ε ⟦ σ' ⟧
      k1vκ  (p'' , a) γ' = κ  a p''
      k1vκ' (p'' , a) γ' = κ' a p''
      l1vEq : l1vκ ≡ l1vκ'
      l1vEq = funext (λ{ (p'' , a) → funext (λ γ1 → cong (λ w → mapŴ (λ { (_ , r1) → r1 }) (collectX (ext̂ Ŵ-alg γ w))) (cong (λ f → f p'') (κeq a))) })
      k1vEq : k1vκ ≡ k1vκ'
      k1vEq = funext (λ{ (p'' , a) → funext (λ γ' → cong (λ f → f p'') (κeq a)) })

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
  subE-coh σs ρ' ρ coh (opE m op e) = cong (bind̂ˢ (λ a → φ̂ˢ m op a η̂ˢ)) (subE-coh σs ρ' ρ coh e)
  subE-coh σs ρ' ρ coh (lossE e) =
    funext (λ γ → cong (λ w → bind̂ w (λ a → tell a (η̂ tt))) (cong (λ F → F (λ _ → η̂ tt)) (subE-coh σs ρ' ρ coh e)))
  subE-coh σs ρ' ρ coh (thenE sub e1 g) = funext (λ γ → cong₂
    (λ w1 f2 → bind̂ (collectX w1) (λ{ (a , r1) → mapŴ (r1 +_) (f2 a) }))
    e1treeEq innerEq)
    where
    contEq : (λ a → widenŴ sub (Lsem (subV σs g) ρ' a)) ≡ (λ a → widenŴ sub (Lsem g ρ a))
    contEq = funext (λ a → cong (widenŴ sub) (subLsem-coh σs ρ' ρ coh g a))
    e1treeEq : Esem (subE σs e1) ρ' (λ a → widenŴ sub (Lsem (subV σs g) ρ' a)) ≡ Esem e1 ρ (λ a → widenŴ sub (Lsem g ρ a))
    e1treeEq = trans (cong (λ F → F (λ a → widenŴ sub (Lsem (subV σs g) ρ' a))) (subE-coh σs ρ' ρ coh e1))
                      (cong (Esem e1 ρ) contEq)
    innerEq : (λ a → widenŴ sub (Vsem (subV σs g) ρ' a (λ _ → η̂ tt))) ≡ (λ a → widenŴ sub (Vsem g ρ a (λ _ → η̂ tt)))
    innerEq = funext (λ a → cong (λ F → widenŴ sub (F a (λ _ → η̂ tt))) (subV-coh σs ρ' ρ coh g))

  subE-coh σs ρ' ρ coh (glocalE sub1 sub2 e g) = funext (λ γ →
    cong (widenŴ sub2) (trans (cong (λ F → F (λ a → widenŴ sub1 (Lsem (subV σs g) ρ' a))) (subE-coh σs ρ' ρ coh e))
                               (cong (Esem e ρ) (funext (λ a → cong (widenŴ sub1) (subLsem-coh σs ρ' ρ coh g a))))))

  subE-coh σs ρ' ρ coh (resetE e) = funext (λ γ → cong censor (cong (λ F → F γ) (subE-coh σs ρ' ρ coh e)))

  subE-coh σs ρ' ρ coh (handleE h e1 e2) = cong₂ bind̂ˢ pFunEq (subE-coh σs ρ' ρ coh e1)
    where
    pFunEq : (λ p → handlerSem (subH σs h) ρ' p (Esem (subE σs e2) ρ')) ≡ (λ p → handlerSem h ρ p (Esem e2 ρ))
    pFunEq = funext (λ p → trans (cong (handlerSem (subH σs h) ρ' p) (subE-coh σs ρ' ρ coh e2))
                                  (funext (λ γ → subH-coh σs ρ' ρ coh h p (Esem e2 ρ) γ)))

-- Single substitution, e[v] : the special case σs := sub1 v, coh := λ x → refl.
sub1-coh : ∀ {Γ σ τ ε} (e : (Γ , σ) ⊢ τ ! ε) (ρ : Env Γ) (v : Val Γ σ) → Esem (e [ v ]) ρ ≡ Esem e (ρ ,, Vsem v ρ)
sub1-coh e ρ v = subE-coh (sub1 v) ρ (ρ ,, Vsem v ρ) (λ { Z → refl ; (S x) → refl }) e

-- ---------------------------------------------------------------------
-- Lemma 7.6 (hat-Lemma B.6): the context lemma for regular frames.
-- "For e:σ!ε and F[e]:τ!ε where F is a regular frame:
--    Ssem(F[e])(ρ) = let_Sε a∈σ be Ssem(e)(ρ) in Ssem(F[x])(ρ[x/a])"
--
-- Proved case-by-case on F (Fig. 5's nine forms). Every case except
-- F-loss reduces cleanly to the Ŝ unit law (bindˢ-unitˡ, as in Lemma
-- B.4) plus weakening coherence -- exactly "no case here touches Ŵε's
-- internal structure" as the source states. F-loss is the one frame
-- whose hole is loss-typed, and hand-computation shows its case needs a
-- naturality property of Ŝ's bind w.r.t. tell that traces back to the
-- same unresolved fusion law as Lemma B.5 (§7's THEN lemma) -- both are
-- ultimately about how `tell` commutes with "let"; postponed with it.
-- ---------------------------------------------------------------------

postulate
  postulate-Ŝ-tell-naturality :
    ∀ {Γ ε} (e : Γ ⊢ Loss ! ε) (ρ : Env Γ)
    → Esem (lossE e) ρ ≡ bind̂ˢ (λ a → Esem (lossE {ε = ε} (val (vvar Z))) (ρ ,, a)) (Esem e ρ)

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

lemma-B6 (F-op m op) e ρ = cong (λ F → bind̂ˢ F (Esem e ρ)) (funext (λ a →
  sym (bindˢ-unitˡ (λ b → φ̂ˢ m op b η̂ˢ) a)))

lemma-B6 {α = α} (F-handleP h body) e ρ = cong (λ F → bind̂ˢ F (Esem e ρ)) (funext (λ a → sym (trans
  (bindˢ-unitˡ (λ p → handlerSem (renH S h) (ρ ,, a) p (Esem (weaken1 body) (ρ ,, a))) a)
  (trans (funext (weaken1H-coh α h ρ a a (Esem (weaken1 body) (ρ ,, a))))
         (cong (handlerSem h ρ a) (weaken1-coh α body ρ a))))))

lemma-B6 F-loss e ρ = postulate-Ŝ-tell-naturality e ρ

-- Lemma 7.7 (hat-Lemma B.7), "threading loss continuations through
-- frames", is not formalised here: its proof needs Lemma 7.5(3)/B.5(3),
-- which turned out not to hold unconditionally (see the writeup above
-- Lemma B.5's old location, and B5Counterexample.agda/B5Core.agda). B.7
-- was also not consumed by anything else in this file -- Theorem
-- 7.9/B.9's harder cases below are independent postulates in their own
-- right -- so it's omitted rather than kept as an unconsumed, only
-- partially-provable lemma.

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
weaken1F-skip (F-op m op) υ ρ c a = refl
weaken1F-skip F-loss υ ρ c a = refl
weaken1F-skip {α = α} (F-handleP h body) υ ρ c a = trans lhsRed (sym rhsRed)
  where
  bodyEq2 : Esem (weaken1 (weaken1 body)) ((ρ ,, c) ,, a) ≡ Esem body ρ
  bodyEq2 = trans (weaken1-coh α (weaken1 body) (ρ ,, c) a) (weaken1-coh υ body ρ c)
  bodyEq3 : Esem (weaken1 body) (ρ ,, a) ≡ Esem body ρ
  bodyEq3 = weaken1-coh α body ρ a
  lhsRed : Esem (handleE (renH S (renH S h)) (val (vvar Z)) (weaken1 (weaken1 body))) ((ρ ,, c) ,, a) ≡ handlerSem h ρ a (Esem body ρ)
  lhsRed = trans (bindˢ-unitˡ (λ p → handlerSem (renH S (renH S h)) ((ρ ,, c) ,, a) p (Esem (weaken1 (weaken1 body)) ((ρ ,, c) ,, a))) a)
                 (trans (cong (handlerSem (renH S (renH S h)) ((ρ ,, c) ,, a) a) bodyEq2)
                        (funext (λ γ → trans (weaken1H-coh α (renH S h) (ρ ,, c) a a (Esem body ρ) γ)
                                              (weaken1H-coh υ h ρ c a (Esem body ρ) γ))))
  rhsRed : Esem (handleE (renH S h) (val (vvar Z)) (weaken1 body)) (ρ ,, a) ≡ handlerSem h ρ a (Esem body ρ)
  rhsRed = trans (bindˢ-unitˡ (λ p → handlerSem (renH S h) (ρ ,, a) p (Esem (weaken1 body) (ρ ,, a))) a)
                 (trans (cong (handlerSem (renH S h) (ρ ,, a) a) bodyEq3)
                        (funext (λ γ → weaken1H-coh α h ρ a a (Esem body ρ) γ)))

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
           (ρ : Env Γ) (γ : ⟦ τ ⟧ → Ŵ εO ⊤)
         → Esem (plugK k (opE mH op (val v))) ρ γ
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
            (ρ : Env Γ) (γ : ⟦ τ ⟧ → Ŵ εO ⊤)
          → Esem (plugK (F∘ k f) (opE mH op (val v))) ρ γ
          ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K (F∘ k f)) (val (vvar Z))) (ρ ,, a)) γ
lemma-B8-F∘-eq {α = α} op v k f mH nh ρ γ = trans step1 (trans step2 step3)
  where
  e₀ = plugK k (opE mH op (val v))
  H : ⟦ α ⟧ → Ŝ _ _
  H a = Esem (plugF (weaken1F f) (val (vvar Z))) (ρ ,, a)
  ih : Esem e₀ ρ ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, a))
  ih = funext (λ γ' → lemma-B8 op v k mH nh ρ γ')
  step1 : Esem (plugF f (plugK k (opE mH op (val v)))) ρ γ ≡ bind̂ˢ H (Esem e₀ ρ) γ
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
            (ρ : Env Γ) (γ : ⟦ τ ⟧ → Ŵ εO ⊤)
          → Esem (plugK (F∘ k f) (opE mH op (val v))) ρ γ
          ≡ φ̂ˢ (promote (F∘ k f) nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K (F∘ k f)) (val (vvar Z))) (ρ ,, a)) γ
lemma-B8-F∘ {β = β} {εO = εO} op v k f mH nh ρ γ = helper (Frame-effect-eq f)
  where
  helper : (eq : β ≡ εO) → Esem (plugK (F∘ k f) (opE mH op (val v))) ρ γ
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
            (ρ : Env Γ) (γ : ⟦ Loss ⟧ → Ŵ ε ⊤)
          → Esem (thenE sub (plugK k (opE mH op (val v))) g) ρ γ
          ≡ φ̂ˢ (promote k nh mH) op (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-then sub g))) (val (vvar Z))) (ρ ,, b)) γ
lemma-B8-S∘-then {α = α} {ε = ε} op v k sub g mH nh ρ γ = trans step1 step2
  where
  e₀ = plugK k (opE mH op (val v))
  δ1 : ⟦ α ⟧ → Ŵ ε ⊤
  δ1 a = widenŴ sub (Lsem g ρ a)
  K : ⟦ α ⟧ × R → Ŵ ε R
  K (a , r1) = mapŴ (r1 +_) (widenŴ sub (Vsem g ρ a (λ _ → η̂ tt)))
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
    K'Eq : ∀ (ar1 : ⟦ α ⟧ × R) → K ar1 ≡ mapŴ (proj₂ ar1 +_) (widenŴ sub (Vsem (weaken1V g) (ρ ,, b) (proj₁ ar1) (λ _ → η̂ tt)))
    K'Eq (a , r1) = cong (λ w → mapŴ (r1 +_) (widenŴ sub w)) (sym (cong (λ f → f a (λ _ → η̂ tt)) (renV-coh S ρ (ρ ,, b) (λ _ → refl) g)))
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
            (ρ : Env Γ) (γ : ⟦ α ⟧ → Ŵ ε ⊤)
          → Esem (glocalE sub1 sub2 (plugK k (opE mH op (val v))) g) ρ γ
          ≡ φ̂ˢ (sub2 (promote k nh mH)) op (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-glocal sub1 sub2 g))) (val (vvar Z))) (ρ ,, b)) γ
lemma-B8-S∘-glocal {α = α} {ε₁ = ε₁} op v k sub1 sub2 g mH nh ρ γ = mainStep
  where
  e₀ = plugK k (opE mH op (val v))
  δ1 : ⟦ α ⟧ → Ŵ ε₁ ⊤
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
-- NEW label-equality dispatch (the fix from this session) takes the
-- "no" branch here via `neq` (derived directly from nh), landing on
-- EXACTLY `demoteMem`'s own construction -- which promote's own
-- S-handleB clause was ALREADY computing by hand (same ∈-++⁻ split,
-- same nh-derived absurd case), so the two agree definitionally.
-- Bridges promote's own S-handleB clause to demoteMem -- both compute
-- via the SAME `∈-++⁻ ε (promote k nh' mH)` split (nh already rules out
-- the "here" case identically in both), but as separately-elaborated
-- `with`s they don't unify automatically; matching it once, explicitly,
-- here settles both sides at once.
promote-S-handleB-eq : ∀ {Γ ℓ σ εH α ℓ' par σ' ε} (k : ContCxt Γ σ εH α (ε ,ℓ ℓ')) (h : Handler Γ ℓ' par α σ' ε) (w : Val Γ (gnd par))
                        (nh : ¬ Handles (S∘ k (S-handleB h w)) ℓ) (mH : ℓ ∈ εH)
                     → promote (S∘ k (S-handleB h w)) nh mH ≡ demoteMem (promote k (λ hk → nh (inj₂ hk)) mH) (λ eq → nh (inj₁ eq))
promote-S-handleB-eq {ε = ε} k h w nh mH with ∈-++⁻ ε (promote k (λ hk → nh (inj₂ hk)) mH)
... | inj₁ m-old       = refl
... | inj₂ (here eq)   = ⊥-elim (nh (inj₁ eq))
... | inj₂ (there ())

lemma-B8-S∘-handleB : ∀ {Γ ℓ εH α ℓ' par σ' ε} (op : Op ℓ) (v : Val Γ (gnd (out op)))
            (k : ContCxt Γ (gnd (in′ op)) εH α (ε ,ℓ ℓ')) (h : Handler Γ ℓ' par α σ' ε) (w : Val Γ (gnd par))
            (mH : ℓ ∈ εH) (nh : ¬ Handles (S∘ k (S-handleB h w)) ℓ) (ρ : Env Γ) (γ : ⟦ σ' ⟧ → Ŵ ε ⊤)
          → Esem (handleE h (val w) (plugK k (opE mH op (val v)))) ρ γ
          ≡ φ̂ˢ (promote (S∘ k (S-handleB h w)) nh mH) op (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-handleB h w))) (val (vvar Z))) (ρ ,, b)) γ
lemma-B8-S∘-handleB {ℓ = ℓ} {α = α} {ℓ' = ℓ'} {par = par} {ε = ε} op v k h w mH nh ρ γ = mainStep
  where
  neq : ¬ (ℓ ≡ ℓ')
  neq eq = nh (inj₁ eq)
  nh' : ¬ Handles k ℓ
  nh' hk = nh (inj₂ hk)
  e₀ = plugK k (opE mH op (val v))
  pe : ⟦ gnd par ⟧
  pe = Vsem w ρ
  κ : ⟦ in′ op ⟧ᴳ → Ŝ (ε ,ℓ ℓ') ⟦ α ⟧
  κ b = Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, b)
  ih : Esem e₀ ρ (λ _ → η̂ tt) ≡ φ̂ˢ (promote k nh' mH) op (Vsem v ρ) κ (λ _ → η̂ tt)
  ih = lemma-B8 op v k mH nh' ρ (λ _ → η̂ tt)
  step1 : Esem (handleE h (val w) e₀) ρ γ ≡ ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (φ̂ˢ (promote k nh' mH) op (Vsem v ρ) κ (λ _ → η̂ tt)) pe
  step1 = trans (cong (λ F → F γ) (bindˢ-unitˡ (λ p' → handlerSem h ρ p' (Esem e₀ ρ)) pe))
                (cong (λ w' → ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) w' pe) ih)
  bAeq : ∀ (b : ⟦ in′ op ⟧ᴳ) → ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (κ b (λ _ → η̂ tt)) pe ≡ Esem (plugK (weaken1K (S∘ k (S-handleB h w))) (val (vvar Z))) (ρ ,, b) γ
  bAeq b = trans (sym (renH-coh S ρ (ρ ,, b) (λ _ → refl) h pe (κ b) γ))
                 (trans (cong (λ p' → handlerSem (renH S h) (ρ ,, b) p' (κ b) γ) (sym peEq))
                        (sym step2))
    where
    peEq : Vsem (weaken1V w) (ρ ,, b) ≡ pe
    peEq = weaken1V-coh _ w ρ b
    step2 : Esem (plugK (weaken1K (S∘ k (S-handleB h w))) (val (vvar Z))) (ρ ,, b) γ
          ≡ handlerSem (renH S h) (ρ ,, b) (Vsem (weaken1V w) (ρ ,, b)) (κ b) γ
    step2 = cong (λ F → F γ) (bindˢ-unitˡ (λ p' → handlerSem (renH S h) (ρ ,, b) p' (κ b)) (Vsem (weaken1V w) (ρ ,, b)))
  step3 : ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (φ̂ˢ (promote k nh' mH) op (Vsem v ρ) κ (λ _ → η̂ tt)) pe
        ≡ node (demoteMem (promote k nh' mH) neq) op 0# (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-handleB h w))) (val (vvar Z))) (ρ ,, b) γ)
  step3 = trans (tell-0 _)
                (trans (cong (λ F → F pe) (handlerΨ-no-eq h ρ γ (promote k nh' mH) neq op (Vsem v ρ) (λ b → ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (κ b (λ _ → η̂ tt)))))
                       (cong (node (demoteMem (promote k nh' mH) neq) op 0# (Vsem v ρ)) (funext bAeq)))
  mainStep : Esem (handleE h (val w) e₀) ρ γ
           ≡ φ̂ˢ (promote (S∘ k (S-handleB h w)) nh mH) op (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-handleB h w))) (val (vvar Z))) (ρ ,, b)) γ
  mainStep = trans (trans step1 step3)
                   (cong (λ m → φ̂ˢ m op (Vsem v ρ) (λ b → Esem (plugK (weaken1K (S∘ k (S-handleB h w))) (val (vvar Z))) (ρ ,, b)) γ)
                         (sym (promote-S-handleB-eq k h w nh mH)))

-- Bridges R5's own `fk`/`fl` construction to lemma-B8's own continuation κ.
-- R5 reifies the delimited continuation by weakening k by the WHOLE pair
-- (par × in) and filling its hole with `snd(zP)` (projecting out the
-- resumption value from the freshly-bound pair variable), whereas lemma-B8
-- weakens the SAME k by `in` alone and fills its hole with a bare
-- `val (vvar Z)`. k itself never references either freshly-introduced
-- variable (weaken1K only ever shifts references to OLDER, Γ-level
-- variables), so which one it's weakened by -- and what value/type
-- inhabits it -- is immaterial to k's own contribution; only the
-- projection `snd(zP)` ≡ a needs accounting for, one Esem-step at a time.
-- This is exactly weaken1F-skip/weaken1V-coh/weaken1H-coh's own
-- "an unused extra binding doesn't matter" fact, lifted from a single
-- Frame/Val/Handler to a whole ContCxt, by induction on k mirroring
-- lemma-B8's own ▫/F∘/S∘ case split (but simpler throughout: no
-- promote/φ̂ˢ node-shape bookkeeping is needed here at all, since neither
-- side ever gets stuck on an operation).
fk-match : ∀ {Γ ℓ par τ εH εO} (op : Op ℓ) (k : ContCxt Γ (gnd (in′ op)) εH τ εO)
           (ρ : Env Γ) (p'' : ⟦ gnd par ⟧) (a : ⟦ in′ op ⟧ᴳ)
         → Esem (plugK (weaken1K {υ = gnd par `× gnd (in′ op)} k) (snd (val (vvar Z)))) (ρ ,, (p'' , a))
         ≡ Esem (plugK (weaken1K {υ = gnd (in′ op)} k) (val (vvar Z))) (ρ ,, a)
fk-match {Γ} {par = par} {εH = εH} op ▫ ρ p'' a =
  bindˢ-unitˡ {ε = εH} {X = ⟦ gnd par ⟧ × ⟦ in′ op ⟧ᴳ} {Y = ⟦ in′ op ⟧ᴳ} (λ{ (x , y) → η̂ˢ y }) (p'' , a)
fk-match {par = par} {εO = εO} op (F∘ {β = β} k' f) ρ p'' a = helper (Frame-effect-eq f)
  where
  pairTy = gnd par `× gnd (in′ op)
  inTy   = gnd (in′ op)
  f₁  = weaken1F {υ = pairTy} f
  k'₁ = weaken1K {υ = pairTy} k'
  f₂  = weaken1F {υ = inTy} f
  k'₂ = weaken1K {υ = inTy} k'
  helper : β ≡ εO
         → Esem (plugF f₁ (plugK k'₁ (snd (val (vvar Z))))) (ρ ,, (p'' , a))
         ≡ Esem (plugF f₂ (plugK k'₂ (val (vvar Z)))) (ρ ,, a)
  helper refl = trans step1 (trans step2 (sym step3))
    where
    step1 : Esem (plugF f₁ (plugK k'₁ (snd (val (vvar Z))))) (ρ ,, (p'' , a))
          ≡ bind̂ˢ (λ b → Esem (plugF (weaken1F f₁) (val (vvar Z))) ((ρ ,, (p'' , a)) ,, b))
                  (Esem (plugK k'₁ (snd (val (vvar Z)))) (ρ ,, (p'' , a)))
    step1 = lemma-B6 f₁ (plugK k'₁ (snd (val (vvar Z)))) (ρ ,, (p'' , a))
    step2 : bind̂ˢ (λ b → Esem (plugF (weaken1F f₁) (val (vvar Z))) ((ρ ,, (p'' , a)) ,, b))
                  (Esem (plugK k'₁ (snd (val (vvar Z)))) (ρ ,, (p'' , a)))
          ≡ bind̂ˢ (λ b → Esem (plugF (weaken1F f₂) (val (vvar Z))) ((ρ ,, a) ,, b))
                  (Esem (plugK k'₂ (val (vvar Z))) (ρ ,, a))
    step2 = cong₂ bind̂ˢ (funext (λ b → trans (weaken1F-skip f pairTy ρ (p'' , a) b) (sym (weaken1F-skip f inTy ρ a b))))
                        (fk-match op k' ρ p'' a)
    step3 : Esem (plugF f₂ (plugK k'₂ (val (vvar Z)))) (ρ ,, a)
          ≡ bind̂ˢ (λ b → Esem (plugF (weaken1F f₂) (val (vvar Z))) ((ρ ,, a) ,, b))
                  (Esem (plugK k'₂ (val (vvar Z))) (ρ ,, a))
    step3 = lemma-B6 f₂ (plugK k'₂ (val (vvar Z))) (ρ ,, a)
fk-match op (S∘ k' S-reset) ρ p'' a = cong (λ w → (λ γ → censor (w γ))) (fk-match op k' ρ p'' a)
fk-match op (S∘ k' (S-then sub g)) ρ p'' a = trans step1 (trans step2 (sym step3))
  where
  e₁  = plugK (weaken1K k') (snd (val (vvar Z)))
  e₁' = plugK (weaken1K k') (val (vvar Z))
  δ : _ → Ŵ _ ⊤
  δ c = widenŴ sub (Lsem g ρ c)
  Kf : _ → Ŵ _ _
  Kf (c , r1) = mapŴ (r1 +_) (widenŴ sub (Vsem g ρ c (λ _ → η̂ tt)))
  δ1Eq : ∀ c → widenŴ sub (Lsem (weaken1V g) (ρ ,, (p'' , a)) c) ≡ δ c
  δ1Eq c = cong (widenŴ sub) (renLsem-coh S ρ (ρ ,, (p'' , a)) (λ _ → refl) g c)
  δ2Eq : ∀ c → widenŴ sub (Lsem (weaken1V g) (ρ ,, a) c) ≡ δ c
  δ2Eq c = cong (widenŴ sub) (renLsem-coh S ρ (ρ ,, a) (λ _ → refl) g c)
  K1Eq : ∀ (cr : _ × R) → mapŴ (proj₂ cr +_) (widenŴ sub (Vsem (weaken1V g) (ρ ,, (p'' , a)) (proj₁ cr) (λ _ → η̂ tt))) ≡ Kf cr
  K1Eq (c , r1) = cong (λ w → mapŴ (r1 +_) (widenŴ sub w)) (cong (λ F → F c (λ _ → η̂ tt)) (renV-coh S ρ (ρ ,, (p'' , a)) (λ _ → refl) g))
  K2Eq : ∀ (cr : _ × R) → mapŴ (proj₂ cr +_) (widenŴ sub (Vsem (weaken1V g) (ρ ,, a) (proj₁ cr) (λ _ → η̂ tt))) ≡ Kf cr
  K2Eq (c , r1) = cong (λ w → mapŴ (r1 +_) (widenŴ sub w)) (cong (λ F → F c (λ _ → η̂ tt)) (renV-coh S ρ (ρ ,, a) (λ _ → refl) g))
  step1 : Esem (thenE sub e₁ (weaken1V g)) (ρ ,, (p'' , a))
        ≡ (λ γ → bind̂ (collectX (Esem e₁ (ρ ,, (p'' , a)) δ)) Kf)
  step1 = funext (λ γ → cong₂ (λ w K → bind̂ (collectX w) K) (cong (Esem e₁ (ρ ,, (p'' , a))) (funext δ1Eq)) (funext K1Eq))
  step2 : (λ γ → bind̂ (collectX (Esem e₁ (ρ ,, (p'' , a)) δ)) Kf) ≡ (λ γ → bind̂ (collectX (Esem e₁' (ρ ,, a) δ)) Kf)
  step2 = cong (λ w → (λ γ → bind̂ (collectX w) Kf)) (cong (λ F → F δ) (fk-match op k' ρ p'' a))
  step3 : Esem (thenE sub e₁' (weaken1V g)) (ρ ,, a)
        ≡ (λ γ → bind̂ (collectX (Esem e₁' (ρ ,, a) δ)) Kf)
  step3 = funext (λ γ → cong₂ (λ w K → bind̂ (collectX w) K) (cong (Esem e₁' (ρ ,, a)) (funext δ2Eq)) (funext K2Eq))
fk-match op (S∘ k' (S-glocal sub1 sub2 g)) ρ p'' a = funext (λ γ → trans step1 (trans step2 (sym step3)))
  where
  e₁  = plugK (weaken1K k') (snd (val (vvar Z)))
  e₁' = plugK (weaken1K k') (val (vvar Z))
  δ : _ → Ŵ _ ⊤
  δ c = widenŴ sub1 (Lsem g ρ c)
  δ1Eq : ∀ c → widenŴ sub1 (Lsem (weaken1V g) (ρ ,, (p'' , a)) c) ≡ δ c
  δ1Eq c = cong (widenŴ sub1) (renLsem-coh S ρ (ρ ,, (p'' , a)) (λ _ → refl) g c)
  δ2Eq : ∀ c → widenŴ sub1 (Lsem (weaken1V g) (ρ ,, a) c) ≡ δ c
  δ2Eq c = cong (widenŴ sub1) (renLsem-coh S ρ (ρ ,, a) (λ _ → refl) g c)
  step1 : widenŴ sub2 (Esem e₁ (ρ ,, (p'' , a)) (λ c → widenŴ sub1 (Lsem (weaken1V g) (ρ ,, (p'' , a)) c)))
        ≡ widenŴ sub2 (Esem e₁ (ρ ,, (p'' , a)) δ)
  step1 = cong (λ w → widenŴ sub2 (Esem e₁ (ρ ,, (p'' , a)) w)) (funext δ1Eq)
  step2 : widenŴ sub2 (Esem e₁ (ρ ,, (p'' , a)) δ) ≡ widenŴ sub2 (Esem e₁' (ρ ,, a) δ)
  step2 = cong (λ w → widenŴ sub2 (w δ)) (fk-match op k' ρ p'' a)
  step3 : widenŴ sub2 (Esem e₁' (ρ ,, a) (λ c → widenŴ sub1 (Lsem (weaken1V g) (ρ ,, a) c)))
        ≡ widenŴ sub2 (Esem e₁' (ρ ,, a) δ)
  step3 = cong (λ w → widenŴ sub2 (Esem e₁' (ρ ,, a) w)) (funext δ2Eq)
fk-match op (S∘ k' (S-handleB h w)) ρ p'' a = trans step1 (trans step2 (sym step3))
  where
  e₁  = plugK (weaken1K k') (snd (val (vvar Z)))
  e₁' = plugK (weaken1K k') (val (vvar Z))
  step1 : Esem (handleE (renH S h) (val (renV S w)) e₁) (ρ ,, (p'' , a))
        ≡ handlerSem (renH S h) (ρ ,, (p'' , a)) (Vsem (renV S w) (ρ ,, (p'' , a))) (Esem e₁ (ρ ,, (p'' , a)))
  step1 = funext (λ γ → cong (λ F → F γ)
            (bindˢ-unitˡ (λ p → handlerSem (renH S h) (ρ ,, (p'' , a)) p (Esem e₁ (ρ ,, (p'' , a)))) (Vsem (renV S w) (ρ ,, (p'' , a)))))
  step2 : handlerSem (renH S h) (ρ ,, (p'' , a)) (Vsem (renV S w) (ρ ,, (p'' , a))) (Esem e₁ (ρ ,, (p'' , a)))
        ≡ handlerSem h ρ (Vsem w ρ) (Esem e₁' (ρ ,, a))
  step2 = funext (λ γ →
            trans (weaken1H-coh _ h ρ (p'' , a) (Vsem (renV S w) (ρ ,, (p'' , a))) (Esem e₁ (ρ ,, (p'' , a))) γ)
            (trans (cong (λ p → handlerSem h ρ p (Esem e₁ (ρ ,, (p'' , a))) γ) (weaken1V-coh _ w ρ (p'' , a)))
                   (cong (λ F → handlerSem h ρ (Vsem w ρ) F γ) (fk-match op k' ρ p'' a))))
  step3 : Esem (handleE (renH S h) (val (renV S w)) e₁') (ρ ,, a)
        ≡ handlerSem h ρ (Vsem w ρ) (Esem e₁' (ρ ,, a))
  step3 = funext (λ γ →
            trans (cong (λ F → F γ) (bindˢ-unitˡ (λ p → handlerSem (renH S h) (ρ ,, a) p (Esem e₁' (ρ ,, a))) (Vsem (renV S w) (ρ ,, a))))
            (trans (weaken1H-coh _ h ρ a (Vsem (renV S w) (ρ ,, a)) (Esem e₁' (ρ ,, a)) γ)
                   (cong (λ p → handlerSem h ρ p (Esem e₁' (ρ ,, a)) γ) (weaken1V-coh _ w ρ a))))

lemma-B8-S∘ : ∀ {Γ ℓ εH α β τ εO} (op : Op ℓ) (v : Val Γ (gnd (out op)))
            (k : ContCxt Γ (gnd (in′ op)) εH α β) (s : SFrame Γ α β τ εO) (mH : ℓ ∈ εH) (nh : ¬ Handles (S∘ k s) ℓ)
            (ρ : Env Γ) (γ : ⟦ τ ⟧ → Ŵ εO ⊤)
          → Esem (plugK (S∘ k s) (opE mH op (val v))) ρ γ
          ≡ φ̂ˢ (promote (S∘ k s) nh mH) op (Vsem v ρ) (λ a → Esem (plugK (weaken1K (S∘ k s)) (val (vvar Z))) (ρ ,, a)) γ
lemma-B8-S∘ op v k S-reset mH nh ρ γ = cong censor (lemma-B8 op v k mH nh ρ γ)
lemma-B8-S∘ op v k (S-then sub g) mH nh ρ γ = lemma-B8-S∘-then op v k sub g mH nh ρ γ
lemma-B8-S∘ op v k (S-glocal sub1 sub2 g) mH nh ρ γ = lemma-B8-S∘-glocal op v k sub1 sub2 g mH nh ρ γ
lemma-B8-S∘ op v k (S-handleB h w) mH nh ρ γ = lemma-B8-S∘-handleB op v k h w mH nh ρ γ

-- Base case ▫: exactly the (op)(v) clause of Fig. 9, plus the Ŝ unit law.
lemma-B8 op v ▫ mH nh ρ γ = cong (λ F → F γ) (bindˢ-unitˡ (λ a → φ̂ˢ mH op a η̂ˢ) (Vsem v ρ))
lemma-B8 op v (F∘ k f) mH nh ρ γ = lemma-B8-F∘ op v k f mH nh ρ γ
lemma-B8 op v (S∘ k s) mH nh ρ γ = lemma-B8-S∘ op v k s mH nh ρ γ

-- k1v-match: R5-gen's k1v (built by applying handlerΨ's OWN outer-D-fed
-- continuation ONLY at the final p'') agrees with a genuinely FRESH
-- handlerSem call at p'' -- confirmed empirically first (B5Core.agda's
-- PLeakCheck: a handler whose ret reports its own parameter directly as
-- a loss, applied through a k containing a nested same-label operation,
-- shows NO discrepancy between the two constructions). The reason: D's
-- own "outer p" only ever gets consulted at a NATURAL value-terminal leaf
-- of κ's own evaluation (a point where the underlying term is genuinely
-- `val v`), and there Esem's own η̂ˢ is UNCONDITIONALLY continuation-
-- independent (η̂ˢ x γ = leaf 0# x, regardless of γ). Formalised below as
-- a general parametricity/logical-relations argument: `Esem e ρ` never
-- actually depends on its own continuation, GIVEN ρ's own function-typed
-- bindings don't either (needed since e.g. a handler clause's own `app`
-- of a free variable could otherwise be adversarial) -- a type-indexed
-- relation GConstV/GConstW/GConstE/GConstEnv, proved by mutual induction
-- over Val/Term mirroring Vsem/Esem's own mutual definition.

-- ---------------------------------------------------------------------
-- GConst: "genuinely continuation-independent", a logical relation
-- indexed by type. At ground types every value trivially qualifies
-- (ground values carry no hidden continuation-sensitivity at all). At
-- product types, both components must. At function types, applying the
-- function to ANY GConst-qualifying argument must yield a GConst-
-- qualifying Ŝ-computation (GConstE below) -- this is what lets `app`'s
-- case go through even when the function comes from a free variable,
-- PROVIDED the environment supplying it (GConstEnv) is itself assumed
-- GConst throughout.
-- ---------------------------------------------------------------------

mutual
  GConstV : (σ : Ty) → ⟦ σ ⟧ → Set
  GConstV (gnd γ)     x       = ⊤
  GConstV (σ `× τ)    (a , b) = GConstV σ a × GConstV τ b
  GConstV (σ ⇒ τ ! ε) f       = ∀ (a : ⟦ σ ⟧) → GConstV σ a → GConstE τ ε (f a)

  -- Every leaf payload reachable in a Ŵ-tree is GConstV (node shape/labels
  -- themselves carry no continuation-sensitivity to speak of -- only what
  -- VALUE eventually gets produced, at any leaf, however deep).
  GConstW : (σ : Ty) (ε : EffCxt) → Ŵ ε ⟦ σ ⟧ → Set
  GConstW σ ε (leaf r x)        = GConstV σ x
  GConstW σ ε (node m op r o κ) = ∀ b → GConstW σ ε (κ b)

  -- A Ŝ-computation is GConst if (a) its own Ŵ-tree result doesn't depend
  -- on which continuation it's fed, and (b) whatever it produces (at any
  -- leaf, for any continuation -- (a) makes these the same tree anyway) is
  -- itself GConstV.
  GConstE : (σ : Ty) (ε : EffCxt) → Ŝ ε ⟦ σ ⟧ → Set
  GConstE σ ε F = (∀ γ1 γ2 → F γ1 ≡ F γ2) × (∀ γ → GConstW σ ε (F γ))

GConstEnv : (Γ : Cxt) → Env Γ → Set
GConstEnv Γ ρ = ∀ {σ} (x : Γ ∋ σ) → GConstV σ (ρ x)

GConstEnv-,, : ∀ {Γ σ} {ρ : Env Γ} {a : ⟦ σ ⟧} → GConstEnv Γ ρ → GConstV σ a → GConstEnv (Γ , σ) (ρ ,, a)
GConstEnv-,, gcρ gca Z     = gca
GConstEnv-,, gcρ gca (S x) = gcρ x

-- tell/widenŴ/censor only ever touch a Ŵ-tree's own r-fields (loss
-- bookkeeping) -- never the leaf payload or the node shape/children --
-- so GConstW (a property purely of leaf payloads) passes through them
-- unchanged, by direct case analysis (no induction needed: each clause
-- literally reuses the same children/leaf-value).
tell-GConstW : ∀ σ {ε} (r : R) (w : Ŵ ε ⟦ σ ⟧) → GConstW σ ε w → GConstW σ ε (tell r w)
tell-GConstW σ r (leaf r₀ x)        gw = gw
tell-GConstW σ r (node m op r₀ o κ) gw = gw

widenŴ-GConstW : ∀ σ {ε ε'} (sub : ε ⊆ᵉ ε') (w : Ŵ ε ⟦ σ ⟧) → GConstW σ ε w → GConstW σ ε' (widenŴ sub w)
widenŴ-GConstW σ sub (leaf r x)        gw = gw
widenŴ-GConstW σ sub (node m op r o κ) gw = λ b → widenŴ-GConstW σ sub (κ b) (gw b)

censor-GConstW : ∀ σ {ε} (w : Ŵ ε ⟦ σ ⟧) → GConstW σ ε w → GConstW σ ε (censor w)
censor-GConstW σ (leaf r x)        gw = gw
censor-GConstW σ (node m op r o κ) gw = λ b → censor-GConstW σ (κ b) (gw b)

-- bind̂ W g ≡ bind̂ W g' whenever g,g' merely agree on every leaf VALUE W
-- itself actually contains (not universally) -- exactly what's needed
-- since g will only ever be instantiated (below) at values already known
-- GConstV, not at arbitrary ones.
bind̂-GConst-cong : ∀ σ {ε Y} (W : Ŵ ε ⟦ σ ⟧) → GConstW σ ε W → (g1 g2 : ⟦ σ ⟧ → Ŵ ε Y)
                  → (∀ x → GConstV σ x → g1 x ≡ g2 x) → bind̂ W g1 ≡ bind̂ W g2
bind̂-GConst-cong σ (leaf r x)        gW g1 g2 geq = cong (tell r) (geq x gW)
bind̂-GConst-cong σ (node m op r o κ) gW g1 g2 geq = cong (λ κ' → node m op (r + 0#) o κ') (funext (λ b → bind̂-GConst-cong σ (κ b) (gW b) g1 g2 geq))

-- GConstW is preserved by bind̂, given the outer tree's own leaves are
-- GConstV and g maps any GConstV-satisfying leaf to a GConstW-satisfying
-- result.
bind̂-GConstW : ∀ σ {ε} τ (W : Ŵ ε ⟦ σ ⟧) → GConstW σ ε W → (g : ⟦ σ ⟧ → Ŵ ε ⟦ τ ⟧)
             → (∀ x → GConstV σ x → GConstW τ ε (g x)) → GConstW τ ε (bind̂ W g)
bind̂-GConstW σ τ (leaf r x)        gW g gG = tell-GConstW τ r (g x) (gG x gW)
bind̂-GConstW σ τ (node m op r o κ) gW g gG = λ b → bind̂-GConstW σ τ (κ b) (gW b) g gG

-- Lifts GConst through bind̂ˢ: given F is GConst, and f maps any GConstV
-- leaf of F to a GConst Ŝ-computation, bind̂ˢ f F is GConst too.
bindˢ-GConst : ∀ σ {ε} τ (f : ⟦ σ ⟧ → Ŝ ε ⟦ τ ⟧) (F : Ŝ ε ⟦ σ ⟧)
             → GConstE σ ε F → (∀ x → GConstV σ x → GConstE τ ε (f x)) → GConstE τ ε (bind̂ˢ f F)
bindˢ-GConst σ {ε} τ f F (Fconst , FleafG) fG = tconst , tleaf
  where
  tconst : ∀ γ1 γ2 → bind̂ˢ f F γ1 ≡ bind̂ˢ f F γ2
  tconst γ1 γ2 =
    trans (bind̂-GConst-cong σ (F (λ x → R̂-of (f x) γ1)) (FleafG (λ x → R̂-of (f x) γ1))
                            (λ x → f x γ1) (λ x → f x γ2)
                            (λ x gcx → proj₁ (fG x gcx) γ1 γ2))
          (cong (λ w → bind̂ w (λ x → f x γ2)) (Fconst (λ x → R̂-of (f x) γ1) (λ x → R̂-of (f x) γ2)))
  tleaf : ∀ γ → GConstW τ ε (bind̂ˢ f F γ)
  tleaf γ = bind̂-GConstW σ τ (F (λ x → R̂-of (f x) γ)) (FleafG (λ x → R̂-of (f x) γ))
                          (λ x → f x γ) (λ x gcx → proj₂ (fG x gcx) γ)

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
⌊_⌋[_,_] : ∀ {Γ σ ε εg} → LC Γ σ εg → εg ⊆ᵉ ε → Env Γ → ⟦ σ ⟧ → Ŵ ε ⊤
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

-- ATTEMPTED, and REFUTED: a hoped-for "step-g-irrelevant" lemma, retargeting
-- any derivation g1⊢e-[r]→e' to an arbitrary g2⊢e-[r]→e' (same e,e',r) at
-- the SAME εg. Every other constructor (R1-R9 minus R5, F-rule, S1-S4) is
-- fine -- none of them pattern-match on g, and F-rule/S1 just recurse at the
-- compound ambient built from g2 instead of g1. But R5's own conclusion
-- (see OpSem.agda) literally embeds g (via renV S g, into fk/fl, substituted
-- into the handler clause body) -- so g1⊢e-[r]→e' and g2⊢e-[r]→e' are
-- derivations of DIFFERENT target terms e' whenever g1 ≠ g2 and the
-- derivation bottoms out in R5. "▶ disregards g" (S2's own remark) does NOT
-- extend to R5: R5 reifies the CURRENT ambient into the delimited
-- continuation it produces, by design (the §8 erratum fix), so the target
-- term is genuinely g-dependent there. This kills the general lemma as a
-- tool for theorem-B9-F/F-pairL -- see the writeup delivered alongside this
-- comment for what remains viable.

-- NoR5 stp: stp never invokes R5 anywhere in its structure. Checked
-- recursively through F-rule/S1's own inner hypothesis (the only two
-- constructors that recurse under the SAME ambient-swap we're doing);
-- S2/S3's inner hypothesis is irrelevant here since it's judged under its
-- own g1, never the outer g we're retargeting -- and, like every other
-- non-F-rule/S1/R5/S4 constructor, S2/S3's own conclusion doesn't mention
-- g at all (only R5 embeds it), so those cases are trivially retargetable
-- regardless of what their inner derivation contains.
NoR5 : ∀ {Γ σ ε εg} {g : LC Γ σ εg} {e e' : Γ ⊢ σ ! ε} {r : R} → g ⊢ e -[ r ]→ e' → Set
NoR5 (R1 f x)                    = ⊤
NoR5 (R2-fst v w)                = ⊤
NoR5 (R2-snd v w)                = ⊤
NoR5 (R3 e v)                    = ⊤
NoR5 (R4 r)                      = ⊤
NoR5 (R6 h v1 v2)                = ⊤
NoR5 (R7 sub v e)                = ⊤
NoR5 (R8 sub1 sub2 v g1')        = ⊤
NoR5 (R9 v)                      = ⊤
NoR5 (F-rule sub f stp)          = NoR5 stp
NoR5 (S1 sub h v stp)            = NoR5 stp
NoR5 (S2 sub g1' stp)            = ⊤
NoR5 (S3 sub1 sub2 g1' stp)      = ⊤
NoR5 (S4 stp)                    = NoR5 stp
NoR5 (R5 sub h v1 m op v2 k nh)  = ⊥

-- step-g-irrelevant, restricted to R5-free derivations: every OTHER
-- constructor's conclusion is genuinely independent of its own ambient g
-- (checked directly against OpSem.agda -- R1-R4/R6-R9/S2/S3 never mention
-- g in the produced term at all; F-rule/S1 only ever feed g into the
-- COMPOUND ambient for their recursive inner hypothesis, never into the
-- outer plugF f e'/handleE h (val v) e' result directly), so a NoR5
-- witness lets us swap g1↦g2 freely by structural induction.
step-g-irrelevant : ∀ {Γ σ ε εg} {g1 : LC Γ σ εg} (g2 : LC Γ σ εg) {e e' : Γ ⊢ σ ! ε} {r : R}
                   → (stp : g1 ⊢ e -[ r ]→ e') → NoR5 stp → g2 ⊢ e -[ r ]→ e'
step-g-irrelevant g2 (R1 f x)             _   = R1 f x
step-g-irrelevant g2 (R2-fst v w)         _   = R2-fst v w
step-g-irrelevant g2 (R2-snd v w)         _   = R2-snd v w
step-g-irrelevant g2 (R3 e v)             _   = R3 e v
step-g-irrelevant g2 (R4 r)               _   = R4 r
step-g-irrelevant g2 (R6 h v1 v2)         _   = R6 h v1 v2
step-g-irrelevant g2 (R7 sub v e)         _   = R7 sub v e
step-g-irrelevant g2 (R8 sub1 sub2 v g1') _   = R8 sub1 sub2 v g1'
step-g-irrelevant g2 (R9 v)               _   = R9 v
step-g-irrelevant g2 (F-rule {α = α} sub f stp) nr5 =
  F-rule sub f (step-g-irrelevant (vabs (thenE sub (plugF (weaken1F f) (val (vvar Z))) (weaken1V g2))) stp nr5)
step-g-irrelevant g2 (S1 {σ' = σ'} sub h v stp) nr5 =
  S1 sub h v (step-g-irrelevant (vabs (thenE sub (retApplied h v) (weaken1V g2))) stp nr5)
step-g-irrelevant g2 (S2 sub g1' stp)     _   = S2 sub g1' stp
step-g-irrelevant g2 (S3 sub1 sub2 g1' stp) _ = S3 sub1 sub2 g1' stp
step-g-irrelevant g2 (S4 stp)             nr5 = S4 (step-g-irrelevant g2 stp nr5)
step-g-irrelevant g2 (R5 sub h v1 m op v2 k nh) ()

-- Theorem 7.9/B.9's own type, forward-declared so theorem-B9-S3/S4 below
-- can recurse into it directly (on the *given*, structurally smaller step
-- derivation) rather than being separate postulates.
theorem-B9 : ∀ {Γ σ ε εg} (sub : εg ⊆ᵉ ε) {g : LC Γ σ εg} {e e' : Γ ⊢ σ ! ε} {r : R} → g ⊢ e -[ r ]→ e' → (ρ : Env Γ)
           → Esem e ρ ⌊ g ⌋[ sub , ρ ] ≡ tell r (Esem e' ρ ⌊ g ⌋[ sub , ρ ])

-- (F)'s own type, likewise forward-declared: its body (below, past
-- lemma-B6/miniB7-value) recurses into theorem-B9 on the given,
-- structurally smaller step derivation, mirroring theorem-B9-S2/S3/S4.
theorem-B9-F : ∀ {Γ σ ε εg α} (sub : εg ⊆ᵉ ε) {g : LC Γ σ εg} (f : Frame Γ α ε σ ε) {e e' : Γ ⊢ α ! ε} {r : R}
  → vabs (thenE sub (plugF (weaken1F f) (val (vvar Z))) (weaken1V g)) ⊢ e -[ r ]→ e' → (ρ : Env Γ)
  → Esem (plugF f e) ρ ⌊ g ⌋[ sub , ρ ] ≡ tell r (Esem (plugF f e') ρ ⌊ g ⌋[ sub , ρ ])

-- Two simple facts about how widenŴ/censor commute with tell (both by a
-- direct case split, no induction needed -- unlike collapse, neither of
-- these ever touches a leaf's *payload*, only its root-loss slot, so
-- there's nothing for them to disagree about the way collapse and tell
-- did in the B.5 investigation).
widenŴ-tell-comm : ∀ {ε ε' X} (sub : ε ⊆ᵉ ε') (r : R) (w : Ŵ ε X) → widenŴ sub (tell r w) ≡ tell r (widenŴ sub w)
widenŴ-tell-comm sub r (leaf r₀ x)        = refl
widenŴ-tell-comm sub r (node m op r₀ o κ) = refl

censor-tell-absorb : ∀ {ε X} (r : R) (w : Ŵ ε X) → censor (tell r w) ≡ censor w
censor-tell-absorb r (leaf r₀ x)        = refl
censor-tell-absorb r (node m op r₀ o κ) = refl

-- Lemma B.9's glocal congruence (S3): unlike (F)/(S1)/(R5)/(R7), the
-- given step g1⊢e-[r]→e' is already stated at glocalE's own ambient (g1,
-- sub1) -- no need to relate ⌊g⌋ to Lsem of some *new* compound
-- continuation via collapse (that's what made B.5/B.7 hard), just push
-- the IH's `tell r` through the frame's own outer widenŴ sub2.
theorem-B9-S3 : ∀ {Γ ε ε₂ ε₁ σ} (sub1 : ε₂ ⊆ᵉ ε₁) (sub2 : ε₁ ⊆ᵉ ε) {εamb} (subamb : εamb ⊆ᵉ ε) {g : LC Γ σ εamb} (g1 : LC Γ σ ε₂)
    {e e' : Γ ⊢ σ ! ε₁} {r : R}
  → g1 ⊢ e -[ r ]→ e' → (ρ : Env Γ)
  → Esem (glocalE sub1 sub2 e g1) ρ ⌊ g ⌋[ subamb , ρ ] ≡ tell r (Esem (glocalE sub1 sub2 e' g1) ρ ⌊ g ⌋[ subamb , ρ ])
theorem-B9-S3 sub1 sub2 subamb g1 stp ρ =
  trans (cong (widenŴ sub2) (theorem-B9 sub1 stp ρ)) (widenŴ-tell-comm sub2 _ _)

-- Lemma B.9's reset congruence (S4): same story -- the given step is
-- already at the SAME ambient (g, sub) theorem-B9-S4 itself is stated
-- for, so no Lsem/collapse detour is needed, just censor absorbing
-- whatever tell the IH produces.
theorem-B9-S4 : ∀ {Γ ε εg σ} {g : LC Γ σ εg} {e e' : Γ ⊢ σ ! ε} {r : R}
  → g ⊢ e -[ r ]→ e' → (ρ : Env Γ) (sub : εg ⊆ᵉ ε)
  → Esem (resetE e) ρ ⌊ g ⌋[ sub , ρ ] ≡ tell 0# (Esem (resetE e') ρ ⌊ g ⌋[ sub , ρ ])
theorem-B9-S4 {g = g} stp ρ sub =
  trans (cong censor (theorem-B9 sub stp ρ)) (trans (censor-tell-absorb _ _) (sym (tell-0 _)))

widenŴ-refl : ∀ {ε X} (w : Ŵ ε X) → widenŴ ⊆ᵉ-refl w ≡ w
widenŴ-refl (leaf r x)        = refl
widenŴ-refl (node m op r o κ) = cong (node m op r o) (funext (λ a → widenŴ-refl (κ a)))

-- collapse discards root-loss at every level unconditionally -- neither
-- of collapse's own clauses ever inspects the root it's handed, so
-- prepending any `tell r` is invisible to it.
collapse-tell : ∀ {ε} (r : R) (W : Ŵ ε R) → collapse (tell r W) ≡ collapse W
collapse-tell r (leaf r₀ x)        = refl
collapse-tell r (node m op r₀ o κ) = refl

-- Consequently collapse also can't see a `tell r` applied *after* a
-- bind̂ (as opposed to wrapping the whole bind̂), by induction using
-- collapse-tell at each level.
collapse-bind̂-tell : ∀ {ε X} (r : R) (T : Ŵ ε X) (K : X → Ŵ ε R)
  → collapse (bind̂ T (λ x → tell r (K x))) ≡ collapse (bind̂ T K)
collapse-bind̂-tell r (leaf r₀ x) K =
  trans (collapse-tell r₀ (tell r (K x))) (trans (collapse-tell r (K x)) (sym (collapse-tell r₀ (K x))))
collapse-bind̂-tell r (node m op r₀ o κ) K =
  trans (collapse-tell r₀ (node m op 0# o (λ a → bind̂ (κ a) (λ x → tell r (K x)))))
        (trans (cong (node m op 0# o) (funext (λ a → collapse-bind̂-tell r (κ a) K)))
               (sym (collapse-tell r₀ (node m op 0# o (λ a → bind̂ (κ a) K)))))

-- collapse(shift 0# T) ≡ collapse T -- NOT because shift 0# is the
-- identity (it isn't: at a node, collectX still redistributes the node's
-- own root loss down into its leaves even when the *added* amount is 0#,
-- confirmed false concretely in B5Core.agda's shift0Test-refuted) -- but
-- because collapse discards root-loss at *every* level regardless (see
-- collapse-tell), so it can't see that redistribution. (The further
-- generalisation "collapse(shift r T) ≡ tell r(collapse T)" is FALSE for
-- r ≠ 0#, confirmed concretely in B5Core.agda's collapseShiftGen-check
-- failing at r=10 -- this really is specific to r=0#.)
collapse-shift-0 : ∀ {ε} (T : Ŵ ε R) → collapse (shift 0# T) ≡ collapse T
collapse-shift-0 (leaf r x) = cong (λ z → leaf z tt) (+-identityˡ x)
collapse-shift-0 (node m op r o κ) =
  cong (node m op 0# o) (funext (λ a →
    trans (cong collapse (bump-shift r (collectX (κ a)) (λ x r1 → tell r1 (η̂ (0# + x)))))
          (trans (cong collapse (cong (bind̂ (collectX (κ a)))
                                       (funext (λ { (x , r1) → tell-+ r r1 (η̂ (0# + x)) }))))
                 (trans (collapse-bind̂-tell r (collectX (κ a)) (λ { (x , r1) → tell r1 (η̂ (0# + x)) }))
                        (collapse-shift-0 (κ a))))))

-- mapŴ (0# +_) is the identity -- unlike shift 0#, this holds outright
-- (mapŴ only ever touches leaf payloads, never redistributes anything
-- through node structure, so there's no root-loss-vs-node subtlety
-- here at all).
mapŴ-plus-0 : ∀ {ε} (T : Ŵ ε R) → mapŴ (0# +_) T ≡ T
mapŴ-plus-0 (leaf r x)        = cong (leaf r) (+-identityˡ x)
mapŴ-plus-0 (node m op r o κ) = cong (node m op r o) (funext (λ a → mapŴ-plus-0 (κ a)))

-- widenŴ commutes with collapse (both recurse through the tree structure
-- untouched by the other -- widenŴ only rewrites a node's membership
-- witness, collapse only rewrites root-loss/leaf-payload).
collapse-widenŴ-comm : ∀ {ε ε'} (sub : ε ⊆ᵉ ε') (W : Ŵ ε R) → collapse (widenŴ sub W) ≡ widenŴ sub (collapse W)
collapse-widenŴ-comm sub (leaf r x)        = refl
collapse-widenŴ-comm sub (node m op r o κ) = cong (node (sub m) op 0# o) (funext (λ a → collapse-widenŴ-comm sub (κ a)))

-- The "companion-free" special case of Lemma 7.7/B.7: whenever a regular
-- frame's F[x] reduces to a *bare value transport* η̂ˢ(φ x) -- i.e. F has
-- no separate companion subexpression that could itself discard a loss
-- (F-fun, F-fst, F-snd) -- Lsem(λx.F[x]▶g) agrees with R̂ε(Ssem(F[x])|g)
-- EXACTLY, not just approximately: the accumulated loss r1 that a
-- companion would otherwise contribute is identically 0#, which is
-- exactly the case collapse-shift-0 (not the false general "shift r is
-- the identity") settles. bodyE stands for plugF(weaken1F f)(val(vvar Z)).
miniB7-value : ∀ {Γ ε εg σ τ} (sub : εg ⊆ᵉ ε) (g : LC Γ τ εg) (ρ : Env Γ) (φ : ⟦ σ ⟧ → ⟦ τ ⟧) (bodyE : (Γ , σ) ⊢ τ ! ε)
             → (∀ (a : ⟦ σ ⟧) → Esem bodyE (ρ ,, a) ≡ η̂ˢ (φ a))
             → (a : ⟦ σ ⟧) → Lsem (vabs (thenE sub bodyE (weaken1V g))) ρ a ≡ R̂-of (η̂ˢ (φ a)) ⌊ g ⌋[ sub , ρ ]
miniB7-value {σ = σ} {τ = τ} sub g ρ φ bodyE bodyEq a = trans step2 step5
  where
  δ' : R → Ŵ _ ⊤
  δ' = λ _ → η̂ tt
  γ1 : ⟦ τ ⟧ → Ŵ _ ⊤
  γ1 = λ c → widenŴ sub (Lsem (weaken1V g) (ρ ,, a) c)

  step2 : Lsem (vabs (thenE sub bodyE (weaken1V g))) ρ a
        ≡ collapse (bind̂ (collectX (η̂ˢ (φ a) γ1))
                         (λ { (c , r1) → mapŴ (r1 +_) (widenŴ sub (Vsem (weaken1V g) (ρ ,, a) c δ')) }))
  step2 = cong (λ F → collapse (bind̂ (collectX (F γ1))
                                     (λ { (c , r1) → mapŴ (r1 +_) (widenŴ sub (Vsem (weaken1V g) (ρ ,, a) c δ')) })))
              (bodyEq a)

  step5 : collapse (bind̂ (collectX (η̂ˢ (φ a) γ1))
                         (λ { (c , r1) → mapŴ (r1 +_) (widenŴ sub (Vsem (weaken1V g) (ρ ,, a) c δ')) }))
        ≡ R̂-of (η̂ˢ (φ a)) ⌊ g ⌋[ sub , ρ ]
  step5 = trans (cong (λ v → collapse (tell 0# (mapŴ (0# +_) (widenŴ sub (v (φ a) δ')))))
                       (weaken1V-coh σ g ρ a))
                (trans (collapse-tell 0# _)
                       (trans (cong collapse (mapŴ-plus-0 (widenŴ sub (Vsem g ρ (φ a) δ'))))
                              (trans (collapse-widenŴ-comm sub (Vsem g ρ (φ a) δ'))
                                     (sym (tell-0 _)))))

-- (F) itself is no longer wholly postulated. Its "companion-free" cases
-- -- F-fun, F-fst, F-snd (bare value-transports η̂ˢ(φ x), via miniB7-value/
-- theorem-B9-F-value-transport) and F-op (constructs a fresh node
-- φ̂ˢ m op x η̂ˢ instead, via miniB7-op/theorem-B9-F-op, same toolkit
-- adapted to the node-shaped case) -- none of these have a separate
-- companion subexpression that could discard its own loss, which is
-- exactly why they're provable unconditionally, using only lemma-B6
-- (already unconditional) plus collapse-tell/collapse-bind̂-tell/
-- collapse-shift-0/collapse-widenŴ-comm (all provably true, none needing
-- B.5(3)). The remaining shapes -- F-pairL, F-pairR, F-appL, F-appR (each
-- has a companion subexpression whose own discarded loss is exactly what
-- breaks the general Lemma B.7 route), F-loss (whose Lemma B.6 case
-- already rests on postulate-Ŝ-tell-naturality), and F-handleP
-- (handler-shaped, comparable in difficulty to (S1)/(R5)) -- are
-- collected in theorem-B9-F-companion, declared here (ahead of
-- theorem-B9-F's own body below) so its clauses can delegate to it.
-- ---------------------------------------------------------------------
-- theorem-B9-gen / theorem-B9-F-gen: theorem-B9's conclusion GENERALISED
-- to hold at an ARBITRARY continuation γ:⟦σ⟧→Ŵε⊤, not just the specific
-- ⌊g⌋[sub,ρ] built from the given step's own ambient g.
--
-- Motivation: theorem-B9-F's companion-bearing cases (F-pairL etc.) got
-- stuck because Esem(pair e e₂)ργ's own bind̂ˢ-unfolding forces e's
-- evaluation to receive a continuation D built from e₂/γ, NOT
-- δ:=Lsem(g*)ρ (what theorem-B9's IH is stated at) -- and relating D to
-- δ needs exactly the FALSE mini-B7-style identity refuted concretely
-- via B5Core.agda's collapseMapGen-refuted/b9F6-* (a dirty AMBIENT g
-- applied to the companion's own value, i.e. Vsem gρ(a,b)δ' node-shaped,
-- is exactly where collapse/mapŴ disagree). But if theorem-B9 holds at
-- ANY γ, we can apply the IH DIRECTLY at γ:=D -- no bridge needed, and
-- (as the proof below shows) no case-split on the frame's own shape
-- either: it works identically for every regular frame lemma-B6 covers.
--
-- Hand-checked (and explains exactly why (R7) is false vs true): every
-- OpSem-*active* clause (thenE, glocalE, lossE) ignores its own λγ
-- argument entirely (ONLY consults its embedded ambient's own Lsem, at
-- a fixed δ'=λ_→η̂tt) -- so (R4), (R7), (S2), (S3) each end up proving
-- an equation between two γ-CONSTANT expressions: the generalisation
-- costs nothing, it's the SAME proof term with γ renamed throughout.
-- (S4) threads the SAME outer γ into its own recursive call unchanged,
-- so it also generalises for free. Only (S1) and (R5) are genuinely
-- γ-dependent, through handleE's own non-thenE-shaped clause (its own
-- bind̂ˢ threads γ down to the SECOND/body argument, not lemma-B6's
-- position) -- kept as (correspondingly generalised) postulates,
-- matching their pre-existing unproven status; the goal here is only to
-- discharge theorem-B9-F-companion's postulate, not those two.
-- ---------------------------------------------------------------------

theorem-B9-gen : ∀ {Γ σ ε εg} {g : LC Γ σ εg} {e e' : Γ ⊢ σ ! ε} {r : R}
                → g ⊢ e -[ r ]→ e' → (ρ : Env Γ) (γ : ⟦ σ ⟧ → Ŵ ε ⊤)
                → Esem e ρ γ ≡ tell r (Esem e' ρ γ)

theorem-B9-F-gen : ∀ {Γ σ ε εg α} (sub : εg ⊆ᵉ ε) {g : LC Γ σ εg} (f : Frame Γ α ε σ ε) {e e' : Γ ⊢ α ! ε} {r : R}
  → vabs (thenE sub (plugF (weaken1F f) (val (vvar Z))) (weaken1V g)) ⊢ e -[ r ]→ e' → (ρ : Env Γ) (γ : ⟦ σ ⟧ → Ŵ ε ⊤)
  → Esem (plugF f e) ρ γ ≡ tell r (Esem (plugF f e') ρ γ)

-- handlerAlg h ρ γ's own carrier is a FUNCTION type (⟦gnd par⟧→Ŵε⟦σ'⟧),
-- with act r g = λp→tell r(g p) -- a "tell wrapped around a function
-- application", exactly parallel to Ŵ-alg's own act=tell (which is what
-- makes tell-bind̂-comm hold). Same two-case proof, since neither leaf
-- nor node case of ext̂ ever inspects act beyond this shape, and tell
-- only ever touches a tree's own root-loss field (never m/op/o/κ), so
-- the node case's ψ-built branches are identical on both sides.
handlerAlg-tell-comm : ∀ {Γ ℓ par σ σ' ε X} (h : Handler Γ ℓ par σ σ' ε) (ρ : Env Γ) (γ : ⟦ σ' ⟧ → Ŵ ε ⊤)
  (f : X → ⟦ gnd par ⟧ → Ŵ ε ⟦ σ' ⟧) (r : R) (W : Ŵ (ε ,ℓ ℓ) X) (p : ⟦ gnd par ⟧)
  → ext̂ (handlerAlg h ρ γ) f (tell r W) p ≡ tell r (ext̂ (handlerAlg h ρ γ) f W p)
handlerAlg-tell-comm h ρ γ f r (leaf r₀ x) p = tell-+ r r₀ (f x p)
handlerAlg-tell-comm h ρ γ f r (node m op r₀ o κ) p =
  tell-+ r r₀ (handlerΨ h ρ γ m op o (λ a → ext̂ (handlerAlg h ρ γ) f (κ a)) p)

-- theorem-B9-S1-gen, PROVEN (not postulated): exactly the same trick as
-- theorem-B9-F-gen -- unfold Esem(handleE h(val v)e)ργ (via bindˢ-unitˡ,
-- since e1=val v is already a value) down to ext̂(handlerAlghργ)
-- (handlerRethργ)(EsemeρD)p for the continuation D e's own evaluation is
-- ALREADY forced by handlerSem's definition to receive -- apply
-- theorem-B9-gen directly at γ:=D (no relation to the given step's own
-- compound ambient vabs(thenE...) needed at all), then push tell r out
-- with handlerAlg-tell-comm instead of tell-bind̂-comm.
theorem-B9-S1-gen : ∀ {Γ ε εamb ℓ par σ σ'} (sub : εamb ⊆ᵉ ε) {g : LC Γ σ' εamb} (h : Handler Γ ℓ par σ σ' ε) (v : Val Γ (gnd par))
    {e e' : Γ ⊢ σ ! (ε ,ℓ ℓ)} {r : R}
    → vabs (thenE sub (retApplied h v) (weaken1V g)) ⊢ e -[ r ]→ e' → (ρ : Env Γ) (γ : ⟦ σ' ⟧ → Ŵ ε ⊤)
    → Esem (handleE h (val v) e) ρ γ ≡ tell r (Esem (handleE h (val v) e') ρ γ)
theorem-B9-S1-gen {ε = ε} {ℓ = ℓ} {par = par} {σ = σ} {σ' = σ'} sub {g} h v {e} {e'} {r} stp ρ γ =
  trans step1 (trans step3 step5)
  where
  p : ⟦ gnd par ⟧
  p = Vsem v ρ
  ih : Esem e ρ (λ _ → η̂ tt) ≡ tell r (Esem e' ρ (λ _ → η̂ tt))
  ih = theorem-B9-gen stp ρ (λ _ → η̂ tt)
  step1 : Esem (handleE h (val v) e) ρ γ ≡ ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (Esem e ρ (λ _ → η̂ tt)) p
  step1 = cong (λ F → F γ) (bindˢ-unitˡ (λ p' → handlerSem h ρ p' (Esem e ρ)) p)
  step3 : ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (Esem e ρ (λ _ → η̂ tt)) p
        ≡ tell r (ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (Esem e' ρ (λ _ → η̂ tt)) p)
  step3 = trans (cong (λ w → ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) w p) ih)
                (handlerAlg-tell-comm h ρ γ (handlerRet h ρ γ) r (Esem e' ρ (λ _ → η̂ tt)) p)
  step5 : tell r (ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (Esem e' ρ (λ _ → η̂ tt)) p) ≡ tell r (Esem (handleE h (val v) e') ρ γ)
  step5 = cong (tell r) (sym (cong (λ F → F γ) (bindˢ-unitˡ (λ p' → handlerSem h ρ p' (Esem e' ρ)) p)))

-- Generalised (R5): ORIGINALLY FOUND FALSE AS STATED (not just
-- unproven), via a genuine, machine-checked counterexample --
-- B5Core.agda's r5-lhs-old/r5-lhs-new block. EffCxt is explicitly a
-- MULTISET (Domains.agda's own comment on `_,ℓ_`: "extend ε by one
-- further (freshly introduced, 'outermost') copy of ℓ" -- nested
-- handlers for the SAME effect label are a legitimate, intended
-- scenario). This statement's own `m : ℓ ∈ εop` is universally
-- quantified with no side-condition pinning it to the fresh/outermost
-- occurrence specifically -- and handlerΨ USED TO dispatch on the
-- WITNESS's own position (∈-++⁻ ε m: does it land in the old prefix or
-- the freshly-appended slot?), which could disagree between two
-- witnesses for the very same label, while R5's own OPERATIONAL rule
-- never inspected m's structure at all (only `¬ Handles k ℓ`, itself
-- already witness-independent) -- node ≠ leaf, confirmed concretely.
--
-- FIXED (Denotational.agda's handlerΨ now dispatches on LABEL EQUALITY,
-- ℓ1 ≟ᵉ ℓ, instead of witness position -- Sig gained a new `_≟ᵉ_` field
-- for this; renH-coh/subH-coh's own ψEq cases were re-proven against the
-- new dispatch via a shared top-level `demoteMem` helper). B5Core.agda's
-- r5-fixed-check now confirms the SAME two witnesses that used to
-- disagree (r5-lhs-old vs r5-lhs-new) produce IDENTICAL results,
-- matching R7's own resolution pattern: the operational semantics
-- (OpSem.agda) was right all along, the "hat" denotational semantics had
-- the bug. lemma-B8 was subsequently closed IN FULL (all of ▫/F∘/S-then/
-- S-glocal/S-handleB/S-reset -- no postulate remains), and fk-match (the
-- "value substitution" half of the fk/k1v-matching argument) was proven
-- unconditionally.
--
-- SECOND, DEEPER FINDING (same investigation, after lemma-B8/fk-match):
-- theorem-B9-R5-gen (γ fully arbitrary, independent of the ambient loss
-- continuation g) is ALSO false -- B5Core.agda's PLeakCheck2 (a handler
-- whose clause reports its OWN choice-continuation l1's value via
-- `lossE` before resuming via k1 -- l1 is documented, right above
-- handlerΨ's own "yes" branch, as "collect(γ†Ŵε(k(a)(p)))", DELIBERATELY
-- exposing whatever the ambient continuation would report; this is not
-- an edge case, it's the mechanism the whole selection-monad framework
-- exists for) shows handlerSem's own result genuinely depends on which
-- of two arbitrary, unrelated continuations it's run against. This is
-- NOT a defect in theorem-B9 itself, though: theorem-B9 (below) never
-- actually invokes theorem-B9-R5-gen at an arbitrary γ -- it only ever
-- uses theorem-B9-R5 (below), which is theorem-B9-R5-gen specialised to
-- γ := ⌊g⌋[sub,ρ] (the SAME "generalise, then specialise" pattern
-- theorem-B9-R7/theorem-B9-R7-gen already use, and theorem-B9-S1/
-- theorem-B9-S1-gen above). B5Core.agda's R5NonGenCheck confirmed
-- theorem-B9-R5 (γ tied to g, NOT arbitrary) survives the SAME leaking
-- clause, at two different g values (par := unit, so there is no
-- separate p-vs-p'' axis to worry about there).
--
-- THIRD FINDING (same investigation, going further): with a NONTRIVIAL
-- par, B5Core2.agda (module B5Core2, using a fresh two-label Sig --
-- Example2.agda -- since R5's own ¬ Handles k ℓ precondition forbids a
-- nested handler from sharing the outer one's label) built a k whose
-- captured continuation embeds, via S-handleB, a DIFFERENT, adversarial
-- handler h2 (the SAME "leaking" clause as PLeakCheck2), combined with an
-- OUTER handler hIll whose own clause calls k1 at a SYNTACTICALLY-
-- CONSTRUCTED CONSTANT parameter value rather than its own bound p
-- (perfectly well-typed: Loss/R values are always embeddable as
-- constants, no PrimFun needed). Against the OLD handlerSem this made
-- lhsIll/rhsIll diverge concretely (23 vs 25) -- a genuine, machine-
-- checked counterexample to theorem-B9-R5 itself, not just -gen.
--
-- RESOLVED: comparing to the paper's own operational rule (R5, read
-- directly from arXiv:2504.03890v1, Fig 6/Fig 11) and its own denotational
-- handler semantics (§5.3) showed the bug was a PORTING error, not a
-- defect in the paper -- the old handlerSem fed the handler's own body G
-- a continuation with the OUTER p baked in ahead of time (via a
-- separately-constructed "D"), rather than the canonical zero
-- continuation (λ_→η̂tt), letting ext̂'s own leaf case apply handlerRet
-- generically at whatever value is reached (exactly the paper's
-- W_ε(S[[σ']])^{S[[par]]}-carrier mechanism, resolved only at the FINAL p
-- application). With handlerSem corrected accordingly (see Denotational.
-- agda), B5Core2.agda's own r5-ill-check -- the EXACT scenario that
-- broke theorem-B9-R5 above -- now holds by refl (both sides report
-- leaf 7 tt, i.e. p''), and every other concrete instance checked this
-- session (PLeakCheck, PLeakCheck2, R5NonGenCheck) continues to hold.
-- renH-coh/subH-coh/lemma-B8-S∘-handleB/theorem-B9-S1-gen were reworked
-- for the simpler, D-free handlerSem and Proofs.agda re-verified to
-- compile clean throughout.
--
-- FOURTH FINDING (attempting the direct, postulate-free proof of
-- theorem-B9-R5): the fk/k1v half of the matching argument goes through
-- cleanly -- lemma-B8 identifies the stuck-operation shape, fk-match
-- (proven unconditionally) identifies fk's own reified continuation with
-- lemma-B8's κ, and weaken1H-coh/handlerΨ-yes-eq assemble these into
-- exactly handlerΨ's own "yes" branch, landing on
-- tell 0#(Esem(clause h op)(...)γ) on both sides via the SAME env,
-- PROVIDED Vsem fk ρ and Vsem fl ρ match k1v/l1v as FUNCTIONS (needed for
-- subE-coh/SubCoh). fk vs k1v matches (fk-match). But fl vs l1v does
-- NOT, in general: B5Core2.agda's r5-leak-check2 (hLeakIll, a clause that
-- reports fl's own value via lossE, combined with g2Ill, a g whose OWN
-- body has genuine nonzero internal accumulated loss via an internal
-- lossE) is a concrete, machine-checked counterexample -- lhsLeak2 = 25,
-- rhsLeak2 = 32 = 25 + (g2Ill's own internal loss, 7). Diagnosis: l1v
-- (handlerΨ's "yes" branch, matching the paper's own §5.3 formula
-- l1(p,a)=λγ1.δ_ε(γ†Ŵε(kap))) only ever consults the already-COLLAPSED
-- outer γ; R5's own fl:=(...)▶g (thenE-based) reification's final
-- combine step genuinely re-runs g and folds in g's RAW, uncollapsed
-- internal report. These agree when g has no internal accounting (every
-- concrete g used elsewhere this session -- gIll, the g/g3/g3b of
-- R5NonGenCheck, etc. -- happens to be a bare value, trivially so), but
-- differ whenever g's own body does not (B5Core2.agda's γB2-same-as-γB
-- confirms the discrepancy is invisible at the TOP-level ambient γ,
-- i.e. it is purely an artifact of the SUBSTITUTED fl's own internal
-- construction, not of the theorem's stated equation being tested
-- against the wrong γ). This is DISTINCT from the paper's own documented
-- erratum (paper.tex §"An Error in the Original Appendix B.4", about the
-- necessity of fk's ⟨·⟩ᵍ wrapper) -- that erratum concerns fk/k1v only,
-- already correctly handled here (fk-match), and does not address
-- fl/l1v. Whether this is a further porting bug (perhaps in Esem's own
-- thenE clause, or in R5's own fl construction, paralleling the
-- handlerSem fix) or reflects a genuine gap in the theorem as stated is
-- not yet resolved.
--
-- FIFTH FINDING (pursuing the natural fix -- restricting g rather than
-- changing the semantics): does the mismatch disappear if g is required
-- to be "well-formed" in the sense theorem-B9's own induction actually
-- maintains -- built only by repeatedly wrapping zeroLC via thenE/glocalE
-- (exactly what (F-rule)/(S1) ever do to build a "new" ambient g; no
-- other rule changes g at all), rather than an arbitrary expression?
-- RootZero (defined above, before "Lemma 7.4") captures the invariant
-- actually needed: a Ŵ-tree whose root/node-r fields are ALWAYS 0#
-- (its LEAF PAYLOAD can still be anything, so g may still report nonzero
-- loss via lossE internally). RootZero-thenE-wrap proves this invariant
-- is preserved by (F-rule)/(S1)'s own g-rebuilding, for ANY wrapped
-- expression whatsoever (even one whose own internal lossE reports are
-- nonzero) -- confirmed both by this general proof and empirically
-- (B5Core2.agda's r5-leak-checkWF, gWF built via thenE-wrapping a
-- nonzero-report lossE over zeroLC, now MATCHES).
--
-- RootZero(g) alone turned out necessary but not sufficient: it does not
-- rule out g's own semantic value getting STUCK on an unresolved
-- operation (a `node`, which RootZero permits, provided its root is 0#)
-- while the delimited continuation it's combined with has already
-- accumulated some NONZERO root loss elsewhere. RootZeroSubLemmaCheck.
-- agda is a minimal, standalone refutation of exactly this case, at the
-- raw Ŵ level: for a RootZero node D (a stuck `decide()`, root 0#) and a
-- nonzero outer bump r=7, `collect(tell r(collapse D))` (l1v read via
-- `collect`) gives root 7, while `mapŴ(r +_) D` (the fl/thenE side)
-- leaves D's own root at 0# -- collapse zeroes a node's own root
-- unconditionally, so `tell r` reintroduces r at the top, which `collect`
-- preserves as the result's own root, but `mapŴ` never touches node
-- roots at all, only the eventual leaf payload.
--
-- SIXTH FINDING, AND RESOLUTION: `collect`'s own "preserve node roots,
-- discard only at leaves" behaviour is exactly the mismatch; `collectX`
-- (unlike `collect`) REDISTRIBUTES an outer bump down to every leaf via
-- `bump`, exactly matching what `mapŴ`'s own "hold the bump in reserve
-- until a leaf" behaviour needs. RootZeroSubLemmaCheck.agda's
-- sub-lemma-checkX confirms `mapŴ π₂ (collectX (tell r (collapse D)))
-- ≡ mapŴ (r +_) D` DOES hold for the same RootZero node D that broke the
-- `collect`-based version -- proven in general as
-- RootZero-collect-via-collectX below, and lifted to the full fl/l1v
-- matching argument as lemma-fl-l1v-match (unconditional on the
-- delimited continuation's own shape, needing RootZero only of g).
-- Denotational.agda's handlerΨ (l1v) now reads δ_ε via `collectX`
-- (mapŴ π₂ ∘ collectX) instead of `collect` -- this is a THIRD genuine
-- porting-bug fix in this file (after handlerSem's D-continuation and
-- (R7)'s mapŴ fix), motivated by the exact same "collectX redistributes,
-- collect discards" principle as the (R7) fix, just uncovered later,
-- specifically for l1's own construction.
--
-- theorem-B9-R5-WF, below theorem-B9-R5, is the result: theorem-B9-R5
-- PROVEN DIRECTLY (not via theorem-B9-R5-gen, which remains genuinely
-- false and is kept postulated, unused by theorem-B9), postulate-free,
-- under the added hypothesis `∀ a → RootZero (Vsem g ρ a (λ _ → η̂ tt))`
-- -- discharged, in the real induction, by RootZero-thenE-wrap/
-- RootZero-zeroLC, since g only ever starts as zeroLC and gets rebuilt
-- via thenE-wrapping. Both matching halves close: fk-match (fk/k1v,
-- unconditional) and lemma-fl-l1v-match (fl/l1v, needing RootZero(g)).
-- theorem-B9-R5-gen's fully-arbitrary-γ status was never needed by
-- theorem-B9 (which only ever uses theorem-B9-R5 at γ:=⌊g⌋[sub,ρ]) and
-- remains separately open, kept postulated below purely for its
-- historical role in this investigation.
postulate
  theorem-B9-R5-gen : ∀ {Γ ε εamb ℓ par σ σ' εop} (sub : εamb ⊆ᵉ ε) {g : LC Γ σ' εamb}
    (h : Handler Γ ℓ par σ σ' ε) (v1 : Val Γ (gnd par)) (m : ℓ ∈ εop) (op : Op ℓ) (v2 : Val Γ (gnd (out op)))
    (k : ContCxt Γ (gnd (in′ op)) εop σ (ε ,ℓ ℓ)) (nh : ¬ Handles k ℓ) (ρ : Env Γ) (γ : ⟦ σ' ⟧ → Ŵ ε ⊤) → let
      h' = renH S h ; g' = renV S g ; k' = weaken1K k
      handled = handleE h' (fst (val (vvar Z))) (plugK k' (snd (val (vvar Z))))
      fk = vabs {σ = gnd par `× gnd (in′ op)} (glocalE sub ⊆ᵉ-refl handled g')
      fl = vabs {σ = gnd par `× gnd (in′ op)} (thenE sub handled g')
    in Esem (handleE h (val v1) (plugK k (opE m op (val v2)))) ρ γ
     ≡ tell 0# (Esem (subE (cons fk (cons fl (cons v2 (cons v1 idSub)))) (clause h op)) ρ γ)

-- (R7), generalised and PROVEN (not postulated!) now that the mapŴ fix
-- is in place: both sides turn out to be γ-CONSTANT (thenE/glocalE both
-- ignore their own λγ, only ever consulting their embedded ambient at
-- δ'=λ_→η̂tt), so the equation reduces, on both sides, to
-- tell0#(widenŴsub(Esem(e[v])ρδ')) -- matches the hand-derivation that
-- diagnosed why (R7) was false pre-fix (shift 0# ≠ id at a node) and
-- true post-fix (mapŴ (0# +_) ≡ id, no such subtlety).
theorem-B9-R7-gen : ∀ {Γ ε εg σ} (sub : εg ⊆ᵉ ε) (v : Val Γ σ) (e : (Γ , σ) ⊢ Loss ! εg) (ρ : Env Γ) (γ : ⟦ Loss ⟧ → Ŵ ε ⊤)
  → Esem (thenE sub (val v) (vabs e)) ρ γ ≡ tell 0# (Esem (glocalE ⊆ᵉ-refl sub (e [ v ]) zeroLC) ρ γ)
theorem-B9-R7-gen sub v e ρ γ = trans lhsEq (sym rhsEq)
  where
  δ' : R → Ŵ _ ⊤
  δ' = λ _ → η̂ tt

  step0 : Esem (thenE sub (val v) (vabs e)) ρ γ ≡ tell 0# (mapŴ (0# +_) (widenŴ sub (Esem e (ρ ,, Vsem v ρ) δ')))
  step0 = refl

  step1 : tell 0# (mapŴ (0# +_) (widenŴ sub (Esem e (ρ ,, Vsem v ρ) δ'))) ≡ tell 0# (widenŴ sub (Esem e (ρ ,, Vsem v ρ) δ'))
  step1 = cong (tell 0#) (mapŴ-plus-0 (widenŴ sub (Esem e (ρ ,, Vsem v ρ) δ')))

  step2 : tell 0# (widenŴ sub (Esem e (ρ ,, Vsem v ρ) δ')) ≡ tell 0# (widenŴ sub (Esem (e [ v ]) ρ δ'))
  step2 = cong (λ w → tell 0# (widenŴ sub w)) (sym (cong (λ F → F δ') (sub1-coh e ρ v)))

  lhsEq : Esem (thenE sub (val v) (vabs e)) ρ γ ≡ tell 0# (widenŴ sub (Esem (e [ v ]) ρ δ'))
  lhsEq = trans step0 (trans step1 step2)

  γ0-eq : (λ (a : R) → widenŴ ⊆ᵉ-refl (Lsem (zeroLC {σ = Loss}) ρ a)) ≡ δ'
  γ0-eq = funext (λ a → widenŴ-refl (η̂ tt))

  rhsEq : tell 0# (Esem (glocalE ⊆ᵉ-refl sub (e [ v ]) zeroLC) ρ γ) ≡ tell 0# (widenŴ sub (Esem (e [ v ]) ρ δ'))
  rhsEq = cong (λ F → tell 0# (widenŴ sub (Esem (e [ v ]) ρ F))) γ0-eq

-- Generalised (S2)/(S3)/(S4): direct copies of theorem-B9-S2/S3/S4's own
-- proofs (below) with the outer continuation freed from ⌊g⌋[subamb,ρ] to
-- an arbitrary γ, and the recursive IH re-targeted at theorem-B9-gen.
theorem-B9-S2-gen : ∀ {Γ ε εg} (sub : εg ⊆ᵉ ε) (g1 : LC Γ Loss εg) {e e' : Γ ⊢ Loss ! ε} {r : R}
  → g1 ⊢ e -[ r ]→ e' → (ρ : Env Γ) (γ : ⟦ Loss ⟧ → Ŵ ε ⊤)
  → Esem (thenE sub e g1) ρ γ
  ≡ tell 0# (Esem (thenE ⊆ᵉ-refl (lossE (val (vgnd r))) (vabs (weaken1 (thenE sub e' g1)))) ρ γ)
theorem-B9-S2-gen sub g1 {e} {e'} {r} stp ρ γ = trans step1 (sym (tell-0 _))
  where
  Gg1 : ⟦ Loss ⟧ → Ŵ _ ⊤
  Gg1 = ⌊ g1 ⌋[ sub , ρ ]

  h : ⟦ Loss ⟧ → R → Ŵ _ R
  h a r1 = mapŴ (r1 +_) (widenŴ sub (Vsem g1 ρ a (λ _ → η̂ tt)))

  ih : Esem e ρ Gg1 ≡ tell r (Esem e' ρ Gg1)
  ih = theorem-B9-gen stp ρ Gg1

  hShift : ∀ a r1 → h a (r + r1) ≡ mapŴ (r +_) (h a r1)
  hShift a r1 = trans (cong (λ f → mapŴ f (widenŴ sub (Vsem g1 ρ a (λ _ → η̂ tt)))) (funext (+-assoc r r1)))
                       (sym (mapŴ-∘ (r +_) (r1 +_) (widenŴ sub (Vsem g1 ρ a (λ _ → η̂ tt)))))

  lhsStep : Esem (thenE sub e g1) ρ γ
          ≡ mapŴ (r +_) (bind̂ (collectX (Esem e' ρ Gg1)) (λ { (a , r1) → h a r1 }))
  lhsStep = trans (cong (λ w → bind̂ (collectX w) (λ { (a , r1) → h a r1 })) ih)
                  (trans (cong (λ w → bind̂ w (λ { (a , r1) → h a r1 })) (sym (bump-collectX-comm r (Esem e' ρ Gg1))))
                         (trans (bump-shift r (collectX (Esem e' ρ Gg1)) h)
                                (trans (cong (bind̂ (collectX (Esem e' ρ Gg1))) (funext (λ { (a , r1) → hShift a r1 })))
                                       (bind̂-mapŴ-after (collectX (Esem e' ρ Gg1)) (λ { (a , r1) → h a r1 }) (r +_)))))

  T : Ŵ _ ⟦ Loss ⟧
  T = bind̂ (collectX (Esem e' ρ Gg1)) (λ { (a , r1) → h a r1 })

  H'tt-eq : widenŴ ⊆ᵉ-refl (Esem (weaken1 (thenE sub e' g1)) (ρ ,, tt) (λ _ → η̂ tt)) ≡ T
  H'tt-eq = trans (cong (λ F → widenŴ ⊆ᵉ-refl (F (λ _ → η̂ tt))) (weaken1-coh UnitTy (thenE sub e' g1) ρ tt)) (widenŴ-refl T)

  rhsStep : Esem (thenE ⊆ᵉ-refl (lossE (val (vgnd r))) (vabs (weaken1 (thenE sub e' g1)))) ρ γ
          ≡ mapŴ (r +_) T
  rhsStep =
    trans (cong (λ z → tell 0# (mapŴ (z +_) (widenŴ ⊆ᵉ-refl (Esem (weaken1 (thenE sub e' g1)) (ρ ,, tt) (λ _ → η̂ tt)))))
                (trans (cong (0# +_) (+-identityʳ r)) (+-identityˡ r)))
          (trans (cong (λ w → tell 0# (mapŴ (r +_) w)) H'tt-eq)
                 (tell-0 _))

  step1 : Esem (thenE sub e g1) ρ γ
        ≡ Esem (thenE ⊆ᵉ-refl (lossE (val (vgnd r))) (vabs (weaken1 (thenE sub e' g1)))) ρ γ
  step1 = trans lhsStep (sym rhsStep)

theorem-B9-S3-gen : ∀ {Γ ε ε₂ ε₁ σ} (sub1 : ε₂ ⊆ᵉ ε₁) (sub2 : ε₁ ⊆ᵉ ε) (g1 : LC Γ σ ε₂)
    {e e' : Γ ⊢ σ ! ε₁} {r : R}
  → g1 ⊢ e -[ r ]→ e' → (ρ : Env Γ) (γ : ⟦ σ ⟧ → Ŵ ε ⊤)
  → Esem (glocalE sub1 sub2 e g1) ρ γ ≡ tell r (Esem (glocalE sub1 sub2 e' g1) ρ γ)
theorem-B9-S3-gen sub1 sub2 g1 stp ρ γ =
  trans (cong (widenŴ sub2) (theorem-B9-gen stp ρ ⌊ g1 ⌋[ sub1 , ρ ])) (widenŴ-tell-comm sub2 _ _)

theorem-B9-S4-gen : ∀ {Γ ε εg σ} {g : LC Γ σ εg} {e e' : Γ ⊢ σ ! ε} {r : R}
  → g ⊢ e -[ r ]→ e' → (ρ : Env Γ) (γ : ⟦ σ ⟧ → Ŵ ε ⊤)
  → Esem (resetE e) ρ γ ≡ tell 0# (Esem (resetE e') ρ γ)
theorem-B9-S4-gen stp ρ γ =
  trans (cong censor (theorem-B9-gen stp ρ γ)) (trans (censor-tell-absorb _ _) (sym (tell-0 _)))

-- theorem-B9-F-gen's own proof: UNIFORM across every regular frame (no
-- case-split on f at all) -- lemma-B6 (already unconditional for every
-- constructor of Frame) turns Esem(plugFfe)ρ into bind̂ˢH(Esemeρ) for a
-- FIXED H (independent of e/e'/stp); apply the (arbitrary-γ) IH directly
-- at D:=λa→R̂-of(Ha)γ -- the continuation e's own evaluation is ALREADY
-- forced to receive by bind̂ˢ's definition -- then push tell r out with
-- tell-bind̂-comm. No mini-B7, no collapse/mapŴ reasoning needed at all.
theorem-B9-F-gen {σ = σ} {ε = ε} {α = α} sub {g} f {e} {e'} {r} stp ρ γ = trans step1 (trans step2 step3)
  where
  H : ⟦ α ⟧ → Ŝ ε ⟦ σ ⟧
  H a = Esem (plugF (weaken1F f) (val (vvar Z))) (ρ ,, a)
  b6 : Esem (plugF f e) ρ ≡ bind̂ˢ H (Esem e ρ)
  b6 = lemma-B6 f e ρ
  b6' : Esem (plugF f e') ρ ≡ bind̂ˢ H (Esem e' ρ)
  b6' = lemma-B6 f e' ρ
  D : ⟦ α ⟧ → Ŵ ε ⊤
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
theorem-B9-gen (R2-fst {σ = σ} {τ = τ} v w) ρ γ =
  trans (cong (λ F → F γ) fstEqS) (sym (tell-0 (leaf 0# (Vsem v ρ))))
  where
  pairEq : Esem (pair (val v) (val w)) ρ ≡ η̂ˢ (Vsem v ρ , Vsem w ρ)
  pairEq = trans (bindˢ-unitˡ (λ a → bind̂ˢ (λ b → η̂ˢ (a , b)) (η̂ˢ (Vsem w ρ))) (Vsem v ρ))
                 (bindˢ-unitˡ (λ b → η̂ˢ (Vsem v ρ , b)) (Vsem w ρ))
  fstEqS : Esem (fst (pair (val v) (val w))) ρ ≡ η̂ˢ (Vsem v ρ)
  fstEqS = trans (cong (bind̂ˢ (λ{ (a , b) → η̂ˢ a })) pairEq)
                 (bindˢ-unitˡ {X = ⟦ σ ⟧ × ⟦ τ ⟧} (λ{ (a , b) → η̂ˢ a }) (Vsem v ρ , Vsem w ρ))
theorem-B9-gen (R2-snd {σ = σ} {τ = τ} v w) ρ γ =
  trans (cong (λ F → F γ) sndEqS) (sym (tell-0 (leaf 0# (Vsem w ρ))))
  where
  pairEq : Esem (pair (val v) (val w)) ρ ≡ η̂ˢ (Vsem v ρ , Vsem w ρ)
  pairEq = trans (bindˢ-unitˡ (λ a → bind̂ˢ (λ b → η̂ˢ (a , b)) (η̂ˢ (Vsem w ρ))) (Vsem v ρ))
                 (bindˢ-unitˡ (λ b → η̂ˢ (Vsem v ρ , b)) (Vsem w ρ))
  sndEqS : Esem (snd (pair (val v) (val w))) ρ ≡ η̂ˢ (Vsem w ρ)
  sndEqS = trans (cong (bind̂ˢ (λ{ (a , b) → η̂ˢ b })) pairEq)
                 (bindˢ-unitˡ {X = ⟦ σ ⟧ × ⟦ τ ⟧} (λ{ (a , b) → η̂ˢ b }) (Vsem v ρ , Vsem w ρ))
theorem-B9-gen (R3 e v) ρ γ = trans step1 (trans step2 (sym (tell-0 (Esem (e [ v ]) ρ γ))))
  where
  step1 : Esem (app (val (vabs e)) (val v)) ρ γ ≡ Esem e (ρ ,, Vsem v ρ) γ
  step1 = trans (cong (λ F → F γ) (bindˢ-unitˡ (λ φ → bind̂ˢ (λ a → φ a) (η̂ˢ (Vsem v ρ))) (Vsem (vabs e) ρ)))
                (cong (λ F → F γ) (bindˢ-unitˡ (λ a → Vsem (vabs e) ρ a) (Vsem v ρ)))
  step2 : Esem e (ρ ,, Vsem v ρ) γ ≡ Esem (e [ v ]) ρ γ
  step2 = sym (cong (λ F → F γ) (sub1-coh e ρ v))
theorem-B9-gen (R4 r) ρ γ = tell-0 (tell r (η̂ tt))
theorem-B9-gen (R6 h v1 v2) ρ γ = trans step1 (sym (tell-0 (Esem (subE (cons v2 (cons v1 idSub)) (ret h)) ρ γ)))
  where
  step1 : Esem (handleE h (val v1) (val v2)) ρ γ ≡ Esem (subE (cons v2 (cons v1 idSub)) (ret h)) ρ γ
  step1 = trans (cong (λ F → F γ) (bindˢ-unitˡ (λ p → handlerSem h ρ p (η̂ˢ (Vsem v2 ρ))) (Vsem v1 ρ)))
                subst2-step
    where
    subst2-step : tell 0# (Esem (ret h) ((ρ ,, Vsem v1 ρ) ,, Vsem v2 ρ) γ) ≡ Esem (subE (cons v2 (cons v1 idSub)) (ret h)) ρ γ
    subst2-step = trans (tell-0 _) (sym (cong (λ F → F γ)
      (subE-coh (cons v2 (cons v1 idSub)) ρ ((ρ ,, Vsem v1 ρ) ,, Vsem v2 ρ) subcoh (ret h))))
      where
      subcoh : SubCoh (cons v2 (cons v1 idSub)) ρ ((ρ ,, Vsem v1 ρ) ,, Vsem v2 ρ)
      subcoh Z         = refl
      subcoh (S Z)     = refl
      subcoh (S (S x)) = refl
theorem-B9-gen (R9 v) ρ γ = sym (tell-0 (leaf 0# (Vsem v ρ)))
theorem-B9-gen (R8 sub1 sub2 v g1) ρ γ = sym (tell-0 (leaf 0# (Vsem v ρ)))
theorem-B9-gen (R7 sub' v e) ρ γ = theorem-B9-R7-gen sub' v e ρ γ
theorem-B9-gen (F-rule sub' f stp) ρ γ = theorem-B9-F-gen sub' f stp ρ γ
theorem-B9-gen (S1 sub' h v stp) ρ γ = theorem-B9-S1-gen sub' h v stp ρ γ
theorem-B9-gen (S2 sub' g1 stp) ρ γ = theorem-B9-S2-gen sub' g1 stp ρ γ
theorem-B9-gen (S3 sub1 sub2 g1 stp) ρ γ = theorem-B9-S3-gen sub1 sub2 g1 stp ρ γ
theorem-B9-gen (S4 stp) ρ γ = theorem-B9-S4-gen stp ρ γ
theorem-B9-gen (R5 sub' h v1 m op v2 k nh) ρ γ = theorem-B9-R5-gen sub' h v1 m op v2 k nh ρ γ

-- theorem-B9-F-companion, DISCHARGED (no longer a postulate): a direct
-- corollary of theorem-B9-F-gen, instantiated at γ:=⌊g⌋[sub,ρ]. This
-- covers ALL of F-pairL/F-pairR/F-appL/F-appR/F-loss/F-handleP uniformly
-- (F-loss inherits its dependence on postulate-Ŝ-tell-naturality via
-- lemma-B6's own F-loss case; F-handleP is fully unconditional; the
-- other four are now fully unconditional too) -- contingent only on the
-- still-open theorem-B9-S1-gen/theorem-B9-R5-gen postulates above.
theorem-B9-F-companion : ∀ {Γ σ ε εg α} (sub : εg ⊆ᵉ ε) {g : LC Γ σ εg} (f : Frame Γ α ε σ ε) {e e' : Γ ⊢ α ! ε} {r : R}
    → vabs (thenE sub (plugF (weaken1F f) (val (vvar Z))) (weaken1V g)) ⊢ e -[ r ]→ e' → (ρ : Env Γ)
    → Esem (plugF f e) ρ ⌊ g ⌋[ sub , ρ ] ≡ tell r (Esem (plugF f e') ρ ⌊ g ⌋[ sub , ρ ])
theorem-B9-F-companion sub {g} f stp ρ = theorem-B9-F-gen sub f stp ρ ⌊ g ⌋[ sub , ρ ]

-- F-op: plugF(weaken1F(F-op m op))(val(vvar Z)) = opE m op(val(vvar Z))
-- reduces to a *node* (φ̂ˢ m op x η̂ˢ), not a value transport -- the same
-- collapse-tell/collapse-shift-0/collapse-widenŴ-comm toolkit closes it,
-- by the same argument (no companion subexpression to contribute a
-- nonzero r1).
miniB7-op : ∀ {Γ ε εg ℓ} (sub : εg ⊆ᵉ ε) {op : Op ℓ} (m : ℓ ∈ ε) (g : LC Γ (gnd (in′ op)) εg) (ρ : Env Γ) (x : ⟦ gnd (out op) ⟧)
          → Lsem (vabs (thenE sub (opE m op (val (vvar Z))) (weaken1V g))) ρ x ≡ R̂-of (φ̂ˢ m op x (η̂ˢ {X = ⟦ gnd (in′ op) ⟧})) ⌊ g ⌋[ sub , ρ ]
miniB7-op {Γ = Γ} {ε = ε} {εg = εg} sub {op} m g ρ x = trans step2 step5
  where
  η̂ˢ' : ⟦ gnd (in′ op) ⟧ → Ŝ _ ⟦ gnd (in′ op) ⟧
  η̂ˢ' = η̂ˢ {X = ⟦ gnd (in′ op) ⟧}
  δ' : R → Ŵ _ ⊤
  δ' = λ _ → η̂ tt
  gw : Val (Γ , gnd (out op)) ((gnd (in′ op)) ⇒ Loss ! εg)
  gw = weaken1V {τ = gnd (out op)} g

  γ1 : ⟦ gnd (in′ op) ⟧ → Ŵ _ ⊤
  γ1 = λ c → widenŴ sub (Lsem gw (ρ ,, x) c)

  bodyEq : Esem (opE m op (val (vvar Z))) (ρ ,, x) ≡ φ̂ˢ m op x η̂ˢ'
  bodyEq = bindˢ-unitˡ (λ a → φ̂ˢ m op a η̂ˢ') x

  step2 : Lsem (vabs (thenE sub (opE m op (val (vvar Z))) gw)) ρ x
        ≡ collapse (bind̂ (collectX (φ̂ˢ m op x η̂ˢ' γ1))
                         (λ { (c , r1) → mapŴ (r1 +_) (widenŴ sub (Vsem gw (ρ ,, x) c δ')) }))
  step2 = cong (λ (F : Ŝ ε ⟦ gnd (in′ op) ⟧) → collapse (bind̂ (collectX (F γ1))
                                     (λ { (c , r1) → mapŴ (r1 +_) (widenŴ sub (Vsem gw (ρ ,, x) c δ')) })))
              bodyEq

  step5 = trans (cong (node m op 0# x) (funext (λ a → trans (inner a) (sym (tell-0 _))))) (sym (tell-0 _))
    where
    inner : (a : ⟦ in′ op ⟧ᴳ)
          → collapse (bind̂ (bump 0# (collectX (η̂ a)))
                           (λ { (c , r1) → mapŴ (r1 +_) (widenŴ sub (Vsem gw (ρ ,, x) c δ')) }))
          ≡ widenŴ sub (Lsem g ρ a)
    inner a =
      trans (collapse-tell 0# _)
            (trans (cong (λ v → collapse (mapŴ ((0# + 0#) +_) (widenŴ sub (v a δ'))))
                         (weaken1V-coh (gnd (out op)) g ρ x))
                   (trans (cong (λ z → collapse (mapŴ (z +_) (widenŴ sub (Vsem g ρ a δ'))))
                                (+-identityˡ 0#))
                          (trans (cong collapse (mapŴ-plus-0 (widenŴ sub (Vsem g ρ a δ'))))
                                 (collapse-widenŴ-comm sub (Vsem g ρ a δ')))))

-- Discharges theorem-B9-F for any frame whose plugF(weaken1F f)(val
-- (vvar Z)) is a bare value-transport η̂ˢ(φ x) (F-fun, F-fst, F-snd):
-- combine Lemma B.6 (unconditional) with miniB7-value (the companion-free
-- case of Lemma B.7, likewise unconditional) and the recursive
-- theorem-B9 call (the given step's own IH) via tell-bind̂-comm.
theorem-B9-F-value-transport : ∀ {Γ σ ε εg α} (sub : εg ⊆ᵉ ε) {g : LC Γ σ εg} (f : Frame Γ α ε σ ε) (φ : ⟦ α ⟧ → ⟦ σ ⟧)
  → (∀ (ρ : Env Γ) (a : ⟦ α ⟧) → Esem (plugF (weaken1F f) (val (vvar Z))) (ρ ,, a) ≡ η̂ˢ (φ a))
  → {e e' : Γ ⊢ α ! ε} {r : R}
  → vabs (thenE sub (plugF (weaken1F f) (val (vvar Z))) (weaken1V g)) ⊢ e -[ r ]→ e' → (ρ : Env Γ)
  → Esem (plugF f e) ρ ⌊ g ⌋[ sub , ρ ] ≡ tell r (Esem (plugF f e') ρ ⌊ g ⌋[ sub , ρ ])
theorem-B9-F-value-transport {σ = σ} sub {g} f φ bodyEq {e} {e'} {r} stp ρ = trans step1 (trans step2 step3)
  where
  gStar = vabs (thenE sub (plugF (weaken1F f) (val (vvar Z))) (weaken1V g))
  γ = ⌊ g ⌋[ sub , ρ ]
  δ = Lsem gStar ρ
  mb7 : ∀ a → δ a ≡ R̂-of (η̂ˢ (φ a)) γ
  mb7 = miniB7-value sub g ρ φ (plugF (weaken1F f) (val (vvar Z))) (bodyEq ρ)
  ih : Esem e ρ δ ≡ tell r (Esem e' ρ δ)
  ih = trans (cong (Esem e ρ) (funext (λ a → sym (widenŴ-refl (Lsem gStar ρ a)))))
             (trans (theorem-B9 ⊆ᵉ-refl stp ρ)
                    (cong (λ F → tell r (Esem e' ρ F)) (funext (λ a → widenŴ-refl (Lsem gStar ρ a)))))
  b6 : Esem (plugF f e) ρ ≡ bind̂ˢ (λ a → η̂ˢ (φ a)) (Esem e ρ)
  b6 = trans (lemma-B6 f e ρ) (cong (λ F → bind̂ˢ F (Esem e ρ)) (funext (bodyEq ρ)))
  b6' : Esem (plugF f e') ρ ≡ bind̂ˢ (λ a → η̂ˢ (φ a)) (Esem e' ρ)
  b6' = trans (lemma-B6 f e' ρ) (cong (λ F → bind̂ˢ F (Esem e' ρ)) (funext (bodyEq ρ)))
  step1 : Esem (plugF f e) ρ γ ≡ bind̂ (Esem e ρ δ) (λ a → η̂ˢ (φ a) γ)
  step1 = trans (cong (λ F → F γ) b6) (cong (λ F → bind̂ (Esem e ρ F) (λ a → η̂ˢ (φ a) γ)) (sym (funext mb7)))
  step2 : bind̂ (Esem e ρ δ) (λ a → η̂ˢ (φ a) γ) ≡ tell r (bind̂ (Esem e' ρ δ) (λ a → η̂ˢ (φ a) γ))
  step2 = trans (cong (λ w → bind̂ w (λ a → η̂ˢ (φ a) γ)) ih) (tell-bind̂-comm r (Esem e' ρ δ) (λ a → η̂ˢ (φ a) γ))
  step3 : tell r (bind̂ (Esem e' ρ δ) (λ a → η̂ˢ (φ a) γ)) ≡ tell r (Esem (plugF f e') ρ γ)
  step3 = cong (tell r) (trans (cong (λ F → bind̂ (Esem e' ρ F) (λ a → η̂ˢ (φ a) γ)) (funext mb7))
                               (sym (cong (λ F → F γ) b6')))

-- Discharges theorem-B9-F for F-op via miniB7-op, mirroring
-- theorem-B9-F-value-transport's structure exactly (Lemma B.6 +
-- miniB7-op + the recursive IH via tell-bind̂-comm) with the
-- value-transport continuation η̂ˢ(φ x) replaced by the node-constructing
-- one φ̂ˢ m op x η̂ˢ.
theorem-B9-F-op : ∀ {Γ ε εg ℓ} (sub : εg ⊆ᵉ ε) {op : Op ℓ} (m : ℓ ∈ ε) {g : LC Γ (gnd (in′ op)) εg}
  {e e' : Γ ⊢ gnd (out op) ! ε} {r : R}
  → vabs (thenE sub (opE m op (val (vvar Z))) (weaken1V g)) ⊢ e -[ r ]→ e' → (ρ : Env Γ)
  → Esem (opE m op e) ρ ⌊ g ⌋[ sub , ρ ] ≡ tell r (Esem (opE m op e') ρ ⌊ g ⌋[ sub , ρ ])
theorem-B9-F-op sub {op} m {g} {e} {e'} {r} stp ρ = trans step1 (trans step2 step3)
  where
  η̂ˢ' : ⟦ gnd (in′ op) ⟧ → Ŝ _ ⟦ gnd (in′ op) ⟧
  η̂ˢ' = η̂ˢ {X = ⟦ gnd (in′ op) ⟧}
  K : ⟦ gnd (out op) ⟧ → Ŝ _ ⟦ gnd (in′ op) ⟧
  K a = φ̂ˢ m op a η̂ˢ'
  bodyEq : ∀ (ρ' : Env _) (a : ⟦ gnd (out op) ⟧) → Esem (opE m op (val (vvar Z))) (ρ' ,, a) ≡ K a
  bodyEq ρ' a = bindˢ-unitˡ (λ a' → φ̂ˢ m op a' η̂ˢ') a
  gStar = vabs (thenE sub (opE m op (val (vvar Z))) (weaken1V g))
  γ = ⌊ g ⌋[ sub , ρ ]
  δ = Lsem gStar ρ
  mb7 : ∀ a → δ a ≡ R̂-of (K a) γ
  mb7 = miniB7-op sub m g ρ
  ih : Esem e ρ δ ≡ tell r (Esem e' ρ δ)
  ih = trans (cong (Esem e ρ) (funext (λ a → sym (widenŴ-refl (Lsem gStar ρ a)))))
             (trans (theorem-B9 ⊆ᵉ-refl stp ρ)
                    (cong (λ F → tell r (Esem e' ρ F)) (funext (λ a → widenŴ-refl (Lsem gStar ρ a)))))
  b6 : Esem (opE m op e) ρ ≡ bind̂ˢ K (Esem e ρ)
  b6 = trans (lemma-B6 (F-op m op) e ρ) (cong (λ F → bind̂ˢ F (Esem e ρ)) (funext (bodyEq ρ)))
  b6' : Esem (opE m op e') ρ ≡ bind̂ˢ K (Esem e' ρ)
  b6' = trans (lemma-B6 (F-op m op) e' ρ) (cong (λ F → bind̂ˢ F (Esem e' ρ)) (funext (bodyEq ρ)))
  step1 : Esem (opE m op e) ρ γ ≡ bind̂ (Esem e ρ δ) (λ a → K a γ)
  step1 = trans (cong (λ F → F γ) b6) (cong (λ F → bind̂ (Esem e ρ F) (λ a → K a γ)) (sym (funext mb7)))
  step2 : bind̂ (Esem e ρ δ) (λ a → K a γ) ≡ tell r (bind̂ (Esem e' ρ δ) (λ a → K a γ))
  step2 = trans (cong (λ w → bind̂ w (λ a → K a γ)) ih) (tell-bind̂-comm r (Esem e' ρ δ) (λ a → K a γ))
  step3 : tell r (bind̂ (Esem e' ρ δ) (λ a → K a γ)) ≡ tell r (Esem (opE m op e') ρ γ)
  step3 = cong (tell r) (trans (cong (λ F → bind̂ (Esem e' ρ F) (λ a → K a γ)) (funext mb7))
                               (sym (cong (λ F → F γ) b6')))

-- theorem-B9-F's own body: proven outright for the value-transport
-- frames (F-fun, F-fst, F-snd) and for F-op; the remaining shapes
-- (companion-bearing F-pairL/F-pairR/F-appL/F-appR, F-loss, F-handleP)
-- delegate to theorem-B9-F-companion, still postulated (see the comment
-- above it).
theorem-B9-F sub {g} (F-fun pf) {e} {e'} {r} stp ρ =
  theorem-B9-F-value-transport sub (F-fun pf) (λ b → ⟦ pf ⟧f b) (λ ρ' a → bindˢ-unitˡ (λ b → η̂ˢ (⟦ pf ⟧f b)) a) stp ρ
theorem-B9-F sub {g} F-fst {e} {e'} {r} stp ρ =
  theorem-B9-F-value-transport sub F-fst proj₁ (λ ρ' ab → bindˢ-unitˡ (λ { (a , b) → η̂ˢ a }) ab) stp ρ
theorem-B9-F sub {g} F-snd {e} {e'} {r} stp ρ =
  theorem-B9-F-value-transport sub F-snd proj₂ (λ ρ' ab → bindˢ-unitˡ (λ { (a , b) → η̂ˢ b }) ab) stp ρ
theorem-B9-F sub {g} (F-pairL e₂) stp ρ = theorem-B9-F-companion sub (F-pairL e₂) stp ρ
theorem-B9-F sub {g} (F-pairR v) stp ρ  = theorem-B9-F-companion sub (F-pairR v) stp ρ
theorem-B9-F sub {g} (F-appL e₂) stp ρ  = theorem-B9-F-companion sub (F-appL e₂) stp ρ
theorem-B9-F sub {g} (F-appR v) stp ρ   = theorem-B9-F-companion sub (F-appR v) stp ρ
theorem-B9-F sub {g} (F-op m op) {e} {e'} {r} stp ρ = theorem-B9-F-op sub m stp ρ
theorem-B9-F sub {g} F-loss stp ρ       = theorem-B9-F-companion sub F-loss stp ρ
theorem-B9-F sub {g} (F-handleP h b) stp ρ = theorem-B9-F-companion sub (F-handleP h b) stp ρ

-- Lemma B.9's THEN congruence (S2): unlike (F)/(S1)/(R5)/(R7) below, this
-- does NOT go through Lsem/collapse at all -- its given step is at
-- thenE's own g1, the SAME ambient the reconstructed reduct's own thenE
-- also uses, so no compound continuation is involved, only collectX/bind̂
-- bookkeeping (which, unlike collapse, never discards information). The
-- earlier direct-induction attempt at proving `shift(r+s) ≡ shift r ∘
-- shift s` got stuck because shift (built from collectX) redistributes a
-- node's own accumulated loss down into its leaves, so "match the root,
-- cong on children" doesn't apply the way it did for bump-shift; routing
-- through collectX-bind̂-fusion/collectX-idem instead (shift-fusion,
-- shift-thenE-comm above) sidesteps that by never re-examining a tree's
-- own node structure directly.
theorem-B9-S2 : ∀ {Γ ε εg εamb} (sub : εg ⊆ᵉ ε) {g : LC Γ Loss εamb} (subamb : εamb ⊆ᵉ ε) (g1 : LC Γ Loss εg) {e e' : Γ ⊢ Loss ! ε} {r : R}
  → g1 ⊢ e -[ r ]→ e' → (ρ : Env Γ)
  → Esem (thenE sub e g1) ρ ⌊ g ⌋[ subamb , ρ ]
  ≡ tell 0# (Esem (thenE ⊆ᵉ-refl (lossE (val (vgnd r))) (vabs (weaken1 (thenE sub e' g1)))) ρ ⌊ g ⌋[ subamb , ρ ])
theorem-B9-S2 sub {g = g} subamb g1 {e} {e'} {r} stp ρ = trans step1 (sym (tell-0 _))
  where
  Gg1 : ⟦ Loss ⟧ → Ŵ _ ⊤
  Gg1 = ⌊ g1 ⌋[ sub , ρ ]

  -- EXPERIMENTAL VARIANT: h is now a plain mapŴ bump (no inner
  -- collectX/tell cycle at all), matching Denotational.agda's own
  -- reworked Esem(thenE) clause.
  h : ⟦ Loss ⟧ → R → Ŵ _ R
  h a r1 = mapŴ (r1 +_) (widenŴ sub (Vsem g1 ρ a (λ _ → η̂ tt)))

  ih : Esem e ρ Gg1 ≡ tell r (Esem e' ρ Gg1)
  ih = theorem-B9 sub stp ρ

  hShift : ∀ a r1 → h a (r + r1) ≡ mapŴ (r +_) (h a r1)
  hShift a r1 = trans (cong (λ f → mapŴ f (widenŴ sub (Vsem g1 ρ a (λ _ → η̂ tt)))) (funext (+-assoc r r1)))
                       (sym (mapŴ-∘ (r +_) (r1 +_) (widenŴ sub (Vsem g1 ρ a (λ _ → η̂ tt)))))

  lhsStep : Esem (thenE sub e g1) ρ ⌊ g ⌋[ subamb , ρ ]
          ≡ mapŴ (r +_) (bind̂ (collectX (Esem e' ρ Gg1)) (λ { (a , r1) → h a r1 }))
  lhsStep = trans (cong (λ w → bind̂ (collectX w) (λ { (a , r1) → h a r1 })) ih)
                  (trans (cong (λ w → bind̂ w (λ { (a , r1) → h a r1 })) (sym (bump-collectX-comm r (Esem e' ρ Gg1))))
                         (trans (bump-shift r (collectX (Esem e' ρ Gg1)) h)
                                (trans (cong (bind̂ (collectX (Esem e' ρ Gg1))) (funext (λ { (a , r1) → hShift a r1 })))
                                       (bind̂-mapŴ-after (collectX (Esem e' ρ Gg1)) (λ { (a , r1) → h a r1 }) (r +_)))))

  T : Ŵ _ ⟦ Loss ⟧
  T = bind̂ (collectX (Esem e' ρ Gg1)) (λ { (a , r1) → h a r1 })

  H'tt-eq : widenŴ ⊆ᵉ-refl (Esem (weaken1 (thenE sub e' g1)) (ρ ,, tt) (λ _ → η̂ tt)) ≡ T
  H'tt-eq = trans (cong (λ F → widenŴ ⊆ᵉ-refl (F (λ _ → η̂ tt))) (weaken1-coh UnitTy (thenE sub e' g1) ρ tt)) (widenŴ-refl T)

  rhsStep : Esem (thenE ⊆ᵉ-refl (lossE (val (vgnd r))) (vabs (weaken1 (thenE sub e' g1)))) ρ ⌊ g ⌋[ subamb , ρ ]
          ≡ mapŴ (r +_) T
  rhsStep =
    trans (cong (λ z → tell 0# (mapŴ (z +_) (widenŴ ⊆ᵉ-refl (Esem (weaken1 (thenE sub e' g1)) (ρ ,, tt) (λ _ → η̂ tt)))))
                (trans (cong (0# +_) (+-identityʳ r)) (+-identityˡ r)))
          (trans (cong (λ w → tell 0# (mapŴ (r +_) w)) H'tt-eq)
                 (tell-0 _))

  step1 : Esem (thenE sub e g1) ρ ⌊ g ⌋[ subamb , ρ ]
        ≡ Esem (thenE ⊆ᵉ-refl (lossE (val (vgnd r))) (vabs (weaken1 (thenE sub e' g1)))) ρ ⌊ g ⌋[ subamb , ρ ]
  step1 = trans lhsStep (sym rhsStep)

-- (F), (S1), (R5), (R7): the remaining frame/context-manipulating cases.
-- Unlike (S2)/(S3)/(S4) above, each of these has its *given* step stated
-- under a captured continuation vabs(thenE sub ...) that is a NEW, more
-- complex continuation than the ambient g theorem-B9 itself is stated
-- for -- relating the two needs the ⌊g⌋-to-Lsem-of-a-compound-
-- continuation move that is exactly Lemma B.7's content, which (S2)'s
-- collectX-only route sidesteps entirely.
--
-- (F) is *almost* Lemma B.7 directly (its captured continuation
-- vabs(thenE sub ...) is exactly the g-continuation the premise reduces
-- under) -- except Lemma B.7 (not itself formalised here, see the note
-- above lemma-B6's F-loss case) only covers g : LC Γ τ ε (the *same* ε as
-- the frame), whereas (F)'s own g genuinely lives at a smaller εg⊆ε
-- (F-rule's own `sub`). Closing this gap needs a version of B.7
-- generalised the same way Esem's own thenE/glocalE clauses are (an extra
-- widenŴ threaded through), which is new work beyond what B.7 itself
-- would establish, not a restatement of it -- and would in any case
-- inherit B.7's own dependence on the not-unconditionally-true B.5(3).
--
-- (S1), (R7) and (R5) need the analogous generalisations of Lemma
-- B.7-style reasoning for the handler/then special frames (R7
-- additionally has to push a substitution through the same threading),
-- plus (for R5) a four-fold substitution-coherence instantiation of Lemma
-- B.8 together with the fk/fl continuation identities the source proves in
-- the same breath (§8's "wrapper is essential" discussion) -- each
-- comparable in scope to what (F) alone needs. Postulated as a group; the
-- definitional content (what has to be shown) is recorded precisely in
-- each type. (R8) (like R9) instead reduces cleanly to unit-law /
-- definitional reasoning and is proved directly below, no postulate
-- needed.
--
-- Investigated further (2026-07-24, see B5Core.agda's b53F-*/b9F-* block):
-- does B.5(3)'s failure actually break (F)'s own conclusion, or only the
-- auxiliary Lemma B.7 construction one particular proof route builds on
-- top of it? Concretely instantiated B.5(3) at exactly the substitution
-- (F)'s own proof would need it at (e-role := F[x] for a frame whose
-- companion discards a real loss; g-role := the ambient, genuinely stuck
-- on an unhandled operation) -- confirmed that instance is false
-- (b53F-refuted: root 0 vs 7). But testing (F)'s own conclusion directly,
-- on a genuine F-rule step (R4, loss/() ) through the very same dirty
-- companion and stuck ambient, it HOLDS (b9F-check, by refl) -- because
-- both the stepped subterm and the companion are operation-free, so the
-- pair never reaches a stuck node and the ambient is never actually
-- consulted by either side; the B.5(3) discrepancy lives only inside the
-- intermediate Lsem(λx.F[x]▶g) construction Lemma B.7's *proof* builds,
-- not in (F)'s own directly observable equation. Every step rule cheap
-- enough to test this way (R1-R9) is exactly the class paper.tex calls
-- "never mentions Ŵ,R at all", so none of them can discriminate -- a
-- genuine test would need the *inner* step itself to be another
-- F-rule/S1/R5/R7 instance, nested, which is substantially more
-- construction and wasn't pursued. Working assumption at the time:
-- (F)/(S1)/(R7)/(R5) are true statements with a genuine proof-technique
-- gap, not falsified theorems -- REVISED BELOW for (R7).
--
-- CORRECTION (2026-07-24, third pass): theorem-B9-R7 is not merely
-- unproven -- it is FALSE, confirmed by a genuine, machine-checked
-- counterexample (B5Core.agda's r7b-refuted). Unlike (F), (R7) has no
-- embedded step-derivation to recurse on -- it's a direct, one-shot
-- equality with nothing to let the collectX/shift-based "root-loss
-- redistribution" defect cancel out (the same defect documented at
-- Lemma B.5's old location and re-confirmed for (F)'s auxiliary lemma
-- above). Concretely: e[v] := snd(pair(loss(7), snd(pair(decide(),5))))
-- records loss 7 *before* reaching a stuck operation; thenE's own Esem
-- clause redistributes that root loss via a "shift 0#"-shaped step that
-- provably drops it at a node (collapse-shift-0's generalisation to
-- r ≠ 0# is false, confirmed earlier), giving LHS root 0 where RHS
-- (glocalE ... zeroLC, which faithfully preserves e[v]'s own denotation)
-- has root 7. So rule (R7) is denotationally UNSOUND for this "hat"
-- semantics as formalised: there exist well-typed programs where the
-- R7 step doesn't preserve Esem. theorem-B9-R7 is kept postulated here
-- only as a clearly-flagged FALSE statement (not "true but hard") --
-- theorem-B9 as a whole therefore has a genuine counterexample through
-- this case, not just a gap. (R5)'s "fl" continuation is built via the
-- exact same thenE-wrapping-a-potentially-stuck-body shape (`vabs
-- (thenE sub handled g')`), so it's suspected to share this defect, but
-- a full concrete counterexample (needing a real Handler/ContCxt
-- instance) wasn't constructed.
--
-- SECOND CORRECTION (same session, after the above): the FALSITY
-- diagnosed just above was traced to Esem(thenE...)'s own combine-step
-- (a collectX+bind̂+tell cycle that redistributes g's own accumulated
-- root-loss down past any stuck node it reaches -- exactly the "shift
-- 0# ≠ id at a node" defect). Replacing that combine-step with a plain
-- mapŴ bump (see Denotational.agda's Esem(thenE...) clause, and its own
-- comment) fixes R7 outright -- confirmed both in Haskell
-- (R7Counterexample.hs) and here: theorem-B9-R7-gen (above, PROVEN, not
-- postulated) is the generalised replacement, and theorem-B9-R7 below is
-- now just its corollary at γ:=⌊g⌋[subamb,ρ]. B5Core.agda's r7b-check
-- now holds by refl (the counterexample that used to refute it no
-- longer does). theorem-B9-S1 remains genuinely open -- (S1) was never
-- shown false, only unproven, and (unlike R7) it has no fix candidate
-- identified yet.
-- theorem-B9-S1, consolidated onto the single theorem-B9-S1-gen
-- postulate above (rather than being its own independent, potentially-
-- divergent assumption).
theorem-B9-S1 : ∀ {Γ ε εamb ℓ par σ σ'} (sub : εamb ⊆ᵉ ε) {g : LC Γ σ' εamb} (h : Handler Γ ℓ par σ σ' ε) (v : Val Γ (gnd par))
    {e e' : Γ ⊢ σ ! (ε ,ℓ ℓ)} {r : R}
    → vabs (thenE sub (retApplied h v) (weaken1V g)) ⊢ e -[ r ]→ e' → (ρ : Env Γ)
    → Esem (handleE h (val v) e) ρ ⌊ g ⌋[ sub , ρ ] ≡ tell r (Esem (handleE h (val v) e') ρ ⌊ g ⌋[ sub , ρ ])
theorem-B9-S1 sub {g} h v stp ρ = theorem-B9-S1-gen sub h v stp ρ ⌊ g ⌋[ sub , ρ ]

theorem-B9-R7 : ∀ {Γ ε εg εamb σ} (sub : εg ⊆ᵉ ε) {g : LC Γ Loss εamb} (subamb : εamb ⊆ᵉ ε)
  (v : Val Γ σ) (e : (Γ , σ) ⊢ Loss ! εg) (ρ : Env Γ)
  → Esem (thenE sub (val v) (vabs e)) ρ ⌊ g ⌋[ subamb , ρ ]
  ≡ tell 0# (Esem (glocalE ⊆ᵉ-refl sub (e [ v ]) zeroLC) ρ ⌊ g ⌋[ subamb , ρ ])
theorem-B9-R7 sub {g} subamb v e ρ = theorem-B9-R7-gen sub v e ρ ⌊ g ⌋[ subamb , ρ ]

-- theorem-B9-R5, likewise consolidated onto theorem-B9-R5-gen -- kept
-- for historical reference (theorem-B9-R5-gen is genuinely false, see
-- above), but SUPERSEDED by theorem-B9-R5-WF below, which proves this
-- exact statement directly and postulate-free, under an added RootZero
-- (g) hypothesis. This was refuted by B5Core2.agda's hIll/h2
-- counterexample (an "ill-behaved" clause combined with an adversarial,
-- S-handleB-embedded nested handler) against the OLD handlerSem, then
-- RESOLVED by fixing handlerSem to match the paper's own construction
-- (Denotational.agda) -- that exact counterexample (B5Core2.agda's
-- r5-ill-check) now holds by refl.
theorem-B9-R5 : ∀ {Γ ε εamb ℓ par σ σ' εop} (sub : εamb ⊆ᵉ ε) {g : LC Γ σ' εamb}
    (h : Handler Γ ℓ par σ σ' ε) (v1 : Val Γ (gnd par)) (m : ℓ ∈ εop) (op : Op ℓ) (v2 : Val Γ (gnd (out op)))
    (k : ContCxt Γ (gnd (in′ op)) εop σ (ε ,ℓ ℓ)) (nh : ¬ Handles k ℓ) (ρ : Env Γ) → let
      h' = renH S h ; g' = renV S g ; k' = weaken1K k
      handled = handleE h' (fst (val (vvar Z))) (plugK k' (snd (val (vvar Z))))
      fk = vabs {σ = gnd par `× gnd (in′ op)} (glocalE sub ⊆ᵉ-refl handled g')
      fl = vabs {σ = gnd par `× gnd (in′ op)} (thenE sub handled g')
    in Esem (handleE h (val v1) (plugK k (opE m op (val v2)))) ρ ⌊ g ⌋[ sub , ρ ]
     ≡ tell 0# (Esem (subE (cons fk (cons fl (cons v2 (cons v1 idSub)))) (clause h op)) ρ ⌊ g ⌋[ sub , ρ ])
theorem-B9-R5 sub {g} h v1 m op v2 k nh ρ = theorem-B9-R5-gen sub h v1 m op v2 k nh ρ ⌊ g ⌋[ sub , ρ ]

-- theorem-B9-R5, proved DIRECTLY (not via theorem-B9-R5-gen, which is
-- genuinely false -- see the comment above its own postulate), under the
-- extra hypothesis that g's own semantic value never has any nonzero
-- root/node-loss (RootZero) -- exactly the invariant RootZero-thenE-wrap
-- proves theorem-B9's own induction actually maintains (g only ever
-- gets rebuilt via thenE-wrapping, at (F-rule)/(S1), starting from
-- zeroLC). Both halves of the fk/fl-vs-k1v/l1v matching argument now
-- close: fk-match (fk/k1v, unconditional) and lemma-fl-l1v-match
-- (fl/l1v, needing RootZero(g) -- this is what l1v's collectX-based
-- reading, not the old collect-based one, actually buys us).
theorem-B9-R5-WF : ∀ {Γ ε εamb ℓ par σ σ' εop} (sub : εamb ⊆ᵉ ε) {g : LC Γ σ' εamb}
    (h : Handler Γ ℓ par σ σ' ε) (v1 : Val Γ (gnd par)) (m : ℓ ∈ εop) (op : Op ℓ) (v2 : Val Γ (gnd (out op)))
    (k : ContCxt Γ (gnd (in′ op)) εop σ (ε ,ℓ ℓ)) (nh : ¬ Handles k ℓ) (ρ : Env Γ)
    (rzg : ∀ a → RootZero (Vsem g ρ a (λ _ → η̂ tt))) → let
      h' = renH S h ; g' = renV S g ; k' = weaken1K k
      handled = handleE h' (fst (val (vvar Z))) (plugK k' (snd (val (vvar Z))))
      fk = vabs {σ = gnd par `× gnd (in′ op)} (glocalE sub ⊆ᵉ-refl handled g')
      fl = vabs {σ = gnd par `× gnd (in′ op)} (thenE sub handled g')
    in Esem (handleE h (val v1) (plugK k (opE m op (val v2)))) ρ ⌊ g ⌋[ sub , ρ ]
     ≡ tell 0# (Esem (subE (cons fk (cons fl (cons v2 (cons v1 idSub)))) (clause h op)) ρ ⌊ g ⌋[ sub , ρ ])
theorem-B9-R5-WF {Γ} {ε} {εamb} {ℓ} {par} {σ} {σ'} {εop} sub {g} h v1 m op v2 k nh ρ rzg =
  trans (trans step1 step2) (trans step3 (sym (tell-0 _)))
  where
  h' = renH S h ; g' = renV S g ; k' = weaken1K k
  pArg' : (Γ , (gnd par `× gnd (in′ op))) ⊢ gnd par ! ε
  pArg' = pArg {Γ = Γ} {γ = par} {δ = in′ op}
  yArg' : (Γ , (gnd par `× gnd (in′ op))) ⊢ gnd (in′ op) ! εop
  yArg' = yArg {Γ = Γ} {γ = par} {δ = in′ op}
  handled = handleE h' pArg' (plugK k' yArg')
  fk = vabs {σ = gnd par `× gnd (in′ op)} (glocalE sub ⊆ᵉ-refl handled g')
  fl = vabs {σ = gnd par `× gnd (in′ op)} (thenE sub handled g')

  γ : ⟦ σ' ⟧ → Ŵ ε ⊤
  γ = ⌊ g ⌋[ sub , ρ ]
  p1 : ⟦ gnd par ⟧
  p1 = Vsem v1 ρ
  κ : ⟦ in′ op ⟧ᴳ → Ŝ (ε ,ℓ ℓ) ⟦ σ ⟧
  κ a = Esem (plugK (weaken1K k) (val (vvar Z))) (ρ ,, a)
  K' : ⟦ in′ op ⟧ᴳ → (⟦ gnd par ⟧ → Ŵ ε ⟦ σ' ⟧)
  K' a = ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) (κ a (λ _ → η̂ tt))
  π₂ = λ { (_ , r1) → r1 }

  clauseEnv : Env ((((Γ , gnd par) , gnd (out op)) , ((gnd par `× gnd (in′ op)) ⇒ Loss ! ε)) , ((gnd par `× gnd (in′ op)) ⇒ σ' ! ε))
  clauseEnv = (((ρ ,, p1) ,, Vsem v2 ρ) ,, (λ { (p'' , a) γ1 → mapŴ π₂ (collectX (ext̂ Ŵ-alg γ (K' a p''))) })) ,, (λ { (p'' , a) γ' → K' a p'' })

  step1 : Esem (handleE h (val v1) (plugK k (opE m op (val v2)))) ρ γ
        ≡ tell 0# (handlerΨ h ρ γ (promote k nh m) op (Vsem v2 ρ) K' p1)
  step1 = trans (cong (λ F → F γ) (bindˢ-unitˡ (λ p → handlerSem h ρ p (Esem (plugK k (opE m op (val v2))) ρ)) p1))
                (cong (λ w → ext̂ (handlerAlg h ρ γ) (handlerRet h ρ γ) w p1) (lemma-B8 op v2 k m nh ρ (λ _ → η̂ tt)))

  step2 : tell 0# (handlerΨ h ρ γ (promote k nh m) op (Vsem v2 ρ) K' p1)
        ≡ Esem (clause h op) clauseEnv γ
  step2 = trans (tell-0 _) (cong (λ f → f p1) (handlerΨ-yes-eq h ρ γ (promote k nh m) op (Vsem v2 ρ) K'))

  -- Bridges handled's own evaluation (under ANY ambient γ0) to a fresh
  -- handlerSem call -- same pattern as fk-match's own S-handleB case,
  -- now against the simpler, D-free handlerSem.
  handled-eq : ∀ (p'' : ⟦ gnd par ⟧) (a : ⟦ in′ op ⟧ᴳ) (γ0 : ⟦ σ' ⟧ → Ŵ ε ⊤)
             → Esem handled (ρ ,, (p'' , a)) γ0 ≡ handlerSem h ρ p'' (κ a) γ0
  handled-eq p'' a γ0 = trans (cong (λ F → F γ0) (trans hStepA hStepB)) (trans hStepC hStepD)
    where
    pArgEq : Esem pArg' (ρ ,, (p'' , a)) ≡ η̂ˢ p''
    pArgEq = bindˢ-unitˡ {ε = ε} {X = ⟦ gnd par ⟧ × ⟦ in′ op ⟧ᴳ} {Y = ⟦ gnd par ⟧} (λ { (x , y) → η̂ˢ x }) (p'' , a)

    hStepA : bind̂ˢ (λ p → handlerSem h' (ρ ,, (p'' , a)) p (Esem (plugK k' yArg') (ρ ,, (p'' , a)))) (Esem pArg' (ρ ,, (p'' , a)))
           ≡ bind̂ˢ (λ p → handlerSem h' (ρ ,, (p'' , a)) p (Esem (plugK k' yArg') (ρ ,, (p'' , a)))) (η̂ˢ p'')
    hStepA = cong (bind̂ˢ (λ p → handlerSem h' (ρ ,, (p'' , a)) p (Esem (plugK k' yArg') (ρ ,, (p'' , a))))) pArgEq

    hStepB : bind̂ˢ (λ p → handlerSem h' (ρ ,, (p'' , a)) p (Esem (plugK k' yArg') (ρ ,, (p'' , a)))) (η̂ˢ p'')
           ≡ handlerSem h' (ρ ,, (p'' , a)) p'' (Esem (plugK k' yArg') (ρ ,, (p'' , a)))
    hStepB = bindˢ-unitˡ {ε = ε} {X = ⟦ gnd par ⟧} {Y = ⟦ σ' ⟧} (λ p → handlerSem h' (ρ ,, (p'' , a)) p (Esem (plugK k' yArg') (ρ ,, (p'' , a)))) p''

    hStepC : handlerSem h' (ρ ,, (p'' , a)) p'' (Esem (plugK k' yArg') (ρ ,, (p'' , a))) γ0
           ≡ handlerSem h' (ρ ,, (p'' , a)) p'' (κ a) γ0
    hStepC = cong (λ w → handlerSem h' (ρ ,, (p'' , a)) p'' w γ0) (fk-match op k ρ p'' a)

    hStepD : handlerSem h' (ρ ,, (p'' , a)) p'' (κ a) γ0 ≡ handlerSem h ρ p'' (κ a) γ0
    hStepD = weaken1H-coh (gnd par `× gnd (in′ op)) h ρ (p'' , a) p'' (κ a) γ0

  δ-eq : ∀ (p'' : ⟦ gnd par ⟧) (a : ⟦ in′ op ⟧ᴳ) → (λ (b : ⟦ σ' ⟧) → widenŴ sub (Lsem g' (ρ ,, (p'' , a)) b)) ≡ γ
  δ-eq p'' a = funext (λ b → cong (widenŴ sub) (cong collapse (cong (λ f → f b (λ _ → η̂ tt)) (weaken1V-coh (gnd par `× gnd (in′ op)) g ρ (p'' , a)))))

  fkMatch : ∀ (p'' : ⟦ gnd par ⟧) (a : ⟦ in′ op ⟧ᴳ) (γ' : ⟦ σ' ⟧ → Ŵ ε ⊤) → Vsem fk ρ (p'' , a) γ' ≡ K' a p''
  fkMatch p'' a γ' =
    trans (widenŴ-refl (Esem handled (ρ ,, (p'' , a)) (λ b → widenŴ sub (Lsem g' (ρ ,, (p'' , a)) b))))
          (trans (handled-eq p'' a (λ b → widenŴ sub (Lsem g' (ρ ,, (p'' , a)) b)))
                 (cong (λ γ0 → handlerSem h ρ p'' (κ a) γ0) (δ-eq p'' a)))

  Gv : ⟦ σ' ⟧ → Ŵ ε R
  Gv b = widenŴ sub (Vsem g ρ b (λ _ → η̂ tt))

  Gv-eq : ∀ (p'' : ⟦ gnd par ⟧) (a : ⟦ in′ op ⟧ᴳ) (b : ⟦ σ' ⟧)
        → widenŴ sub (Vsem g' (ρ ,, (p'' , a)) b (λ _ → η̂ tt)) ≡ Gv b
  Gv-eq p'' a b = cong widenŴ' (cong (λ f → f b (λ _ → η̂ tt)) (weaken1V-coh (gnd par `× gnd (in′ op)) g ρ (p'' , a)))
    where widenŴ' = widenŴ sub

  flMatch : ∀ (p'' : ⟦ gnd par ⟧) (a : ⟦ in′ op ⟧ᴳ) (γ1 : R → Ŵ ε ⊤)
          → Vsem fl ρ (p'' , a) γ1 ≡ mapŴ π₂ (collectX (ext̂ Ŵ-alg γ (K' a p'')))
  flMatch p'' a γ1 = trans (trans stepA (trans stepB stepC)) stepE
    where
    δ : ⟦ σ' ⟧ → Ŵ ε ⊤
    δ b = widenŴ sub (Lsem g' (ρ ,, (p'' , a)) b)
    combine : Ŵ ε ⟦ σ' ⟧ → Ŵ ε R
    combine w = bind̂ (collectX w) (λ { (b , r1) → mapŴ (r1 +_) (widenŴ sub (Vsem g' (ρ ,, (p'' , a)) b (λ _ → η̂ tt))) })

    stepA : Vsem fl ρ (p'' , a) γ1 ≡ combine (Esem handled (ρ ,, (p'' , a)) δ)
    stepA = refl

    stepB : combine (Esem handled (ρ ,, (p'' , a)) δ) ≡ combine (handlerSem h ρ p'' (κ a) δ)
    stepB = cong combine (handled-eq p'' a δ)

    stepC : combine (handlerSem h ρ p'' (κ a) δ) ≡ bind̂ (collectX (K' a p'')) (λ { (b , r1) → mapŴ (r1 +_) (Gv b) })
    stepC = trans (cong (λ γ0 → combine (handlerSem h ρ p'' (κ a) γ0)) (δ-eq p'' a))
                  (cong (bind̂ (collectX (K' a p''))) (funext (λ { (b , r1) → cong (mapŴ (r1 +_)) (Gv-eq p'' a b) })))

    collapse-Gv-eq : (λ b → collapse (Gv b)) ≡ γ
    collapse-Gv-eq = funext (λ b → collapse-widenŴ-comm sub (Vsem g ρ b (λ _ → η̂ tt)))

    stepD : mapŴ π₂ (collectX (bind̂ (K' a p'') (λ b → collapse (Gv b)))) ≡ mapŴ π₂ (collectX (ext̂ Ŵ-alg γ (K' a p'')))
    stepD = cong (λ F → mapŴ π₂ (collectX (bind̂ (K' a p'') F))) collapse-Gv-eq

    stepE : bind̂ (collectX (K' a p'')) (λ { (b , r1) → mapŴ (r1 +_) (Gv b) }) ≡ mapŴ π₂ (collectX (ext̂ Ŵ-alg γ (K' a p'')))
    stepE = trans (sym (lemma-fl-l1v-match (K' a p'') Gv (λ b → RootZero-widenŴ sub (Vsem g ρ b (λ _ → η̂ tt)) (rzg b)))) stepD

  step3 : Esem (clause h op) clauseEnv γ ≡ Esem (subE (cons fk (cons fl (cons v2 (cons v1 idSub)))) (clause h op)) ρ γ
  step3 = sym (cong (λ F → F γ) (subE-coh (cons fk (cons fl (cons v2 (cons v1 idSub)))) ρ clauseEnv subcoh (clause h op)))
    where
    subcoh : SubCoh (cons fk (cons fl (cons v2 (cons v1 idSub)))) ρ clauseEnv
    subcoh Z                 = funext (λ { (p'' , a) → funext (fkMatch p'' a) })
    subcoh (S Z)             = funext (λ { (p'' , a) → funext (flMatch p'' a) })
    subcoh (S (S Z))         = refl
    subcoh (S (S (S Z)))     = refl
    subcoh (S (S (S (S x)))) = refl

-- (R1) f(v) → v'
theorem-B9 sub {g} (R1 f x) ρ = trans
  (cong (λ F → F ⌊ g ⌋[ sub , ρ ]) (bindˢ-unitˡ (λ a → η̂ˢ (⟦ f ⟧f a)) x))
  (sym (tell-0 (leaf 0# (⟦ f ⟧f x))))

-- (R2) (v1,v2).i → vi
theorem-B9 sub {g} (R2-fst {σ = σ} {τ = τ} v w) ρ =
  trans (cong (λ F → F ⌊ g ⌋[ sub , ρ ]) fstEqS) (sym (tell-0 (leaf 0# (Vsem v ρ))))
  where
  pairEq : Esem (pair (val v) (val w)) ρ ≡ η̂ˢ (Vsem v ρ , Vsem w ρ)
  pairEq = trans (bindˢ-unitˡ (λ a → bind̂ˢ (λ b → η̂ˢ (a , b)) (η̂ˢ (Vsem w ρ))) (Vsem v ρ))
                 (bindˢ-unitˡ (λ b → η̂ˢ (Vsem v ρ , b)) (Vsem w ρ))
  fstEqS : Esem (fst (pair (val v) (val w))) ρ ≡ η̂ˢ (Vsem v ρ)
  fstEqS = trans (cong (bind̂ˢ (λ{ (a , b) → η̂ˢ a })) pairEq)
                 (bindˢ-unitˡ {X = ⟦ σ ⟧ × ⟦ τ ⟧} (λ{ (a , b) → η̂ˢ a }) (Vsem v ρ , Vsem w ρ))

theorem-B9 sub {g} (R2-snd {σ = σ} {τ = τ} v w) ρ =
  trans (cong (λ F → F ⌊ g ⌋[ sub , ρ ]) sndEqS) (sym (tell-0 (leaf 0# (Vsem w ρ))))
  where
  pairEq : Esem (pair (val v) (val w)) ρ ≡ η̂ˢ (Vsem v ρ , Vsem w ρ)
  pairEq = trans (bindˢ-unitˡ (λ a → bind̂ˢ (λ b → η̂ˢ (a , b)) (η̂ˢ (Vsem w ρ))) (Vsem v ρ))
                 (bindˢ-unitˡ (λ b → η̂ˢ (Vsem v ρ , b)) (Vsem w ρ))
  sndEqS : Esem (snd (pair (val v) (val w))) ρ ≡ η̂ˢ (Vsem w ρ)
  sndEqS = trans (cong (bind̂ˢ (λ{ (a , b) → η̂ˢ b })) pairEq)
                 (bindˢ-unitˡ {X = ⟦ σ ⟧ × ⟦ τ ⟧} (λ{ (a , b) → η̂ˢ b }) (Vsem v ρ , Vsem w ρ))

-- (R3) (λ^ε x:σ.e) v → e[v/x]
theorem-B9 sub {g} (R3 e v) ρ = trans step1 (trans step2 (sym (tell-0 (Esem (e [ v ]) ρ γ))))
  where
  γ = ⌊ g ⌋[ sub , ρ ]
  step1 : Esem (app (val (vabs e)) (val v)) ρ γ ≡ Esem e (ρ ,, Vsem v ρ) γ
  step1 = trans (cong (λ F → F γ) (bindˢ-unitˡ (λ φ → bind̂ˢ (λ a → φ a) (η̂ˢ (Vsem v ρ))) (Vsem (vabs e) ρ)))
                (cong (λ F → F γ) (bindˢ-unitˡ (λ a → Vsem (vabs e) ρ a) (Vsem v ρ)))
  step2 : Esem e (ρ ,, Vsem v ρ) γ ≡ Esem (e [ v ]) ρ γ
  step2 = sym (cong (λ F → F γ) (sub1-coh e ρ v))

-- (R4) loss(r) → ()
theorem-B9 sub (R4 r) ρ = tell-0 (tell r (η̂ tt))

-- (R6) with h from v1 handle v2 → vr(v1,v2)
theorem-B9 sub {g} (R6 h v1 v2) ρ = trans step1 (sym (tell-0 (Esem (subE (cons v2 (cons v1 idSub)) (ret h)) ρ γ)))
  where
  γ = ⌊ g ⌋[ sub , ρ ]
  step1 : Esem (handleE h (val v1) (val v2)) ρ γ ≡ Esem (subE (cons v2 (cons v1 idSub)) (ret h)) ρ γ
  step1 = trans (cong (λ F → F γ) (bindˢ-unitˡ (λ p → handlerSem h ρ p (η̂ˢ (Vsem v2 ρ))) (Vsem v1 ρ)))
                (subst2-step)
    where
    -- handlerSem h ρ p (η̂ˢ a) γ = tell 0# (handlerRet h ρ γ a p), and
    -- Esem(ret h)((ρ,,p),,a) γ *is* handlerRet h ρ γ a p by definition, so
    -- with p := Vsem v1 ρ, a := Vsem v2 ρ, the only gap to the two-fold
    -- substitution subE (cons v2 (cons v1 idSub)) (ret h) is coherence.
    subst2-step : tell 0# (Esem (ret h) ((ρ ,, Vsem v1 ρ) ,, Vsem v2 ρ) γ) ≡ Esem (subE (cons v2 (cons v1 idSub)) (ret h)) ρ γ
    subst2-step = trans (tell-0 _) (sym (cong (λ F → F γ)
      (subE-coh (cons v2 (cons v1 idSub)) ρ ((ρ ,, Vsem v1 ρ) ,, Vsem v2 ρ) subcoh (ret h))))
      where
      subcoh : SubCoh (cons v2 (cons v1 idSub)) ρ ((ρ ,, Vsem v1 ρ) ,, Vsem v2 ρ)
      subcoh Z         = refl
      subcoh (S Z)     = refl
      subcoh (S (S x)) = refl

-- (R9) reset v → v
theorem-B9 sub {g} (R9 v) ρ = sym (tell-0 (leaf 0# (Vsem v ρ)))

-- (R8) ⟨v⟩^ε₁_g1 → v
theorem-B9 sub {g} (R8 sub1 sub2 v g1) ρ = sym (tell-0 (leaf 0# (Vsem v ρ)))

-- (R7) v ▶ λ^εg x:σ.e → ⟨e[v/x]⟩^εg_{λ^εg x:σ.0}
theorem-B9 sub {g} (R7 sub' v e) ρ = theorem-B9-R7 sub' {g = g} sub v e ρ

theorem-B9 sub {g} {e} {e'} {r} (F-rule sub' f stp) ρ =
  trans (cong (Esem e ρ) (⌊⌋-irrelevant g sub sub' ρ))
        (trans (theorem-B9-F sub' f stp ρ)
               (cong (λ F → tell r (Esem e' ρ F)) (sym (⌊⌋-irrelevant g sub sub' ρ))))
theorem-B9 sub {g} {e} {e'} {r} (S1 sub' h v stp) ρ =
  trans (cong (Esem e ρ) (⌊⌋-irrelevant g sub sub' ρ))
        (trans (theorem-B9-S1 sub' h v stp ρ)
               (cong (λ F → tell r (Esem e' ρ F)) (sym (⌊⌋-irrelevant g sub sub' ρ))))
theorem-B9 sub {g} (S2 sub' g1 stp) ρ = theorem-B9-S2 sub' {g = g} sub g1 stp ρ
theorem-B9 sub {g} (S3 sub1 sub2 g1 stp) ρ = theorem-B9-S3 sub1 sub2 sub {g = g} g1 stp ρ
theorem-B9 sub {g} (S4 stp) ρ = theorem-B9-S4 {g = g} stp ρ sub
theorem-B9 sub {g} (R5 sub' h v1 m op v2 k nh) ρ =
  trans (cong (Esem (handleE h (val v1) (plugK k (opE m op (val v2)))) ρ) (⌊⌋-irrelevant g sub sub' ρ))
        (trans (theorem-B9-R5 sub' h v1 m op v2 k nh ρ)
               (cong (λ F → tell 0# (Esem (subE (cons fk (cons fl (cons v2 (cons v1 idSub)))) (clause h op)) ρ F))
                     (sym (⌊⌋-irrelevant g sub sub' ρ))))
  where
  g' = renV S g
  handled = handleE (renH S h) (fst (val (vvar Z))) (plugK (weaken1K k) (snd (val (vvar Z))))
  fk = vabs {σ = gnd _ `× gnd (in′ op)} (glocalE sub' ⊆ᵉ-refl handled g')
  fl = vabs {σ = gnd _ `× gnd (in′ op)} (thenE sub' handled g')

-- ---------------------------------------------------------------------
-- Theorem 7.10 (hat-Theorem B.10): evaluation soundness. "None of Theorems
-- B.10, B.11, Corollary B.12, or Theorem B.13 inspect any deeper structure
-- of Ŵ_ε than [the] top-level pair" (the leaf's (r,x) or a stuck node's
-- (ℓ,op,v,f)) -- so, as the source observes, they transfer essentially
-- verbatim from Theorem 7.9 by induction on the big-step derivation.
-- `Stuck` records the two shapes big-step evaluation can end at: a value,
-- or a term stuck on an unhandled operation call under a context K.
-- ---------------------------------------------------------------------

data Stuck : ∀ {Γ σ ε} → Γ ⊢ σ ! ε → Set where
  stuckVal : ∀ {Γ σ ε} (v : Val Γ σ) → Stuck {Γ} {σ} {ε} (val v)
  stuckOp  : ∀ {Γ σ ε εop ℓ} (m : ℓ ∈ εop) (op : Op ℓ) (v : Val Γ (gnd (out op)))
             (K : ContCxt Γ (gnd (in′ op)) εop σ ε) (nh : ¬ Handles K ℓ)
           → Stuck (plugK K (opE m op (val v)))

-- (base case v, r=0: Lemma 7.2/lemma-B2 -- here just η̂ˢ's own definition,
-- so `done` reduces to `refl`; step case: Theorem 7.9 plus tell's own
-- definitional additivity at a leaf, tell r (leaf s x) = leaf (r+s) x,
-- exactly the "r=r₁+r₂" combination the source spells out via tell-+.)
theorem-7-10-val : ∀ {Γ σ ε εg} (sub : εg ⊆ᵉ ε) {g : LC Γ σ εg} {e : Γ ⊢ σ ! ε} {r : R} (v : Val Γ σ)
  → g ⊢ e ⇒[ r ] (val v) → (ρ : Env Γ)
  → Esem e ρ ⌊ g ⌋[ sub , ρ ] ≡ leaf r (Vsem v ρ)
theorem-7-10-val sub v (done .(val v)) ρ = refl
theorem-7-10-val sub v (step {r = r} stp rest) ρ =
  trans (theorem-B9 sub stp ρ) (cong (tell r) (theorem-7-10-val sub v rest ρ))

-- (base case, r=0: Lemma 7.8/lemma-B8 directly, φ̂ˢ unfolding to exactly
-- this node; step case: as above, using tell's definitional additivity at
-- a node, tell r (node m op s o κ) = node m op (r+s) o κ.)
theorem-7-10-op : ∀ {Γ σ ε εg εop ℓ} (sub : εg ⊆ᵉ ε) {g : LC Γ σ εg} {e : Γ ⊢ σ ! ε} {r : R}
  (m : ℓ ∈ εop) (op : Op ℓ) (v : Val Γ (gnd (out op))) (K : ContCxt Γ (gnd (in′ op)) εop σ ε) (nh : ¬ Handles K ℓ)
  → g ⊢ e ⇒[ r ] (plugK K (opE m op (val v))) → (ρ : Env Γ)
  → Esem e ρ ⌊ g ⌋[ sub , ρ ] ≡
    node (promote K nh m) op r (Vsem v ρ) (λ a → Esem (plugK (weaken1K K) (val (vvar Z))) (ρ ,, a) ⌊ g ⌋[ sub , ρ ])
theorem-7-10-op sub {g} m op v K nh (done .(plugK K (opE m op (val v)))) ρ = lemma-B8 op v K m nh ρ ⌊ g ⌋[ sub , ρ ]
theorem-7-10-op sub {g} m op v K nh (step {r = r} stp rest) ρ =
  trans (theorem-B9 sub stp ρ) (cong (tell r) (theorem-7-10-op sub m op v K nh rest ρ))

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
             → Σ R (λ r → Σ (Γ ⊢ σ ! ε) (λ w → (g ⊢ e ⇒[ r ] w) × Stuck w))

leaf≢node : ∀ {ε X} {r x} {ℓ} {m : ℓ ∈ ε} {op : Op ℓ} {r' o κ}
          → leaf {ε} {X} r x ≡ node m op r' o κ → ⊥
leaf≢node ()

leaf-inj-r : ∀ {ε X} {r r' : R} {x x' : X} → leaf {ε} r x ≡ leaf r' x' → r ≡ r'
leaf-inj-r refl = refl

leaf-inj-x : ∀ {ε X} {r r' : R} {x x' : X} → leaf {ε} r x ≡ leaf r' x' → x ≡ x'
leaf-inj-x refl = refl

theorem-7-11-val : ∀ {Γ σ ε εg} (sub : εg ⊆ᵉ ε) (g : LC Γ σ εg) (e : Γ ⊢ σ ! ε) (ρ : Env Γ) {r : R} {a : ⟦ σ ⟧}
  → Esem e ρ ⌊ g ⌋[ sub , ρ ] ≡ leaf r a
  → Σ (Val Γ σ) (λ v → (g ⊢ e ⇒[ r ] (val v)) × (Vsem v ρ ≡ a))
theorem-7-11-val sub g e ρ {r} {a} heq with Terminates g e
theorem-7-11-val sub g e ρ {r} {a} heq | r' , .(val v') , bigstep , stuckVal v'
  with leaf-inj-r (trans (sym heq) (theorem-7-10-val sub v' bigstep ρ))
     | leaf-inj-x (trans (sym heq) (theorem-7-10-val sub v' bigstep ρ))
... | refl | refl = v' , bigstep , refl
theorem-7-11-val sub g e ρ {r} {a} heq | r' , .(plugK K (opE m op (val v'))) , bigstep , stuckOp m op v' K nh
  = ⊥-elim (leaf≢node (trans (sym heq) (theorem-7-10-op sub m op v' K nh bigstep ρ)))

-- The node/op-stuck half of adequacy: same argument shape (Terminates +
-- Theorem 7.10 + Ŵ-injectivity, ruling out the mismatching leaf case
-- exactly as above), but concluding the equality of *two* node terms
-- rather than two leaves. Since `node`'s own `op` (and hence the type of
-- its `o`,`κ` fields) is indexed by its own `ℓ ∈ ε` witness, extracting
-- "the ℓ,op Terminates discovers are the ones the hypothesis names" is a
-- "no confusion" argument for this dependent constructor -- the same kind
-- of index bookkeeping already postulated for Lemma B.8's F∘/S∘ cases and
-- several of Theorem B.9's frame cases, not chased down further here.
postulate
  theorem-7-11-op : ∀ {Γ σ ε εg ℓ} (sub : εg ⊆ᵉ ε) (g : LC Γ σ εg) (e : Γ ⊢ σ ! ε) (ρ : Env Γ)
    {r : R} (m : ℓ ∈ ε) (op : Op ℓ) (o : ⟦ out op ⟧ᴳ) (κ : ⟦ in′ op ⟧ᴳ → Ŵ ε ⟦ σ ⟧)
    → Esem e ρ ⌊ g ⌋[ sub , ρ ] ≡ node m op r o κ
    → Σ (Val Γ (gnd (out op))) (λ v →
        Σ EffCxt (λ εop → Σ (ℓ ∈ εop) (λ m' →
        Σ (ContCxt Γ (gnd (in′ op)) εop σ ε) (λ K → Σ (¬ Handles K ℓ) (λ nh →
          (promote K nh m' ≡ m)
          × (g ⊢ e ⇒[ r ] (plugK K (opE m' op (val v))))
          × (Vsem v ρ ≡ o)
          × (κ ≡ (λ a → Esem (plugK (weaken1K K) (val (vvar Z))) (ρ ,, a) ⌊ g ⌋[ sub , ρ ])))))))

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
  → g ⊢ e ⇒[ r ] (val v) → Esem e ρ ⌊ g ⌋[ ⊆ᵉ-refl , ρ ] ≡ leaf r (Vsem v ρ)
corollary-7-12-fwd g e ρ v bigstep = theorem-7-10-val ⊆ᵉ-refl v bigstep ρ

corollary-7-12-bwd : ∀ {σ} → FirstOrder σ → (g : LC ∅ σ []) (e : ∅ ⊢ σ ! []) (ρ : Env ∅) {r : R} (v : Val ∅ σ)
  → Esem e ρ ⌊ g ⌋[ ⊆ᵉ-refl , ρ ] ≡ leaf r (Vsem v ρ) → g ⊢ e ⇒[ r ] (val v)
corollary-7-12-bwd fo g e ρ v heq with theorem-7-11-val ⊆ᵉ-refl g e ρ heq
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
