-- Standalone check of the "sub-lemma" needed inside Lemma L (the fl/l1v
-- matching argument): does
--   collect (tell r (collapse D)) ≡ mapŴ (r +_) D
-- hold whenever RootZero D, for D a genuine STUCK-OPERATION NODE (not
-- just a leaf) and r a NONZERO outer bump amount? B5Core2.agda's own
-- empirical confirmation (r5-leak-checkWF) only ever exercised the case
-- where D reduces to a LEAF (since it used ε=[], where a node is
-- impossible at all) -- this file tests the genuinely open NODE case
-- directly, at the raw Ŵ level, no Esem/handler machinery needed.
module RootZeroSubLemmaCheck where

open import Domains
open import Example using (mySig)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Product using (_×_; _,_; proj₂)

open Sig mySig
open import Denotational mySig using (collapse)
import Example

εD : EffCxt
εD = Example.ndet ∷ []

mD : Example.ndet ∈ εD
mD = here refl

-- D: a genuine stuck-operation NODE (decide()), with root 0# (so
-- RootZero D holds), whose two branches are LEAVES reporting 3/5.
D : Ŵ εD R
D = node mD Example.decide 0# tt (λ { true → leaf 0# 3 ; false → leaf 0# 5 })

-- r: a nonzero outer bump amount (mirrors K's own accumulated root loss
-- from an earlier, already-resolved operation).
r : R
r = 7

lhs rhs : Ŵ εD R
lhs = collect (tell r (collapse D))
rhs = mapŴ (r +_) D

-- Does the sub-lemma's claim hold for this D (a RootZero node)? NO --
-- confirmed false (7 vs 0): collapse ZEROES a node's own root
-- unconditionally (Denotational.agda: `collapse(node m op r o κ) =
-- node m op 0# o (...)`), so `tell r` re-introduces r AT THE ROOT of the
-- collapsed tree, and `collect` (which PRESERVES node roots, unlike
-- collapse) carries that r all the way through as the result's own root.
-- But `mapŴ (r +_) D` NEVER touches D's own node root at all (mapŴ only
-- ever bumps the eventual LEAF payload) -- so D's OWN root (0#, from
-- RootZero D) survives unchanged on that side. The two sides only agree
-- when D never actually reaches this node case at all, i.e. when g's own
-- semantic value is ALWAYS fully resolved to a leaf (never stuck on an
-- unhandled operation) for every input -- RootZero alone does not imply
-- this; RootZero permits a node with root 0#, exactly what breaks here.
-- sub-lemma-check : lhs ≡ rhs
-- sub-lemma-check = refl  -- FAILS: 7 != 0

-- ---------------------------------------------------------------------
-- Does replacing `collect` by `mapŴ proj₂ ∘ collectX` (collectX properly
-- REDISTRIBUTES an outer bump down to every leaf via `bump`, rather than
-- discarding it like collect does at nodes) fix this, given RootZero?
-- ---------------------------------------------------------------------

proj₂' : ⊤ × R → R
proj₂' (_ , b) = b

collectXD : Ŵ εD (⊤ × R)
collectXD = collectX (tell r (collapse D))

lhsX : Ŵ εD R
lhsX = mapŴ proj₂' collectXD

rhsX : Ŵ εD R
rhsX = mapŴ (r +_) D

-- D is RootZero (its own root is 0#, and both its leaf branches have
-- root 0# too) -- confirmed by lhsX/rhsX genuinely being trees whose
-- own equality needs function extensionality to state (Bool-branching
-- continuations), not by bare `refl`. The GENERAL, permanent version of
-- this fix -- proven by induction, not checked numerically -- lives in
-- Proofs.agda as `RootZero-collect-via-collectX`, and is what
-- Denotational.agda's handlerΨ (l1v) and theorem-B9-R5-WF actually use.
open import Proofs mySig using (RootZero; RootZero-collect-via-collectX)

D-RootZero : RootZero D
D-RootZero = refl , (λ { true → refl ; false → refl })

sub-lemma-checkX : lhsX ≡ rhsX
sub-lemma-checkX = RootZero-collect-via-collectX r D D-RootZero
