{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Modulo-H accessibility / guardedness through the two DATA-level
-- branchings a loop body is built from: a Boolean conditional
-- (`if_then_else_`, which `_◁_▷_` unfolds to) and a `Maybe` eliminator
-- (`maybe′`).  Both are pure case splits, so each lemma is a case split.
-- No `postulate`, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Level using (Level)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Process_Trees

module CSP.Laws.DivFree.ReachExtra {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open import CSP.Operators E-≟ using (EventSet)
open import CSP.Laws.DivFree.ModAcc E-≟ using (MAccR)
open import CSP.Laws.DivFree.Loop E-≟ using (Guarded)

private
  variable
    ℓr ℓa : Level
    R     : Set ℓr
    A     : Set ℓa
    H     : EventSet

-- a conditional is accessible when both arms are
MAccR-if : ∀ (b : Bool) {P Q : PTree E (ExtI E) R} → MAccR H P → MAccR H Q → MAccR H (if b then P else Q)
MAccR-if true  rp rq = rp
MAccR-if false rp rq = rq

-- a conditional is guarded when both arms are
Guarded-if : ∀ (b : Bool) {P Q : PTree E (ExtI E) R} → Guarded H P → Guarded H Q → Guarded H (if b then P else Q)
Guarded-if true  gp gq = gp
Guarded-if false gp gq = gq

-- a `Maybe` eliminator is accessible when both of its cases are
MAccR-maybe′ : {f : A → PTree E (ExtI E) R} {y : PTree E (ExtI E) R}
             → (∀ x → MAccR H (f x)) → MAccR H y → ∀ m → MAccR H (maybe′ f y m)
MAccR-maybe′ rf ry (just x) = rf x
MAccR-maybe′ rf ry nothing  = ry

-- a `Maybe` eliminator is guarded when both of its cases are
Guarded-maybe′ : {f : A → PTree E (ExtI E) R} {y : PTree E (ExtI E) R}
               → (∀ x → Guarded H (f x)) → Guarded H y → ∀ m → Guarded H (maybe′ f y m)
Guarded-maybe′ gf gy (just x) = gf x
Guarded-maybe′ gf gy nothing  = gy
