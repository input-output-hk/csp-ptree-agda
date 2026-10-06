{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- τ-accessibility at every reachable state survives the injective
-- renaming `renameMap` (a renamed τ is a source τ: `ren-τ-inv`; a √-free
-- renamed run is the image of a source run: `rename-∖√-elim`).
-- Only the τ form (H = ∅) — every hide in the Leios composites sits ABOVE
-- the renamings, so no counted event set has to cross one.
-- No `postulate`, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Data.Maybe using (Maybe; just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees

module CSP.Laws.DivFree.ReachRename {ℓ ℓe₁ ℓe₂}
  {E₁ : Set ℓ → Set ℓe₁} {E₂ : Set ℓ → Set ℓe₂}
  (ι      : ∀ {A} → E₁ A → E₂ A)
  (ι⁻¹    : ∀ {A} → E₂ A → Maybe (E₁ A))
  (ι-linv : ∀ {A} (e : E₁ A) → ι⁻¹ (ι e) ≡ just e) where
open PTree
open import CSP.Rename {E₁ = E₁} {E₂ = E₂} ι ι⁻¹ ι-linv
open import CSP.Laws.Traces.RenameDeadlock {E₁ = E₁} {E₂ = E₂} ι ι⁻¹ ι-linv
  using (ren-τ-inv; rename-∖√-elim)
import Semantics.DivergenceFree {E = E₁} {I = ExtI E₁} as DF1
import Semantics.DivergenceFree {E = E₂} {I = ExtI E₂} as DF2

-- root: a renamed τ is a source τ, so accessibility transfers step by step
τ-Acc-renameMap : ∀ {ℓr} {Rr : Set ℓr} {P : PTree E₁ (ExtI E₁) Rr}
                → DF1.τ-Acc P → DF2.τ-Acc (renameMap P)
τ-Acc-renameMap {P = P} (DF1.acc f) = DF2.acc λ st →
  τ-Acc-renameMap-step f (ren-τ-inv {inv = ι-vis-inv} {P = P} st)
  where
    -- decode one renamed τ and recurse on the source successor
    τ-Acc-renameMap-step : ∀ {W} → (∀ {P₁} → _ → DF1.τ-Acc P₁) → _ → DF2.τ-Acc W
    τ-Acc-renameMap-step g (P₁ , Pτ , refl) = τ-Acc-renameMap (g Pτ)

-- reachable states: pull the √-free run back to the source
τ-AccReach-renameMap : ∀ {ℓr} {Rr : Set ℓr} {P : PTree E₁ (ExtI E₁) Rr}
                     → DF1.τ-AccReach P → DF2.τ-AccReach (renameMap P)
τ-AccReach-renameMap ar r with rename-∖√-elim r
... | s , P′ , rP , refl = τ-Acc-renameMap (ar rP)
