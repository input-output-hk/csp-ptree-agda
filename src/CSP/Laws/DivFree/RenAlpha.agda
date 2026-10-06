{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- The ALPHABET of a renamed process (Leios no-livelock, Stage C, Task 9b).
-- Generic: no Leios/Cardano content.  With `CountRename`'s parameters
-- (ι⁻¹ an exact partial inverse), every label of every run of
-- `renameMap P` is an ι-image, so a fact true of every ι-image of a
-- source label holds along the run (`AllL-ren`).
-- No postulate, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Data.Maybe using (Maybe; just)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Process_Trees

module CSP.Laws.DivFree.RenAlpha {ℓ ℓe₁ ℓe₂}
  {E₁ : Set ℓ → Set ℓe₁} {E₂ : Set ℓ → Set ℓe₂}
  (ι      : ∀ {A} → E₁ A → E₂ A)
  (ι⁻¹    : ∀ {A} → E₂ A → Maybe (E₁ A))
  (ι-linv : ∀ {A} (e : E₁ A) → ι⁻¹ (ι e) ≡ just e)
  (ι-rinv : ∀ {A} {e₂ : E₂ A} {e : E₁ A} → ι⁻¹ e₂ ≡ just e → e₂ ≡ ι e)
  (E₁-≟ : (x y : AnyTypes E₁) → Dec (x ≡ y))
  (E₂-≟ : (x y : AnyTypes E₂) → Dec (x ≡ y)) where

open import CSP.Rename {E₁ = E₁} {E₂ = E₂} ι ι⁻¹ ι-linv using (renameMap)
open import CSP.Laws.DivFree.CountRename ι ι⁻¹ ι-linv ι-rinv E₁-≟ E₂-≟
  using (renE; RenL; rnil; rcons; ren-trace-elim-rel)
import Semantics.LTS {E = E₂} {I = ExtI E₂} as L2
import Semantics.Failures {E = E₂} {I = ExtI E₂} as D2
open import CSP.Laws.DivFree.Count E₂-≟ using (AllL; []; _∷_; labels)

-- a fact of every ι-image holds of every label of every run of the renamed process
AllL-ren : ∀ {ℓr} {Rr : Set ℓr} {Q : L2.Event → Set} → (∀ e → Q (renE e))
         → ∀ {P : PTree E₁ (ExtI E₁) Rr} {s W} → renameMap P D2.⟹⟨ s ⟩ W → AllL Q (labels s)
AllL-ren {Q = Q} q tr with ren-trace-elim-rel tr
... | _ , _ , _ , rl = go rl
  where
    -- along the label correspondence
    go : ∀ {ls ls′} → RenL ls ls′ → AllL Q ls′
    go rnil      = []
    go (rcons r) = q _ ∷ go r
