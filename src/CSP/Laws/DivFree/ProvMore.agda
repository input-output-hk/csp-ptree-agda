{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- More VALUE PROVENANCE (Leios no-livelock, Stage C, owner decision
-- D1-b).  Generic: no Leios/Cardano content.  Extends `Prov` with
--   * `Prov-free`, `AllL→Prov`, `AllT→PA` — chain-free and rely-only
--     components (every obligation absent, or an input of its own label)
--   * `ProvT-if`, `ProvT-maybe′`, `PA-if` — conditionals
--   * `PA-⦀⁺`, `PA-⦀Fin⁺`                 — the non-empty interleavings
--   * `Prov-comap`                         — re-valuing a chain along a relation
-- No postulate, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as UP
open UP using () renaming (⊤ to ⊤′)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Process_Trees

module CSP.Laws.DivFree.ProvMore {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open import CSP.Operators E-≟
open import Semantics.LTS {E = E} {I = ExtI E} hiding (Diverges)
open import CSP.Laws.DivFree.Count E-≟ using (AllL; []; _∷_; AllT)
open import CSP.Laws.DivFree.Prov E-≟

module _ {V : Set} {O Kp In : Event → V → Set} where

  -- a predicate that no label meets is never an obligation (chain-free components)
  Prov-free : ∀ {K} → (∀ {e x} → O e x → ⊥) → ∀ ls → Prov O Kp In K ls
  Prov-free f []       = tt
  Prov-free f (e ∷ ls) = (λ ox → ⊥-elim (f ox)) , Prov-free f ls

  -- a rely-only label list (every obligation is an input of its own label)
  AllL→Prov : ∀ {K ls} → AllL (λ e → ∀ {x} → O e x → In e x) ls → Prov O Kp In K ls
  AllL→Prov []      = tt
  AllL→Prov (p ∷ a) = (λ ox → inj₁ (p ox)) , AllL→Prov a

  -- … for a whole process, from an `AllT` traversal (the rely-only threads, the chain-free stores)
  AllT→PA : ∀ {ℓr} {R : Set ℓr} {P : PTree E (ExtI E) R}
          → AllT (λ e → ∀ {x} → O e x → In e x) P → PA O Kp In P
  AllT→PA a = pa λ tr → AllL→Prov (a tr)

  -- a conditional round tree
  ProvT-if : ∀ {ℓr} {R : Set ℓr} {K} {P Q : PTree E (ExtI E) R}
           → ∀ b → ProvT O Kp In K P → ProvT O Kp In K Q → ProvT O Kp In K (if b then P else Q)
  ProvT-if true  p q = p
  ProvT-if false p q = q

  -- a `maybe′` round tree
  ProvT-maybe′ : ∀ {ℓr ℓx} {R : Set ℓr} {X : Set ℓx} {K} {f : X → PTree E (ExtI E) R} {y : PTree E (ExtI E) R}
               → (∀ x → ProvT O Kp In K (f x)) → ProvT O Kp In K y → ∀ m → ProvT O Kp In K (maybe′ f y m)
  ProvT-maybe′ pf py (just x) = pf x
  ProvT-maybe′ pf py nothing  = py

  -- a conditional process
  PA-if : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R}
        → ∀ b → PA O Kp In P → PA O Kp In Q → PA O Kp In (if b then P else Q)
  PA-if true  p q = p
  PA-if false p q = q

  -- a non-empty interleaving of a list
  PA-⦀⁺ : ∀ {ℓr} {P : PTree E (ExtI E) (⊤′ {ℓr})} {Ps : List (PTree E (ExtI E) (⊤′ {ℓr}))}
        → PA O Kp In P → All (PA O Kp In) Ps → PA O Kp In (⦀⁺ P Ps)
  PA-⦀⁺ pP []          = pP
  PA-⦀⁺ pP (pQ ∷ pQs)  = PA-par≡ pP (PA-⦀⁺ pQ pQs)

  -- a non-empty finite interleaving
  PA-⦀Fin⁺ : ∀ {ℓr} n (f : Fin (suc n) → PTree E (ExtI E) (⊤′ {ℓr}))
           → (∀ i → PA O Kp In (f i)) → PA O Kp In (⦀Fin⁺ n f)
  PA-⦀Fin⁺ zero    f pf = pf fzero
  PA-⦀Fin⁺ (suc n) f pf = PA-par≡ (pf fzero) (PA-⦀Fin⁺ n (λ i → f (fsuc i)) (λ i → pf (fsuc i)))

-- re-valuing a chain (the medium carries payloads, the system blocks)
Prov-comap : {V V′ : Set} (Rv : V → V′ → Set) {O Kp In : Event → V → Set} {O′ Kp′ In′ : Event → V′ → Set}
             {K : V → Set} {K′ : V′ → Set}
           → (∀ {e y′} → O′ e y′ → Σ[ y ∈ V ] (O e y × Rv y y′))
           → (∀ {e y y′} → In e y → Rv y y′ → In′ e y′) → (∀ {e y y′} → Kp e y → Rv y y′ → Kp′ e y′)
           → (∀ {y y′} → K y → Rv y y′ → K′ y′)
           → ∀ ls → Prov O Kp In K ls → Prov O′ Kp′ In′ K′ ls
Prov-comap Rv o i kp k []       _       = tt
Prov-comap Rv o i kp k (e ∷ ls) (h , p) =
    (λ o′ → case o o′ of λ { (y , oy , r) → case h oy of λ { (inj₁ iy) → inj₁ (i iy r) ; (inj₂ ky) → inj₂ (k ky r) } })
  , Prov-comap Rv o i kp (λ { (inj₁ ky) r → inj₁ (k ky r) ; (inj₂ py) r → inj₂ (kp py r) }) ls p
