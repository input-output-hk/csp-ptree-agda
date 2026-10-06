{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- The no-livelock bridge under NESTED hiding.
--
--   noLivelockT-∖ : for A ⊆ H, a counting bound for H on P (with F
--                   monotone) and τ-accessibility of P give
--                   `(P ∖ A) ∖ H` NO divergences at all.
--
-- Route (generic; no LEM, no `HideDivergence`):
--   (a) a trace of `P ∖ A` de-hides to a trace of P (`Hide-trace-elim`);
--       hiding A ⊆ H only DROPS H-events, so #H H can only fall and
--       #V H is unchanged (`#H-hide`, `#V-hide`): the bound carries over;
--   (b) the bound for H also bounds A (#H A ≤ #H H, #V H ≤ #V A, F
--       monotone), so `τ-AccReach-∖# A` keeps `P ∖ A` τ-accessible, hence
--       no reachable state of `P ∖ A` diverges (`τ-AccReach→noDiv`);
--   then `noLivelockT H` on `P ∖ A`.
--
-- No `postulate`, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤n⇒m≤1+n)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees

module CSP.Laws.FD.NoLivelockHide {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS {E = E} {I = ExtI E} using (Event√; evl; evLabel; √)
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (divergences)
open import Semantics.DivergenceFree {E = E} {I = ExtI E} using (τ-AccReach)
open import CSP.Laws.Traces.TraceLawsHide E-≟ using (HideTr; hnil; hkeep; hdrop; h√; Hide-trace-elim)
open import CSP.Laws.DivFree.ModAcc E-≟ using (τ-AccReach→noDiv)
open import CSP.Laws.FD.NoLivelock E-≟ using (#H; #V; #H-in; #V-in; noLivelockT; τ-AccReach-∖#)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- an event set inside another
_⊆ᴱ_ : EventSet → EventSet → Set (lsuc ℓ ⊔ ℓe)
A ⊆ᴱ H = ∀ at a → A .mem at a → H .mem at a

-- a smaller set hides fewer events of a trace …
#H-⊆ : ∀ {A H} → A ⊆ᴱ H → ∀ (s : List (Event√ R)) → #H A s ≤ #H H s
#H-⊆ sub [] = z≤n
#H-⊆ {A = A} {H} sub (evl (evLabel B e a) ∷ s) with A .dec (B , e) a | H .dec (B , e) a
... | yes _  | yes _  = s≤s (#H-⊆ sub s)
... | yes mA | no ¬mH = ⊥-elim (¬mH (sub _ a mA))
... | no _   | yes _  = m≤n⇒m≤1+n (#H-⊆ sub s)
... | no _   | no _   = #H-⊆ sub s
#H-⊆ sub (√ _ ∷ s) = #H-⊆ sub s

-- … and so leaves more of them visible
#V-⊆ : ∀ {A H} → A ⊆ᴱ H → ∀ (s : List (Event√ R)) → #V H s ≤ #V A s
#V-⊆ sub [] = z≤n
#V-⊆ {A = A} {H} sub (evl (evLabel B e a) ∷ s) with A .dec (B , e) a | H .dec (B , e) a
... | yes _  | yes _  = #V-⊆ sub s
... | yes mA | no ¬mH = ⊥-elim (¬mH (sub _ a mA))
... | no _   | yes _  = m≤n⇒m≤1+n (#V-⊆ sub s)
... | no _   | no _   = s≤s (#V-⊆ sub s)
#V-⊆ sub (√ _ ∷ s) = s≤s (#V-⊆ sub s)

-- hiding A ⊆ H can only lower the H-count of a trace
#H-hide : ∀ {A H} {s′ s : List (Event√ R)} → A ⊆ᴱ H → HideTr A s′ s → #H H s ≤ #H H s′
#H-hide sub hnil = z≤n
#H-hide {H = H} sub (hkeep {B} {e} {a} _ h) with H .dec (B , e) a
... | yes _ = s≤s (#H-hide sub h)
... | no _  = #H-hide sub h
#H-hide {H = H} sub (hdrop {a = a} {s′} mA h) =
  ≤-trans (m≤n⇒m≤1+n (#H-hide sub h)) (≤-reflexive (sym (#H-in H s′ (sub _ a mA))))
#H-hide sub h√ = ≤-refl

-- … and keeps its H-visible count
#V-hide : ∀ {A H} {s′ s : List (Event√ R)} → A ⊆ᴱ H → HideTr A s′ s → #V H s ≡ #V H s′
#V-hide sub hnil = refl
#V-hide {H = H} sub (hkeep {B} {e} {a} _ h) with H .dec (B , e) a
... | yes _ = #V-hide sub h
... | no _  = cong suc (#V-hide sub h)
#V-hide {H = H} sub (hdrop {a = a} {s′} mA h) = trans (#V-hide sub h) (sym (#V-in H s′ (sub _ a mA)))
#V-hide sub h√ = refl

-- THE NESTED BRIDGE: a bound for H on P and τ-accessibility of P ⇒ `(P ∖ A) ∖ H` is divergence-free
noLivelockT-∖ : (A H : EventSet) (F : ℕ → ℕ) → (∀ {m n} → m ≤ n → F m ≤ F n) → A ⊆ᴱ H
  → {P : PTree E (ExtI E) R}
  → (∀ {s Q} → P ⟹⟨ s ⟩ Q → #H H s ≤ F (#V H s)) → τ-AccReach P
  → ∀ {s} → ¬ divergences ((P ∖ A) ∖ H) s
noLivelockT-∖ A H F mono sub {P} bnd acc =
  noLivelockT H F bndA (τ-AccReach→noDiv (τ-AccReach-∖# A F bndIO acc))
  where
    -- (a) on `P ∖ A`: de-hide the trace, then the H-counts move the right way
    bndA : ∀ {s Q} → (P ∖ A) ⟹⟨ s ⟩ Q → #H H s ≤ F (#V H s)
    bndA {s} tr = case Hide-trace-elim A P tr of λ where
      (s′ , _ , tr′ , h) →
        ≤-trans (#H-hide sub h) (subst (λ x → #H H s′ ≤ F x) (sym (#V-hide sub h)) (bnd tr′))
    -- the same bound, read for the smaller set A (for `τ-AccReach-∖# A`)
    bndIO : ∀ {s Q} → P ⟹⟨ s ⟩ Q → #H A s ≤ F (#V A s)
    bndIO {s} tr = ≤-trans (#H-⊆ sub s) (≤-trans (bnd tr) (mono (#V-⊆ sub s)))
