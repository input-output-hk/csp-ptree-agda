{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Traces of the interrupt `P △ Q` (Stage L, the breakable medium): every
-- run is a run of `P` followed by a run of `Q` (`△-trace-elim`), so a
-- label fact, a weighted relay and a provenance guarantee of `P` survive
-- an interrupt whose handler carries no counted / chain label.
-- No `postulate`, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Level using (Level)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Nat.Properties using (+-mono-≤; +-monoˡ-≤; m≤m+n; ≤-trans; ≤-reflexive; +-assoc; +-identityʳ)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Process_Trees

module CSP.Laws.DivFree.TraceInterrupt {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open import CSP.Operators E-≟ using (_△_)
open import Semantics.LTS {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import CSP.Laws.Traces.TraceLawsThrowInterrupt E-≟
  using (△τR; △τP; △τQ; △τQret; △τ⊓P; △τ⊓Q; △-τ-elim; △evR; △evP; △evQ; △evPQ; △-ev-elim)
open import CSP.Laws.DivFree.ReachInterrupt E-≟ using (Both△; Both△-τ-elim)
open import CSP.Laws.DivFree.Count E-≟ using (labels; labels-++; AllL; []; _∷_; AllL-++; AllT; Σc; Σc-++)
open import CSP.Laws.DivFree.Prov E-≟ using (Prov; Prov-++; PA; pa; runA)
open import Data.Unit using (tt)
open import Function using (case_of_)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- a run of the interrupt, split: a run of the body, then a run of the handler
△Split : PTree E (ExtI E) R → PTree E (ExtI E) R → List (Event√ R) → Set _
△Split P Q s = Σ[ s₁ ∈ List (Event√ _) ] Σ[ s₂ ∈ List (Event√ _) ] Σ[ P′ ∈ PTree E (ExtI E) _ ] Σ[ Q′ ∈ PTree E (ExtI E) _ ]
                 (s ≡ s₁ ++ s₂) × (P ⟹⟨ s₁ ⟩ P′) × (Q ⟹⟨ s₂ ⟩ Q′)

-- the split of every run of the interrupt
△-trace-elim : {P Q W : PTree E (ExtI E) R} {s : List (Event√ R)} → (P △ Q) ⟹⟨ s ⟩ W → △Split P Q s
-- … of a run out of the both-offer node, after the shared event
both-elim : {P Q P₁ Q₁ W : PTree E (ExtI E) R} {s : List (Event√ R)} {e : Event√ R}
          → P ─[ ev e ]─► P₁ → Q ─[ ev e ]─► Q₁ → Both△ P₁ Q Q₁ ⟹⟨ s ⟩ W → △Split P Q (e ∷ s)

△-trace-elim {P = P} {Q} ⟹-refl = [] , [] , P , Q , refl , ⟹-refl , ⟹-refl
△-trace-elim {P = P} {Q} (⟹-τ st r) with △-τ-elim P Q st
... | △τP stP with △-trace-elim r
...   | s₁ , s₂ , P′ , Q′ , eq , tP , tQ = s₁ , s₂ , P′ , Q′ , eq , ⟹-τ stP tP , tQ
△-trace-elim {P = P} {Q} (⟹-τ st r) | △τQ stQ with △-trace-elim r
...   | s₁ , s₂ , P′ , Q′ , eq , tP , tQ = s₁ , s₂ , P′ , Q′ , eq , tP , ⟹-τ stQ tQ
△-trace-elim {P = P} {Q} (⟹-τ st r) | △τQret _ = [] , _ , P , _ , refl , ⟹-refl , r
△-trace-elim {P = P} {Q} (⟹-τ st r) | △τ⊓P _   = _ , [] , _ , Q , sym (++-[] _) , r , ⟹-refl
  where
    -- appending nothing
    ++-[] : ∀ {A : Set _} (xs : List A) → xs ++ [] ≡ xs
    ++-[] []       = refl
    ++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)
△-trace-elim {P = P} {Q} (⟹-τ st r) | △τ⊓Q _   = [] , _ , P , _ , refl , ⟹-refl , r
△-trace-elim {P = P} {Q} (⟹-ev st r) with △-ev-elim P Q st
... | △evP stP with △-trace-elim r
...   | s₁ , s₂ , P′ , Q′ , eq , tP , tQ = _ ∷ s₁ , s₂ , P′ , Q′ , cong (_ ∷_) eq , ⟹-ev stP tP , tQ
△-trace-elim {P = P} {Q} (⟹-ev st r) | △evQ stQ      = [] , _ , P , _ , refl , ⟹-refl , ⟹-ev stQ r
△-trace-elim {P = P} {Q} (⟹-ev st r) | △evPQ stP stQ = both-elim stP stQ r

both-elim {P = P} {Q} {P₁} stP stQ ⟹-refl = _ ∷ [] , [] , P₁ , Q , refl , ⟹-ev stP ⟹-refl , ⟹-refl
both-elim {P = P} stP stQ (⟹-τ st r) with Both△-τ-elim st
... | inj₁ refl with △-trace-elim r
...   | s₁ , s₂ , P′ , Q′ , eq , tP , tQ = _ ∷ s₁ , s₂ , P′ , Q′ , cong (_ ∷_) eq , ⟹-ev stP tP , tQ
both-elim {P = P} stP stQ (⟹-τ st r) | inj₂ refl = [] , _ , P , _ , refl , ⟹-refl , ⟹-ev stQ r
both-elim stP stQ (⟹-ev (sRet ()) r)
both-elim stP stQ (⟹-ev (sVis refl ()) r)

-- a label fact of body and handler holds of the interrupt
AllT-△ : ∀ {P Q : PTree E (ExtI E) R} {F : Event → Set} → AllT F P → AllT F Q → AllT F (P △ Q)
AllT-△ aP aQ tr with △-trace-elim tr
... | s₁ , s₂ , _ , _ , refl , tP , tQ = subst (AllL _) (sym (labels-++ s₁ s₂)) (AllL-++ (aP tP) (aQ tQ))

-- a weight the handler never carries
Σc-inert : ∀ {c : Event → ℕ} {ls} → AllL (λ e → c e ≡ 0) ls → Σc c ls ≡ 0
Σc-inert []       = refl
Σc-inert {c = c} {e ∷ ls} (z ∷ zs) = trans (cong (_+ Σc c ls) z) (Σc-inert zs)

-- a relay of the body survives an interrupt whose handler carries none of the counted weight `c`
Rl-△inert : ∀ {P Q : PTree E (ExtI E) R} {c d : Event → ℕ} {k}
          → (∀ {s W} → P ⟹⟨ s ⟩ W → Σc c (labels s) ≤ Σc d (labels s) + k)
          → AllT (λ e → c e ≡ 0) Q
          → ∀ {s W} → (P △ Q) ⟹⟨ s ⟩ W → Σc c (labels s) ≤ Σc d (labels s) + k
Rl-△inert {c = c} {d} {k} hP zQ tr with △-trace-elim tr
... | s₁ , s₂ , _ , _ , refl , tP , tQ
  rewrite labels-++ s₁ s₂ | Σc-++ c (labels s₁) (labels s₂) | Σc-++ d (labels s₁) (labels s₂) | Σc-inert {c = c} (zQ tQ) =
  ≤-trans (≤-reflexive (+-identityʳ _)) (≤-trans (hP tP) (+-monoˡ-≤ k (m≤m+n _ _)))

-- a handler with no chain label adds nothing to provenance
Prov-inert : ∀ {V : Set} {O Kp In : Event → V → Set} {K : V → Set} {ls} → AllL (λ e → ∀ {x} → O e x → ⊥) ls → Prov O Kp In K ls
Prov-inert []       = tt
Prov-inert (n ∷ ns) = (λ o → ⊥-elim (n o)) , Prov-inert ns

-- a provenance guarantee of the body survives an interrupt whose handler has no chain label
PA-△inert : ∀ {V : Set} {O Kp In : Event → V → Set} {P Q : PTree E (ExtI E) R}
          → PA O Kp In P → AllT (λ e → ∀ {x} → O e x → ⊥) Q → PA O Kp In (P △ Q)
PA-△inert pP nQ = pa λ tr → case △-trace-elim tr of λ where
  (s₁ , s₂ , _ , _ , refl , tP , tQ) →
    subst (Prov _ _ _ _) (sym (labels-++ s₁ s₂)) (Prov-++ (labels s₁) (runA pP tP) (Prov-inert (nQ tQ)))
