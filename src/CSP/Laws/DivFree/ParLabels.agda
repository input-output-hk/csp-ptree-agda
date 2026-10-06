{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Label facts through one `Par` run (Leios no-livelock, Stage L hoist).
-- Generic: no Leios/Cardano content.  Moved verbatim from Stage C's
-- `Logic2`:
--   * `subR`   — a right side wholly inside the sync set weighs at most
--                the left side
--   * `labR`   — a left side wholly inside the sync set leaves the run's
--                labels those of the right side
--   * `AllL-⦀` — a label fact of both sides holds of the run
-- No postulate, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _≤_; z≤n)
open import Data.Nat.Properties using (≤-trans; +-monoʳ-≤; m≤n+m)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Process_Trees

module CSP.Laws.DivFree.ParLabels {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open import Semantics.LTS {E = E} {I = ExtI E} using (Event; Event√)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟ using (ParInter; pnil; psync; psoloL; psoloR; p√)
open import CSP.Laws.DivFree.Count E-≟ using (Σc; labels; AllL; []; _∷_)
open import CSP.Laws.DivFree.Prov E-≟ using (InA)

-- a right side wholly inside the sync set weighs at most the left side
subR : ∀ (c : Event → ℕ) {R₁ R₂ R₀ : Set} {A merge} {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R₀)}
     → AllL (InA A) (labels sQ) → ParInter A merge sP sQ s → Σc c (labels sQ) ≤ Σc c (labels sP)
subR c al pnil                 = z≤n
subR c (_ ∷ al) (psync _ pi)   = +-monoʳ-≤ (c _) (subR c al pi)
subR c al (psoloL _ pi)        = ≤-trans (subR c al pi) (m≤n+m _ (c _))
subR c (a ∷ al) (psoloR ¬m pi) = ⊥-elim (¬m a)
subR c al p√                   = z≤n

-- labels of a parallel run whose left side lies wholly inside the sync set
labR : ∀ {R₁ R₂ R₀ : Set} {A merge} {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R₀)}
     → AllL (InA A) (labels sP) → ParInter A merge sP sQ s → labels s ≡ labels sQ
labR al pnil                 = refl
labR (_ ∷ al) (psync _ pi)   = cong (_ ∷_) (labR al pi)
labR (a ∷ al) (psoloL ¬m pi) = ⊥-elim (¬m a)
labR al (psoloR _ pi)        = cong (_ ∷_) (labR al pi)
labR al p√                   = refl

-- label facts of both sides of an interleaving
AllL-⦀ : ∀ {P : Event → Set} {R₁ R₂ R₀ : Set} {A merge} {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R₀)}
       → AllL P (labels sP) → AllL P (labels sQ) → ParInter A merge sP sQ s → AllL P (labels s)
AllL-⦀ ap aq pnil                     = []
AllL-⦀ (p ∷ ap) (_ ∷ aq) (psync _ pi) = p ∷ AllL-⦀ ap aq pi
AllL-⦀ (p ∷ ap) aq (psoloL _ pi)      = p ∷ AllL-⦀ ap aq pi
AllL-⦀ ap (q ∷ aq) (psoloR _ pi)      = q ∷ AllL-⦀ ap aq pi
AllL-⦀ ap aq p√                       = []
