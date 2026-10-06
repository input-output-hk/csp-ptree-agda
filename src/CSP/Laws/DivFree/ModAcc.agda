{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Modulo-H accessibility: the divergence-freedom calculus generalised from
-- τ-steps to "τ or a step on an event of H" (the steps that become τ once H
-- is hidden).
--
--   * `ModAStep` / `DivModA` / `div∖→modA` — DEFINITIONAL COPIES of the
--     postulate-free definitions in `CSP.Laws.Bisim.DRCongruence` (§1 there).
--     Copied, not imported: that module also postulates `modA-transfer` and
--     imports `Par-Diverges→`, and both would enter every closure below.
--   * `MAcc H t` — inductive accessibility of `ModAStep H` (same shape as
--     `HideDivergence.MAcc`, again copied to keep that module's König
--     postulate out).  `MAcc ∅ES` is `τ-Acc`.
--   * `MAccR H P` — `MAcc H` at every √-free reachable state of `P` (the
--     `τ-AccReach` of `Semantics.DivergenceFree`, generalised to H).
--
-- No `postulate`, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; ¬_; yes; no; _×-dec_; _⊎-dec_; ¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.DivFree.ModAcc {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.Deadlock {E = E} {I = ExtI E} using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Semantics.DivergenceFree {E = E} {I = ExtI E}
  using (Diverges; τ-Acc; acc; τ-Acc→¬Div; τ-AccReach; deadlock-no-τ)
open import CSP.Laws.Traces.TraceLawsHide E-≟
  using (Hide-τ-elim; hτP; hτH)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟ using (deadlock-no-ev)

private
  variable
    ℓr : Level
    R  : Set ℓr

------------------------------------------------------------------------
-- §1. Event-set algebra used by the calculus
------------------------------------------------------------------------

-- union of two event sets
_∪H_ : EventSet → EventSet → EventSet
(A ∪H B) .mem at a = A .mem at a ⊎ B .mem at a
(A ∪H B) .dec at a = A .dec at a ⊎-dec B .dec at a

-- H minus A: the H-events a component performs ALONE (outside the sync set A)
_−H_ : EventSet → EventSet → EventSet
(H −H A) .mem at a = H .mem at a × ¬ A .mem at a
(H −H A) .dec at a = H .dec at a ×-dec ¬? (A .dec at a)

-- event-set inclusion
_⊆H_ : EventSet → EventSet → Set (lsuc ℓ ⊔ ℓe)
A ⊆H B = ∀ at a → A .mem at a → B .mem at a

------------------------------------------------------------------------
-- §2. The modulo-H step, its infinite paths, and the hiding bridge
--     (definitional copies of DRCongruence §1, see the header)
------------------------------------------------------------------------

-- a modulo-H step of t: a τ, or a visible step on an event of H
data ModAStep {ℓr} {R : Set ℓr} (A : EventSet)
              (t : PTree E (ExtI E) R) (t′ : PTree E (ExtI E) R)
     : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  maτ : t ─[ τ ]─► t′ → ModAStep A t t′
  maE : {B : Set ℓ} {e : E B} {a : B} → A .mem (B , e) a
      → t ─[ ev (evl (evLabel B e a)) ]─► t′ → ModAStep A t t′

-- an infinite modulo-H path
record DivModA {ℓr} {R : Set ℓr} (A : EventSet) (t : PTree E (ExtI E) R)
     : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  coinductive
  field
    {maNext} : PTree E (ExtI E) R
    maStep   : ModAStep A t maNext
    maRest   : DivModA A maNext
open DivModA public

-- one τ of `P ∖ A`, decoded as a modulo-A step of P (Σ-packaged for copatterns)
hide-τ-step-Σ : (A : EventSet) (P : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
              → (P ∖ A) ─[ τ ]─► M
              → Σ[ P′ ∈ PTree E (ExtI E) R ] (ModAStep A P P′ × (P′ ∖ A ≡ M))
hide-τ-step-Σ A P step with Hide-τ-elim A P step
... | hτP P′ Pτ teq       = P′ , maτ Pτ , sym teq
... | hτH P′ mem Pev teq  = P′ , maE mem Pev , sym teq

-- a divergence of `P ∖ A` is an infinite modulo-A path of P
div∖→modA : (A : EventSet) (P : PTree E (ExtI E) R)
          → Diverges (P ∖ A) → DivModA A P
div∖→modA A P d .maNext = proj₁ (hide-τ-step-Σ A P (d .Diverges.step))
div∖→modA A P d .maStep = proj₁ (proj₂ (hide-τ-step-Σ A P (d .Diverges.step)))
div∖→modA A P d .maRest =
  div∖→modA A _
    (subst Diverges (sym (proj₂ (proj₂ (hide-τ-step-Σ A P (d .Diverges.step)))))
           (d .Diverges.rest))

------------------------------------------------------------------------
-- §3. Modulo-H accessibility
------------------------------------------------------------------------

-- every modulo-H successor is again accessible (inductive, so it REDUCES)
data MAcc {ℓr} {R : Set ℓr} (H : EventSet) (t : PTree E (ExtI E) R)
     : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  macc : (∀ {t′} → ModAStep H t t′ → MAcc H t′) → MAcc H t

-- the accessor
maccSub : {H : EventSet} {t t′ : PTree E (ExtI E) R}
        → MAcc H t → ModAStep H t t′ → MAcc H t′
maccSub (macc f) st = f st

-- fewer counted events ⇒ fewer steps ⇒ still accessible
MAcc-mono : {H H′ : EventSet} {t : PTree E (ExtI E) R}
          → H′ ⊆H H → MAcc H t → MAcc H′ t
MAcc-mono sub (macc f) = macc λ where
  (maτ st)      → MAcc-mono sub (f (maτ st))
  (maE {B} {e} {a} m st) → MAcc-mono sub (f (maE (sub (B , e) a m) st))

-- the τ-steps are among the modulo-H steps, so MAcc H gives τ-Acc
MAcc→τ-Acc : {H : EventSet} {t : PTree E (ExtI E) R} → MAcc H t → τ-Acc t
MAcc→τ-Acc (macc f) = acc λ st → MAcc→τ-Acc (f (maτ st))

-- … and conversely τ-Acc is MAcc of the empty set (no ∅ES-event exists)
τ-Acc→MAcc∅ : {t : PTree E (ExtI E) R} → τ-Acc t → MAcc ∅ES t
τ-Acc→MAcc∅ (acc f) = macc λ where
  (maτ st)   → τ-Acc→MAcc∅ (f st)
  (maE () _)

-- MAcc H at every √-free reachable state
MAccR : ∀ {ℓr} {R : Set ℓr} → EventSet → PTree E (ExtI E) R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
MAccR {R = R} H P = ∀ {s : List Event} {Q : PTree E (ExtI E) R} → P ⟹∖√⟨ s ⟩ Q → MAcc H Q

-- reachability-closed accessibility, weakened along ⊆H
MAccR-mono : {H H′ : EventSet} {P : PTree E (ExtI E) R}
           → H′ ⊆H H → MAccR H P → MAccR H′ P
MAccR-mono sub ar r = MAcc-mono sub (ar r)

-- reachability-closed MAcc gives the repo's `τ-AccReach`
MAccR→τ-AccReach : {H : EventSet} {P : PTree E (ExtI E) R} → MAccR H P → τ-AccReach P
MAccR→τ-AccReach ar r = MAcc→τ-Acc (ar r)

-- … and `τ-AccReach` is `MAccR ∅ES`
τ-AccReach→MAccR∅ : {P : PTree E (ExtI E) R} → τ-AccReach P → MAccR ∅ES P
τ-AccReach→MAccR∅ ar r = τ-Acc→MAcc∅ (ar r)

-- a run out of `deadlock` cannot reach a diverging state
deadlock-run-¬Div : ∀ {s} {W : PTree E (ExtI E) R} → deadlock ⟹⟨ s ⟩ W → ¬ Diverges W
deadlock-run-¬Div ⟹-refl      d = deadlock-no-τ (d .Diverges.step)
deadlock-run-¬Div (⟹-τ st _)  _ = deadlock-no-τ st
deadlock-run-¬Div (⟹-ev st _) _ = ⊥-elim (deadlock-no-ev st)

-- THE PREMISE-(b) DISCHARGER: τ-accessibility at every √-free reachable state
-- rules out divergence at every (√-inclusive) reachable state — a √ lands on
-- `deadlock`, which cannot move at all
τ-AccReach→noDiv : {P : PTree E (ExtI E) R} → τ-AccReach P
                 → ∀ {s Q} → P ⟹⟨ s ⟩ Q → ¬ Diverges Q
τ-AccReach→noDiv ar ⟹-refl = τ-Acc→¬Div (ar ∖√-refl)
τ-AccReach→noDiv ar (⟹-τ st r) = τ-AccReach→noDiv (λ r′ → ar (∖√-τ st r′)) r
τ-AccReach→noDiv ar (⟹-ev {e = evl e} st r) = τ-AccReach→noDiv (λ r′ → ar (∖√-ev st r′)) r
τ-AccReach→noDiv ar (⟹-ev {e = √ x} (sRet _) r) = deadlock-run-¬Div r
