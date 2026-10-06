{-# OPTIONS --guardedness #-}

-- Trace approximation for native replication (CSP.Replication), interleaving instance:
-- every trace of `Rep⦀ P k Q` is a trace of a FINITE approximant `Approx P k n Q`, which
-- starts the copies P k … P (k+n-1) eagerly, nested exactly as `Rep` nests them
-- (`Q ⦀ P k`, then `(Q ⦀ P k) ⦀ P (suc k)`, …).  The witness `n` counts the spawns on
-- the run.  Every `Rep` run is √-free (`Rep-no-√`, `repBoth-no-ev`), which is what lets a
-- run of the running copies be lifted through the eagerly started ones (`Approx-lift`).
--
-- The lift re-uses `Par-soloL-reach`/`Par-soloR-reach` (the endpoint-preserving building
-- blocks of `Par-trace-intro`, CSP/Laws/Traces/TraceLawsParallelMono.agda): the endpoint
-- matters here, and `Par-trace-intro` only returns `traces`.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; Σ-syntax)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.Traces.ReplicationApprox {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open import CSP.Operators E-≟
open import CSP.Replication E-≟
open import Semantics.LTS {E = E} {I = ExtI E}
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)
open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Par-τ-L; Par-τ-R)
open import CSP.Laws.Traces.TraceLawsParallelMono E-≟ using (Par-soloL-reach; Par-soloR-reach)
open import CSP.Laws.Traces.ReplicationSteps E-≟

private
  variable
    ℓr : Level

  -- the ⊤-merge of `Rep⦀` / `_⦀_`
  tm : ⊤ {ℓr} → ⊤ {ℓr} → ⊤ {ℓr}
  tm _ _ = tt

-- run append; restated locally (not imported from Semantics.LTL.Refinement) to keep this module's closure postulate-free (Semantics/LTL/Traces_Based.agda:435,731)
⟹-++ : ∀ {R : Set ℓr} {p q r : PTree E (ExtI E) R} {s₁ s₂ : List (Event√ R)}
     → p ⟹⟨ s₁ ⟩ q → q ⟹⟨ s₂ ⟩ r → p ⟹⟨ s₁ ++ s₂ ⟩ r
⟹-++ ⟹-refl        g = g
⟹-++ (⟹-τ st f)    g = ⟹-τ st (⟹-++ f g)
⟹-++ (⟹-ev st f)   g = ⟹-ev st (⟹-++ f g)

-- the n-copy approximant of `Rep⦀ P k Q`: start P k … P (k+n-1) eagerly, nested exactly as Rep nests them
Approx : (ℕ → PTree E (ExtI E) (⊤ {ℓr})) → ℕ → ℕ → PTree E (ExtI E) (⊤ {ℓr}) → PTree E (ExtI E) (⊤ {ℓr})
Approx P k zero    Q = Q
Approx P k (suc n) Q = Approx P (suc k) n (Q ⦀ P k)

-- a trace label is visible, not a termination √
data IsEvl {R : Set ℓr} : Event√ R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  -- a visible event label
  isEvl : (x : Event) → IsEvl (evl x)

-- a √-free run of X lifts to `X ⦀ Y` with Y idle (a both-offer detours via the commit τ)
⦀-lift-L : (Y : PTree E (ExtI E) (⊤ {ℓr})) {X X′ : PTree E (ExtI E) (⊤ {ℓr})}
           {s : List (Event√ (⊤ {ℓr}))}
         → All IsEvl s → X ⟹⟨ s ⟩ X′ → (X ⦀ Y) ⟹⟨ s ⟩ (X′ ⦀ Y)
⦀-lift-L Y ok             ⟹-refl         = ⟹-refl
⦀-lift-L Y ok             (⟹-τ st rest)  = ⟹-τ (Par-τ-L ∅ES tm _ Y st) (⦀-lift-L Y ok rest)
⦀-lift-L Y (isEvl _ ∷ ok) (⟹-ev st rest) =
  Par-soloL-reach ∅ES tm _ Y (λ z → z) st (⦀-lift-L Y ok rest)

-- a √-free run of the running copies lifts through the eagerly started copies of `Approx`
Approx-lift : (P : ℕ → PTree E (ExtI E) (⊤ {ℓr})) (k n : ℕ) {X X′ : PTree E (ExtI E) (⊤ {ℓr})}
              {s : List (Event√ (⊤ {ℓr}))}
            → All IsEvl s → X ⟹⟨ s ⟩ X′ → Approx P k n X ⟹⟨ s ⟩ Approx P k n X′
Approx-lift P k zero    ok run = run
Approx-lift P k (suc n) ok run = Approx-lift P (suc k) n ok (⦀-lift-L (P k) ok run)

-- every run of `Rep⦀ P k Q` is a trace of some finite approximant (n = spawns on the run)
Rep-run-approx : (P : ℕ → PTree E (ExtI E) (⊤ {ℓr})) (k : ℕ) (Q : PTree E (ExtI E) (⊤ {ℓr}))
                 {s : List (Event√ (⊤ {ℓr}))} {M : PTree E (ExtI E) (⊤ {ℓr})}
               → Rep⦀ P k Q ⟹⟨ s ⟩ M → Σ[ n ∈ ℕ ] traces (Approx P k n Q) s

-- the run continuing from an `evBoth` collision node: either still at the node (read it
-- as the running copy's step) or τ-committed to one of the two `Rep` states
repBoth-run-approx : (P : ℕ → PTree E (ExtI E) (⊤ {ℓr})) (k : ℕ) (Q Q′ P′ : PTree E (ExtI E) (⊤ {ℓr}))
                     {X : Set ℓ} {e : E X} {a : X}
                     {s : List (Event√ (⊤ {ℓr}))} {M : PTree E (ExtI E) (⊤ {ℓr})}
                   → Q ─[ ev (evl (evLabel X e a)) ]─► Q′ → P k ─[ ev (evl (evLabel X e a)) ]─► P′
                   → repBoth tm P k Q Q′ P′ ⟹⟨ s ⟩ M
                   → Σ[ n ∈ ℕ ] traces (Approx P k n Q) (evl (evLabel X e a) ∷ s)

Rep-run-approx P k Q ⟹-refl = zero , Q , ⟹-refl
Rep-run-approx P k Q (⟹-τ st rest) with Rep-τ-elim tm P k Q st
... | τRun {Q′} Qτ with Rep-run-approx P k Q′ rest
...   | n , M , r = n , M , ⟹-++ (Approx-lift P k n [] (⟹-τ Qτ ⟹-refl)) r
Rep-run-approx P k Q (⟹-τ st rest) | τFresh {P′} Pτ with Rep-run-approx P (suc k) (Q ⦀ P′) rest
...   | n , M , r =
  suc n , M , ⟹-++ (Approx-lift P (suc k) n [] (⟹-τ (Par-τ-R ∅ES tm Q (P k) Pτ) ⟹-refl)) r
Rep-run-approx P k Q (⟹-ev {e = √ _} st rest) = ⊥-elim (Rep-no-√ tm P k Q st)
Rep-run-approx P k Q (⟹-ev {e = evl x} st rest) with Rep-ev-elim tm P k Q st
... | evRun {Q′} Qev _ with Rep-run-approx P k Q′ rest
...   | n , M , r = n , M , ⟹-++ (Approx-lift P k n (isEvl x ∷ []) (⟹-ev Qev ⟹-refl)) r
Rep-run-approx P k Q (⟹-ev {e = evl x} st rest) | evFresh {P′} Pev _
  with Rep-run-approx P (suc k) (Q ⦀ P′) rest
...   | n , M , r =
  suc n , M , ⟹-++ (Approx-lift P (suc k) n (isEvl x ∷ [])
                      (Par-soloR-reach ∅ES tm Q (P k) (λ z → z) Pev ⟹-refl)) r
Rep-run-approx P k Q (⟹-ev {e = evl x} st rest) | evBoth Qev Pev =
  repBoth-run-approx P k Q _ _ Qev Pev rest

repBoth-run-approx P k Q Q′ P′ Qev Pev ⟹-refl = zero , Q′ , ⟹-ev Qev ⟹-refl
repBoth-run-approx P k Q Q′ P′ Qev Pev (⟹-ev st rest) = ⊥-elim (repBoth-no-ev tm P k Q Q′ P′ st)
repBoth-run-approx P k Q Q′ P′ Qev Pev (⟹-τ st rest) with repBoth-τ-elim tm P k Q Q′ P′ st
... | inj₁ refl with Rep-run-approx P k Q′ rest
...   | n , M , r = n , M , ⟹-++ (Approx-lift P k n (isEvl _ ∷ []) (⟹-ev Qev ⟹-refl)) r
repBoth-run-approx P k Q Q′ P′ Qev Pev (⟹-τ st rest) | inj₂ refl
  with Rep-run-approx P (suc k) (Q ⦀ P′) rest
...   | n , M , r =
  suc n , M , ⟹-++ (Approx-lift P (suc k) n (isEvl _ ∷ [])
                      (Par-soloR-reach ∅ES tm Q (P k) (λ z → z) Pev ⟹-refl)) r

-- every trace of `Rep⦀ P k Q` is a trace of a finite approximant
Rep-traces-approx : (P : ℕ → PTree E (ExtI E) (⊤ {ℓr})) (k : ℕ) (Q : PTree E (ExtI E) (⊤ {ℓr}))
                    {s : List (Event√ (⊤ {ℓr}))}
                  → traces (Rep⦀ P k Q) s → Σ[ n ∈ ℕ ] traces (Approx P k n Q) s
Rep-traces-approx P k Q (_ , run) = Rep-run-approx P k Q run
