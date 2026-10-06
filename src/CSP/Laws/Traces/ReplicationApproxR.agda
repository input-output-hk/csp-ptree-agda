{-# OPTIONS --guardedness #-}

-- PORT of CSP.Laws.Traces.ReplicationApprox (frozen at polymorphic ⊤, built on `_⦀_`) to a
-- generic result type `R` and merge function `merge`, replacing every `_⦀_` by the generic
-- `Par ∅ES merge`.  Needed because the security layer's process type is a `PTree` over its
-- own event type and its own result type with its own `merge`, so the proof must go through
-- `Par merge`, not the frozen `_⦀_` combinator.  This restates the recursion of
-- `Rep-run-approx` / `repBoth-run-approx` / `Approx-lift` / `⦀-lift-L`
-- (ReplicationApprox.agda:54-130) at `merge` explicit -- it is NOT a reusable lemma lifted to
-- `R`, it is the same proof shape re-derived because `Rep merge` and `Par ∅ES merge` differ
-- at each instantiation of `R`/`merge`.  `IsEvl` and the run-append `⟹-++` ARE reused as-is
-- (ReplicationApprox.agda already states them for any `R`).
--
-- `ApproxR-foldL` relates the approximant to Task 1's `foldL`
-- (CSP.Laws.Traces.InterleaveFold): `ApproxR merge P k n Q` is exactly
-- `foldL Q (map P (upTo k n))`, nested the same way `Rep` nests its copies.
--
-- `Rep-trace-evl` is new here (not in ReplicationApprox): every trace of `Rep merge P k Q`
-- is √-free, by the same elim machinery (`Rep-no-√`/`repBoth-no-ev` rule out a √ at either
-- state, so only `evl` labels remain).
--
-- Postulates: none used, none in closure (a grep of this module and its imports finds no
-- `postulate`).

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; Σ-syntax)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.Traces.ReplicationApproxR {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open import CSP.Operators E-≟
open import CSP.Replication E-≟
open import Semantics.LTS {E = E} {I = ExtI E}
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)
open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Par-τ-L; Par-τ-R)
open import CSP.Laws.Traces.TraceLawsParallelMono E-≟ using (Par-soloL-reach; Par-soloR-reach)
open import CSP.Laws.Traces.ReplicationSteps E-≟
open import CSP.Laws.Traces.ReplicationApprox E-≟ using (IsEvl; isEvl; ⟹-++)

module _ {ℓr} {R : Set ℓr} (merge : R → R → R) where

  open import CSP.Laws.Traces.InterleaveFold E-≟ merge using (foldL)

  -- the process type the lemmas of this module talk about
  private
    T : Set _
    T = PTree E (ExtI E) R

  -- the index list k, suc k, …, k+n-1 that `ApproxR` spawns copies over
  upTo : ℕ → ℕ → List ℕ
  upTo k zero    = []
  upTo k (suc n) = k ∷ upTo (suc k) n

  -- the n-copy approximant of `Rep merge P k Q`: start P k … P (k+n-1) eagerly, nested
  -- exactly as Rep nests them
  ApproxR : (ℕ → T) → ℕ → ℕ → T → T
  ApproxR P k zero    Q = Q
  ApproxR P k (suc n) Q = ApproxR P (suc k) n (Par ∅ES merge Q (P k))

  -- `ApproxR` is exactly Task 1's left fold over the spawned copies' processes
  ApproxR-foldL : (P : ℕ → T) (k n : ℕ) (Q : T)
                → ApproxR P k n Q ≡ foldL Q (map P (upTo k n))
  ApproxR-foldL P k zero    Q = refl
  ApproxR-foldL P k (suc n) Q = ApproxR-foldL P (suc k) n (Par ∅ES merge Q (P k))

  -- a √-free run of X lifts to `X ∥ Y` with Y idle (a both-offer detours via the commit τ)
  Par-lift-L : (Y : T) {X X′ : T} {s : List (Event√ R)}
             → All IsEvl s → X ⟹⟨ s ⟩ X′ → (Par ∅ES merge X Y) ⟹⟨ s ⟩ (Par ∅ES merge X′ Y)
  Par-lift-L Y ok             ⟹-refl         = ⟹-refl
  Par-lift-L Y ok             (⟹-τ st rest)  = ⟹-τ (Par-τ-L ∅ES merge _ Y st) (Par-lift-L Y ok rest)
  Par-lift-L Y (isEvl _ ∷ ok) (⟹-ev st rest) =
    Par-soloL-reach ∅ES merge _ Y (λ z → z) st (Par-lift-L Y ok rest)

  -- a √-free run of the running copies lifts through the eagerly started copies of `ApproxR`
  ApproxR-lift : (P : ℕ → T) (k n : ℕ) {X X′ : T} {s : List (Event√ R)}
               → All IsEvl s → X ⟹⟨ s ⟩ X′ → ApproxR P k n X ⟹⟨ s ⟩ ApproxR P k n X′
  ApproxR-lift P k zero    ok run = run
  ApproxR-lift P k (suc n) ok run = ApproxR-lift P (suc k) n ok (Par-lift-L (P k) ok run)

  -- every run of `Rep merge P k Q` is a trace of some finite approximant (n = spawns on the run)
  Rep-run-approxR : (P : ℕ → T) (k : ℕ) (Q : T) {s : List (Event√ R)} {M : T}
                  → Rep merge P k Q ⟹⟨ s ⟩ M → Σ[ n ∈ ℕ ] traces (ApproxR P k n Q) s

  -- the run continuing from an `evBoth` collision node: either still at the node (read it
  -- as the running copy's step) or τ-committed to one of the two `Rep` states
  repBoth-run-approxR : (P : ℕ → T) (k : ℕ) (Q Q′ P′ : T)
                       {X : Set ℓ} {e : E X} {a : X} {s : List (Event√ R)} {M : T}
                     → Q ─[ ev (evl (evLabel X e a)) ]─► Q′ → P k ─[ ev (evl (evLabel X e a)) ]─► P′
                     → repBoth merge P k Q Q′ P′ ⟹⟨ s ⟩ M
                     → Σ[ n ∈ ℕ ] traces (ApproxR P k n Q) (evl (evLabel X e a) ∷ s)

  Rep-run-approxR P k Q ⟹-refl = zero , Q , ⟹-refl
  Rep-run-approxR P k Q (⟹-τ st rest) with Rep-τ-elim merge P k Q st
  ... | τRun {Q′} Qτ with Rep-run-approxR P k Q′ rest
  ...   | n , M , r = n , M , ⟹-++ (ApproxR-lift P k n [] (⟹-τ Qτ ⟹-refl)) r
  Rep-run-approxR P k Q (⟹-τ st rest) | τFresh {P′} Pτ
    with Rep-run-approxR P (suc k) (Par ∅ES merge Q P′) rest
  ...   | n , M , r =
    suc n , M , ⟹-++ (ApproxR-lift P (suc k) n [] (⟹-τ (Par-τ-R ∅ES merge Q (P k) Pτ) ⟹-refl)) r
  Rep-run-approxR P k Q (⟹-ev {e = √ _} st rest) = ⊥-elim (Rep-no-√ merge P k Q st)
  Rep-run-approxR P k Q (⟹-ev {e = evl x} st rest) with Rep-ev-elim merge P k Q st
  ... | evRun {Q′} Qev _ with Rep-run-approxR P k Q′ rest
  ...   | n , M , r = n , M , ⟹-++ (ApproxR-lift P k n (isEvl x ∷ []) (⟹-ev Qev ⟹-refl)) r
  Rep-run-approxR P k Q (⟹-ev {e = evl x} st rest) | evFresh {P′} Pev _
    with Rep-run-approxR P (suc k) (Par ∅ES merge Q P′) rest
  ...   | n , M , r =
    suc n , M , ⟹-++ (ApproxR-lift P (suc k) n (isEvl x ∷ [])
                        (Par-soloR-reach ∅ES merge Q (P k) (λ z → z) Pev ⟹-refl)) r
  Rep-run-approxR P k Q (⟹-ev {e = evl x} st rest) | evBoth Qev Pev =
    repBoth-run-approxR P k Q _ _ Qev Pev rest

  repBoth-run-approxR P k Q Q′ P′ Qev Pev ⟹-refl = zero , Q′ , ⟹-ev Qev ⟹-refl
  repBoth-run-approxR P k Q Q′ P′ Qev Pev (⟹-ev st rest) =
    ⊥-elim (repBoth-no-ev merge P k Q Q′ P′ st)
  repBoth-run-approxR P k Q Q′ P′ Qev Pev (⟹-τ st rest) with repBoth-τ-elim merge P k Q Q′ P′ st
  ... | inj₁ refl with Rep-run-approxR P k Q′ rest
  ...   | n , M , r = n , M , ⟹-++ (ApproxR-lift P k n (isEvl _ ∷ []) (⟹-ev Qev ⟹-refl)) r
  repBoth-run-approxR P k Q Q′ P′ Qev Pev (⟹-τ st rest) | inj₂ refl
    with Rep-run-approxR P (suc k) (Par ∅ES merge Q P′) rest
  ...   | n , M , r =
    suc n , M , ⟹-++ (ApproxR-lift P (suc k) n (isEvl _ ∷ [])
                        (Par-soloR-reach ∅ES merge Q (P k) (λ z → z) Pev ⟹-refl)) r

  -- every trace of `Rep merge P k Q` is a trace of a finite approximant
  Rep-traces-approxR : (P : ℕ → T) (k : ℕ) (Q : T) {s : List (Event√ R)}
                      → traces (Rep merge P k Q) s → Σ[ n ∈ ℕ ] traces (ApproxR P k n Q) s
  Rep-traces-approxR P k Q (_ , run) = Rep-run-approxR P k Q run

  -- every run of `Rep merge P k Q` is √-free (mirrors Rep-run-approxR's case split)
  Rep-run-evl : (P : ℕ → T) (k : ℕ) (Q : T) {s : List (Event√ R)} {M : T}
              → Rep merge P k Q ⟹⟨ s ⟩ M → All IsEvl s

  -- every run continuing from an `evBoth` collision node is √-free
  repBoth-run-evl : (P : ℕ → T) (k : ℕ) (Q Q′ P′ : T)
                   {X : Set ℓ} {e : E X} {a : X} {s : List (Event√ R)} {M : T}
                 → Q ─[ ev (evl (evLabel X e a)) ]─► Q′ → P k ─[ ev (evl (evLabel X e a)) ]─► P′
                 → repBoth merge P k Q Q′ P′ ⟹⟨ s ⟩ M → All IsEvl s

  Rep-run-evl P k Q ⟹-refl = []
  Rep-run-evl P k Q (⟹-τ st rest) with Rep-τ-elim merge P k Q st
  ... | τRun {Q′} _   = Rep-run-evl P k Q′ rest
  ... | τFresh {P′} _ = Rep-run-evl P (suc k) (Par ∅ES merge Q P′) rest
  Rep-run-evl P k Q (⟹-ev {e = √ _} st rest) = ⊥-elim (Rep-no-√ merge P k Q st)
  Rep-run-evl P k Q (⟹-ev {e = evl x} st rest) with Rep-ev-elim merge P k Q st
  ... | evRun {Q′} _ _   = isEvl x ∷ Rep-run-evl P k Q′ rest
  ... | evFresh {P′} _ _ = isEvl x ∷ Rep-run-evl P (suc k) (Par ∅ES merge Q P′) rest
  ... | evBoth Qev Pev   = isEvl x ∷ repBoth-run-evl P k Q _ _ Qev Pev rest

  repBoth-run-evl P k Q Q′ P′ Qev Pev ⟹-refl = []
  repBoth-run-evl P k Q Q′ P′ Qev Pev (⟹-ev st rest) =
    ⊥-elim (repBoth-no-ev merge P k Q Q′ P′ st)
  repBoth-run-evl P k Q Q′ P′ Qev Pev (⟹-τ st rest) with repBoth-τ-elim merge P k Q Q′ P′ st
  ... | inj₁ refl = Rep-run-evl P k Q′ rest
  ... | inj₂ refl = Rep-run-evl P (suc k) (Par ∅ES merge Q P′) rest

  -- every trace of `Rep merge P k Q` is √-free
  Rep-trace-evl : (P : ℕ → T) (k : ℕ) (Q : T) {s : List (Event√ R)}
                → traces (Rep merge P k Q) s → All IsEvl s
  Rep-trace-evl P k Q (_ , run) = Rep-run-evl P k Q run
