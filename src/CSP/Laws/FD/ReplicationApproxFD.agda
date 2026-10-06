{-# OPTIONS --guardedness #-}

-- Rep runs reduce to runs of FINITE approximants, keeping the END STATE, for UNIFORM
-- replication `RepC P k Y = Rep⦀ (λ _ → P) k Y` (the FD twin of
-- CSP/Laws/Traces/ReplicationApprox.agda's `Rep-run-approx`, whose recursion is restated,
-- not edited).
--
--   * `Rep-reach-approx` : a Rep run along s is an `Approx` run along s, and `RepEnd` says
--     where the Rep run stopped: at a Rep state whose running copies ARE the approximant's
--     end (`atRep`), or at a same-event collision node (`atBoth`), whose running-copy branch
--     is the approximant's end and whose fresh-copy branch `Q ⦀ P′` ends a second
--     approximant run (with one more copy).
--   * `Rep-no-√-trace` : a Rep run never ticks.
--   * `Rep-fail-approx` : a failure never ends at a collision node (it has τ-branches), so the
--     approximant's end and the pristine copy P are both inert (`RepC-Refuses-elim`).
--   * `Rep-reach-div` / `Rep-div-approx` : a divergence ends at a Rep state or at a collision
--     node (split by `repBoth-Diverges→`); at a Rep state `Rep-Diverges→` gives an approximant
--     divergence or a τ of P.  In the τ-of-P case only the divergence PREFIX is a trace of the
--     approximant, so that disjunct is stated over the prefix.
-- POSTULATES USED: `Par-Diverges→` only (through `Rep-Diverges→`); everything else is constructive.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.FD.ReplicationApproxFD {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) {ℓr : Level} where

open import CSP.Operators E-≟
open import Semantics.LTS {E = E} {I = ExtI E}
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (IsDivergence; divergences)
open import Semantics.Stability {E = E} {I = ExtI E} using (stable-no-τ)
open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Par-τ-R)
open import CSP.Laws.Traces.TraceLawsParallelMono E-≟ using (Par-soloR-reach)
open import CSP.Laws.Traces.ReplicationSteps E-≟
  using (repBoth; Rep-τ-elim; τRun; τFresh; Rep-ev-elim; evRun; evFresh; evBoth; Rep-no-√;
         repBoth-no-ev; repBoth-τ-elim; repBoth-τ0)
open import CSP.Laws.Traces.ReplicationApprox E-≟ using (Approx; Approx-lift; IsEvl; isEvl; ⟹-++)
open import CSP.Laws.FD.ReplicationDivergence E-≟ {ℓr} using (RepC; Rep-Diverges→; repBoth-Diverges→)
open import CSP.Laws.FD.ReplicationRefusals E-≟ {ℓr} using (vis; Inert; RepC-Refuses-elim)

private
  -- the process type of this module
  T : Set _
  T = PTree E (ExtI E) (⊤ {ℓr})

  -- traces of this module
  L : Set _
  L = List (Event√ (⊤ {ℓr}))

  -- the ⊤-merge of `Rep⦀` / `_⦀_`
  tm : ⊤ {ℓr} → ⊤ {ℓr} → ⊤ {ℓr}
  tm _ _ = tt

-- the uniform copy family: every copy is P
AP : PTree E (ExtI E) (⊤ {ℓr}) → ℕ → PTree E (ExtI E) (⊤ {ℓr})
AP P _ = P

module _ (P : PTree E (ExtI E) (⊤ {ℓr})) where

  -- where a Rep run from `RepC P k Y` along s ended, read against the approximant's end Z
  data RepEnd (k : ℕ) (Y : T) (s : L) : T → T → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
    -- at a Rep state: its running copies are the approximant's end
    atRep  : ∀ {k′ Z} → RepEnd k Y s (RepC P k′ Z) Z
    -- at a collision node: Z is its running-copy branch; its fresh-copy branch `Q ⦀ P′`
    -- ends another approximant run along s
    atBoth : ∀ {k′ Q Z P′} (n′ : ℕ) → Approx (AP P) k n′ Y ⟹⟨ s ⟩ (Q ⦀ P′)
           → RepEnd k Y s (repBoth tm (AP P) k′ Q Z P′) Z

  -- an approximant reading of a Rep run ending at M: n copies, the end Z, and where M is
  Reach : ℕ → T → L → T → Set _
  Reach k Y s M = Σ[ n ∈ ℕ ] Σ[ Z ∈ T ] (Approx (AP P) k n Y ⟹⟨ s ⟩ Z) × RepEnd k Y s M Z

  private
    -- approximant runs from a successor state, read back as runs from its predecessor
    Back : ℕ → T → L → ℕ → T → L → Set _
    Back k₀ Y₀ s₀ k₁ Y₁ s₁ = ∀ m {W} → Approx (AP P) k₁ m Y₁ ⟹⟨ s₁ ⟩ W
                           → Σ[ m′ ∈ ℕ ] Approx (AP P) k₀ m′ Y₀ ⟹⟨ s₀ ⟩ W

    -- a reading from the successor is one from the predecessor (both runs are read back)
    back : ∀ {k₀ Y₀ s₀ k₁ Y₁ s₁ M} → Back k₀ Y₀ s₀ k₁ Y₁ s₁ → Reach k₁ Y₁ s₁ M → Reach k₀ Y₀ s₀ M
    back f (n , Z , r , atRep)       = proj₁ (f n r) , Z , proj₂ (f n r) , atRep
    back f (n , Z , r , atBoth m r₂) = proj₁ (f n r) , Z , proj₂ (f n r) , atBoth (proj₁ (f m r₂)) (proj₂ (f m r₂))

    -- a √-free step of the running copies X ⟹ X′: same copy count
    same : (k : ℕ) {X X′ : T} {l s : L} → All IsEvl l → X ⟹⟨ l ⟩ X′ → Back k X (l ++ s) k X′ s
    same k ok r₀ m r = m , ⟹-++ (Approx-lift (AP P) k m ok r₀) r

    -- a √-free step of the fresh copy (X ⦀ P ⟹ X ⦀ P′): one more copy
    more : (k : ℕ) {X P′ : T} {l s : L} → All IsEvl l → (X ⦀ P) ⟹⟨ l ⟩ (X ⦀ P′)
         → Back k X (l ++ s) (suc k) (X ⦀ P′) s
    more k ok r₀ m r = suc m , ⟹-++ (Approx-lift (AP P) (suc k) m ok r₀) r

  -- every Rep run is an approximant run along the same trace, remembering where it ended
  Rep-reach-approx : (k : ℕ) (Y : T) {s : L} {M : T} → RepC P k Y ⟹⟨ s ⟩ M → Reach k Y s M

  -- the same from the collision node of an event e taken by both Y (to Y′) and P (to P′)
  repBoth-reach-approx : (k : ℕ) (Y Y′ P′ : T) {X : Set ℓ} {e : E X} {a : X} {s : L} {M : T}
                       → Y ─[ ev (evl (evLabel X e a)) ]─► Y′ → P ─[ ev (evl (evLabel X e a)) ]─► P′
                       → repBoth tm (AP P) k Y Y′ P′ ⟹⟨ s ⟩ M → Reach k Y (evl (evLabel X e a) ∷ s) M

  Rep-reach-approx k Y ⟹-refl = zero , Y , ⟹-refl , atRep
  Rep-reach-approx k Y (⟹-τ st rest) with Rep-τ-elim tm (AP P) k Y st
  ... | τRun Yτ   = back (same k [] (⟹-τ Yτ ⟹-refl)) (Rep-reach-approx k _ rest)
  ... | τFresh Pτ = back (more k [] (⟹-τ (Par-τ-R ∅ES tm Y P Pτ) ⟹-refl)) (Rep-reach-approx (suc k) _ rest)
  Rep-reach-approx k Y (⟹-ev {e = √ _} st rest) = ⊥-elim (Rep-no-√ tm (AP P) k Y st)
  Rep-reach-approx k Y (⟹-ev {e = evl x} st rest) with Rep-ev-elim tm (AP P) k Y st
  ... | evRun Yev _   = back (same k (isEvl x ∷ []) (⟹-ev Yev ⟹-refl)) (Rep-reach-approx k _ rest)
  ... | evFresh Pev _ = back (more k (isEvl x ∷ []) (Par-soloR-reach ∅ES tm Y P (λ z → z) Pev ⟹-refl))
                             (Rep-reach-approx (suc k) _ rest)
  ... | evBoth Yev Pev = repBoth-reach-approx k Y _ _ Yev Pev rest

  repBoth-reach-approx k Y Y′ P′ Yev Pev ⟹-refl =
    zero , Y′ , ⟹-ev Yev ⟹-refl , atBoth 1 (Par-soloR-reach ∅ES tm Y P (λ z → z) Pev ⟹-refl)
  repBoth-reach-approx k Y Y′ P′ Yev Pev (⟹-ev st rest) = ⊥-elim (repBoth-no-ev tm (AP P) k Y Y′ P′ st)
  repBoth-reach-approx k Y Y′ P′ Yev Pev (⟹-τ st rest) with repBoth-τ-elim tm (AP P) k Y Y′ P′ st
  ... | inj₁ refl = back (same k (isEvl _ ∷ []) (⟹-ev Yev ⟹-refl)) (Rep-reach-approx k Y′ rest)
  ... | inj₂ refl = back (more k (isEvl _ ∷ []) (Par-soloR-reach ∅ES tm Y P (λ z → z) Pev ⟹-refl))
                         (Rep-reach-approx (suc k) (Y ⦀ P′) rest)

  -- a Rep run never ticks
  Rep-no-√-trace : (k : ℕ) (Y : T) {s : L} {M : T} → RepC P k Y ⟹⟨ s ⟩ M → All IsEvl s

  -- … nor does a run from a collision node
  repBoth-no-√-trace : (k : ℕ) (Y Y′ P′ : T) {s : L} {M : T}
                     → repBoth tm (AP P) k Y Y′ P′ ⟹⟨ s ⟩ M → All IsEvl s

  Rep-no-√-trace k Y ⟹-refl = []
  Rep-no-√-trace k Y (⟹-τ st rest) with Rep-τ-elim tm (AP P) k Y st
  ... | τRun _   = Rep-no-√-trace k _ rest
  ... | τFresh _ = Rep-no-√-trace (suc k) _ rest
  Rep-no-√-trace k Y (⟹-ev {e = √ _} st rest) = ⊥-elim (Rep-no-√ tm (AP P) k Y st)
  Rep-no-√-trace k Y (⟹-ev {e = evl x} st rest) with Rep-ev-elim tm (AP P) k Y st
  ... | evRun _ _   = isEvl x ∷ Rep-no-√-trace k _ rest
  ... | evFresh _ _ = isEvl x ∷ Rep-no-√-trace (suc k) _ rest
  ... | evBoth _ _  = isEvl x ∷ repBoth-no-√-trace k Y _ _ rest

  repBoth-no-√-trace k Y Y′ P′ ⟹-refl = []
  repBoth-no-√-trace k Y Y′ P′ (⟹-ev st rest) = ⊥-elim (repBoth-no-ev tm (AP P) k Y Y′ P′ st)
  repBoth-no-√-trace k Y Y′ P′ (⟹-τ st rest) with repBoth-τ-elim tm (AP P) k Y Y′ P′ st
  ... | inj₁ refl = Rep-no-√-trace k Y′ rest
  ... | inj₂ refl = Rep-no-√-trace (suc k) (Y ⦀ P′) rest

  -- a RepC failure is an approximant run whose end, and the pristine copy P, are inert on B
  Rep-fail-approx : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} (k : ℕ) (Y : T) {s : L}
                  → failures (RepC P k Y) s B
                  → Σ[ n ∈ ℕ ] Σ[ Z ∈ T ] (Approx (AP P) k n Y ⟹⟨ s ⟩ Z) × Inert Z (vis B) × Inert P (vis B)
  Rep-fail-approx k Y (_ , run , ref) with Rep-reach-approx k Y run
  ... | n , Z , r , atRep {k′} = n , Z , r , RepC-Refuses-elim P k′ Z ref
  ... | n , Z , r , atBoth {k′} {Q} {_} {P′} _ _ =
    ⊥-elim (stable-no-τ (proj₁ ref) (repBoth-τ0 tm (AP P) k′ Q Z P′))

  -- a divergent end of a Rep run: an approximant run along s whose end diverges, or a τ of P
  Rep-reach-div : (k : ℕ) (Y : T) {s : L} {M : T} → RepC P k Y ⟹⟨ s ⟩ M → Diverges M
                → Σ[ n ∈ ℕ ] Σ[ Z ∈ T ] (Approx (AP P) k n Y ⟹⟨ s ⟩ Z)
                    × (Diverges Z ⊎ Σ[ P′ ∈ T ] (P ─[ τ ]─► P′))
  Rep-reach-div k Y run d with Rep-reach-approx k Y run
  ... | n , Z , r , atRep {k′} = n , Z , r , Rep-Diverges→ P k′ Z d
  ... | n , Z , r , atBoth {k′} {Q} {_} {P′} n′ r₂ with repBoth-Diverges→ P k′ Q Z P′ d
  ...   | inj₁ d′ = n , Z , r , Rep-Diverges→ P k′ Z d′
  ...   | inj₂ d′ = n′ , (Q ⦀ P′) , r₂ , Rep-Diverges→ P (suc k′) (Q ⦀ P′) d′

  -- a RepC divergence is an approximant divergence, or a τ of P after a trace (the prefix) of it
  Rep-div-approx : (k : ℕ) (Y : T) {s : L} → divergences (RepC P k Y) s
                 → Σ[ n ∈ ℕ ] (divergences (Approx (AP P) k n Y) s
                               ⊎ (Σ[ s₀ ∈ L ] Σ[ s₁ ∈ L ] (s ≡ s₀ ++ s₁) × traces (Approx (AP P) k n Y) s₀
                                    × Σ[ P′ ∈ T ] (P ─[ τ ]─► P′)))
  Rep-div-approx k Y d with Rep-reach-div k Y (IsDivergence.reach d) (IsDivergence.divwit d)
  ... | n , Z , r , inj₁ dZ = n , inj₁ (record
          { prefix = IsDivergence.prefix d ; suffix = IsDivergence.suffix d ; split = IsDivergence.split d
          ; witness = Z ; reach = r ; divwit = dZ })
  ... | n , Z , r , inj₂ Pτ =
    n , inj₂ (IsDivergence.prefix d , IsDivergence.suffix d , IsDivergence.split d , (Z , r) , Pτ)
