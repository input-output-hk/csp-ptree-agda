{-# OPTIONS --guardedness #-}

-- Divergence of UNIFORM replication `RepC P k Y = Rep⦀ (λ _ → P) k Y` (CSP.Replication).
--
--   * `Rep-Diverges→` : the Rep König step, `Diverges (RepC P k Y) → Diverges Y ⊎ P ─τ→ _`.
--     No new postulate: a Rep divergence maps CONSTRUCTIVELY to one of `Y ⦀ τShadow P`
--     (`toShadow`: a running copy's τ is the left operand's τ; the first fresh copy's τ
--     hands over to the shadow's self-loop), and the existing König step `Par-Diverges→`
--     (CSP/Laws/FD/ParallelDivergence.agda:55) splits that.  `τShadow P` offers nothing and
--     loops by τ exactly where P has a τ-branch, so its divergence yields a τ of P.
--   * `repBoth-Diverges→` : the same-event collision node diverges ⇒ one of its two `Rep`
--     branches does (one step + `repBoth-τ-elim`, constructive).
--   * `Rep-Diverges-L` / `Approx-Diverges-L` : the running copies' divergence lifts (constructive).
--   * `Rep-Diverges-fresh` : an unguarded copy makes `RepC` diverge (`Rep-unguarded-diverges`).
-- POSTULATES USED: `Par-Diverges→` only (by `Rep-Diverges→`); everything else is constructive.

open import Level using (Level)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂)
open import Data.Product using (Σ; _,_; Σ-syntax)
open import Function using (case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

open import Process_Trees

module CSP.Laws.FD.ReplicationDivergence {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) {ℓr : Level} where
open PTree

open import CSP.Operators E-≟
open import CSP.Replication E-≟
open import Semantics.LTS {E = E} {I = ExtI E}
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟ using (viewT-τ)
open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Par-τ-L)
open import CSP.Laws.Traces.ReplicationSteps E-≟
  using (τ→viewT; repBoth; RepτR; τRun; τFresh; Rep-τ-elim; repBoth-τ-elim; Rep-τRun-intro)
open import CSP.Laws.Traces.ReplicationApprox E-≟ using (Approx)
open import CSP.Laws.DivFree.Replication E-≟ using (Rep-unguarded-diverges)
open import CSP.Laws.FD.ParallelDivergence E-≟ using (Par-Diverges→; Par-Diverges-L; Par-Diverges-R)

private
  -- the process type of this module
  T : Set _
  T = PTree E (ExtI E) (⊤ {ℓr})

  -- the ⊤-merge of `Rep⦀` / `_⦀_`
  tm : ⊤ {ℓr} → ⊤ {ℓr} → ⊤ {ℓr}
  tm _ _ = tt

-- uniform replication: every copy is P
RepC : PTree E (ExtI E) (⊤ {ℓr}) → ℕ → PTree E (ExtI E) (⊤ {ℓr}) → PTree E (ExtI E) (⊤ {ℓr})
RepC P = Rep⦀ (λ _ → P)

-------------------------------------------------------------------------------------
-- the τ-shadow
-------------------------------------------------------------------------------------

-- the τ-shadow of P: offers nothing, and loops by τ exactly where P has a τ-branch
τShadow : PTree E (ExtI E) (⊤ {ℓr}) → PTree E (ExtI E) (⊤ {ℓr})

-- a τ-branch of P becomes a τ self-loop of the shadow
τShadow-br : PTree E (ExtI E) (⊤ {ℓr}) → Maybe (PTree E (ExtI E) (⊤ {ℓr})) → Maybe (PTree E (ExtI E) (⊤ {ℓr}))

τShadow-br P (just _) = just (τShadow P)
τShadow-br P nothing  = nothing

force (τShadow P) = react ∅v (λ i a → τShadow-br P (viewT (force P) i a))

-- a divergence of the shadow starts with a τ-branch of P, i.e. P has a τ
τShadow-Diverges→ : {P : T} → Diverges (τShadow P) → Σ[ P′ ∈ T ] (P ─[ τ ]─► P′)
τShadow-Diverges→ {P} d with τ-inv (d .Diverges.step)
... | inj₁ ()
... | inj₂ (_ , _ , i , a , refl , br) with viewT (force P) i a in veq
...   | just P′ = P′ , viewT-τ refl veq
...   | nothing = case br of λ ()

-- a τ of P is a τ self-loop of the shadow
τShadow-self : {P P′ : T} → P ─[ τ ]─► P′ → τShadow P ─[ τ ]─► τShadow P
τShadow-self {P} st with τ→viewT st
... | j , b , eq = sTau {i = j} {a = b} refl (cong (τShadow-br P) eq)

-- the shadow of a τ-able P diverges by its self-loop
shadow-loop : {P P′ : T} → P ─[ τ ]─► P′ → Diverges (τShadow P)
shadow-loop {P} st .Diverges.next = τShadow P
shadow-loop st .Diverges.step = τShadow-self st
shadow-loop st .Diverges.rest = shadow-loop st

-------------------------------------------------------------------------------------
-- the Rep König step, through the shadow
-------------------------------------------------------------------------------------

-- a Rep divergence is a divergence of the running copies beside P's shadow
toShadow : (P : T) (k : ℕ) (Y : T) → Diverges (RepC P k Y) → Diverges (Y ⦀ τShadow P)

-- … one Rep τ at a time: a running τ is mirrored on the left, the first fresh τ hands over
toShadow-step : (P : T) (k : ℕ) (Y : T) {M : T}
              → RepτR tm (λ _ → P) k Y M → Diverges M → Diverges (Y ⦀ τShadow P)

toShadow P k Y d = toShadow-step P k Y (Rep-τ-elim tm (λ _ → P) k Y (d .Diverges.step)) (d .Diverges.rest)

toShadow-step P k Y (τRun {Q′} st) d .Diverges.next = Q′ ⦀ τShadow P
toShadow-step P k Y (τRun st) d .Diverges.step = Par-τ-L ∅ES tm Y (τShadow P) st
toShadow-step P k Y (τRun {Q′} st) d .Diverges.rest = toShadow P k Q′ d
toShadow-step P k Y (τFresh st) d = Par-Diverges-R ∅ES tm Y (shadow-loop st)

-- the Rep König step: the running copies diverge, or P itself has a τ
Rep-Diverges→ : (P : T) (k : ℕ) (Y : T) → Diverges (RepC P k Y) → Diverges Y ⊎ Σ[ P′ ∈ T ] (P ─[ τ ]─► P′)
Rep-Diverges→ P k Y d = map₂ τShadow-Diverges→ (Par-Diverges→ ∅ES tm (toShadow P k Y d))

-- the collision node diverges ⇒ one of its two `Rep` branches diverges
repBoth-Diverges→ : (P : T) (k : ℕ) (Q Q′ P′ : T)
                  → Diverges (repBoth tm (λ _ → P) k Q Q′ P′)
                  → Diverges (RepC P k Q′) ⊎ Diverges (RepC P (suc k) (Q ⦀ P′))
repBoth-Diverges→ P k Q Q′ P′ d with repBoth-τ-elim tm (λ _ → P) k Q Q′ P′ (d .Diverges.step)
... | inj₁ e = inj₁ (subst Diverges e (d .Diverges.rest))
... | inj₂ e = inj₂ (subst Diverges e (d .Diverges.rest))

-------------------------------------------------------------------------------------
-- divergence lifts
-------------------------------------------------------------------------------------

-- the running copies' divergence is Rep's (each τ is a `τRun`)
Rep-Diverges-L : (P : T) (k : ℕ) {Y : T} → Diverges Y → Diverges (RepC P k Y)
Rep-Diverges-L P k d .Diverges.next = RepC P k (d .Diverges.next)
Rep-Diverges-L P k {Y} d .Diverges.step = Rep-τRun-intro tm (λ _ → P) k Y (d .Diverges.step)
Rep-Diverges-L P k d .Diverges.rest = Rep-Diverges-L P k (d .Diverges.rest)

-- an unguarded copy makes uniform replication diverge (every fresh copy's τ spawns it)
Rep-Diverges-fresh : {P P′ : T} {k : ℕ} {Y : T} → P ─[ τ ]─► P′ → Diverges (RepC P k Y)
Rep-Diverges-fresh {P} {P′} {k} {Y} st = Rep-unguarded-diverges tm (λ _ → P) k Y (λ _ → P′) (λ _ → st)

-- the running copies' divergence lifts through the eagerly started copies of `Approx`
Approx-Diverges-L : (P : T) (k n : ℕ) {Y : T} → Diverges Y → Diverges (Approx (λ _ → P) k n Y)
Approx-Diverges-L P k zero    d = d
Approx-Diverges-L P k (suc n) d = Approx-Diverges-L P (suc k) n (Par-Diverges-L ∅ES tm P d)
