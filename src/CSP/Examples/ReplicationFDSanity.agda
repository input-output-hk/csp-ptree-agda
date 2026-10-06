{-# OPTIONS --guardedness #-}

-- Sanity checks for the replication divergence layer (CSP.Laws.FD.ReplicationDivergence).
-- Review Focus 1: with an UNGUARDED copy (initial τ) both sides of the unfold
-- `!ᶜ P ≈FD (P ⦀ !ᶜ P)` diverge at once, the `⦀`-headed side through its right operand.
-- Review Focus 2 (CSP.Laws.FD.ReplicationRefusals): a terminated copy is `Inert` though
-- not stable, and `!ᶜ Skip` (whose fresh copy is never spawned) refuses everything.
-- Review Focus 3 (CSP.Laws.FD.ReplicationCharFD): the kept pristine copy is not a process —
-- `RepC Pa1 0 Stop ⊑FD (Stop ⦀ Pa1)` is refuted by the failure (⟨a⟩, Σ) of the right side.
-- Instantiation checks (CSP.Laws.FD.ReplicationUnfold): `!ᶜ-unfold-FD` is premise-free
-- (visible in its type), so instantiating it at `Skip` (a copy that terminates at once) and
-- at `a → a → Stop` (identical copies colliding on `a`) cannot fail; they merely confirm the
-- parameterised module instantiates at a concrete event type.

open import Level using () renaming (zero to lzero)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Examples.ReplicationFDSanity where

-- two ⊤-carried events
data Ev : Set → Set where
  evA evB : Ev ⊤

-- decidable equality on the event index
Ev-≟ : (x y : AnyTypes Ev) → Dec (x ≡ y)
Ev-≟ (_ , evA) (_ , evA) = yes refl
Ev-≟ (_ , evB) (_ , evB) = yes refl
Ev-≟ (_ , evA) (_ , evB) = no λ ()
Ev-≟ (_ , evB) (_ , evA) = no λ ()

open import CSP.Operators Ev-≟
open import CSP.Replication Ev-≟
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
  using (Event√; evl; evLabel; _─[_]─►_; τ; sSil; sRet; sVis; sTau; Diverges)
open import Semantics.Refusals {E = Ev} {I = ExtI Ev} using (Refuses)
open import Semantics.Stability {E = Ev} {I = ExtI Ev} using (stable-no-τ)
open import Semantics.Failures {E = Ev} {I = ExtI Ev} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.FailuresDivergences {E = Ev} {I = ExtI Ev} using (_⊑FD_; _≈FD_)
open import CSP.Laws.Traces.TraceLawsParallelTrace Ev-≟ using (pnil; psoloR)
open import CSP.Laws.Traces.ReplicationApprox Ev-≟ using (isEvl)
open import CSP.Laws.Traces.InterleaveNest Ev-≟ using (Par-reach-intro)
open import CSP.Laws.FD.ParallelDivergence Ev-≟ using (Par-Diverges-R)
open import CSP.Laws.FD.ReplicationDivergence Ev-≟ using (RepC; Rep-Diverges-fresh)
open import CSP.Laws.FD.ReplicationRefusals Ev-≟ using (Inert; RepC-Refuses-intro; inert-no-offer; Inert-⦀-intro)
open import CSP.Laws.FD.InterleaveNestFD Ev-≟ using (Inert-vis→)
open import CSP.Laws.FD.ReplicationCharFD Ev-≟
  using (RepFailOut; RepDivOut; RepC-failures-elim; RepC-div-elim)
open import CSP.Laws.FD.ReplicationUnfold Ev-≟ using (!ᶜ-unfold-FD)

-- the process type of these checks
T : Set _
T = PTree Ev (ExtI Ev) (⊤ {lzero})

-- an unguarded copy: its first move is a τ
Pτ : T
Pτ = Tau (evA ⟶₀ Stop)

-- that first τ (`Tau` is a `sil` node)
τstep : Pτ ─[ τ ]─► (evA ⟶₀ Stop)
τstep = sSil refl

-- Review Focus 1: with an unguarded copy both `!ᶜ Pτ` and `Pτ ⦀ !ᶜ Pτ` diverge at once
unguarded-both-diverge : Diverges (!ᶜ Pτ) × Diverges (Pτ ⦀ !ᶜ Pτ)
unguarded-both-diverge = Rep-Diverges-fresh τstep , Par-Diverges-R ∅ES (λ _ _ → tt) Pτ (Rep-Diverges-fresh τstep)

-- Review Focus 2: a terminated copy is inert for every refusal set, although it is not stable
inert-skip : ∀ {ℓx} {B : Event√ (⊤ {lzero}) → Set ℓx} → Inert Skip B
inert-skip = inj₁ (tt , refl)

-- Stop is stable and offers nothing, so it refuses every set
stop-refuses-all : ∀ {ℓx} {X : _ → Set ℓx} → Refuses (Stop {R = ⊤ {lzero}}) X
stop-refuses-all = (λ _ _ → refl) , λ { _ _ (_ , sRet ()) ; _ _ (_ , sVis refl ()) }

-- `!ᶜ Skip` never spawns its `ret` fresh copy, so it refuses every set
rep-skip-refuses : Refuses (!ᶜ Skip) (λ _ → ⊤ {lzero})
rep-skip-refuses = RepC-Refuses-intro Skip 0 Stop (inj₂ stop-refuses-all) inert-skip

-- one copy: a → Stop
Pa1 : T
Pa1 = evA ⟶₀ Stop

-- the event a
aa : Event√ (⊤ {lzero})
aa = evl (evLabel ⊤ evA tt)

-- a state reached from Stop is stable (Stop never moves)
stop-reach-stable : ∀ {s} {W : T} → Stop ⟹⟨ s ⟩ W → isStable W
stop-reach-stable ⟹-refl                  = λ _ _ → refl
stop-reach-stable (⟹-τ (sSil ()) _)
stop-reach-stable (⟹-τ (sTau refl ()) _)
stop-reach-stable (⟹-ev (sRet ()) _)
stop-reach-stable (⟹-ev (sVis refl ()) _)

-- a state reached from Pa1 is stable (Pa1, or Stop after a)
pa1-reach-stable : ∀ {s} {W : T} → Pa1 ⟹⟨ s ⟩ W → isStable W
pa1-reach-stable ⟹-refl                                   = λ _ _ → refl
pa1-reach-stable (⟹-τ (sSil ()) _)
pa1-reach-stable (⟹-τ (sTau refl ()) _)
pa1-reach-stable (⟹-ev (sRet ()) _)
pa1-reach-stable (⟹-ev (sVis {at = _ , evA} refl refl) r) = stop-reach-stable r
pa1-reach-stable (⟹-ev (sVis {at = _ , evB} refl ()) _)

-- no copy end reached from Pa1 diverges
pa1-ends-converge : ∀ {cps} → All (λ c → Pa1 ⟹⟨ proj₁ c ⟩ proj₂ c) cps → ¬ Any (λ c → Diverges (proj₂ c)) cps
pa1-ends-converge (r ∷ _)  (here d)  = stable-no-τ (pa1-reach-stable r) (Diverges.step d)
pa1-ends-converge (_ ∷ rs) (there a) = pa1-ends-converge rs a

-- the right side refuses everything after ⟨a⟩: Stop ⦀ Stop is inert
rhs-failure : failures (Stop ⦀ Pa1) (aa ∷ []) (λ _ → ⊤ {lzero})
rhs-failure with Inert-vis→ {B = λ _ → ⊤ {lzero}} (Stop ⦀ Stop)
                   (Inert-⦀-intro Stop Stop (inj₂ stop-refuses-all) (inj₂ stop-refuses-all))
... | inj₁ (_ , ())
... | inj₂ ref = Stop ⦀ Stop
               , Par-reach-intro ∅ES (λ _ _ → tt) Stop Pa1 ⟹-refl (⟹-ev (sVis refl refl) ⟹-refl)
                   (psoloR (λ z → z) pnil) (isEvl _ ∷ [])
               , ref

-- Review Focus 3: the kept pristine copy is NOT a process — after ⟨a⟩, `Stop ⦀ Pa1` refuses `a`
-- but `RepC Pa1 0 Stop` does not (a fresh copy still offers it), so this refinement fails
pristine-not-process : ¬ (RepC Pa1 0 Stop ⊑FD (Stop ⦀ Pa1))
pristine-not-process (fd , _) with fd (inj₁ rhs-failure)
... | inj₁ f = inert-no-offer (RepFailOut.inP (RepC-failures-elim Pa1 0 Stop f)) (tt , isEvl _) (Stop , sVis refl refl)
... | inj₂ d with RepDivOut.dv (RepC-div-elim Pa1 0 Stop d)
...   | inj₁ dY              = stable-no-τ (stop-reach-stable (RepDivOut.runY (RepC-div-elim Pa1 0 Stop d))) (Diverges.step dY)
...   | inj₂ (inj₁ a)        = pa1-ends-converge (RepDivOut.runs (RepC-div-elim Pa1 0 Stop d)) a
...   | inj₂ (inj₂ (_ , st)) = stable-no-τ {t = Pa1} (λ _ _ → refl) st

-- instantiation check: the unfold at a copy that terminates at once (cannot fail — the
-- theorem it instantiates, `!ᶜ-unfold-FD`, is premise-free)
skip-unfold : !ᶜ (Skip {lzero}) ≈FD (Skip ⦀ !ᶜ Skip)
skip-unfold = !ᶜ-unfold-FD Skip

-- every copy: a → a → Stop, so identical copies collide on `a` (the deferral that ruled out R3)
Paa1 : T
Paa1 = evA ⟶₀ (evA ⟶₀ Stop)

-- instantiation check: the unfold holds even when copies collide (cannot fail — same
-- premise-free theorem, instantiated at a concrete event type)
collide-unfold : !ᶜ Paa1 ≈FD (Paa1 ⦀ !ᶜ Paa1)
collide-unfold = !ᶜ-unfold-FD Paa1
