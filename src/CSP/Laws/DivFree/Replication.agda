{-# OPTIONS --guardedness #-}

-- Divergence (freedom) of native replication `Rep` (CSP.Replication).
--
--   * NEGATIVE CONTROL.  `Rep-unguarded-diverges`: if every copy `P j` has an initial τ,
--     `Rep merge P k Q` DIVERGES — each fresh copy's τ spawns it and exposes the next
--     fresh copy.  So the `isStable` premise of the theorems below is load-bearing.
--   * `τ-Acc-Rep`: with stable (hence τ-free) fresh copies, a τ of `Rep` is a τ of the
--     running copies `Q`, so `τ-Acc Q` lifts to `Rep` (structural recursion on `τ-Acc`).
--   * `τ-AccReach-Par` (general, absent from the repo before): τ-accessibility at every
--     √-free-reachable state is closed under `Par`.
--   * `τ-AccReach-Rep` / `!-divergenceFree`: the same for `Rep` and for `!`.
-- NOTE on `isStable` (`Process_Trees.agda:173-176`): it is `⊥` on `ret` as well as on
-- `sil`, so the `∀ j → isStable (P j)` premise excludes terminating (`ret`) copies too,
-- not only copies with an initial τ.
-- All three reachability proofs are inductions on the `⟹∖√` run, the state invariant
-- being carried by two forward-declared functions (one per state shape: the operator,
-- and its inline same-event collision node).

open import Level using (Level)
open import Data.Nat using (ℕ; suc)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (nothing)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.DivFree.Replication {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import CSP.Replication E-≟
open import Semantics.LTS {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Deadlock {E = E} {I = ExtI E} using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Semantics.DivergenceFree {E = E} {I = ExtI E}
open import CSP.Laws.DivFree.Closure E-≟ using (τ-Acc-Par; τ-Acc-Stop)
open import CSP.Laws.Traces.TraceLaws E-≟ using (Stop-no-ev)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟
  using (Par-τ-elim; τL; τR; Par-ev-elim; evSync; evL; evR) renaming (evBoth to parEvBoth)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟ using (brBoth-τ-elim; brBoth-no-ev)
open import CSP.Laws.Traces.ReplicationSteps E-≟
  using ( repBoth; Rep-τ-elim; τRun; τFresh; Rep-ev-elim; evRun; evFresh; evBoth
        ; repBoth-τ-elim; repBoth-no-ev; Rep-τFresh-intro )

private
  variable
    ℓ₁ ℓ₂ ℓ₃ : Level
    R₁ : Set ℓ₁
    R₂ : Set ℓ₂
    R₃ : Set ℓ₃

-------------------------------------------------------------------------------------
-- §1.  Generic plumbing for `τ-AccReach`.
-- `arτ`/`arev` are the one-liners of `CSP.Laws.FSim.AlphaParCong`, restated here
-- rather than imported: that module's closure contains the postulate `αpar-Diverges→`
-- (`CSP/Laws/FD/AlphaParallelDivergence.agda:59-62`), and this module's closure is
-- postulate-free.
-------------------------------------------------------------------------------------

-- `τ-AccReach` survives one τ-step (prepend it to the run)
arτ : {t u : PTree E (ExtI E) R₁} → τ-AccReach t → t ─[ τ ]─► u → τ-AccReach u
arτ ar st run = ar (∖√-τ st run)

-- `τ-AccReach` survives one visible non-√ step
arev : {t u : PTree E (ExtI E) R₁} {e : Event} → τ-AccReach t → t ─[ ev (evl e) ]─► u → τ-AccReach u
arev ar st run = ar (∖√-ev st run)

-- `Stop` has no step at all, so every state it reaches is itself: τ-accessible
τ-AccReach-Stop : τ-AccReach (Stop {R = R₁})
τ-AccReach-Stop ∖√-refl      = τ-Acc-Stop
τ-AccReach-Stop (∖√-τ st _)  = ⊥-elim (stable-no-τ {t = Stop} (λ _ _ → refl) st)
τ-AccReach-Stop (∖√-ev st _) = ⊥-elim (Stop-no-ev st)

-------------------------------------------------------------------------------------
-- §2.  `τ-AccReach` is closed under generalised parallel.  Run induction; the two
-- state shapes are `Par A merge P Q` and the both-offer overlap node of `par-pVis`
-- (`CSP/Operators.agda`), each with operands √-free-reachable from the originals.
-------------------------------------------------------------------------------------

-- the both-offer overlap node of `Par` (τ-only, branch 0 = `Par P′ Q`, 1 = `Par P Q′`)
parBoth : (A : EventSet) (merge : R₁ → R₂ → R₃)
          (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
          (P′ : PTree E (ExtI E) R₁) (Q′ : PTree E (ExtI E) R₂) → PTree E (ExtI E) R₃
parBoth A merge P Q P′ Q′ = ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P′ Q′))

-- τ-accessibility at every √-free-reachable state is closed under `Par`
τ-AccReach-Par : (A : EventSet) (merge : R₁ → R₂ → R₃)
                 (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
               → τ-AccReach P → τ-AccReach Q → τ-AccReach (Par A merge P Q)

-- … and at the overlap node, given its four operand states are
τ-AccReach-parBoth : (A : EventSet) (merge : R₁ → R₂ → R₃)
                     (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                     (P′ : PTree E (ExtI E) R₁) (Q′ : PTree E (ExtI E) R₂)
                   → τ-AccReach P → τ-AccReach Q → τ-AccReach P′ → τ-AccReach Q′
                   → τ-AccReach (parBoth A merge P Q P′ Q′)

τ-AccReach-Par A merge P Q aP aQ ∖√-refl = τ-Acc-Par A merge (aP ∖√-refl) (aQ ∖√-refl)
τ-AccReach-Par A merge P Q aP aQ (∖√-τ st run) with Par-τ-elim A merge P Q st
... | τL P′ pτ refl = τ-AccReach-Par A merge P′ Q (arτ aP pτ) aQ run
... | τR Q′ qτ refl = τ-AccReach-Par A merge P Q′ aP (arτ aQ qτ) run
τ-AccReach-Par A merge P Q aP aQ (∖√-ev st run) with Par-ev-elim A merge P Q st
... | evSync {P' = P′} {Q' = Q′} _ pe qe =
        τ-AccReach-Par A merge P′ Q′ (arev aP pe) (arev aQ qe) run
... | evL {P' = P′} _ pe = τ-AccReach-Par A merge P′ Q (arev aP pe) aQ run
... | evR {Q' = Q′} _ qe = τ-AccReach-Par A merge P Q′ aP (arev aQ qe) run
... | parEvBoth {P' = P′} {Q' = Q′} _ pe qe =
        τ-AccReach-parBoth A merge P Q P′ Q′ aP aQ (arev aP pe) (arev aQ qe) run

τ-AccReach-parBoth A merge P Q P′ Q′ aP aQ aP′ aQ′ ∖√-refl = acc go
  where
    -- the overlap node's two τ's land on `Par P′ Q` / `Par P Q′`
    go : ∀ {M} → parBoth A merge P Q P′ Q′ ─[ τ ]─► M → τ-Acc M
    go st with brBoth-τ-elim A merge P Q P′ Q′ st
    ... | inj₁ refl = τ-Acc-Par A merge (aP′ ∖√-refl) (aQ ∖√-refl)
    ... | inj₂ refl = τ-Acc-Par A merge (aP ∖√-refl) (aQ′ ∖√-refl)
τ-AccReach-parBoth A merge P Q P′ Q′ aP aQ aP′ aQ′ (∖√-τ st run)
  with brBoth-τ-elim A merge P Q P′ Q′ st
... | inj₁ refl = τ-AccReach-Par A merge P′ Q aP′ aQ run
... | inj₂ refl = τ-AccReach-Par A merge P Q′ aP aQ′ run
τ-AccReach-parBoth A merge P Q P′ Q′ aP aQ aP′ aQ′ (∖√-ev st run) =
  ⊥-elim (brBoth-no-ev A merge P Q P′ Q′ st)

module _ {ℓr} {R : Set ℓr} (merge : R → R → R) where

  -- the process type the combinator lives in
  private
    T : Set _
    T = PTree E (ExtI E) R

  -- an UNGUARDED copy (initial τ) makes replication diverge: each fresh copy's τ spawns it
  Rep-unguarded-diverges : (P : ℕ → T) (k : ℕ) (Q : T)
                         → (P′ : ℕ → T) → (∀ j → P j ─[ τ ]─► P′ j)
                         → Diverges (Rep merge P k Q)
  Rep-unguarded-diverges P k Q P′ st .Diverges.next = Rep merge P (suc k) (Par ∅ES merge Q (P′ k))
  Rep-unguarded-diverges P k Q P′ st .Diverges.step = Rep-τFresh-intro merge P k Q (st k)
  Rep-unguarded-diverges P k Q P′ st .Diverges.rest =
    Rep-unguarded-diverges P (suc k) (Par ∅ES merge Q (P′ k)) P′ st

  -- the collision node is τ-accessible once both of its τ-targets are
  τ-Acc-repBoth : (P : ℕ → T) (k : ℕ) (Q Q′ P′ : T)
                → τ-Acc (Rep merge P k Q′) → τ-Acc (Rep merge P (suc k) (Par ∅ES merge Q P′))
                → τ-Acc (repBoth merge P k Q Q′ P′)
  τ-Acc-repBoth P k Q Q′ P′ a₀ a₁ = acc go
    where
      -- exactly two τ-targets (`repBoth-τ-elim`)
      go : ∀ {M} → repBoth merge P k Q Q′ P′ ─[ τ ]─► M → τ-Acc M
      go st with repBoth-τ-elim merge P k Q Q′ P′ st
      ... | inj₁ refl = a₀
      ... | inj₂ refl = a₁

  -- stable fresh copies have no τ, so every τ of `Rep` is a τ of `Q`: `τ-Acc Q` lifts
  τ-Acc-Rep : (P : ℕ → T) (k : ℕ) (Q : T)
            → (∀ j → isStable (P j)) → τ-Acc Q → τ-Acc (Rep merge P k Q)
  τ-Acc-Rep P k Q stP (acc f) = acc go
    where
      -- a running copy's τ recurses on `f`; a fresh copy's τ contradicts stability
      go : ∀ {M} → Rep merge P k Q ─[ τ ]─► M → τ-Acc M
      go st with Rep-τ-elim merge P k Q st
      ... | τRun {Q′ = Q′} qτ = τ-Acc-Rep P k Q′ stP (f qτ)
      ... | τFresh pτ         = ⊥-elim (stable-no-τ (stP k) pτ)

  -- τ-accessibility at every √-free-reachable state of `Rep` (run induction)
  τ-AccReach-Rep : (P : ℕ → T) (k : ℕ) (Q : T)
                 → (∀ j → isStable (P j)) → (∀ j → τ-AccReach (P j)) → τ-AccReach Q
                 → τ-AccReach (Rep merge P k Q)

  -- … and of its collision node, given both of its τ-targets' running parts
  τ-AccReach-repBoth : (P : ℕ → T) (k : ℕ) (Q Q′ P′ : T)
                     → (∀ j → isStable (P j)) → (∀ j → τ-AccReach (P j))
                     → τ-AccReach Q′ → τ-AccReach (Par ∅ES merge Q P′)
                     → τ-AccReach (repBoth merge P k Q Q′ P′)

  τ-AccReach-Rep P k Q stP aP aQ ∖√-refl = τ-Acc-Rep P k Q stP (aQ ∖√-refl)
  τ-AccReach-Rep P k Q stP aP aQ (∖√-τ st run) with Rep-τ-elim merge P k Q st
  ... | τRun {Q′ = Q′} qτ = τ-AccReach-Rep P k Q′ stP aP (arτ aQ qτ) run
  ... | τFresh pτ         = ⊥-elim (stable-no-τ (stP k) pτ)
  τ-AccReach-Rep P k Q stP aP aQ (∖√-ev st run) with Rep-ev-elim merge P k Q st
  ... | evRun {Q′ = Q′} qe _ = τ-AccReach-Rep P k Q′ stP aP (arev aQ qe) run
  ... | evFresh {P′ = P′} pe _ =
          τ-AccReach-Rep P (suc k) (Par ∅ES merge Q P′) stP aP
            (τ-AccReach-Par ∅ES merge Q P′ aQ (arev (aP k) pe)) run
  ... | evBoth {Q′ = Q′} {P′ = P′} qe pe =
          τ-AccReach-repBoth P k Q Q′ P′ stP aP (arev aQ qe)
            (τ-AccReach-Par ∅ES merge Q P′ aQ (arev (aP k) pe)) run

  τ-AccReach-repBoth P k Q Q′ P′ stP aP aQ′ aQP ∖√-refl =
    τ-Acc-repBoth P k Q Q′ P′ (τ-Acc-Rep P k Q′ stP (aQ′ ∖√-refl))
                              (τ-Acc-Rep P (suc k) (Par ∅ES merge Q P′) stP (aQP ∖√-refl))
  τ-AccReach-repBoth P k Q Q′ P′ stP aP aQ′ aQP (∖√-τ st run)
    with repBoth-τ-elim merge P k Q Q′ P′ st
  ... | inj₁ refl = τ-AccReach-Rep P k Q′ stP aP aQ′ run
  ... | inj₂ refl = τ-AccReach-Rep P (suc k) (Par ∅ES merge Q P′) stP aP aQP run
  τ-AccReach-repBoth P k Q Q′ P′ stP aP aQ′ aQP (∖√-ev st run) =
    ⊥-elim (repBoth-no-ev merge P k Q Q′ P′ st)

  -- `!` of stable, reachably-divergence-free copies is divergence-free
  !-divergenceFree : (P : ℕ → T)
                   → (∀ j → isStable (P j)) → (∀ j → τ-AccReach (P j))
                   → DivergenceFree (! merge P)
  !-divergenceFree P stP aP =
    τ-AccReach→DivergenceFree (τ-AccReach-Rep P 0 Stop stP aP τ-AccReach-Stop)
