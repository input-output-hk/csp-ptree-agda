{-# OPTIONS --safe #-}

-- Reordered hidden menus retain the same paired language, including exhaustive rejection.
module Semantics.Replay.Examples.TwoListOrderedTests where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (false; true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (does; toWitness; toWitnessFalse)
import Semantics.Replay.Examples.TwoListTests as Fixture
import Semantics.Replay.TwoListDecide as Search

-- The current client input selects a different ordering, with duplicated successful targets.
targets : Fixture.State → List ⊤ → List ⊤ → List Fixture.State
targets Fixture.start [] _ = Fixture.dead ∷ Fixture.hub ∷ []
targets Fixture.start (_ ∷ _) _ = Fixture.hub ∷ Fixture.dead ∷ Fixture.hub ∷ []
targets _ _ _ = []

-- Reordering or repeating a target introduces no new hidden transition.
sound : ∀ {s cs ss t} → t ∈ targets s cs ss → Fixture.Tau s t
sound {Fixture.start} {[]} (here refl) = Fixture.bad
sound {Fixture.start} {[]} (there (here refl)) = Fixture.good
sound {Fixture.start} {_ ∷ _} (here refl) = Fixture.good
sound {Fixture.start} {_ ∷ _} (there (here refl)) = Fixture.bad
sound {Fixture.start} {_ ∷ _} (there (there (here refl))) = Fixture.good

-- Both actual source rules remain available for every input-dependent ordering.
complete : ∀ {s cs ss t} → Fixture.Tau s t → t ∈ targets s cs ss
complete {cs = []} Fixture.bad = here refl
complete {cs = []} Fixture.good = there (here refl)
complete {cs = _ ∷ _} Fixture.bad = there (here refl)
complete {cs = _ ∷ _} Fixture.good = here refl

-- The instance changes only silent enumeration, reusing the original relation and accessibility.
module Check = Search.OrderedDecider Fixture.replay
  (λ (_ : ⊤) → false) (λ (_ : ⊤) → true) Fixture.accessible
  targets (λ {s} {cs} {ss} → sound {s} {cs} {ss})
    (λ {s} {cs} {ss} → complete {s} {cs} {ss})

-- The altered order computes a witness for exactly the original paired trace proposition.
reordered-success : Fixture.Trace.PairTrace Fixture.start (tt ∷ []) (tt ∷ [])
reordered-success = toWitness {a? = Check.decide (tt ∷ []) (tt ∷ []) Fixture.start} tt

-- Empty client input exercises the other menu ordering without introducing unrecorded actions.
server-only : Fixture.Trace.PairTrace Fixture.start [] (tt ∷ [])
server-only = toWitness {a? = Check.decide [] (tt ∷ []) Fixture.start} tt

-- The independent server-first merge remains visible when the client head is unavailable.
forced-server-first : Fixture.Trace.PairTrace Fixture.serverGate (tt ∷ []) (tt ∷ [])
forced-server-first = toWitness {a? = Check.decide (tt ∷ []) (tt ∷ []) Fixture.serverGate} tt

-- Exhaustive rejection still covers every reordered and duplicated hidden branch.
reordered-rejection : Fixture.Trace.PairTrace Fixture.start (tt ∷ tt ∷ []) (tt ∷ []) → ⊥
reordered-rejection = toWitnessFalse {a? = Check.decide (tt ∷ tt ∷ []) (tt ∷ []) Fixture.start} tt

-- The custom silent policy cannot manufacture a missing visible client record.
no-unmatched-visible : Fixture.Trace.PairTrace Fixture.needsClient [] (tt ∷ []) → ⊥
no-unmatched-visible = toWitnessFalse {a? = Check.decide [] (tt ∷ []) Fixture.needsClient} tt

-- EOF keeps prefix semantics rather than forcing the hidden menu to drain.
eof-prefix : Fixture.Trace.PairTrace Fixture.start [] []
eof-prefix = toWitness {a? = Check.decide [] [] Fixture.start} tt

-- The compatibility wrapper retains the original computed acceptance gate.
default-success-gate : does (Fixture.Check.decide (tt ∷ []) (tt ∷ []) Fixture.start) ≡ true
default-success-gate = refl

-- Reordering retains computed rejection while the original default engine remains unchanged.
ordered-rejection-gate : does (Check.decide (tt ∷ tt ∷ []) (tt ∷ []) Fixture.start) ≡ false
ordered-rejection-gate = refl
