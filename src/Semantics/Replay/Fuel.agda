{-# OPTIONS --safe #-}

-- Fuel-bounded replay checker (semi-decision): depth-first search for a
-- weak-trace witness. Acceptance is sound by construction (the witness is
-- built from the `-sound` fields only); `unknown` says nothing.
module Semantics.Replay.Fuel where

open import Level using (Level; _⊔_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Unit.Properties as Unitₚ

open import Semantics.Replay

-- The checker over one replay interface.
module Checker {ℓs ℓe ℓr : Level} {S : Set ℓs} {E : Set ℓe}
               (R : Replay ℓr S E) where
  open Replay R
  open Traces R

  -- Outcome of a bounded search: a witness, or no conclusion.
  data Verdict (s : S) (es : List E) : Set (ℓs ⊔ ℓe ⊔ ℓr) where
    -- es is a weak trace of s, with the run as evidence
    accept  : HasTrace s es → Verdict s es
    -- fuel ran out or no run was found within it
    unknown : Verdict s es

  -- The verdict is an acceptance (computes to ⊤ / ⊥ for typecheck-time tests).
  IsAccept : ∀ {s es} → Verdict s es → Set
  IsAccept (accept _) = ⊤
  IsAccept unknown    = ⊥

  -- Extract the witness from an accepting verdict.
  accept-sound : ∀ {s es} (v : Verdict s es) → IsAccept v → HasTrace s es
  accept-sound (accept h) _ = h

  -- Left-biased choice: keep the first acceptance.
  _orElse_ : ∀ {s es} → Verdict s es → Verdict s es → Verdict s es
  accept h orElse _ = accept h
  unknown  orElse v = v

  -- Prefix a visible step to a verdict.
  vis-lift : ∀ {s s′ e es} → s -[ e ]→ s′ → Verdict s′ es → Verdict s (e ∷ es)
  vis-lift st (accept (_ , p)) = accept (_ , vis st p)
  vis-lift st unknown          = unknown

  -- Prefix a τ step to a verdict.
  τ-lift : ∀ {s s′ es} → s -τ→ s′ → Verdict s′ es → Verdict s es
  τ-lift st (accept (_ , p)) = accept (_ , tau st p)
  τ-lift st unknown          = unknown

  -- check n s es: search for a run of s on es using at most n τ steps.
  -- Fuel is GLOBAL along a run: it is not reset after a visible step, so n
  -- bounds the total number of τ steps on the whole run. Sibling branches
  -- (backtracking) each start from the same remaining fuel.
  -- Termination: size-change on (es, fuel) — visible steps shrink es with
  -- fuel unchanged, τ steps shrink fuel with es unchanged — plus structural
  -- recursion on the candidate list in the two helpers.
  check   : ℕ → (s : S) → (es : List E) → Verdict s es
  -- Try each listed e-successor (with its membership proof) on the tail.
  tryVis  : ℕ → (s : S) (e : E) (es : List E) (xs : List S) →
            (∀ {x} → x ∈ xs → s -[ e ]→ x) → Verdict s (e ∷ es)
  -- Try each listed τ-successor (with its membership proof) on the same trace.
  tryTau  : ℕ → (s : S) (es : List E) (xs : List S) →
            (∀ {x} → x ∈ xs → s -τ→ x) → Verdict s es

  check n       s []       = accept (s , done)
  check zero    s (e ∷ es) = tryVis zero s e es (after s e) after-sound
  check (suc n) s (e ∷ es) =
    tryVis (suc n) s e es (after s e) after-sound
      orElse tryTau n s (e ∷ es) (taus s) taus-sound

  tryVis n s e es []       _ = unknown
  tryVis n s e es (x ∷ xs) k =
    vis-lift (k (here refl)) (check n x es)
      orElse tryVis n s e es xs (λ m → k (there m))

  tryTau n s es []       _ = unknown
  tryTau n s es (x ∷ xs) k =
    τ-lift (k (here refl)) (check n x es)
      orElse tryTau n s es xs (λ m → k (there m))

-- Sanity test on a toy two-state machine: false -τ→ true, true -[tt]→ true.
private
  module Toy where

    -- the single τ step
    data Tau : Bool → Bool → Set where
      go : Tau false true

    -- the single visible step
    data Vis : Bool → ⊤ → Bool → Set where
      tick : Vis true tt true

    -- e-successors
    toyAfter : Bool → ⊤ → List Bool
    toyAfter true  _ = true ∷ []
    toyAfter false _ = []

    -- τ-successors
    toyTaus : Bool → List Bool
    toyTaus false = true ∷ []
    toyTaus true  = []

    -- soundness of toyAfter
    toyAfter-sound : ∀ {s e s′} → s′ ∈ toyAfter s e → Vis s e s′
    toyAfter-sound {true}  {tt} (here refl) = tick
    toyAfter-sound {true}  (there ())
    toyAfter-sound {false} ()

    -- soundness of toyTaus
    toyTaus-sound : ∀ {s s′} → s′ ∈ toyTaus s → Tau s s′
    toyTaus-sound {false} (here refl) = go
    toyTaus-sound {false} (there ())
    toyTaus-sound {true}  ()

    -- the toy replay interface
    toy : Replay Level.zero Bool ⊤
    toy = record
      { _-[_]→_        = Vis
      ; _-τ→_          = Tau
      ; _≟E_           = Unitₚ._≟_
      ; after          = toyAfter
      ; taus           = toyTaus
      ; after-sound    = toyAfter-sound
      ; taus-sound     = toyTaus-sound
      ; after-complete = λ { tick → here refl }
      ; taus-complete  = λ { go → here refl }
      }

    open Checker toy

    -- one τ of fuel reaches the ticking state
    _ : IsAccept (check 1 false (tt ∷ tt ∷ []))
    _ = tt

    -- with no fuel the τ step is unavailable
    _ : check 0 false (tt ∷ []) ≡ unknown
    _ = refl
