{-# OPTIONS --safe #-}

-- Decision procedure for weak traces of a replay interface (trace-replay
-- Phase 4). Under the hypothesis that τ is well-founded on the states
-- reachable from s₀ (amendment A5), `HasTrace s₀ es` is decidable: `yes`
-- carries a run built from the `-sound` fields, `no` a refutation built
-- from the `-complete` fields. The boolean part of the result (`does`)
-- computes by evaluation, so `True`/`False` tests reduce at typecheck time.
-- Imports only stdlib and Semantics.Replay.
module Semantics.Replay.Decide where

open import Level using (Level; _⊔_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; find; lose)
open import Data.List.Relation.Unary.Any using (Any; here; there; fromSum; toSum)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′; _⊎-dec_)

open import Semantics.Replay

-- The decider over one replay interface.
module Decider {ℓs ℓe ℓr : Level} {S : Set ℓs} {E : Set ℓe}
               (R : Replay ℓr S E) where
  open Replay R
  open Traces R

  -- Inductive accessibility of τ: every τ-path out of s is finite.
  data τAcc (s : S) : Set (ℓs ⊔ ℓr) where
    -- all τ-successors are accessible
    acc : (∀ {s′} → s -τ→ s′ → τAcc s′) → τAcc s

  -- τ is well-founded on every state reachable from s₀ (by a weak run).
  τAccReach : S → Set (ℓs ⊔ ℓe ⊔ ℓr)
  τAccReach s₀ = ∀ {es s} → s₀ ⇒⟨ es ⟩ s → τAcc s

  -- A global certificate gives the reachable one at every root.
  τAccReach-all : (∀ s → τAcc s) → ∀ s₀ → τAccReach s₀
  τAccReach-all cert _ _ = cert _

  -- Decide `Any P xs` from a decider for the members of xs only.
  any∈? : ∀ {p} {P : S → Set p} (xs : List S) →
          (∀ {x} → x ∈ xs → Dec (P x)) → Dec (Any P xs)
  any∈? []       _ = no λ ()
  any∈? (x ∷ xs) d =
    map′ fromSum toSum (d (here refl) ⊎-dec any∈? xs (λ m → d (there m)))

  -- The two ways a run on e ∷ es can start: a listed e-successor runs es,
  -- or a listed τ-successor runs e ∷ es.
  Next : S → E → List E → Set (ℓs ⊔ ℓe ⊔ ℓr)
  Next s e es = Any (λ x → HasTrace x es) (after s e)
              ⊎ Any (λ x → HasTrace x (e ∷ es)) (taus s)

  -- Soundness of Next (uses the `-sound` fields).
  Next→HasTrace : ∀ {s e es} → Next s e es → HasTrace s (e ∷ es)
  Next→HasTrace (inj₁ a) with find a
  ... | _ , m , s″ , p = s″ , vis (after-sound m) p
  Next→HasTrace (inj₂ a) with find a
  ... | _ , m , s″ , p = s″ , tau (taus-sound m) p

  -- Inversion: a run on e ∷ es starts with a τ or with the e step
  -- (uses the `-complete` fields).
  HasTrace→Next : ∀ {s e es} → HasTrace s (e ∷ es) → Next s e es
  HasTrace→Next (_ , vis st p) = inj₁ (lose (after-complete st) (_ , p))
  HasTrace→Next (_ , tau st p) = inj₂ (lose (taus-complete st) (_ , p))

  -- Decide whether es is a weak trace of s₀, given τ well-founded on the
  -- states reachable from s₀.
  -- Termination: lexicographic on (es, τAcc). A visible step calls
  -- `hasTrace?` on the strictly shorter tail; a τ step keeps the trace and
  -- descends into the τAcc proof (`f st` is a subterm of `acc f`).
  -- The hypothesis is re-based along each step (`vis`/`tau` prepended).
  hasTrace? : ∀ {s₀} → τAccReach s₀ → (es : List E) → Dec (HasTrace s₀ es)
  -- Worker carrying the accessibility proof of the current state.
  go : ∀ {s} → τAccReach s → τAcc s → (es : List E) → Dec (HasTrace s es)

  hasTrace? h es = go h (h done) es

  go h _ [] = yes (_ , done)
  go {s} h (acc f) (e ∷ es) =
    map′ Next→HasTrace HasTrace→Next
      ( any∈? {P = λ x → HasTrace x es} (after s e)
          (λ m → hasTrace? (λ p → h (vis (after-sound m) p)) es)
      ⊎-dec
        any∈? {P = λ x → HasTrace x (e ∷ es)} (taus s)
          (λ m → go (λ p → h (tau (taus-sound m) p)) (f (taus-sound m)) (e ∷ es)))
