{-# OPTIONS --safe #-}

-- Generic trace-replay interface: a state type with visible and silent
-- step relations, computable finite successor lists that are sound and
-- complete for those relations, weak traces, and prefix closure.
-- Model-agnostic: imports neither Process_Trees nor any CSP module.
module Semantics.Replay where

open import Level using (Level; _⊔_; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (∃-syntax; _,_)
open import Relation.Binary.Definitions using (DecidableEquality)

-- A replay interface over states S and visible events E: step relations
-- plus finite, computable successor lists that are sound and complete.
record Replay {ℓs ℓe : Level} (ℓr : Level) (S : Set ℓs) (E : Set ℓe)
       : Set (ℓs ⊔ ℓe ⊔ suc ℓr) where
  field
    -- visible step on event e
    _-[_]→_ : S → E → S → Set ℓr
    -- silent (τ) step
    _-τ→_   : S → S → Set ℓr
    -- decidable equality of visible events
    _≟E_    : DecidableEquality E

    -- all e-successors of a state
    after : S → E → List S
    -- all τ-successors of a state
    taus  : S → List S

    -- every listed e-successor is an e-step
    after-sound : ∀ {s e s′} → s′ ∈ after s e → s -[ e ]→ s′
    -- every listed τ-successor is a τ-step
    taus-sound  : ∀ {s s′}   → s′ ∈ taus s    → s -τ→ s′

    -- every e-step is listed
    after-complete : ∀ {s e s′} → s -[ e ]→ s′ → s′ ∈ after s e
    -- every τ-step is listed
    taus-complete  : ∀ {s s′}   → s -τ→ s′    → s′ ∈ taus s

-- Weak traces of a replay interface; uses only the two step relations.
module Traces {ℓs ℓe ℓr : Level} {S : Set ℓs} {E : Set ℓe}
              (R : Replay ℓr S E) where
  open Replay R

  infix 4 _⇒⟨_⟩_

  -- s ⇒⟨ es ⟩ s″: from s, perform the visible events es (with any τ steps
  -- interleaved) and end in s″.
  data _⇒⟨_⟩_ : S → List E → S → Set (ℓs ⊔ ℓe ⊔ ℓr) where
    -- empty trace, no step
    done : ∀ {s} → s ⇒⟨ [] ⟩ s
    -- a τ step, invisible in the trace
    tau  : ∀ {s s′ s″ es} → s -τ→ s′ → s′ ⇒⟨ es ⟩ s″ → s ⇒⟨ es ⟩ s″
    -- a visible step on e, prepended to the trace
    vis  : ∀ {s s′ s″ e es} → s -[ e ]→ s′ → s′ ⇒⟨ es ⟩ s″ → s ⇒⟨ e ∷ es ⟩ s″

  -- es is a weak trace of s
  HasTrace : S → List E → Set (ℓs ⊔ ℓe ⊔ ℓr)
  HasTrace s es = ∃[ s″ ] s ⇒⟨ es ⟩ s″

  -- Concatenation: a run on es followed by a run on fs is a run on es ++ fs.
  ⇒-++ : ∀ {s s′ s″ es fs} → s ⇒⟨ es ⟩ s′ → s′ ⇒⟨ fs ⟩ s″ → s ⇒⟨ es ++ fs ⟩ s″
  ⇒-++ done        q = q
  ⇒-++ (tau st p)  q = tau st (⇒-++ p q)
  ⇒-++ (vis st p)  q = vis st (⇒-++ p q)

  -- Splitting: a run on es ++ fs passes through a state reached on es.
  ⇒-prefix : ∀ {s s″} es {fs} → s ⇒⟨ es ++ fs ⟩ s″ → HasTrace s es
  ⇒-prefix []       _              = _ , done
  ⇒-prefix (e ∷ es) (tau st p)     with ⇒-prefix (e ∷ es) p
  ... | s′ , q = s′ , tau st q
  ⇒-prefix (e ∷ es) (vis st p)     with ⇒-prefix es p
  ... | s′ , q = s′ , vis st q

  -- Prefix closure of weak traces.
  HasTrace-prefix : ∀ {s} es {fs} → HasTrace s (es ++ fs) → HasTrace s es
  HasTrace-prefix es (_ , p) = ⇒-prefix es p
