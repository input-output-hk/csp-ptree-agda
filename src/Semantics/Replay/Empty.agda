{-# OPTIONS --safe #-}

-- Identity component for finite products of replay machines.
module Semantics.Replay.Empty where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.List using ([])
open import Data.Product using (_,_)
open import Semantics.Replay
open import Relation.Nullary using (yes)

-- No visible or silent steps; only the empty trace is possible.
empty : Replay 0ℓ ⊤ ⊥
empty = record
  { _-[_]→_ = λ _ _ _ → ⊥
  ; _-τ→_ = λ _ _ → ⊥
  ; _≟E_ = λ ()
  ; after = λ _ _ → []
  ; taus = λ _ → []
  ; after-sound = λ ()
  ; taus-sound = λ ()
  ; after-complete = λ ()
  ; taus-complete = λ ()
  }

open Traces empty public
open import Data.List using (List; _∷_)
open import Relation.Nullary using (Dec)

-- Decide the identity component's trace membership.
empty? : (es : List ⊥) → Dec (HasTrace tt es)
empty? [] = yes (tt , done)
empty? (() ∷ es)
