{-# OPTIONS --safe #-}

-- Complete two-list weak prefix search: finite local branching and silent accessibility suffice.
module Semantics.Replay.TwoListDecide where

open import Level using (Level; _⊔_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; find; lose)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′; _⊎-dec_)
open import Semantics.Replay
import Semantics.Replay.Decide as Existing
import Semantics.Replay.TwoList as Paired

-- Input-dependent silent menus may reorder branches while preserving the original transition relation.
module OrderedDecider {ℓs ℓe ℓr ℓc ℓv : Level}
  {S : Set ℓs} {E : Set ℓe} {Client : Set ℓc} {Server : Set ℓv}
  (R : Replay ℓr S E) (embedClient : Client → E) (embedServer : Server → E)
  (accessible : ∀ s → Existing.Decider.τAcc R s)
  (tauTargets : S → List Client → List Server → List S)
  (tauSound : ∀ {s cs ss t} → t ∈ tauTargets s cs ss → Replay._-τ→_ R s t)
  (tauComplete : ∀ {s cs ss t} → Replay._-τ→_ R s t → t ∈ tauTargets s cs ss) where
  open Replay R
  open Paired.Traces R embedClient embedServer
  module Backend = Existing.Decider R

  -- Empty endpoint input has no visible branch, so unrecorded events can never be inserted.
  data ClientNext (s : S) : List Client → List Server → Set (ℓs ⊔ ℓe ⊔ ℓr ⊔ ℓc ⊔ ℓv) where
    next : ∀ {c cs ss} → Any (λ t → PairTrace t cs ss) (after s (embedClient c)) →
      ClientNext s (c ∷ cs) ss

  -- The other endpoint's head remains an independent alternative to preserve all possible merges.
  data ServerNext (s : S) : List Client → List Server → Set (ℓs ⊔ ℓe ⊔ ℓr ⊔ ℓc ⊔ ℓv) where
    next : ∀ {cs v ss} → Any (λ t → PairTrace t cs ss) (after s (embedServer v)) →
      ServerNext s cs (v ∷ ss)

  -- A nonempty paired prefix begins with either endpoint head or one listed silent successor.
  Next : S → List Client → List Server → Set (ℓs ⊔ ℓe ⊔ ℓr ⊔ ℓc ⊔ ℓv)
  Next s cs ss = ClientNext s cs ss ⊎ (ServerNext s cs ss ⊎ Any (λ t → PairTrace t cs ss) (tauTargets s cs ss))

  -- Every finite successor branch yields an actual paired run using the interface's soundness fields.
  forward : ∀ {s cs ss} → Next s cs ss → PairTrace s cs ss
  forward (inj₁ (next branch)) with find branch
  ... | _ , member , target , rest = target , client (after-sound member) rest
  forward (inj₂ (inj₁ (next branch))) with find branch
  ... | _ , member , target , rest = target , server (after-sound member) rest
  forward (inj₂ (inj₂ branch)) with find branch
  ... | _ , member , target , rest = target , tau (tauSound member) rest

  -- The empty-prefix constructor is excluded exactly when at least one endpoint still has a row.
  data Remaining : List Client → List Server → Set (ℓc ⊔ ℓv) where
    left : ∀ {c cs ss} → Remaining (c ∷ cs) ss
    right : ∀ {v ss} → Remaining [] (v ∷ ss)

  -- Complete successor lists cover each possible first operation of an independently given witness.
  backward : ∀ {s cs ss} → Remaining cs ss → PairTrace s cs ss → Next s cs ss
  backward () (_ , done)
  backward nonempty (_ , tau step rest) = inj₂ (inj₂ (lose (tauComplete step) (_ , rest)))
  backward nonempty (_ , client step rest) = inj₁ (next (lose (after-complete step) (_ , rest)))
  backward nonempty (_ , server step rest) = inj₂ (inj₁ (next (lose (after-complete step) (_ , rest))))

  -- The mutually defined worker decreases endpoint lists on visible steps and accessibility on silent steps.
  decide : (cs : List Client) (ss : List Server) (s : S) → Dec (PairTrace s cs ss)
  -- Accessibility is refreshed after consuming either endpoint's row, even when visible steps increase rank.
  go : (cs : List Client) (ss : List Server) {s : S} → Backend.τAcc s → Dec (PairTrace s cs ss)

  decide cs ss s = go cs ss (accessible s)
  go [] [] _ = yes (_ , done)
  go (c ∷ cs) [] {s = s} (Backend.acc smaller) = map′ forward (backward left)
    (map′ next (λ { (next branch) → branch })
      (Backend.any∈? (after s (embedClient c)) (λ member → decide cs [] _)) ⊎-dec
      ((no λ ()) ⊎-dec
        Backend.any∈? (tauTargets s (c ∷ cs) []) (λ member → go (c ∷ cs) [] (smaller (tauSound member)))))
  go [] (v ∷ ss) {s = s} (Backend.acc smaller) = map′ forward (backward right)
    ((no λ ()) ⊎-dec
      (map′ next (λ { (next branch) → branch })
        (Backend.any∈? (after s (embedServer v)) (λ member → decide [] ss _)) ⊎-dec
        Backend.any∈? (tauTargets s [] (v ∷ ss)) (λ member → go [] (v ∷ ss) (smaller (tauSound member)))))
  go (c ∷ cs) (v ∷ ss) {s = s} (Backend.acc smaller) = map′ forward (backward left)
    (map′ next (λ { (next branch) → branch })
      (Backend.any∈? (after s (embedClient c)) (λ member → decide cs (v ∷ ss) _)) ⊎-dec
      (map′ next (λ { (next branch) → branch })
        (Backend.any∈? (after s (embedServer v)) (λ member → decide (c ∷ cs) ss _)) ⊎-dec
        Backend.any∈? (tauTargets s (c ∷ cs) (v ∷ ss)) (λ member → go (c ∷ cs) (v ∷ ss) (smaller (tauSound member)))))

-- The original public engine retains its original successor order by transparent instantiation.
module Decider {ℓs ℓe ℓr ℓc ℓv : Level}
  {S : Set ℓs} {E : Set ℓe} {Client : Set ℓc} {Server : Set ℓv}
  (R : Replay ℓr S E) (embedClient : Client → E) (embedServer : Server → E)
  (accessible : ∀ s → Existing.Decider.τAcc R s) =
  OrderedDecider R embedClient embedServer accessible
    (λ s _ _ → Replay.taus R s)
    (Replay.taus-sound R) (Replay.taus-complete R)
