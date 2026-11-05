{-# OPTIONS --safe #-}

-- Two ordered endpoint prefixes describe an existential merge, never a chosen timestamp order.
module Semantics.Replay.TwoList where

open import Level using (Level; _⊔_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Semantics.Replay using (Replay)

-- Embeddings preserve the caller's event identities; disjointness and injectivity are unnecessary.
module Traces {ℓs ℓe ℓr ℓc ℓv : Level}
  {S : Set ℓs} {E : Set ℓe} {Client : Set ℓc} {Server : Set ℓv}
  (R : Replay ℓr S E) (embedClient : Client → E) (embedServer : Server → E) where
  open Replay R
  module Single = Semantics.Replay.Traces R

  -- A run consumes exactly the two endpoint lists, preserving order within each endpoint.
  data PairRun : S → List Client → List Server → S → Set (ℓs ⊔ ℓe ⊔ ℓr ⊔ ℓc ⊔ ℓv) where
    done : ∀ {s} → PairRun s [] [] s
    tau : ∀ {s t u cs ss} → s -τ→ t → PairRun t cs ss u → PairRun s cs ss u
    client : ∀ {s t u c cs ss} → s -[ embedClient c ]→ t →
      PairRun t cs ss u → PairRun s (c ∷ cs) ss u
    server : ∀ {s t u cs v ss} → s -[ embedServer v ]→ t →
      PairRun t cs ss u → PairRun s cs (v ∷ ss) u

  -- Prefix acceptance retains an actual endpoint; it does not require return or quiescence.
  PairTrace : S → List Client → List Server → Set (ℓs ⊔ ℓe ⊔ ℓr ⊔ ℓc ⊔ ℓv)
  PairTrace s cs ss = Σ[ t ∈ S ] PairRun s cs ss t

  -- Merge records the endpoint choice at every position, even if the embeddings overlap.
  data Merge : List Client → List Server → List E → Set (ℓe ⊔ ℓc ⊔ ℓv) where
    empty : Merge [] [] []
    client : ∀ {c cs ss es} → Merge cs ss es → Merge (c ∷ cs) ss (embedClient c ∷ es)
    server : ∀ {cs v ss es} → Merge cs ss es → Merge cs (v ∷ ss) (embedServer v ∷ es)

  -- Every paired witness supplies its concrete merged history and the identical raw weak run.
  merge-run : ∀ {s cs ss t} → PairRun s cs ss t →
    Σ[ es ∈ List E ] (Merge cs ss es × Single._⇒⟨_⟩_ s es t)
  merge-run done = [] , empty , Single.done
  merge-run (tau step rest) with merge-run rest
  ... | es , merged , raw = es , merged , Single.tau step raw
  merge-run (client {c = c} step rest) with merge-run rest
  ... | es , merged , raw = embedClient c ∷ es , client merged , Single.vis step raw
  merge-run (server {v = v} step rest) with merge-run rest
  ... | es , merged , raw = embedServer v ∷ es , server merged , Single.vis step raw

  -- Merge evidence directs each visible raw step without guessing an unspecified shuffle.
  split-run : ∀ {s cs ss es t} → Merge cs ss es → Single._⇒⟨_⟩_ s es t → PairRun s cs ss t
  split-run merged (Single.tau step rest) = tau step (split-run merged rest)
  split-run empty Single.done = done
  split-run (client merged) (Single.vis step rest) = client step (split-run merged rest)
  split-run (server merged) (Single.vis step rest) = server step (split-run merged rest)

  -- The single-list formulation explicitly existentially quantifies its order-preserving merge.
  MergedTrace : S → List Client → List Server → Set (ℓs ⊔ ℓe ⊔ ℓr ⊔ ℓc ⊔ ℓv)
  MergedTrace s cs ss = Σ[ es ∈ List E ] (Merge cs ss es × Single.HasTrace s es)

  -- Paired acceptance constructs the selected merged history instead of assuming one in advance.
  to-merged : ∀ {s cs ss} → PairTrace s cs ss → MergedTrace s cs ss
  to-merged (target , run) with merge-run run
  ... | es , merged , raw = es , merged , target , raw

  -- Every witnessed merged weak trace preserves the exact supplied endpoint lists.
  from-merged : ∀ {s cs ss} → MergedTrace s cs ss → PairTrace s cs ss
  from-merged (es , merged , target , raw) = target , split-run merged raw

  -- The equivalence retains finite-prefix semantics on both sides, including silent trailing steps.
  equivalence : ∀ s cs ss → (PairTrace s cs ss → MergedTrace s cs ss) ×
    (MergedTrace s cs ss → PairTrace s cs ss)
  equivalence s cs ss = to-merged , from-merged
