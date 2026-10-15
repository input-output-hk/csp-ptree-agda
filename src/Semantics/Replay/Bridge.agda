{-# OPTIONS --guardedness #-}

-- Generic bridge between the √-free weak traces `_⟹∖√⟨_⟩_` of a PTree model
-- and the weak traces `_⇒⟨_⟩_` of a `Replay` spec (trace-replay Phase 5).
-- Model events are classified by `cls` (nothing = unlogged, i.e. silent for
-- the replay); spec events are compared after `forget`.  `Sim` gives
-- soundness (model ⊆ spec) by induction on `⟹∖√`, `CoSim` gives completeness
-- (spec ⊆ model, under a per-event premise) by induction on `⇒⟨⟩`.
-- Model-agnostic: no CSP operator is mentioned.
-- Invariant 1 (B7a): checked with `agda --safe` on the command line.
module Semantics.Replay.Bridge {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.List using (List; []; _∷_; _++_; map; mapMaybe)
open import Data.List.Properties using (mapMaybe-++; map-++)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong₂)

open import Process_Trees using (PTree)
open import Semantics.LTS {ℓ} {ℓe} {ℓi} {E} {I} using (Event; _─[_]─►_; ev; evl; τ)
open import Semantics.Deadlock {ℓ} {ℓe} {ℓi} {E} {I}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Semantics.Replay using (Replay; module Traces)

-- concatenation of √-free runs
⟹∖√-++ : ∀ {ℓr} {R : Set ℓr} {p q r : PTree E I R} {s t : List Event}
        → p ⟹∖√⟨ s ⟩ q → q ⟹∖√⟨ t ⟩ r → p ⟹∖√⟨ s ++ t ⟩ r
⟹∖√-++ ∖√-refl         q = q
⟹∖√-++ (∖√-τ  st run) q = ∖√-τ  st (⟹∖√-++ run q)
⟹∖√-++ (∖√-ev st run) q = ∖√-ev st (⟹∖√-++ run q)

-- the model trace t and the spec trace es agree on what the log sees
Obs : ∀ {ℓv ℓb} {Ev : Set ℓv} {E♭ : Set ℓb}
    → (Event → Maybe E♭) → (Ev → E♭) → List Event → List Ev → Set ℓb
Obs cls forget t es = mapMaybe cls t ≡ map forget es

-- observations concatenate
Obs-++ : ∀ {ℓv ℓb} {Ev : Set ℓv} {E♭ : Set ℓb} (cls : Event → Maybe E♭) (forget : Ev → E♭)
       → ∀ t t′ {es es′} → Obs cls forget t es → Obs cls forget t′ es′
       → Obs cls forget (t ++ t′) (es ++ es′)
Obs-++ cls forget t t′ {es} {es′} o o′ =
  trans (mapMaybe-++ cls t t′) (trans (cong₂ _++_ o o′) (sym (map-++ forget es es′)))

module _ {ℓr ℓs ℓv ℓq ℓb : Level} {R : Set ℓr} {S : Set ℓs} {Ev : Set ℓv} {E♭ : Set ℓb}
         (Rp : Replay ℓq S Ev) (cls : Event → Maybe E♭) (forget : Ev → E♭) where
  open Replay Rp using (_-[_]→_; _-τ→_)
  open Traces Rp using (_⇒⟨_⟩_; done; tau; vis; ⇒-++)

  -- the observation relation at this classifier
  Obs′ : List Event → List Ev → Set ℓb
  Obs′ = Obs cls forget

  -- a simulation of the model by the spec: each model step is matched by a
  -- spec run with the same observation (none for τ)
  record Sim {ℓρ} (Rel : PTree E I R → S → Set ℓρ)
         : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs ⊔ ℓv ⊔ ℓq ⊔ ℓb ⊔ ℓρ) where
    field
      -- a model τ is matched by a silent spec run
      sim-τ  : ∀ {P P′ s} → Rel P s → P ─[ τ ]─► P′
             → Σ[ s′ ∈ S ] (s ⇒⟨ [] ⟩ s′ × Rel P′ s′)
      -- a model event is matched by a spec run observing the same
      sim-ev : ∀ {P P′ s e} → Rel P s → P ─[ ev (evl e) ]─► P′
             → Σ[ es ∈ List Ev ] Σ[ s′ ∈ S ] (Obs′ (e ∷ []) es × s ⇒⟨ es ⟩ s′ × Rel P′ s′)

  -- SOUNDNESS: every √-free model run is observed as a spec run
  sound : ∀ {ℓρ} {Rel : PTree E I R → S → Set ℓρ} → Sim Rel
        → ∀ {P P′ s t} → Rel P s → P ⟹∖√⟨ t ⟩ P′
        → Σ[ es ∈ List Ev ] Σ[ s′ ∈ S ] (Obs′ t es × s ⇒⟨ es ⟩ s′ × Rel P′ s′)
  sound sm r ∖√-refl = [] , _ , refl , done , r
  sound sm r (∖√-τ st run) with Sim.sim-τ sm r st
  ... | s₁ , p₁ , r₁ with sound sm r₁ run
  ...   | es , s′ , o , p , r′ = es , s′ , o , ⇒-++ p₁ p , r′
  sound sm r (∖√-ev {s = t₂} {e = e} st run) with Sim.sim-ev sm r st
  ... | es₁ , s₁ , o₁ , p₁ , r₁ with sound sm r₁ run
  ...   | es , s′ , o , p , r′ = es₁ ++ es , s′ , Obs-++ cls forget (e ∷ []) t₂ o₁ o , ⇒-++ p₁ p , r′

  -- a co-simulation: each spec step whose event satisfies `Pre` is matched by a
  -- √-free model run with the same observation (none for τ)
  record CoSim {ℓρ ℓπ} (Rel : PTree E I R → S → Set ℓρ) (Pre : Ev → Set ℓπ)
         : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs ⊔ ℓv ⊔ ℓq ⊔ ℓb ⊔ ℓρ ⊔ ℓπ) where
    field
      -- a spec τ is matched by a model run observing nothing
      co-τ  : ∀ {P s s′} → Rel P s → s -τ→ s′
            → Σ[ P′ ∈ PTree E I R ] Σ[ t ∈ List Event ]
                (P ⟹∖√⟨ t ⟩ P′ × Obs′ t [] × Rel P′ s′)
      -- a spec event (with its premise) is matched by a model run observing it
      co-ev : ∀ {P s s′ e} → Rel P s → Pre e → s -[ e ]→ s′
            → Σ[ P′ ∈ PTree E I R ] Σ[ t ∈ List Event ]
                (P ⟹∖√⟨ t ⟩ P′ × Obs′ t (e ∷ []) × Rel P′ s′)

  -- COMPLETENESS: every spec run whose events satisfy `Pre` is observed as a model run
  complete : ∀ {ℓρ ℓπ} {Rel : PTree E I R → S → Set ℓρ} {Pre : Ev → Set ℓπ}
           → CoSim Rel Pre
           → ∀ {P s s′ es} → Rel P s → All Pre es → s ⇒⟨ es ⟩ s′
           → Σ[ P′ ∈ PTree E I R ] Σ[ t ∈ List Event ]
               (P ⟹∖√⟨ t ⟩ P′ × Obs′ t es × Rel P′ s′)
  complete cs r ps done = _ , [] , ∖√-refl , refl , r
  complete cs r ps (tau st p) with CoSim.co-τ cs r st
  ... | P₁ , t₁ , run₁ , o₁ , r₁ with complete cs r₁ ps p
  ...   | P′ , t , run , o , r′ = P′ , t₁ ++ t , ⟹∖√-++ run₁ run , Obs-++ cls forget t₁ t o₁ o , r′
  complete cs r (pe ∷ ps) (vis st p) with CoSim.co-ev cs r pe st
  ... | P₁ , t₁ , run₁ , o₁ , r₁ with complete cs r₁ ps p
  ...   | P′ , t , run , o , r′ = P′ , t₁ ++ t , ⟹∖√-++ run₁ run , Obs-++ cls forget t₁ t o₁ o , r′
