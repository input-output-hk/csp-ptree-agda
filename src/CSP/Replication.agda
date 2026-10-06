{-# OPTIONS --guardedness #-}

-- Native lazy replication (ProVerif `!P ≡ P | !P`).
--
-- `Rep merge P k Q` stands for  Q ∥ P k ∥ P (suc k) ∥ …  (interleaved, empty alphabet).
-- `Q` holds the copies already started; a FRESH copy `P k` is spawned lazily on its
-- first step (visible or τ), into `Rep merge P (suc k) (Par ∅ES merge Q P′)`.  Copies are
-- named in SPAWN ORDER: the j-th copy to start is `P j` (ProVerif's `new` at spawn).
--
-- WHY THIS SHAPE.  `!P = P ⦀ !P` puts the corecursive call in an ARGUMENT of a defined
-- function, which --guardedness refuses even with an event in between (measured; see
-- `Security/Compose.agda` ruling R31).  Here the operator sits inside the corecursive
-- call's STATE argument and every corecursive call is directly under `just`.
--
-- BEHAVIOUR TO KNOW.  A `ret` copy contributes nothing (its √ is dropped); a `ret` FRESH
-- copy is never spawned, which blocks every later copy — `!⦀ (λ _ → Skip)` is `Stop`-like.
-- A fresh copy's τ spawns it, so a `P` with an initial τ makes `Rep` DIVERGE
-- (`CSP.Laws.DivFree.Replication.Rep-unguarded-diverges`).  A same-event collision between
-- the running copies and the fresh copy is resolved by an inline 2-way τ node, the
-- `par-pVis` idiom (`CSP/Operators.agda`, both-offer case of `par-pVis`).

open import Level using (Level; Lift; lift)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Process_Trees

module CSP.Replication {ℓ ℓe} {E : Set ℓ → Set ℓe}
                       (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open PTree
open import CSP.Operators E-≟

module _ {ℓr} {R : Set ℓr} (merge : R → R → R) where

  -- the process type the combinator lives in
  private
    T : Set _
    T = PTree E (ExtI E) R

  -- Rep P k Q ≈ Q ∥ P k ∥ P (suc k) ∥ …; a fresh copy joins Q on its first step
  Rep : (ℕ → T) → ℕ → T → T

  -- both-offer collision: inline internal choice (branch 0 = running copies, 1 = fresh copy)
  rep-brBoth : (ℕ → T) → ℕ → T → T → T
             → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe T)

  -- visible offers: running copies (Q) or the fresh copy (P k)
  rep-vis : NodeKind E (ExtI E) R → NodeKind E (ExtI E) R
          → (ℕ → T) → ℕ → T
          → (at : AnyTypes E) → ContinueType at (Maybe T)

  -- τ: tag 0 = a running copy's τ, tag 1 = the fresh copy's τ (which spawns it)
  rep-tau : NodeKind E (ExtI E) R → NodeKind E (ExtI E) R
          → (ℕ → T) → ℕ → T
          → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe T)

  rep-brBoth P k Q Q′ P′ (_ , fin) (lift fzero)        = just (Rep P k Q′)
  rep-brBoth P k Q Q′ P′ (_ , fin) (lift (fsuc fzero)) = just (Rep P (suc k) (Par ∅ES merge Q P′))
  rep-brBoth P k Q Q′ P′ (_ , fin) _                   = nothing
  rep-brBoth P k Q Q′ P′ (_ , base _)   _              = nothing
  rep-brBoth P k Q Q′ P′ (_ , pair _ _) _              = nothing

  rep-vis nQ nP P k Q at a with viewV nQ at a | viewV nP at a
  ... | just Q′ | nothing = just (Rep P k Q′)
  ... | nothing | just P′ = just (Rep P (suc k) (Par ∅ES merge Q P′))
  ... | just Q′ | just P′ = just (ptree (react (λ _ _ → nothing) (rep-brBoth P k Q Q′ P′)))
  ... | nothing | nothing = nothing

  rep-tau nQ nP P k Q (_ , base _)            _ = nothing
  rep-tau nQ nP P k Q (_ , fin)               _ = nothing
  rep-tau nQ nP P k Q (_ , pair (base _) _)   _ = nothing
  rep-tau nQ nP P k Q (_ , pair (pair _ _) _) _ = nothing
  rep-tau nQ nP P k Q (_ , pair fin i) (lift fzero , a) with viewT nQ (_ , i) a
  ... | just Q′ = just (Rep P k Q′)
  ... | nothing = nothing
  rep-tau nQ nP P k Q (_ , pair fin i) (lift (fsuc fzero) , a) with viewT nP (_ , i) a
  ... | just P′ = just (Rep P (suc k) (Par ∅ES merge Q P′))
  ... | nothing = nothing
  rep-tau nQ nP P k Q (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = nothing

  -- ret nodes contribute nothing (viewV/viewT of ret are empty); Rep itself never terminates
  force (Rep P k Q) = react (rep-vis (force Q) (force (P k)) P k Q)
                            (rep-tau (force Q) (force (P k)) P k Q)

  -- ProVerif `!`: no copy started yet, the first spawn is named 0
  ! : (ℕ → T) → T
  ! P = Rep P 0 Stop

-- interleaving instance at the polymorphic unit, so `Par ∅ES merge Q P′` is `Q ⦀ P′` on the nose
Rep⦀ : ∀ {ℓr} → (ℕ → PTree E (ExtI E) (⊤ {ℓr})) → ℕ
     → PTree E (ExtI E) (⊤ {ℓr}) → PTree E (ExtI E) (⊤ {ℓr})
Rep⦀ = Rep (λ _ _ → tt)

-- `!` at the interleaving instance
!⦀ : ∀ {ℓr} → (ℕ → PTree E (ExtI E) (⊤ {ℓr})) → PTree E (ExtI E) (⊤ {ℓr})
!⦀ P = Rep⦀ P 0 Stop

-- uniform replication: every copy is the same process
!ᶜ : ∀ {ℓr} → PTree E (ExtI E) (⊤ {ℓr}) → PTree E (ExtI E) (⊤ {ℓr})
!ᶜ P = !⦀ (λ _ → P)
