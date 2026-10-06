{-# OPTIONS --guardedness #-}

-- One-copy embedding into native replication `Rep` (CSP.Replication), generic result
-- type.  Read `P k` on its own, as an ordinary process with no notion of `Rep` yet --
-- its own run embeds as a trace of `Rep merge P k Stop` (copy `k` spawning as the very
-- first copy, nothing else running), PROVIDED copy `k`'s own transitions never clash
-- with copy `suc k`'s (the next copy `Rep` would spawn once `k` has started): that
-- side condition is `NoClash`.  The run's first step spawns copy `k`
-- (`Rep-τFresh-intro` / `Rep-evFresh-intro`, side-condition-free since the base `Stop`
-- offers nothing); from there the running residual is `Stop ⦀ (copy k's continuation)`,
-- and every later step is a running-copy step (`Rep-τRun-intro` / `Rep-evRun-intro`),
-- lifted through the idle `Stop` by `Par-τ-R` / `Par-soloR`.  `NoClash` rules out the
-- `evBoth` collision case, so `evRun` always applies.  `All IsEvl s` keeps the run
-- √-free, as `Rep` itself is (`Rep-no-√`): copy `k` never actually terminates on this
-- run, so the `Par` operand never needs the ret/merge case.
--
-- Postulates: none used, none in closure (a grep of this module and its imports finds no
-- `postulate`).

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)

open import Process_Trees

module CSP.Laws.Traces.ReplicationEmbedR {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import CSP.Replication E-≟
open import Semantics.LTS {E = E} {I = ExtI E}
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)
open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Par-τ-R; Par-soloR)
open import CSP.Laws.Traces.ReplicationSteps E-≟
  using (ev→viewV; Rep-evRun-intro; Rep-evFresh-intro; Rep-τRun-intro; Rep-τFresh-intro)
open import CSP.Laws.Traces.ReplicationApprox E-≟ using (IsEvl; isEvl; ⟹-++)

-- a step's source state offers that event (nonzero view), whatever its target is
viewV-offers : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree E (ExtI E) R}
               {X : Set ℓ} {e : E X} {a : X}
             → t ─[ ev (evl (evLabel X e a)) ]─► t′ → viewV (force t) (X , e) a ≢ nothing
viewV-offers st eq = case trans (sym (ev→viewV st)) eq of λ ()

module _ {ℓr} {R : Set ℓr} (merge : R → R → R) where

  -- the process type the lemmas of this module talk about
  private
    T : Set _
    T = PTree E (ExtI E) R

  -- after copy k has started, no state reachable from its own run offers a visible
  -- event that copy `suc k` (the next fresh copy `Rep` would spawn) also offers
  -- initially -- the side condition `Rep-evRun-intro` needs to rule out `evBoth`
  NoClash : (ℕ → T) → ℕ → Set _
  NoClash P k = ∀ {s W} → P k ⟹⟨ s ⟩ W
              → ∀ at a → viewV (force W) at a ≢ nothing
              → viewV (force (P (suc k))) at a ≡ nothing

  -- after copy k has spawned, embed the REST of its run: the running residual is
  -- `Stop ⦀ Cur`, reached via `pre` from `P k` (so `NC pre` certifies no clash at Cur)
  embedCopy : (P : ℕ → T) (k : ℕ) → NoClash P k
            → {preS : List (Event√ R)} (Cur : T) → P k ⟹⟨ preS ⟩ Cur
            → {s : List (Event√ R)} {W : T} → Cur ⟹⟨ s ⟩ W → All IsEvl s
            → traces (Rep merge P (suc k) (Par ∅ES merge Stop Cur)) s
  embedCopy P k NC Cur pre ⟹-refl allEvl = _ , ⟹-refl
  embedCopy P k NC Cur pre (⟹-τ {q = Cur′} st rest) allEvl
    with embedCopy P k NC Cur′ (⟹-++ pre (⟹-τ st ⟹-refl)) rest allEvl
  ... | M , run2 =
    M , ⟹-τ (Rep-τRun-intro merge P (suc k) (Par ∅ES merge Stop Cur)
                            (Par-τ-R ∅ES merge Stop Cur st)) run2
  embedCopy P k NC Cur pre (⟹-ev {q = Cur′} st rest) (isEvl _ ∷ restEvl)
    with NC pre _ _ (viewV-offers st)
  ... | np
    with embedCopy P k NC Cur′ (⟹-++ pre (⟹-ev st ⟹-refl)) rest restEvl
  ...   | M , run2 =
    M , ⟹-ev (Rep-evRun-intro merge P (suc k) (Par ∅ES merge Stop Cur)
                              (Par-soloR ∅ES merge Stop Cur (λ ()) st refl) np) run2

  -- a single copy's own run embeds as a trace of `Rep` when it never clashes with the
  -- next copy `Rep` would spawn: the first step spawns copy k, the rest runs it
  Rep-one-copy : (P : ℕ → T) (k : ℕ) → NoClash P k
               → {s : List (Event√ R)} {W : T} → P k ⟹⟨ s ⟩ W → All IsEvl s
               → traces (Rep merge P k Stop) s
  Rep-one-copy P k NC ⟹-refl allEvl = _ , ⟹-refl
  Rep-one-copy P k NC (⟹-τ {q = P′} st rest) allEvl
    with embedCopy P k NC P′ (⟹-τ st ⟹-refl) rest allEvl
  ... | M , run2 = M , ⟹-τ (Rep-τFresh-intro merge P k Stop st) run2
  Rep-one-copy P k NC (⟹-ev {q = P′} st rest) (isEvl _ ∷ restEvl)
    with embedCopy P k NC P′ (⟹-ev st ⟹-refl) rest restEvl
  ... | M , run2 = M , ⟹-ev (Rep-evFresh-intro merge P k Stop st refl) run2
