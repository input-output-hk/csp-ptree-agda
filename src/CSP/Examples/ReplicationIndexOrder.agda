{-# OPTIONS --guardedness #-}

-- D2 negative control: with index-dependent copies the naive unfold `!P ≈ P 0 ⦀ Rep P 1 Stop`
-- is FALSE even at traces — copies start in spawn order, so copy 1 cannot move first.
-- Also the frame law's non-vacuity instance on the same copies (`frame-Pt`, singleton alphabets).

open import Level using () renaming (zero to lzero)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties as ℕP
open import Data.List using (List; []; _∷_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

open import Process_Trees

module CSP.Examples.ReplicationIndexOrder where

open PTree

-- one ℕ-indexed ⊤-carried event per copy
data EvN : Set → Set where
  tick : ℕ → EvN ⊤

-- decidable equality on the event index
EvN-≟ : (x y : AnyTypes EvN) → Dec (x ≡ y)
EvN-≟ (_ , tick m) (_ , tick n) with ℕP._≟_ m n
... | yes refl = yes refl
... | no  m≢n  = no λ { refl → m≢n refl }

open import CSP.Operators EvN-≟
open import CSP.Replication EvN-≟
open import Semantics.Failures {E = EvN} {I = ExtI EvN} using (traces; _⊇T_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.LTS {E = EvN} {I = ExtI EvN}
  using (Event√; evl; evLabel; sVis; sSil; sTau)
open import CSP.Laws.Traces.TraceLawsParallelMono EvN-≟ using (Par-soloR-reach)
open import CSP.Laws.Traces.ReplicationSteps EvN-≟

-- copy j offers only its own tick
Pt : ℕ → PTree EvN (ExtI EvN) (⊤ {lzero})
Pt j = tick j ⟶₀ Stop

-- the trace label of copy 1's tick
tick1 : Event√ (⊤ {lzero})
tick1 = evl (evLabel ⊤ (tick 1) tt)

-- the naive unfold has ⟨tick 1⟩: its right operand's fresh copy (copy 1) fires at once
rhs-has : traces (Pt 0 ⦀ Rep⦀ Pt 1 Stop) (tick1 ∷ [])
rhs-has = _ , Par-soloR-reach ∅ES (λ _ _ → tt) (Pt 0) (Rep⦀ Pt 1 Stop) (λ z → z)
                (Rep-evFresh-intro (λ _ _ → tt) Pt 1 Stop (sVis refl refl) refl) ⟹-refl

-- `!⦀ Pt` lacks ⟨tick 1⟩: it has no τ (neither `Stop` nor `Pt 0` has one), `Stop` offers
-- nothing, and the fresh copy `Pt 0` offers only `tick 0`
lhs-lacks : ¬ traces (!⦀ Pt) (tick1 ∷ [])
lhs-lacks (_ , ⟹-τ st _) with Rep-τ-elim (λ _ _ → tt) Pt 0 Stop st
... | τRun   (sSil ())
... | τRun   (sTau refl ())
... | τFresh (sSil ())
... | τFresh (sTau refl ())
lhs-lacks (_ , ⟹-ev st _) with Rep-ev-elim (λ _ _ → tt) Pt 0 Stop st
... | evRun   (sVis refl ()) _
... | evFresh (sVis refl ()) _
... | evBoth  (sVis refl ()) _

-- hence the naive unfold is not trace-contained in `!⦀ Pt`: index order is observable
naive-unfold-fails : ¬ (!⦀ Pt ⊇T (Pt 0 ⦀ Rep⦀ Pt 1 Stop))
naive-unfold-fails h = lhs-lacks (h (tick1 ∷ []) rhs-has)

-------------------------------------------------------------------------------------
-- Non-vacuity of the frame law (`CSP.Laws.Bisim.ReplicationFrame`): its premises are
-- dischargeable on these very copies
-------------------------------------------------------------------------------------

open import Data.Nat using (_≤_)
open import Semantics.Bisim {E = EvN} {I = ExtI EvN} using (_∼_)
open import CSP.Laws.Bisim.DRCongruenceRep EvN-≟ using (Alpha; Disj; OffersOnly-Prefix₀)
open import CSP.Laws.Bisim.ReplicationFrame EvN-≟ using (RepDisj; OffersOnly-Stop; !-frame-∼)

-- copy j's alphabet: its own tick only
αt : ℕ → Alpha
αt j (_ , tick i) _ = i ≡ j

-- distinct copies have disjoint alphabets
αt-disj : ∀ {i j} → i ≢ j → Disj (αt i) (αt j)
αt-disj i≢j (_ , tick _) _ refl refl = i≢j refl

-- the tick copies are confined to their own ticks and pairwise disjoint
rdPt : RepDisj αt Pt
rdPt = record { conf = λ _ → OffersOnly-Prefix₀ (λ _ → refl) OffersOnly-Stop ; disj = αt-disj }

-- copy 0's alphabet misses every copy from 1 on
fresh0 : ∀ j → 1 ≤ j → Disj (αt 0) (αt j)
fresh0 (suc _) _ = αt-disj (λ ())

-- the frame law at work: copy 0, already running, slides out of `Rep⦀ Pt 1`
frame-Pt : Rep⦀ Pt 1 (Pt 0 ⦀ Stop) ∼ (Pt 0 ⦀ Rep⦀ Pt 1 Stop)
frame-Pt = !-frame-∼ rdPt (RepDisj.conf rdPt 0) fresh0
