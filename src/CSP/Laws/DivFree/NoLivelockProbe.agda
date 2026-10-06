{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Stage-G probe: the no-livelock bridge instantiated END TO END on a toy
-- two-process pipe, with BOTH premises discharged (none assumed).
--
--   Left  = inp → mid → Left        Right = mid → out → Right
--   Sys   = Left ∥⇘ M ⇙ Right       M = {| mid |}   (the internal channel)
--
--   (a) every trace of Sys has #mid ≤ #inp ≤ #(non-mid)       (F = id)
--       — via `Par-trace-elim`: mid is synchronised, so Sys's mids are
--       Left's mids; Left's own run invariant gives #mid ≤ #inp
--   (b) τ-accessibility at every reachable state of Sys — via `MAccR-∥`
--   ⇒ `pipe-noLivelock : ∀ {s} → ¬ divergences (Sys ∖ M) s`
--
-- Controls (each premise is load-bearing):
--   * `ctl-a`: `inp → Spin`, Spin = mid → Spin, satisfies (b) (PROVED:
--              `ctl-a-b`) but not (a); hiding mid DIVERGES after ⟨inp⟩.
--   * `ctl-b`: `inp → div` satisfies (a) (PROVED: `ctl-b-a`, no mid at all)
--              but not (b); hiding mid DIVERGES after ⟨inp⟩.
-- No `postulate`, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

module CSP.Laws.DivFree.NoLivelockProbe where

open import Level using (0ℓ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; m≤n⇒m≤1+n)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
import Data.Unit as U
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Process_Trees

------------------------------------------------------------------------
-- The toy alphabet
------------------------------------------------------------------------

-- three unit-carrying channels
data Ev : Set → Set where
  inp mid out : Ev U.⊤

-- decidable equality of channel labels
Ev-≟ : (x y : AnyTypes Ev) → Dec (x ≡ y)
Ev-≟ (_ , inp) (_ , inp) = yes refl
Ev-≟ (_ , inp) (_ , mid) = no λ ()
Ev-≟ (_ , inp) (_ , out) = no λ ()
Ev-≟ (_ , mid) (_ , inp) = no λ ()
Ev-≟ (_ , mid) (_ , mid) = yes refl
Ev-≟ (_ , mid) (_ , out) = no λ ()
Ev-≟ (_ , out) (_ , inp) = no λ ()
Ev-≟ (_ , out) (_ , mid) = no λ ()
Ev-≟ (_ , out) (_ , out) = yes refl

open import CSP.Operators Ev-≟
open EventSet
open import Semantics.LTS {E = Ev} {I = ExtI Ev} hiding (Diverges)
open import Semantics.Failures {E = Ev} {I = ExtI Ev} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.Deadlock {E = Ev} {I = ExtI Ev} using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Semantics.FailuresDivergences {E = Ev} {I = ExtI Ev} using (divergences)
open import Semantics.DivergenceFree {E = Ev} {I = ExtI Ev}
  using (Diverges; τ-Acc; acc; τ-AccReach)
open import CSP.Laws.Traces.TraceLawsHide Ev-≟ using (Hide-keep; Hide-hidden)
open import CSP.Laws.Traces.TraceLawsParallelTrace Ev-≟
  using (Par-trace-elim; ParInter; pnil; psync; psoloL; psoloR; p√)
open import CSP.Laws.FD.NoLivelock Ev-≟ using (#H; #V; noLivelockT)
open import CSP.Laws.DivFree.ModAcc Ev-≟
  using (MAccR; MAccR-mono; τ-AccReach→MAccR∅; MAccR→τ-AccReach; τ-AccReach→noDiv)
open import CSP.Laws.DivFree.Reach Ev-≟ using (MAccR-∥)
open import CSP.Laws.DivFree.Loop Ev-≟ using (MAccR-⟶₀)

-- the process type of the probe
Proc : Set₁
Proc = PTree Ev (ExtI Ev) (⊤ {0ℓ})

------------------------------------------------------------------------
-- Event sets
------------------------------------------------------------------------

-- membership in {| mid |}
isMid : AnyTypes Ev → Set
isMid (_ , mid) = U.⊤
isMid _         = ⊥

-- … decided by cases, so that counts REDUCE on concrete events
isMid? : (at : AnyTypes Ev) → Dec (isMid at)
isMid? (_ , inp) = no λ ()
isMid? (_ , mid) = yes U.tt
isMid? (_ , out) = no λ ()

-- membership in {| inp |}
isInp : AnyTypes Ev → Set
isInp (_ , inp) = U.⊤
isInp _         = ⊥

-- … decided by cases
isInp? : (at : AnyTypes Ev) → Dec (isInp at)
isInp? (_ , inp) = yes U.tt
isInp? (_ , mid) = no λ ()
isInp? (_ , out) = no λ ()

-- the hidden (= synchronised) channel
M : EventSet
M = chanSet isMid isMid?

-- the input channel (used only for counting)
I : EventSet
I = chanSet isInp isInp?

------------------------------------------------------------------------
-- The pipe (direct corecursion; forward declarations)
------------------------------------------------------------------------

-- Left: inp then mid, forever
Left  : Proc
-- Left after its inp
Left′ : Proc
-- Right: mid then out, forever
Right  : Proc
-- Right after its mid
Right′ : Proc

PTree.force Left   = react (λ { (_ , inp) _ → just Left′  ; _ _ → nothing }) ∅t
PTree.force Left′  = react (λ { (_ , mid) _ → just Left   ; _ _ → nothing }) ∅t
PTree.force Right  = react (λ { (_ , mid) _ → just Right′ ; _ _ → nothing }) ∅t
PTree.force Right′ = react (λ { (_ , out) _ → just Right  ; _ _ → nothing }) ∅t

-- the composite
Sys : Proc
Sys = Left ∥⇘ M ⇙ Right

------------------------------------------------------------------------
-- Premise (b): τ-accessible at every reachable state
------------------------------------------------------------------------

-- `nothing` is not `just`
nothing≢just : ∀ {X : Set₁} {t : Proc} → nothing ≡ just t → X
nothing≢just ()

-- `∅t` has no τ-branch
absurd-τ : ∀ {X : Set₁} {t : Proc} {v v′ τc i a t′} → PTree.force t ≡ react v ∅t
         → PTree.force t ≡ react v′ τc → τc i a ≡ just t′ → X
absurd-τ {i = i} {a} eqf eqr br =
  nothing≢just (trans (sym (cong (λ g → g i a) (proj₂ (react-injective (trans (sym eqr) eqf))))) br)

-- `sil` is not `react`
absurd-sil : ∀ {X : Set₁} {t c : Proc} {v} → PTree.force t ≡ react v ∅t → PTree.force t ≡ sil c → X
absurd-sil eqf eqs = ⊥-elim (sil≢react (trans (sym eqs) eqf))

-- the four states are stable menus: a stable node is τ-accessible
stable-acc : {t : Proc} {v : (at : AnyTypes Ev) → ContinueType at (Maybe Proc)}
           → PTree.force t ≡ react v ∅t → τ-Acc t
stable-acc {t = t} eqf = acc λ where
  (sSil eqs)      → absurd-sil {t = t} eqf eqs
  (sTau eqr br)   → absurd-τ {t = t} eqf eqr br

-- reachable states of Left / Left′ (forward declarations)
reachL  : τ-AccReach Left
reachL′ : τ-AccReach Left′

reachL ∖√-refl = stable-acc refl
reachL (∖√-τ (sTau refl ()) _)
reachL (∖√-ev (sVis {at = _ , inp} refl refl) r) = reachL′ r
reachL (∖√-ev (sVis {at = _ , mid} refl ()) _)
reachL (∖√-ev (sVis {at = _ , out} refl ()) _)

reachL′ ∖√-refl = stable-acc refl
reachL′ (∖√-τ (sTau refl ()) _)
reachL′ (∖√-ev (sVis {at = _ , inp} refl ()) _)
reachL′ (∖√-ev (sVis {at = _ , mid} refl refl) r) = reachL r
reachL′ (∖√-ev (sVis {at = _ , out} refl ()) _)

-- reachable states of Right / Right′ (forward declarations)
reachR  : τ-AccReach Right
reachR′ : τ-AccReach Right′

reachR ∖√-refl = stable-acc refl
reachR (∖√-τ (sTau refl ()) _)
reachR (∖√-ev (sVis {at = _ , inp} refl ()) _)
reachR (∖√-ev (sVis {at = _ , mid} refl refl) r) = reachR′ r
reachR (∖√-ev (sVis {at = _ , out} refl ()) _)

reachR′ ∖√-refl = stable-acc refl
reachR′ (∖√-τ (sTau refl ()) _)
reachR′ (∖√-ev (sVis {at = _ , inp} refl ()) _)
reachR′ (∖√-ev (sVis {at = _ , mid} refl ()) _)
reachR′ (∖√-ev (sVis {at = _ , out} refl refl) r) = reachR r

-- premise (b) for the composite, through the parallel closure (H = ∅ES)
Sys-τ-AccReach : τ-AccReach Sys
Sys-τ-AccReach =
  MAccR→τ-AccReach
    (MAccR-∥ M ∅ES (τ-AccReach→MAccR∅ reachL)
                   (MAccR-mono (λ at a m → proj₁ m) (τ-AccReach→MAccR∅ reachR)))

------------------------------------------------------------------------
-- Premise (a): #mid ≤ #inp ≤ #visible on every trace of Sys
------------------------------------------------------------------------

private
  -- the trace alphabet of the probe
  Tr : Set₁
  Tr = List (Event√ (⊤ {0ℓ}))

-- Left's run invariant (forward declarations)
invL  : ∀ {s : Tr} {Q} → Left  ⟹⟨ s ⟩ Q → #H M s ≤ #H I s
invL′ : ∀ {s : Tr} {Q} → Left′ ⟹⟨ s ⟩ Q → #H M s ≤ suc (#H I s)

invL ⟹-refl = z≤n
invL (⟹-τ (sTau refl ()) _)
invL (⟹-ev (sVis {at = _ , inp} refl refl) r) = invL′ r
invL (⟹-ev (sVis {at = _ , mid} refl ()) _)
invL (⟹-ev (sVis {at = _ , out} refl ()) _)

invL′ ⟹-refl = z≤n
invL′ (⟹-τ (sTau refl ()) _)
invL′ (⟹-ev (sVis {at = _ , inp} refl ()) _)
invL′ (⟹-ev (sVis {at = _ , mid} refl refl) r) = s≤s (invL r)
invL′ (⟹-ev (sVis {at = _ , out} refl ()) _)

-- one more event never lowers a count, on both sides
#H-cons : (X : EventSet) (s s′ : Tr) (e : Event√ (⊤ {0ℓ}))
        → #H X s ≤ #H X s′ → #H X (e ∷ s) ≤ #H X (e ∷ s′)
#H-cons X s s′ (evl (evLabel B e a)) le with X .dec (B , e) a
... | yes _ = s≤s le
... | no  _ = le
#H-cons X s s′ (√ _) le = le

-- … and the right side may gain one
#H-step : (X : EventSet) (s s′ : Tr) (e : Event√ (⊤ {0ℓ}))
        → #H X s ≤ #H X s′ → #H X s ≤ #H X (e ∷ s′)
#H-step X s s′ (evl (evLabel B e a)) le with X .dec (B , e) a
... | yes _ = m≤n⇒m≤1+n le
... | no  _ = le
#H-step X s s′ (√ _) le = le

-- a synchronised channel's events in s are exactly the left operand's
countSync : ∀ {mg} {sP sQ s : Tr} → ParInter M mg sP sQ s → #H M s ≤ #H M sP
countSync pnil = z≤n
countSync (psync {X = X} {e = e} {a = a} {sP = sP} {s = s} m∈ i) =
  #H-cons M s sP (evl (evLabel X e a)) (countSync i)
countSync (psoloL {X = X} {e = e} {a = a} {sP = sP} {s = s} m∉ i) =
  #H-cons M s sP (evl (evLabel X e a)) (countSync i)
countSync (psoloR {X = X} {e = e} {a = a} m∉ i) with M .dec (X , e) a
... | yes m = ⊥-elim (m∉ m)
... | no  _ = countSync i
countSync p√ = z≤n

-- every event of the left operand's trace is in s
countSub : ∀ {mg} (X : EventSet) {sP sQ s : Tr} → ParInter M mg sP sQ s → #H X sP ≤ #H X s
countSub X pnil = z≤n
countSub X (psync {X = Y} {e = e} {a = a} {sP = sP} {s = s} _ i) =
  #H-cons X sP s (evl (evLabel Y e a)) (countSub X i)
countSub X (psoloL {X = Y} {e = e} {a = a} {sP = sP} {s = s} _ i) =
  #H-cons X sP s (evl (evLabel Y e a)) (countSub X i)
countSub X (psoloR {X = Y} {e = e} {a = a} {sP = sP} {s = s} _ i) =
  #H-step X sP s (evl (evLabel Y e a)) (countSub X i)
countSub X p√ = ≤-refl

-- inp is never mid, so inputs are visible
inp≤vis : (s : Tr) → #H I s ≤ #V M s
inp≤vis [] = z≤n
inp≤vis (evl (evLabel _ inp a) ∷ s) = s≤s (inp≤vis s)
inp≤vis (evl (evLabel _ mid a) ∷ s) = inp≤vis s
inp≤vis (evl (evLabel _ out a) ∷ s) = m≤n⇒m≤1+n (inp≤vis s)
inp≤vis (√ _ ∷ s) = m≤n⇒m≤1+n (inp≤vis s)

-- PREMISE (a), F = id
Sys-bound : ∀ {s : Tr} {Q} → Sys ⟹⟨ s ⟩ Q → #H M s ≤ #V M s
Sys-bound {s} r with Par-trace-elim M (λ _ _ → tt) Left Right r
... | sP , sQ , P′ , Q′ , rP , rQ , inter =
  ≤-trans (countSync inter)
    (≤-trans (invL rP) (≤-trans (countSub I inter) (inp≤vis s)))

------------------------------------------------------------------------
-- THE PROBE THEOREM
------------------------------------------------------------------------

-- hiding the pipe's internal channel creates no divergence, at any trace
pipe-noLivelock : ∀ {s} → ¬ divergences (Sys ∖ M) s
pipe-noLivelock = noLivelockT M (λ m → m) Sys-bound (τ-AccReach→noDiv Sys-τ-AccReach)

------------------------------------------------------------------------
-- Controls: each premise is load-bearing
------------------------------------------------------------------------

-- Spin: mid forever
Spin : Proc
PTree.force Spin = react (λ { (_ , mid) _ → just Spin ; _ _ → nothing }) ∅t

-- `Spin ∖ M` takes a hidden mid forever
Spin∖M-diverges : Diverges (Spin ∖ M)
Spin∖M-diverges .Diverges.next = Spin ∖ M
Spin∖M-diverges .Diverges.step = Hide-hidden M Spin {e = mid} {a = U.tt} U.tt (sVis refl refl)
Spin∖M-diverges .Diverges.rest = Spin∖M-diverges

-- control (a): stable everywhere, yet hiding mid diverges after ⟨inp⟩
ctl-a : divergences ((inp ⟶₀ Spin) ∖ M) (evl (evLabel U.⊤ inp U.tt) ∷ [])
ctl-a = record
  { prefix = evl (evLabel U.⊤ inp U.tt) ∷ [] ; suffix = [] ; split = refl
  ; witness = Spin ∖ M
  ; reach = ⟹-ev (Hide-keep M (inp ⟶₀ Spin) (λ ()) (sVis refl refl)) ⟹-refl
  ; divwit = Spin∖M-diverges }

-- `div ∖ M` diverges (div's own τ)
div∖M-diverges : Diverges (div {E = Ev} {I = ExtI Ev} {R = ⊤ {0ℓ}} ∖ M)
div∖M-diverges .Diverges.next = div ∖ M
div∖M-diverges .Diverges.step = sSil refl
div∖M-diverges .Diverges.rest = div∖M-diverges

-- control (b): no mid at all, yet hiding diverges after ⟨inp⟩ (div is reachable)
ctl-b : divergences ((inp ⟶₀ div) ∖ M) (evl (evLabel U.⊤ inp U.tt) ∷ [])
ctl-b = record
  { prefix = evl (evLabel U.⊤ inp U.tt) ∷ [] ; suffix = [] ; split = refl
  ; witness = div ∖ M
  ; reach = ⟹-ev (Hide-keep M (inp ⟶₀ div) (λ ()) (sVis refl refl)) ⟹-refl
  ; divwit = div∖M-diverges }

-- Spin is τ-accessible at every reachable state (its only move is mid)
reachS : τ-AccReach Spin
reachS ∖√-refl = stable-acc refl
reachS (∖√-τ (sTau refl ()) _)
reachS (∖√-ev (sVis {at = _ , inp} refl ()) _)
reachS (∖√-ev (sVis {at = _ , mid} refl refl) r) = reachS r
reachS (∖√-ev (sVis {at = _ , out} refl ()) _)

-- control (a)'s process satisfies premise (b): no reachable state diverges
ctl-a-b : ∀ {s Q} → (inp ⟶₀ Spin) ⟹⟨ s ⟩ Q → ¬ Diverges Q
ctl-a-b = τ-AccReach→noDiv (MAccR→τ-AccReach (MAccR-⟶₀ inp (τ-AccReach→MAccR∅ reachS)))

-- `div` has no visible step, so its traces are empty and satisfy the bound
divTr : ∀ {s : Tr} {Q} → div {E = Ev} {I = ExtI Ev} {R = ⊤ {0ℓ}} ⟹⟨ s ⟩ Q → #H M s ≤ #V M s
divTr ⟹-refl = z≤n
divTr (⟹-τ (sSil refl) r) = divTr r
divTr (⟹-ev (sVis () _) _)
divTr (⟹-ev (sRet ()) _)

-- control (b)'s process satisfies premise (a) at F = id: it never performs mid
ctl-b-a : ∀ {s : Tr} {Q} → (inp ⟶₀ div) ⟹⟨ s ⟩ Q → #H M s ≤ #V M s
ctl-b-a ⟹-refl = z≤n
ctl-b-a (⟹-τ (sTau refl ()) _)
ctl-b-a (⟹-ev (sVis {at = _ , inp} refl refl) r) = m≤n⇒m≤1+n (divTr r)
ctl-b-a (⟹-ev (sVis {at = _ , mid} refl ()) _)
ctl-b-a (⟹-ev (sVis {at = _ , out} refl ()) _)
