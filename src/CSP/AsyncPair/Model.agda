{-# OPTIONS --guardedness #-}

-- A concrete asynchronous product of two supplied peer PTrees and payload FIFOs.
open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc)
open import Relation.Binary.Definitions using (DecidableEquality)
open import CSP.AsyncPair.Flow using (Flow; application; send; receive)
import Semantics.LTS
module CSP.AsyncPair.Model
  {ℓ ℓe ℓi ℓr ℓp : Level}
  (E : Set ℓ → Set ℓe) (I : Set ℓ → Set ℓi) (R : Set ℓr)
  (Packet : Set ℓp) (packetEq : DecidableEquality Packet)
  (classify : Semantics.LTS.Event {E = E} {I = I} → Flow Packet) where

open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.Product using (Σ-syntax; _,_; proj₁)
import Data.Maybe.Properties
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Process_Trees using (PTree; AnyTypes; ContinueType; NodeKind; react; ret; sil)
import Semantics.LTS {E = E} {I = I} as Local

-- The supplied peers are never replaced by replay-generated processes.
Proc : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
Proc = PTree E I R

-- Endpoint tags preserve distinct local sends, receives and application events.
data PairEv (A : Set ℓ) : Set ℓe where
  atClient atServer : E A → PairEv A

-- The original silent constructor and indexed silent choices remain distinct.
data OneI : Set ℓ → Set (lsuc ℓ ⊔ ℓi) where
  silence : OneI (Lift ℓ ⊤)
  branch : ∀ {A} → I A → OneI A

-- Both peers may move silently, independently of FIFO communication.
data PairI (A : Set ℓ) : Set (lsuc ℓ ⊔ ℓi) where
  clientI serverI : OneI A → PairI A

-- Concrete channel state retains the complete sent payload, including metadata.
record Queues : Set ℓp where
  constructor queues
  field
    clientToServer serverToClient : List Packet
open Queues public

-- Fresh composition has no uncaptured in-flight messages.
empty : Queues
empty = queues [] []

-- The client medium gate enqueues sends and permits only exact FIFO receives.
clientGate : Local.Event → Queues → Maybe Queues
clientGate e (queues cs sc) with classify e
... | application = just (queues cs sc)
... | send x = just (queues (cs ∷ʳ x) sc)
... | receive x with sc
...   | [] = nothing
...   | y ∷ ys with packetEq x y
...     | yes _ = just (queues cs ys)
...     | no _ = nothing

-- The server gate uses the opposite queue directions.
serverGate : Local.Event → Queues → Maybe Queues
serverGate e (queues cs sc) with classify e
... | application = just (queues cs sc)
... | send x = just (queues cs (sc ∷ʳ x))
... | receive x with cs
...   | [] = nothing
...   | y ∷ ys with packetEq x y
...     | yes _ = just (queues ys sc)
...     | no _ = nothing

-- Observe exactly the offers already present in a peer node.
offers : Proc → (at : AnyTypes E) → ContinueType at (Maybe Proc)
offers t at a with PTree.force t
... | react v τc = v at a
... | ret _ = nothing
... | sil _ = nothing

-- Inspect an original node without introducing any additional peer moves.
silentView : NodeKind E I R →
  (i : AnyTypes OneI) → ContinueType i (Maybe Proc)
silentView (sil u) (_ , silence) _ = just u
silentView (react v τc) (_ , branch i) a = τc (_ , i) a
silentView _ _ _ = nothing

-- Observe the existing silent constructor or indexed silent choice.
silents : Proc → (i : AnyTypes OneI) → ContinueType i (Maybe Proc)
silents t = silentView (PTree.force t)

-- Forward declarations keep recursive continuations beneath the PTree guard.
compose : Proc → Proc → Queues → PTree PairEv PairI ⊤
pairOffers : Proc → Proc → Queues →
  (at : AnyTypes PairEv) → ContinueType at (Maybe (PTree PairEv PairI ⊤))
pairSilents : Proc → Proc → Queues →
  (i : AnyTypes PairI) → ContinueType i (Maybe (PTree PairEv PairI ⊤))

-- The persistent medium never terminates; stopped peers leave a stopped product.
-- Wire/API events remain visible here; only the later observation map hides APIs.
PTree.force (compose c s q) = react (pairOffers c s q) (pairSilents c s q)

-- Visible offers synchronise one peer step with the corresponding FIFO gate.
pairOffers c s q (_ , atClient ch) a with offers c (_ , ch) a | clientGate (Local.evLabel _ ch a) q
... | just c′ | just q′ = just (compose c′ s q′)
... | _ | _ = nothing
pairOffers c s q (_ , atServer ch) a with offers s (_ , ch) a | serverGate (Local.evLabel _ ch a) q
... | just s′ | just q′ = just (compose c s′ q′)
... | _ | _ = nothing

-- A peer silent move preserves both network queues and the other peer.
pairSilents c s q (_ , clientI i) a with silents c (_ , i) a
... | just c′ = just (compose c′ s q)
... | nothing = nothing
pairSilents c s q (_ , serverI i) a with silents s (_ , i) a
... | just s′ = just (compose c s′ q)
... | nothing = nothing

-- A local visible step is equivalent to its original offer-map lookup.
offer-step : ∀ {t u at a} → offers t at a ≡ just u →
  t Local.─[ Local.ev (Local.evl (Local.evLabel (proj₁ at) (Data.Product.proj₂ at) a)) ]─► u
offer-step {t} eq with PTree.force t in forceEq
... | react v τc = Local.sVis forceEq eq
... | ret _ with () ← eq
... | sil _ with () ← eq

-- Local visible transition evidence recovers the exact lookup.
step-offer : ∀ {t u X} {ch : E X} {a} →
  t Local.─[ Local.ev (Local.evl (Local.evLabel X ch a)) ]─► u → offers t (X , ch) a ≡ just u
step-offer (Local.sVis eq br) rewrite eq = br

-- A silent lookup introduces a supplied peer silent transition.
silent-step : ∀ {t u i a} → silents t i a ≡ just u → t Local.─[ Local.τ ]─► u
silent-step {t} {i = _ , silence} eq with PTree.force t in forceEq
... | sil u with refl ← Data.Maybe.Properties.just-injective eq = Local.sSil forceEq
... | ret _ with () ← eq
... | react _ _ with () ← eq
silent-step {t} {i = _ , branch j} eq with PTree.force t in forceEq
... | react v τc = Local.sTau forceEq eq
... | ret _ with () ← eq
... | sil _ with () ← eq

-- Every original peer silent transition has one corresponding index.
step-silent : ∀ {t u} → t Local.─[ Local.τ ]─► u →
  Σ[ i ∈ AnyTypes OneI ] Σ[ a ∈ proj₁ i ] silents t i a ≡ just u
step-silent {t} {u} (Local.sSil eq) = (_ , silence) , lift tt ,
  subst (λ n → silentView n (_ , silence) (lift tt) ≡ just u) (sym eq) refl
step-silent {t} {u} (Local.sTau {i = X , i} {a = a} eq br) = (_ , branch i) , a ,
  subst (λ n → silentView n (_ , branch i) a ≡ just u) (sym eq) br

import Semantics.LTS {E = PairEv} {I = PairI} as Pair
open import Relation.Nullary using (¬_)

-- The persistent product never emits semantic termination, even after both peers return.
no-tick : ∀ {c s q x T} → ¬ (compose c s q Pair.─[ Pair.ev (Pair.√ x) ]─► T)
no-tick (Pair.sRet ())
