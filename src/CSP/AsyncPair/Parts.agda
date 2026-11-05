{-# OPTIONS --guardedness #-}

-- Operational introduction/inversion for the full-payload peer composition.
open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc)
open import Relation.Binary.Definitions using (DecidableEquality)
open import CSP.AsyncPair.Flow using (Flow; application; send; receive)
import Semantics.LTS
module CSP.AsyncPair.Parts
  {ℓ ℓe ℓi ℓr ℓp : Level}
  (E : Set ℓ → Set ℓe) (I : Set ℓ → Set ℓi) (R : Set ℓr)
  (Packet : Set ℓp) (packetEq : DecidableEquality Packet)
  (classify : Semantics.LTS.Event {E = E} {I = I} → Flow Packet) where

open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Process_Trees using (PTree; ExtI)
open import CSP.AsyncPair.Model E I R Packet packetEq classify
import Semantics.LTS {E = E} {I = I} as Local
import Semantics.LTS {E = PairEv} {I = PairI} as Pair

-- An observable move advances exactly one original peer and the exact gate.
data Visible (c s : Proc) (q : Queues) : Pair.Event → Proc → Proc → Queues → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓp) where
  client : ∀ {X} {ch : E X} {a c′ q′} →
    c Local.─[ Local.ev (Local.evl (Local.evLabel X ch a)) ]─► c′ →
    clientGate (Local.evLabel X ch a) q ≡ just q′ →
    Visible c s q (Pair.evLabel X (atClient ch) a) c′ s q′
  server : ∀ {X} {ch : E X} {a s′ q′} →
    s Local.─[ Local.ev (Local.evl (Local.evLabel X ch a)) ]─► s′ →
    serverGate (Local.evLabel X ch a) q ≡ just q′ →
    Visible c s q (Pair.evLabel X (atServer ch) a) c s′ q′

-- An internal move advances one peer and leaves the payload queues unchanged.
data Silent (c s : Proc) : Proc → Proc → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓp) where
  clientτ : ∀ {c′} → c Local.─[ Local.τ ]─► c′ → Silent c s c′ s
  serverτ : ∀ {s′} → s Local.─[ Local.τ ]─► s′ → Silent c s c s′

-- Invert an observable product step without assuming tree extensionality.
visible-inv : ∀ {c s q T e} → compose c s q Pair.─[ Pair.ev (Pair.evl e) ]─► T →
  Σ[ c′ ∈ Proc ] Σ[ s′ ∈ Proc ] Σ[ q′ ∈ Queues ]
    (Visible c s q e c′ s′ q′ × T ≡ compose c′ s′ q′)
visible-inv {c} {s} {q} (Pair.sVis {at = X , atClient ch} {a = a} refl br)
  with offers c (X , ch) a in offer | clientGate (Local.evLabel X ch a) q in gate
... | just c′ | just q′ = c′ , s , q′ , client (offer-step offer) gate , sym (just-injective br)
... | nothing | _ with () ← br
... | just _ | nothing with () ← br
visible-inv {c} {s} {q} (Pair.sVis {at = X , atServer ch} {a = a} refl br)
  with offers s (X , ch) a in offer | serverGate (Local.evLabel X ch a) q in gate
... | just s′ | just q′ = c , s′ , q′ , server (offer-step offer) gate , sym (just-injective br)
... | nothing | _ with () ← br
... | just _ | nothing with () ← br

-- Introduce the exact product step from a local transition and queue update.
visible-fire : ∀ {c s q c′ s′ q′ e} → Visible c s q e c′ s′ q′ →
  compose c s q Pair.─[ Pair.ev (Pair.evl e) ]─► compose c′ s′ q′
visible-fire {c} {s} {q} (client {X} {ch} {a} {c′} {q′} st gate) = Pair.sVis refl br
  where
  -- Both the original peer offer and the medium gate have succeeded.
  br : pairOffers c s q (_ , atClient ch) a ≡ just (compose c′ s q′)
  br rewrite step-offer st | gate = refl
visible-fire {c} {s} {q} (server {X} {ch} {a} {s′} {q′} st gate) = Pair.sVis refl br
  where
  -- Synchronisation preserves the other peer and chooses this payload update.
  br : pairOffers c s q (_ , atServer ch) a ≡ just (compose c s′ q′)
  br rewrite step-offer st | gate = refl

-- Invert an indexed silent branch of the product.
silent-inv : ∀ {c s q T} → compose c s q Pair.─[ Pair.τ ]─► T →
  Σ[ c′ ∈ Proc ] Σ[ s′ ∈ Proc ] (Silent c s c′ s′ × T ≡ compose c′ s′ q)
silent-inv (Pair.sSil ())
silent-inv {c} {s} {q} (Pair.sTau {i = X , clientI i} {a = a} refl br)
  with silents c (X , i) a in eq
... | nothing with () ← br
... | just c′ = c′ , s , clientτ (silent-step eq) , sym (just-injective br)
silent-inv {c} {s} {q} (Pair.sTau {i = X , serverI i} {a = a} refl br)
  with silents s (X , i) a in eq
... | nothing with () ← br
... | just s′ = c , s′ , serverτ (silent-step eq) , sym (just-injective br)

-- Lift an original silent step through the asynchronous composition.
silent-fire : ∀ {c s q c′ s′} → Silent c s c′ s′ →
  compose c s q Pair.─[ Pair.τ ]─► compose c′ s′ q
silent-fire {c} {s} {q} {c′} (clientτ st) with step-silent st
... | (X , i) , a , eq = Pair.sTau {i = X , clientI i} {a = a} refl br
  where
  -- The indexed peer branch is mapped directly to a composed continuation.
  br : pairSilents c s q (_ , clientI i) a ≡ just (compose c′ s q)
  br rewrite eq = refl
silent-fire {c} {s} {q} {s′ = s′} (serverτ st) with step-silent st
... | (X , i) , a , eq = Pair.sTau {i = X , serverI i} {a = a} refl br
  where
  -- No network event or queue update accompanies the silent move.
  br : pairSilents c s q (_ , serverI i) a ≡ just (compose c s′ q)
  br rewrite eq = refl
