{-# OPTIONS --guardedness #-}

-- Positive controls for fused react nodes, sil, FIFO order and persistent media.
module CSP.AsyncPair.Tests where
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (_≟_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Process_Trees using (PTree; ptree; react; ret; sil)
open import CSP.AsyncPair.Flow using (Flow; send; receive; application)

-- One small alphabet retains value-level wire data and a peer-local API channel.
data Ch : Set → Set where
  output input : Ch ℕ
  api : Ch ⊤

-- A genuine indexed internal branch, distinct from the sil constructor.
data Branch : Set → Set where
  choice : Branch ⊤

import Semantics.LTS {E = Ch} {I = Branch} as Local

-- Channel classification leaves API steps outside the communication medium.
flow : Local.Event → Flow ℕ
flow (Local.evLabel _ output n) = send n
flow (Local.evLabel _ input n) = receive n
flow _ = application

open import CSP.AsyncPair.Model Ch Branch ⊤ ℕ _≟_ flow
import Semantics.LTS {E = PairEv} {I = PairI} as Pair

-- A returned peer is retained as an inactive component of the persistent product.
ended : Proc
ended = ptree (ret tt)

-- This peer simultaneously offers visible output and an indexed silent move.
fused : Proc
PTree.force fused = react visible internal
  where
  -- Every offered packet has a real visible continuation.
  visible : (at : Process_Trees.AnyTypes Ch) → Process_Trees.ContinueType at (Data.Maybe.Maybe Proc)
  visible (_ , output) _ = just ended
  visible _ _ = nothing

  -- The fused node also offers one independent silent branch.
  internal : (at : Process_Trees.AnyTypes Branch) → Process_Trees.ContinueType at (Data.Maybe.Maybe Proc)
  internal (_ , choice) _ = just ended

-- A visible offer survives even when the same peer can move silently.
visible-and-silent : compose fused ended empty Pair.─[ Pair.ev (Pair.evl (Pair.evLabel _ (atClient output) 5)) ]─►
  compose ended ended (queues (5 ∷ []) [])
visible-and-silent = Pair.sVis refl refl

-- The indexed branch remains possible at exactly that same product state.
indexed-silent : compose fused ended empty Pair.─[ Pair.τ ]─► compose ended ended empty
indexed-silent = Pair.sTau {i = _ , clientI (branch choice)} {a = tt} refl refl

-- A plain sil constructor is mapped independently of indexed branches.
plain-silent : compose (ptree (sil ended)) ended empty Pair.─[ Pair.τ ]─► compose ended ended empty
plain-silent = Pair.sTau {i = _ , clientI silence} {a = lift tt} refl refl

-- API gates neither insert nor remove packets.
api-preserves : clientGate (Local.evLabel _ api tt) (queues (3 ∷ []) (4 ∷ [])) ≡
  just (queues (3 ∷ []) (4 ∷ []))
api-preserves = refl

-- Matching the queue head consumes exactly one packet.
head-only : serverGate (Local.evLabel _ input 3) (queues (3 ∷ 4 ∷ []) []) ≡
  just (queues (4 ∷ []) [])
head-only = refl

-- Receiving a later packet cannot skip an earlier transmitted value.
no-reordering : serverGate (Local.evLabel _ input 4) (queues (3 ∷ 4 ∷ []) []) ≡ nothing
no-reordering = refl

-- The product does not emit semantic termination when its two peers have returned.
no-product-tick : ∀ {T} → ¬ (compose ended ended empty Pair.─[ Pair.ev (Pair.√ tt) ]─► T)
no-product-tick (Pair.sRet ())
