{-# OPTIONS --guardedness #-}

-- Exact finite-run correspondence for the actual peer/FIFO PTree product.
open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc)
open import Relation.Binary.Definitions using (DecidableEquality)
open import CSP.AsyncPair.Flow using (Flow; application; send; receive)
import Semantics.LTS
module CSP.AsyncPair.Trace
  {ℓ ℓe ℓi ℓr ℓp : Level}
  (E : Set ℓ → Set ℓe) (I : Set ℓ → Set ℓi) (R : Set ℓr)
  (Packet : Set ℓp) (packetEq : DecidableEquality Packet)
  (classify : Semantics.LTS.Event {E = E} {I = I} → Flow Packet) where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Maybe using (just)
open import Data.Unit using (⊤)
open import Function.Bundles using (_⇔_; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees using (PTree; ExtI)
open import CSP.AsyncPair.Model E I R Packet packetEq classify
open import CSP.AsyncPair.Parts E I R Packet packetEq classify
import Semantics.LTS {E = E} {I = I} as Local
import Semantics.Deadlock {E = E} {I = I} as LD
import Semantics.LTS {E = PairEv} {I = PairI} as Pair
open import Semantics.Deadlock {E = PairEv} {I = PairI}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)

-- The three independent components at a finite product residual.
record State : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓp) where
  constructor state
  field
    clientPeer serverPeer : Proc
    network : Queues
open State public

-- The corresponding concrete PTree, retaining all three components.
tree : State → PTree PairEv PairI ⊤
tree (state c s q) = compose c s q

-- Operational runs are defined from existing local LTS steps and exact gates.
data Run : State → List Pair.Event → State → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓp) where
  stop : ∀ {s} → Run s [] s
  silent : ∀ {c s q c′ s′ t end} → Silent c s c′ s′ →
    Run (state c′ s′ q) t end → Run (state c s q) t end
  visible : ∀ {c s q c′ s′ q′ e t end} → Visible c s q e c′ s′ q′ →
    Run (state c′ s′ q′) t end → Run (state c s q) (e ∷ t) end

-- Every concrete PTree run decomposes into those actual component steps.
sound : ∀ {start t T} → tree start ⟹∖√⟨ t ⟩ T →
  Σ[ end ∈ State ] (Run start t end × T ≡ tree end)
sound {start} ∖√-refl = start , stop , refl
sound {state c s q} (∖√-τ st rest) with silent-inv st
... | c′ , s′ , move , refl with sound {state c′ s′ q} rest
...   | end , run , eq = end , silent move run , eq
sound {state c s q} (∖√-ev st rest) with visible-inv st
... | c′ , s′ , q′ , move , refl with sound {state c′ s′ q′} rest
...   | end , run , eq = end , visible move run , eq

-- Conversely every component/gate run is realised by the composed PTree.
complete : ∀ {start end t} → Run start t end → tree start ⟹∖√⟨ t ⟩ tree end
complete stop = ∖√-refl
complete (silent move run) = ∖√-τ (silent-fire move) (complete run)
complete (visible move run) = ∖√-ev (visible-fire move) (complete run)

-- Operational concatenation preserves the exact composed endpoint.
append : ∀ {a b c t u} → Run a t b → Run b u c → Run a (t ++ u) c
append stop r = r
append (silent move r) s = silent move (append r s)
append (visible move r) s = visible move (append r s)

-- A trace of application/wire events must pass the medium at each visible row.
data ClientQueues : Queues → List Local.Event → Queues → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓp) where
  stopC : ∀ {q} → ClientQueues q [] q
  stepC : ∀ {q q′ q″ e t} → clientGate e q ≡ just q′ →
    ClientQueues q′ t q″ → ClientQueues q (e ∷ t) q″

-- The server has the corresponding opposite-direction gate trace.
data ServerQueues : Queues → List Local.Event → Queues → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓp) where
  stopS : ∀ {q} → ServerQueues q [] q
  stepS : ∀ {q q′ q″ e t} → serverGate e q ≡ just q′ →
    ServerQueues q′ t q″ → ServerQueues q (e ∷ t) q″

-- Tag a local trace with its originating endpoint without erasing API events.
clientEvents : List Local.Event → List Pair.Event
clientEvents [] = []
clientEvents (Local.evLabel X ch a ∷ t) = Pair.evLabel X (atClient ch) a ∷ clientEvents t

-- Server traces use the distinct endpoint constructor.
serverEvents : List Local.Event → List Pair.Event
serverEvents [] = []
serverEvents (Local.evLabel X ch a ∷ t) = Pair.evLabel X (atServer ch) a ∷ serverEvents t

-- Lift an existing client trace whenever its exact payloads pass the medium.
lift-client : ∀ {c c′ s q q′ t} → c LD.⟹∖√⟨ t ⟩ c′ → ClientQueues q t q′ →
  Run (state c s q) (clientEvents t) (state c′ s q′)
lift-client LD.∖√-refl stopC = stop
lift-client (LD.∖√-τ st run) gates = silent (clientτ st) (lift-client run gates)
lift-client (LD.∖√-ev st run) (stepC gate gates) = visible (client st gate) (lift-client run gates)

-- The symmetric lifting preserves the client and all FIFO payloads.
lift-server : ∀ {c s s′ q q′ t} → s LD.⟹∖√⟨ t ⟩ s′ → ServerQueues q t q′ →
  Run (state c s q) (serverEvents t) (state c s′ q′)
lift-server LD.∖√-refl stopS = stop
lift-server (LD.∖√-τ st run) gates = silent (serverτ st) (lift-server run gates)
lift-server (LD.∖√-ev st run) (stepS gate gates) = visible (server st gate) (lift-server run gates)

-- Project the tagged trace back to the client's original visible alphabet.
projectClient : List Pair.Event → List Local.Event
projectClient [] = []
projectClient (Pair.evLabel X (atClient ch) a ∷ es) = Local.evLabel X ch a ∷ projectClient es
projectClient (Pair.evLabel _ (atServer _) _ ∷ es) = projectClient es

-- Recover the server order independently of the other endpoint's scheduling.
projectServer : List Pair.Event → List Local.Event
projectServer [] = []
projectServer (Pair.evLabel _ (atClient _) _ ∷ es) = projectServer es
projectServer (Pair.evLabel X (atServer ch) a ∷ es) = Local.evLabel X ch a ∷ projectServer es

-- Every operational execution projects to a genuine run of its supplied client.
client-projection : ∀ {start es end} → Run start es end →
  clientPeer start LD.⟹∖√⟨ projectClient es ⟩ clientPeer end
client-projection stop = LD.∖√-refl
client-projection (silent (clientτ st) run) = LD.∖√-τ st (client-projection run)
client-projection (silent (serverτ st) run) = client-projection run
client-projection (visible (client st gate) run) = LD.∖√-ev st (client-projection run)
client-projection (visible (server st gate) run) = client-projection run

-- Projection likewise preserves every original server API, wire and silent move.
server-projection : ∀ {start es end} → Run start es end →
  serverPeer start LD.⟹∖√⟨ projectServer es ⟩ serverPeer end
server-projection stop = LD.∖√-refl
server-projection (silent (clientτ st) run) = server-projection run
server-projection (silent (serverτ st) run) = LD.∖√-τ st (server-projection run)
server-projection (visible (client st gate) run) = server-projection run
server-projection (visible (server st gate) run) = LD.∖√-ev st (server-projection run)

-- Exact finite trace equivalence with the operational peer/FIFO product.
-- This theorem does not itself identify any log parser or protocol replay model.
operational-bridge : ∀ start es →
  (Σ[ end ∈ State ] Run start es end) ⇔
  (Σ[ T ∈ PTree PairEv PairI ⊤ ] tree start ⟹∖√⟨ es ⟩ T)
operational-bridge start es = mk⇔
  (λ { (end , run) → tree end , complete run })
  (λ { (T , run) → let end , components , _ = sound run in end , components })
