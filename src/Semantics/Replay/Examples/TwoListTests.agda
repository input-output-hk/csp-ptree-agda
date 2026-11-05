{-# OPTIONS --safe #-}

-- Independent finite rules exercise nondeterministic silent/visible successors and both merge orders.
module Semantics.Replay.Examples.TwoListTests where

open import Level using (0ℓ)
open import Data.Bool using (Bool; true; false)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Semantics.Replay using (Replay)
import Semantics.Replay.Decide as Existing
import Semantics.Replay.TwoList as Paired
import Semantics.Replay.TwoListDecide as Search

-- Dead alternatives occur first; successful search must also explore later alternatives.
data State : Set where
  start dead hub clientFirst serverFirst ended needsClient serverGate : State

-- Visible rules support either endpoint order and a repeated same-label path.
data Step : State → Bool → State → Set where
  bad : Step hub false dead
  client : Step hub false clientFirst
  server : Step hub true serverFirst
  finishServer : Step clientFirst true ended
  finishClient : Step serverFirst false ended
  repeatClient : Step clientFirst false ended
  bridgeClient : Step needsClient false clientFirst
  openGate : Step serverGate true needsClient

-- The first silent alternative deadlocks while the second enables the requested history.
data Tau : State → State → Set where
  bad : Tau start dead
  good : Tau start hub

-- Deliberately duplicated successors demonstrate that uniqueness and duplicate elimination are unnecessary.
after : State → Bool → List State
after hub false = dead ∷ dead ∷ clientFirst ∷ []
after hub true = serverFirst ∷ []
after clientFirst true = ended ∷ []
after clientFirst false = ended ∷ []
after serverFirst false = ended ∷ []
after needsClient false = clientFirst ∷ []
after serverGate true = needsClient ∷ []
after _ _ = []

-- Silent branching is finite but need not be deterministic.
taus : State → List State
taus start = dead ∷ hub ∷ []
taus _ = []

-- Every enumerated visible alternative independently satisfies its rule, including the repeated target.
after-sound : ∀ {s e t} → t ∈ after s e → Step s e t
after-sound {hub} {false} (here refl) = bad
after-sound {hub} {false} (there (here refl)) = bad
after-sound {hub} {false} (there (there (here refl))) = client
after-sound {hub} {true} (here refl) = server
after-sound {clientFirst} {true} (here refl) = finishServer
after-sound {clientFirst} {false} (here refl) = repeatClient
after-sound {serverFirst} {false} (here refl) = finishClient
after-sound {needsClient} {false} (here refl) = bridgeClient
after-sound {serverGate} {true} (here refl) = openGate

-- All independent visible rules occur in the menu; duplicates do not affect completeness.
after-complete : ∀ {s e t} → Step s e t → t ∈ after s e
after-complete bad = here refl
after-complete client = there (there (here refl))
after-complete server = here refl
after-complete finishServer = here refl
after-complete repeatClient = here refl
after-complete finishClient = here refl
after-complete bridgeClient = here refl
after-complete openGate = here refl

-- The two silent menu entries preserve their independently declared operational rules.
taus-sound : ∀ {s t} → t ∈ taus s → Tau s t
taus-sound {start} (here refl) = bad
taus-sound {start} (there (here refl)) = good

-- Both possible hidden steps are included.
taus-complete : ∀ {s t} → Tau s t → t ∈ taus s
taus-complete bad = here refl
taus-complete good = there (here refl)

-- This small fixture has the same finite successor contract as applications with infinite state types.
replay : Replay 0ℓ State Bool
replay = record
  { _-[_]→_ = Step; _-τ→_ = Tau; _≟E_ = Bool._≟_
  ; after = after; taus = taus; after-sound = after-sound; after-complete = after-complete
  ; taus-sound = taus-sound; taus-complete = taus-complete }

module Single = Existing.Decider replay

-- No silent successor of the initial state can take another silent step.
accessible : ∀ s → Single.τAcc s
accessible start = Single.acc λ { bad → Single.acc λ (); good → Single.acc λ () }
accessible dead = Single.acc λ ()
accessible hub = Single.acc λ ()
accessible clientFirst = Single.acc λ ()
accessible serverFirst = Single.acc λ ()
accessible ended = Single.acc λ ()
accessible needsClient = Single.acc λ ()
accessible serverGate = Single.acc λ ()

module Trace = Paired.Traces replay (λ (_ : ⊤) → false) (λ (_ : ⊤) → true)
module Check = Search.Decider replay (λ (_ : ⊤) → false) (λ (_ : ⊤) → true) accessible

-- Success requires passing both a failed silent branch and duplicated failed visible alternatives.
nondeterministic-success : Trace.PairTrace start (tt ∷ []) (tt ∷ [])
nondeterministic-success = toWitness {a? = Check.decide (tt ∷ []) (tt ∷ []) start} tt

-- No client head is initially possible here, so deciding this prefix must try the server branch.
forced-server-first : Trace.PairTrace serverGate (tt ∷ []) (tt ∷ [])
forced-server-first = toWitness {a? = Check.decide (tt ∷ []) (tt ∷ []) serverGate} tt

-- An exhausted server list still permits exactly the remaining client row.
client-only : Trace.PairTrace serverFirst (tt ∷ []) []
client-only = toWitness {a? = Check.decide (tt ∷ []) [] serverFirst} tt

-- An exhausted client list still permits exactly the remaining server row.
server-only : Trace.PairTrace clientFirst [] (tt ∷ [])
server-only = toWitness {a? = Check.decide [] (tt ∷ []) clientFirst} tt

-- The alternate endpoint merge has a direct witness with the server row first.
server-first : Trace.PairTrace start (tt ∷ []) (tt ∷ [])
server-first = ended , Trace.tau good (Trace.server server (Trace.client finishClient Trace.done))

-- Each accepted merge transports to an ordinary single-list weak trace with explicit merge evidence.
merged-server-first : Trace.MergedTrace start (tt ∷ []) (tt ∷ [])
merged-server-first = Trace.to-merged server-first

-- Splitting that explicit merge recovers a paired run without any endpoint-order guess.
split-server-first : Trace.PairTrace start (tt ∷ []) (tt ∷ [])
split-server-first = Trace.from-merged merged-server-first

-- No hidden schedule or endpoint merge can fit this extra recorded row.
exhaustive-rejection : Trace.PairTrace start (tt ∷ tt ∷ []) (tt ∷ []) → ⊥
exhaustive-rejection = toWitnessFalse {a? = Check.decide (tt ∷ tt ∷ []) (tt ∷ []) start} tt

-- Empty input is accepted immediately even where hidden and visible progress remain available.
eof-prefix : Trace.PairTrace start [] []
eof-prefix = toWitness {a? = Check.decide [] [] start} tt

-- Exhausted client input cannot insert the unrecorded client action needed to reach the server row.
no-unmatched-visible : Trace.PairTrace needsClient [] (tt ∷ []) → ⊥
no-unmatched-visible = toWitnessFalse {a? = Check.decide [] (tt ∷ []) needsClient} tt

module Overlap = Paired.Traces replay (λ (_ : ⊤) → false) (λ (_ : ⊤) → false)
module OverlapCheck = Search.Decider replay (λ (_ : ⊤) → false) (λ (_ : ⊤) → false) accessible

-- Even identical embeddings retain two endpoint positions and need no disjointness assumption.
overlapping-embeddings : Overlap.PairTrace start (tt ∷ []) (tt ∷ [])
overlapping-embeddings = toWitness {a? = OverlapCheck.decide (tt ∷ []) (tt ∷ []) start} tt
