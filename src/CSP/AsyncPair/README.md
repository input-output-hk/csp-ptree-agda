# Asynchronous PTree composition with two FIFOs

`Model` composes two supplied PTrees with exact-packet communication. `Parts`
proves introduction and inversion for each product step. `Trace` proves exact
finite operational correspondence and both local trace projections. All are
universe polymorphic and protocol independent; they import no application
alphabet or replay checker. Check the roots with `agda --safe` under the
repository's guardedness convention.

Parameters are the event alphabet `E`, internal-choice alphabet `I`, return type
`R`, packet carrier, decidable packet equality, and an event classifier into
`Flow Packet`:

- `application`: advance the originating peer without changing either queue.
- `send packet`: advance the peer and append to its outgoing FIFO.
- `receive packet`: advance only if its incoming FIFO has an equal head.

`compose client server queues` retains the two actual peer trees. `atClient` and
`atServer` distinguish their events, including separate wire sends and receives.
The constructor preserves fused `react` offers and indexed silent branches.
A peer's `sil` is represented by a separate product silent index with a lifted
unit carrier. A silent move advances exactly one peer and preserves both queues.
The queues have no capacity bound; any outstanding-request bound belongs to the
supplied peer. Any initial queues can be supplied; `empty` represents fresh
capture. Packet envelopes are preserved only to the extent included in the
chosen packet carrier and classifier.

The medium persists after peers return. The product emits no semantic `√` and
all trace theorems use finite `⟹∖√` traces. API events stay visible in this
composition; an application-specific observer can hide them later. No fairness,
eventual delivery, deadlock freedom, mux equivalence or protocol legality follows
without additional hypotheses about the supplied peers.

`Trace` exports:

- `Run`: operational execution using actual local LTS steps and medium gates.
- `sound`: decompose any product PTree execution into a `Run`, retaining equality
  of its final tree with the reconstructed composition.
- `complete`: realize every operational `Run` as an actual PTree execution.
- `operational-bridge`: equivalence of existential operational and PTree traces.
- `lift-client`, `lift-server`: lift original local executions with matching FIFO
  gate evidence into the product.
- `projectClient`, `projectServer`, `client-projection`, `server-projection`:
  recover genuine local PTree executions in their original event order.

This equivalence concerns PTrees and their operational product. It does not
identify a log format or supply a replay-checker bridge automatically.

`Tests` gives inhabited controls for a fused visible/silent menu, both silent
constructors, exact FIFO consumption, rejected reordering and API preservation.
It also proves that two returned peers do not terminate the persistent medium.
ChainSync and the Leios paired models instantiate this same implementation.
