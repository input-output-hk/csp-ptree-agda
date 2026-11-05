{-# OPTIONS --safe #-}

-- Protocol-independent classification of a peer's visible event.
module CSP.AsyncPair.Flow where
open import Level using (Level)

-- Application events leave the medium unchanged; wire events carry exact packets.
data Flow {ℓ : Level} (Packet : Set ℓ) : Set ℓ where
  application : Flow Packet
  send receive : Packet → Flow Packet
