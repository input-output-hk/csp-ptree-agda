{-# OPTIONS --guardedness #-}

-- Sanity checks for native replication `Rep`/`!⦀`: spawning, collisions, a terminating copy,
-- and the negative control showing the frame law's disjointness premises are load-bearing.

open import Level using (Lift; lift) renaming (zero to lzero)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing) renaming (_>>=_ to _>>=ₘ_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_,_; proj₁)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Examples.ReplicationSanity where

open PTree

-- two ⊤-carried events
data Ev : Set → Set where
  evA evB : Ev ⊤

-- decidable equality on the event index
Ev-≟ : (x y : AnyTypes Ev) → Dec (x ≡ y)
Ev-≟ (_ , evA) (_ , evA) = yes refl
Ev-≟ (_ , evB) (_ , evB) = yes refl
Ev-≟ (_ , evA) (_ , evB) = no λ ()
Ev-≟ (_ , evB) (_ , evA) = no λ ()

open import CSP.Operators Ev-≟
open import CSP.Replication Ev-≟

-- the process type of these checks
T : Set _
T = PTree Ev (ExtI Ev) (⊤ {lzero})

-- one visible step of a process, read off its react node
after : T → (at : AnyTypes Ev) → proj₁ at → Maybe T
after t at a with force t
... | react v _ = v at a
... | _         = nothing

-- one τ-branch of a process, read off its react node
τ-after : T → (i : AnyTypes (ExtI Ev)) → proj₁ i → Maybe T
τ-after t i a with force t
... | react _ τc = τc i a
... | _          = nothing

-- does t offer `at` visibly right now?
offers? : T → (at : AnyTypes Ev) → proj₁ at → Bool
offers? t at a with after t at a
... | just _  = true
... | nothing = false

-- the continuation of a copy after its first `a`
Pb : T
Pb = evB ⟶₀ Stop

-- every copy: a → b → Stop
Pa : ℕ → T
Pa _ = evA ⟶₀ Pb

-- after two `a`s: two started copies (each waiting on b), fresh counter = 2
two-a : (after (!⦀ Pa) (_ , evA) tt >>=ₘ λ t → after t (_ , evA) tt)
      ≡ just (Rep⦀ Pa 2 ((Stop ⦀ Pb) ⦀ Pb))
two-a = refl

-- every copy: a → a → Stop, so after one `a` the running copy and the fresh one collide on `a`
Paa : ℕ → T
Paa _ = evA ⟶₀ (evA ⟶₀ Stop)

-- the state reached by two `a`s: the inline collision node
collided : Maybe T
collided = after (!⦀ Paa) (_ , evA) tt >>=ₘ λ t → after t (_ , evA) tt

-- the collision node offers nothing visibly
collide-silent : (collided >>=ₘ λ c → after c (_ , evA) tt) ≡ nothing
collide-silent = refl

-- branch 0: the RUNNING copy took the second `a`
collide-run : (collided >>=ₘ λ c → τ-after c (_ , fin {n = 2}) (lift fzero))
            ≡ just (Rep⦀ Paa 1 (Stop ⦀ Stop))
collide-run = refl

-- branch 1: a FRESH copy took it, so a second copy is running and the counter is 2
collide-fresh : (collided >>=ₘ λ c → τ-after c (_ , fin {n = 2}) (lift (fsuc fzero)))
              ≡ just (Rep⦀ Paa 2 ((Stop ⦀ (evA ⟶₀ Stop)) ⦀ (evA ⟶₀ Stop)))
collide-fresh = refl

-- a copy that terminates at once is never spawned: `!⦀ (const Skip)` offers nothing (behaves as Stop)
rep-skip : offers? (!⦀ (λ _ → Skip)) (_ , evA) tt ≡ false
rep-skip = refl

open import Semantics.LTS {E = Ev} {I = ExtI Ev} using (_─[_]─►_; ev; evl; evLabel; sVis)
open import CSP.Laws.Traces.ReplicationSteps Ev-≟

-- the fresh copy of `!⦀ Pa` fires `a`, spawning copy 0
fresh-a-step : !⦀ Pa ─[ ev (evl (evLabel ⊤ evA tt)) ]─► Rep⦀ Pa 1 (Stop ⦀ Pb)
fresh-a-step = Rep-evFresh-intro (λ _ _ → tt) Pa 0 Stop (sVis refl refl) refl

-------------------------------------------------------------------------------------
-- Task 6 Step 7: the frame law's disjointness premises are load-bearing
-------------------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Semantics.LTS {E = Ev} {I = ExtI Ev} using (τ; sSil; sTau)
open import Semantics.Bisim {E = Ev} {I = ExtI Ev} using (Sbisim; SSimF; _∼_)
open import CSP.Laws.Traces.TraceLawsParallelElim Ev-≟ using (Par-τ-elim; τL; τR)

-- a process offering `a` once: used for every copy, for Q and for S
P1 : T
P1 = evA ⟶₀ Stop

-- the uniform copies
P1s : ℕ → T
P1s _ = P1

-- the framed side's τ-branch where Q took `a` is stable: no component has a τ
framed-stable : ∀ {M} → (Stop ⦀ Rep⦀ P1s 0 P1) ─[ τ ]─► M → ⊥
framed-stable st with Par-τ-elim ∅ES (λ _ _ → tt) Stop (Rep⦀ P1s 0 P1) st
... | τL _ (sSil ()) _
... | τL _ (sTau refl ()) _
... | τR _ st′ _ with Rep-τ-elim (λ _ _ → tt) P1s 0 P1 st′
...   | τRun   (sSil ())
...   | τRun   (sTau refl ())
...   | τFresh (sSil ())
...   | τFresh (sTau refl ())

-- with Q, S and every copy offering `a`, `Rep-frame-∼` FAILS: after `a`, the replicated
-- side's τ to "running copies took it" reaches `Rep⦀ P1s 0 N` (N = the Q/S collision
-- node), which still has a τ AND keeps the fresh copy's `a`, `a` alive; the framed side's
-- two τ-branches are `Stop ⦀ Rep⦀ P1s 0 P1` (no τ) and `P1 ⦀ R` (R = the S/fresh
-- collision node, offering nothing, so only one more `a`)
frame-needs-disj : ¬ (Rep⦀ P1s 0 (P1 ⦀ P1) ∼ (P1 ⦀ Rep⦀ P1s 0 P1))
frame-needs-disj h
  with SSimF.on-ev (Sbisim.fwd h) (sVis {at = _ , evA} {a = tt} refl refl)
... | _ , sVis refl refl , l1r1
    with SSimF.on-tau (Sbisim.fwd l1r1) (sTau {i = _ , fin {n = 2}} {a = lift fzero} refl refl)
...   | _ , sTau {i = _ , base _}   refl () , _
...   | _ , sTau {i = _ , pair _ _} refl () , _
...   | _ , sTau {i = _ , fin} {a = lift (fsuc (fsuc _))} refl () , _
...   | _ , sTau {i = _ , fin} {a = lift fzero} refl refl , ac
      with SSimF.on-tau (Sbisim.fwd ac)
             (Rep-τRun-intro (λ _ _ → tt) P1s 0 _ (sTau {i = _ , fin {n = 2}} {a = lift fzero} refl refl))
...     | _ , st , _ = framed-stable st
frame-needs-disj h
    | _ , sVis refl refl , l1r1
    | _ , sTau {i = _ , fin} {a = lift (fsuc fzero)} refl refl , ad
      with SSimF.on-ev (Sbisim.fwd ad) (sVis {at = _ , evA} {a = tt} refl refl)
...     | _ , sVis refl refl , a′d′
        with SSimF.on-ev (Sbisim.fwd a′d′) (sVis {at = _ , evA} {a = tt} refl refl)
...       | _ , sVis refl () , _
