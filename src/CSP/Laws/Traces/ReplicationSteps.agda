{-# OPTIONS --guardedness #-}

-- Single-step calculus for native replication `Rep` (CSP.Replication): every strong
-- step of `Rep merge P k Q` and of its same-event collision node `repBoth`, inverted
-- into the copy step that produced it (…-elim), and built back from it (…-intro).
--   visible:  a running copy (Q) alone, the fresh copy (P k) alone, or BOTH on the same
--             event (→ the τ-only collision node `repBoth`);
--   τ:        a running copy's τ, or the fresh copy's τ (which spawns it);
--   √:        never (`Rep` drops a terminating copy's √).
-- Mirrors `Par-τ-elim` / `Par-ev-elim` (CSP/Laws/Traces/TraceLawsParallelElim.agda).

open import Level using (lift; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; suc)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.Traces.ReplicationSteps {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import CSP.Replication E-≟
open import Semantics.LTS {E = E} {I = ExtI E}
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟ using (viewT-τ)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟ using (viewV-ev)

-------------------------------------------------------------------------------------
-- generic bridges: a step read back as an offer / τ-branch of the forced node
-- (the converses `viewV-ev` / `viewT-τ` are reused from the Par/□ elim modules)
-------------------------------------------------------------------------------------

-- a visible step of t is a visible offer of t's forced node
ev→viewV : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree E (ExtI E) R} {X : Set ℓ} {e : E X} {a : X}
         → t ─[ ev (evl (evLabel X e a)) ]─► t′ → viewV (force t) (X , e) a ≡ just t′
ev→viewV {t′ = t′} {X = X} {e = e} {a = a} st with ev-inv st
... | _ , _ , eq , br = subst (λ n → viewV n (X , e) a ≡ just t′) (sym eq) br

-- a τ step of t is a τ-branch of t's forced node (a `sil` is the single branch fin/0)
τ→viewT : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree E (ExtI E) R}
        → t ─[ τ ]─► t′
        → Σ[ j ∈ AnyTypes (ExtI E) ] Σ[ b ∈ proj₁ j ] (viewT (force t) j b ≡ just t′)
τ→viewT {t′ = t′} (sSil eq) =
  (_ , fin {n = 1}) , lift fzero
  , subst (λ n → viewT n (_ , fin {n = 1}) (lift fzero) ≡ just t′) (sym eq) refl
τ→viewT {t′ = t′} (sTau {i = i} {a = b} eq br) =
  i , b , subst (λ n → viewT n i b ≡ just t′) (sym eq) br

module _ {ℓr} {R : Set ℓr} (merge : R → R → R) where

  -- the process type the combinator lives in
  private
    T : Set _
    T = PTree E (ExtI E) R

  -- the same-event collision node: τ-only, branch 0 = a running copy, 1 = the fresh copy
  repBoth : (ℕ → T) → ℕ → T → T → T → T
  repBoth P k Q Q′ P′ = ptree (react (λ _ _ → nothing) (rep-brBoth merge P k Q Q′ P′))

  -----------------------------------------------------------------------------------
  -- branch-equation elims / intros for the named continuations (generic node kinds)
  -----------------------------------------------------------------------------------

  -- a visible branch of rep-vis, decoded by which side offered the event
  rep-vis-elim : (nQ nP : NodeKind E (ExtI E) R) (P : ℕ → T) (k : ℕ) (Q : T)
                 {at : AnyTypes E} {a : proj₁ at} {M : T}
               → rep-vis merge nQ nP P k Q at a ≡ just M
               → (Σ[ Q′ ∈ T ] (viewV nQ at a ≡ just Q′) × (viewV nP at a ≡ nothing)
                    × (M ≡ Rep merge P k Q′))
               ⊎ (Σ[ P′ ∈ T ] (viewV nQ at a ≡ nothing) × (viewV nP at a ≡ just P′)
                    × (M ≡ Rep merge P (suc k) (Par ∅ES merge Q P′)))
               ⊎ (Σ[ Q′ ∈ T ] Σ[ P′ ∈ T ] (viewV nQ at a ≡ just Q′) × (viewV nP at a ≡ just P′)
                    × (M ≡ repBoth P k Q Q′ P′))
  rep-vis-elim nQ nP P k Q {at} {a} eq with viewV nQ at a | viewV nP at a
  ... | just Q′ | nothing = inj₁ (Q′ , refl , refl , sym (just-injective eq))
  ... | nothing | just P′ = inj₂ (inj₁ (P′ , refl , refl , sym (just-injective eq)))
  ... | just Q′ | just P′ = inj₂ (inj₂ (Q′ , P′ , refl , refl , sym (just-injective eq)))
  ... | nothing | nothing = case eq of λ ()

  -- a τ branch of rep-tau: a running copy's τ (tag 0) or the fresh copy's τ (tag 1)
  rep-tau-elim : (nQ nP : NodeKind E (ExtI E) R) (P : ℕ → T) (k : ℕ) (Q : T)
                 {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : T}
               → rep-tau merge nQ nP P k Q i a ≡ just M
               → (Σ[ j ∈ AnyTypes (ExtI E) ] Σ[ b ∈ proj₁ j ] Σ[ Q′ ∈ T ]
                    (viewT nQ j b ≡ just Q′) × (M ≡ Rep merge P k Q′))
               ⊎ (Σ[ j ∈ AnyTypes (ExtI E) ] Σ[ b ∈ proj₁ j ] Σ[ P′ ∈ T ]
                    (viewT nP j b ≡ just P′) × (M ≡ Rep merge P (suc k) (Par ∅ES merge Q P′)))
  rep-tau-elim nQ nP P k Q {_ , base _}            eq = case eq of λ ()
  rep-tau-elim nQ nP P k Q {_ , fin}               eq = case eq of λ ()
  rep-tau-elim nQ nP P k Q {_ , pair (base _) _}   eq = case eq of λ ()
  rep-tau-elim nQ nP P k Q {_ , pair (pair _ _) _} eq = case eq of λ ()
  rep-tau-elim nQ nP P k Q {_ , pair fin j} {lift fzero , b} eq
    with viewT nQ (_ , j) b in veq
  ... | just Q′ = inj₁ ((_ , j) , b , Q′ , veq , sym (just-injective eq))
  ... | nothing = case eq of λ ()
  rep-tau-elim nQ nP P k Q {_ , pair fin j} {lift (fsuc fzero) , b} eq
    with viewT nP (_ , j) b in veq
  ... | just P′ = inj₂ ((_ , j) , b , P′ , veq , sym (just-injective eq))
  ... | nothing = case eq of λ ()
  rep-tau-elim nQ nP P k Q {_ , pair fin j} {lift (fsuc (fsuc _)) , b} eq = case eq of λ ()

  -- a τ branch of the collision node: branch 0 (running copy) or branch 1 (fresh copy)
  rep-brBoth-elim : (P : ℕ → T) (k : ℕ) (Q Q′ P′ : T)
                    {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : T}
                  → rep-brBoth merge P k Q Q′ P′ i a ≡ just M
                  → (M ≡ Rep merge P k Q′) ⊎ (M ≡ Rep merge P (suc k) (Par ∅ES merge Q P′))
  rep-brBoth-elim P k Q Q′ P′ {_ , fin} {lift fzero}          eq = inj₁ (sym (just-injective eq))
  rep-brBoth-elim P k Q Q′ P′ {_ , fin} {lift (fsuc fzero)}   eq = inj₂ (sym (just-injective eq))
  rep-brBoth-elim P k Q Q′ P′ {_ , fin} {lift (fsuc (fsuc _))} eq = case eq of λ ()
  rep-brBoth-elim P k Q Q′ P′ {_ , base _}   eq = case eq of λ ()
  rep-brBoth-elim P k Q Q′ P′ {_ , pair _ _} eq = case eq of λ ()

  -- rep-vis branch: only a running copy offers the event
  rep-vis-run : (nQ nP : NodeKind E (ExtI E) R) (P : ℕ → T) (k : ℕ) (Q : T)
                {at : AnyTypes E} {a : proj₁ at} {Q′ : T}
              → viewV nQ at a ≡ just Q′ → viewV nP at a ≡ nothing
              → rep-vis merge nQ nP P k Q at a ≡ just (Rep merge P k Q′)
  rep-vis-run nQ nP P k Q {at} {a} eQ eP with viewV nQ at a | viewV nP at a
  ... | just _  | nothing = case eQ of λ { refl → refl }
  ... | just _  | just _  = case eP of λ ()
  ... | nothing | _       = case eQ of λ ()

  -- rep-vis branch: only the fresh copy offers the event
  rep-vis-fresh : (nQ nP : NodeKind E (ExtI E) R) (P : ℕ → T) (k : ℕ) (Q : T)
                  {at : AnyTypes E} {a : proj₁ at} {P′ : T}
                → viewV nQ at a ≡ nothing → viewV nP at a ≡ just P′
                → rep-vis merge nQ nP P k Q at a ≡ just (Rep merge P (suc k) (Par ∅ES merge Q P′))
  rep-vis-fresh nQ nP P k Q {at} {a} eQ eP with viewV nQ at a | viewV nP at a
  ... | nothing | just _  = case eP of λ { refl → refl }
  ... | nothing | nothing = case eP of λ ()
  ... | just _  | _       = case eQ of λ ()

  -- rep-vis branch: both sides offer the event, landing in the collision node
  rep-vis-both : (nQ nP : NodeKind E (ExtI E) R) (P : ℕ → T) (k : ℕ) (Q : T)
                 {at : AnyTypes E} {a : proj₁ at} {Q′ P′ : T}
               → viewV nQ at a ≡ just Q′ → viewV nP at a ≡ just P′
               → rep-vis merge nQ nP P k Q at a ≡ just (repBoth P k Q Q′ P′)
  rep-vis-both nQ nP P k Q {at} {a} eQ eP with viewV nQ at a | viewV nP at a
  ... | just _  | just _  = case eQ of λ { refl → case eP of λ { refl → refl } }
  ... | just _  | nothing = case eP of λ ()
  ... | nothing | _       = case eQ of λ ()

  -- rep-tau branch at tag 0: a running copy's τ-branch j/b
  rep-tau-run : (nQ nP : NodeKind E (ExtI E) R) (P : ℕ → T) (k : ℕ) (Q : T)
                {j : AnyTypes (ExtI E)} {b : proj₁ j} {Q′ : T}
              → viewT nQ j b ≡ just Q′
              → rep-tau merge nQ nP P k Q (_ , pair (fin {n = 2}) (proj₂ j)) (lift fzero , b)
                ≡ just (Rep merge P k Q′)
  rep-tau-run nQ nP P k Q {_ , j} {b} eq with viewT nQ (_ , j) b
  ... | just _  = case eq of λ { refl → refl }
  ... | nothing = case eq of λ ()

  -- rep-tau branch at tag 1: the fresh copy's τ-branch j/b (spawning it)
  rep-tau-fresh : (nQ nP : NodeKind E (ExtI E) R) (P : ℕ → T) (k : ℕ) (Q : T)
                  {j : AnyTypes (ExtI E)} {b : proj₁ j} {P′ : T}
                → viewT nP j b ≡ just P′
                → rep-tau merge nQ nP P k Q (_ , pair (fin {n = 2}) (proj₂ j)) (lift (fsuc fzero) , b)
                  ≡ just (Rep merge P (suc k) (Par ∅ES merge Q P′))
  rep-tau-fresh nQ nP P k Q {_ , j} {b} eq with viewT nP (_ , j) b
  ... | just _  = case eq of λ { refl → refl }
  ... | nothing = case eq of λ ()

  -----------------------------------------------------------------------------------
  -- Rep-ev-elim : a visible step of Rep
  -----------------------------------------------------------------------------------

  -- the three ways Rep fires a visible event
  data RepEvR (P : ℕ → T) (k : ℕ) (Q : T) {X : Set ℓ} (e : E X) (a : X)
       : T → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
    -- a running copy alone offers the event
    evRun   : ∀ {Q′} → Q ─[ ev (evl (evLabel X e a)) ]─► Q′
            → viewV (force (P k)) (X , e) a ≡ nothing
            → RepEvR P k Q e a (Rep merge P k Q′)
    -- the fresh copy alone offers it: copy k is spawned, the counter moves on
    evFresh : ∀ {P′} → P k ─[ ev (evl (evLabel X e a)) ]─► P′
            → viewV (force Q) (X , e) a ≡ nothing
            → RepEvR P k Q e a (Rep merge P (suc k) (Par ∅ES merge Q P′))
    -- both offer it: the τ-only collision node decides which one took it
    evBoth  : ∀ {Q′ P′} → Q ─[ ev (evl (evLabel X e a)) ]─► Q′
            → P k ─[ ev (evl (evLabel X e a)) ]─► P′
            → RepEvR P k Q e a (repBoth P k Q Q′ P′)

  -- every visible step of Rep is one of evRun / evFresh / evBoth
  Rep-ev-elim : (P : ℕ → T) (k : ℕ) (Q : T) {X : Set ℓ} {e : E X} {a : X} {M : T}
              → Rep merge P k Q ─[ ev (evl (evLabel X e a)) ]─► M → RepEvR P k Q e a M
  Rep-ev-elim P k Q st with ev-inv st
  ... | _ , _ , refl , br with rep-vis-elim (force Q) (force (P k)) P k Q br
  ...   | inj₁ (Q′ , vQ , vP , refl)             = evRun (viewV-ev refl vQ) vP
  ...   | inj₂ (inj₁ (P′ , vQ , vP , refl))      = evFresh (viewV-ev refl vP) vQ
  ...   | inj₂ (inj₂ (Q′ , P′ , vQ , vP , refl)) = evBoth (viewV-ev refl vQ) (viewV-ev refl vP)

  -----------------------------------------------------------------------------------
  -- Rep-τ-elim : a τ step of Rep
  -----------------------------------------------------------------------------------

  -- the two ways Rep makes a τ
  data RepτR (P : ℕ → T) (k : ℕ) (Q : T) : T → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
    -- a running copy's τ
    τRun   : ∀ {Q′} → Q ─[ τ ]─► Q′ → RepτR P k Q (Rep merge P k Q′)
    -- the fresh copy's τ, which spawns copy k
    τFresh : ∀ {P′} → P k ─[ τ ]─► P′ → RepτR P k Q (Rep merge P (suc k) (Par ∅ES merge Q P′))

  -- every τ step of Rep is τRun or τFresh
  Rep-τ-elim : (P : ℕ → T) (k : ℕ) (Q : T) {M : T}
             → Rep merge P k Q ─[ τ ]─► M → RepτR P k Q M
  Rep-τ-elim P k Q st with τ-inv st
  ... | inj₁ ()
  ... | inj₂ (_ , _ , i , b , refl , br)
    with rep-tau-elim (force Q) (force (P k)) P k Q {i = i} {a = b} br
  ...   | inj₁ (_ , _ , Q′ , vQ , refl) = τRun (viewT-τ refl vQ)
  ...   | inj₂ (_ , _ , P′ , vP , refl) = τFresh (viewT-τ refl vP)

  -- Rep never terminates
  Rep-no-√ : (P : ℕ → T) (k : ℕ) (Q : T) {r : R} {M : T}
           → ¬ (Rep merge P k Q ─[ ev (√ r) ]─► M)
  Rep-no-√ P k Q (sRet ())

  -----------------------------------------------------------------------------------
  -- the collision node
  -----------------------------------------------------------------------------------

  -- the collision node offers nothing visible and never terminates
  repBoth-no-ev : (P : ℕ → T) (k : ℕ) (Q Q′ P′ : T) {l : Event√ R} {M : T}
                → ¬ (repBoth P k Q Q′ P′ ─[ ev l ]─► M)
  repBoth-no-ev P k Q Q′ P′ (sRet ())
  repBoth-no-ev P k Q Q′ P′ (sVis refl ())

  -- the collision node's τ goes to exactly one of its two branches
  repBoth-τ-elim : (P : ℕ → T) (k : ℕ) (Q Q′ P′ : T) {M : T}
                 → repBoth P k Q Q′ P′ ─[ τ ]─► M
                 → (M ≡ Rep merge P k Q′) ⊎ (M ≡ Rep merge P (suc k) (Par ∅ES merge Q P′))
  repBoth-τ-elim P k Q Q′ P′ st with τ-inv st
  ... | inj₁ ()
  ... | inj₂ (_ , _ , _ , _ , refl , br) = rep-brBoth-elim P k Q Q′ P′ br

  -- branch 0: the running copy took the event
  repBoth-τ0 : (P : ℕ → T) (k : ℕ) (Q Q′ P′ : T)
             → repBoth P k Q Q′ P′ ─[ τ ]─► Rep merge P k Q′
  repBoth-τ0 P k Q Q′ P′ = sTau {i = _ , fin {n = 2}} {a = lift fzero} refl refl

  -- branch 1: the fresh copy took the event (spawning copy k)
  repBoth-τ1 : (P : ℕ → T) (k : ℕ) (Q Q′ P′ : T)
             → repBoth P k Q Q′ P′ ─[ τ ]─► Rep merge P (suc k) (Par ∅ES merge Q P′)
  repBoth-τ1 P k Q Q′ P′ = sTau {i = _ , fin {n = 2}} {a = lift (fsuc fzero)} refl refl

  -----------------------------------------------------------------------------------
  -- intros: one per RepEvR / RepτR constructor
  -----------------------------------------------------------------------------------

  -- a running copy's lone visible step lifts to Rep
  Rep-evRun-intro : (P : ℕ → T) (k : ℕ) (Q : T) {X : Set ℓ} {e : E X} {a : X} {Q′ : T}
                  → Q ─[ ev (evl (evLabel X e a)) ]─► Q′
                  → viewV (force (P k)) (X , e) a ≡ nothing
                  → Rep merge P k Q ─[ ev (evl (evLabel X e a)) ]─► Rep merge P k Q′
  Rep-evRun-intro P k Q stQ nP =
    sVis refl (rep-vis-run (force Q) (force (P k)) P k Q (ev→viewV stQ) nP)

  -- the fresh copy's lone visible step lifts to Rep, spawning copy k
  Rep-evFresh-intro : (P : ℕ → T) (k : ℕ) (Q : T) {X : Set ℓ} {e : E X} {a : X} {P′ : T}
                    → P k ─[ ev (evl (evLabel X e a)) ]─► P′
                    → viewV (force Q) (X , e) a ≡ nothing
                    → Rep merge P k Q ─[ ev (evl (evLabel X e a)) ]─►
                        Rep merge P (suc k) (Par ∅ES merge Q P′)
  Rep-evFresh-intro P k Q stP nQ =
    sVis refl (rep-vis-fresh (force Q) (force (P k)) P k Q nQ (ev→viewV stP))

  -- a same-event offer by a running copy and the fresh copy lands in the collision node
  Rep-evBoth-intro : (P : ℕ → T) (k : ℕ) (Q : T) {X : Set ℓ} {e : E X} {a : X} {Q′ P′ : T}
                   → Q ─[ ev (evl (evLabel X e a)) ]─► Q′
                   → P k ─[ ev (evl (evLabel X e a)) ]─► P′
                   → Rep merge P k Q ─[ ev (evl (evLabel X e a)) ]─► repBoth P k Q Q′ P′
  Rep-evBoth-intro P k Q stQ stP =
    sVis refl (rep-vis-both (force Q) (force (P k)) P k Q (ev→viewV stQ) (ev→viewV stP))

  -- a running copy's τ lifts to Rep
  Rep-τRun-intro : (P : ℕ → T) (k : ℕ) (Q : T) {Q′ : T}
                 → Q ─[ τ ]─► Q′ → Rep merge P k Q ─[ τ ]─► Rep merge P k Q′
  Rep-τRun-intro P k Q stQ with τ→viewT stQ
  ... | j , b , eq = sTau {i = _ , pair (fin {n = 2}) (proj₂ j)} {a = lift fzero , b}
                          refl (rep-tau-run (force Q) (force (P k)) P k Q eq)

  -- the fresh copy's τ lifts to Rep, spawning copy k
  Rep-τFresh-intro : (P : ℕ → T) (k : ℕ) (Q : T) {P′ : T}
                   → P k ─[ τ ]─► P′
                   → Rep merge P k Q ─[ τ ]─► Rep merge P (suc k) (Par ∅ES merge Q P′)
  Rep-τFresh-intro P k Q stP with τ→viewT stP
  ... | j , b , eq = sTau {i = _ , pair (fin {n = 2}) (proj₂ j)} {a = lift (fsuc fzero) , b}
                          refl (rep-tau-fresh (force Q) (force (P k)) P k Q eq)
