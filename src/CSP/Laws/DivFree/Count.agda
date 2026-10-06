{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Counting events of a process over its TRACES (Leios no-livelock,
-- Stage C, premise (a)).  Generic: no Leios/Cardano content.
--   * `#e`, `labels`, `Σc`  — visible events, their labels, a label weight
--   * `Dp n t`              — every trace of `t` has at most n visible events
--   * `Ends a t`, `Cm`      — every COMPLETED run of `t` returns `a` (and,
--                             for `Cm`, performed an `Rd` event on the way)
--   * `AllT`, `Post`        — a per-label invariant of every trace; a
--                             post-condition of every completed run
--   * `Rounds`              — a trace of `iter-bind t k` as completed rounds
--                             plus one partial round (inductive, structural)
--   * `ptrLoop`             — THE POINTER-LOOP BOUND: a loop whose round from
--                             state a has depth ≤ D, reads index `idx a` and
--                             advances, does at most D·(B∸idx a)+D events on
--                             any trace whose reads are all below B
--   * `invLoop`             — a loop invariant whose budget grows with the
--                             counted events, giving a per-label property
--   * `Σc-par`/`-parL`/`-parR` — additivity through `Par` (trace projection)
-- No postulate, no `NON_TERMINATING`, no sized types; closure postulate-free.
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; m≤m+n; m≤n+m; +-mono-≤; +-assoc; *-suc; +-identityʳ; +-monoʳ-≤; +-monoˡ-≤; +-comm)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; cong)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Laws.DivFree.Count {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)
open import CSP.Laws.Traces.TraceLawsBind E-≟
  using (EvlOnly; enil; econs; BindSplit; bs-live; bs-term; bind-elim-aux; ⟹-append-√)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟ using (□-trace-elim)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟
  using (deadlock-no-τ; deadlock-no-ev; ParInter; pnil; psync; psoloL; psoloR; p√)
open import CSP.Laws.DivFree.Loop E-≟
  using (iter-τ-elim; IterτR; itτ; itBack; iter-ev-elim; loopStep)

private
  variable
    ℓr ℓs : Level
    R : Set ℓr
    S : Set ℓs

------------------------------------------------------------------------
-- §1. Counting visible events
------------------------------------------------------------------------

-- the number of visible (non-√) events of a trace
#e : List (Event√ R) → ℕ
#e []          = 0
#e (evl _ ∷ s) = suc (#e s)
#e (√ _ ∷ s)   = #e s

-- `#e` is additive over `++`
#e-++ : (s₁ s₂ : List (Event√ R)) → #e (s₁ ++ s₂) ≡ #e s₁ + #e s₂
#e-++ []           s₂ = refl
#e-++ (evl _ ∷ s₁) s₂ = cong suc (#e-++ s₁ s₂)
#e-++ (√ _ ∷ s₁)   s₂ = #e-++ s₁ s₂

-- `EvlOnly` keeps the count
#e-EvlOnly : {r : List (Event√ R)} {s : List (Event√ S)} → EvlOnly r s → #e r ≡ #e s
#e-EvlOnly enil      = refl
#e-EvlOnly (econs e) = cong suc (#e-EvlOnly e)

-- a label predicate lifted to a trace element (`√` never satisfies it)
IsE : (Event → Set) → Event√ R → Set
IsE P (evl e) = P e
IsE P (√ _)   = ⊥

-- some visible event of the trace satisfies `P`
AnyE : (Event → Set) → List (Event√ R) → Set _
AnyE P = Any (IsE P)

-- `EvlOnly` carries `AnyE` across
AnyE-EvlOnly : {P : Event → Set} {r : List (Event√ R)} {s : List (Event√ S)}
             → EvlOnly r s → AnyE P r → AnyE P s
AnyE-EvlOnly (econs eo) (here p)  = here p
AnyE-EvlOnly (econs eo) (there a) = there (AnyE-EvlOnly eo a)

-- an `EvlOnly` image never ends in `√`
EvlOnly-no-√ : {r : List (Event√ R)} {s : List (Event√ S)} {y : S} → EvlOnly r (s ++ √ y ∷ []) → ⊥
EvlOnly-no-√ {s = []}    ()
EvlOnly-no-√ {s = _ ∷ s} (econs eo) = EvlOnly-no-√ {s = s} eo

-- split a √-terminated trace that is an `EvlOnly` prefix followed by a tail
split√ : {r : List (Event√ R)} {sS s s_k : List (Event√ S)} {y : S}
       → EvlOnly r sS → s ++ (√ y ∷ []) ≡ sS ++ s_k
       → Σ[ s₂ ∈ List (Event√ S) ] (s_k ≡ s₂ ++ (√ y ∷ []) × s ≡ sS ++ s₂)
split√ {s = s} enil eq = s , sym eq , refl
split√ {s = []}    (econs eo) ()
split√ {s = x ∷ s} (econs eo) eq with cong (λ { [] → [] ; (_ ∷ t) → t }) eq | cong (λ { [] → x ; (h ∷ _) → h }) eq
... | eq′ | refl with split√ {s = s} eo eq′
...   | s₂ , e₁ , e₂ = s₂ , e₁ , cong (x ∷_) e₂

------------------------------------------------------------------------
-- §2. Trace inversions for the leaf operators
------------------------------------------------------------------------

-- `Ret x` can only stay, or emit its `√` and stop
Ret-tr : {x : R} {s : List (Event√ R)} {W : PTree E (ExtI E) R}
       → Ret x ⟹⟨ s ⟩ W → (s ≡ []) ⊎ (s ≡ √ x ∷ [])
Ret-tr ⟹-refl                    = inj₁ refl
Ret-tr (⟹-τ (sSil ()) _)
Ret-tr (⟹-τ (sTau () _) _)
Ret-tr (⟹-ev (sRet refl) ⟹-refl)  = inj₂ refl
Ret-tr (⟹-ev (sRet refl) (⟹-τ st _))  = ⊥-elim (deadlock-no-τ st)
Ret-tr (⟹-ev (sRet refl) (⟹-ev st _)) = ⊥-elim (deadlock-no-ev st)
Ret-tr (⟹-ev (sVis () _) _)

-- a fired prefix offer names the prefix's own channel
pfx-cont : {A : Set ℓ} (e : E A) (P : A → PTree E (ExtI E) R) {at : AnyTypes E} {a : proj₁ at}
           {t′ : PTree E (ExtI E) R}
         → Prefix-cont e P at a ≡ just t′
         → Σ[ x ∈ A ] (evLabel (proj₁ at) (proj₂ at) a ≡ evLabel A e x × t′ ≡ P x)
pfx-cont {A = A} e P {at} {a} eq with E-≟ (A , e) at
... | yes refl = a , refl , sym (just-injective eq)
... | no _     = case eq of λ ()

-- a fired output offer names the output's own channel and value
out-cont : {A : Set ℓ} ⦃ _ : DecEq A ⦄ (e : E A) (v : A) (P : PTree E (ExtI E) R)
           {at : AnyTypes E} {a : proj₁ at} {t′ : PTree E (ExtI E) R}
         → Output-cont e v P at a ≡ just t′
         → evLabel (proj₁ at) (proj₂ at) a ≡ evLabel A e v × t′ ≡ P
out-cont {A = A} e v P {at} {a} eq with E-≟ (A , e) at
... | no _ = case eq of λ ()
... | yes refl with a Class.DecEq.≟ v
...   | yes refl = refl , sym (just-injective eq)
...   | no _     = case eq of λ ()

-- a trace of a prefix is empty, or its event followed by a trace of the continuation
pfx-tr : {A : Set ℓ} {e : E A} {P : A → PTree E (ExtI E) R} {s : List (Event√ R)} {W : PTree E (ExtI E) R}
       → (e ⟶ P) ⟹⟨ s ⟩ W
       → (s ≡ []) ⊎ Σ[ x ∈ A ] Σ[ s′ ∈ List (Event√ R) ] (s ≡ evl (evLabel A e x) ∷ s′ × P x ⟹⟨ s′ ⟩ W)
pfx-tr ⟹-refl = inj₁ refl
pfx-tr (⟹-τ (sSil ()) _)
pfx-tr (⟹-τ (sTau refl ()) _)
pfx-tr (⟹-ev (sRet ()) _)
pfx-tr {e = e} {P} (⟹-ev (sVis refl br) rest) with pfx-cont e P br
... | x , refl , refl = inj₂ (x , _ , refl , rest)

-- a trace of an output is empty, or its event followed by a trace of the continuation
out-tr : {A : Set ℓ} ⦃ _ : DecEq A ⦄ {e : E A} {v : A} {P : PTree E (ExtI E) R}
         {s : List (Event√ R)} {W : PTree E (ExtI E) R}
       → (e ! v ⟶ P) ⟹⟨ s ⟩ W
       → (s ≡ []) ⊎ Σ[ s′ ∈ List (Event√ R) ] (s ≡ evl (evLabel A e v) ∷ s′ × P ⟹⟨ s′ ⟩ W)
out-tr ⟹-refl = inj₁ refl
out-tr (⟹-τ (sSil ()) _)
out-tr (⟹-τ (sTau refl ()) _)
out-tr (⟹-ev (sRet ()) _)
out-tr {e = e} {v} {P} (⟹-ev (sVis refl br) rest) with out-cont e v P br
... | refl , refl = inj₂ (_ , refl , rest)

------------------------------------------------------------------------
-- §3. Depth
------------------------------------------------------------------------

-- every trace of `t` has at most `n` visible events
Dp : ℕ → PTree E (ExtI E) R → Set _
Dp n t = ∀ {s W} → t ⟹⟨ s ⟩ W → #e s ≤ n

-- weakening
Dp-mono : {m n : ℕ} {t : PTree E (ExtI E) R} → m ≤ n → Dp m t → Dp n t
Dp-mono m≤n d tr = ≤-trans (d tr) m≤n

-- a return has no visible event
Dp-Ret : {x : R} → Dp 0 (Ret x)
Dp-Ret tr with Ret-tr tr
... | inj₁ refl = z≤n
... | inj₂ refl = z≤n

-- a prefix adds one
Dp-⟶ : {n : ℕ} {A : Set ℓ} (e : E A) {P : A → PTree E (ExtI E) R}
     → (∀ x → Dp n (P x)) → Dp (suc n) (e ⟶ P)
Dp-⟶ e dp tr with pfx-tr tr
... | inj₁ refl                    = z≤n
... | inj₂ (x , s′ , refl , rest)  = s≤s (dp x rest)

-- an output adds one
Dp-Output : {n : ℕ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (e : E A) (v : A) {P : PTree E (ExtI E) R}
          → Dp n P → Dp (suc n) (e ! v ⟶ P)
Dp-Output e v dp tr with out-tr tr
... | inj₁ refl              = z≤n
... | inj₂ (s′ , refl , rest) = s≤s (dp rest)

-- a bind adds the two depths
Dp->>= : {m n : ℕ} {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
       → Dp m P → (∀ r → Dp n (k r)) → Dp (m + n) (P >>= k)
Dp->>= {m = m} {n} {P} {k} dp dk tr with bind-elim-aux P k tr
... | bs-live d eo = ≤-trans (subst (_≤ m) (#e-EvlOnly eo) (dp d)) (m≤m+n m n)
... | bs-term {sS = sS} {s_k = s_k} d fr eo (_ , kt) refl =
      subst (_≤ m + n) (sym (#e-++ sS s_k))
        (+-mono-≤ (subst (_≤ m) (#e-EvlOnly eo) (dp d)) (dk _ kt))

-- an external choice is no deeper than its deeper branch
Dp-□ : ⦃ _ : DecEq R ⦄ {n : ℕ} {P Q : PTree E (ExtI E) R} → Dp n P → Dp n Q → Dp n (P □ Q)
Dp-□ {P = P} {Q} dp dq tr with □-trace-elim P Q tr
... | inj₁ (_ , tP) = dp tP
... | inj₂ (_ , tQ) = dq tQ

------------------------------------------------------------------------
-- §4. Completion: what a run that RETURNS must have done
------------------------------------------------------------------------

-- every completed run of `t` returns `a`
Ends : R → PTree E (ExtI E) R → Set _
Ends a t = ∀ {s x W} → t ⟹⟨ s ++ (√ x ∷ []) ⟩ W → x ≡ a

-- every completed run of `t` returns `a` AND performed an `Rd` event
Cm : (Event → Set) → R → PTree E (ExtI E) R → Set _
Cm Rd a t = ∀ {s x W} → t ⟹⟨ s ++ (√ x ∷ []) ⟩ W → AnyE Rd s × x ≡ a

-- a list ending in an element is not empty
++∷≢[] : {A : Set ℓs} (s : List A) {y : A} → s ++ (y ∷ []) ≡ [] → ⊥
++∷≢[] []      ()
++∷≢[] (_ ∷ _) ()

-- peel the head off a √-terminated trace
peel : {e : Event} {s s′ : List (Event√ R)} {y : R}
     → s ++ (√ y ∷ []) ≡ evl e ∷ s′ → Σ[ s₀ ∈ List (Event√ R) ] (s ≡ evl e ∷ s₀ × s′ ≡ s₀ ++ (√ y ∷ []))
peel {s = []}    ()
peel {s = x ∷ s} refl = s , refl , refl

-- `Ret x` returns `x`
Ends-Ret : {x : R} → Ends x (Ret x)
Ends-Ret {s = s} tr with Ret-tr tr
... | inj₁ eq = ⊥-elim (++∷≢[] s eq)
... | inj₂ eq with s | eq
...   | []    | refl = refl
...   | _ ∷ s′ | eq′ = ⊥-elim (++∷≢[] s′ (cong (λ { [] → [] ; (_ ∷ t) → t }) eq′))

-- a prefix returns what its continuations return
Ends-⟶ : {a : R} {A : Set ℓ} (e : E A) {P : A → PTree E (ExtI E) R}
       → (∀ x → Ends a (P x)) → Ends a (e ⟶ P)
Ends-⟶ e ep {s = s} tr with pfx-tr tr
... | inj₁ eq = ⊥-elim (++∷≢[] s eq)
... | inj₂ (x , s′ , eq , rest) with peel {s = s} eq
...   | s₀ , refl , refl = ep x rest

-- an output returns what its continuation returns
Ends-Output : {a : R} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (e : E A) (v : A) {P : PTree E (ExtI E) R}
            → Ends a P → Ends a (e ! v ⟶ P)
Ends-Output e v ep {s = s} tr with out-tr tr
... | inj₁ eq = ⊥-elim (++∷≢[] s eq)
... | inj₂ (s′ , eq , rest) with peel {s = s} eq
...   | s₀ , refl , refl = ep rest

-- a bind returns what its continuation returns
Ends->>= : {a : S} {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
         → (∀ r → Ends a (k r)) → Ends a (P >>= k)
Ends->>= {P = P} {k} ek {s = s} tr with bind-elim-aux P k tr
... | bs-live d eo = ⊥-elim (EvlOnly-no-√ {s = s} eo)
... | bs-term d fr eo (_ , kt) seq with split√ {s = s} eo seq
...   | s₂ , refl , _ = ek _ kt

-- a bind whose head READS (and returns `x`) and whose continuation at `x` returns `a`
Cm->>= : {Rd : Event → Set} {x : R} {a : S} {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
       → Cm Rd x P → Ends a (k x) → Cm Rd a (P >>= k)
Cm->>= {P = P} {k} cp ek {s = s} tr with bind-elim-aux P k tr
... | bs-live d eo = ⊥-elim (EvlOnly-no-√ {s = s} eo)
... | bs-term {sR = sR} d fr eo (_ , kt) seq with split√ {s = s} eo seq | cp (⟹-append-√ d fr)
...   | s₂ , refl , refl | rd , refl = ++⁺ˡ (AnyE-EvlOnly eo rd) , ek kt

-- a prefix that is not yet the read: the read happens in every continuation
Cm-⟶ : {Rd : Event → Set} {a : R} {A : Set ℓ} (e : E A) {P : A → PTree E (ExtI E) R}
     → (∀ x → Cm Rd a (P x)) → Cm Rd a (e ⟶ P)
Cm-⟶ e cp {s = s} tr with pfx-tr tr
... | inj₁ eq = ⊥-elim (++∷≢[] s eq)
... | inj₂ (x , s′ , eq , rest) with peel {s = s} eq
...   | s₀ , refl , refl with cp x rest
...     | rd , ea = there rd , ea

-- THE read: a prefix every value of which is an `Rd` event
Cm-⟶-rd : {Rd : Event → Set} {a : R} {A : Set ℓ} (e : E A) {P : A → PTree E (ExtI E) R}
        → (∀ x → Rd (evLabel A e x)) → (∀ x → Ends a (P x)) → Cm Rd a (e ⟶ P)
Cm-⟶-rd e rd ep {s = s} tr with pfx-tr tr
... | inj₁ eq = ⊥-elim (++∷≢[] s eq)
... | inj₂ (x , s′ , eq , rest) with peel {s = s} eq
...   | s₀ , refl , refl = here (rd x) , ep x rest

------------------------------------------------------------------------
-- §5. Rounds of an iteration
------------------------------------------------------------------------

module _ {ℓx : Level} {Rx : Set ℓx} {A : Set ℓ} (k : A → PTree E (ExtI E) (A ⊎ Rx)) where

  -- a trace of `iter-bind t k`: inside the current round, or the round completes
  -- (loop-back to `k a′`) and the rest is a trace of the next rounds, or it returns
  data Rounds : PTree E (ExtI E) (A ⊎ Rx) → List (Event√ Rx) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓx) where
    rLive : ∀ {t r P″ s} → t ⟹⟨ r ⟩ P″ → EvlOnly r s → Rounds t s
    rBack : ∀ {t r P″ a′ s₁ s₂} → t ⟹⟨ r ⟩ P″ → force P″ ≡ ret (inj₁ a′) → EvlOnly r s₁
          → Rounds (k a′) s₂ → Rounds t (s₁ ++ s₂)
    rDone : ∀ {t r P″ x s₁} → t ⟹⟨ r ⟩ P″ → force P″ ≡ ret (inj₂ x) → EvlOnly r s₁
          → Rounds t (s₁ ++ (√ x ∷ []))

  -- a τ of the round tree extends the current round
  Rounds-τ : ∀ {t t′ s} → t ─[ τ ]─► t′ → Rounds t′ s → Rounds t s
  Rounds-τ st (rLive d eo)          = rLive (⟹-τ st d) eo
  Rounds-τ st (rBack d fr eo rs)    = rBack (⟹-τ st d) fr eo rs
  Rounds-τ st (rDone d fr eo)       = rDone (⟹-τ st d) fr eo

  -- a visible event of the round tree extends the current round
  Rounds-ev : ∀ {t t′ s} {e : Event} → t ─[ ev (evl e) ]─► t′ → Rounds t′ s → Rounds t (evl e ∷ s)
  Rounds-ev st (rLive d eo)          = rLive (⟹-ev st d) (econs eo)
  Rounds-ev st (rBack d fr eo rs)    = rBack (⟹-ev st d) fr (econs eo) rs
  Rounds-ev st (rDone d fr eo)       = rDone (⟹-ev st d) fr (econs eo)

  -- a `√` of the iteration is the round tree returning `inj₂`
  iter-√ : ∀ {t M} {x : Rx} → iter-bind t k ─[ ev (√ x) ]─► M → force t ≡ ret (inj₂ x)
  iter-√ {t} (sRet eqf) with force t in eqt | eqf
  ... | ret (inj₂ _) | refl = refl
  ... | ret (inj₁ _) | ()
  ... | sil _        | ()
  ... | react _ _    | ()

  -- every trace of `iter-bind t k` decomposes into rounds
  rounds : ∀ {t s W} → iter-bind t k ⟹⟨ s ⟩ W → Rounds t s
  rounds ⟹-refl = rLive ⟹-refl enil
  rounds {t} (⟹-τ st rest) with iter-τ-elim t k st
  ... | itτ t′ tτ refl      = Rounds-τ tτ (rounds rest)
  ... | itBack a′ fr refl   = rBack ⟹-refl fr enil (rounds rest)
  rounds {t} (⟹-ev {e = evl e} st rest) with iter-ev-elim t k st
  ... | t′ , tev , refl     = Rounds-ev tev (rounds rest)
  rounds {t} (⟹-ev {e = √ x} st ⟹-refl)     = rDone ⟹-refl (iter-√ st) enil
  rounds {t} (⟹-ev {e = √ x} (sRet _) (⟹-τ st _))  = ⊥-elim (deadlock-no-τ st)
  rounds {t} (⟹-ev {e = √ x} (sRet _) (⟹-ev st _)) = ⊥-elim (deadlock-no-ev st)

------------------------------------------------------------------------
-- §6. The pointer-loop bound
------------------------------------------------------------------------

-- `B ∸ k` is one more than `B ∸ suc k` below the bound
∸-suc : ∀ {k B} → k < B → B ∸ k ≡ suc (B ∸ suc k)
∸-suc {zero}  {suc B} (s≤s z≤n)  = refl
∸-suc {suc k} {suc B} (s≤s k<B) = ∸-suc k<B

-- arithmetic: one more round of cost ≤ D below the potential
ptr-arith : (D B k x y : ℕ) → k < B → x ≤ D → y ≤ D * (B ∸ suc k) + D → x + y ≤ D * (B ∸ k) + D
ptr-arith D B k x y k<B x≤ y≤
  rewrite ∸-suc k<B | *-suc D (B ∸ suc k) | +-assoc D (D * (B ∸ suc k)) D = +-mono-≤ x≤ y≤

module _ {A : Set ℓ} {body : A → PTree E (ExtI E) A} {idx : A → ℕ} {nxt : A → A}
         (idx-nxt : ∀ a → idx (nxt a) ≡ suc (idx a))
         {Rd : ℕ → Event → Set} {D B : ℕ}
         (dp : ∀ a → Dp D (loopStep {R = R} body a))
         (cm : ∀ a → Cm (Rd (idx a)) (inj₁ (nxt a)) (loopStep {R = R} body a)) where

  -- the bound along the rounds, from state a
  ptrRounds : ∀ a {s} → Rounds {Rx = R} (loopStep body) (loopStep body a) s
            → (∀ j → AnyE (Rd j) s → j < B) → #e s ≤ D * (B ∸ idx a) + D
  ptrRounds a (rLive d eo) rb =
    ≤-trans (subst (_≤ D) (#e-EvlOnly eo) (dp a d)) (m≤n+m D (D * (B ∸ idx a)))
  ptrRounds a (rBack {s₁ = s₁} {s₂ = s₂} d fr eo rs) rb with cm a (⟹-append-√ d fr)
  ... | rd , refl =
    subst (_≤ D * (B ∸ idx a) + D) (sym (#e-++ s₁ s₂))
      (ptr-arith D B (idx a) (#e s₁) (#e s₂)
        (rb (idx a) (++⁺ˡ (AnyE-EvlOnly eo rd)))
        (subst (_≤ D) (#e-EvlOnly eo) (dp a d))
        (subst (λ i → #e s₂ ≤ D * (B ∸ i) + D) (idx-nxt a)
           (ptrRounds (nxt a) rs (λ j x → rb j (++⁺ʳ s₁ x)))))
  ptrRounds a (rDone {x = x} {s₁ = s₁} d fr eo) rb =
    subst (_≤ D * (B ∸ idx a) + D) (sym (#e-++ s₁ (√ x ∷ [])))
      (subst (_≤ D * (B ∸ idx a) + D) (sym (+-identityʳ (#e s₁)))
        (≤-trans (subst (_≤ D) (#e-EvlOnly eo) (dp a d)) (m≤n+m D (D * (B ∸ idx a)))))

  -- THE POINTER-LOOP BOUND
  ptrLoop : ∀ a {s W} → loop {R = R} body a ⟹⟨ s ⟩ W
          → (∀ j → AnyE (Rd j) s → j < B) → #e s ≤ D * (B ∸ idx a) + D
  ptrLoop a tr = ptrRounds a (rounds {Rx = R} (loopStep body) tr)

------------------------------------------------------------------------
-- §7. Per-event invariants and post-conditions of a round
------------------------------------------------------------------------

-- the labels of a trace (`√` dropped)
labels : List (Event√ R) → List Event
labels []          = []
labels (evl e ∷ s) = e ∷ labels s
labels (√ _ ∷ s)   = labels s

-- `labels` distributes over `++`
labels-++ : (s₁ s₂ : List (Event√ R)) → labels (s₁ ++ s₂) ≡ labels s₁ ++ labels s₂
labels-++ []           s₂ = refl
labels-++ (evl e ∷ s₁) s₂ = cong (e ∷_) (labels-++ s₁ s₂)
labels-++ (√ _ ∷ s₁)   s₂ = labels-++ s₁ s₂

-- `EvlOnly` keeps the labels
labels-EvlOnly : {r : List (Event√ R)} {s : List (Event√ S)} → EvlOnly r s → labels r ≡ labels s
labels-EvlOnly enil      = refl
labels-EvlOnly (econs e) = cong (_ ∷_) (labels-EvlOnly e)

-- the weight of a label list
Σc : (Event → ℕ) → List Event → ℕ
Σc c []      = 0
Σc c (e ∷ s) = c e + Σc c s

-- `Σc` is additive
Σc-++ : (c : Event → ℕ) (s₁ s₂ : List Event) → Σc c (s₁ ++ s₂) ≡ Σc c s₁ + Σc c s₂
Σc-++ c []       s₂ = refl
Σc-++ c (e ∷ s₁) s₂ = trans (cong (c e +_) (Σc-++ c s₁ s₂)) (sym (+-assoc (c e) (Σc c s₁) (Σc c s₂)))

-- every label of the list satisfies `P`
data AllL (P : Event → Set) : List Event → Set (lsuc ℓ ⊔ ℓe) where
  []  : AllL P []
  _∷_ : ∀ {e s} → P e → AllL P s → AllL P (e ∷ s)

-- `AllL` over `++`
AllL-++ : {P : Event → Set} {s₁ s₂ : List Event} → AllL P s₁ → AllL P s₂ → AllL P (s₁ ++ s₂)
AllL-++ []       a₂ = a₂
AllL-++ (p ∷ a₁) a₂ = p ∷ AllL-++ a₁ a₂

-- `AllL` is monotone in the predicate
AllL-map : {P Q : Event → Set} {s : List Event} → (∀ {e} → P e → Q e) → AllL P s → AllL Q s
AllL-map f []      = []
AllL-map f (p ∷ a) = f p ∷ AllL-map f a

-- every label of every trace of `t` satisfies `P`
AllT : (Event → Set) → PTree E (ExtI E) R → Set _
AllT P t = ∀ {s W} → t ⟹⟨ s ⟩ W → AllL P (labels s)

-- a return performs nothing
AllT-Ret : {P : Event → Set} {x : R} → AllT P (Ret x)
AllT-Ret tr with Ret-tr tr
... | inj₁ refl = []
... | inj₂ refl = []

-- a prefix whose every value satisfies `P`
AllT-⟶ : {P : Event → Set} {A : Set ℓ} (e : E A) {Q : A → PTree E (ExtI E) R}
       → (∀ x → P (evLabel A e x)) → (∀ x → AllT P (Q x)) → AllT P (e ⟶ Q)
AllT-⟶ e p q tr with pfx-tr tr
... | inj₁ refl                   = []
... | inj₂ (x , s′ , refl , rest) = p x ∷ q x rest

-- an output whose value satisfies `P`
AllT-Output : {P : Event → Set} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (e : E A) (v : A) {Q : PTree E (ExtI E) R}
            → P (evLabel A e v) → AllT P Q → AllT P (e ! v ⟶ Q)
AllT-Output e v p q tr with out-tr tr
... | inj₁ refl               = []
... | inj₂ (s′ , refl , rest) = p ∷ q rest

-- both branches of a choice
AllT-□ : ⦃ _ : DecEq R ⦄ {P : Event → Set} {Q₁ Q₂ : PTree E (ExtI E) R} → AllT P Q₁ → AllT P Q₂ → AllT P (Q₁ □ Q₂)
AllT-□ {Q₁ = Q₁} {Q₂} a₁ a₂ tr with □-trace-elim Q₁ Q₂ tr
... | inj₁ (_ , t₁) = a₁ t₁
... | inj₂ (_ , t₂) = a₂ t₂

-- both halves of a bind
AllT->>= : {P : Event → Set} {Q : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
         → AllT P Q → (∀ r → AllT P (k r)) → AllT P (Q >>= k)
AllT->>= {Q = Q} {k} aq ak tr with bind-elim-aux Q k tr
... | bs-live d eo = subst (AllL _) (labels-EvlOnly eo) (aq d)
... | bs-term {sS = sS} {s_k = s_k} d fr eo (_ , kt) refl =
      subst (AllL _) (sym (labels-++ sS s_k)) (AllL-++ (subst (AllL _) (labels-EvlOnly eo) (aq d)) (ak _ kt))

-- every completed run of `t` satisfies `Q` (of its labels and its return value) — raw form
PostR : (List Event → R → Set) → PTree E (ExtI E) R → Set _
PostR Q t = ∀ {s x W} → t ⟹⟨ s ++ (√ x ∷ []) ⟩ W → Q (labels s) x

-- … wrapped, so that `Q` unifies first-order at use sites
record Post {ℓq} {Rq : Set ℓq} (Q : List Event → Rq → Set) (t : PTree E (ExtI E) Rq)
       : Set (lsuc ℓ ⊔ ℓe ⊔ ℓq) where
  constructor post
  field run : PostR Q t
open Post public

-- a return: the empty run (raw)
Post-Ret′ : {Q : List Event → R → Set} {x : R} → Q [] x → PostR Q (Ret x)
Post-Ret′ {x = x} q {s = s} tr with Ret-tr tr
... | inj₁ eq = ⊥-elim (++∷≢[] s eq)
... | inj₂ eq with s | eq
...   | []     | refl = q
...   | _ ∷ s′ | eq′  = ⊥-elim (++∷≢[] s′ (cong (λ { [] → [] ; (_ ∷ t) → t }) eq′))

-- a return: the empty run
Post-Ret : {Q : List Event → R → Set} {x : R} → Q [] x → Post Q (Ret x)
Post-Ret {Q = Q} q = post (Post-Ret′ {Q = Q} q)

-- a prefix: the continuation's post-condition, shifted by the event (raw)
Post-⟶′ : {Q : List Event → R → Set} {A : Set ℓ} (e : E A) {P : A → PTree E (ExtI E) R}
        → (∀ x → Post (λ ls r → Q (evLabel A e x ∷ ls) r) (P x)) → PostR Q (e ⟶ P)
Post-⟶′ e pp {s = s} tr with pfx-tr tr
... | inj₁ eq = ⊥-elim (++∷≢[] s eq)
... | inj₂ (x , s′ , eq , rest) with peel {s = s} eq
...   | s₀ , refl , refl = run (pp x) rest

-- a prefix
Post-⟶ : {Q : List Event → R → Set} {A : Set ℓ} (e : E A) {P : A → PTree E (ExtI E) R}
       → (∀ x → Post (λ ls r → Q (evLabel A e x ∷ ls) r) (P x)) → Post Q (e ⟶ P)
Post-⟶ {Q = Q} e pp = post (Post-⟶′ {Q = Q} e pp)

-- an output (raw)
Post-Output′ : {Q : List Event → R → Set} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (e : E A) (v : A) {P : PTree E (ExtI E) R}
             → Post (λ ls r → Q (evLabel A e v ∷ ls) r) P → PostR Q (e ! v ⟶ P)
Post-Output′ e v pp {s = s} tr with out-tr tr
... | inj₁ eq = ⊥-elim (++∷≢[] s eq)
... | inj₂ (s′ , eq , rest) with peel {s = s} eq
...   | s₀ , refl , refl = run pp rest

-- an output
Post-Output : {Q : List Event → R → Set} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (e : E A) (v : A) {P : PTree E (ExtI E) R}
            → Post (λ ls r → Q (evLabel A e v ∷ ls) r) P → Post Q (e ! v ⟶ P)
Post-Output {Q = Q} e v pp = post (Post-Output′ {Q = Q} e v pp)

-- a choice: both branches
Post-□ : ⦃ _ : DecEq R ⦄ {Q : List Event → R → Set} {P₁ P₂ : PTree E (ExtI E) R}
       → Post Q P₁ → Post Q P₂ → Post Q (P₁ □ P₂)
Post-□ {Q = Q} {P₁ = P₁} {P₂} q₁ q₂ = post go
  where
    -- the run itself
    go : PostR Q (P₁ □ P₂)
    go tr with □-trace-elim P₁ P₂ tr
    ... | inj₁ (_ , t₁) = run q₁ t₁
    ... | inj₂ (_ , t₂) = run q₂ t₂

-- a bind (raw)
Post->>=′ : {Q₁ : List Event → R → Set} {Q : List Event → S → Set}
            {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
          → Post Q₁ P → (∀ {ls₁ r} → Q₁ ls₁ r → Post (λ ls₂ x → Q (ls₁ ++ ls₂) x) (k r))
          → PostR Q (P >>= k)
Post->>=′ {Q = Q} {P = P} {k} p₁ p₂ {s = s} tr with bind-elim-aux P k tr
... | bs-live d eo = ⊥-elim (EvlOnly-no-√ {s = s} eo)
... | bs-term {sR = sR} {sS = sS} d fr eo (_ , kt) seq with split√ {s = s} eo seq
...   | s₂ , refl , refl =
        subst (λ ls → Q ls _) (trans (cong (_++ labels s₂) (labels-EvlOnly eo)) (sym (labels-++ sS s₂)))
          (run (p₂ (run p₁ (⟹-append-√ d fr))) kt)

-- a bind: the head's post-condition, then the continuation's at the head's return value
Post->>= : {Q₁ : List Event → R → Set} {Q : List Event → S → Set}
           {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
         → Post Q₁ P → (∀ {ls₁ r} → Q₁ ls₁ r → Post (λ ls₂ x → Q (ls₁ ++ ls₂) x) (k r))
         → Post Q (P >>= k)
Post->>= {Q₁ = Q₁} {Q = Q} p₁ p₂ = post (Post->>=′ {Q₁ = Q₁} {Q = Q} p₁ p₂)

------------------------------------------------------------------------
-- §8. The invariant-loop lemma (a budget that grows with counted events)
------------------------------------------------------------------------

-- the invariant at a round's return value (a loop-back carries the new state)
InvAt : {A : Set ℓ} → (A → ℕ → Set) → A ⊎ R → ℕ → Set
InvAt I (inj₁ a) n = I a n
InvAt I (inj₂ _) n = ⊤′
  where
    -- the trivially true proposition
    data ⊤′ : Set where tt′ : ⊤′

module _ {A : Set ℓ} {body : A → PTree E (ExtI E) A}
         (I : A → ℕ → Set) (c : Event → ℕ) (Ok : ℕ → Event → Set)
         (Ok-mono : ∀ {m m′ e} → m ≤ m′ → Ok m e → Ok m′ e)
         (rOk  : ∀ {a m} → I a m → AllT (Ok m) (loopStep {R = R} body a))
         (rInv : ∀ {a m} → I a m → Post (λ ls x → InvAt I x (m + Σc c ls))
                                        (loopStep {R = R} body a)) where

  -- the invariant along the rounds
  invRounds : ∀ {a m s} → I a m → Rounds {Rx = R} (loopStep body) (loopStep body a) s
            → AllL (Ok (m + Σc c (labels s))) (labels s)
  invRounds {m = m} i (rLive d eo) =
    subst (λ ls → AllL (Ok (m + Σc c ls)) ls) (labels-EvlOnly eo)
      (AllL-map (Ok-mono (m≤m+n m _)) (rOk i d))
  invRounds {m = m} i (rBack {r = r} {s₁ = s₁} {s₂ = s₂} d fr eo rs) =
    subst (λ ls → AllL (Ok (m + Σc c ls)) ls) (sym (labels-++ s₁ s₂))
      (AllL-++
        (AllL-map (Ok-mono (m≤m+n m (Σc c (labels s₁ ++ labels s₂))))
          (subst (AllL (Ok m)) (labels-EvlOnly eo) (rOk i d)))
        (subst (λ z → AllL (Ok z) (labels s₂))
           (trans (+-assoc m _ _) (cong (m +_) (sym (Σc-++ c (labels s₁) (labels s₂)))))
           (invRounds (subst (λ ls → I _ (m + Σc c ls)) (labels-EvlOnly eo) (run (rInv i) (⟹-append-√ d fr))) rs)))
  invRounds {m = m} i (rDone {x = x} {s₁ = s₁} d fr eo) =
    subst (λ ls → AllL (Ok (m + Σc c ls)) ls) (sym (trans (labels-++ s₁ (√ x ∷ [])) (++-[] (labels s₁))))
      (subst (λ ls → AllL (Ok (m + Σc c ls)) ls) (labels-EvlOnly eo)
        (AllL-map (Ok-mono (m≤m+n m _)) (rOk i d)))
    where
      -- right identity of `++`
      ++-[] : (xs : List Event) → xs ++ [] ≡ xs
      ++-[] []       = refl
      ++-[] (x ∷ xs) = cong (x ∷_) (++-[] xs)

  -- THE INVARIANT-LOOP LEMMA
  invLoop : ∀ {a m s W} → I a m → loop {R = R} body a ⟹⟨ s ⟩ W
          → AllL (Ok (m + Σc c (labels s))) (labels s)
  invLoop i tr = invRounds i (rounds {Rx = R} _ tr)

-- `Stop` performs nothing
AllT-Stop : {P : Event → Set} → AllT P (Stop {R = R})
AllT-Stop ⟹-refl = []
AllT-Stop (⟹-τ (sSil ()) _)
AllT-Stop (⟹-τ (sTau refl ()) _)
AllT-Stop (⟹-ev (sRet ()) _)
AllT-Stop (⟹-ev (sVis refl ()) _)

-- `Stop` never completes (raw)
Post-Stop′ : {Q : List Event → R → Set} → PostR Q (Stop {R = R})
Post-Stop′ {s = []}    (⟹-τ (sSil ()) _)
Post-Stop′ {s = []}    (⟹-τ (sTau refl ()) _)
Post-Stop′ {s = []}    (⟹-ev (sRet ()) _)
Post-Stop′ {s = _ ∷ _} (⟹-τ (sSil ()) _)
Post-Stop′ {s = _ ∷ _} (⟹-τ (sTau refl ()) _)
Post-Stop′ {s = _ ∷ _} (⟹-ev (sRet ()) _)
Post-Stop′ {s = _ ∷ _} (⟹-ev (sVis refl ()) _)

-- `Stop` never completes
Post-Stop : {Q : List Event → R → Set} → Post Q (Stop {R = R})
Post-Stop {Q = Q} = post (Post-Stop′ {Q = Q})


------------------------------------------------------------------------
-- §9. Additivity through parallel composition (trace projection)
------------------------------------------------------------------------

-- the weight of a composite trace is at most the sum of its projections' weights
Σc-par : (c : Event → ℕ) {ℓ₁ ℓ₂ ℓs : Level} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R₀ : Set ℓs}
         {A : EventSet} {merge : R₁ → R₂ → R₀}
         {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R₀)}
       → ParInter A merge sP sQ s
       → Σc c (labels s) ≤ Σc c (labels sP) + Σc c (labels sQ)
Σc-par c pnil = z≤n
Σc-par c {sP = evl e ∷ sP} {sQ = _ ∷ sQ} {s = _ ∷ s} (psync _ pi) =
  ≤-trans (+-monoʳ-≤ (c e) (Σc-par c pi))
    (≤-trans (≤-reflexive′ (sym (+-assoc (c e) (Σc c (labels sP)) (Σc c (labels sQ)))))
             (+-monoʳ-≤ (c e + Σc c (labels sP)) (m≤n+m (Σc c (labels sQ)) (c e))))
  where
    -- an equation read as an inequality
    ≤-reflexive′ : ∀ {x y} → x ≡ y → x ≤ y
    ≤-reflexive′ refl = ≤-refl
Σc-par c {sP = evl e ∷ sP} {sQ = sQ} {s = _ ∷ s} (psoloL _ pi) =
  subst (c e + Σc c (labels s) ≤_) (sym (+-assoc (c e) (Σc c (labels sP)) (Σc c (labels sQ))))
    (+-monoʳ-≤ (c e) (Σc-par c pi))
Σc-par c {sP = sP} {sQ = evl e ∷ sQ} {s = _ ∷ s} (psoloR _ pi) =
  subst (c e + Σc c (labels s) ≤_) (sym (+-comm′ (Σc c (labels sP)) (c e) (Σc c (labels sQ))))
    (+-monoʳ-≤ (c e) (Σc-par c pi))
  where
    -- `x + (y + z) ≡ y + (x + z)`
    +-comm′ : ∀ x y z → x + (y + z) ≡ y + (x + z)
    +-comm′ x y z = trans (sym (+-assoc x y z)) (trans (cong (_+ z) (+-comm x y)) (+-assoc y x z))
Σc-par c p√ = z≤n

-- the LEFT projection weighs at most the composite
Σc-parL : (c : Event → ℕ) {ℓ₁ ℓ₂ ℓs : Level} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R₀ : Set ℓs}
          {A : EventSet} {merge : R₁ → R₂ → R₀}
          {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R₀)}
        → ParInter A merge sP sQ s → Σc c (labels sP) ≤ Σc c (labels s)
Σc-parL c pnil                               = z≤n
Σc-parL c {sP = evl e ∷ _} (psync _ pi)      = +-monoʳ-≤ (c e) (Σc-parL c pi)
Σc-parL c {sP = evl e ∷ _} (psoloL _ pi)     = +-monoʳ-≤ (c e) (Σc-parL c pi)
Σc-parL c {s = evl e ∷ _} (psoloR _ pi)      = ≤-trans (Σc-parL c pi) (m≤n+m _ (c e))
Σc-parL c p√                                 = z≤n

-- the RIGHT projection weighs at most the composite
Σc-parR : (c : Event → ℕ) {ℓ₁ ℓ₂ ℓs : Level} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R₀ : Set ℓs}
          {A : EventSet} {merge : R₁ → R₂ → R₀}
          {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R₀)}
        → ParInter A merge sP sQ s → Σc c (labels sQ) ≤ Σc c (labels s)
Σc-parR c pnil                               = z≤n
Σc-parR c {sQ = evl e ∷ _} (psync _ pi)      = +-monoʳ-≤ (c e) (Σc-parR c pi)
Σc-parR c {s = evl e ∷ _} (psoloL _ pi)      = ≤-trans (Σc-parR c pi) (m≤n+m _ (c e))
Σc-parR c {sQ = evl e ∷ _} (psoloR _ pi)     = +-monoʳ-≤ (c e) (Σc-parR c pi)
Σc-parR c p√                                 = z≤n
