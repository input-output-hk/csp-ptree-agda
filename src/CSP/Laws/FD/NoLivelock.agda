{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- The no-livelock bridge.
--
--   noLivelockT : a counting bound (every trace of P has at most F m events
--                 of H when it has m events outside H) plus "no reachable
--                 state of P diverges" ⇒ `P ∖ H` has NO divergences at all.
--
-- Route (constructive — no LEM, no König step, no `HideDivergence`):
--   1. `pull`  walks a run of `P ∖ H` back to a run of P (`Hide-τ-elim` /
--      `Hide-ev-elim`), carrying the bound as `Bnd H F Q k m` (k hidden and
--      m visible events spent so far) and premise (b) as `NoDiv Q`;
--   2. at the diverging endpoint, `div∖→modA` turns the divergence of
--      `Q ∖ H` into an infinite τ/H path of Q;
--   3. `¬modA` refutes that path by induction on the spare budget n
--      (`F m ≤ n + k`): `build` corecursively reads the path as a pure τ-run
--      (a `Diverges Q`, refuted by `NoDiv`), and `τOnly` refutes every H-step
--      on it — at n = 0 by the bound directly, at n = suc n′ by `¬modA n′`.
-- Also: `τ-AccReach-∖#`, the τ-Acc-FORM consequence of the same bound — the
-- hidden process is τ-accessible at every √-free reachable state.
--
-- No `postulate`, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; m≤m+n; ≤-trans; 1+n≰n)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import Process_Trees

module CSP.Laws.FD.NoLivelock {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.Deadlock {E = E} {I = ExtI E} using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (divergences; IsDivergence)
open import Semantics.DivergenceFree {E = E} {I = ExtI E}
  using (Diverges; τ-Acc; acc; τ-AccReach)
open import CSP.Laws.Traces.TraceLawsHide E-≟
  using (Hide-τ-elim; Hide-ev-elim; HideτR; hτP; hτH; heV; he√)
open import CSP.Laws.DivFree.ModAcc E-≟
  using (ModAStep; maτ; maE; DivModA; maNext; maStep; maRest; div∖→modA; deadlock-run-¬Div)

private
  variable
    ℓr : Level
    R  : Set ℓr

------------------------------------------------------------------------
-- §1. Counting the hidden / visible events of a trace
------------------------------------------------------------------------

-- number of events of `s` inside `H` (√ is never inside H)
#H : EventSet → List (Event√ R) → ℕ
#H H []                          = 0
#H H (evl (evLabel B e a) ∷ s) with H .dec (B , e) a
... | yes _ = suc (#H H s)
... | no  _ = #H H s
#H H (√ _ ∷ s)                   = #H H s

-- number of events of `s` outside `H` (√ counts as visible)
#V : EventSet → List (Event√ R) → ℕ
#V H []                          = 0
#V H (evl (evLabel B e a) ∷ s) with H .dec (B , e) a
... | yes _ = #V H s
... | no  _ = suc (#V H s)
#V H (√ _ ∷ s)                   = suc (#V H s)

-- an H-event raises the hidden count …
#H-in : (H : EventSet) {B : Set ℓ} {e : E B} {a : B} (s : List (Event√ R))
      → H .mem (B , e) a → #H H (evl (evLabel B e a) ∷ s) ≡ suc (#H H s)
#H-in H {B} {e} {a} s m with H .dec (B , e) a
... | yes _ = refl
... | no ¬m = ⊥-elim (¬m m)

-- … and leaves the visible count alone
#V-in : (H : EventSet) {B : Set ℓ} {e : E B} {a : B} (s : List (Event√ R))
      → H .mem (B , e) a → #V H (evl (evLabel B e a) ∷ s) ≡ #V H s
#V-in H {B} {e} {a} s m with H .dec (B , e) a
... | yes _ = refl
... | no ¬m = ⊥-elim (¬m m)

-- a non-H event leaves the hidden count alone …
#H-out : (H : EventSet) {B : Set ℓ} {e : E B} {a : B} (s : List (Event√ R))
       → ¬ H .mem (B , e) a → #H H (evl (evLabel B e a) ∷ s) ≡ #H H s
#H-out H {B} {e} {a} s ¬m with H .dec (B , e) a
... | yes m = ⊥-elim (¬m m)
... | no _  = refl

-- … and raises the visible count
#V-out : (H : EventSet) {B : Set ℓ} {e : E B} {a : B} (s : List (Event√ R))
       → ¬ H .mem (B , e) a → #V H (evl (evLabel B e a) ∷ s) ≡ suc (#V H s)
#V-out H {B} {e} {a} s ¬m with H .dec (B , e) a
... | yes m = ⊥-elim (¬m m)
... | no _  = refl

------------------------------------------------------------------------
-- §2. The bound and premise (b), carried along a run
------------------------------------------------------------------------

module _ (H : EventSet) (F : ℕ → ℕ) where

  -- Q, reached after k hidden and m visible events, keeps the bound on every continuation
  Bnd : ∀ {ℓr} {R : Set ℓr} → PTree E (ExtI E) R → ℕ → ℕ → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
  Bnd {R = R} Q k m =
    ∀ {s : List (Event√ R)} {Q′ : PTree E (ExtI E) R}
    → Q ⟹⟨ s ⟩ Q′ → k + #H H s ≤ F (m + #V H s)

  -- no state reachable from Q diverges
  NoDiv : ∀ {ℓr} {R : Set ℓr} → PTree E (ExtI E) R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
  NoDiv {R = R} Q = ∀ {s : List (Event√ R)} {Q′ : PTree E (ExtI E) R} → Q ⟹⟨ s ⟩ Q′ → ¬ Diverges Q′

  -- a τ changes neither count
  Bnd-τ : {Q Q′ : PTree E (ExtI E) R} {k m : ℕ} → Q ─[ τ ]─► Q′ → Bnd Q k m → Bnd Q′ k m
  Bnd-τ st b r = b (⟹-τ st r)

  -- an H-event spends one unit of hidden budget
  Bnd-H : {Q Q′ : PTree E (ExtI E) R} {k m : ℕ} {B : Set ℓ} {e : E B} {a : B}
        → H .mem (B , e) a → Q ─[ ev (evl (evLabel B e a)) ]─► Q′
        → Bnd Q k m → Bnd Q′ (suc k) m
  Bnd-H {k = k} {m} m∈ st b {s} r
    with b (⟹-ev st r)
  ... | le rewrite #H-in H s m∈ | #V-in H s m∈ | +-suc k (#H H s) = le

  -- a visible event raises the visible count
  Bnd-V : {Q Q′ : PTree E (ExtI E) R} {k m : ℕ} {B : Set ℓ} {e : E B} {a : B}
        → ¬ H .mem (B , e) a → Q ─[ ev (evl (evLabel B e a)) ]─► Q′
        → Bnd Q k m → Bnd Q′ k (suc m)
  Bnd-V {k = k} {m} m∉ st b {s} r
    with b (⟹-ev st r)
  ... | le rewrite #H-out H s m∉ | #V-out H s m∉ | +-suc m (#V H s) = le

  -- premise (b) survives every step
  NoDiv-step : {Q Q′ : PTree E (ExtI E) R} {l : Label R}
             → Q ─[ l ]─► Q′ → NoDiv Q → NoDiv Q′
  NoDiv-step {l = τ}    st nd r = nd (⟹-τ st r)
  NoDiv-step {l = ev _} st nd r = nd (⟹-ev st r)

  -- at zero spare budget a further H-event breaks the bound
  slack0 : ∀ {ℓr} {R : Set ℓr} {Q Q′ : PTree E (ExtI E) R} {k m : ℕ} {B : Set ℓ} {e : E B} {a : B}
         → F m ≤ k → Bnd Q k m
         → H .mem (B , e) a → Q ─[ ev (evl (evLabel B e a)) ]─► Q′ → ⊥
  slack0 {R = R} {k = k} {m} {B} {e} {a} le b m∈ st =
    1+n≰n (≤-trans (subst₂ _≤_ eqL eqR (b (⟹-ev st ⟹-refl))) le)
    where
      -- one hidden event on top of k
      eqL : k + #H H (evl {R = R} (evLabel B e a) ∷ []) ≡ suc k
      eqL = trans (cong (k +_) (#H-in H [] m∈)) (trans (+-suc k 0) (cong suc (+-identityʳ k)))
      -- no visible event on top of m
      eqR : F (m + #V H (evl {R = R} (evLabel B e a) ∷ [])) ≡ F m
      eqR = cong F (trans (cong (m +_) (#V-in H [] m∈)) (+-identityʳ m))

  ----------------------------------------------------------------------
  -- §3. The core: no infinite τ/H path within a finite hidden budget
  --     (forward declarations; ¬modA → build → τOnly → ¬modA at n−1)
  ----------------------------------------------------------------------

  -- an infinite τ/H path is impossible when the spare budget is n
  ¬modA : ∀ (n : ℕ) {Q : PTree E (ExtI E) R} {k m : ℕ}
        → F m ≤ n + k → Bnd Q k m → NoDiv Q → ¬ DivModA H Q

  -- every step of such a path is in fact a τ (an H-step would contradict the budget)
  τOnly : ∀ (n : ℕ) {Q Q′ : PTree E (ExtI E) R} {k m : ℕ}
        → F m ≤ n + k → Bnd Q k m → NoDiv Q
        → ModAStep H Q Q′ → DivModA H Q′ → Q ─[ τ ]─► Q′

  -- … so the path, read step by step, is a divergence of Q
  build : ∀ (n : ℕ) {Q : PTree E (ExtI E) R} {k m : ℕ}
        → F m ≤ n + k → Bnd Q k m → NoDiv Q → DivModA H Q → Diverges Q

  ¬modA n le b nd d = nd ⟹-refl (build n le b nd d)

  τOnly n       le b nd (maτ st)    _ = st
  τOnly zero    le b nd (maE m∈ st) _ = ⊥-elim (slack0 le b m∈ st)
  τOnly (suc n) {k = k} {m} le b nd (maE m∈ st) d =
    ⊥-elim (¬modA n (subst (F m ≤_) (sym (+-suc n k)) le) (Bnd-H m∈ st b) (NoDiv-step st nd) d)

  build n le b nd d .Diverges.next = d .maNext
  build n le b nd d .Diverges.step = τOnly n le b nd (d .maStep) (d .maRest)
  build n le b nd d .Diverges.rest =
    build n le (Bnd-τ st b) (NoDiv-step st nd) (d .maRest)
    where st = τOnly n le b nd (d .maStep) (d .maRest)

  -- walk a run of the hidden process back to P, then refute its endpoint's divergence
  pull : ∀ {t : List (Event√ R)} {W : PTree E (ExtI E) R} {Q : PTree E (ExtI E) R} {k m : ℕ}
       → (Q ∖ H) ⟹⟨ t ⟩ W → Bnd Q k m → NoDiv Q → ¬ Diverges W
  pull {Q = Q} {k} {m} ⟹-refl b nd d =
    ¬modA (F m) (m≤m+n (F m) k) b nd (div∖→modA H Q d)
  pull {Q = Q} (⟹-τ st r) b nd d with Hide-τ-elim H Q st
  ... | hτP Q′ τst refl    = pull r (Bnd-τ τst b) (NoDiv-step τst nd) d
  ... | hτH Q′ m∈ est refl = pull r (Bnd-H m∈ est b) (NoDiv-step est nd) d
  pull {Q = Q} (⟹-ev st r) b nd d with Hide-ev-elim H Q st
  ... | heV Q′ m∉ est = pull r (Bnd-V m∉ est b) (NoDiv-step est nd) d
  ... | he√ _         = deadlock-run-¬Div r d

  ----------------------------------------------------------------------
  -- §3′. The τ-Acc form: lexicographic on (spare budget, τ-Acc of the P-state)
  ----------------------------------------------------------------------

  -- the hidden process is τ-accessible within a finite hidden budget
  accHide : ∀ (n : ℕ) {Q : PTree E (ExtI E) R} {k m : ℕ}
          → F m ≤ n + k → Bnd Q k m → τ-AccReach Q → τ-Acc Q → τ-Acc (Q ∖ H)

  -- one τ of the hidden process, decoded (a τ of Q, or a hidden H-event of Q)
  accHideStep : ∀ (n : ℕ) {Q M : PTree E (ExtI E) R} {k m : ℕ}
              → F m ≤ n + k → Bnd Q k m → τ-AccReach Q → τ-Acc Q
              → HideτR H Q M → τ-Acc M

  accHide n {Q} le b ar a = acc λ st → accHideStep n le b ar a (Hide-τ-elim H Q st)

  accHideStep n le b ar (acc f) (hτP Q′ st refl) =
    accHide n le (Bnd-τ st b) (λ r → ar (∖√-τ st r)) (f st)
  accHideStep zero le b ar _ (hτH Q′ m∈ st refl) = ⊥-elim (slack0 le b m∈ st)
  accHideStep (suc n) {k = k} {m} le b ar _ (hτH Q′ m∈ st refl) =
    accHide n (subst (F m ≤_) (sym (+-suc n k)) le) (Bnd-H m∈ st b)
            (λ r → ar (∖√-ev st r)) (ar (∖√-ev st ∖√-refl))

  -- walk a √-free run of the hidden process back to P, then apply `accHide`
  pullAcc : ∀ {t : List Event} {W : PTree E (ExtI E) R} {Q : PTree E (ExtI E) R} {k m : ℕ}
          → (Q ∖ H) ⟹∖√⟨ t ⟩ W → Bnd Q k m → τ-AccReach Q → τ-Acc W
  pullAcc {Q = Q} {k} {m} ∖√-refl b ar = accHide (F m) (m≤m+n (F m) k) b ar (ar ∖√-refl)
  pullAcc {Q = Q} (∖√-τ st r) b ar with Hide-τ-elim H Q st
  ... | hτP Q′ τst refl    = pullAcc r (Bnd-τ τst b) (λ r′ → ar (∖√-τ τst r′))
  ... | hτH Q′ m∈ est refl = pullAcc r (Bnd-H m∈ est b) (λ r′ → ar (∖√-ev est r′))
  pullAcc {Q = Q} (∖√-ev st r) b ar with Hide-ev-elim H Q st
  ... | heV Q′ m∉ est = pullAcc r (Bnd-V m∉ est b) (λ r′ → ar (∖√-ev est r′))

------------------------------------------------------------------------
-- §4. THE BRIDGE
------------------------------------------------------------------------

-- a counting bound plus "no reachable state diverges" ⇒ hiding H creates no divergence
noLivelockT : (H : EventSet) (F : ℕ → ℕ) {P : PTree E (ExtI E) R}
  → (∀ {s Q} → P ⟹⟨ s ⟩ Q → #H H s ≤ F (#V H s))   -- (a) counting bound on every trace of P
  → (∀ {s Q} → P ⟹⟨ s ⟩ Q → ¬ Diverges Q)          -- (b) no reachable state of P diverges
  → ∀ {s} → ¬ divergences (P ∖ H) s
noLivelockT H F bnd nd d =
  pull H F (d .IsDivergence.reach) bnd nd (d .IsDivergence.divwit)

-- the τ-Acc form of the same bound: hiding H keeps τ-accessibility at every √-free reachable state
τ-AccReach-∖# : (H : EventSet) (F : ℕ → ℕ) {P : PTree E (ExtI E) R}
  → (∀ {s Q} → P ⟹⟨ s ⟩ Q → #H H s ≤ F (#V H s))
  → τ-AccReach P
  → τ-AccReach (P ∖ H)
τ-AccReach-∖# H F bnd ar r = pullAcc H F r bnd ar
