{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Modulo-H accessibility at every REACHABLE state, closed under the
-- composition operators (the gap recorded at `Parametric/Assembly.agda`
-- 32-45: the existing `CSP.Laws.DivFree.Closure` lemmas cover the root only).
--
--   * `MAccR-Par` — generalised parallel, ASYMMETRIC in H: the left operand
--     counts every H-event, the right operand only its SOLO H-events
--     (`H −H A`).  Sound because a synchronised H-step always advances the
--     left operand.  With `H = ∅ES` it is the symmetric τ-Acc closure.
--   * `MAccR-∖`  — hiding moves events from H to τ: MAcc (A ∪H B) ⇒ MAcc B (· ∖ A).
--   * the CSP instances `∥⇘ ⇙`, `⦀`, `⦀⁺`, `⦀Fin⁺`, `⦀Fin`, `⦀⋆`, and `Ret`/`Skip`.
--
-- No `postulate`, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees

module CSP.Laws.DivFree.Reach {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Deadlock {E = E} {I = ExtI E} using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Semantics.DivergenceFree {E = E} {I = ExtI E} using (ret→no-τ)
open import CSP.Laws.Traces.TraceLawsHide E-≟
  using (Hide-τ-elim; Hide-ev-elim; HideτR; hτP; hτH; HideevR; heV)
open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Mg)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟
  using (Par-τ-elim; ParτR; τL; τR; Par-ev-elim; ParevR; evSync; evL; evR; evBoth)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟ using (brBoth-τ-elim; brBoth-no-ev)
open import CSP.Laws.DivFree.ModAcc E-≟

private
  variable
    ℓr : Level
    R  : Set ℓr

------------------------------------------------------------------------
-- §1. Leaves
------------------------------------------------------------------------

-- `ret` and `react` are distinct node kinds
ret≢react : ∀ {r : R} {v τc} → _≡_ {A = NodeKind E (ExtI E) R} (ret r) (react v τc) → ⊥
ret≢react ()

-- a `ret` node has no modulo-H step at all
ret→MAcc : {H : EventSet} {t : PTree E (ExtI E) R} {r : R}
         → PTree.force t ≡ ret r → MAcc H t
ret→MAcc eqf = macc λ where
  (maτ st) → ⊥-elim (ret→no-τ eqf st)
  (maE _ (sVis eqv _)) → ⊥-elim (ret≢react (trans (sym eqf) eqv))

-- `Ret r` can only tick √, so its √-free runs stay put
MAccR-Ret : {H : EventSet} (r : R) → MAccR H (Ret r)
MAccR-Ret r ∖√-refl                      = ret→MAcc refl
MAccR-Ret r (∖√-τ st _)                  = ⊥-elim (ret→no-τ refl st)
MAccR-Ret r (∖√-ev (sVis () _) _)

-- `Skip`
MAccR-Skip : ∀ {ℓx : Level} {H : EventSet} → MAccR H (Skip {ℓx})
MAccR-Skip = MAccR-Ret tt

------------------------------------------------------------------------
-- §2. Generalised parallel (asymmetric in H)
------------------------------------------------------------------------

module _ {ℓ₁ ℓ₂ ℓs} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R : Set ℓs}
         (A H : EventSet) (mg : Mg R₁ R₂ R) where

  -- the right operand's accessibility, at every state reachable from Q
  RAcc : PTree E (ExtI E) R₂ → Set (lsuc ℓ ⊔ ℓe ⊔ ℓ₂)
  RAcc Q = MAccR (H −H A) Q

  -- the both-offer overlap node `(Par P′ Q) ⊓ (Par P Q′)`
  Both : PTree E (ExtI E) R₁ → PTree E (ExtI E) R₂
       → PTree E (ExtI E) R₁ → PTree E (ExtI E) R₂ → PTree E (ExtI E) R
  Both P Q P′ Q′ = ptree (react (λ _ _ → nothing) (par-brBoth A mg P Q P′ Q′))

  -- root closure, lexicographic on (MAcc of P, MAcc of Q)
  MAcc-Par : {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂}
           → MAcc H P → MAcc (H −H A) Q → RAcc Q → MAcc H (Par A mg P Q)

  -- one modulo-H step of the composite, by cases
  MAcc-Par-τ : {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂} {M : PTree E (ExtI E) R}
             → MAcc H P → MAcc (H −H A) Q → RAcc Q → ParτR A mg P Q M → MAcc H M
  MAcc-Par-ev : {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂} {M : PTree E (ExtI E) R}
                {B : Set ℓ} {e : E B} {a : B}
              → MAcc H P → MAcc (H −H A) Q → RAcc Q → H .mem (B , e) a
              → ParevR A mg P Q M (evl (evLabel B e a)) → MAcc H M
  -- the overlap node: its two τ's land on `Par P′ Q` / `Par P Q′`
  MAcc-Both : {P P′ : PTree E (ExtI E) R₁} {Q Q′ : PTree E (ExtI E) R₂}
            → MAcc H P′ → MAcc H P → MAcc (H −H A) Q′ → MAcc (H −H A) Q
            → RAcc Q′ → RAcc Q → MAcc H (Both P Q P′ Q′)
  -- the overlap node's two commit branches
  MAcc-Both-τ : {P P′ : PTree E (ExtI E) R₁} {Q Q′ : PTree E (ExtI E) R₂} {M : PTree E (ExtI E) R}
              → MAcc H P′ → MAcc H P → MAcc (H −H A) Q′ → MAcc (H −H A) Q
              → RAcc Q′ → RAcc Q
              → (M ≡ Par A mg P′ Q) ⊎ (M ≡ Par A mg P Q′) → MAcc H M

  MAcc-Par {P} {Q} ap aq rq = macc λ where
    (maτ st)    → MAcc-Par-τ ap aq rq (Par-τ-elim A mg P Q st)
    (maE m∈ st) → MAcc-Par-ev ap aq rq m∈ (Par-ev-elim A mg P Q st)

  MAcc-Par-τ (macc fp) aq rq (τL P′ st refl) = MAcc-Par (fp (maτ st)) aq rq
  MAcc-Par-τ ap (macc fq) rq (τR Q′ st refl) =
    MAcc-Par ap (fq (maτ st)) (λ r → rq (∖√-τ st r))

  MAcc-Par-ev (macc fp) aq rq m∈ (evSync _ stP stQ) =
    MAcc-Par (fp (maE m∈ stP)) (rq (∖√-ev stQ ∖√-refl)) (λ r → rq (∖√-ev stQ r))
  MAcc-Par-ev (macc fp) aq rq m∈ (evL _ stP) = MAcc-Par (fp (maE m∈ stP)) aq rq
  MAcc-Par-ev ap (macc fq) rq m∈ (evR a∉ stQ) =
    MAcc-Par ap (fq (maE (m∈ , a∉) stQ)) (λ r → rq (∖√-ev stQ r))
  MAcc-Par-ev (macc fp) (macc fq) rq m∈ (evBoth a∉ stP stQ) =
    MAcc-Both (fp (maE m∈ stP)) (macc fp) (fq (maE (m∈ , a∉) stQ)) (macc fq)
              (λ r → rq (∖√-ev stQ r)) rq

  MAcc-Both {P} {P′} {Q} {Q′} ap′ ap aq′ aq rq′ rq = macc λ where
    (maτ st)   → MAcc-Both-τ ap′ ap aq′ aq rq′ rq (brBoth-τ-elim A mg P Q P′ Q′ st)
    (maE _ st) → ⊥-elim (brBoth-no-ev A mg P Q P′ Q′ st)

  MAcc-Both-τ ap′ ap aq′ aq rq′ rq (inj₁ refl) = MAcc-Par ap′ aq rq
  MAcc-Both-τ ap′ ap aq′ aq rq′ rq (inj₂ refl) = MAcc-Par ap aq′ rq′

  -- REACHABILITY CLOSURE: walk the √-free run, tracking the operands' residuals
  MAccR-Par : {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂}
            → MAccR H P → RAcc Q → MAccR H (Par A mg P Q)

  -- the run after a τ / visible step of the composite, by cases
  MAccR-Par-τ : {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂} {M W : PTree E (ExtI E) R}
                {s : List Event}
              → MAccR H P → RAcc Q → ParτR A mg P Q M → M ⟹∖√⟨ s ⟩ W → MAcc H W
  MAccR-Par-ev : {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂} {M W : PTree E (ExtI E) R}
                 {s : List Event} {e : Event}
               → MAccR H P → RAcc Q → ParevR A mg P Q M (evl e) → M ⟹∖√⟨ s ⟩ W → MAcc H W
  -- a run out of the overlap node
  MAccR-Both : {P P′ : PTree E (ExtI E) R₁} {Q Q′ : PTree E (ExtI E) R₂} {W : PTree E (ExtI E) R}
               {s : List Event}
             → MAccR H P′ → MAccR H P → RAcc Q′ → RAcc Q
             → Both P Q P′ Q′ ⟹∖√⟨ s ⟩ W → MAcc H W

  MAccR-Par rp rq ∖√-refl = MAcc-Par (rp ∖√-refl) (rq ∖√-refl) rq
  MAccR-Par {P} {Q} rp rq (∖√-τ st r)  = MAccR-Par-τ rp rq (Par-τ-elim A mg P Q st) r
  MAccR-Par {P} {Q} rp rq (∖√-ev st r) = MAccR-Par-ev rp rq (Par-ev-elim A mg P Q st) r

  MAccR-Par-τ rp rq (τL P′ st refl) r = MAccR-Par (λ r′ → rp (∖√-τ st r′)) rq r
  MAccR-Par-τ rp rq (τR Q′ st refl) r = MAccR-Par rp (λ r′ → rq (∖√-τ st r′)) r

  MAccR-Par-ev rp rq (evSync _ stP stQ) r =
    MAccR-Par (λ r′ → rp (∖√-ev stP r′)) (λ r′ → rq (∖√-ev stQ r′)) r
  MAccR-Par-ev rp rq (evL _ stP) r = MAccR-Par (λ r′ → rp (∖√-ev stP r′)) rq r
  MAccR-Par-ev rp rq (evR _ stQ) r = MAccR-Par rp (λ r′ → rq (∖√-ev stQ r′)) r
  MAccR-Par-ev rp rq (evBoth _ stP stQ) r =
    MAccR-Both (λ r′ → rp (∖√-ev stP r′)) rp (λ r′ → rq (∖√-ev stQ r′)) rq r

  MAccR-Both rp′ rp rq′ rq ∖√-refl =
    MAcc-Both (rp′ ∖√-refl) (rp ∖√-refl) (rq′ ∖√-refl) (rq ∖√-refl) rq′ rq
  MAccR-Both {P} {P′} {Q} {Q′} rp′ rp rq′ rq (∖√-τ st r)
    with brBoth-τ-elim A mg P Q P′ Q′ st
  ... | inj₁ refl = MAccR-Par rp′ rq r
  ... | inj₂ refl = MAccR-Par rp rq′ r
  MAccR-Both {P} {P′} {Q} {Q′} rp′ rp rq′ rq (∖√-ev st r) =
    ⊥-elim (brBoth-no-ev A mg P Q P′ Q′ st)

------------------------------------------------------------------------
-- §3. Hiding
------------------------------------------------------------------------

module _ (A B : EventSet) where

  -- root: every modulo-B step of `t ∖ A` is a modulo-(A ∪ B) step of t
  MAcc-∖ : {t : PTree E (ExtI E) R} → MAcc (A ∪H B) t → MAcc B (t ∖ A)

  -- a decoded τ of the hidden process
  MAcc-∖-τ : {t M : PTree E (ExtI E) R} → MAcc (A ∪H B) t → HideτR A t M → MAcc B M
  -- a decoded visible (B-)step of the hidden process
  MAcc-∖-ev : {t M : PTree E (ExtI E) R} {C : Set ℓ} {e : E C} {a : C}
            → MAcc (A ∪H B) t → B .mem (C , e) a
            → HideevR A t M (evl (evLabel C e a)) → MAcc B M

  MAcc-∖ {t = t} at = macc λ where
    (maτ st)    → MAcc-∖-τ at (Hide-τ-elim A t st)
    (maE m∈ st) → MAcc-∖-ev at m∈ (Hide-ev-elim A t st)

  MAcc-∖-τ (macc f) (hτP t′ st refl)    = MAcc-∖ (f (maτ st))
  MAcc-∖-τ (macc f) (hτH t′ m∈ st refl) = MAcc-∖ (f (maE (inj₁ m∈) st))

  MAcc-∖-ev (macc f) m∈ (heV t′ _ st) = MAcc-∖ (f (maE (inj₂ m∈) st))

  -- reachability closure: a √-free run of `P ∖ A` is the image of one of P
  MAccR-∖ : {P : PTree E (ExtI E) R} → MAccR (A ∪H B) P → MAccR B (P ∖ A)
  MAccR-∖ ar ∖√-refl = MAcc-∖ (ar ∖√-refl)
  MAccR-∖ {P = P} ar (∖√-τ st r) with Hide-τ-elim A P st
  ... | hτP P′ τst refl    = MAccR-∖ (λ r′ → ar (∖√-τ τst r′)) r
  ... | hτH P′ m∈ est refl = MAccR-∖ (λ r′ → ar (∖√-ev est r′)) r
  MAccR-∖ {P = P} ar (∖√-ev st r) with Hide-ev-elim A P st
  ... | heV P′ m∉ est = MAccR-∖ (λ r′ → ar (∖√-ev est r′)) r

------------------------------------------------------------------------
-- §4. The CSP instances
------------------------------------------------------------------------

-- removing nothing from H changes nothing
−∅ : (H : EventSet) → (H −H ∅ES) ⊆H H
−∅ H at a m = proj₁ m

-- alphabetised parallel `P ∥⇘ A ⇙ Q`
MAccR-∥ : ∀ {ℓx : Level} {P Q : PTree E (ExtI E) (⊤ {ℓx})} (A H : EventSet)
        → MAccR H P → MAccR (H −H A) Q → MAccR H (P ∥⇘ A ⇙ Q)
MAccR-∥ A H = MAccR-Par A H (λ _ _ → tt)

-- interleaving: symmetric
MAccR-⦀ : ∀ {ℓx : Level} {P Q : PTree E (ExtI E) (⊤ {ℓx})} (H : EventSet)
        → MAccR H P → MAccR H Q → MAccR H (P ⦀ Q)
MAccR-⦀ H rp rq = MAccR-Par ∅ES H (λ _ _ → tt) rp (MAccR-mono (−∅ H) rq)

-- non-empty replicated interleaving over a list
MAccR-⦀⁺ : ∀ {ℓx : Level} (H : EventSet) {P : PTree E (ExtI E) (⊤ {ℓx})} {Qs : List (PTree E (ExtI E) ⊤)}
         → MAccR H P → All (MAccR H) Qs → MAccR H (⦀⁺ P Qs)
MAccR-⦀⁺ H rp []         = rp
MAccR-⦀⁺ H rp (rq ∷ rqs) = MAccR-⦀ H rp (MAccR-⦀⁺ H rq rqs)

-- replicated interleaving over a list, `Skip`-terminated
MAccR-⦀⋆ : ∀ {ℓx : Level} (H : EventSet) {Ps : List (PTree E (ExtI E) (⊤ {ℓx}))}
         → All (MAccR H) Ps → MAccR H (⦀⋆ Ps)
MAccR-⦀⋆ H []         = MAccR-Skip
MAccR-⦀⋆ H (rp ∷ rps) = MAccR-⦀ H rp (MAccR-⦀⋆ H rps)

-- non-empty replicated interleaving over `Fin (suc n)`
MAccR-⦀Fin⁺ : ∀ {ℓx : Level} (H : EventSet) (n : ℕ) {f : Fin (suc n) → PTree E (ExtI E) (⊤ {ℓx})}
            → (∀ i → MAccR H (f i)) → MAccR H (⦀Fin⁺ n f)
MAccR-⦀Fin⁺ H zero    rf = rf fzero
MAccR-⦀Fin⁺ H (suc n) rf = MAccR-⦀ H (rf fzero) (MAccR-⦀Fin⁺ H n (λ i → rf (fsuc i)))

-- replicated interleaving over `Fin n`, `Skip` at zero
MAccR-⦀Fin : ∀ {ℓx : Level} (H : EventSet) (n : ℕ) {f : Fin n → PTree E (ExtI E) (⊤ {ℓx})}
           → (∀ i → MAccR H (f i)) → MAccR H (⦀Fin n f)
MAccR-⦀Fin H zero    rf = MAccR-Skip
MAccR-⦀Fin H (suc n) rf = MAccR-⦀ H (rf fzero) (MAccR-⦀Fin H n (λ i → rf (fsuc i)))
