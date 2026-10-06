{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Counting and provenance through the injective renaming `renameMap`
-- (Leios no-livelock, Stage C).  Generic: no Leios/Cardano content.
--   * `RenL`               — the label correspondence of a renamed trace
--   * `ren-trace-elim-rel` — a run of `renameMap P` is the image of a run of
--                            `P` (relational `rename-∖√-elim`, plus the √ case)
--   * `Σc-ren`, `Prov-ren` — weights and provenance carried across `RenL`
--   * `Σc≤-ren`, `PA-ren`  — a whole process's bound / provenance carried across
-- Parameters beyond `ReachRename`'s: `E₁-≟`/`E₂-≟` (to name `Count`/`Prov` on
-- both alphabets) and `ι-rinv` — ι⁻¹ is an EXACT partial inverse.  Without
-- `ι-rinv` the statement is FALSE: with ι c = c′ and ι⁻¹ c′ = ι⁻¹ d′ = just c
-- (ι-linv holds), `renameMap (c → deadlock)` performs d′, which is no ι-image
-- (the counterexample is in the comment above; the machine-checked refutation
-- was not kept in the repo).
-- Each renaming that uses this module must discharge `ι-rinv` (Tasks 4–6).
-- Worked example (34 clauses), for ιKA of `NetworkPar`:
--   ιKA-rinv : ∀ {A} {e₂ : Net_Api Payload A} {e : KAEv A} → ιKA⁻¹ e₂ ≡ just e → e₂ ≡ ιKA e
--   ιKA-rinv {e₂ = input  _ _ N2N_KeepAlive} refl = refl   -- likewise output/done, and apiKA _ _ _
--   ιKA-rinv {e₂ = input  _ _ N2N_ChainSync} ()            -- one absurd clause per other IDs tag
--                                                          -- of input/output/done, and per other
--   ιKA-rinv {e₂ = sndmsg _ _ _} ()                        -- Net_Api constructor (ιKA⁻¹ ends in a
--                                                          -- catch-all, so every case is spelled)
-- No postulate, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _≤_; _+_)
open import Function using (case_of_)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; subst₂)
open import Process_Trees

module CSP.Laws.DivFree.CountRename {ℓ ℓe₁ ℓe₂}
  {E₁ : Set ℓ → Set ℓe₁} {E₂ : Set ℓ → Set ℓe₂}
  (ι      : ∀ {A} → E₁ A → E₂ A)
  (ι⁻¹    : ∀ {A} → E₂ A → Maybe (E₁ A))
  (ι-linv : ∀ {A} (e : E₁ A) → ι⁻¹ (ι e) ≡ just e)
  (ι-rinv : ∀ {A} {e₂ : E₂ A} {e : E₁ A} → ι⁻¹ e₂ ≡ just e → e₂ ≡ ι e)
  (E₁-≟ : (x y : AnyTypes E₁) → Dec (x ≡ y))
  (E₂-≟ : (x y : AnyTypes E₂) → Dec (x ≡ y)) where
open PTree
open import CSP.Rename {E₁ = E₁} {E₂ = E₂} ι ι⁻¹ ι-linv using (renameMap; ι-vis-inv)
open import CSP.Laws.Traces.RenameDeadlock {E₁ = E₁} {E₂ = E₂} ι ι⁻¹ ι-linv using (ren-τ-inv; ren-ev-inv)
import Semantics.LTS {E = E₁} {I = ExtI E₁} as L1
import Semantics.LTS {E = E₂} {I = ExtI E₂} as L2
import Semantics.Failures {E = E₁} {I = ExtI E₁} as D1
import Semantics.Failures {E = E₂} {I = ExtI E₂} as D2
open import CSP.Laws.DivFree.Count E₁-≟ using () renaming (labels to labels₁; Σc to Σc₁)
open import CSP.Laws.DivFree.Count E₂-≟ using () renaming (labels to labels₂; Σc to Σc₂)
import CSP.Laws.DivFree.Prov E₁-≟ as P1
import CSP.Laws.DivFree.Prov E₂-≟ as P2
open import CSP.Laws.Traces.TraceLawsParallelTrace E₂-≟ using (deadlock-no-τ; deadlock-no-ev)

private
  variable
    ℓr : Level
    Rr : Set ℓr

-- the label map of the renaming
renE : L1.Event → L2.Event
renE (L1.evLabel A e a) = L2.evLabel A (ι e) a

-- the label correspondence of a renamed trace
data RenL : List L1.Event → List L2.Event → Set (lsuc ℓ ⊔ ℓe₁ ⊔ ℓe₂) where
  rnil  : RenL [] []
  rcons : ∀ {A} {e : E₁ A} {a s s′} → RenL s s′ → RenL (L1.evLabel A e a ∷ s) (L2.evLabel A (ι e) a ∷ s′)

-- a target label that `ι-vis-inv` pulls back is the ι-image of what it pulls back to
vis-inv-lab : ∀ {B} {e₂ : E₂ B} {b : B} {at : AnyTypes E₁} {a : proj₁ at}
            → ι-vis-inv (B , e₂) b ≡ just (at , a)
            → L2.evLabel B e₂ b ≡ L2.evLabel (proj₁ at) (ι (proj₂ at)) a
vis-inv-lab {B} {e₂} {b} eq with ι⁻¹ e₂ in eqι | eq
... | just e₁ | refl = cong (λ x → L2.evLabel B x b) (ι-rinv eqι)

-- a run of `renameMap P` is the image of a run of `P` (relational `rename-∖√-elim`, plus the √ case)
ren-trace-elim-rel : ∀ {P : PTree E₁ (ExtI E₁) Rr} {W s′} → renameMap P D2.⟹⟨ s′ ⟩ W
                   → Σ[ s ∈ List (L1.Event√ Rr) ] Σ[ P′ ∈ _ ] (P D1.⟹⟨ s ⟩ P′ × RenL (labels₁ s) (labels₂ s′))
ren-trace-elim-rel {P = P} D2.⟹-refl = [] , P , D1.⟹-refl , rnil
ren-trace-elim-rel {P = P} (D2.⟹-τ st rest) with ren-τ-inv {inv = ι-vis-inv} {P = P} st
... | P₁ , Pτ , refl with ren-trace-elim-rel {P = P₁} rest
...   | s , P′ , tr , rl = s , P′ , D1.⟹-τ Pτ tr , rl
ren-trace-elim-rel {P = P} (D2.⟹-ev st rest) with ren-ev-inv {inv = ι-vis-inv} {P = P} st
... | inj₁ ((A , e) , a , bt , b , P₁ , Pev , inv-eq , refl , refl) with ren-trace-elim-rel {P = P₁} rest
...   | s , P′ , tr , rl =
        L1.evl (L1.evLabel A e a) ∷ s , P′ , D1.⟹-ev Pev tr ,
        subst (λ y → RenL (L1.evLabel A e a ∷ labels₁ s) (y ∷ _)) (sym (vis-inv-lab inv-eq)) (rcons rl)
ren-trace-elim-rel {P = P} (D2.⟹-ev st D2.⟹-refl)         | inj₂ (r , refl , fr , refl) =
  L1.√ r ∷ [] , _ , D1.⟹-ev (L1.sRet fr) D1.⟹-refl , rnil
ren-trace-elim-rel {P = P} (D2.⟹-ev st (D2.⟹-τ st′ _))   | inj₂ (r , refl , fr , refl) = ⊥-elim (deadlock-no-τ st′)
ren-trace-elim-rel {P = P} (D2.⟹-ev st (D2.⟹-ev st′ _))  | inj₂ (r , refl , fr , refl) = ⊥-elim (deadlock-no-ev st′)

-- a weight on the target is the pulled-back weight on the source
Σc-ren : (c : L2.Event → ℕ) {ls : List L1.Event} {ls′ : List L2.Event}
       → RenL ls ls′ → Σc₂ c ls′ ≡ Σc₁ (λ e → c (renE e)) ls
Σc-ren c rnil      = refl
Σc-ren c (rcons r) = cong (c _ Data.Nat.+_) (Σc-ren c r)

-- provenance of pulled-back predicates is provenance of the renamed labels
Prov-ren : ∀ {V : Set} {O Kp In : L2.Event → V → Set} {K : V → Set} {ls ls′}
         → RenL ls ls′
         → P1.Prov (λ e → O (renE e)) (λ e → Kp (renE e)) (λ e → In (renE e)) K ls
         → P2.Prov O Kp In K ls′
Prov-ren rnil      _       = tt
Prov-ren (rcons r) (h , q) = h , Prov-ren r q

-- a source weight bound on every run of `P` is the same bound on every run of `renameMap P`
Σc≤-ren : (c d : L2.Event → ℕ) (n : ℕ) {P : PTree E₁ (ExtI E₁) Rr}
        → (∀ {s W} → P D1.⟹⟨ s ⟩ W → Σc₁ (λ e → c (renE e)) (labels₁ s) ≤ Σc₁ (λ e → d (renE e)) (labels₁ s) + n)
        → ∀ {s W} → renameMap P D2.⟹⟨ s ⟩ W → Σc₂ c (labels₂ s) ≤ Σc₂ d (labels₂ s) + n
Σc≤-ren c d n h tr with ren-trace-elim-rel tr
... | _ , _ , tr₁ , rl = subst₂ (λ x y → x ≤ y + n) (sym (Σc-ren c rl)) (sym (Σc-ren d rl)) (h tr₁)

-- provenance of `P` for the pulled-back predicates is provenance of `renameMap P`
PA-ren : ∀ {V : Set} {O Kp In : L2.Event → V → Set} {P : PTree E₁ (ExtI E₁) Rr}
       → P1.PA (λ e → O (renE e)) (λ e → Kp (renE e)) (λ e → In (renE e)) P → P2.PA O Kp In (renameMap P)
PA-ren pp = P2.pa λ tr → case ren-trace-elim-rel tr of λ { (_ , _ , tr₁ , rl) → Prov-ren rl (P1.runA pp tr₁) }
