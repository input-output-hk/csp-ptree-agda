{-# OPTIONS --guardedness #-}

-- Refusals of UNIFORM replication `RepC P k Y = Rep⦀ (λ _ → P) k Y`.
--
--   * `Inert t B` : t contributes no τ and no event of B to an interleaving — it has
--     terminated (`ret`), or it stably refuses B.  NOT `Refuses`: `isStable (ret _) = ⊥`,
--     yet a terminated copy (e.g. `Skip`) is exactly as silent as a refusing one.
--   * `RepC-Refuses-elim` / `RepC-Refuses-intro` : `RepC P k Y` refuses B iff the running
--     copies Y and the pristine fresh copy P are both inert on the visible part `vis B`
--     (`Rep` never offers √, so √ ∈ B costs nothing).
--   * `Inert-⦀-elim` / `Inert-⦀-intro` : inertness splits over `⦀`.
-- Every lemma goes through the characterisation `Inert t B ⟺ no τ × no B-offer`
-- (`inert-no-τ`, `inert-no-offer`, `inert-of`) and the one-step Rep / Par calculi.
-- POSTULATES USED: none.  (`CSP.Laws.FD.ParallelRefusals` is imported for its
-- CONSTRUCTIVE offer lemmas; its `offer-LEM` is in the closure but not used here.)

open import Level using (Level)
open import Data.Nat using (ℕ)
open import Data.Maybe using (just; nothing)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees

module CSP.Laws.FD.ReplicationRefusals {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) {ℓr : Level} where
open PTree

open import CSP.Operators E-≟
open import CSP.Replication E-≟
open import Semantics.LTS {E = E} {I = ExtI E}
open import Semantics.Refusals {E = E} {I = ExtI E} using (Offers; Refuses)
open import Semantics.Stability {E = E} {I = ExtI E} using (stable-no-τ; react-no-τ→stable)
open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Par-τ-L; Par-τ-R)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟ using (viewV-ev; Par-τ-elim; τL; τR)
open import CSP.Laws.Traces.ReplicationSteps E-≟
  using (Rep-ev-elim; evRun; evFresh; evBoth; Rep-τ-elim; τRun; τFresh; Rep-no-√;
         Rep-evRun-intro; Rep-evFresh-intro; Rep-evBoth-intro; Rep-τRun-intro; Rep-τFresh-intro)
open import CSP.Laws.Traces.ReplicationApprox E-≟ using (IsEvl; isEvl)
open import CSP.Laws.FD.ParallelRefusals E-≟
  using (Par-offer-elim; Par-offer-soloL; Par-offer-soloR; ret-no-vis-offer)
open import CSP.Laws.FD.ReplicationDivergence E-≟ {ℓr} using (RepC)

private
  -- the process type of this module
  T : Set _
  T = PTree E (ExtI E) (⊤ {ℓr})

  -- the ⊤-merge of `Rep⦀` / `_⦀_`
  tm : ⊤ {ℓr} → ⊤ {ℓr} → ⊤ {ℓr}
  tm _ _ = tt

-- the visible (non-√) part of a refusal set
vis : ∀ {ℓx} → (Event√ (⊤ {ℓr}) → Set ℓx) → Event√ (⊤ {ℓr}) → Set _
vis B e = B e × IsEvl e

-- t contributes no τ and no event of B to an interleaving: terminated, or stably refusing B
Inert : ∀ {ℓx} → PTree E (ExtI E) (⊤ {ℓr}) → (Event√ (⊤ {ℓr}) → Set ℓx) → Set _
Inert t B = (Σ[ r ∈ ⊤ ] PTree.force t ≡ ret r) ⊎ Refuses t B

-------------------------------------------------------------------------------------
-- Inert ⟺ no τ × no offer
-------------------------------------------------------------------------------------

-- an inert tree makes no τ
inert-no-τ : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} {t t′ : T} → Inert t B → ¬ (t ─[ τ ]─► t′)
inert-no-τ (inj₁ (_ , eq)) (sSil eq′)   = case trans (sym eq) eq′ of λ ()
inert-no-τ (inj₁ (_ , eq)) (sTau eq′ _) = case trans (sym eq) eq′ of λ ()
inert-no-τ (inj₂ (st , _)) s            = stable-no-τ st s

-- an inert tree offers no visible event of B
inert-no-offer : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} {t : T} {e : Event√ (⊤ {ℓr})}
               → Inert t (vis B) → vis B e → ¬ Offers t e
inert-no-offer (inj₁ (_ , eq))  (_ , isEvl _) = ret-no-vis-offer eq
inert-no-offer {e = e} (inj₂ (_ , ref)) Be   = ref e Be

-- no τ and no B-offer make a tree inert (a `react` node is then stable)
inert-of : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} (t : T)
         → (∀ {t′} → ¬ (t ─[ τ ]─► t′)) → (∀ e → B e → ¬ Offers t e) → Inert t B
inert-of {B = B} t noτ noOff = go (PTree.force t) refl
  where
    -- split on the forced node, keeping its equation
    go : (n : NodeKind E (ExtI E) (⊤ {ℓr})) → PTree.force t ≡ n → Inert t B
    go (ret r)      eq = inj₁ (r , eq)
    go (sil t′)     eq = ⊥-elim (noτ (sSil eq))
    go (react v τc) eq = inj₂ (react-no-τ→stable {t = t} eq noτ , noOff)

-------------------------------------------------------------------------------------
-- RepC offers from its copies' offers
-------------------------------------------------------------------------------------

-- a running copy's visible offer is an offer of RepC (alone, or colliding with the fresh copy)
RepC-offer-run : (P : T) (k : ℕ) (Y : T) {e : Event√ (⊤ {ℓr})}
               → IsEvl e → Offers Y e → Offers (RepC P k Y) e
RepC-offer-run P k Y (isEvl (evLabel X f a)) (_ , sY) with viewV (force P) (X , f) a in eq
... | nothing = _ , Rep-evRun-intro tm (λ _ → P) k Y sY eq
... | just _  = _ , Rep-evBoth-intro tm (λ _ → P) k Y sY (viewV-ev {at = X , f} {a = a} refl eq)

-- the fresh copy's visible offer is an offer of RepC (alone, or colliding with a running copy)
RepC-offer-fresh : (P : T) (k : ℕ) (Y : T) {e : Event√ (⊤ {ℓr})}
                 → IsEvl e → Offers P e → Offers (RepC P k Y) e
RepC-offer-fresh P k Y (isEvl (evLabel X f a)) (_ , sP) with viewV (force Y) (X , f) a in eq
... | nothing = _ , Rep-evFresh-intro tm (λ _ → P) k Y sP eq
... | just _  = _ , Rep-evBoth-intro tm (λ _ → P) k Y (viewV-ev {at = X , f} {a = a} refl eq) sP

-------------------------------------------------------------------------------------
-- the refusal characterisation of RepC
-------------------------------------------------------------------------------------

-- a RepC refusal makes the running copies and the pristine fresh copy inert on its visible part
RepC-Refuses-elim : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} (P : T) (k : ℕ) (Y : T)
                  → Refuses (RepC P k Y) B → Inert Y (vis B) × Inert P (vis B)
RepC-Refuses-elim P k Y (st , ref) =
    inert-of Y (λ s → stable-no-τ st (Rep-τRun-intro tm (λ _ → P) k Y s))
               (λ { e (Be , iv) o → ref e Be (RepC-offer-run P k Y iv o) })
  , inert-of P (λ s → stable-no-τ st (Rep-τFresh-intro tm (λ _ → P) k Y s))
               (λ { e (Be , iv) o → ref e Be (RepC-offer-fresh P k Y iv o) })

-- inert running copies and an inert fresh copy make RepC refuse B (√ included: Rep never ticks)
RepC-Refuses-intro : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} (P : T) (k : ℕ) (Y : T)
                   → Inert Y (vis B) → Inert P (vis B) → Refuses (RepC P k Y) B
RepC-Refuses-intro {B = B} P k Y iY iP = react-no-τ→stable {t = RepC P k Y} refl noτ , noOff
  where
    -- a τ of RepC is a running copy's or the fresh copy's
    noτ : ∀ {M} → ¬ (RepC P k Y ─[ τ ]─► M)
    noτ s with Rep-τ-elim tm (λ _ → P) k Y s
    ... | τRun sY   = inert-no-τ iY sY
    ... | τFresh sP = inert-no-τ iP sP
    -- a visible offer of RepC is a running copy's or the fresh copy's
    noOff : ∀ e → B e → ¬ Offers (RepC P k Y) e
    noOff (√ _) _ (_ , s) = Rep-no-√ tm (λ _ → P) k Y s
    noOff (evl x) Be (_ , s) with Rep-ev-elim tm (λ _ → P) k Y s
    ... | evRun sY _   = inert-no-offer iY (Be , isEvl x) (_ , sY)
    ... | evFresh sP _ = inert-no-offer iP (Be , isEvl x) (_ , sP)
    ... | evBoth sY _  = inert-no-offer iY (Be , isEvl x) (_ , sY)

-------------------------------------------------------------------------------------
-- inertness over ⦀
-------------------------------------------------------------------------------------

-- an inert interleaving has inert operands (each operand's τ / offer is the composite's)
Inert-⦀-elim : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} (X Z : T)
             → Inert (X ⦀ Z) (vis B) → Inert X (vis B) × Inert Z (vis B)
Inert-⦀-elim X Z i =
    inert-of X (λ s → inert-no-τ i (Par-τ-L ∅ES tm X Z s))
               (λ { e (Be , isEvl _) o → inert-no-offer i (Be , isEvl _)
                                           (Par-offer-soloL ∅ES tm X Z (λ z → z) o) })
  , inert-of Z (λ s → inert-no-τ i (Par-τ-R ∅ES tm X Z s))
               (λ { e (Be , isEvl _) o → inert-no-offer i (Be , isEvl _)
                                           (Par-offer-soloR ∅ES tm X Z (λ z → z) o) })

-- inert operands make an inert interleaving (a composite τ / offer is an operand's)
Inert-⦀-intro : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} (X Z : T)
              → Inert X (vis B) → Inert Z (vis B) → Inert (X ⦀ Z) (vis B)
Inert-⦀-intro {B = B} X Z iX iZ = inert-of (X ⦀ Z) noτ noOff
  where
    -- a τ of X ⦀ Z is an operand's τ
    noτ : ∀ {M} → ¬ ((X ⦀ Z) ─[ τ ]─► M)
    noτ s with Par-τ-elim ∅ES tm X Z s
    ... | τL _ sX _ = inert-no-τ iX sX
    ... | τR _ sZ _ = inert-no-τ iZ sZ
    -- a visible offer of X ⦀ Z is an operand's (∅ES synchronises nothing)
    noOff : ∀ e → vis B e → ¬ Offers (X ⦀ Z) e
    noOff e (Be , isEvl _) o with Par-offer-elim ∅ES tm X Z o
    ... | inj₁ (() , _)
    ... | inj₂ (_ , inj₁ oX) = inert-no-offer iX (Be , isEvl _) oX
    ... | inj₂ (_ , inj₂ oZ) = inert-no-offer iZ (Be , isEvl _) oZ
