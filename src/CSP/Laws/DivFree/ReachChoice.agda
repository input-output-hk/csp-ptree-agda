{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Modulo-H accessibility at every reachable state for the choice
-- operators a loop body is built from: internal choice `⊓`, the slide `▷`
-- (which `□` steps into) and external choice `□`.
-- No `postulate`, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Level using (Level)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Laws.DivFree.ReachChoice {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Deadlock {E = E} {I = ExtI E} using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-τ-inv)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟
  using (▷-τ-elim; ▷-ev-elim; ▷-force-ret-inv; □-force-ret-inv; □-τ-elim; □τR; cP; cQ; sPQ; sQP; chP; chQ; □-ev-elim; □evR; evP; evQ; evPQ)
open import CSP.Laws.DivFree.ModAcc E-≟
open import CSP.Laws.DivFree.Loop E-≟ using (noRet; noRet-here; Guarded)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- internal choice offers nothing visible
⊓-no-ev : {P Q M : PTree E (ExtI E) R} {e : Event} → (P ⊓ Q) ─[ ev (evl e) ]─► M → ⊥
⊓-no-ev (sVis refl ())

-- ⊓ root: both τ's land on an operand
MAcc-⊓ : {H : EventSet} {P Q : PTree E (ExtI E) R} → MAcc H P → MAcc H Q → MAcc H (P ⊓ Q)
-- one resolution
MAcc-⊓-pick : {H : EventSet} {P Q M : PTree E (ExtI E) R} → MAcc H P → MAcc H Q → (M ≡ P) ⊎ (M ≡ Q) → MAcc H M

MAcc-⊓ {P = P} {Q} ap aq = macc λ where
  (maτ st)   → MAcc-⊓-pick ap aq (⊓-τ-inv P Q st)
  (maE _ st) → ⊥-elim (⊓-no-ev st)

MAcc-⊓-pick ap aq (inj₁ refl) = ap
MAcc-⊓-pick ap aq (inj₂ refl) = aq

-- ⊓ reachable states
MAccR-⊓ : {H : EventSet} {P Q : PTree E (ExtI E) R} → MAccR H P → MAccR H Q → MAccR H (P ⊓ Q)
MAccR-⊓ rp rq ∖√-refl = MAcc-⊓ (rp ∖√-refl) (rq ∖√-refl)
MAccR-⊓ {P = P} {Q} rp rq (∖√-τ st r) with ⊓-τ-inv P Q st
... | inj₁ refl = rp r
... | inj₂ refl = rq r
MAccR-⊓ rp rq (∖√-ev st r) = ⊥-elim (⊓-no-ev st)

-- ▷ root: lexicographic on P (Q is only ever reached whole)
MAcc-▷ : {H : EventSet} {P Q : PTree E (ExtI E) R} → MAcc H P → MAcc H Q → MAcc H (P ▷ Q)
-- a decoded τ of the slide
MAcc-▷-τ : {H : EventSet} {P Q M : PTree E (ExtI E) R} → MAcc H P → MAcc H Q
         → (M ≡ Q) ⊎ (Σ (PTree E (ExtI E) R) λ P′ → (P ─[ τ ]─► P′) Data.Product.× (M ≡ (P′ ▷ Q)))
         → MAcc H M

MAcc-▷ {P = P} {Q} ap aq = macc λ where
  (maτ st)    → MAcc-▷-τ ap aq (▷-τ-elim P Q st)
  (maE m∈ st) → maccSub ap (maE m∈ (▷-ev-elim P Q st))

MAcc-▷-τ ap       aq (inj₁ refl)              = aq
MAcc-▷-τ (macc f) aq (inj₂ (P′ , st , refl))  = MAcc-▷ (f (maτ st)) aq

-- ▷ reachable states
MAccR-▷ : {H : EventSet} {P Q : PTree E (ExtI E) R} → MAccR H P → MAccR H Q → MAccR H (P ▷ Q)
MAccR-▷ rp rq ∖√-refl = MAcc-▷ (rp ∖√-refl) (rq ∖√-refl)
MAccR-▷ {P = P} {Q} rp rq (∖√-τ st r) with ▷-τ-elim P Q st
... | inj₁ refl             = rq r
... | inj₂ (P′ , pst , refl) = MAccR-▷ (λ r′ → rp (∖√-τ pst r′)) rq r
MAccR-▷ {P = P} {Q} rp rq (∖√-ev st r) = rp (∖√-ev (▷-ev-elim P Q st) r)

module _ ⦃ _ : DecEq R ⦄ where

  -- □ root: lexicographic on (P, Q), six τ shapes and three visible shapes
  MAcc-□ : {H : EventSet} {P Q : PTree E (ExtI E) R} → MAcc H P → MAcc H Q → MAcc H (P □ Q)
  -- a decoded τ / visible H-step of the choice
  MAcc-□-τ : {H : EventSet} {P Q M : PTree E (ExtI E) R} → MAcc H P → MAcc H Q → □τR P Q M → MAcc H M
  MAcc-□-ev : {H : EventSet} {P Q M : PTree E (ExtI E) R} {B : Set ℓ} {e : E B} {a : B}
            → MAcc H P → MAcc H Q → H .mem (B , e) a
            → □evR P Q M (evl (evLabel B e a)) → MAcc H M

  MAcc-□ {P = P} {Q} ap aq = macc λ where
    (maτ st)    → MAcc-□-τ ap aq (□-τ-elim P Q st)
    (maE m∈ st) → MAcc-□-ev ap aq m∈ (□-ev-elim P Q st)

  MAcc-□-τ ap       aq       (cP refl)          = ap
  MAcc-□-τ ap       aq       (cQ refl)          = aq
  MAcc-□-τ (macc f) aq       (sPQ P′ st refl)   = MAcc-▷ (f (maτ st)) aq
  MAcc-□-τ ap       (macc g) (sQP Q′ st refl)   = MAcc-▷ (g (maτ st)) ap
  MAcc-□-τ (macc f) aq       (chP P′ st refl)   = MAcc-□ (f (maτ st)) aq
  MAcc-□-τ ap       (macc g) (chQ Q′ st refl)   = MAcc-□ ap (g (maτ st))

  MAcc-□-ev (macc f) aq       m∈ (evP st)         = f (maE m∈ st)
  MAcc-□-ev ap       (macc g) m∈ (evQ st)         = g (maE m∈ st)
  MAcc-□-ev (macc f) (macc g) m∈ (evPQ stP stQ)   = MAcc-⊓ (f (maE m∈ stP)) (g (maE m∈ stQ))

  -- □ reachable states
  MAccR-□ : {H : EventSet} {P Q : PTree E (ExtI E) R} → MAccR H P → MAccR H Q → MAccR H (P □ Q)
  -- the run after a τ / visible step of the choice
  MAccR-□-τ : {H : EventSet} {P Q M W : PTree E (ExtI E) R} {s : List Event}
            → MAccR H P → MAccR H Q → □τR P Q M → M ⟹∖√⟨ s ⟩ W → MAcc H W
  MAccR-□-ev : {H : EventSet} {P Q M W : PTree E (ExtI E) R} {s : List Event} {e : Event}
             → MAccR H P → MAccR H Q → □evR P Q M (evl e) → M ⟹∖√⟨ s ⟩ W → MAcc H W

  MAccR-□ rp rq ∖√-refl = MAcc-□ (rp ∖√-refl) (rq ∖√-refl)
  MAccR-□ {P = P} {Q} rp rq (∖√-τ st r)  = MAccR-□-τ rp rq (□-τ-elim P Q st) r
  MAccR-□ {P = P} {Q} rp rq (∖√-ev st r) = MAccR-□-ev rp rq (□-ev-elim P Q st) r

  MAccR-□-τ rp rq (cP refl)        r = rp r
  MAccR-□-τ rp rq (cQ refl)        r = rq r
  MAccR-□-τ rp rq (sPQ P′ st refl) r = MAccR-▷ (λ r′ → rp (∖√-τ st r′)) rq r
  MAccR-□-τ rp rq (sQP Q′ st refl) r = MAccR-▷ (λ r′ → rq (∖√-τ st r′)) rp r
  MAccR-□-τ rp rq (chP P′ st refl) r = MAccR-□ (λ r′ → rp (∖√-τ st r′)) rq r
  MAccR-□-τ rp rq (chQ Q′ st refl) r = MAccR-□ rp (λ r′ → rq (∖√-τ st r′)) r

  MAccR-□-ev rp rq (evP st)       r = rp (∖√-ev st r)
  MAccR-□-ev rp rq (evQ st)       r = rq (∖√-ev st r)
  MAccR-□-ev rp rq (evPQ stP stQ) r = MAccR-⊓ (λ r′ → rp (∖√-ev stP r′)) (λ r′ → rq (∖√-ev stQ r′)) r

------------------------------------------------------------------------
-- Guardedness through the choices (a loop body that starts with a choice)
------------------------------------------------------------------------

-- `⊓` is guarded when both operands are (its own node is a react, never a ret)
Guarded-⊓ : {H : EventSet} {P Q : PTree E (ExtI E) R} → Guarded H P → Guarded H Q → Guarded H (P ⊓ Q)
-- one resolution
Guarded-⊓-pick : {H : EventSet} {P Q M : PTree E (ExtI E) R} → Guarded H P → Guarded H Q
               → (M ≡ P) ⊎ (M ≡ Q) → Guarded H M

Guarded-⊓ {P = P} {Q} gp gq = noRet (λ { () }) λ where
  (maτ st)   → Guarded-⊓-pick gp gq (⊓-τ-inv P Q st)
  (maE _ st) → ⊥-elim (⊓-no-ev st)

Guarded-⊓-pick gp gq (inj₁ refl) = gp
Guarded-⊓-pick gp gq (inj₂ refl) = gq

-- `▷` is guarded when both operands are
Guarded-▷ : {H : EventSet} {P Q : PTree E (ExtI E) R} → Guarded H P → Guarded H Q → Guarded H (P ▷ Q)
-- a decoded τ of the slide
Guarded-▷-τ : {H : EventSet} {P Q M : PTree E (ExtI E) R} → Guarded H P → Guarded H Q
            → (M ≡ Q) ⊎ (Σ (PTree E (ExtI E) R) λ P′ → (P ─[ τ ]─► P′) Data.Product.× (M ≡ (P′ ▷ Q)))
            → Guarded H M
-- a decoded visible H-step of the slide (it is P's)
Guarded-▷-ev : {H : EventSet} {P M : PTree E (ExtI E) R} {B : Set ℓ} {e : E B} {a : B}
             → Guarded H P → H .mem (B , e) a → P ─[ ev (evl (evLabel B e a)) ]─► M → Guarded H M

Guarded-▷ {P = P} {Q} gp gq =
  noRet (λ eq → noRet-here gp (▷-force-ret-inv {P = P} {Q = Q} eq)) λ where
    (maτ st)    → Guarded-▷-τ gp gq (▷-τ-elim P Q st)
    (maE m∈ st) → Guarded-▷-ev gp m∈ (▷-ev-elim P Q st)

Guarded-▷-τ gp            gq (inj₁ refl)             = gq
Guarded-▷-τ (noRet _ f)   gq (inj₂ (P′ , st , refl)) = Guarded-▷ (f (maτ st)) gq

Guarded-▷-ev (noRet _ f) m∈ st = f (maE m∈ st)

module _ ⦃ _ : DecEq R ⦄ where

  -- `□` is guarded when both operands are
  Guarded-□ : {H : EventSet} {P Q : PTree E (ExtI E) R} → Guarded H P → Guarded H Q → Guarded H (P □ Q)
  -- a decoded τ / visible H-step of the choice
  Guarded-□-τ : {H : EventSet} {P Q M : PTree E (ExtI E) R} → Guarded H P → Guarded H Q
              → □τR P Q M → Guarded H M
  Guarded-□-ev : {H : EventSet} {P Q M : PTree E (ExtI E) R} {B : Set ℓ} {e : E B} {a : B}
               → Guarded H P → Guarded H Q → H .mem (B , e) a
               → □evR P Q M (evl (evLabel B e a)) → Guarded H M

  Guarded-□ {P = P} {Q} gp gq =
    noRet (λ eq → noRet-here gp (□-force-ret-inv {P = P} {Q = Q} eq)) λ where
      (maτ st)    → Guarded-□-τ gp gq (□-τ-elim P Q st)
      (maE m∈ st) → Guarded-□-ev gp gq m∈ (□-ev-elim P Q st)

  Guarded-□-τ gp          gq          (cP refl)        = gp
  Guarded-□-τ gp          gq          (cQ refl)        = gq
  Guarded-□-τ (noRet _ f) gq          (sPQ P′ st refl) = Guarded-▷ (f (maτ st)) gq
  Guarded-□-τ gp          (noRet _ g) (sQP Q′ st refl) = Guarded-▷ (g (maτ st)) gp
  Guarded-□-τ (noRet _ f) gq          (chP P′ st refl) = Guarded-□ (f (maτ st)) gq
  Guarded-□-τ gp          (noRet _ g) (chQ Q′ st refl) = Guarded-□ gp (g (maτ st))

  Guarded-□-ev (noRet _ f) gq          m∈ (evP st)       = f (maE m∈ st)
  Guarded-□-ev gp          (noRet _ g) m∈ (evQ st)       = g (maE m∈ st)
  Guarded-□-ev (noRet _ f) (noRet _ g) m∈ (evPQ stP stQ) = Guarded-⊓ (f (maE m∈ stP)) (g (maE m∈ stQ))
