{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- τ-accessibility at every reachable state survives the interrupt `P △ Q`
-- (needed for the breakable medium `cell △ (break ⟶₀ Skip)`).  Only the
-- τ form: the breakable medium is composed with the nodes BEFORE any hide.
-- No `postulate`, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Level using (Level; Lift; lift; _⊔_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Process_Trees

module CSP.Laws.DivFree.ReachInterrupt {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Deadlock {E = E} {I = ExtI E} using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Semantics.DivergenceFree {E = E} {I = ExtI E} using (τ-Acc; acc; τ-AccReach)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟ using (react-τ-inv)
open import CSP.Laws.Traces.TraceLawsThrowInterrupt E-≟
  using (△τR; △τP; △τQ; △τQret; △τ⊓P; △τ⊓Q; △-τ-elim; △evR; △evP; △evQ; △evPQ; △-ev-elim)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- the both-offer overlap node of `P △ Q`: `(P′ △ Q) ⊓ Q′`
Both△ : PTree E (ExtI E) R → PTree E (ExtI E) R → PTree E (ExtI E) R → PTree E (ExtI E) R
Both△ P′ Q Q′ = ptree (react ∅v (△-br2 P′ Q Q′))

-- its τ lands on `P′ △ Q` or on `Q′`
Both△-τ-elim : {P′ Q Q′ M : PTree E (ExtI E) R} → Both△ P′ Q Q′ ─[ τ ]─► M → (M ≡ (P′ △ Q)) ⊎ (M ≡ Q′)
Both△-τ-elim st with react-τ-inv refl st
... | (_ , fin) , lift fzero , eq             = inj₁ (sym (just-injective eq))
... | (_ , fin) , lift (fsuc fzero) , eq      = inj₂ (sym (just-injective eq))
... | (_ , fin) , lift (fsuc (fsuc _)) , ()
... | (_ , base _) , _ , ()
... | (_ , pair _ _) , _ , ()

-- … and it has no visible step
Both△-no-ev : {P′ Q Q′ M : PTree E (ExtI E) R} {e : Event} → Both△ P′ Q Q′ ─[ ev (evl e) ]─► M → ⊥
Both△-no-ev (sVis refl ())

-- root: lexicographic on (τ-Acc P, τ-Acc Q)
τ-Acc-△ : {P Q : PTree E (ExtI E) R} → τ-Acc P → τ-Acc Q → τ-Acc (P △ Q)
-- one decoded τ of the interrupt
τ-Acc-△-step : {P Q M : PTree E (ExtI E) R} → τ-Acc P → τ-Acc Q → △τR P Q M → τ-Acc M

τ-Acc-△ {P = P} {Q = Q} ap aq = acc λ st → τ-Acc-△-step ap aq (△-τ-elim P Q st)

τ-Acc-△-step (acc f) aq (△τP st) = τ-Acc-△ (f st) aq
τ-Acc-△-step ap (acc g) (△τQ st) = τ-Acc-△ ap (g st)
τ-Acc-△-step ap aq (△τQret _)    = aq
τ-Acc-△-step ap aq (△τ⊓P _)      = ap
τ-Acc-△-step ap aq (△τ⊓Q _)      = aq

-- the overlap node: both resolutions are accessible
τ-Acc-Both△ : {P′ Q Q′ : PTree E (ExtI E) R} → τ-Acc P′ → τ-Acc Q → τ-Acc Q′ → τ-Acc (Both△ P′ Q Q′)
-- one resolution
τ-Acc-Both△-pick : {P′ Q Q′ M : PTree E (ExtI E) R} → τ-Acc P′ → τ-Acc Q → τ-Acc Q′
                 → (M ≡ (P′ △ Q)) ⊎ (M ≡ Q′) → τ-Acc M

τ-Acc-Both△ ap′ aq aq′ = acc λ st → τ-Acc-Both△-pick ap′ aq aq′ (Both△-τ-elim st)

τ-Acc-Both△-pick ap′ aq aq′ (inj₁ refl) = τ-Acc-△ ap′ aq
τ-Acc-Both△-pick ap′ aq aq′ (inj₂ refl) = aq′

-- REACHABILITY CLOSURE
τ-AccReach-△ : {P Q : PTree E (ExtI E) R} → τ-AccReach P → τ-AccReach Q → τ-AccReach (P △ Q)
-- the run after one τ / one visible step of the interrupt, and out of the overlap node
τ-AccReach-△-τ : {P Q M W : PTree E (ExtI E) R} {s : List Event}
               → τ-AccReach P → τ-AccReach Q → △τR P Q M → M ⟹∖√⟨ s ⟩ W → τ-Acc W
τ-AccReach-△-ev : {P Q M W : PTree E (ExtI E) R} {s : List Event} {e : Event}
                → τ-AccReach P → τ-AccReach Q → △evR P Q M (evl e) → M ⟹∖√⟨ s ⟩ W → τ-Acc W
τ-AccReach-Both△ : {P′ Q Q′ W : PTree E (ExtI E) R} {s : List Event}
                 → τ-AccReach P′ → τ-AccReach Q → τ-AccReach Q′
                 → Both△ P′ Q Q′ ⟹∖√⟨ s ⟩ W → τ-Acc W

τ-AccReach-△ rp rq ∖√-refl = τ-Acc-△ (rp ∖√-refl) (rq ∖√-refl)
τ-AccReach-△ {P = P} {Q} rp rq (∖√-τ st r)  = τ-AccReach-△-τ rp rq (△-τ-elim P Q st) r
τ-AccReach-△ {P = P} {Q} rp rq (∖√-ev st r) = τ-AccReach-△-ev rp rq (△-ev-elim P Q st) r

τ-AccReach-△-τ rp rq (△τP st)   r = τ-AccReach-△ (λ r′ → rp (∖√-τ st r′)) rq r
τ-AccReach-△-τ rp rq (△τQ st)   r = τ-AccReach-△ rp (λ r′ → rq (∖√-τ st r′)) r
τ-AccReach-△-τ rp rq (△τQret _) r = rq r
τ-AccReach-△-τ rp rq (△τ⊓P _)   r = rp r
τ-AccReach-△-τ rp rq (△τ⊓Q _)   r = rq r

τ-AccReach-△-ev rp rq (△evP st)      r = τ-AccReach-△ (λ r′ → rp (∖√-ev st r′)) rq r
τ-AccReach-△-ev rp rq (△evQ st)      r = rq (∖√-ev st r)
τ-AccReach-△-ev rp rq (△evPQ stP stQ) r =
  τ-AccReach-Both△ (λ r′ → rp (∖√-ev stP r′)) rq (λ r′ → rq (∖√-ev stQ r′)) r

τ-AccReach-Both△ rp′ rq rq′ ∖√-refl = τ-Acc-Both△ (rp′ ∖√-refl) (rq ∖√-refl) (rq′ ∖√-refl)
τ-AccReach-Both△ rp′ rq rq′ (∖√-τ st r) with Both△-τ-elim st
... | inj₁ refl = τ-AccReach-△ rp′ rq r
... | inj₂ refl = rq′ r
τ-AccReach-Both△ rp′ rq rq′ (∖√-ev st r) = ⊥-elim (Both△-no-ev st)
