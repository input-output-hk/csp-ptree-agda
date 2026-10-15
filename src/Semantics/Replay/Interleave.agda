{-# OPTIONS --safe #-}

-- Independent heterogeneous machines: tagged events update one component.
-- Fold this binary product to replay finite families of mini-protocols.
module Semantics.Replay.Interleave where

open import Level using (Level; _⊔_)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-map⁺; ∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum.Properties as Sum
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (Dec; yes; no)
open import Function.Bundles using (_⇔_; mk⇔)
open import Semantics.Replay

-- Components may have different state, event and relation universes.
module Product {s₁ s₂ e₁ e₂ r₁ r₂ : Level}
               {S₁ : Set s₁} {S₂ : Set s₂} {E₁ : Set e₁} {E₂ : Set e₂}
               (L : Replay r₁ S₁ E₁) (R : Replay r₂ S₂ E₂) where
  private
    module L = Replay L
    module R = Replay R
    module LT = Traces L
    module RT = Traces R

  -- Visible events advance only their tagged component.
  data Step : S₁ × S₂ → E₁ ⊎ E₂ → S₁ × S₂ → Set (s₁ ⊔ s₂ ⊔ e₁ ⊔ e₂ ⊔ r₁ ⊔ r₂) where
    left : ∀ {a a′ b e} → L._-[_]→_ a e a′ → Step (a , b) (inj₁ e) (a′ , b)
    right : ∀ {a b b′ e} → R._-[_]→_ b e b′ → Step (a , b) (inj₂ e) (a , b′)

  -- Silent events advance one component without synchronisation.
  data Tau : S₁ × S₂ → S₁ × S₂ → Set (s₁ ⊔ s₂ ⊔ e₁ ⊔ e₂ ⊔ r₁ ⊔ r₂) where
    leftτ : ∀ {a a′ b} → L._-τ→_ a a′ → Tau (a , b) (a′ , b)
    rightτ : ∀ {a b b′} → R._-τ→_ b b′ → Tau (a , b) (a , b′)

  -- Enumerate visible successors of the selected component.
  caseAfter : S₁ × S₂ → E₁ ⊎ E₂ → List (S₁ × S₂)
  caseAfter (a , b) (inj₁ e) = map (_, b) (L.after a e)
  caseAfter (a , b) (inj₂ e) = map (a ,_) (R.after b e)
  -- Listed visible successors are actual steps, with the listed target.
  afterSound : ∀ {s e t} → t ∈ caseAfter s e → Step s e t
  afterSound {a , b} {inj₁ e} m with ∈-map⁻ (_, b) m
  ... | a′ , am , refl = left (L.after-sound am)
  afterSound {a , b} {inj₂ e} m with ∈-map⁻ (a ,_) m
  ... | b′ , bm , refl = right (R.after-sound bm)

  -- Enumerate all silent successors from either component.
  caseTaus : S₁ × S₂ → List (S₁ × S₂)
  caseTaus (a , b) = map (_, b) (L.taus a) ++ map (a ,_) (R.taus b)

  -- Recover the silent step and target from successor membership.
  tauSound : ∀ {s t} → t ∈ caseTaus s → Tau s t
  tauSound {a , b} m with ∈-++⁻ (map (_, b) (L.taus a)) m
  ... | inj₁ lm with ∈-map⁻ (_, b) lm
  ...   | a′ , am , refl = leftτ (L.taus-sound am)
  tauSound {a , b} m | inj₂ rm with ∈-map⁻ (a ,_) rm
  ... | b′ , bm , refl = rightτ (R.taus-sound bm)

  -- Finite successor enumeration gives a generic replay instance.
  interleave : Replay (s₁ ⊔ s₂ ⊔ e₁ ⊔ e₂ ⊔ r₁ ⊔ r₂) (S₁ × S₂) (E₁ ⊎ E₂)
  interleave = record
    { _-[_]→_ = Step
    ; _-τ→_ = Tau
    ; _≟E_ = Sum.≡-dec L._≟E_ R._≟E_
    ; after = caseAfter
    ; taus = caseTaus
    ; after-sound = afterSound
    ; taus-sound = tauSound
    ; after-complete = λ { (left p) → ∈-map⁺ (_, _) (L.after-complete p)
                         ; (right p) → ∈-map⁺ (_ ,_) (R.after-complete p) }
    ; taus-complete = λ { (leftτ p) → ∈-++⁺ˡ (∈-map⁺ (_, _) (L.taus-complete p))
                        ; (rightτ p) → ∈-++⁺ʳ _ (∈-map⁺ (_ ,_) (R.taus-complete p)) }
    }

  open Traces interleave public

  -- Left projection preserves its component's visible event order.
  projectL : List (E₁ ⊎ E₂) → List E₁
  projectL [] = []
  projectL (inj₁ e ∷ es) = e ∷ projectL es
  projectL (inj₂ e ∷ es) = projectL es

  -- Right projection preserves its component's visible event order.
  projectR : List (E₁ ⊎ E₂) → List E₂
  projectR [] = []
  projectR (inj₁ e ∷ es) = projectR es
  projectR (inj₂ e ∷ es) = e ∷ projectR es

  -- Project a global run and its endpoint onto the left machine.
  runL : ∀ {s t es} → s ⇒⟨ es ⟩ t → LT._⇒⟨_⟩_ (proj₁ s) (projectL es) (proj₁ t)
  runL done = LT.done
  runL (tau (leftτ p) q) = LT.tau p (runL q)
  runL (tau (rightτ p) q) = runL q
  runL (vis (left p) q) = LT.vis p (runL q)
  runL (vis (right p) q) = runL q

  -- Project a global run onto the right machine.
  runR : ∀ {s t es} → s ⇒⟨ es ⟩ t → RT._⇒⟨_⟩_ (proj₂ s) (projectR es) (proj₂ t)
  runR done = RT.done
  runR (tau (leftτ p) q) = runR q
  runR (tau (rightτ p) q) = RT.tau p (runR q)
  runR (vis (left p) q) = runR q
  runR (vis (right p) q) = RT.vis p (runR q)

  -- Weave local runs in global order; trailing silent steps are optional.
  weave : ∀ {a b a′ b′} (es : List (E₁ ⊎ E₂)) →
          LT._⇒⟨_⟩_ a (projectL es) a′ → RT._⇒⟨_⟩_ b (projectR es) b′ → HasTrace (a , b) es
  weave {a} {b} [] p q = (a , b) , done
  weave (inj₁ e ∷ es) (LT.tau st p) q with weave (inj₁ e ∷ es) p q
  ... | t , r = t , tau (leftτ st) r
  weave (inj₁ e ∷ es) (LT.vis st p) q with weave es p q
  ... | t , r = t , vis (left st) r
  weave (inj₂ e ∷ es) p (RT.tau st q) with weave (inj₂ e ∷ es) p q
  ... | t , r = t , tau (rightτ st) r
  weave (inj₂ e ∷ es) p (RT.vis st q) with weave es p q
  ... | t , r = t , vis (right st) r

  -- Global membership implies both projection memberships.
  split : ∀ {a b es} → HasTrace (a , b) es → LT.HasTrace a (projectL es) × RT.HasTrace b (projectR es)
  split (t , p) = (proj₁ t , runL p) , (proj₂ t , runR p)

  -- Projection witnesses yield a genuine global run.
  join : ∀ {a b es} → LT.HasTrace a (projectL es) × RT.HasTrace b (projectR es) → HasTrace (a , b) es
  join {es = es} ((_ , p) , (_ , q)) = weave es p q

  -- Independent global traces are exactly the traces of both projections.
  projection-equivalence : ∀ {a b es} → HasTrace (a , b) es ⇔
                           (LT.HasTrace a (projectL es) × RT.HasTrace b (projectR es))
  projection-equivalence = mk⇔ split join

  -- Decide membership without enumerating independent silent-step permutations.
  decide : ∀ {a b} → ((es : List E₁) → Dec (LT.HasTrace a es)) →
           ((es : List E₂) → Dec (RT.HasTrace b es)) →
           (es : List (E₁ ⊎ E₂)) → Dec (HasTrace (a , b) es)
  decide dl dr es with dl (projectL es) | dr (projectR es)
  ... | yes p | yes q = yes (join (p , q))
  ... | no np | _ = no λ h → np (proj₁ (split h))
  ... | _ | no nq = no λ h → nq (proj₂ (split h))
