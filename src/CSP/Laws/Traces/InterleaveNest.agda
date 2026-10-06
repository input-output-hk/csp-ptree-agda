{-# OPTIONS --guardedness #-}

-- n-ary interleaving nests (generic, trace level): the missing n-ary counterpart of the
-- binary `ParInter` machinery.
--   Nest Y cs         : Y, then each component of cs interleaved on the right (left-nested `_⦀_`).
--   ILv tss s         : s is an interleaving of the component traces tss, one constructor per
--                       merged event.  A step names its component by a `Pick` path, NOT by the
--                       `Fin (length tss)` / `updateAt` index first planned: that index is not a
--                       constructor pattern, so no consumer could split an `ILv (t ∷ ts) s`
--                       (MEASURED: Agda 2.8 `SplitError.UnificationStuck` on
--                       `replicate n [] ≟ t ∷ u ∷ ts`).
--   Nest-reach-elim   : a √-free run of a nest splits into one run per component, an `ILv`, and
--                       the τ-resolution of the reached state to the nest of the ends.
--   Nest-reach-intro  : the converse, endpoint-exact.
-- Both iterate endpoint-exact, √-free binary versions (`Par-reach-elim` / `Par-reach-intro`,
-- below) through the fold.  `Par-trace-reach` (CSP/Laws/FD/ParallelAssocFail.agda) is not used:
-- its √ disjunct cannot be refuted from its output, and `Par-trace-elim-eq`
-- (TraceLawsParallelTrace.agda) records only "not ret" for a pending overlap node.
-- The only replication-specific item is the bridge `Approx-Nest`.  No postulates.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
  renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.Maybe using (nothing)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Process_Trees

module CSP.Laws.Traces.InterleaveNest {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS {E = E} {I = ExtI E}
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Mg; Par-τ-L; Par-τ-R; Par-sync)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟
  using (Par-τ-elim; τL; τR; Par-ev-elim; evSync; evL; evR; evBoth; ev√)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟
  using (ParInter; pnil; psync; psoloL; psoloR; p√; brBoth-τ-elim; brBoth-no-ev)
open import CSP.Laws.Traces.TraceLawsParallelMono E-≟
  using (brBoth-commitL; Par-soloL-reach; Par-soloR-reach)
open import CSP.Laws.Traces.ReplicationApprox E-≟ using (Approx; IsEvl; isEvl; ⟹-++; ⦀-lift-L)

private
  variable
    ℓr ℓ₁ ℓ₂ ℓs : Level
    R₁ : Set ℓ₁
    R₂ : Set ℓ₂
    R  : Set ℓs

  -- the ⊤-merge of `_⦀_`
  tm : ⊤ {ℓr} → ⊤ {ℓr} → ⊤ {ℓr}
  tm _ _ = tt

-------------------------------------------------------------------------------------
-- binary, endpoint-exact, √-free
-------------------------------------------------------------------------------------

-- a de-interleaved run of `Par P Q` to W: operand runs, their interleaving, and W's τ-only
-- resolution to the composite of the operand ends
ParOut : (A : EventSet) (merge : Mg R₁ R₂ R) → PTree E (ExtI E) R₁ → PTree E (ExtI E) R₂
       → List (Event√ R) → PTree E (ExtI E) R → Set _
ParOut {R₁ = R₁} {R₂ = R₂} A merge P Q s W =
  Σ[ sP ∈ List (Event√ R₁) ] Σ[ sQ ∈ List (Event√ R₂) ]
  Σ[ P′ ∈ PTree E (ExtI E) R₁ ] Σ[ Q′ ∈ PTree E (ExtI E) R₂ ]
    (P ⟹⟨ sP ⟩ P′) × (Q ⟹⟨ sQ ⟩ Q′) × ParInter A merge sP sQ s × (W ⟹⟨ [] ⟩ Par A merge P′ Q′)

-- a √-free run of `Par P Q` de-interleaves; an overlap node left pending by the last event
-- is resolved by its left commit (the witness names the left operand)
Par-reach-elim : (A : EventSet) (merge : Mg R₁ R₂ R)
                 (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                 {s : List (Event√ R)} {W : PTree E (ExtI E) R}
               → (Par A merge P Q) ⟹⟨ s ⟩ W → All IsEvl s → ParOut A merge P Q s W

-- the same from the inline both-offer overlap node reached by the event both operands offered
Par-ov-reach-elim : (A : EventSet) (merge : Mg R₁ R₂ R)
                    (P P′ : PTree E (ExtI E) R₁) (Q Q′ : PTree E (ExtI E) R₂)
                    {X : Set ℓ} {e : E X} {a : X} {s : List (Event√ R)} {W : PTree E (ExtI E) R}
                  → ¬ A .mem (X , e) a
                  → P ─[ ev (evl (evLabel X e a)) ]─► P′
                  → Q ─[ ev (evl (evLabel X e a)) ]─► Q′
                  → (ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P′ Q′))) ⟹⟨ s ⟩ W
                  → All IsEvl s → ParOut A merge P Q (evl (evLabel X e a) ∷ s) W

Par-reach-elim A merge P Q ⟹-refl _ = [] , [] , P , Q , ⟹-refl , ⟹-refl , pnil , ⟹-refl
Par-reach-elim A merge P Q (⟹-τ step rest) ok with Par-τ-elim A merge P Q step
... | τL P″ Pτ refl = case Par-reach-elim A merge P″ Q rest ok of λ where
        (sP , sQ , P′ , Q′ , rP , rQ , PI , res) → sP , sQ , P′ , Q′ , ⟹-τ Pτ rP , rQ , PI , res
... | τR Q″ Qτ refl = case Par-reach-elim A merge P Q″ rest ok of λ where
        (sP , sQ , P′ , Q′ , rP , rQ , PI , res) → sP , sQ , P′ , Q′ , rP , ⟹-τ Qτ rQ , PI , res
Par-reach-elim A merge P Q (⟹-ev step rest) (px ∷ ok) with Par-ev-elim A merge P Q step
... | evSync cs Pev Qev = case Par-reach-elim A merge _ _ rest ok of λ where
        (sP , sQ , P′ , Q′ , rP , rQ , PI , res) →
          _ ∷ sP , _ ∷ sQ , P′ , Q′ , ⟹-ev Pev rP , ⟹-ev Qev rQ , psync cs PI , res
... | evL ¬cs Pev = case Par-reach-elim A merge _ Q rest ok of λ where
        (sP , sQ , P′ , Q′ , rP , rQ , PI , res) →
          _ ∷ sP , sQ , P′ , Q′ , ⟹-ev Pev rP , rQ , psoloL ¬cs PI , res
... | evR ¬cs Qev = case Par-reach-elim A merge P _ rest ok of λ where
        (sP , sQ , P′ , Q′ , rP , rQ , PI , res) →
          sP , _ ∷ sQ , P′ , Q′ , rP , ⟹-ev Qev rQ , psoloR ¬cs PI , res
... | evBoth ¬cs Pev Qev = Par-ov-reach-elim A merge P _ Q _ ¬cs Pev Qev rest ok
... | ev√ _ _ = case px of λ ()

Par-ov-reach-elim A merge P P′ Q Q′ ¬cs Pev Qev ⟹-refl _ =
  _ ∷ [] , [] , P′ , Q , ⟹-ev Pev ⟹-refl , ⟹-refl , psoloL ¬cs pnil ,
  ⟹-τ (brBoth-commitL A merge P Q P′ Q′) ⟹-refl
Par-ov-reach-elim A merge P P′ Q Q′ ¬cs Pev Qev (⟹-τ step rest) ok
  with brBoth-τ-elim A merge P Q P′ Q′ step
... | inj₁ refl = case Par-reach-elim A merge P′ Q rest ok of λ where
        (sP , sQ , P* , Q* , rP , rQ , PI , res) →
          _ ∷ sP , sQ , P* , Q* , ⟹-ev Pev rP , rQ , psoloL ¬cs PI , res
... | inj₂ refl = case Par-reach-elim A merge P Q′ rest ok of λ where
        (sP , sQ , P* , Q* , rP , rQ , PI , res) →
          sP , _ ∷ sQ , P* , Q* , rP , ⟹-ev Qev rQ , psoloR ¬cs PI , res
Par-ov-reach-elim A merge P P′ Q Q′ ¬cs Pev Qev (⟹-ev step _) _ =
  ⊥-elim (brBoth-no-ev A merge P Q P′ Q′ step)

-- the converse: √-free operand runs re-interleave into a run of `Par P Q` to `Par P′ Q′`
-- (a both-offer detours through the overlap node and commits towards the named operand)
Par-reach-intro : (A : EventSet) (merge : Mg R₁ R₂ R)
                  (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                  {P′ : PTree E (ExtI E) R₁} {Q′ : PTree E (ExtI E) R₂}
                  {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R)}
                → P ⟹⟨ sP ⟩ P′ → Q ⟹⟨ sQ ⟩ Q′ → ParInter A merge sP sQ s → All IsEvl s
                → (Par A merge P Q) ⟹⟨ s ⟩ (Par A merge P′ Q′)
Par-reach-intro A merge P Q (⟹-τ st rP) rQ PI ok =
  ⟹-τ (Par-τ-L A merge P Q st) (Par-reach-intro A merge _ Q rP rQ PI ok)
Par-reach-intro A merge P Q rP (⟹-τ st rQ) PI ok =
  ⟹-τ (Par-τ-R A merge P Q st) (Par-reach-intro A merge P _ rP rQ PI ok)
Par-reach-intro A merge P Q ⟹-refl ⟹-refl pnil _ = ⟹-refl
Par-reach-intro A merge P Q (⟹-ev st rP) (⟹-ev st′ rQ) (psync cs PI) (_ ∷ ok) =
  ⟹-ev (Par-sync A merge P Q cs st st′) (Par-reach-intro A merge _ _ rP rQ PI ok)
Par-reach-intro A merge P Q (⟹-ev st rP) rQ (psoloL ¬cs PI) (_ ∷ ok) =
  Par-soloL-reach A merge P Q ¬cs st (Par-reach-intro A merge _ Q rP rQ PI ok)
Par-reach-intro A merge P Q rP (⟹-ev st rQ) (psoloR ¬cs PI) (_ ∷ ok) =
  Par-soloR-reach A merge P Q ¬cs st (Par-reach-intro A merge P _ rP rQ PI ok)
Par-reach-intro A merge P Q _ _ p√ (() ∷ _)

-------------------------------------------------------------------------------------
-- the n-ary interleaving witness
-------------------------------------------------------------------------------------

-- `Pick e tss tss′`: tss′ is tss with the event e consed onto exactly one component
data Pick {ℓr} (e : Event√ (⊤ {ℓr}))
     : List (List (Event√ (⊤ {ℓr}))) → List (List (Event√ (⊤ {ℓr}))) → Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓr) where
  -- e goes to the first component
  here  : ∀ {t ts} → Pick e (t ∷ ts) ((e ∷ t) ∷ ts)
  -- e goes to a later component
  there : ∀ {t ts ts′} → Pick e ts ts′ → Pick e (t ∷ ts) (t ∷ ts′)

-- n-ary interleaving of component traces: each step hands the next merged event to one component.
-- Meaningful only for √-free merged traces (a Pick may hand √ to one component, unlike ⦀'s joint
-- termination); every lemma below guards with `All IsEvl`.
data ILv {ℓr} : List (List (Event√ (⊤ {ℓr}))) → List (Event√ (⊤ {ℓr})) → Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓr) where
  -- every component trace empty, merged trace empty
  ilv-nil  : ∀ {tss} → All (_≡ []) tss → ILv tss []
  -- the next merged event belongs to the component the `Pick` names
  ilv-step : ∀ {tss tss′ s e} → Pick e tss tss′ → ILv tss s → ILv tss′ (e ∷ s)

-- a lone component's trace interleaves to itself
ILv-one : (s : List (Event√ (⊤ {ℓr}))) → ILv (s ∷ []) s
ILv-one []      = ilv-nil (refl ∷ [])
ILv-one (e ∷ s) = ilv-step here (ILv-one s)

-- conversely, a lone component's interleaving is its trace
ILv-one⁻¹ : {t s : List (Event√ (⊤ {ℓr}))} → ILv (t ∷ []) s → t ≡ s
ILv-one⁻¹ (ilv-nil (refl ∷ []))   = refl
ILv-one⁻¹ (ilv-step here w)       = cong (_ ∷_) (ILv-one⁻¹ w)
ILv-one⁻¹ (ilv-step (there ()) w)

-- the first component's trace is √-free when the merged trace is
ILv-head-evl : {t s : List (Event√ (⊤ {ℓr}))} {ts : List (List (Event√ (⊤ {ℓr})))}
             → ILv (t ∷ ts) s → All IsEvl s → All IsEvl t
ILv-head-evl (ilv-nil (refl ∷ _))   _        = []
ILv-head-evl (ilv-step here w)      (p ∷ ok) = p ∷ ILv-head-evl w ok
ILv-head-evl (ilv-step (there _) w) (_ ∷ ok) = ILv-head-evl w ok

-- a binary interleaving inside the first component splits it into two leading components
ILv-join : {tY tc t s : List (Event√ (⊤ {ℓr}))} {ts : List (List (Event√ (⊤ {ℓr})))}
         → ILv (t ∷ ts) s → ParInter ∅ES tm tY tc t → All IsEvl s → ILv (tY ∷ tc ∷ ts) s
ILv-join (ilv-nil (refl ∷ z))   pnil           _        = ilv-nil (refl ∷ refl ∷ z)
ILv-join (ilv-step here w)      (psoloL _ PI)  (_ ∷ ok) = ilv-step here (ILv-join w PI ok)
ILv-join (ilv-step here w)      (psoloR _ PI)  (_ ∷ ok) = ilv-step (there here) (ILv-join w PI ok)
ILv-join (ilv-step here w)      (psync () _)   _
ILv-join (ilv-step here w)      p√             (() ∷ _)
ILv-join (ilv-step (there pk) w) PI            (_ ∷ ok) = ilv-step (there (there pk)) (ILv-join w PI ok)

-- conversely, two leading components merge into one by a binary interleaving
ILv-split : {tY tc s : List (Event√ (⊤ {ℓr}))} {ts : List (List (Event√ (⊤ {ℓr})))}
          → ILv (tY ∷ tc ∷ ts) s → All IsEvl s
          → Σ[ t ∈ List (Event√ (⊤ {ℓr})) ] ParInter ∅ES tm tY tc t × ILv (t ∷ ts) s
ILv-split (ilv-nil (refl ∷ refl ∷ z)) _ = [] , pnil , ilv-nil (refl ∷ z)
ILv-split (ilv-step here w) (isEvl _ ∷ ok) = case ILv-split w ok of λ where
  (t , PI , w′) → _ ∷ t , psoloL (λ z → z) PI , ilv-step here w′
ILv-split (ilv-step (there here) w) (isEvl _ ∷ ok) = case ILv-split w ok of λ where
  (t , PI , w′) → _ ∷ t , psoloR (λ z → z) PI , ilv-step here w′
ILv-split (ilv-step (there (there pk)) w) (_ ∷ ok) = case ILv-split w ok of λ where
  (t , PI , w′) → t , PI , ilv-step (there pk) w′

-- the first component against the rest: an `ILv` is a binary interleaving of the head with an
-- interleaving of the tail
ILv-uncons : {t s : List (Event√ (⊤ {ℓr}))} {ts : List (List (Event√ (⊤ {ℓr})))}
           → ILv (t ∷ ts) s → All IsEvl s
           → Σ[ u ∈ List (Event√ (⊤ {ℓr})) ] ParInter ∅ES tm t u s × ILv ts u
ILv-uncons (ilv-nil (refl ∷ z)) _ = [] , pnil , ilv-nil z
ILv-uncons (ilv-step here w) (isEvl _ ∷ ok) = case ILv-uncons w ok of λ where
  (u , PI , w′) → u , psoloL (λ z → z) PI , w′
ILv-uncons (ilv-step (there pk) w) (isEvl _ ∷ ok) = case ILv-uncons w ok of λ where
  (u , PI , w′) → _ ∷ u , psoloR (λ z → z) PI , ilv-step pk w′

-- conversely, the head interleaved with an interleaving of the tail is an `ILv`
ILv-cons : {t u s : List (Event√ (⊤ {ℓr}))} {ts : List (List (Event√ (⊤ {ℓr})))}
         → ParInter ∅ES tm t u s → ILv ts u → All IsEvl s → ILv (t ∷ ts) s
ILv-cons pnil          (ilv-nil z)      _        = ilv-nil (refl ∷ z)
ILv-cons (psoloL _ PI) w                (_ ∷ ok) = ilv-step here (ILv-cons PI w ok)
ILv-cons (psoloR _ PI) (ilv-step pk w)  (_ ∷ ok) = ilv-step (there pk) (ILv-cons PI w ok)
ILv-cons (psync () _)  _                _
ILv-cons p√            _                (() ∷ _)

-- re-bracketing, left to right: (tQ | tS) as the first component becomes tQ against (tS ∷ ts)
ILv-assocL : {tQ tS t s : List (Event√ (⊤ {ℓr}))} {ts : List (List (Event√ (⊤ {ℓr})))}
           → ParInter ∅ES tm tQ tS t → ILv (t ∷ ts) s → All IsEvl s
           → Σ[ u ∈ List (Event√ (⊤ {ℓr})) ] ParInter ∅ES tm tQ u s × ILv (tS ∷ ts) u
ILv-assocL PI w ok = ILv-uncons (ILv-join w PI ok) ok

-- re-bracketing, right to left: tQ against (tS ∷ ts) becomes (tQ | tS) as the first component
ILv-assocR : {tQ tS u s : List (Event√ (⊤ {ℓr}))} {ts : List (List (Event√ (⊤ {ℓr})))}
           → ParInter ∅ES tm tQ u s → ILv (tS ∷ ts) u → All IsEvl s
           → Σ[ t ∈ List (Event√ (⊤ {ℓr})) ] ParInter ∅ES tm tQ tS t × ILv (t ∷ ts) s
ILv-assocR PI w ok = ILv-split (ILv-cons PI w ok) ok

-------------------------------------------------------------------------------------
-- nests
-------------------------------------------------------------------------------------

-- a left-nested interleaving: Y, then each component added on the right (the shape Rep and Approx build)
Nest : PTree E (ExtI E) (⊤ {ℓr}) → List (PTree E (ExtI E) (⊤ {ℓr})) → PTree E (ExtI E) (⊤ {ℓr})
Nest Y []       = Y
Nest Y (c ∷ cs) = Nest (Y ⦀ c) cs

-- the uniform approximant is the nest of its n copies
Approx-Nest : (P : PTree E (ExtI E) (⊤ {ℓr})) (k n : ℕ) (Y : PTree E (ExtI E) (⊤ {ℓr}))
            → Approx (λ _ → P) k n Y ≡ Nest Y (replicate n P)
Approx-Nest P k zero    Y = refl
Approx-Nest P k (suc n) Y = Approx-Nest P (suc k) n (Y ⦀ P)

-- a √-free run of the base lifts through the nest with every component idle
Nest-lift : (cs : List (PTree E (ExtI E) (⊤ {ℓr}))) {Z Z′ : PTree E (ExtI E) (⊤ {ℓr})}
            {s : List (Event√ (⊤ {ℓr}))}
          → All IsEvl s → Z ⟹⟨ s ⟩ Z′ → Nest Z cs ⟹⟨ s ⟩ Nest Z′ cs
Nest-lift []       ok r = r
Nest-lift (c ∷ cs) ok r = Nest-lift cs ok (⦀-lift-L c ok r)

-- one run per component: component c runs along trace `proj₁` to end `proj₂`
Runs : List (PTree E (ExtI E) (⊤ {ℓr})) → List (List (Event√ (⊤ {ℓr})) × PTree E (ExtI E) (⊤ {ℓr}))
     → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
Runs = Pointwise (λ c tc → c ⟹⟨ proj₁ tc ⟩ proj₂ tc)

-- how a reached state W stands to the nest of the component ends: `⟹-refl` when W IS that
-- nest; otherwise W holds both-offer overlap nodes left pending by the last event (possibly
-- one per level), each resolved LEFT (`Par-ov-reach-elim`, :115-117), whose τ-commits resolve
-- W to the nest, the witness then naming the left operand
NestEnd : PTree E (ExtI E) (⊤ {ℓr}) → PTree E (ExtI E) (⊤ {ℓr}) → List (PTree E (ExtI E) (⊤ {ℓr}))
        → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
NestEnd W Y′ cs′ = W ⟹⟨ [] ⟩ Nest Y′ cs′

-- a √-free run of `Nest Y cs` to W, told component by component
record NestOut (Y : PTree E (ExtI E) (⊤ {ℓr})) (cs : List (PTree E (ExtI E) (⊤ {ℓr})))
               (s : List (Event√ (⊤ {ℓr}))) (W : PTree E (ExtI E) (⊤ {ℓr}))
     : Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓr) where
  field
    sY   : List (Event√ (⊤ {ℓr}))
    Y′   : PTree E (ExtI E) (⊤ {ℓr})
    runY : Y ⟹⟨ sY ⟩ Y′
    cps  : List (List (Event√ (⊤ {ℓr})) × PTree E (ExtI E) (⊤ {ℓr}))
    runs : Runs cs cps
    ilv  : ILv (sY ∷ map proj₁ cps) s
    end  : NestEnd W Y′ (map proj₂ cps)

-- the n-ary `Par-trace-intro`, endpoint-exact: component runs re-interleave per an `ILv` into
-- a run of the nest to the nest of their ends (collisions resolved towards the named component)
Nest-reach-intro : {Y Y′ : PTree E (ExtI E) (⊤ {ℓr})} {cs : List (PTree E (ExtI E) (⊤ {ℓr}))}
                   {sY s : List (Event√ (⊤ {ℓr}))}
                   {cps : List (List (Event√ (⊤ {ℓr})) × PTree E (ExtI E) (⊤ {ℓr}))}
                 → Y ⟹⟨ sY ⟩ Y′ → Runs cs cps → ILv (sY ∷ map proj₁ cps) s → All IsEvl s
                 → Nest Y cs ⟹⟨ s ⟩ Nest Y′ (map proj₂ cps)
Nest-reach-intro rY []ᵖ w ok with ILv-one⁻¹ w
... | refl = rY
Nest-reach-intro {Y = Y} rY (_∷ᵖ_ {x = c} rc runs) w ok = case ILv-split w ok of λ where
  (t , PI , w′) → Nest-reach-intro (Par-reach-intro ∅ES tm Y c rY rc PI (ILv-head-evl w′ ok)) runs w′ ok

-- a √-free run of a nest splits into component runs, an `ILv`, and the end relation
Nest-reach-elim : (Y : PTree E (ExtI E) (⊤ {ℓr})) (cs : List (PTree E (ExtI E) (⊤ {ℓr})))
                  {s : List (Event√ (⊤ {ℓr}))} {W : PTree E (ExtI E) (⊤ {ℓr})}
                → Nest Y cs ⟹⟨ s ⟩ W → All IsEvl s → NestOut Y cs s W
Nest-reach-elim Y [] {s = s} run ok =
  record { sY = s ; Y′ = _ ; runY = run ; cps = [] ; runs = []ᵖ ; ilv = ILv-one s ; end = ⟹-refl }
Nest-reach-elim Y (c ∷ cs) run ok =
  let o = Nest-reach-elim (Y ⦀ c) cs run ok
      open NestOut o using (runY; cps; runs; ilv; end)
  in case Par-reach-elim ∅ES tm Y c runY (ILv-head-evl ilv ok) of λ where
    (sY′ , sc , Y″ , c′ , rY , rc , PI , res) →
      record { sY = sY′ ; Y′ = Y″ ; runY = rY ; cps = (sc , c′) ∷ cps ; runs = rc ∷ᵖ runs
             ; ilv = ILv-join ilv PI ok
             ; end = ⟹-++ end (Nest-lift (map proj₂ cps) [] res) }
