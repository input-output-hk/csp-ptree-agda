{-# OPTIONS --guardedness #-}

-- n-ary interleaving nests (generic, FD level): failures and divergences of `Nest Y cs`
-- (CSP/Laws/Traces/InterleaveNest.agda), told component by component.
--   NestRun Y cs s       : one run per component and an `ILv` of their traces into s.
--   Nest-failures-elim   : a √-free failure of a nest is a `NestRun` whose component ends are
--                          all `Inert` on the visible part of the refusal (stability of the
--                          reached state collapses the τ-only `NestEnd` to `⟹-refl`).
--   Nest-failures-intro  : the converse, endpoint-exact: the nest reaches the nest of the ends,
--                          which is `Inert` on the WHOLE refusal set.  `Inert` = `ret ⊎ Refuses`,
--                          so the result is a failure (`inj₂`) or, when every component end
--                          rets, a trace to a `ret` nest end (`inj₁`, no failure: that nest end
--                          can still tick).  `Nest-failures` spells out the two cases.
--   Nest-div-elim        : a divergence of a nest is a `NestRun` of its prefix with SOME
--                          component end divergent (`Any`).  Level by level with
--                          `Par-reach-div`, NOT via `NestEnd` (a pending overlap node may
--                          diverge through the other commit).
--   Nest-div-intro       : the converse, lifting the divergent end through the fold with
--                          `Par-Diverges-L` / `Par-Diverges-R`.
-- POSTULATES USED: `Par-Diverges→` (CSP/Laws/FD/ParallelDivergence.agda), by `Nest-div-elim`
-- through `Par-reach-div` only.  The failure lemmas and `Nest-div-intro` use none.
-- In closure but not used: `offer-LEM` (via CSP.Laws.FD.ReplicationRefusals).

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Binary.Pointwise using () renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Process_Trees

module CSP.Laws.FD.InterleaveNestFD {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) {ℓr : Level} where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.Refusals {E = E} {I = ExtI E} using (Offers; Refuses; deadlock-no-offer)
open import Semantics.Stability {E = E} {I = ExtI E} using (stable-no-τ; stable-not-ret)
open import Semantics.DRBisim {E = E} {I = ExtI E} using (Diverges; deadlock-converges; deadlock-no-τ)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (divergences; IsDivergence)
open import CSP.Laws.Traces.ReplicationApprox E-≟ using (IsEvl; isEvl)
open import CSP.Laws.Traces.InterleaveNest E-≟
  using (Nest; Runs; ILv; ILv-one; ILv-head-evl; ILv-join; Par-reach-elim;
         NestOut; Nest-reach-elim; Nest-reach-intro)
open import CSP.Laws.FD.ParallelDivergence E-≟ using (Par-reach-div; Par-Diverges-L; Par-Diverges-R)
open import CSP.Laws.FD.ReplicationRefusals E-≟ {ℓr} using (vis; Inert; Inert-⦀-elim; Inert-⦀-intro)

private
  -- the process type of this module
  T : Set _
  T = PTree E (ExtI E) (⊤ {ℓr})

  -- its traces
  L : Set _
  L = List (Event√ (⊤ {ℓr}))

  -- the ⊤-merge of `_⦀_`
  tm : ⊤ {ℓr} → ⊤ {ℓr} → ⊤ {ℓr}
  tm _ _ = tt

-------------------------------------------------------------------------------------
-- de-interleaved runs of a nest
-------------------------------------------------------------------------------------

-- one run per component of `Nest Y cs`, and an interleaving of their traces into s
record NestRun (Y : T) (cs : List T) (s : L) : Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓr) where
  field
    sY   : L
    Y′   : T
    runY : Y ⟹⟨ sY ⟩ Y′
    cps  : List (L × T)
    runs : Runs cs cps
    ilv  : ILv (sY ∷ map proj₁ cps) s

  -- the component ends, Y's first
  ends : List T
  ends = Y′ ∷ map proj₂ cps

  -- the nest of the component ends
  nest′ : T
  nest′ = Nest Y′ (map proj₂ cps)
open NestRun

-- forget the end relation of a `NestOut`
nestRun : {Y : T} {cs : List T} {s : L} {W : T} → NestOut Y cs s W → NestRun Y cs s
nestRun o = record { sY = NestOut.sY o ; Y′ = NestOut.Y′ o ; runY = NestOut.runY o
                   ; cps = NestOut.cps o ; runs = NestOut.runs o ; ilv = NestOut.ilv o }

-------------------------------------------------------------------------------------
-- inertness through the fold
-------------------------------------------------------------------------------------

-- a non-`ret` tree offers no √, so inertness on the visible part is inertness outright
Inert-vis→ : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} (t : T) → Inert t (vis B) → Inert t B
Inert-vis→ t (inj₁ r)          = inj₁ r
Inert-vis→ {B = B} t (inj₂ (st , ref)) = inj₂ (st , noOff)
  where
    -- a visible B-offer is a `vis B`-offer; a √-offer would make the stable t a `ret`
    noOff : ∀ e → B e → ¬ Offers t e
    noOff (evl x) Be o             = ref (evl x) (Be , isEvl x) o
    noOff (√ _)   _  (_ , sRet eq) = stable-not-ret {t = t} st eq

-- an inert nest has inert components
Nest-Inert-elim : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} (Y : T) (cs : List T)
                → Inert (Nest Y cs) (vis B) → All (λ c → Inert c (vis B)) (Y ∷ cs)
Nest-Inert-elim Y []       i = i ∷ []
Nest-Inert-elim Y (c ∷ cs) i with Nest-Inert-elim (Y ⦀ c) cs i
... | iYc ∷ is = case Inert-⦀-elim Y c iYc of λ where (iY , ic) → iY ∷ ic ∷ is

-- inert components make an inert nest
Nest-Inert-intro : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} (Y : T) (cs : List T)
                 → All (λ c → Inert c (vis B)) (Y ∷ cs) → Inert (Nest Y cs) (vis B)
Nest-Inert-intro Y []       (i ∷ [])        = i
Nest-Inert-intro Y (c ∷ cs) (iY ∷ ic ∷ is) = Nest-Inert-intro (Y ⦀ c) cs (Inert-⦀-intro Y c iY ic ∷ is)

-------------------------------------------------------------------------------------
-- failures
-------------------------------------------------------------------------------------

-- a τ-only reach out of a τ-free tree is trivial
τ-free-reach : {W X : T} → (∀ {W′} → ¬ (W ─[ τ ]─► W′)) → W ⟹⟨ [] ⟩ X → W ≡ X
τ-free-reach _   ⟹-refl     = refl
τ-free-reach noτ (⟹-τ st _) = ⊥-elim (noτ st)

-- a √-free failure of a nest: component runs whose ends are all inert on the refusal's visible part
Nest-failures-elim : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} (Y : T) (cs : List T) {s : L}
                   → failures (Nest Y cs) s B → All IsEvl s
                   → Σ[ r ∈ NestRun Y cs s ] All (λ c → Inert c (vis B)) (ends r)
Nest-failures-elim {B = B} Y cs (W , run , st , ref) ok =
  let o  = Nest-reach-elim Y cs run ok
      eq = τ-free-reach (stable-no-τ st) (NestOut.end o)
  in nestRun o
   , Nest-Inert-elim (NestOut.Y′ o) (map proj₂ (NestOut.cps o))
       (inj₂ (subst (λ X → Refuses X (vis B)) eq (st , λ e Be → ref e (proj₁ Be))))

-- component runs with inert ends re-interleave into a run of the nest to the (inert) nest of the ends
Nest-failures-intro : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} {Y : T} {cs : List T} {s : L}
                      (r : NestRun Y cs s) → All IsEvl s → All (λ c → Inert c (vis B)) (ends r)
                    → (Nest Y cs ⟹⟨ s ⟩ nest′ r) × Inert (nest′ r) B
Nest-failures-intro r ok is =
    Nest-reach-intro (runY r) (runs r) (ilv r) ok
  , Inert-vis→ (nest′ r) (Nest-Inert-intro (Y′ r) (map proj₂ (cps r)) is)

-- the two cases of the intro: a failure, or (every end `ret`) a trace to a `ret` nest end
Nest-failures : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} {Y : T} {cs : List T} {s : L}
                (r : NestRun Y cs s) → All IsEvl s → All (λ c → Inert c (vis B)) (ends r)
              → failures (Nest Y cs) s B
              ⊎ ((Nest Y cs ⟹⟨ s ⟩ nest′ r) × Σ[ u ∈ ⊤ ] force (nest′ r) ≡ ret u)
Nest-failures r ok is with Nest-failures-intro r ok is
... | run , inj₁ rt  = inj₂ (run , rt)
... | run , inj₂ ref = inj₁ (nest′ r , run , ref)

-------------------------------------------------------------------------------------
-- divergences
-------------------------------------------------------------------------------------

-- a reach ending in a divergent state is √-free (after √ comes the convergent deadlock)
reach-div-evl : {X W : T} {s : L} → X ⟹⟨ s ⟩ W → Diverges W → All IsEvl s
reach-div-evl ⟹-refl                      _ = []
reach-div-evl (⟹-τ _ rest)                d = reach-div-evl rest d
reach-div-evl (⟹-ev {e = evl x} _ rest)   d = isEvl x ∷ reach-div-evl rest d
reach-div-evl (⟹-ev (sRet _) ⟹-refl)      d = ⊥-elim (deadlock-converges d)
reach-div-evl (⟹-ev (sRet _) (⟹-τ st _))  d = ⊥-elim (deadlock-no-τ st)
reach-div-evl (⟹-ev (sRet _) (⟹-ev st _)) d = ⊥-elim (deadlock-no-offer st)

-- a run of a nest to a divergent state: component runs with some divergent end
-- (generalised base; each level decomposes its `Y ⦀ c` end, by `Par-reach-div` when that
-- end is the divergent one, else by `Par-reach-elim`)
Nest-reach-div : (Y : T) (cs : List T) {pre : L} {W : T}
               → Nest Y cs ⟹⟨ pre ⟩ W → Diverges W → All IsEvl pre
               → Σ[ r ∈ NestRun Y cs pre ] Any Diverges (ends r)
Nest-reach-div Y [] {pre} run d ok =
  record { sY = pre ; Y′ = _ ; runY = run ; cps = [] ; runs = []ᵖ ; ilv = ILv-one pre } , here d
Nest-reach-div Y (c ∷ cs) run d ok with Nest-reach-div (Y ⦀ c) cs run d ok
... | r , here dZ = case Par-reach-div ∅ES tm Y c (runY r) dZ of λ where
  (sY″ , sc , Y* , c* , rY , rc , PI , dd) →
      record { sY = sY″ ; Y′ = Y* ; runY = rY ; cps = (sc , c*) ∷ cps r ; runs = rc ∷ᵖ runs r
             ; ilv = ILv-join (ilv r) PI ok }
    , [ here , (λ dc → there (here dc)) ]′ dd
... | r , there a = case Par-reach-elim ∅ES tm Y c (runY r) (ILv-head-evl (ilv r) ok) of λ where
  (sY″ , sc , Y* , c* , rY , rc , PI , _) →
      record { sY = sY″ ; Y′ = Y* ; runY = rY ; cps = (sc , c*) ∷ cps r ; runs = rc ∷ᵖ runs r
             ; ilv = ILv-join (ilv r) PI ok }
    , there (there a)

-- a divergence of a nest: component runs of its prefix with some divergent end
Nest-div-elim : (Y : T) (cs : List T) {s : L} (d : divergences (Nest Y cs) s)
              → Σ[ r ∈ NestRun Y cs (IsDivergence.prefix d) ] Any Diverges (ends r)
Nest-div-elim Y cs d =
  Nest-reach-div Y cs (IsDivergence.reach d) (IsDivergence.divwit d)
    (reach-div-evl (IsDivergence.reach d) (IsDivergence.divwit d))

-- one divergent component makes the nest diverge
Nest-Diverges : (Y : T) (cs : List T) → Any Diverges (Y ∷ cs) → Diverges (Nest Y cs)
Nest-Diverges Y []       (here d)          = d
Nest-Diverges Y []       (there ())
Nest-Diverges Y (c ∷ cs) (here d)          = Nest-Diverges (Y ⦀ c) cs (here (Par-Diverges-L ∅ES tm c d))
Nest-Diverges Y (c ∷ cs) (there (here d))  = Nest-Diverges (Y ⦀ c) cs (here (Par-Diverges-R ∅ES tm Y d))
Nest-Diverges Y (c ∷ cs) (there (there a)) = Nest-Diverges (Y ⦀ c) cs (there a)

-- component runs of a √-free prefix with some divergent end give a divergence of the nest
Nest-div-intro : {Y : T} {cs : List T} {pre : L} {suf : L}
                 (r : NestRun Y cs pre) → All IsEvl pre → Any Diverges (ends r)
               → divergences (Nest Y cs) (pre ++ suf)
Nest-div-intro {pre = pre} {suf = suf} r ok a = record
  { prefix = pre ; suffix = suf ; split = refl ; witness = nest′ r
  ; reach  = Nest-reach-intro (runY r) (runs r) (ilv r) ok
  ; divwit = Nest-Diverges (Y′ r) (map proj₂ (cps r)) a }
