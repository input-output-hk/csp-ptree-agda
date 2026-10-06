{-# OPTIONS --guardedness #-}

-- The uniform-replication laws at ≈FD, with NO premise on P (unguarded P, P = Skip and
-- colliding copies included):
--   !ᶜ-frame-FD  : RepC P k (Q ⦀ S) ≈FD (Q ⦀ RepC P k S)
--   !ᶜ-absorb-FD : RepC P k (Q ⦀ P) ≈FD RepC P k Q
--   !ᶜ-unfold-FD : !ᶜ P ≈FD (P ⦀ !ᶜ P)
-- Frame and absorb match the component data of CSP.Laws.FD.ReplicationCharFD's records
-- (`RepFailOut` / `RepDivOut`) and split or rebuild the base component with the binary,
-- √-free `Par-reach-elim` / `Par-reach-intro` (`Par-reach-div` for a divergent base); the
-- re-bracketing of the base's binary interleaving inside the n-ary one is `ILv-assocL/R`
-- (frame) and `ILv-join` / `ILv-split` (absorb).  `failures⊥`'s divergence disjunct goes
-- through the `⊇D` halves.
-- The unfold: frame (Q = P, S = Stop), `∼→≈FD (Rep-state-cong-∼ (Par-comm ∅ES P Stop))`, and
-- absorb (Q = Stop), chained by `≈FD-trans` / `≈FD-sym`; `!ᶜ P` is `RepC P 0 Stop`.
-- POSTULATES USED (by reading the called definitions):
--   `Par-Diverges→` (CSP/Laws/FD/ParallelDivergence.agda:55), through `Par-reach-div`,
--      `RepC-div-elim` and `Rep-reach-div` (divergence halves of frame and absorb);
--   `¬-divergent→normal` (Semantics/DRImpliesFD.agda:69), through `∼→≈FD` → `drbisim→≈FD`
--      (the Par-comm step of the unfold only).
--   Both are in E4.  The failure halves use none.
-- In closure but NOT used (`agda --dependency-graph` scan, 7 local modules with a postulate):
--   `offer-LEM` (CSP/Laws/FD/ParallelRefusals.agda:161), `Diverges-LEM`
--   (CSP/Laws/FD/FDTransfer.agda:51), `modA-transfer` (CSP/Laws/Bisim/DRCongruence.agda:278),
--   `□-Diverges→` / `▷-Diverges→` (CSP/Laws/FD/ExtChoiceDivergence.agda:29),
--   `△-Diverges→` (CSP/Laws/FD/InterruptDivergence.agda:26).

open import Level using (Level)
open import Data.Nat using (ℕ; _+_)
open import Data.List using (List; []; _∷_; _++_; map; length; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁻ʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using () renaming (map⁻ to Any-map⁻)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.FD.ReplicationUnfold {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) {ℓr : Level} where
open PTree

open import CSP.Operators E-≟
open import CSP.Replication E-≟ using (!ᶜ)
open import Semantics.LTS {E = E} {I = ExtI E}
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.Refusals {E = E} {I = ExtI E} using (Refuses)
open import Semantics.Stability {E = E} {I = ExtI E} using (stable-not-ret)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (IsDivergence; divergences; _⊇F⊥_; _⊑FD_; _≈FD_; ≈FD-sym; ≈FD-trans)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟ using (Par-force-ret-inv)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟ using (ParInter; pnil; psoloL; Par-trace-elim)
open import CSP.Laws.Traces.ReplicationApprox E-≟ using (IsEvl; isEvl; ⟹-++)
open import CSP.Laws.Traces.InterleaveNest E-≟
  using (ILv; ilv-nil; ILv-one; ILv-one⁻¹; ILv-head-evl; ILv-join; ILv-split; ILv-assocL; ILv-assocR;
         Par-reach-elim; Par-reach-intro)
open import CSP.Laws.FD.ParallelDivergence E-≟ using (Par-reach-div; Par-Diverges-L; Par-Diverges-R)
open import CSP.Laws.FD.ParallelComm E-≟ using (Par-comm)
open import CSP.Laws.FD.ParallelExchange E-≟ using (∼→≈FD)
open import CSP.Laws.Bisim.ReplicationFrame E-≟ using (Rep-state-cong-∼)
open import CSP.Laws.FD.ReplicationDivergence E-≟ {ℓr} using (RepC)
open import CSP.Laws.FD.ReplicationRefusals E-≟ {ℓr} using (vis; Inert; inert-no-τ; Inert-⦀-elim; Inert-⦀-intro)
open import CSP.Laws.FD.ReplicationApproxFD E-≟ {ℓr} using (Rep-no-√-trace; Rep-reach-div)
open import CSP.Laws.FD.InterleaveNestFD E-≟ {ℓr}
  using (NestRun; Inert-vis→; τ-free-reach; reach-div-evl; Nest-reach-div)
open import CSP.Laws.FD.ReplicationIntro E-≟ {ℓr} using (Rep-reach-intro; Rep-end-div)
open import CSP.Laws.FD.ReplicationCharFD E-≟ {ℓr}
  using (RepRun; RepFailOut; RepDivOut; RepC-traces-elim; RepC-failures-elim; RepC-failures-intro;
         RepC-div-elim; RepC-div-intro; runs-rep; toNest; PI-evl; PI-evlR)

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

  -- a τ of the fresh copy P
  Pτ : T → Set _
  Pτ P = Σ[ P′ ∈ T ] (P ─[ τ ]─► P′)

-------------------------------------------------------------------------------------
-- binary `⦀` at inert ends, and RepC ends
-------------------------------------------------------------------------------------

-- a √-free run of X ⦀ Z to an inert end: component runs to inert ends
⦀-inert-elim : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} (X Z : T) {s : L} {V : T}
             → (X ⦀ Z) ⟹⟨ s ⟩ V → All IsEvl s → Inert V (vis B)
             → Σ[ sX ∈ L ] Σ[ sZ ∈ L ] Σ[ X′ ∈ T ] Σ[ Z′ ∈ T ]
                 (X ⟹⟨ sX ⟩ X′) × (Z ⟹⟨ sZ ⟩ Z′) × ParInter ∅ES tm sX sZ s
                 × Inert X′ (vis B) × Inert Z′ (vis B)
⦀-inert-elim X Z run ok iV with Par-reach-elim ∅ES tm X Z run ok
... | sX , sZ , X′ , Z′ , rX , rZ , PI , end with τ-free-reach (λ st → inert-no-τ iV st) end
...   | refl = case Inert-⦀-elim X′ Z′ iV of λ where
  (iX , iZ) → sX , sZ , X′ , Z′ , rX , rZ , PI , iX , iZ

-- a run of X to an inert end and a failure of Z interleave into a failure of X ⦀ Z
⦀-fail-intro : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} (X Z : T) {X′ : T} {sX sZ s : L}
             → X ⟹⟨ sX ⟩ X′ → Inert X′ (vis B) → failures Z sZ B → ParInter ∅ES tm sX sZ s → All IsEvl s
             → failures (X ⦀ Z) s B
⦀-fail-intro {B = B} X Z {X′} rX iX (Z′ , rZ , st , ref) PI ok =
  X′ ⦀ Z′ , Par-reach-intro ∅ES tm X Z rX rZ PI ok , refs
  where
    -- the end is inert on B, and not `ret` because its right operand is stable
    refs : Refuses (X′ ⦀ Z′) B
    refs with Inert-vis→ (X′ ⦀ Z′) (Inert-⦀-intro X′ Z′ iX (inj₂ (st , λ e Be → ref e (proj₁ Be))))
    ... | inj₂ r        = r
    ... | inj₁ (_ , eq) = case Par-force-ret-inv ∅ES tm {P = X′} {Q = Z′} eq of λ where
      (_ , _ , _ , eqZ , _) → ⊥-elim (stable-not-ret {t = Z′} st eqZ)

-- a trace of X ⦀ RepC P k Y never ticks (its right operand never does)
⦀rep-evl : (P : T) (k : ℕ) (Y : T) {X W : T} {s : L} → (X ⦀ RepC P k Y) ⟹⟨ s ⟩ W → All IsEvl s
⦀rep-evl P k Y {X} run with Par-trace-elim ∅ES tm X (RepC P k Y) run
... | _ , _ , _ , _ , _ , rR , PI = PI-evl PI (Rep-no-√-trace P k Y rR)

-- an end reached by RepC is never `ret`: it would tick, and a Rep trace never ticks
rep-end-not-ret : (P : T) (k : ℕ) (Y : T) {u : L} {W : T} {r : ⊤ {ℓr}}
                → RepC P k Y ⟹⟨ u ⟩ W → force W ≡ ret r → ⊥
rep-end-not-ret P k Y {u} run eq with ++⁻ʳ u (Rep-no-√-trace P k Y (⟹-++ run (⟹-ev (sRet eq) ⟹-refl)))
... | () ∷ _

-- an end reached by RepC that is inert on the visible part refuses outright
rep-end-refuses : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} (P : T) (k : ℕ) (Y : T) {u : L} {W : T}
                → RepC P k Y ⟹⟨ u ⟩ W → Inert W (vis B) → Refuses W B
rep-end-refuses P k Y {W = W} run iW with Inert-vis→ W iW
... | inj₁ (_ , eq) = ⊥-elim (rep-end-not-ret P k Y run eq)
... | inj₂ ref      = ref

-- a √-free trace interleaves with the empty trace into itself
PI-left : {s : L} → All IsEvl s → ParInter ∅ES tm s [] s
PI-left []             = pnil
PI-left (isEvl _ ∷ ok) = psoloL (λ z → z) (PI-left ok)

-- a √-free run of X ⦀ Z whose end diverges, or some D: component runs, and X′ or Z′ diverges, or D
⦀-div-split : ∀ {ℓd} {D : Set ℓd} (X Z : T) {s : L} {V : T} → (X ⦀ Z) ⟹⟨ s ⟩ V → All IsEvl s
            → Diverges V ⊎ D
            → Σ[ sX ∈ L ] Σ[ sZ ∈ L ] Σ[ X′ ∈ T ] Σ[ Z′ ∈ T ]
                (X ⟹⟨ sX ⟩ X′) × (Z ⟹⟨ sZ ⟩ Z′) × ParInter ∅ES tm sX sZ s × (Diverges X′ ⊎ Diverges Z′ ⊎ D)
⦀-div-split X Z run ok (inj₁ dV) with Par-reach-div ∅ES tm X Z run dV
... | sX , sZ , X′ , Z′ , rX , rZ , PI , inj₁ dX = sX , sZ , X′ , Z′ , rX , rZ , PI , inj₁ dX
... | sX , sZ , X′ , Z′ , rX , rZ , PI , inj₂ dZ = sX , sZ , X′ , Z′ , rX , rZ , PI , inj₂ (inj₁ dZ)
⦀-div-split X Z run ok (inj₂ d) with Par-reach-elim ∅ES tm X Z run ok
... | sX , sZ , X′ , Z′ , rX , rZ , PI , _ = sX , sZ , X′ , Z′ , rX , rZ , PI , inj₂ (inj₂ d)

-- a nest run of n copies of P over a √-free trace, as a `RepRun`
nest→run : {P Y : T} {u : L} (n : ℕ) → NestRun Y (replicate n P) u → All IsEvl u → RepRun P Y u
nest→run n nr ok = record
  { sY = NestRun.sY nr ; Y′ = NestRun.Y′ nr ; runY = NestRun.runY nr ; cps = NestRun.cps nr
  ; runs = runs-rep n (NestRun.runs nr) ; ilv = NestRun.ilv nr ; noTick = ok }

-- a run of RepC P k Y to a divergent state, AT its own trace: P has a τ, or component runs
-- with Y′ or some copy end divergent
RepC-reach-div : (P : T) (k : ℕ) (Y : T) {u : L} {W : T} → RepC P k Y ⟹⟨ u ⟩ W → Diverges W
               → Pτ P ⊎ Σ[ o ∈ RepRun P Y u ]
                          (Diverges (RepRun.Y′ o) ⊎ Any (λ c → Diverges (proj₂ c)) (RepRun.cps o))
RepC-reach-div P k Y run dW with Rep-reach-div P k Y run dW
... | n , Z , r , inj₂ pτ = inj₁ pτ
... | n , Z , r , inj₁ dZ with Nest-reach-div Y (replicate n P) (toNest k n r) dZ (Rep-no-√-trace P k Y run)
...   | nr , here dY = inj₂ (nest→run n nr (Rep-no-√-trace P k Y run) , inj₁ dY)
...   | nr , there a = inj₂ (nest→run n nr (Rep-no-√-trace P k Y run) , inj₂ (Any-map⁻ a))

-- a τ of P makes RepC P k Y diverge at once, hence at every trace
Pτ-div : (P : T) (k : ℕ) (Y : T) {s : L} → Pτ P → divergences (RepC P k Y) s
Pτ-div P k Y {s} pτ = RepC-div-intro P k Y (record
  { pre = [] ; suf = s ; split = refl ; sY = [] ; Y′ = Y ; runY = ⟹-refl ; cps = [] ; runs = []
  ; ilv = ilv-nil (refl ∷ []) ; noTick = [] ; dv = inj₂ (inj₂ pτ) })

-- a failure map and a divergence map give an FD refinement
⊑FD-of : {X Z : T} → (∀ {s} {B : Event√ (⊤ {ℓr}) → Set ℓr} → failures Z s B → failures X s B)
       → (∀ {s} → divergences Z s → divergences X s) → X ⊑FD Z
⊑FD-of f d = (λ { (inj₁ x) → inj₁ (f x) ; (inj₂ x) → inj₂ (d x) }) , d

-------------------------------------------------------------------------------------
-- the frame  RepC P k (Q ⦀ S) ≈FD (Q ⦀ RepC P k S)
-------------------------------------------------------------------------------------

module _ (P Q S : T) (k : ℕ) where

  -- left failure to right: split the base Q ⦀ S, and Q's part leaves the n-ary interleaving
  fr-f→ : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} {s : L}
        → failures (RepC P k (Q ⦀ S)) s B → failures (Q ⦀ RepC P k S) s B
  fr-f→ f =
    let o  = RepC-failures-elim P k (Q ⦀ S) f
        ok = RepFailOut.noTick o
    in case ⦀-inert-elim Q S (RepFailOut.runY o) (ILv-head-evl (RepFailOut.ilv o) ok) (RepFailOut.inY o) of λ where
      (sQ , sS , Q′ , S′ , rQ , rS , PI , iQ , iS) → case ILv-assocL PI (RepFailOut.ilv o) ok of λ where
        (u , PI′ , w) → ⦀-fail-intro Q (RepC P k S) rQ iQ
          (RepC-failures-intro P k S (record
            { sY = sS ; Y′ = S′ ; runY = rS ; cps = RepFailOut.cps o ; runs = RepFailOut.runs o
            ; ilv = w ; noTick = PI-evlR PI′ ok ; inY = iS ; ins = RepFailOut.ins o ; inP = RepFailOut.inP o }))
          PI′ ok

  -- right failure to left: Q's part joins the base
  fr-f← : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} {s : L}
        → failures (Q ⦀ RepC P k S) s B → failures (RepC P k (Q ⦀ S)) s B
  fr-f← (W , run , st , ref) =
    let ok = ⦀rep-evl P k S run in
    case ⦀-inert-elim Q (RepC P k S) run ok (inj₂ (st , λ e Be → ref e (proj₁ Be))) of λ where
      (sQ , u , Q′ , W′ , rQ , rR , PI′ , iQ , iW) →
        let o = RepC-failures-elim P k S (W′ , rR , rep-end-refuses P k S rR iW) in
        case ILv-assocR PI′ (RepFailOut.ilv o) ok of λ where
          (t , PI , w) → RepC-failures-intro P k (Q ⦀ S) (record
            { sY = t ; Y′ = Q′ ⦀ RepFailOut.Y′ o
            ; runY = Par-reach-intro ∅ES tm Q S rQ (RepFailOut.runY o) PI (ILv-head-evl w ok)
            ; cps = RepFailOut.cps o ; runs = RepFailOut.runs o ; ilv = w ; noTick = ok
            ; inY = Inert-⦀-intro Q′ (RepFailOut.Y′ o) iQ (RepFailOut.inY o)
            ; ins = RepFailOut.ins o ; inP = RepFailOut.inP o })

  -- left divergence to right: split the base (divergent or not), rebuild RepC P k S on S's part
  fr-d→ : {s : L} → divergences (RepC P k (Q ⦀ S)) s → divergences (Q ⦀ RepC P k S) s
  fr-d→ d =
    let o  = RepC-div-elim P k (Q ⦀ S) d
        ok = RepDivOut.noTick o
    in case ⦀-div-split Q S (RepDivOut.runY o) (ILv-head-evl (RepDivOut.ilv o) ok) (RepDivOut.dv o) of λ where
      (sQ , sS , Q* , S* , rQ , rS , PI , dv) → case ILv-assocL PI (RepDivOut.ilv o) ok of λ where
        (u , PI′ , w) → case Rep-reach-intro P k rS (RepDivOut.cps o) (RepDivOut.runs o) w (PI-evlR PI′ ok) of λ where
          (ends , r , p) → subst (divergences (Q ⦀ RepC P k S)) (sym (RepDivOut.split o)) (record
            { prefix = RepDivOut.pre o ; suffix = RepDivOut.suf o ; split = refl ; witness = _
            ; reach  = Par-reach-intro ∅ES tm Q (RepC P k S) rQ r PI′ ok
            ; divwit = [ Par-Diverges-L ∅ES tm _
                       , (λ x → Par-Diverges-R ∅ES tm Q*
                                  (Rep-end-div P (k + length ends) (RepDivOut.cps o) (RepDivOut.runs o) ends p x)) ]′ dv })

  -- a Q-run and a RepRun of S interleaved into a √-free pre, with Q*, S′ or a copy end
  -- divergent, give a divergence of the left side
  fr-div← : {sQ u pre suf : L} {Q* : T} → Q ⟹⟨ sQ ⟩ Q* → ParInter ∅ES tm sQ u pre → All IsEvl pre
          → (o : RepRun P S u)
          → Diverges Q* ⊎ Diverges (RepRun.Y′ o) ⊎ Any (λ c → Diverges (proj₂ c)) (RepRun.cps o)
          → divergences (RepC P k (Q ⦀ S)) (pre ++ suf)
  fr-div← {pre = pre} {suf} {Q*} rQ PI′ ok o dv with ILv-assocR PI′ (RepRun.ilv o) ok
  ... | t , PI , w = RepC-div-intro P k (Q ⦀ S) (record
    { pre = pre ; suf = suf ; split = refl ; sY = t ; Y′ = Q* ⦀ RepRun.Y′ o
    ; runY = Par-reach-intro ∅ES tm Q S rQ (RepRun.runY o) PI (ILv-head-evl w ok)
    ; cps = RepRun.cps o ; runs = RepRun.runs o ; ilv = w ; noTick = ok
    ; dv = [ (λ dQ → inj₁ (Par-Diverges-L ∅ES tm _ dQ))
           , [ (λ dS → inj₁ (Par-Diverges-R ∅ES tm Q* dS)) , (λ a → inj₂ (inj₁ a)) ]′ ]′ dv })

  -- right divergence to left: split Q ⦀ RepC P k S, then Q's divergence, RepC's at its own
  -- trace, or (P τ-able) the left side's immediate divergence
  fr-d← : {s : L} → divergences (Q ⦀ RepC P k S) s → divergences (RepC P k (Q ⦀ S)) s
  fr-d← d =
    let sp = IsDivergence.split d
        ok = reach-div-evl (IsDivergence.reach d) (IsDivergence.divwit d)
    in case Par-reach-div ∅ES tm Q (RepC P k S) (IsDivergence.reach d) (IsDivergence.divwit d) of λ where
      (sQ , u , Q* , R* , rQ , rR , PI′ , inj₁ dQ) →
        subst (divergences (RepC P k (Q ⦀ S))) (sym sp)
          (fr-div← rQ PI′ ok (RepC-traces-elim P k S (R* , rR)) (inj₁ dQ))
      (sQ , u , Q* , R* , rQ , rR , PI′ , inj₂ dR) → case RepC-reach-div P k S rR dR of λ where
        (inj₁ pτ)       → Pτ-div P k (Q ⦀ S) pτ
        (inj₂ (o , dv)) → subst (divergences (RepC P k (Q ⦀ S))) (sym sp) (fr-div← rQ PI′ ok o (inj₂ dv))

-- the frame law of uniform replication at ≈FD, no premise
!ᶜ-frame-FD : (P Q S : T) (k : ℕ) → RepC P k (Q ⦀ S) ≈FD (Q ⦀ RepC P k S)
!ᶜ-frame-FD P Q S k = ⊑FD-of (fr-f← P Q S k) (fr-d← P Q S k) , ⊑FD-of (fr-f→ P Q S k) (fr-d→ P Q S k)

-------------------------------------------------------------------------------------
-- absorption  RepC P k (Q ⦀ P) ≈FD RepC P k Q
-------------------------------------------------------------------------------------

module _ (P Q : T) (k : ℕ) where

  -- left failure to right: the pre-placed copy's run joins the copies
  ab-f→ : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} {s : L}
        → failures (RepC P k (Q ⦀ P)) s B → failures (RepC P k Q) s B
  ab-f→ f =
    let o  = RepC-failures-elim P k (Q ⦀ P) f
        ok = RepFailOut.noTick o
    in case ⦀-inert-elim Q P (RepFailOut.runY o) (ILv-head-evl (RepFailOut.ilv o) ok) (RepFailOut.inY o) of λ where
      (sQ , sP , Q′ , P′ , rQ , rP , PI , iQ , iP) → RepC-failures-intro P k Q (record
        { sY = sQ ; Y′ = Q′ ; runY = rQ ; cps = (sP , P′) ∷ RepFailOut.cps o ; runs = rP ∷ RepFailOut.runs o
        ; ilv = ILv-join (RepFailOut.ilv o) PI ok ; noTick = ok ; inY = iQ
        ; ins = iP ∷ RepFailOut.ins o ; inP = RepFailOut.inP o })

  -- component data of a right failure give a left one: the first copy moves into the base, or
  -- (no copy) the pre-placed P stays unmoved, inert by the fresh supply's inertness
  ab-fail : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} {sQ s : L} {Q′ : T} → Q ⟹⟨ sQ ⟩ Q′
          → (cps : List (L × T)) → All (λ c → P ⟹⟨ proj₁ c ⟩ proj₂ c) cps
          → ILv (sQ ∷ map proj₁ cps) s → All IsEvl s
          → Inert Q′ (vis B) → All (λ c → Inert (proj₂ c) (vis B)) cps → Inert P (vis B)
          → failures (RepC P k (Q ⦀ P)) s B
  ab-fail {Q′ = Q′} rQ [] [] w ok iQ [] iP with ILv-one⁻¹ w
  ... | refl = RepC-failures-intro P k (Q ⦀ P) (record
    { sY = _ ; Y′ = Q′ ⦀ P ; runY = Par-reach-intro ∅ES tm Q P rQ ⟹-refl (PI-left ok) ok
    ; cps = [] ; runs = [] ; ilv = ILv-one _ ; noTick = ok ; inY = Inert-⦀-intro Q′ P iQ iP ; ins = [] ; inP = iP })
  ab-fail {Q′ = Q′} rQ ((_ , P₁) ∷ cps) (r₁ ∷ rs) w ok iQ (i₁ ∷ is) iP with ILv-split w ok
  ... | t , PI , w′ = RepC-failures-intro P k (Q ⦀ P) (record
    { sY = t ; Y′ = Q′ ⦀ P₁ ; runY = Par-reach-intro ∅ES tm Q P rQ r₁ PI (ILv-head-evl w′ ok)
    ; cps = cps ; runs = rs ; ilv = w′ ; noTick = ok ; inY = Inert-⦀-intro Q′ P₁ iQ i₁ ; ins = is ; inP = iP })

  -- right failure to left
  ab-f← : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} {s : L}
        → failures (RepC P k Q) s B → failures (RepC P k (Q ⦀ P)) s B
  ab-f← f = let o = RepC-failures-elim P k Q f in
    ab-fail (RepFailOut.runY o) (RepFailOut.cps o) (RepFailOut.runs o) (RepFailOut.ilv o) (RepFailOut.noTick o)
      (RepFailOut.inY o) (RepFailOut.ins o) (RepFailOut.inP o)

  -- left divergence to right: the pre-placed copy's run joins the copies
  ab-d→ : {s : L} → divergences (RepC P k (Q ⦀ P)) s → divergences (RepC P k Q) s
  ab-d→ d =
    let o  = RepC-div-elim P k (Q ⦀ P) d
        ok = RepDivOut.noTick o
    in case ⦀-div-split Q P (RepDivOut.runY o) (ILv-head-evl (RepDivOut.ilv o) ok) (RepDivOut.dv o) of λ where
      (sQ , sP , Q* , P* , rQ , rP , PI , dv) → RepC-div-intro P k Q (record
        { pre = RepDivOut.pre o ; suf = RepDivOut.suf o ; split = RepDivOut.split o
        ; sY = sQ ; Y′ = Q* ; runY = rQ ; cps = (sP , P*) ∷ RepDivOut.cps o ; runs = rP ∷ RepDivOut.runs o
        ; ilv = ILv-join (RepDivOut.ilv o) PI ok ; noTick = ok
        ; dv = [ inj₁ , [ (λ dP → inj₂ (inj₁ (here dP)))
                        , [ (λ a → inj₂ (inj₁ (there a))) , (λ x → inj₂ (inj₂ x)) ]′ ]′ ]′ dv })

  -- component data of a right divergence give a left one (as `ab-fail`)
  ab-div : {s pre suf sQ : L} {Q′ : T} → s ≡ pre ++ suf → Q ⟹⟨ sQ ⟩ Q′
         → (cps : List (L × T)) → All (λ c → P ⟹⟨ proj₁ c ⟩ proj₂ c) cps
         → ILv (sQ ∷ map proj₁ cps) pre → All IsEvl pre
         → Diverges Q′ ⊎ Any (λ c → Diverges (proj₂ c)) cps ⊎ Pτ P
         → divergences (RepC P k (Q ⦀ P)) s
  ab-div {Q′ = Q′} sp rQ [] [] w ok dv with ILv-one⁻¹ w
  ... | refl = RepC-div-intro P k (Q ⦀ P) (record
    { pre = _ ; suf = _ ; split = sp ; sY = _ ; Y′ = Q′ ⦀ P
    ; runY = Par-reach-intro ∅ES tm Q P rQ ⟹-refl (PI-left ok) ok
    ; cps = [] ; runs = [] ; ilv = ILv-one _ ; noTick = ok
    ; dv = [ (λ dQ → inj₁ (Par-Diverges-L ∅ES tm P dQ)) , [ (λ ()) , (λ x → inj₂ (inj₂ x)) ]′ ]′ dv })
  ab-div {Q′ = Q′} sp rQ ((_ , P₁) ∷ cps) (r₁ ∷ rs) w ok dv with ILv-split w ok
  ... | t , PI , w′ = RepC-div-intro P k (Q ⦀ P) (record
    { pre = _ ; suf = _ ; split = sp ; sY = t ; Y′ = Q′ ⦀ P₁
    ; runY = Par-reach-intro ∅ES tm Q P rQ r₁ PI (ILv-head-evl w′ ok)
    ; cps = cps ; runs = rs ; ilv = w′ ; noTick = ok
    ; dv = case dv of λ where
        (inj₁ dQ)                → inj₁ (Par-Diverges-L ∅ES tm P₁ dQ)
        (inj₂ (inj₁ (here d₁)))  → inj₁ (Par-Diverges-R ∅ES tm Q′ d₁)
        (inj₂ (inj₁ (there a)))  → inj₂ (inj₁ a)
        (inj₂ (inj₂ x))          → inj₂ (inj₂ x) })

  -- right divergence to left
  ab-d← : {s : L} → divergences (RepC P k Q) s → divergences (RepC P k (Q ⦀ P)) s
  ab-d← d = let o = RepC-div-elim P k Q d in
    ab-div (RepDivOut.split o) (RepDivOut.runY o) (RepDivOut.cps o) (RepDivOut.runs o) (RepDivOut.ilv o)
      (RepDivOut.noTick o) (RepDivOut.dv o)

-- the absorption law of uniform replication at ≈FD, no premise
!ᶜ-absorb-FD : (P Q : T) (k : ℕ) → RepC P k (Q ⦀ P) ≈FD RepC P k Q
!ᶜ-absorb-FD P Q k = ⊑FD-of (ab-f← P Q k) (ab-d← P Q k) , ⊑FD-of (ab-f→ P Q k) (ab-d→ P Q k)

-------------------------------------------------------------------------------------
-- the unfold  !ᶜ P ≈FD (P ⦀ !ᶜ P)
-------------------------------------------------------------------------------------

-- the unfold law of uniform replication at ≈FD, no premise:
--   !ᶜ P = RepC P 0 Stop ≈ RepC P 0 (Stop ⦀ P) ≈ RepC P 0 (P ⦀ Stop) ≈ P ⦀ RepC P 0 Stop
!ᶜ-unfold-FD : (P : T) → !ᶜ P ≈FD (P ⦀ !ᶜ P)
!ᶜ-unfold-FD P =
  ≈FD-trans (≈FD-sym (!ᶜ-absorb-FD P Stop 0))
    (≈FD-trans (≈FD-sym (∼→≈FD (Rep-state-cong-∼ {P = λ _ → P} {k = 0} (Par-comm ∅ES P Stop))))
      (!ᶜ-frame-FD P P Stop 0))
