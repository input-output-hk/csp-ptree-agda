{-# OPTIONS --guardedness #-}

-- The component-wise characterisation of UNIFORM replication `RepC P k Y = Rep⦀ (λ _ → P) k Y`:
-- its traces, failures and divergences, told as one run of the running copies Y, one run of P
-- per listed copy (possibly unmoved; the intros filter with `moved`), and an `ILv` of their traces.
--   RepRun     / RepC-traces-elim   / RepC-traces-intro   : traces.
--   RepFailOut / RepC-failures-elim / RepC-failures-intro : failures; every end is `Inert` on the
--                refusal's visible part, and so is the pristine fresh copy P (Review Focus 3).
--   RepDivOut  / RepC-div-elim      / RepC-div-intro      : divergences, stated over the divergence
--                PREFIX (the model is extension-closed): Y′, some copy end, or P's τ diverges.
--   !ᶜ-unfold-T : the trace-level unfold `traces (!ᶜ P) s ⇔ traces (P ⦀ !ᶜ P) s`, no premise.
-- Every record carries `noTick : All IsEvl _`: a Rep trace never ticks (`Rep-no-√-trace`), and the
-- intros (`Rep-fail-intro` / `Rep-div-intro`) need it.
-- Elims: `Rep-*-approx` (a finite approximant), `Approx-Nest`, then the nest elims.
-- Intros: `Rep-reach-intro` / `Rep-fail-intro` / `Rep-div-intro` (CSP.Laws.FD.ReplicationIntro).
-- POSTULATES USED: `Par-Diverges→` only, by `RepC-div-elim` (through `Rep-reach-div` and
-- `Nest-reach-div`).  The trace and failure lemmas, `RepC-div-intro` and `!ᶜ-unfold-T` use none.
-- In closure but not used: `offer-LEM`.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_; map; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using () renaming (map⁻ to All-map⁻)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using () renaming (map⁻ to Any-map⁻)
open import Data.List.Relation.Binary.Pointwise using () renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (_⇔_; mk⇔; case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.FD.ReplicationCharFD {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) {ℓr : Level} where

open import CSP.Operators E-≟
open import CSP.Replication E-≟ using (!ᶜ)
open import Semantics.LTS {E = E} {I = ExtI E}
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (IsDivergence; divergences)
open import Semantics.Stability {E = E} {I = ExtI E} using (stable-no-τ)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟
  using (ParInter; pnil; psync; psoloL; psoloR; p√; Par-trace-elim)
open import CSP.Laws.Traces.TraceLawsParallelMono E-≟ using (Par-trace-intro)
open import CSP.Laws.Traces.ReplicationApprox E-≟ using (Approx; IsEvl; isEvl)
open import CSP.Laws.Traces.InterleaveNest E-≟
  using (Nest; Runs; ILv; ilv-nil; ilv-step; ILv-one⁻¹; ILv-uncons; ILv-cons; Approx-Nest;
         NestOut; Nest-reach-elim)
  renaming (here to p-here; there to p-there)
open import CSP.Laws.FD.ReplicationDivergence E-≟ {ℓr} using (RepC)
open import CSP.Laws.FD.ReplicationRefusals E-≟ {ℓr} using (vis; Inert; inert-no-τ)
open import CSP.Laws.FD.ReplicationApproxFD E-≟ {ℓr}
  using (Rep-reach-approx; Rep-no-√-trace; Rep-fail-approx; Rep-reach-div)
open import CSP.Laws.FD.InterleaveNestFD E-≟ {ℓr}
  using (NestRun; nestRun; Nest-Inert-elim; τ-free-reach; Nest-reach-div)
open import CSP.Laws.FD.ReplicationIntro E-≟ {ℓr} using (Rep-reach-intro; Rep-fail-intro; Rep-div-intro)

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
-- the records
-------------------------------------------------------------------------------------

-- a trace of uniform replication, told component by component: Y's run, the listed copies'
-- runs (possibly unmoved), and an interleaving of their traces (which never tick)
record RepRun (P Y : T) (s : L) : Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓr) where
  field
    sY   : L
    Y′   : T
    runY : Y ⟹⟨ sY ⟩ Y′
    cps  : List (L × T)
    runs : All (λ c → P ⟹⟨ proj₁ c ⟩ proj₂ c) cps
    ilv  : ILv (sY ∷ map proj₁ cps) s
    noTick : All IsEvl s

-- a failure of uniform replication, told component by component: Y's run, the moved copies' runs,
-- an interleaving of their traces, every end inert, and the fresh supply inert
record RepFailOut {ℓx} (P Y : T) (s : L) (B : Event√ (⊤ {ℓr}) → Set ℓx)
     : Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓr ⊔ ℓx) where
  field
    sY   : L
    Y′   : T
    runY : Y ⟹⟨ sY ⟩ Y′
    cps  : List (L × T)
    runs : All (λ c → P ⟹⟨ proj₁ c ⟩ proj₂ c) cps
    ilv  : ILv (sY ∷ map proj₁ cps) s
    noTick : All IsEvl s
    inY  : Inert Y′ (vis B)
    ins  : All (λ c → Inert (proj₂ c) (vis B)) cps
    inP  : Inert P (vis B)

-- a divergence of uniform replication, told over its prefix: component runs to the prefix's
-- ends, an interleaving of the prefix, and Y′, some copy end, or P's τ divergent
record RepDivOut (P Y : T) (s : L) : Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓr) where
  field
    pre   : L
    suf   : L
    split : s ≡ pre ++ suf
    sY    : L
    Y′    : T
    runY  : Y ⟹⟨ sY ⟩ Y′
    cps   : List (L × T)
    runs  : All (λ c → P ⟹⟨ proj₁ c ⟩ proj₂ c) cps
    ilv   : ILv (sY ∷ map proj₁ cps) pre
    noTick : All IsEvl pre
    dv    : Diverges Y′ ⊎ Any (λ c → Diverges (proj₂ c)) cps ⊎ Σ[ P′ ∈ T ] (P ─[ τ ]─► P′)

-------------------------------------------------------------------------------------
-- from approximant nests to the records
-------------------------------------------------------------------------------------

-- runs of the components `replicate n P` are runs of P
runs-rep : {P : T} (n : ℕ) {cps : List (L × T)} → Runs (replicate n P) cps
         → All (λ c → P ⟹⟨ proj₁ c ⟩ proj₂ c) cps
runs-rep zero    []ᵖ         = []
runs-rep (suc n) (r ∷ᵖ rs) = r ∷ runs-rep n rs

-- a run of the approximant with n copies, as a run of the nest of n copies of P
toNest : {P Y Z : T} (k n : ℕ) {s : L} → Approx (λ _ → P) k n Y ⟹⟨ s ⟩ Z → Nest Y (replicate n P) ⟹⟨ s ⟩ Z
toNest {P} {Y} {Z} k n {s} = subst (λ X → X ⟹⟨ s ⟩ Z) (Approx-Nest P k n Y)

-- a nest run of n copies of P over the prefix of s, with a divergent part, as a `RepDivOut`
mkDiv : {P Y : T} {s pre suf : L} (n : ℕ) → s ≡ pre ++ suf
      → (r : NestRun Y (replicate n P) pre) → All IsEvl pre
      → Diverges (NestRun.Y′ r) ⊎ Any (λ c → Diverges (proj₂ c)) (NestRun.cps r) ⊎ Σ[ P′ ∈ T ] (P ─[ τ ]─► P′)
      → RepDivOut P Y s
mkDiv n sp r ok dv = record
  { pre = _ ; suf = _ ; split = sp ; sY = NestRun.sY r ; Y′ = NestRun.Y′ r ; runY = NestRun.runY r
  ; cps = NestRun.cps r ; runs = runs-rep n (NestRun.runs r) ; ilv = NestRun.ilv r ; noTick = ok ; dv = dv }

-------------------------------------------------------------------------------------
-- traces
-------------------------------------------------------------------------------------

-- a trace of `RepC P k Y`, component by component
RepC-traces-elim : (P : T) (k : ℕ) (Y : T) {s : L} → traces (RepC P k Y) s → RepRun P Y s
RepC-traces-elim P k Y (_ , run) with Rep-reach-approx P k Y run
... | n , Z , r , _ =
  let ok = Rep-no-√-trace P k Y run
      o  = Nest-reach-elim Y (replicate n P) (toNest k n r) ok
  in record { sY = NestOut.sY o ; Y′ = NestOut.Y′ o ; runY = NestOut.runY o ; cps = NestOut.cps o
            ; runs = runs-rep n (NestOut.runs o) ; ilv = NestOut.ilv o ; noTick = ok }

-- component runs re-interleave into a trace of `RepC P k Y`
RepC-traces-intro : (P : T) (k : ℕ) (Y : T) {s : L} → RepRun P Y s → traces (RepC P k Y) s
RepC-traces-intro P k Y o with Rep-reach-intro P k (RepRun.runY o) (RepRun.cps o) (RepRun.runs o)
                                 (RepRun.ilv o) (RepRun.noTick o)
... | _ , r , _ = _ , r

-------------------------------------------------------------------------------------
-- failures
-------------------------------------------------------------------------------------

-- a failure of `RepC P k Y`: component runs with inert ends, and the fresh copy P inert
RepC-failures-elim : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} (P : T) (k : ℕ) (Y : T) {s : L}
                   → failures (RepC P k Y) s B → RepFailOut P Y s B
RepC-failures-elim {B = B} P k Y f with Rep-fail-approx P k Y f
... | n , Z , r , iZ , iP =
  let ok = Rep-no-√-trace P k Y (proj₁ (proj₂ f))
      o  = Nest-reach-elim Y (replicate n P) (toNest k n r) ok
      eq = τ-free-reach (λ st → inert-no-τ iZ st) (NestOut.end o)
  in case Nest-Inert-elim (NestOut.Y′ o) (map proj₂ (NestOut.cps o)) (subst (λ X → Inert X (vis B)) eq iZ) of λ where
       (iY ∷ ics) → record
         { sY = NestOut.sY o ; Y′ = NestOut.Y′ o ; runY = NestOut.runY o ; cps = NestOut.cps o
         ; runs = runs-rep n (NestOut.runs o) ; ilv = NestOut.ilv o ; noTick = ok
         ; inY = iY ; ins = All-map⁻ ics ; inP = iP }

-- component runs with inert ends, and P inert, give a failure of `RepC P k Y`
RepC-failures-intro : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} (P : T) (k : ℕ) (Y : T) {s : L}
                    → RepFailOut P Y s B → failures (RepC P k Y) s B
RepC-failures-intro P k Y o =
  Rep-fail-intro P k (RepFailOut.runY o) (RepFailOut.cps o) (RepFailOut.runs o) (RepFailOut.ilv o)
    (RepFailOut.noTick o) (RepFailOut.inY o) (RepFailOut.ins o) (RepFailOut.inP o)

-------------------------------------------------------------------------------------
-- divergences (over the divergence prefix)
-------------------------------------------------------------------------------------

-- a divergence of `RepC P k Y`: component runs of its prefix, with Y′, a copy end or P's τ divergent
RepC-div-elim : (P : T) (k : ℕ) (Y : T) {s : L} → divergences (RepC P k Y) s → RepDivOut P Y s
RepC-div-elim P k Y d
  with Rep-reach-div P k Y (IsDivergence.reach d) (IsDivergence.divwit d) | Rep-no-√-trace P k Y (IsDivergence.reach d)
... | n , Z , r , inj₁ dZ | ok with Nest-reach-div Y (replicate n P) (toNest k n r) dZ ok
...   | nr , here dY = mkDiv n (IsDivergence.split d) nr ok (inj₁ dY)
...   | nr , there a = mkDiv n (IsDivergence.split d) nr ok (inj₂ (inj₁ (Any-map⁻ a)))
RepC-div-elim P k Y d | n , Z , r , inj₂ pτ | ok =
  mkDiv n (IsDivergence.split d) (nestRun (Nest-reach-elim Y (replicate n P) (toNest k n r) ok)) ok (inj₂ (inj₂ pτ))

-- component runs of a √-free prefix with a divergent part give a divergence of `RepC P k Y`
RepC-div-intro : (P : T) (k : ℕ) (Y : T) {s : L} → RepDivOut P Y s → divergences (RepC P k Y) s
RepC-div-intro P k Y o =
  subst (divergences (RepC P k Y)) (sym (RepDivOut.split o))
    (Rep-div-intro P k {suf = RepDivOut.suf o} (RepDivOut.runY o) (RepDivOut.cps o) (RepDivOut.runs o)
       (RepDivOut.ilv o) (RepDivOut.noTick o) (RepDivOut.dv o))

-------------------------------------------------------------------------------------
-- the trace-level unfold  traces (!ᶜ P) = traces (P ⦀ !ᶜ P)
-------------------------------------------------------------------------------------

-- Stop never moves, so its runs are empty
stop-trace : {s : L} {W : T} → Stop ⟹⟨ s ⟩ W → s ≡ []
stop-trace ⟹-refl             = refl
stop-trace (⟹-τ st _)         = ⊥-elim (stable-no-τ {t = Stop {R = ⊤ {ℓr}}} (λ _ _ → refl) st)
stop-trace (⟹-ev (sRet ()) _)
stop-trace (⟹-ev (sVis refl ()) _)

-- an empty first component drops out of an interleaving
ILv-drop : {ts : List L} {s : L} → ILv ([] ∷ ts) s → ILv ts s
ILv-drop (ilv-nil (_ ∷ z))         = ilv-nil z
ILv-drop (ilv-step (p-there pk) w) = ilv-step pk (ILv-drop w)

-- … and can be added
ILv-pad : {ts : List L} {s : L} → ILv ts s → ILv ([] ∷ ts) s
ILv-pad (ilv-nil z)     = ilv-nil (refl ∷ z)
ILv-pad (ilv-step pk w) = ilv-step (p-there pk) (ILv-pad w)

-- a √-free right trace makes an interleaving √-free (a tick needs both sides)
PI-evl : {sP sQ s : L} → ParInter ∅ES tm sP sQ s → All IsEvl sQ → All IsEvl s
PI-evl pnil          _        = []
PI-evl (psync _ PI)  (_ ∷ ok) = isEvl _ ∷ PI-evl PI ok
PI-evl (psoloL _ PI) ok       = isEvl _ ∷ PI-evl PI ok
PI-evl (psoloR _ PI) (_ ∷ ok) = isEvl _ ∷ PI-evl PI ok
PI-evl p√            (() ∷ _)

-- the right trace of a √-free interleaving is √-free
PI-evlR : {sP sQ s : L} → ParInter ∅ES tm sP sQ s → All IsEvl s → All IsEvl sQ
PI-evlR pnil          _        = []
PI-evlR (psync _ PI)  (_ ∷ ok) = isEvl _ ∷ PI-evlR PI ok
PI-evlR (psoloL _ PI) (_ ∷ ok) = PI-evlR PI ok
PI-evlR (psoloR _ PI) (_ ∷ ok) = isEvl _ ∷ PI-evlR PI ok
PI-evlR p√            (() ∷ _)

-- a trace of `!ᶜ P` interleaves its moved copies' traces alone (the base Stop never moves)
stop-ilv : {P : T} {s : L} (o : RepRun P Stop s) → ILv (map proj₁ (RepRun.cps o)) s
stop-ilv o = ILv-drop (subst (λ x → ILv (x ∷ map proj₁ (RepRun.cps o)) _) (stop-trace (RepRun.runY o)) (RepRun.ilv o))

-- copy runs interleaving into a √-free s give a trace of `!ᶜ P`
copies-trace : (P : T) {s : L} (cps : List (L × T)) → All (λ c → P ⟹⟨ proj₁ c ⟩ proj₂ c) cps
             → ILv (map proj₁ cps) s → All IsEvl s → traces (!ᶜ P) s
copies-trace P cps rs w ok = RepC-traces-intro P 0 Stop
  (record { sY = [] ; Y′ = Stop ; runY = ⟹-refl ; cps = cps ; runs = rs ; ilv = ILv-pad w ; noTick = ok })

-- the first moved copy of a trace of `!ᶜ P` becomes the left operand of `P ⦀ !ᶜ P`
peel→ : (P : T) {s : L} (cps : List (L × T)) → All (λ c → P ⟹⟨ proj₁ c ⟩ proj₂ c) cps
      → ILv (map proj₁ cps) s → All IsEvl s → traces (P ⦀ !ᶜ P) s
peel→ P [] [] (ilv-nil _) _ = _ , ⟹-refl
peel→ P [] [] (ilv-step () _) _
peel→ P ((_ , _) ∷ cps) (rc ∷ rs) w ok with ILv-uncons w ok
... | u , PI , w′ = Par-trace-intro ∅ES tm P (!ᶜ P) rc (proj₂ (copies-trace P cps rs w′ (PI-evlR PI ok))) PI

-- `!ᶜ P` to `P ⦀ !ᶜ P` on traces
unfold→ : (P : T) {s : L} → traces (!ᶜ P) s → traces (P ⦀ !ᶜ P) s
unfold→ P t = let o = RepC-traces-elim P 0 Stop t in
  peel→ P (RepRun.cps o) (RepRun.runs o) (stop-ilv o) (RepRun.noTick o)

-- `P ⦀ !ᶜ P` to `!ᶜ P` on traces: the left operand joins the moved copies
unfold← : (P : T) {s : L} → traces (P ⦀ !ᶜ P) s → traces (!ᶜ P) s
unfold← P (_ , run) with Par-trace-elim ∅ES tm P (!ᶜ P) run
... | sP , sQ , P′ , Q′ , rP , rQ , PI =
  let o  = RepC-traces-elim P 0 Stop (Q′ , rQ)
      ok = PI-evl PI (RepRun.noTick o)
  in copies-trace P ((sP , P′) ∷ RepRun.cps o) (rP ∷ RepRun.runs o) (ILv-cons PI (stop-ilv o) ok) ok

-- the trace-level unfold of uniform replication, no premise on P
!ᶜ-unfold-T : (P : T) {s : L} → traces (!ᶜ P) s ⇔ traces (P ⦀ !ᶜ P) s
!ᶜ-unfold-T P = mk⇔ (unfold→ P) (unfold← P)
