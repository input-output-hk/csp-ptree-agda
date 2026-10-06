{-# OPTIONS --guardedness #-}

-- n-ary introduction for UNIFORM replication `RepC P k Y = Rep⦀ (λ _ → P) k Y`: a run of the
-- running copies Y plus one run of P per copy, glued by an `ILv`, is rebuilt into a run of
-- `RepC P k Y`, spawning each copy on its first move.
--   Rep-reach-intro : the rebuild, endpoint-exact.  The end is `RepC P (k + length ends)
--                     (Nest Y′ ends)`, `ends` the moved copies' ends in SPAWN order, a
--                     permutation (`_↭_`) of `moved cps rs` (the ends of the copies whose run
--                     is not `⟹-refl`, in list order).  Unmoved copies are never spawned: the
--                     fresh supply stands for them.
--   Rep-fail-intro  : with every end inert (and the pristine fresh copy P inert), a failure.
--   Rep-div-intro   : with Y′, some copy end, or P's τ divergent, a divergence.
-- SHAPE.  The running copies are ONE component Z (the Rep state's running nest) with ONE run;
-- spawning a copy merges its run into Z's by a binary interleaving (`ILv-absorb`, then
-- `Par-reach-intro` for the nest's internal collisions).  The recursion
-- (`build` / `peel`) is structural on the merged trace — every call consumes one merged
-- event — with the τ-prefix of the moving component peeled by recursion on its run.  It is
-- NOT structural on the `ILv` witness: a spawn re-derives the witness.
-- `Del`, `Pick-Del` and `ILv-absorb` are generic interleaving lemmas; they live here only
-- because `CSP/Laws/Traces/InterleaveNest.agda` is already committed — live here pending
-- consolidation into InterleaveNest.
-- POSTULATES USED: none.  In closure but not used: `Par-Diverges→`, `offer-LEM`.

open import Level using (Level)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (map⁻)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-refl; ↭-prep; ↭-swap; ↭-trans; ↭-sym)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (All-resp-↭; Any-resp-↭)
open import Data.Maybe using (just; nothing)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map₁ to ⊎-map₁)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂; map₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import Process_Trees

module CSP.Laws.FD.ReplicationIntro {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) {ℓr : Level} where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS {E = E} {I = ExtI E}
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (divergences)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟ using (viewV-ev)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟ using (ParInter; pnil; psoloL; psoloR)
open import CSP.Laws.Traces.ReplicationSteps E-≟
  using (Rep-evRun-intro; Rep-evFresh-intro; Rep-evBoth-intro; repBoth-τ0; repBoth-τ1;
         Rep-τRun-intro; Rep-τFresh-intro)
open import CSP.Laws.Traces.ReplicationApprox E-≟ using (IsEvl; isEvl)
open import CSP.Laws.Traces.InterleaveNest E-≟
  using (Nest; Pick; ILv; ilv-nil; ilv-step; ILv-head-evl; Par-reach-intro)
  renaming (here to p-here; there to p-there)
open import CSP.Laws.FD.ReplicationDivergence E-≟ {ℓr} using (RepC; Rep-Diverges-L; Rep-Diverges-fresh)
open import CSP.Laws.FD.ReplicationRefusals E-≟ {ℓr} using (vis; Inert; RepC-Refuses-intro)
open import CSP.Laws.FD.InterleaveNestFD E-≟ {ℓr} using (Nest-Inert-intro; Nest-Diverges)

private
  -- the process type of this module
  T : Set _
  T = PTree E (ExtI E) (⊤ {ℓr})

  -- its traces
  L : Set _
  L = List (Event√ (⊤ {ℓr}))

  -- the ⊤-merge of `Rep⦀` / `_⦀_`
  tm : ⊤ {ℓr} → ⊤ {ℓr} → ⊤ {ℓr}
  tm _ _ = tt

-------------------------------------------------------------------------------------
-- generic: deleting one component of an interleaving into the first
-------------------------------------------------------------------------------------

-- `Del x xs ys`: ys is xs with one occurrence of x removed
data Del {a} {A : Set a} (x : A) : List A → List A → Set a where
  -- remove the head
  del-here  : ∀ {xs} → Del x (x ∷ xs) xs
  -- remove from the tail
  del-there : ∀ {y xs ys} → Del x xs ys → Del x (y ∷ xs) (y ∷ ys)

-- a predicate on every element holds at the deleted one and on the rest
Del-All : ∀ {a q} {A : Set a} {Q : A → Set q} {x : A} {xs ys : List A}
        → Del x xs ys → All Q xs → Q x × All Q ys
Del-All del-here      (q ∷ qs) = q , qs
Del-All (del-there d) (q ∷ qs) = map₂ (q ∷_) (Del-All d qs)

-- a `Pick` either hit the deleted component (which then had e consed on) or commutes with the deletion
Pick-Del : {e : Event√ (⊤ {ℓr})} {xs ys zs : List L} {u : L}
         → Pick e xs ys → Del u ys zs
         → (Σ[ u′ ∈ L ] (u ≡ e ∷ u′) × Del u′ xs zs) ⊎ (Σ[ ws ∈ List L ] Del u xs ws × Pick e ws zs)
Pick-Del p-here         del-here      = inj₁ (_ , refl , del-here)
Pick-Del p-here         (del-there d) = inj₂ (_ , del-there d , p-here)
Pick-Del (p-there pk)   del-here      = inj₂ (_ , del-here , pk)
Pick-Del (p-there pk)   (del-there d) with Pick-Del pk d
... | inj₁ (u′ , eq , d₁)  = inj₁ (u′ , eq , del-there d₁)
... | inj₂ (ws , d₁ , pk₁) = inj₂ (_ ∷ ws , del-there d₁ , p-there pk₁)

-- any other component of an `ILv` merges into the first by a binary interleaving
ILv-absorb : {t₀ tu s : L} {tss tss⁻ : List L}
           → ILv (t₀ ∷ tss) s → Del tu tss tss⁻ → All IsEvl s
           → Σ[ t ∈ L ] ParInter ∅ES tm t₀ tu t × ILv (t ∷ tss⁻) s
ILv-absorb (ilv-nil (refl ∷ z)) d _ with Del-All d z
... | refl , z⁻ = [] , pnil , ilv-nil (refl ∷ z⁻)
ILv-absorb (ilv-step p-here w) d (isEvl _ ∷ ok) with ILv-absorb w d ok
... | t , PI , w′ = _ ∷ t , psoloL (λ z → z) PI , ilv-step p-here w′
ILv-absorb (ilv-step (p-there pk) w) d (isEvl _ ∷ ok) with Pick-Del pk d
... | inj₁ (_ , refl , d₁) with ILv-absorb w d₁ ok
...   | t , PI , w′ = _ ∷ t , psoloR (λ z → z) PI , ilv-step p-here w′
ILv-absorb (ilv-step (p-there pk) w) d (isEvl _ ∷ ok) | inj₂ (_ , d₁ , pk₁) with ILv-absorb w d₁ ok
...   | t , PI , w′ = t , PI , ilv-step (p-there pk₁) w′

-------------------------------------------------------------------------------------
-- the rebuild
-------------------------------------------------------------------------------------

module _ (P : T) where

  -- one copy's run: trace, end, and the run of P
  CR : Set _
  CR = Σ[ t ∈ L ] Σ[ c′ ∈ T ] (P ⟹⟨ t ⟩ c′)

  -- a copy's trace
  tr : CR → L
  tr = proj₁

  -- the ends of the copies that took a step (visible or τ), in list order
  movedCR : List CR → List T
  movedCR []                         = []
  movedCR ((_ , _  , ⟹-refl)   ∷ us) = movedCR us
  movedCR ((_ , c′ , ⟹-τ _ _)  ∷ us) = c′ ∷ movedCR us
  movedCR ((_ , c′ , ⟹-ev _ _) ∷ us) = c′ ∷ movedCR us

  -- the copy the next merged event belongs to, deleted from the list and from its traces
  pick-copy : (us : List CR) {e : Event√ (⊤ {ℓr})} {tss : List L}
            → Pick e tss (map tr us)
            → Σ[ tu ∈ L ] Σ[ c′ ∈ T ] Σ[ r ∈ P ⟹⟨ e ∷ tu ⟩ c′ ] Σ[ us⁻ ∈ List CR ]
                Del (e ∷ tu , c′ , r) us us⁻ × Del tu tss (map tr us⁻)
  pick-copy ((_ , c′ , r) ∷ us) p-here = _ , c′ , r , us , del-here , del-here
  pick-copy (u ∷ us) (p-there pk) with pick-copy us pk
  ... | tu , c′ , r , us⁻ , d , d′ = tu , c′ , r , u ∷ us⁻ , del-there d , del-there d′

  -- deleting a moved copy moves its end to the front of the moved ends
  moved-Del : {e : Event√ (⊤ {ℓr})} {tu : L} {c′ : T} {r : P ⟹⟨ e ∷ tu ⟩ c′} {us us⁻ : List CR}
            → Del (e ∷ tu , c′ , r) us us⁻ → movedCR us ↭ c′ ∷ movedCR us⁻
  moved-Del {r = ⟹-τ _ _}  del-here = ↭-refl
  moved-Del {r = ⟹-ev _ _} del-here = ↭-refl
  moved-Del (del-there {y = _ , _ , ⟹-refl} d) = moved-Del d
  moved-Del {c′ = c′} (del-there {y = _ , y′ , ⟹-τ _ _} d) =
    ↭-trans (↭-prep y′ (moved-Del d)) (↭-swap y′ c′ ↭-refl)
  moved-Del {c′ = c′} (del-there {y = _ , y′ , ⟹-ev _ _} d) =
    ↭-trans (↭-prep y′ (moved-Del d)) (↭-swap y′ c′ ↭-refl)

  -- a running-nest event lifts through Rep (via the collision's branch 0 when P also offers it)
  run-ev : (k : ℕ) (Z : T) {x : Event} {Z″ W : T} {s : L}
         → Z ─[ ev (evl x) ]─► Z″ → RepC P k Z″ ⟹⟨ s ⟩ W → RepC P k Z ⟹⟨ evl x ∷ s ⟩ W
  run-ev k Z {evLabel X e a} st r with viewV (force P) (X , e) a in eq
  ... | nothing = ⟹-ev (Rep-evRun-intro tm (λ _ → P) k Z st eq) r
  ... | just P′ = ⟹-ev (Rep-evBoth-intro tm (λ _ → P) k Z st (viewV-ev refl eq))
                       (⟹-τ (repBoth-τ0 tm (λ _ → P) k Z _ P′) r)

  -- a fresh copy's event spawns it (via the collision's branch 1 when the nest also offers it)
  fresh-ev : (k : ℕ) (Z : T) {x : Event} {P′ W : T} {s : L}
           → P ─[ ev (evl x) ]─► P′ → RepC P (suc k) (Z ⦀ P′) ⟹⟨ s ⟩ W → RepC P k Z ⟹⟨ evl x ∷ s ⟩ W
  fresh-ev k Z {evLabel X e a} st r with viewV (force Z) (X , e) a in eq
  ... | nothing = ⟹-ev (Rep-evFresh-intro tm (λ _ → P) k Z st eq) r
  ... | just Z″ = ⟹-ev (Rep-evBoth-intro tm (λ _ → P) k Z (viewV-ev refl eq) st)
                       (⟹-τ (repBoth-τ1 tm (λ _ → P) k Z Z″ _) r)

  -- a τ-only run of the running nest lifts through Rep
  Rep-lift-τ : (k : ℕ) {Z Z′ : T} → Z ⟹⟨ [] ⟩ Z′ → RepC P k Z ⟹⟨ [] ⟩ RepC P k Z′
  Rep-lift-τ k ⟹-refl     = ⟹-refl
  Rep-lift-τ k (⟹-τ st r) = ⟹-τ (Rep-τRun-intro tm (λ _ → P) k _ st) (Rep-lift-τ k r)

  -- the spawn counter after one more spawn
  bump : ∀ {k n : ℕ} {A Z : T} {s : L}
       → A ⟹⟨ s ⟩ RepC P (suc k + n) Z → A ⟹⟨ s ⟩ RepC P (k + suc n) Z
  bump {k} {n} {A} {Z} {s} = subst (λ m → A ⟹⟨ s ⟩ RepC P m Z) (sym (+-suc k n))

  -- the rebuild's result: a run to the nest of the running end and the spawned ends
  Out : ℕ → T → L → T → List CR → Set _
  Out k Z s Z′ us = Σ[ ends ∈ List T ]
    (RepC P k Z ⟹⟨ s ⟩ RepC P (k + length ends) (Nest Z′ ends)) × (ends ↭ movedCR us)

  -- no merged event left: the running nest's trailing τs, then each τ-only moved copy spawns
  finish : (k : ℕ) (Z Z′ : T) → Z ⟹⟨ [] ⟩ Z′ → (us : List CR) → All (λ u → tr u ≡ []) us
         → Out k Z [] Z′ us
  finish k Z Z′ rZ [] [] =
    [] , subst (λ m → RepC P k Z ⟹⟨ [] ⟩ RepC P m Z′) (sym (+-identityʳ k)) (Rep-lift-τ k rZ) , ↭-refl
  finish k Z Z′ rZ ((_ , _ , ⟹-refl) ∷ us) (refl ∷ z) = finish k Z Z′ rZ us z
  finish k Z Z′ rZ ((_ , c′ , ⟹-τ {q = P₁} st rest) ∷ us) (refl ∷ z)
    with finish (suc k) (Z ⦀ P₁) (Z′ ⦀ c′) (Par-reach-intro ∅ES tm Z P₁ rZ rest pnil []) us z
  ... | ends , r , p = c′ ∷ ends , bump (⟹-τ (Rep-τFresh-intro tm (λ _ → P) k Z st) r) , ↭-prep c′ p

  -- the rebuild from the running nest's run and the unspawned copies' runs, by the merged trace
  build : (k : ℕ) (Z Z′ : T) (tZ : L) → Z ⟹⟨ tZ ⟩ Z′ → (us : List CR) (s : L)
        → ILv (tZ ∷ map tr us) s → All IsEvl s → Out k Z s Z′ us

  -- the same when the next merged event is the running nest's: peel its τ-prefix, lift the event
  peel : (k : ℕ) (Z Z′ : T) (x : Event) (t : L) → Z ⟹⟨ evl x ∷ t ⟩ Z′ → (us : List CR) (s : L)
       → ILv (t ∷ map tr us) s → All IsEvl s → Out k Z (evl x ∷ s) Z′ us

  build k Z Z′ tZ rZ us [] (ilv-nil (refl ∷ z)) _ = finish k Z Z′ rZ us (map⁻ z)
  build k Z Z′ tZ rZ us (_ ∷ s) (ilv-step p-here w) (isEvl x ∷ ok) = peel k Z Z′ x _ rZ us s w ok
  build k Z Z′ tZ rZ us (_ ∷ s) (ilv-step (p-there pk) w) (isEvl x ∷ ok) with pick-copy us pk
  ... | tu , c′ , ⟹-ev {q = P′} st rest , us⁻ , d , d′ with ILv-absorb w d′ ok
  ...   | t , PI , w′ with build (suc k) (Z ⦀ P′) (Z′ ⦀ c′) t
                              (Par-reach-intro ∅ES tm Z P′ rZ rest PI (ILv-head-evl w′ ok)) us⁻ s w′ ok
  ...     | ends , r , p =
    c′ ∷ ends , bump (fresh-ev k Z st r) , ↭-trans (↭-prep c′ p) (↭-sym (moved-Del d))
  build k Z Z′ tZ rZ us (_ ∷ s) (ilv-step (p-there pk) w) (isEvl x ∷ ok)
    | tu , c′ , ⟹-τ {q = P₁} st rest , us⁻ , d , d′ with ILv-absorb w d′ ok
  ...   | t , PI , w′ with peel (suc k) (Z ⦀ P₁) (Z′ ⦀ c′) x t
                             (Par-reach-intro ∅ES tm Z P₁ rZ rest (psoloR (λ z → z) PI)
                                (isEvl x ∷ ILv-head-evl w′ ok)) us⁻ s w′ ok
  ...     | ends , r , p =
    c′ ∷ ends , bump (⟹-τ (Rep-τFresh-intro tm (λ _ → P) k Z st) r) , ↭-trans (↭-prep c′ p) (↭-sym (moved-Del d))

  peel k Z Z′ x t (⟹-τ st rest) us s w ok with peel k _ Z′ x t rest us s w ok
  ... | ends , r , p = ends , ⟹-τ (Rep-τRun-intro tm (λ _ → P) k Z st) r , p
  peel k Z Z′ x t (⟹-ev st rest) us s w ok with build k _ Z′ t rest us s w ok
  ... | ends , r , p = ends , run-ev k Z st r , p

  -----------------------------------------------------------------------------------
  -- the interface: copies as (trace, end) pairs with an `All` of runs
  -----------------------------------------------------------------------------------

  -- pair the copies with their runs
  toCR : (cps : List (L × T)) → All (λ c → P ⟹⟨ proj₁ c ⟩ proj₂ c) cps → List CR
  toCR []              []       = []
  toCR ((t , c′) ∷ cps) (r ∷ rs) = (t , c′ , r) ∷ toCR cps rs

  -- pairing keeps the traces
  toCR-tr : (cps : List (L × T)) (rs : All (λ c → P ⟹⟨ proj₁ c ⟩ proj₂ c) cps)
          → map tr (toCR cps rs) ≡ map proj₁ cps
  toCR-tr []             []       = refl
  toCR-tr ((t , _) ∷ cps) (_ ∷ rs) = cong (t ∷_) (toCR-tr cps rs)

  -- the ends of the copies whose run is not `⟹-refl`, in list order
  moved : (cps : List (L × T)) → All (λ c → P ⟹⟨ proj₁ c ⟩ proj₂ c) cps → List T
  moved cps rs = movedCR (toCR cps rs)

  -- a property of every copy end holds of every moved end
  moved-All : ∀ {q} {Q : T → Set q} (cps : List (L × T)) (rs : All (λ c → P ⟹⟨ proj₁ c ⟩ proj₂ c) cps)
            → All (λ c → Q (proj₂ c)) cps → All Q (moved cps rs)
  moved-All []            []              []       = []
  moved-All ((_ , _) ∷ cps) (⟹-refl ∷ rs)   (_ ∷ qs) = moved-All cps rs qs
  moved-All ((_ , _) ∷ cps) (⟹-τ _ _ ∷ rs)  (q ∷ qs) = q ∷ moved-All cps rs qs
  moved-All ((_ , _) ∷ cps) (⟹-ev _ _ ∷ rs) (q ∷ qs) = q ∷ moved-All cps rs qs

  -- a property of some copy end holds of some moved end, or of P (an unmoved copy's end)
  moved-Any : ∀ {q} {Q : T → Set q} (cps : List (L × T)) (rs : All (λ c → P ⟹⟨ proj₁ c ⟩ proj₂ c) cps)
            → Any (λ c → Q (proj₂ c)) cps → Any Q (moved cps rs) ⊎ Q P
  moved-Any ((_ , _) ∷ cps) (⟹-refl ∷ rs)   (here q)  = inj₂ q
  moved-Any ((_ , _) ∷ cps) (⟹-τ _ _ ∷ rs)  (here q)  = inj₁ (here q)
  moved-Any ((_ , _) ∷ cps) (⟹-ev _ _ ∷ rs) (here q)  = inj₁ (here q)
  moved-Any ((_ , _) ∷ cps) (⟹-refl ∷ rs)   (there a) = moved-Any cps rs a
  moved-Any ((_ , _) ∷ cps) (⟹-τ _ _ ∷ rs)  (there a) = ⊎-map₁ there (moved-Any cps rs a)
  moved-Any ((_ , _) ∷ cps) (⟹-ev _ _ ∷ rs) (there a) = ⊎-map₁ there (moved-Any cps rs a)

  -- component runs rebuild into a run of `RepC P k Y`, spawning the moved copies in first-move order
  Rep-reach-intro : (k : ℕ) {Y Y′ : T} {sY s : L} → Y ⟹⟨ sY ⟩ Y′
                  → (cps : List (L × T)) (rs : All (λ c → P ⟹⟨ proj₁ c ⟩ proj₂ c) cps)
                  → ILv (sY ∷ map proj₁ cps) s → All IsEvl s
                  → Σ[ ends ∈ List T ] (RepC P k Y ⟹⟨ s ⟩ RepC P (k + length ends) (Nest Y′ ends))
                                     × (ends ↭ moved cps rs)
  Rep-reach-intro k {Y} {Y′} {sY} {s} rY cps rs w ok =
    build k Y Y′ sY rY (toCR cps rs) s (subst (λ ts → ILv (sY ∷ ts) s) (sym (toCR-tr cps rs)) w) ok

  -- component runs with inert ends, and an inert fresh copy, give a failure of `RepC P k Y`
  Rep-fail-intro : ∀ {ℓx} {B : Event√ (⊤ {ℓr}) → Set ℓx} (k : ℕ) {Y Y′ : T} {sY s : L} → Y ⟹⟨ sY ⟩ Y′
                 → (cps : List (L × T)) (rs : All (λ c → P ⟹⟨ proj₁ c ⟩ proj₂ c) cps)
                 → ILv (sY ∷ map proj₁ cps) s → All IsEvl s
                 → Inert Y′ (vis B) → All (λ c → Inert (proj₂ c) (vis B)) cps → Inert P (vis B)
                 → failures (RepC P k Y) s B
  Rep-fail-intro k {Y′ = Y′} rY cps rs w ok iY ics iP with Rep-reach-intro k rY cps rs w ok
  ... | ends , r , p =
    _ , r , RepC-Refuses-intro P (k + length ends) (Nest Y′ ends)
              (Nest-Inert-intro Y′ ends (iY ∷ All-resp-↭ (↭-sym p) (moved-All cps rs ics))) iP

  -- the end of a rebuild diverges when Y′, some copy end, or P's τ does
  Rep-end-div : (k : ℕ) {Y′ : T} (cps : List (L × T)) (rs : All (λ c → P ⟹⟨ proj₁ c ⟩ proj₂ c) cps)
                (ends : List T) → ends ↭ moved cps rs
              → Diverges Y′ ⊎ Any (λ c → Diverges (proj₂ c)) cps ⊎ Σ[ P′ ∈ T ] (P ─[ τ ]─► P′)
              → Diverges (RepC P k (Nest Y′ ends))
  Rep-end-div k {Y′} cps rs ends p (inj₁ d) = Rep-Diverges-L P k (Nest-Diverges Y′ ends (here d))
  Rep-end-div k {Y′} cps rs ends p (inj₂ (inj₁ a)) with moved-Any cps rs a
  ... | inj₁ a′ = Rep-Diverges-L P k (Nest-Diverges Y′ ends (there (Any-resp-↭ (↭-sym p) a′)))
  ... | inj₂ dP = Rep-Diverges-fresh (Diverges.step dP)
  Rep-end-div k cps rs ends p (inj₂ (inj₂ (_ , st))) = Rep-Diverges-fresh st

  -- component runs of a √-free prefix with a divergent end (or P τ-able) give a divergence
  Rep-div-intro : (k : ℕ) {Y Y′ : T} {sY pre suf : L} → Y ⟹⟨ sY ⟩ Y′
                → (cps : List (L × T)) (rs : All (λ c → P ⟹⟨ proj₁ c ⟩ proj₂ c) cps)
                → ILv (sY ∷ map proj₁ cps) pre → All IsEvl pre
                → Diverges Y′ ⊎ Any (λ c → Diverges (proj₂ c)) cps ⊎ Σ[ P′ ∈ T ] (P ─[ τ ]─► P′)
                → divergences (RepC P k Y) (pre ++ suf)
  Rep-div-intro k {Y′ = Y′} {pre = pre} {suf = suf} rY cps rs w ok dv with Rep-reach-intro k rY cps rs w ok
  ... | ends , r , p = record
    { prefix = pre ; suffix = suf ; split = refl ; witness = RepC P (k + length ends) (Nest Y′ ends)
    ; reach  = r ; divwit = Rep-end-div (k + length ends) cps rs ends p dv }
