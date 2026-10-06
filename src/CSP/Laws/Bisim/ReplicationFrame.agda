{-# OPTIONS --guardedness #-}

-- The STRONG frame law for native replication `Rep⦀` (CSP.Replication), under
-- alphabet disjointness, with its ≈DR / ≈FD corollaries.
--
--   Rep-state-cong-∼ : X ∼ Y → Rep⦀ P k X ∼ Rep⦀ P k Y                  (unconditional)
--   Rep-frame-∼      : RepDisj α P → OffersOnly βQ Q → OffersOnly βS S → Disj βQ βS
--                    → FreshFrom α k βQ → FreshFrom α k βS
--                    → Rep⦀ P k (Q ⦀ S) ∼ (Q ⦀ Rep⦀ P k S)
--   Rep-frame-DR / Rep-frame-FD : the same at ≈DR / ≈FD;  !-frame-∼ : the S = Stop case.
--
-- The frame is proved over the generalised relation  Rep⦀ P k X  ~  Q ⦀ Rep⦀ P k S
-- whenever  X ∼ Q ⦀ S  (`frame-gen`).  Under the premises no two components ever offer
-- the same event, so every collision case (inside `Q ⦀ S`, running-vs-fresh copy, `Q`
-- vs `Rep`) is absurd, and every step is the step of exactly one component.  A fresh
-- spawn moves the copy `P k` into `S` (βS grows by `α k`, k becomes suc k), and the new
-- `X ⦀ P′ ∼ Q ⦀ (S ⦀ P′)` is `cong-⦀-∼` followed by `⦀-assoc-∼-disj` — non-corecursive
-- terms passed as the ARGUMENT of the corecursive call.
--
-- POSTULATE PROVENANCE (audit of this module's closure, 2026-09-30, Task 6 report).
-- FIVE postulate modules are IN the closure: `Semantics.DRImpliesFD` (`¬-divergent→normal`)
-- and, via `CSP.Laws.Bisim.DRCongruenceRep`, `CSP.Laws.Bisim.DRCongruence` (`modA-transfer`),
-- `CSP.Laws.FD.{ExtChoice,Interrupt,Parallel}Divergence` (`□/△/Par-Diverges→`).
-- `Rep-state-cong-∼`, `Rep-frame-∼`, `!-frame-∼` and `Rep-frame-DR` USE none of them: the
-- closures of `ReplicationSteps`, `ParallelCong`, `TraceLawsParallel(Elim/Trace)` and
-- `StrongImpliesDR` are postulate-free.  `CSP.Laws.Bisim.ParallelAssocDisj` (whose own
-- closure holds the postulates) is used only through its postulate-free parts: its
-- imports (`ParallelAssocDisj.agda:41-50`) are the Par elim/intro lemmas plus
-- `DRCongruenceRep`'s `Alpha`, `Disj`, `OffersOnly`, `OffersOnly-mono` and `OffersOnly-⦀`,
-- where `OffersOnly-⦀ = OffersOnly-Par ∅ES …` (`DRCongruenceRep.agda:487`) and
-- `OffersOnly-Par`/`-brBoth`/`-deadlock` are built from Par elim lemmas and
-- `deadlock-no-ev` alone.
-- `Rep-frame-FD` USES `¬-divergent→normal`: `drbisim→≈FD` → `drbisim→⊑FD` → `drbisim→fsim`,
-- whose `stab` field is built from it.
--
-- The premises are load-bearing: `CSP.Examples.ReplicationSanity.frame-needs-disj`
-- refutes `Rep⦀ P 0 (Q ⦀ S) ∼ (Q ⦀ Rep⦀ P 0 S)` when Q, S and every copy offer the same
-- event (Task 6 Step 7).  They are also dischargeable: `CSP.Examples.ReplicationIndexOrder.
-- frame-Pt` applies `!-frame-∼` to the index-dependent copies `Pt j = tick j ⟶₀ Stop`
-- with singleton alphabets (non-vacuity).

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; suc; _≤_)
open import Data.Nat.Properties using (≤-refl; <⇒≤; <⇒≢)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Process_Trees

module CSP.Laws.Bisim.ReplicationFrame {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import CSP.Replication E-≟ using (Rep; Rep⦀)
open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E}
open import Semantics.DRBisim {E = E} {I = ExtI E} using (_≈DR_)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import CSP.Laws.Traces.TraceLawsParallel E-≟
  using (Par-τ-L; Par-τ-R; Par-soloL; Par-soloR)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟
  using ( Par-τ-elim; τL; τR
        ; Par-ev-elim; evSync; evL; evR; evBoth; ev√; viewV-ev )
open import CSP.Laws.Traces.ReplicationSteps E-≟
  using ( repBoth
        ; Rep-ev-elim; evRun; evFresh
        ; Rep-τ-elim; τRun; τFresh
        ; Rep-no-√; repBoth-no-ev; repBoth-τ-elim; repBoth-τ0; repBoth-τ1
        ; Rep-evRun-intro; Rep-evFresh-intro; Rep-evBoth-intro
        ; Rep-τRun-intro; Rep-τFresh-intro )
  renaming (evBoth to repEvBoth)
open import CSP.Laws.Bisim.ParallelCong E-≟ using (cong-⦀-∼; noOffer-∼)
open import CSP.Laws.Bisim.DRCongruenceRep E-≟ using (Alpha; Disj; OffersOnly)
open import CSP.Laws.Bisim.ParallelAssocDisj E-≟
  using (OffersOnly-∼; ⦀-assoc-∼-disj; _∪α_; Disj-sym; Disj-∪; OffersOnly-⦀∪; no-offer)

-------------------------------------------------------------------------------------
-- Premises
-------------------------------------------------------------------------------------

-- β never meets a copy not yet spawned (every copy from index k on)
FreshFrom : (ℕ → Alpha) → ℕ → Alpha → Set (lsuc ℓ ⊔ ℓe)
FreshFrom α k β = ∀ j → k ≤ j → Disj β (α j)

-- a fresh-from-k alphabet is fresh from suc k on
fresh-suc : {α : ℕ → Alpha} {k : ℕ} {β : Alpha} → FreshFrom α k β → FreshFrom α (suc k) β
fresh-suc f j k<j = f j (<⇒≤ k<j)

-- `Stop` offers nothing, so it is confined by every alphabet
OffersOnly-Stop : ∀ {ℓr} {R : Set ℓr} {α : Alpha} → OffersOnly α (Stop {R = R})
OffersOnly-Stop .OffersOnly.now  (sVis refl ())
OffersOnly-Stop .OffersOnly.step (sRet ())
OffersOnly-Stop .OffersOnly.step (sSil ())
OffersOnly-Stop .OffersOnly.step (sVis refl ())
OffersOnly-Stop .OffersOnly.step (sTau refl ())

module _ {ℓr : Level} where

  private
    -- the process type of the interleaving instance
    T : Set _
    T = PTree E (ExtI E) (⊤ {ℓr})

    -- the ⊤-merge of `Rep⦀` / `⦀`
    tm : ⊤ {ℓr} → ⊤ {ℓr} → ⊤ {ℓr}
    tm _ _ = tt

  -- the copies are each confined, and pairwise disjoint
  record RepDisj (α : ℕ → Alpha) (P : ℕ → T) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
    field
      conf : ∀ j → OffersOnly (α j) (P j)
      disj : ∀ {i j} → i ≢ j → Disj (α i) (α j)

  -- absorbing the spawned copy k into β keeps it fresh from suc k on
  fresh-absorb : {α : ℕ → Alpha} {P : ℕ → T} {k : ℕ} {β : Alpha}
               → RepDisj α P → FreshFrom α k β → FreshFrom α (suc k) (β ∪α α k)
  fresh-absorb rd f j k<j at a (inj₁ x) y = f j (<⇒≤ k<j) at a x y
  fresh-absorb rd f j k<j at a (inj₂ x) y = RepDisj.disj rd (<⇒≢ k<j) at a x y

  -- `Rep⦀ P k S` offers no γ-event when γ misses S's alphabet and the fresh copy's
  rep-quiet : {P : ℕ → T} {k : ℕ} {S : T} {β γ δ : Alpha} {A : Set ℓ} {e : E A} {a : A}
            → OffersOnly β S → OffersOnly δ (P k) → Disj γ β → Disj γ δ → γ (A , e) a
            → viewV (force (Rep⦀ P k S)) (A , e) a ≡ nothing
  rep-quiet {P = P} {k = k} {S = S} {A = A} {e = e} {a = a} ooS ooP dS dP x
    with viewV (force (Rep⦀ P k S)) (A , e) a in eq
  ... | nothing = refl
  ... | just _ with Rep-ev-elim tm P k S (viewV-ev {P = Rep⦀ P k S} refl eq)
  ...   | evRun Sst _       = ⊥-elim (dS _ _ x (OffersOnly.now ooS Sst))
  ...   | evFresh Pst _     = ⊥-elim (dP _ _ x (OffersOnly.now ooP Pst))
  ...   | repEvBoth Sst _   = ⊥-elim (dS _ _ x (OffersOnly.now ooS Sst))

  -----------------------------------------------------------------------------------
  -- Congruence in the running-copies state (forward-declared corecursive group)
  -----------------------------------------------------------------------------------

  -- `Rep⦀` is a strong congruence in its running-copies state, unconditionally
  Rep-state-cong-∼ : {P : ℕ → T} {k : ℕ} {X Y : T} → X ∼ Y → Rep⦀ P k X ∼ Rep⦀ P k Y

  -- the collision node is a strong congruence in its two state arguments
  repBoth-cong-∼ : {P : ℕ → T} {k : ℕ} {X Y X′ Y′ P′ : T}
                 → X ∼ Y → X′ ∼ Y′ → repBoth tm P k X X′ P′ ∼ repBoth tm P k Y Y′ P′

  -- a visible / √ step of `Rep⦀ P k X` is matched by `Rep⦀ P k Y`
  state-ev : {P : ℕ → T} {k : ℕ} {X Y : T} → X ∼ Y
           → {M : T} {l : Event√ (⊤ {ℓr})} → Rep⦀ P k X ─[ ev l ]─► M
           → Σ[ M′ ∈ T ] ((Rep⦀ P k Y ─[ ev l ]─► M′) × (M ∼ M′))

  -- a τ step of `Rep⦀ P k X` is matched by `Rep⦀ P k Y`
  state-tau : {P : ℕ → T} {k : ℕ} {X Y : T} → X ∼ Y
            → {M : T} → Rep⦀ P k X ─[ τ ]─► M
            → Σ[ M′ ∈ T ] ((Rep⦀ P k Y ─[ τ ]─► M′) × (M ∼ M′))

  -- a τ step of one collision node is matched by the other
  repBoth-tau : {P : ℕ → T} {k : ℕ} {X Y X′ Y′ P′ : T} → X ∼ Y → X′ ∼ Y′
              → {M : T} → repBoth tm P k X X′ P′ ─[ τ ]─► M
              → Σ[ M′ ∈ T ] ((repBoth tm P k Y Y′ P′ ─[ τ ]─► M′) × (M ∼ M′))

  state-ev {P = P} {k = k} {X = X} xy {l = √ _} st = ⊥-elim (Rep-no-√ tm P k X st)
  state-ev {P = P} {k = k} {X = X} {Y = Y} xy {l = evl (evLabel A e a)} st
    with Rep-ev-elim tm P k X st
  ... | evRun Xst nP with SSimF.on-ev (Sbisim.fwd xy) Xst
  ...   | _ , Yst , x′y′ = _ , Rep-evRun-intro tm P k Y Yst nP , Rep-state-cong-∼ x′y′
  state-ev {P = P} {k = k} {X = X} {Y = Y} xy {l = evl (evLabel A e a)} st
      | evFresh Pst nX =
        _ , Rep-evFresh-intro tm P k Y Pst (noOffer-∼ X Y xy nX)
          , Rep-state-cong-∼ (cong-⦀-∼ xy (sbisim-refl _))
  state-ev {P = P} {k = k} {X = X} {Y = Y} xy {l = evl (evLabel A e a)} st
      | repEvBoth Xst Pst with SSimF.on-ev (Sbisim.fwd xy) Xst
  ...   | _ , Yst , x′y′ = _ , Rep-evBoth-intro tm P k Y Yst Pst , repBoth-cong-∼ xy x′y′

  state-tau {P = P} {k = k} {X = X} {Y = Y} xy st with Rep-τ-elim tm P k X st
  ... | τRun Xst with SSimF.on-tau (Sbisim.fwd xy) Xst
  ...   | _ , Yst , x′y′ = _ , Rep-τRun-intro tm P k Y Yst , Rep-state-cong-∼ x′y′
  state-tau {P = P} {k = k} {X = X} {Y = Y} xy st | τFresh Pst =
    _ , Rep-τFresh-intro tm P k Y Pst , Rep-state-cong-∼ (cong-⦀-∼ xy (sbisim-refl _))

  repBoth-tau {P = P} {k = k} {X = X} {Y = Y} {X′ = X′} {Y′ = Y′} {P′ = P′} xy x′y′ st
    with repBoth-τ-elim tm P k X X′ P′ st
  ... | inj₁ refl = _ , repBoth-τ0 tm P k Y Y′ P′ , Rep-state-cong-∼ x′y′
  ... | inj₂ refl = _ , repBoth-τ1 tm P k Y Y′ P′ , Rep-state-cong-∼ (cong-⦀-∼ xy (sbisim-refl P′))

  Rep-state-cong-∼ xy .Sbisim.fwd .SSimF.on-ev  = state-ev  xy
  Rep-state-cong-∼ xy .Sbisim.fwd .SSimF.on-tau = state-tau xy
  Rep-state-cong-∼ xy .Sbisim.bwd .SSimF.on-ev  = state-ev  (sbisim-sym xy)
  Rep-state-cong-∼ xy .Sbisim.bwd .SSimF.on-tau = state-tau (sbisim-sym xy)

  repBoth-cong-∼ {P = P} {k = k} {X = X} {X′ = X′} {P′ = P′} xy x′y′ .Sbisim.fwd .SSimF.on-ev st =
    ⊥-elim (repBoth-no-ev tm P k X X′ P′ st)
  repBoth-cong-∼ xy x′y′ .Sbisim.fwd .SSimF.on-tau = repBoth-tau xy x′y′
  repBoth-cong-∼ {P = P} {k = k} {Y = Y} {Y′ = Y′} {P′ = P′} xy x′y′ .Sbisim.bwd .SSimF.on-ev st =
    ⊥-elim (repBoth-no-ev tm P k Y Y′ P′ st)
  repBoth-cong-∼ xy x′y′ .Sbisim.bwd .SSimF.on-tau = repBoth-tau (sbisim-sym xy) (sbisim-sym x′y′)

  -----------------------------------------------------------------------------------
  -- The frame law (forward-declared corecursive group)
  -----------------------------------------------------------------------------------

  -- generalised frame: Rep⦀ P k X ∼ Q ⦀ Rep⦀ P k S whenever X ∼ Q ⦀ S
  frame-gen : {α : ℕ → Alpha} {P : ℕ → T} {k : ℕ} {βQ βS : Alpha} {Q S X : T}
            → RepDisj α P → OffersOnly βQ Q → OffersOnly βS S → Disj βQ βS
            → FreshFrom α k βQ → FreshFrom α k βS
            → X ∼ (Q ⦀ S) → Rep⦀ P k X ∼ (Q ⦀ Rep⦀ P k S)

  -- the mirror orientation, the residual relation of the `bwd` transfer
  frame-gen⁻¹ : {α : ℕ → Alpha} {P : ℕ → T} {k : ℕ} {βQ βS : Alpha} {Q S X : T}
              → RepDisj α P → OffersOnly βQ Q → OffersOnly βS S → Disj βQ βS
              → FreshFrom α k βQ → FreshFrom α k βS
              → X ∼ (Q ⦀ S) → (Q ⦀ Rep⦀ P k S) ∼ Rep⦀ P k X

  -- a visible / √ step of the replicated side is matched by the framed side
  frame-ev : {α : ℕ → Alpha} {P : ℕ → T} {k : ℕ} {βQ βS : Alpha} {Q S X : T}
           → RepDisj α P → OffersOnly βQ Q → OffersOnly βS S → Disj βQ βS
           → FreshFrom α k βQ → FreshFrom α k βS → X ∼ (Q ⦀ S)
           → {M : T} {l : Event√ (⊤ {ℓr})} → Rep⦀ P k X ─[ ev l ]─► M
           → Σ[ M′ ∈ T ] (((Q ⦀ Rep⦀ P k S) ─[ ev l ]─► M′) × (M ∼ M′))

  -- a τ step of the replicated side is matched by the framed side
  frame-tau : {α : ℕ → Alpha} {P : ℕ → T} {k : ℕ} {βQ βS : Alpha} {Q S X : T}
            → RepDisj α P → OffersOnly βQ Q → OffersOnly βS S → Disj βQ βS
            → FreshFrom α k βQ → FreshFrom α k βS → X ∼ (Q ⦀ S)
            → {M : T} → Rep⦀ P k X ─[ τ ]─► M
            → Σ[ M′ ∈ T ] (((Q ⦀ Rep⦀ P k S) ─[ τ ]─► M′) × (M ∼ M′))

  -- a visible / √ step of the framed side is matched by the replicated side
  unframe-ev : {α : ℕ → Alpha} {P : ℕ → T} {k : ℕ} {βQ βS : Alpha} {Q S X : T}
             → RepDisj α P → OffersOnly βQ Q → OffersOnly βS S → Disj βQ βS
             → FreshFrom α k βQ → FreshFrom α k βS → X ∼ (Q ⦀ S)
             → {M : T} {l : Event√ (⊤ {ℓr})} → (Q ⦀ Rep⦀ P k S) ─[ ev l ]─► M
             → Σ[ M′ ∈ T ] ((Rep⦀ P k X ─[ ev l ]─► M′) × (M ∼ M′))

  -- a τ step of the framed side is matched by the replicated side
  unframe-tau : {α : ℕ → Alpha} {P : ℕ → T} {k : ℕ} {βQ βS : Alpha} {Q S X : T}
              → RepDisj α P → OffersOnly βQ Q → OffersOnly βS S → Disj βQ βS
              → FreshFrom α k βQ → FreshFrom α k βS → X ∼ (Q ⦀ S)
              → {M : T} → (Q ⦀ Rep⦀ P k S) ─[ τ ]─► M
              → Σ[ M′ ∈ T ] ((Rep⦀ P k X ─[ τ ]─► M′) × (M ∼ M′))

  frame-ev {P = P} {k = k} {X = X} rd ooQ ooS dQS fQ fS xqs {l = √ _} st =
    ⊥-elim (Rep-no-√ tm P k X st)
  frame-ev {P = P} {k = k} {Q = Q} {S = S} {X = X} rd ooQ ooS dQS fQ fS xqs
           {l = evl (evLabel A e a)} st
    with Rep-ev-elim tm P k X st
  ... | evRun Xst nP with SSimF.on-ev (Sbisim.fwd xqs) Xst
  ...   | _ , QSst , x′z with Par-ev-elim ∅ES tm Q S QSst
  ...     | evSync () _ _
  ...     | evL _ Qst =
            _ , Par-soloL ∅ES tm Q (Rep⦀ P k S) (λ ()) Qst
                  (rep-quiet ooS (RepDisj.conf rd k) dQS (fQ k ≤-refl) (OffersOnly.now ooQ Qst))
              , frame-gen rd (OffersOnly.step ooQ Qst) ooS dQS fQ fS x′z
  ...     | evR _ Sst =
            _ , Par-soloR ∅ES tm Q (Rep⦀ P k S) (λ ()) (Rep-evRun-intro tm P k S Sst nP)
                  (no-offer ooQ (Disj-sym dQS) (OffersOnly.now ooS Sst))
              , frame-gen rd ooQ (OffersOnly.step ooS Sst) dQS fQ fS x′z
  ...     | evBoth _ Qst Sst = ⊥-elim (dQS _ _ (OffersOnly.now ooQ Qst) (OffersOnly.now ooS Sst))
  frame-ev {P = P} {k = k} {Q = Q} {S = S} {X = X} rd ooQ ooS dQS fQ fS xqs
           {l = evl (evLabel A e a)} st
      | evFresh Pst _ =
        _ , Par-soloR ∅ES tm Q (Rep⦀ P k S) (λ ())
              (Rep-evFresh-intro tm P k S Pst
                 (no-offer ooS (Disj-sym (fS k ≤-refl)) (OffersOnly.now (RepDisj.conf rd k) Pst)))
              (no-offer ooQ (Disj-sym (fQ k ≤-refl)) (OffersOnly.now (RepDisj.conf rd k) Pst))
          , frame-gen rd ooQ (OffersOnly-⦀∪ ooS ooP′) (Disj-∪ dQS (fQ k ≤-refl))
                      (fresh-suc fQ) (fresh-absorb rd fS)
                      (sbisim-trans (cong-⦀-∼ xqs (sbisim-refl _))
                                    (⦀-assoc-∼-disj ooQ ooS ooP′ dQS (fQ k ≤-refl) (fS k ≤-refl)))
    where -- the spawned copy's residual stays confined to its own alphabet α k
          ooP′ = OffersOnly.step (RepDisj.conf rd k) Pst
  frame-ev {P = P} {k = k} {Q = Q} {S = S} {X = X} rd ooQ ooS dQS fQ fS xqs
           {l = evl (evLabel A e a)} st
      | repEvBoth Xst Pst =
        ⊥-elim (Disj-∪ (Disj-sym (fQ k ≤-refl)) (Disj-sym (fS k ≤-refl)) _ _
                  (OffersOnly.now (RepDisj.conf rd k) Pst)
                  (OffersOnly.now (OffersOnly-∼ xqs (OffersOnly-⦀∪ ooQ ooS)) Xst))

  frame-tau {P = P} {k = k} {Q = Q} {S = S} {X = X} rd ooQ ooS dQS fQ fS xqs st
    with Rep-τ-elim tm P k X st
  ... | τRun Xst with SSimF.on-tau (Sbisim.fwd xqs) Xst
  ...   | _ , QSst , x′z with Par-τ-elim ∅ES tm Q S QSst
  ...     | τL _ Qst refl =
            _ , Par-τ-L ∅ES tm Q (Rep⦀ P k S) Qst
              , frame-gen rd (OffersOnly.step ooQ Qst) ooS dQS fQ fS x′z
  ...     | τR _ Sst refl =
            _ , Par-τ-R ∅ES tm Q (Rep⦀ P k S) (Rep-τRun-intro tm P k S Sst)
              , frame-gen rd ooQ (OffersOnly.step ooS Sst) dQS fQ fS x′z
  frame-tau {P = P} {k = k} {Q = Q} {S = S} {X = X} rd ooQ ooS dQS fQ fS xqs st
      | τFresh Pst =
        _ , Par-τ-R ∅ES tm Q (Rep⦀ P k S) (Rep-τFresh-intro tm P k S Pst)
          , frame-gen rd ooQ (OffersOnly-⦀∪ ooS ooP′) (Disj-∪ dQS (fQ k ≤-refl))
                      (fresh-suc fQ) (fresh-absorb rd fS)
                      (sbisim-trans (cong-⦀-∼ xqs (sbisim-refl _))
                                    (⦀-assoc-∼-disj ooQ ooS ooP′ dQS (fQ k ≤-refl) (fS k ≤-refl)))
    where -- the spawned copy's residual stays confined to its own alphabet α k
          ooP′ = OffersOnly.step (RepDisj.conf rd k) Pst

  unframe-ev {P = P} {k = k} {Q = Q} {S = S} rd ooQ ooS dQS fQ fS xqs {l = √ _} st
    with Par-ev-elim ∅ES tm Q (Rep⦀ P k S) st
  ... | ev√ _ ()
  unframe-ev {P = P} {k = k} {Q = Q} {S = S} {X = X} rd ooQ ooS dQS fQ fS xqs
             {l = evl (evLabel A e a)} st
    with Par-ev-elim ∅ES tm Q (Rep⦀ P k S) st
  ... | evSync () _ _
  ... | evL _ Qst
      with SSimF.on-ev (Sbisim.bwd xqs)
             (Par-soloL ∅ES tm Q S (λ ()) Qst (no-offer ooS dQS (OffersOnly.now ooQ Qst)))
  ...   | _ , Xst , zx′ =
          _ , Rep-evRun-intro tm P k X Xst
                (no-offer (RepDisj.conf rd k) (fQ k ≤-refl) (OffersOnly.now ooQ Qst))
            , frame-gen⁻¹ rd (OffersOnly.step ooQ Qst) ooS dQS fQ fS (sbisim-sym zx′)
  unframe-ev {P = P} {k = k} {Q = Q} {S = S} {X = X} rd ooQ ooS dQS fQ fS xqs
             {l = evl (evLabel A e a)} st
      | evR _ Rst with Rep-ev-elim tm P k S Rst
  ...   | evRun Sst nP
        with SSimF.on-ev (Sbisim.bwd xqs)
               (Par-soloR ∅ES tm Q S (λ ()) Sst (no-offer ooQ (Disj-sym dQS) (OffersOnly.now ooS Sst)))
  ...     | _ , Xst , zx′ =
            _ , Rep-evRun-intro tm P k X Xst nP
              , frame-gen⁻¹ rd ooQ (OffersOnly.step ooS Sst) dQS fQ fS (sbisim-sym zx′)
  unframe-ev {P = P} {k = k} {Q = Q} {S = S} {X = X} rd ooQ ooS dQS fQ fS xqs
             {l = evl (evLabel A e a)} st
      | evR _ Rst | evFresh Pst _ =
        _ , Rep-evFresh-intro tm P k X Pst
              (no-offer (OffersOnly-∼ xqs (OffersOnly-⦀∪ ooQ ooS))
                        (Disj-∪ (Disj-sym (fQ k ≤-refl)) (Disj-sym (fS k ≤-refl)))
                        (OffersOnly.now (RepDisj.conf rd k) Pst))
          , frame-gen⁻¹ rd ooQ (OffersOnly-⦀∪ ooS ooP′) (Disj-∪ dQS (fQ k ≤-refl))
                        (fresh-suc fQ) (fresh-absorb rd fS)
                        (sbisim-trans (cong-⦀-∼ xqs (sbisim-refl _))
                                      (⦀-assoc-∼-disj ooQ ooS ooP′ dQS (fQ k ≤-refl) (fS k ≤-refl)))
    where -- the spawned copy's residual stays confined to its own alphabet α k
          ooP′ = OffersOnly.step (RepDisj.conf rd k) Pst
  unframe-ev {P = P} {k = k} {Q = Q} {S = S} {X = X} rd ooQ ooS dQS fQ fS xqs
             {l = evl (evLabel A e a)} st
      | evR _ Rst | repEvBoth Sst Pst =
        ⊥-elim (fS k ≤-refl _ _ (OffersOnly.now ooS Sst) (OffersOnly.now (RepDisj.conf rd k) Pst))
  unframe-ev {P = P} {k = k} {Q = Q} {S = S} {X = X} rd ooQ ooS dQS fQ fS xqs
             {l = evl (evLabel A e a)} st
      | evBoth _ Qst Rst with Rep-ev-elim tm P k S Rst
  ...   | evRun Sst _     = ⊥-elim (dQS _ _ (OffersOnly.now ooQ Qst) (OffersOnly.now ooS Sst))
  ...   | evFresh Pst _   =
          ⊥-elim (fQ k ≤-refl _ _ (OffersOnly.now ooQ Qst) (OffersOnly.now (RepDisj.conf rd k) Pst))
  ...   | repEvBoth Sst _ = ⊥-elim (dQS _ _ (OffersOnly.now ooQ Qst) (OffersOnly.now ooS Sst))

  unframe-tau {P = P} {k = k} {Q = Q} {S = S} {X = X} rd ooQ ooS dQS fQ fS xqs st
    with Par-τ-elim ∅ES tm Q (Rep⦀ P k S) st
  ... | τL _ Qst refl with SSimF.on-tau (Sbisim.bwd xqs) (Par-τ-L ∅ES tm Q S Qst)
  ...   | _ , Xst , zx′ =
          _ , Rep-τRun-intro tm P k X Xst
            , frame-gen⁻¹ rd (OffersOnly.step ooQ Qst) ooS dQS fQ fS (sbisim-sym zx′)
  unframe-tau {P = P} {k = k} {Q = Q} {S = S} {X = X} rd ooQ ooS dQS fQ fS xqs st
      | τR _ Rst refl with Rep-τ-elim tm P k S Rst
  ...   | τRun Sst with SSimF.on-tau (Sbisim.bwd xqs) (Par-τ-R ∅ES tm Q S Sst)
  ...     | _ , Xst , zx′ =
            _ , Rep-τRun-intro tm P k X Xst
              , frame-gen⁻¹ rd ooQ (OffersOnly.step ooS Sst) dQS fQ fS (sbisim-sym zx′)
  unframe-tau {P = P} {k = k} {Q = Q} {S = S} {X = X} rd ooQ ooS dQS fQ fS xqs st
      | τR _ Rst refl | τFresh Pst =
        _ , Rep-τFresh-intro tm P k X Pst
          , frame-gen⁻¹ rd ooQ (OffersOnly-⦀∪ ooS ooP′) (Disj-∪ dQS (fQ k ≤-refl))
                        (fresh-suc fQ) (fresh-absorb rd fS)
                        (sbisim-trans (cong-⦀-∼ xqs (sbisim-refl _))
                                      (⦀-assoc-∼-disj ooQ ooS ooP′ dQS (fQ k ≤-refl) (fS k ≤-refl)))
    where -- the spawned copy's residual stays confined to its own alphabet α k
          ooP′ = OffersOnly.step (RepDisj.conf rd k) Pst

  frame-gen rd ooQ ooS dQS fQ fS xqs .Sbisim.fwd .SSimF.on-ev  = frame-ev    rd ooQ ooS dQS fQ fS xqs
  frame-gen rd ooQ ooS dQS fQ fS xqs .Sbisim.fwd .SSimF.on-tau = frame-tau   rd ooQ ooS dQS fQ fS xqs
  frame-gen rd ooQ ooS dQS fQ fS xqs .Sbisim.bwd .SSimF.on-ev  = unframe-ev  rd ooQ ooS dQS fQ fS xqs
  frame-gen rd ooQ ooS dQS fQ fS xqs .Sbisim.bwd .SSimF.on-tau = unframe-tau rd ooQ ooS dQS fQ fS xqs

  frame-gen⁻¹ rd ooQ ooS dQS fQ fS xqs .Sbisim.fwd = frame-gen rd ooQ ooS dQS fQ fS xqs .Sbisim.bwd
  frame-gen⁻¹ rd ooQ ooS dQS fQ fS xqs .Sbisim.bwd = frame-gen rd ooQ ooS dQS fQ fS xqs .Sbisim.fwd

  -----------------------------------------------------------------------------------
  -- The frame law and its corollaries
  -----------------------------------------------------------------------------------

  -- the strong frame law: a disjoint, not-yet-spawned-fresh Q slides out of `Rep⦀`
  Rep-frame-∼ : {α : ℕ → Alpha} {P : ℕ → T} {k : ℕ} {βQ βS : Alpha} {Q S : T}
              → RepDisj α P → OffersOnly βQ Q → OffersOnly βS S → Disj βQ βS
              → FreshFrom α k βQ → FreshFrom α k βS
              → Rep⦀ P k (Q ⦀ S) ∼ (Q ⦀ Rep⦀ P k S)
  Rep-frame-∼ rd ooQ ooS dQS fQ fS = frame-gen rd ooQ ooS dQS fQ fS (sbisim-refl _)

  -- the frame law at divergence-respecting weak bisimulation
  Rep-frame-DR : {α : ℕ → Alpha} {P : ℕ → T} {k : ℕ} {βQ βS : Alpha} {Q S : T}
               → RepDisj α P → OffersOnly βQ Q → OffersOnly βS S → Disj βQ βS
               → FreshFrom α k βQ → FreshFrom α k βS
               → Rep⦀ P k (Q ⦀ S) ≈DR (Q ⦀ Rep⦀ P k S)
  Rep-frame-DR rd ooQ ooS dQS fQ fS = sbisim→drbisim (Rep-frame-∼ rd ooQ ooS dQS fQ fS)

  -- the frame law at failures-divergences equivalence (uses `¬-divergent→normal`)
  Rep-frame-FD : {α : ℕ → Alpha} {P : ℕ → T} {k : ℕ} {βQ βS : Alpha} {Q S : T}
               → RepDisj α P → OffersOnly βQ Q → OffersOnly βS S → Disj βQ βS
               → FreshFrom α k βQ → FreshFrom α k βS
               → Rep⦀ P k (Q ⦀ S) ≈FD (Q ⦀ Rep⦀ P k S)
  Rep-frame-FD rd ooQ ooS dQS fQ fS = drbisim→≈FD (Rep-frame-DR rd ooQ ooS dQS fQ fS)

  -- the S = Stop instance (empty βS): pushes a disjoint sibling into the state,
  -- Q ⦀ Rep⦀ P k Stop ∼ Rep⦀ P k (Q ⦀ Stop); reachable states, of the shape
  -- Rep⦀ P k ((Stop ⦀ P′₀) ⦀ …), are covered by the general `Rep-frame-∼`
  !-frame-∼ : {α : ℕ → Alpha} {P : ℕ → T} {k : ℕ} {βQ : Alpha} {Q : T}
            → RepDisj α P → OffersOnly βQ Q → FreshFrom α k βQ
            → Rep⦀ P k (Q ⦀ Stop) ∼ (Q ⦀ Rep⦀ P k Stop)
  !-frame-∼ rd ooQ fQ =
    Rep-frame-∼ {βS = λ _ _ → ⊥} rd ooQ OffersOnly-Stop (λ _ _ _ ()) fQ (λ _ _ _ _ ())
