{-# OPTIONS --guardedness #-}

-- STRONG associativity of interleaving `⦀` under alphabet disjointness.
--
--   OffersOnly-∼   : P ∼ Q → OffersOnly α Q → OffersOnly α P
--   ⦀-assoc-∼-disj : OffersOnly α P → OffersOnly β Q → OffersOnly γ R₀
--                  → Disj α β → Disj α γ → Disj β γ
--                  → ((P ⦀ Q) ⦀ R₀) ∼ (P ⦀ (Q ⦀ R₀))
--
-- Unconditional `⦀`-associativity holds only at ≈FD (`CSP.Laws.FD.ParallelAssoc`):
-- a same-event collision creates the inline overlap node `(P′∥Q) ⊓ (P∥Q′)`, whose
-- nesting differs between the two bracketings.  With pairwise-disjoint alphabets no
-- two components ever offer the same event, so every `evBoth` case of `Par-ev-elim`
-- is absurd (by `OffersOnly.now`) and each step is the step of exactly ONE component.
-- The relation {((P⦀Q)⦀R₀ , P⦀(Q⦀R₀))} is then closed under steps: inversion by
-- `Par-ev-elim`/`Par-τ-elim` (twice), re-introduction by `Par-soloL/R`/`Par-τ-L/R`
-- (twice), whose idle-operand side condition is discharged by `no-offer`.
--
-- The `ret` cases need no special treatment: the elim/intro lemmas already absorb
-- `Par`'s ret/ret, ret/sil, ret/react force clauses, and a √ step of either side
-- forces all three components to `ret` (`Par-force-ret-inv`), matched by the other
-- side's √ (`fPar-rr` twice).  No `NoRet` premise is needed.
--
-- POSTULATE PROVENANCE.  No postulate is USED here, but FIVE postulate modules sit in
-- this module's closure, all via `CSP.Laws.Bisim.DRCongruenceRep` (imported for `Alpha`,
-- `Disj`, `OffersOnly` and its closure lemmas): `Semantics.DRImpliesFD`,
-- `CSP.Laws.Bisim.DRCongruence` and `CSP.Laws.FD.{ExtChoice,Interrupt,Parallel}Divergence`.

open import Level using (Level)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.Bisim.ParallelAssocDisj {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E}
open import CSP.Laws.Traces.TraceLawsParallel E-≟
  using (Par-τ-L; Par-τ-R; Par-soloL; Par-soloR)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟
  using ( Par-τ-elim; ParτR; τL; τR
        ; Par-ev-elim; ParevR; evSync; evL; evR; evBoth; ev√
        ; Par-force-ret-inv; fPar-rr; viewV-ev )
open import CSP.Laws.Bisim.DRCongruenceRep E-≟
  using (Alpha; Disj; OffersOnly; OffersOnly-mono; OffersOnly-⦀)

private
  variable
    ℓr : Level
    α β γ : Alpha

  -- the symmetric ⊤-merge of `⦀`
  tm : ⊤ {ℓr} → ⊤ {ℓr} → ⊤ {ℓr}
  tm _ _ = tt

-------------------------------------------------------------------------------------
-- Alphabet bookkeeping
-------------------------------------------------------------------------------------

-- pointwise union of two value-level alphabets
_∪α_ : Alpha → Alpha → Alpha
(α ∪α β) at a = α at a ⊎ β at a

-- disjointness is symmetric
Disj-sym : Disj α β → Disj β α
Disj-sym d at a y x = d at a x y

-- an alphabet disjoint from two alphabets is disjoint from their union
Disj-∪ : Disj α β → Disj α γ → Disj α (β ∪α γ)
Disj-∪ d₁ d₂ at a x (inj₁ y) = d₁ at a x y
Disj-∪ d₁ d₂ at a x (inj₂ y) = d₂ at a x y

-- an interleaving of a β-confined and a γ-confined process is (β ∪ γ)-confined
OffersOnly-⦀∪ : {Q R₀ : PTree E (ExtI E) (⊤ {ℓr})}
              → OffersOnly β Q → OffersOnly γ R₀ → OffersOnly (β ∪α γ) (Q ⦀ R₀)
OffersOnly-⦀∪ ooQ ooR =
  OffersOnly-⦀ (OffersOnly-mono (λ _ _ → inj₁) ooQ) (OffersOnly-mono (λ _ _ → inj₂) ooR)

-- a β-confined process does not offer an α-event when α and β are disjoint
no-offer : {Q : PTree E (ExtI E) (⊤ {ℓr})} {X : Set ℓ} {e : E X} {a : X}
         → OffersOnly β Q → Disj α β → α (X , e) a
         → viewV (PTree.force Q) (X , e) a ≡ nothing
no-offer {Q = Q} {X = X} {e = e} {a = a} ooQ d x with viewV (PTree.force Q) (X , e) a in eq
... | nothing = refl
... | just _  = ⊥-elim (d _ _ x (OffersOnly.now ooQ (viewV-ev {P = Q} refl eq)))

-------------------------------------------------------------------------------------
-- Transfer of alphabet confinement along strong bisimulation
-------------------------------------------------------------------------------------

-- alphabet confinement transfers backwards along a strong bisimulation
OffersOnly-∼ : ∀ {ℓr} {R : Set ℓr} {α : Alpha} {P Q : PTree E (ExtI E) R}
             → P ∼ Q → OffersOnly α Q → OffersOnly α P
OffersOnly-∼ b ooQ .OffersOnly.now st with SSimF.on-ev (Sbisim.fwd b) st
... | _ , Qst , _ = OffersOnly.now ooQ Qst
OffersOnly-∼ b ooQ .OffersOnly.step {l = τ} st with SSimF.on-tau (Sbisim.fwd b) st
... | _ , Qst , b′ = OffersOnly-∼ b′ (OffersOnly.step ooQ Qst)
OffersOnly-∼ b ooQ .OffersOnly.step {l = ev _} st with SSimF.on-ev (Sbisim.fwd b) st
... | _ , Qst , b′ = OffersOnly-∼ b′ (OffersOnly.step ooQ Qst)

-------------------------------------------------------------------------------------
-- The strong bisimulation (forward-declared corecursive group)
-------------------------------------------------------------------------------------

-- left-nested interleaving is strongly bisimilar to right-nested, under disjointness
⦀-assoc-∼-disj : {P Q R₀ : PTree E (ExtI E) (⊤ {ℓr})}
               → OffersOnly α P → OffersOnly β Q → OffersOnly γ R₀
               → Disj α β → Disj α γ → Disj β γ
               → ((P ⦀ Q) ⦀ R₀) ∼ (P ⦀ (Q ⦀ R₀))

-- the mirror orientation, needed as the residual relation of the `bwd` transfer
⦀-assoc-∼-disj⁻¹ : {P Q R₀ : PTree E (ExtI E) (⊤ {ℓr})}
                 → OffersOnly α P → OffersOnly β Q → OffersOnly γ R₀
                 → Disj α β → Disj α γ → Disj β γ
                 → (P ⦀ (Q ⦀ R₀)) ∼ ((P ⦀ Q) ⦀ R₀)

-- a visible / √ step of the left-nested side is matched by the right-nested side
assoc-ev : {P Q R₀ : PTree E (ExtI E) (⊤ {ℓr})}
         → OffersOnly α P → OffersOnly β Q → OffersOnly γ R₀
         → Disj α β → Disj α γ → Disj β γ
         → {M : PTree E (ExtI E) (⊤ {ℓr})} {l : Event√ (⊤ {ℓr})}
         → ((P ⦀ Q) ⦀ R₀) ─[ ev l ]─► M
         → Σ[ M′ ∈ PTree E (ExtI E) (⊤ {ℓr}) ] (((P ⦀ (Q ⦀ R₀)) ─[ ev l ]─► M′) × (M ∼ M′))

-- a τ step of the left-nested side is matched by the right-nested side
assoc-tau : {P Q R₀ : PTree E (ExtI E) (⊤ {ℓr})}
          → OffersOnly α P → OffersOnly β Q → OffersOnly γ R₀
          → Disj α β → Disj α γ → Disj β γ
          → {M : PTree E (ExtI E) (⊤ {ℓr})}
          → ((P ⦀ Q) ⦀ R₀) ─[ τ ]─► M
          → Σ[ M′ ∈ PTree E (ExtI E) (⊤ {ℓr}) ] (((P ⦀ (Q ⦀ R₀)) ─[ τ ]─► M′) × (M ∼ M′))

-- a visible / √ step of the right-nested side is matched by the left-nested side
unassoc-ev : {P Q R₀ : PTree E (ExtI E) (⊤ {ℓr})}
           → OffersOnly α P → OffersOnly β Q → OffersOnly γ R₀
           → Disj α β → Disj α γ → Disj β γ
           → {M : PTree E (ExtI E) (⊤ {ℓr})} {l : Event√ (⊤ {ℓr})}
           → (P ⦀ (Q ⦀ R₀)) ─[ ev l ]─► M
           → Σ[ M′ ∈ PTree E (ExtI E) (⊤ {ℓr}) ] ((((P ⦀ Q) ⦀ R₀) ─[ ev l ]─► M′) × (M ∼ M′))

-- a τ step of the right-nested side is matched by the left-nested side
unassoc-tau : {P Q R₀ : PTree E (ExtI E) (⊤ {ℓr})}
            → OffersOnly α P → OffersOnly β Q → OffersOnly γ R₀
            → Disj α β → Disj α γ → Disj β γ
            → {M : PTree E (ExtI E) (⊤ {ℓr})}
            → (P ⦀ (Q ⦀ R₀)) ─[ τ ]─► M
            → Σ[ M′ ∈ PTree E (ExtI E) (⊤ {ℓr}) ] ((((P ⦀ Q) ⦀ R₀) ─[ τ ]─► M′) × (M ∼ M′))

assoc-ev {P = P} {Q = Q} {R₀ = R₀} ooP ooQ ooR dαβ dαγ dβγ st
  with Par-ev-elim ∅ES tm (P ⦀ Q) R₀ st
... | evSync () _ _
... | evL _ PQst with Par-ev-elim ∅ES tm P Q PQst
...   | evSync () _ _
...   | evL _ Pst =
        _ , Par-soloL ∅ES tm P (Q ⦀ R₀) (λ ()) Pst
              (no-offer (OffersOnly-⦀∪ ooQ ooR) (Disj-∪ dαβ dαγ) (OffersOnly.now ooP Pst))
          , ⦀-assoc-∼-disj (OffersOnly.step ooP Pst) ooQ ooR dαβ dαγ dβγ
...   | evR _ Qst =
        _ , Par-soloR ∅ES tm P (Q ⦀ R₀) (λ ())
              (Par-soloL ∅ES tm Q R₀ (λ ()) Qst (no-offer ooR dβγ (OffersOnly.now ooQ Qst)))
              (no-offer ooP (Disj-sym dαβ) (OffersOnly.now ooQ Qst))
          , ⦀-assoc-∼-disj ooP (OffersOnly.step ooQ Qst) ooR dαβ dαγ dβγ
...   | evBoth _ Pst Qst = ⊥-elim (dαβ _ _ (OffersOnly.now ooP Pst) (OffersOnly.now ooQ Qst))
assoc-ev {P = P} {Q = Q} {R₀ = R₀} ooP ooQ ooR dαβ dαγ dβγ st
    | evR _ Rst =
        _ , Par-soloR ∅ES tm P (Q ⦀ R₀) (λ ())
              (Par-soloR ∅ES tm Q R₀ (λ ()) Rst (no-offer ooQ (Disj-sym dβγ) (OffersOnly.now ooR Rst)))
              (no-offer ooP (Disj-sym dαγ) (OffersOnly.now ooR Rst))
          , ⦀-assoc-∼-disj ooP ooQ (OffersOnly.step ooR Rst) dαβ dαγ dβγ
assoc-ev {P = P} {Q = Q} {R₀ = R₀} ooP ooQ ooR dαβ dαγ dβγ st
    | evBoth _ PQst Rst =
        ⊥-elim (Disj-∪ (Disj-sym dαγ) (Disj-sym dβγ) _ _
                  (OffersOnly.now ooR Rst) (OffersOnly.now (OffersOnly-⦀∪ ooP ooQ) PQst))
assoc-ev {P = P} {Q = Q} {R₀ = R₀} ooP ooQ ooR dαβ dαγ dβγ st
    | ev√ fpPQ fpR with Par-force-ret-inv ∅ES tm fpPQ
...   | _ , _ , fpP , fpQ , refl =
        deadlock , sRet (fPar-rr ∅ES tm fpP (fPar-rr ∅ES tm fpQ fpR)) , sbisim-refl deadlock

assoc-tau {P = P} {Q = Q} {R₀ = R₀} ooP ooQ ooR dαβ dαγ dβγ st
  with Par-τ-elim ∅ES tm (P ⦀ Q) R₀ st
... | τL _ PQst refl with Par-τ-elim ∅ES tm P Q PQst
...   | τL _ Pst refl =
        _ , Par-τ-L ∅ES tm P (Q ⦀ R₀) Pst
          , ⦀-assoc-∼-disj (OffersOnly.step ooP Pst) ooQ ooR dαβ dαγ dβγ
...   | τR _ Qst refl =
        _ , Par-τ-R ∅ES tm P (Q ⦀ R₀) (Par-τ-L ∅ES tm Q R₀ Qst)
          , ⦀-assoc-∼-disj ooP (OffersOnly.step ooQ Qst) ooR dαβ dαγ dβγ
assoc-tau {P = P} {Q = Q} {R₀ = R₀} ooP ooQ ooR dαβ dαγ dβγ st
    | τR _ Rst refl =
        _ , Par-τ-R ∅ES tm P (Q ⦀ R₀) (Par-τ-R ∅ES tm Q R₀ Rst)
          , ⦀-assoc-∼-disj ooP ooQ (OffersOnly.step ooR Rst) dαβ dαγ dβγ

unassoc-ev {P = P} {Q = Q} {R₀ = R₀} ooP ooQ ooR dαβ dαγ dβγ st
  with Par-ev-elim ∅ES tm P (Q ⦀ R₀) st
... | evSync () _ _
... | evL _ Pst =
        _ , Par-soloL ∅ES tm (P ⦀ Q) R₀ (λ ())
              (Par-soloL ∅ES tm P Q (λ ()) Pst (no-offer ooQ dαβ (OffersOnly.now ooP Pst)))
              (no-offer ooR dαγ (OffersOnly.now ooP Pst))
          , ⦀-assoc-∼-disj⁻¹ (OffersOnly.step ooP Pst) ooQ ooR dαβ dαγ dβγ
... | evR _ QRst with Par-ev-elim ∅ES tm Q R₀ QRst
...   | evSync () _ _
...   | evL _ Qst =
        _ , Par-soloL ∅ES tm (P ⦀ Q) R₀ (λ ())
              (Par-soloR ∅ES tm P Q (λ ()) Qst (no-offer ooP (Disj-sym dαβ) (OffersOnly.now ooQ Qst)))
              (no-offer ooR dβγ (OffersOnly.now ooQ Qst))
          , ⦀-assoc-∼-disj⁻¹ ooP (OffersOnly.step ooQ Qst) ooR dαβ dαγ dβγ
...   | evR _ Rst =
        _ , Par-soloR ∅ES tm (P ⦀ Q) R₀ (λ ()) Rst
              (no-offer (OffersOnly-⦀∪ ooP ooQ) (Disj-∪ (Disj-sym dαγ) (Disj-sym dβγ))
                 (OffersOnly.now ooR Rst))
          , ⦀-assoc-∼-disj⁻¹ ooP ooQ (OffersOnly.step ooR Rst) dαβ dαγ dβγ
...   | evBoth _ Qst Rst = ⊥-elim (dβγ _ _ (OffersOnly.now ooQ Qst) (OffersOnly.now ooR Rst))
unassoc-ev {P = P} {Q = Q} {R₀ = R₀} ooP ooQ ooR dαβ dαγ dβγ st
    | evBoth _ Pst QRst =
        ⊥-elim (Disj-∪ dαβ dαγ _ _ (OffersOnly.now ooP Pst) (OffersOnly.now (OffersOnly-⦀∪ ooQ ooR) QRst))
unassoc-ev {P = P} {Q = Q} {R₀ = R₀} ooP ooQ ooR dαβ dαγ dβγ st
    | ev√ fpP fpQR with Par-force-ret-inv ∅ES tm fpQR
...   | _ , _ , fpQ , fpR , refl =
        deadlock , sRet (fPar-rr ∅ES tm (fPar-rr ∅ES tm fpP fpQ) fpR) , sbisim-refl deadlock

unassoc-tau {P = P} {Q = Q} {R₀ = R₀} ooP ooQ ooR dαβ dαγ dβγ st
  with Par-τ-elim ∅ES tm P (Q ⦀ R₀) st
... | τL _ Pst refl =
        _ , Par-τ-L ∅ES tm (P ⦀ Q) R₀ (Par-τ-L ∅ES tm P Q Pst)
          , ⦀-assoc-∼-disj⁻¹ (OffersOnly.step ooP Pst) ooQ ooR dαβ dαγ dβγ
... | τR _ QRst refl with Par-τ-elim ∅ES tm Q R₀ QRst
...   | τL _ Qst refl =
        _ , Par-τ-L ∅ES tm (P ⦀ Q) R₀ (Par-τ-R ∅ES tm P Q Qst)
          , ⦀-assoc-∼-disj⁻¹ ooP (OffersOnly.step ooQ Qst) ooR dαβ dαγ dβγ
...   | τR _ Rst refl =
        _ , Par-τ-R ∅ES tm (P ⦀ Q) R₀ Rst
          , ⦀-assoc-∼-disj⁻¹ ooP ooQ (OffersOnly.step ooR Rst) dαβ dαγ dβγ

⦀-assoc-∼-disj ooP ooQ ooR dαβ dαγ dβγ .Sbisim.fwd .SSimF.on-ev  = assoc-ev    ooP ooQ ooR dαβ dαγ dβγ
⦀-assoc-∼-disj ooP ooQ ooR dαβ dαγ dβγ .Sbisim.fwd .SSimF.on-tau = assoc-tau   ooP ooQ ooR dαβ dαγ dβγ
⦀-assoc-∼-disj ooP ooQ ooR dαβ dαγ dβγ .Sbisim.bwd .SSimF.on-ev  = unassoc-ev  ooP ooQ ooR dαβ dαγ dβγ
⦀-assoc-∼-disj ooP ooQ ooR dαβ dαγ dβγ .Sbisim.bwd .SSimF.on-tau = unassoc-tau ooP ooQ ooR dαβ dαγ dβγ

⦀-assoc-∼-disj⁻¹ ooP ooQ ooR dαβ dαγ dβγ .Sbisim.fwd = ⦀-assoc-∼-disj ooP ooQ ooR dαβ dαγ dβγ .Sbisim.bwd
⦀-assoc-∼-disj⁻¹ ooP ooQ ooR dαβ dαγ dβγ .Sbisim.bwd = ⦀-assoc-∼-disj ooP ooQ ooR dαβ dαγ dβγ .Sbisim.fwd
