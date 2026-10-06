{-# OPTIONS --guardedness #-}

-- Left and right interleaving folds agree on √-free traces, at any result type R and any
-- merge function.  `foldL Y [c₀ , c₁ , …]` is `((Y ∥ c₀) ∥ c₁) …` (the shape of a `Rep` state
-- and of its approximant); `foldR [c₀ , c₁ , …] Z` is `c₀ ∥ (c₁ ∥ (… ∥ Z))` (the shape of
-- `ilv`).  Here `∥` is `Par ∅ES merge`.
--
-- Every result is stated on √-free traces (`All IsEvl s`).  On such traces the joint-√ case
-- `p√` of `ParInter` never fires, so the merge function is irrelevant (`remerge`).  That is
-- what lets commutativity (whose `ParInter-sym` flips the merge) and associativity (whose
-- `ParInter-assoc-LR/RL` needs an associative merge) hold here with NO hypothesis on
-- `merge`: we re-associate at the associative merge `λ a _ → a` and re-merge back.
--
-- Reused, not copied: `Par-trace-elim`, `Par-trace-intro`, `ParInter-sym`,
-- `ParInter-assoc-LR/RL`, `Stop-traces-empty`, and `IsEvl` (CSP.Laws.Traces.ReplicationApprox;
-- it is already generic in R).  Postulates: none used, none in closure (22 local modules,
-- grep-audited 2026-10-01).
--
-- For the replicated-sessions bridge (Security/ComposeRep, plan Task 5):
--   * `ilv`'s base is `pool P n`, which is `Stop` by definition (Security/Compose.agda:450),
--     so `ilv P live n ≡ foldR (map … live) Stop` needs a small induction on `live`, not
--     one `refl`.
--   * Listing the Alice copies before the Bob copies (`aliceCopies ++ bobCopies`) matches
--     `foldR-split` directly and avoids the permutation step; `foldR-perm` is here if
--     position order is wanted instead.

open import Level using (Level)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_) renaming (refl to ↭-refl; prep to ↭-prep; swap to ↭-swap; trans to ↭-trans)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

open import Process_Trees

module CSP.Laws.Traces.InterleaveFold {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  {ℓr} {R : Set ℓr} (merge : R → R → R) where

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS {E = E} {I = ExtI E}
open import Semantics.Failures {E = E} {I = ExtI E} using (traces)
open import CSP.Laws.Traces.TraceLaws E-≟ using (Stop-traces-empty)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟
  using (ParInter; pnil; psync; psoloL; psoloR; p√; Par-trace-elim)
open import CSP.Laws.Traces.TraceLawsParallelMono E-≟ using (Par-trace-intro)
open import CSP.Laws.Traces.TraceLawsParallelComm E-≟ using (ParInter-sym)
open import CSP.Laws.Traces.TraceLawsParallelInterAssoc E-≟
  using (ParInter-assoc-LR; ParInter-assoc-RL)
open import CSP.Laws.Traces.ReplicationApprox E-≟ using (IsEvl; isEvl)

private
  -- the process type of this module
  PT : Set _
  PT = PTree E (ExtI E) R

  -- the interleaving folded over
  _∥_ : PT → PT → PT
  P ∥ Q = Par ∅ES merge P Q

  -- an associative merge (definitionally), used only to re-associate √-free interleavings
  fst : R → R → R
  fst a _ = a

  -- implicit names for sync sets, merges and traces in the lemma signatures
  variable
    A : EventSet
    m m′ : R → R → R
    sP sQ s : List (Event√ R)

-- the √-free traces of P are traces of Q
_⊆ᵉ_ : PT → PT → Set _
P ⊆ᵉ Q = ∀ {s} → traces P s → All IsEvl s → traces Q s

-------------------------------------------------------------------------------------
-- √-free interleavings
-------------------------------------------------------------------------------------

-- on a √-free interleaving the merge function is irrelevant
remerge : ParInter A m sP sQ s → All IsEvl s → ParInter A m′ sP sQ s
remerge pnil         _       = pnil
remerge (psync c i)  (_ ∷ e) = psync c (remerge i e)
remerge (psoloL c i) (_ ∷ e) = psoloL c (remerge i e)
remerge (psoloR c i) (_ ∷ e) = psoloR c (remerge i e)
remerge p√           (() ∷ _)

-- both components of a √-free interleaving are √-free
inter-evl : ParInter A m sP sQ s → All IsEvl s → All IsEvl sP × All IsEvl sQ
inter-evl pnil         _       = [] , []
inter-evl (psync c i)  (x ∷ e) = let (l , r) = inter-evl i e in x ∷ l , x ∷ r
inter-evl (psoloL c i) (x ∷ e) = let (l , r) = inter-evl i e in x ∷ l , r
inter-evl (psoloR c i) (x ∷ e) = let (l , r) = inter-evl i e in l , x ∷ r
inter-evl p√           (() ∷ _)

-- an interleaving of two √-free components is √-free
inter-evl⁻ : ParInter A m sP sQ s → All IsEvl sP → All IsEvl sQ → All IsEvl s
inter-evl⁻ pnil         _       _       = []
inter-evl⁻ (psync c i)  (x ∷ l) (_ ∷ r) = x ∷ inter-evl⁻ i l r
inter-evl⁻ (psoloL c i) (x ∷ l) r       = x ∷ inter-evl⁻ i l r
inter-evl⁻ (psoloR c i) l       (x ∷ r) = x ∷ inter-evl⁻ i l r
inter-evl⁻ p√           (() ∷ _) _

-- an interleaving whose left component is empty is its right component
inter-[]L : ParInter ∅ES m [] sQ s → sQ ≡ s
inter-[]L pnil         = refl
inter-[]L (psoloR c i) = cong (_ ∷_) (inter-[]L i)

-------------------------------------------------------------------------------------
-- the interleaving algebra on √-free traces
-------------------------------------------------------------------------------------

-- an idle `Stop` on the left contributes nothing
Stop-∥ : (Q : PT) → (Stop ∥ Q) ⊆ᵉ Q
Stop-∥ Q (_ , bs) _ with Par-trace-elim ∅ES merge Stop Q bs
... | sP , sQ , _ , _ , rP , rQ , i with Stop-traces-empty (_ , rP)
... | refl = subst (traces Q) (inter-[]L i) (_ , rQ)

-- interleaving commutes
∥-comm : (P Q : PT) → (P ∥ Q) ⊆ᵉ (Q ∥ P)
∥-comm P Q (_ , bs) e with Par-trace-elim ∅ES merge P Q bs
... | _ , _ , _ , _ , rP , rQ , i =
  Par-trace-intro ∅ES merge Q P rQ rP (remerge (ParInter-sym ∅ES merge i) e)

-- interleaving re-associates to the right
∥-assocLR : (P Q Z : PT) → ((P ∥ Q) ∥ Z) ⊆ᵉ (P ∥ (Q ∥ Z))
∥-assocLR P Q Z (_ , bs) e with Par-trace-elim ∅ES merge (P ∥ Q) Z bs
... | _ , _ , _ , _ , rPQ , rZ , o with Par-trace-elim ∅ES merge P Q rPQ
... | _ , _ , _ , _ , rP , rQ , i
  with ParInter-assoc-LR ∅ES fst (λ _ _ _ → refl)
         (remerge i (proj₁ (inter-evl o e))) (remerge o e)
... | _ , jZ , jP =
  Par-trace-intro ∅ES merge P (Q ∥ Z) rP
    (proj₂ (Par-trace-intro ∅ES merge Q Z rQ rZ (remerge jZ (proj₂ (inter-evl jP e)))))
    (remerge jP e)

-- interleaving re-associates to the left
∥-assocRL : (P Q Z : PT) → (P ∥ (Q ∥ Z)) ⊆ᵉ ((P ∥ Q) ∥ Z)
∥-assocRL P Q Z (_ , bs) e with Par-trace-elim ∅ES merge P (Q ∥ Z) bs
... | _ , _ , _ , _ , rP , rQZ , o with Par-trace-elim ∅ES merge Q Z rQZ
... | _ , _ , _ , _ , rQ , rZ , i
  with ParInter-assoc-RL ∅ES fst (λ _ _ _ → refl)
         (remerge i (proj₂ (inter-evl o e))) (remerge o e)
... | _ , jP , jZ =
  Par-trace-intro ∅ES merge (P ∥ Q) Z
    (proj₂ (Par-trace-intro ∅ES merge P Q rP rQ (remerge jP (proj₁ (inter-evl jZ e)))))
    rZ (remerge jZ e)

-- interleaving is monotone in its left operand
∥-monoL : {P P′ : PT} (Q : PT) → P ⊆ᵉ P′ → (P ∥ Q) ⊆ᵉ (P′ ∥ Q)
∥-monoL {P} Q h (_ , bs) e with Par-trace-elim ∅ES merge P Q bs
... | _ , _ , _ , _ , rP , rQ , i with h (_ , rP) (proj₁ (inter-evl i e))
... | _ , rP′ = Par-trace-intro ∅ES merge _ Q rP′ rQ i

-- interleaving is monotone in its right operand
∥-monoR : (P : PT) {Q Q′ : PT} → Q ⊆ᵉ Q′ → (P ∥ Q) ⊆ᵉ (P ∥ Q′)
∥-monoR P {Q} h (_ , bs) e with Par-trace-elim ∅ES merge P Q bs
... | _ , _ , _ , _ , rP , rQ , i with h (_ , rQ) (proj₂ (inter-evl i e))
... | _ , rQ′ = Par-trace-intro ∅ES merge P _ rP rQ′ i

-- the two leading operands of a right-nested interleaving swap
∥-swap : (P Q Z : PT) → (P ∥ (Q ∥ Z)) ⊆ᵉ (Q ∥ (P ∥ Z))
∥-swap P Q Z t e =
  ∥-assocLR Q P Z (∥-monoL Z (∥-comm P Q) (∥-assocRL P Q Z t e) e) e

-------------------------------------------------------------------------------------
-- folds
-------------------------------------------------------------------------------------

-- left fold: `foldL Y [c₀ , c₁ , …] = ((Y ∥ c₀) ∥ c₁) …`, the shape of a `Rep` state
foldL : PT → List PT → PT
foldL Y []       = Y
foldL Y (c ∷ cs) = foldL (Par ∅ES merge Y c) cs

-- right fold: `foldR [c₀ , c₁ , …] Z = c₀ ∥ (c₁ ∥ (… ∥ Z))`, the shape of `ilv`
foldR : List PT → PT → PT
foldR []       Z = Z
foldR (c ∷ cs) Z = Par ∅ES merge c (foldR cs Z)

-- a component appended to a right fold's base moves to its front
foldR-pull : (cs : List PT) (Y c : PT) → foldR cs (Y ∥ c) ⊆ᵉ (c ∥ foldR cs Y)
foldR-pull []       Y c = ∥-comm Y c
foldR-pull (d ∷ cs) Y c t e =
  ∥-swap d c (foldR cs Y) (∥-monoR d (foldR-pull cs Y c) t e) e

-- every √-free trace of the left fold is a trace of the right fold over the same components
foldL⊆foldR : (Y : PT) (cs : List PT) → foldL Y cs ⊆ᵉ foldR cs Y
foldL⊆foldR Y []       t e = t
foldL⊆foldR Y (c ∷ cs) t e = foldR-pull cs Y c (foldL⊆foldR (Y ∥ c) cs t e) e

-- interleaving two right folds is the right fold over the appended components
-- (stated over any base Z of the second fold; the `Stop`-based instance is `foldR-split xs ys Stop`)
foldR-split : (xs ys : List PT) (Z : PT)
            → (foldR xs Stop ∥ foldR ys Z) ⊆ᵉ foldR (xs ++ ys) Z
foldR-split []       ys Z t e = Stop-∥ (foldR ys Z) t e
foldR-split (x ∷ xs) ys Z t e =
  ∥-monoR x (foldR-split xs ys Z) (∥-assocLR x (foldR xs Stop) (foldR ys Z) t e) e

-- a right fold's √-free traces are invariant under permuting its components
foldR-perm : {xs ys : List PT} (Z : PT) → xs ↭ ys → foldR xs Z ⊆ᵉ foldR ys Z
foldR-perm Z ↭-refl            t e = t
foldR-perm Z (↭-prep x p)      t e = ∥-monoR x (foldR-perm Z p) t e
foldR-perm Z (↭-swap {xs = xs} x y p) t e =
  ∥-monoR y (∥-monoR x (foldR-perm Z p)) (∥-swap x y (foldR xs Z) t e) e
foldR-perm Z (↭-trans p q)     t e = foldR-perm Z q (foldR-perm Z p t e) e
