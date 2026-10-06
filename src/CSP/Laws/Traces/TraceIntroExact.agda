{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Trace INTRODUCTION with EXACT endpoints, over any alphabet: the lifts a
-- non-vacuity witness needs to assemble a composite's run from its leaf
-- components' runs WITHOUT ever computing a step of the composite.
--   * `GX` — parallel (`ParX`, with an explicit interleaving `PI`), hiding
--     (`HideX`, with an explicit keep/drop list `HT`), interleaving
--     shorthands, single-step lemmas for `Output`/`Prefix`/iteration, and the
--     interrupt (`△X`: a run of the body under a handler that offers none of
--     its events);
--   * `RX` — renaming (`renX`).
-- Hoisted verbatim from Stage C's `Leios/NoLivelock/Live2.agda` (Stage L,
-- L7), plus `△X`.  No Cardano content; no `postulate`, no pragma.
-- Fixed at `E : Set → Set` and `R = ⊤ {0ℓ}` (as in `Live2`), not universe-polymorphic.
------------------------------------------------------------------------

module CSP.Laws.Traces.TraceIntroExact where

open import Level using (0ℓ; Lift; lift)
import Data.Unit as U
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (PTree; ExtI; AnyTypes; react; sil; NodeKind; pair; fin)


-- the parallel, hiding, interrupt and single-step lifts, over the alphabet `E`
module GX {E : Set → Set} (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
  open import CSP.Operators E-≟ using (EventSet; Par⊤; _⦀_; _∖_; ∅ES; Prefix; Output; Output-cont; iter-bind; iterV; iterT; viewV; viewT; _>>=_; _△_; △-merge; △-τ)
  open import CSP.Laws.Traces.TraceLawsThrowInterrupt E-≟ using (force-△-mt)
  open import CSP.Laws.Traces.TraceLawsExtChoice E-≟ using (NonRet)
  open EventSet
  open import Semantics.LTS {E = E} {I = ExtI E}
  open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
  open import CSP.Laws.Traces.TraceLaws E-≟ using (Prefix-cont-just)
  open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Par-sync; Par-τ-L; Par-τ-R)
  open import CSP.Laws.Traces.TraceLawsParallelMono E-≟ using (Par-soloL-reach; Par-soloR-reach)
  open import CSP.Laws.Traces.TraceLawsHide E-≟ using (Hide-τ; Hide-keep; Hide-hidden)
  open import CSP.Laws.Traces.TraceLawsBind E-≟ using (bind-ev)

  -- the process type of every component
  Pr : Set₁
  Pr = PTree E (ExtI E) (⊤ {0ℓ})

  -- the trace type of every component
  Tr : Set₁
  Tr = List (Event√ (⊤ {0ℓ}))

  -- an `A`-synchronised interleaving of two √-free traces (`ParInter` without its `√` case)
  data PI (A : EventSet) : Tr → Tr → Tr → Set₁ where
    pn : PI A [] [] []
    sy : ∀ {X} {e : E X} {a : X} {sP sQ s} → A .mem (X , e) a → PI A sP sQ s
       → PI A (evl (evLabel X e a) ∷ sP) (evl (evLabel X e a) ∷ sQ) (evl (evLabel X e a) ∷ s)
    lf : ∀ {X} {e : E X} {a : X} {sP sQ s} → ¬ A .mem (X , e) a → PI A sP sQ s
       → PI A (evl (evLabel X e a) ∷ sP) sQ (evl (evLabel X e a) ∷ s)
    rt : ∀ {X} {e : E X} {a : X} {sP sQ s} → ¬ A .mem (X , e) a → PI A sP sQ s
       → PI A sP (evl (evLabel X e a) ∷ sQ) (evl (evLabel X e a) ∷ s)

  -- `Par-trace-intro` with the EXACT endpoint: the two components' own endpoints
  ParX : (A : EventSet) {P P′ Q Q′ : Pr} {sP sQ s : Tr}
       → P ⟹⟨ sP ⟩ P′ → Q ⟹⟨ sQ ⟩ Q′ → PI A sP sQ s → Par⊤ A P Q ⟹⟨ s ⟩ Par⊤ A P′ Q′
  ParX A {P} {Q = Q} (⟹-τ st r) q i = ⟹-τ (Par-τ-L A (λ _ _ → tt) P Q st) (ParX A r q i)
  ParX A {P} {Q = Q} p (⟹-τ st r) i = ⟹-τ (Par-τ-R A (λ _ _ → tt) P Q st) (ParX A p r i)
  ParX A ⟹-refl ⟹-refl pn = ⟹-refl
  ParX A {P} {Q = Q} (⟹-ev sp r) (⟹-ev sq r′) (sy m i) =
    ⟹-ev (Par-sync A (λ _ _ → tt) P Q m sp sq) (ParX A r r′ i)
  ParX A {P} {Q = Q} (⟹-ev sp r) q (lf n i) = Par-soloL-reach A (λ _ _ → tt) P Q n sp (ParX A r q i)
  ParX A {P} {Q = Q} p (⟹-ev sq r) (rt n i) = Par-soloR-reach A (λ _ _ → tt) P Q n sq (ParX A p r i)

  -- which events of a √-free trace an `A`-hiding keeps
  data HT (A : EventSet) : Tr → Tr → Set₁ where
    hn : HT A [] []
    kp : ∀ {X} {e : E X} {a : X} {s′ s} → ¬ A .mem (X , e) a → HT A s′ s
       → HT A (evl (evLabel X e a) ∷ s′) (evl (evLabel X e a) ∷ s)
    dp : ∀ {X} {e : E X} {a : X} {s′ s} → A .mem (X , e) a → HT A s′ s
       → HT A (evl (evLabel X e a) ∷ s′) s

  -- `Hide-trace-intro` with the EXACT endpoint
  HideX : (A : EventSet) {P P′ : Pr} {s′ s : Tr} → P ⟹⟨ s′ ⟩ P′ → HT A s′ s → (P ∖ A) ⟹⟨ s ⟩ (P′ ∖ A)
  HideX A (⟹-τ st r)  h        = ⟹-τ (Hide-τ A _ st) (HideX A r h)
  HideX A ⟹-refl      hn       = ⟹-refl
  HideX A (⟹-ev st r) (kp n h) = ⟹-ev (Hide-keep A _ n st) (HideX A r h)
  HideX A (⟹-ev st r) (dp m h) = ⟹-τ (Hide-hidden A _ m st) (HideX A r h)

  -- a trace of visible events only
  NoTick : Tr → Set
  NoTick []          = U.⊤
  NoTick (evl _ ∷ s) = NoTick s
  NoTick (√ _ ∷ _)   = ⊥

  -- an interleaving with every event on the left
  allL : ∀ s → NoTick s → PI ∅ES s [] s
  allL []                        _  = pn
  allL (evl (evLabel _ _ _) ∷ s) nt = lf (λ ()) (allL s nt)
  allL (√ _ ∷ _)                 ()

  -- an interleaving with every event on the right
  allR : ∀ s → NoTick s → PI ∅ES [] s s
  allR []                        _  = pn
  allR (evl (evLabel _ _ _) ∷ s) nt = rt (λ ()) (allR s nt)
  allR (√ _ ∷ _)                 ()

  -- the left trace, then the right one
  allLR : ∀ s₁ s₂ → NoTick s₁ → NoTick s₂ → PI ∅ES s₁ s₂ (s₁ ++ s₂)
  allLR []                         s₂ _  n₂ = allR s₂ n₂
  allLR (evl (evLabel _ _ _) ∷ s₁) s₂ n₁ n₂ = lf (λ ()) (allLR s₁ s₂ n₁ n₂)
  allLR (√ _ ∷ _)                  _  () _

  -- the left operand of an interleaving moves alone
  ⦀L : {P P′ Q : Pr} {s : Tr} → P ⟹⟨ s ⟩ P′ → NoTick s → (P ⦀ Q) ⟹⟨ s ⟩ (P′ ⦀ Q)
  ⦀L t n = ParX ∅ES t ⟹-refl (allL _ n)

  -- the right operand of an interleaving moves alone
  ⦀R : {P Q Q′ : Pr} {s : Tr} → Q ⟹⟨ s ⟩ Q′ → NoTick s → (P ⦀ Q) ⟹⟨ s ⟩ (P ⦀ Q′)
  ⦀R t n = ParX ∅ES ⟹-refl t (allR _ n)

  -- the left operand's run, then the right one's
  ⦀LR : {P P′ Q Q′ : Pr} {s₁ s₂ : Tr} → P ⟹⟨ s₁ ⟩ P′ → Q ⟹⟨ s₂ ⟩ Q′ → NoTick s₁ → NoTick s₂
      → (P ⦀ Q) ⟹⟨ s₁ ++ s₂ ⟩ (P′ ⦀ Q′)
  ⦀LR t u n₁ n₂ = ParX ∅ES t u (allLR _ _ n₁ n₂)

  -- an `Output`'s menu answers its own event and value (no decision computed on a variable)
  out-just : ∀ {ℓr} {A : Set} {R : Set ℓr} ⦃ _ : DecEq A ⦄ (e : E A) (v : A) (P : PTree E (ExtI E) R)
           → Output-cont e v P (A , e) v ≡ just P
  out-just {A = A} e v P with E-≟ (A , e) (A , e)
  ... | no ¬p = ⊥-elim (¬p refl)
  ... | yes refl with v ≟ v
  ...   | yes _ = refl
  ...   | no ¬p = ⊥-elim (¬p refl)

  -- an `Output` fires its own event
  outS : ∀ {ℓr} {A : Set} {R : Set ℓr} ⦃ _ : DecEq A ⦄ (e : E A) (v : A) (P : PTree E (ExtI E) R)
       → Output e v P ─[ ev (evl (evLabel A e v)) ]─► P
  outS e v P = sVis refl (out-just e v P)

  -- a `Prefix` fires on any value
  preS : ∀ {ℓr} {A : Set} {R : Set ℓr} (e : E A) (P : A → PTree E (ExtI E) R) (x : A)
       → Prefix e P ─[ ev (evl (evLabel A e x)) ]─► P x
  preS e P x = sVis refl (Prefix-cont-just e P x)

  -- the iteration reacts as its current round does
  ibR : ∀ {A : Set} (t : PTree E (ExtI E) (A ⊎ ⊤ {0ℓ})) (k : A → PTree E (ExtI E) (A ⊎ ⊤ {0ℓ})) {v τc}
      → PTree.force t ≡ react v τc → PTree.force (iter-bind t k) ≡ react (iterV k (react v τc)) (iterT k (react v τc))
  ibR t k eq with PTree.force t | eq
  ... | react _ _ | refl = refl

  -- the iteration's offers follow its current round's
  ivJ : ∀ {A : Set} (k : A → PTree E (ExtI E) (A ⊎ ⊤ {0ℓ})) nP {at a t′}
      → viewV nP at a ≡ just t′ → iterV k nP at a ≡ just (iter-bind t′ k)
  ivJ k nP {at} {a} eq with viewV nP at a | eq
  ... | just _ | refl = refl

  -- a step of an iteration's current round is a step of the iteration
  iterEv : ∀ {A : Set} {t t′ : PTree E (ExtI E) (A ⊎ ⊤ {0ℓ})} {k : A → PTree E (ExtI E) (A ⊎ ⊤ {0ℓ})}
             {X : Set} {e : E X} {a : X}
         → t ─[ ev (evl (evLabel X e a)) ]─► t′ → iter-bind t k ─[ ev (evl (evLabel X e a)) ]─► iter-bind t′ k
  iterEv {t = t} {k = k} (sVis {v = v} {τc = τc} eq br) =
    sVis (ibR t k eq) (ivJ k (react v τc) br)

  -- a step of a loop's round body is a step of the loop (through the round's bind and the iteration)
  rndEv : ∀ {A : Set} {P P′ : PTree E (ExtI E) A} {f k : A → PTree E (ExtI E) (A ⊎ ⊤ {0ℓ})}
            {X : Set} {e : E X} {a : X}
        → P ─[ ev (evl (evLabel X e a)) ]─► P′
        → iter-bind (P >>= f) k ─[ ev (evl (evLabel X e a)) ]─► iter-bind (P′ >>= f) k
  rndEv {f = f} st = iterEv (bind-ev f _ st)

  -- the interrupt's handler offers none of a run's events
  data NQ (Q : Pr) : Tr → Set₁ where
    nq[] : NQ Q []
    nq∷  : ∀ {X} {e : E X} {a : X} {s} → viewV (PTree.force Q) (X , e) a ≡ nothing → NQ Q s
         → NQ Q (evl (evLabel X e a) ∷ s)

  -- the interrupt's tag-0 τ branch is the body's τ
  △τ0 : ∀ {nP nQ : NodeKind E (ExtI E) (⊤ {0ℓ})} {P Q P′ : Pr} {B : Set} {jj : ExtI E B} {a : B}
      → viewT nP (B , jj) a ≡ just P′ → △-τ nP nQ P Q (_ , pair (fin {n = 2}) jj) (lift fzero , a) ≡ just (P′ △ Q)
  △τ0 {nP} {B = B} {jj} {a} v with viewT nP (B , jj) a | v
  ... | just _ | refl = refl

  -- the body's τ, under a live handler
  △τL : {P P′ Q : Pr} → NonRet (PTree.force Q) → P ─[ τ ]─► P′ → (P △ Q) ─[ τ ]─► (P′ △ Q)
  △τL {P} {P′} {Q} nq (sSil eqP) =
    sTau {i = (Lift 0ℓ (Fin 2) × Lift 0ℓ (Fin 1)) , pair (fin {n = 2}) (fin {n = 1})} {a = lift fzero , lift fzero}
         (force-△-mt {P = P} {Q = Q} eqP refl U.tt nq) (△τ0 {nP = sil P′} {PTree.force Q} {P} {Q} {jj = fin {n = 1}} {a = lift fzero} refl)
  △τL {P} {Q = Q} nq (sTau {v = v} {τc = τc} {i = _ , jj} {a = a} eqP brP) =
    sTau {i = _ , pair (fin {n = 2}) jj} {a = lift fzero , a} (force-△-mt {P = P} {Q = Q} eqP refl U.tt nq) (△τ0 {nP = react v τc} {PTree.force Q} {P} {Q} brP)

  -- the body's visible step, under a live handler that does not offer it
  △evL : {P P₁ Q : Pr} {X : Set} {e : E X} {a : X} → NonRet (PTree.force Q)
       → P ─[ ev (evl (evLabel X e a)) ]─► P₁ → viewV (PTree.force Q) (X , e) a ≡ nothing
       → (P △ Q) ─[ ev (evl (evLabel X e a)) ]─► (P₁ △ Q)
  △evL {P} {P₁} {Q} {X} {e} {a} nq (sVis {v = v} {τc = τc} eqP br) vq =
    sVis (force-△-mt {P = P} {Q = Q} eqP refl U.tt nq) mg
    where
      -- only the body offers the event
      mg : △-merge (react v τc) (PTree.force Q) Q (X , e) a ≡ just (P₁ △ Q)
      mg with v (X , e) a | viewV (PTree.force Q) (X , e) a
      ... | just _  | nothing = case br of λ { refl → refl }
      ... | just _  | just _  = case vq of λ ()
      ... | nothing | _       = case br of λ ()

  -- a run of the body is a run of the interrupt, the handler still armed (EXACT endpoint)
  △X : {P P′ Q : Pr} {s : Tr} → NonRet (PTree.force Q) → P ⟹⟨ s ⟩ P′ → NQ Q s → (P △ Q) ⟹⟨ s ⟩ (P′ △ Q)
  △X nq ⟹-refl      nq[]        = ⟹-refl
  △X nq (⟹-τ st r) h           = ⟹-τ (△τL nq st) (△X nq r h)
  △X nq (⟹-ev st r) (nq∷ vq h) = ⟹-ev (△evL nq st vq) (△X nq r h)

-- renaming lifts with EXACT endpoints
module RX {E₁ E₂ : Set → Set} (ι : ∀ {A} → E₁ A → E₂ A) (ι⁻¹ : ∀ {A} → E₂ A → Maybe (E₁ A))
          (ι-linv : ∀ {A} (e : E₁ A) → ι⁻¹ (ι e) ≡ just e) where
  open import CSP.Rename {E₁ = E₁} {E₂ = E₂} ι ι⁻¹ ι-linv using (renameMap; ι-vis-inv)
  open import CSP.Laws.Traces.RenameDeadlock {E₁ = E₁} {E₂ = E₂} ι ι⁻¹ ι-linv using (ren-ev-fwd; ren-τ-fwd; ι-vis-inv-fwd)
  import Semantics.LTS {E = E₁} {I = ExtI E₁} as L1
  import Semantics.LTS {E = E₂} {I = ExtI E₂} as L2
  import Semantics.Failures {E = E₁} {I = ExtI E₁} as F1
  import Semantics.Failures {E = E₂} {I = ExtI E₂} as F2

  -- a source trace, relabelled by `ι`
  rmap : List (L1.Event√ (⊤ {0ℓ})) → List (L2.Event√ (⊤ {0ℓ}))
  rmap []                             = []
  rmap (L1.evl (L1.evLabel A e a) ∷ s) = L2.evl (L2.evLabel A (ι e) a) ∷ rmap s
  rmap (L1.√ r ∷ s)                    = L2.√ r ∷ rmap s

  -- a source trace of visible events only
  NoTick₁ : List (L1.Event√ (⊤ {0ℓ})) → Set
  NoTick₁ []             = U.⊤
  NoTick₁ (L1.evl _ ∷ s) = NoTick₁ s
  NoTick₁ (L1.√ _ ∷ _)   = ⊥

  -- a source run is a run of the renamed process, relabelled, with the EXACT endpoint
  renX : {P P′ : PTree E₁ (ExtI E₁) (⊤ {0ℓ})} {s : List (L1.Event√ (⊤ {0ℓ}))}
       → P F1.⟹⟨ s ⟩ P′ → NoTick₁ s → renameMap P F2.⟹⟨ rmap s ⟩ renameMap P′
  renX F1.⟹-refl      _ = F2.⟹-refl
  renX (F1.⟹-τ st r) n = F2.⟹-τ (ren-τ-fwd {inv = ι-vis-inv} st) (renX r n)
  renX {s = L1.evl (L1.evLabel A e a) ∷ _} (F1.⟹-ev st r) n =
    F2.⟹-ev (ren-ev-fwd {inv = ι-vis-inv} {at = A , e} {a = a} {bt = A , ι e} {b = a} st (ι-vis-inv-fwd e a))
            (renX r n)
  renX {s = L1.√ _ ∷ _} (F1.⟹-ev st r) ()
