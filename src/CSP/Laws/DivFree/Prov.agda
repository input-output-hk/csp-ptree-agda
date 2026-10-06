{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- VALUE PROVENANCE over traces (Leios no-livelock, Stage C, owner
-- decision D1-b).  Generic: no Leios/Cardano content.
--   * `Prov O Kp In K ls` — every value an O-label of `ls` carries is a
--     RELIED INPUT of that very label (`In`), or was carried by an EARLIER
--     Kp-label of `ls` (or lies in the initial knowledge `K`)
--   * `Prov-par`   — composition through `Par` by trace projection: a
--     synchronised event is justified by whichever side guarantees it, so
--     a rely of one side is discharged by its partner's guarantee
--   * `Prov-close` — closing a chain: when every known-maker is itself an
--     obligation, every O-value traces back to an earlier INPUT
--   * `Prov-hide`  — hiding events that make nothing known
--   * `ProvT`, `ProvT-*`, `provIter`, `provInv` — the per-round calculus and
--     the iteration lemmas (round-local; with a state invariant)
--   * `Prov→All`   — the non-temporal read-out used by the store bounds
-- No postulate, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as UP
open UP using () renaming (⊤ to ⊤′)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Properties using (++-identityʳ)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe)
open import Function using (case_of_; id)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Laws.DivFree.Prov {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import CSP.Laws.Traces.TraceLawsBind E-≟ using (bs-live; bs-term; bind-elim-aux; ⟹-append-√)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟ using (□-trace-elim)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟ using (ParInter; pnil; psync; psoloL; psoloR; p√; Par-trace-elim)
open import CSP.Laws.Traces.TraceLawsHide E-≟ using (HideTr; hnil; hkeep; hdrop; h√; Hide-trace-elim)
open import CSP.Laws.DivFree.Count E-≟
  using (labels; labels-++; labels-EvlOnly; Ret-tr; pfx-tr; out-tr; AllL; []; _∷_;
         Rounds; rLive; rBack; rDone; rounds; Post; post; run)

-- the event set holds the label
InA : EventSet → Event → Set
InA A (evLabel B e a) = EventSet.mem A (B , e) a

module _ {V : Set} where

  ------------------------------------------------------------------------
  -- §1. The carrier
  ------------------------------------------------------------------------

  -- some label of the list carries `x` as a Kp-value
  Kn : (Event → V → Set) → List Event → V → Set
  Kn Kp []       x = ⊥
  Kn Kp (e ∷ ls) x = Kp e x ⊎ Kn Kp ls x

  -- PROVENANCE: every O-value of every label is an input of that label or already known;
  -- each label then makes its Kp-values known
  Prov : (O Kp In : Event → V → Set) → (V → Set) → List Event → Set
  Prov O Kp In K []       = ⊤
  Prov O Kp In K (e ∷ ls) = (∀ {x} → O e x → In e x ⊎ K x) × Prov O Kp In (λ x → K x ⊎ Kp e x) ls

  -- weakening: fewer obligations, more inputs, more known-makers, more initial knowledge
  Prov-weak : ∀ {O O′ Kp Kp′ In In′ K K′} ls
            → (∀ {e x} → O′ e x → O e x) → (∀ {e x} → In e x → In′ e x) → (∀ {e x} → Kp e x → Kp′ e x)
            → (∀ {x} → K x → K′ x) → Prov O Kp In K ls → Prov O′ Kp′ In′ K′ ls
  Prov-weak []       o i k f _       = tt
  Prov-weak (e ∷ ls) o i k f (h , p) =
      (λ ox → case h (o ox) of λ { (inj₁ a) → inj₁ (i a) ; (inj₂ b) → inj₂ (f b) })
    , Prov-weak ls o i k (λ { (inj₁ a) → inj₁ (f a) ; (inj₂ b) → inj₂ (k b) }) p

  -- more initial knowledge
  Prov-mono : ∀ {O Kp In K K′} ls → (∀ {x} → K x → K′ x) → Prov O Kp In K ls → Prov O Kp In K′ ls
  Prov-mono ls f = Prov-weak ls id id id f

  -- concatenation: the second part may use what the first part made known
  Prov-++ : ∀ {O Kp In K} ls₁ {ls₂} → Prov O Kp In K ls₁ → Prov O Kp In (λ x → K x ⊎ Kn Kp ls₁ x) ls₂
          → Prov O Kp In K (ls₁ ++ ls₂)
  Prov-++ []        _       q = Prov-mono _ (λ { (inj₁ a) → a ; (inj₂ ()) }) q
  Prov-++ (e ∷ ls₁) (h , p) q =
    h , Prov-++ ls₁ p (Prov-mono _ (λ { (inj₁ a) → inj₁ (inj₁ a) ; (inj₂ (inj₁ b)) → inj₁ (inj₂ b)
                                       ; (inj₂ (inj₂ c)) → inj₂ c }) q)

  ------------------------------------------------------------------------
  -- §2. Composition, closure, hiding
  ------------------------------------------------------------------------

  -- COMPOSITION THROUGH `Par`: an unsynchronised input stays an input; a synchronised event
  -- is an input of the composite only if it is one on BOTH sides
  Prov-par : ∀ {ℓ₁ ℓ₂ ℓs} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R₀ : Set ℓs} {A : EventSet} {merge : R₁ → R₂ → R₀}
             {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R₀)}
             {O Kp In₁ In₂ In : Event → V → Set} {K₁ K₂ K : V → Set}
           → (∀ {e x} → ¬ InA A e → In₁ e x → In e x)
           → (∀ {e x} → ¬ InA A e → In₂ e x → In e x)
           → (∀ {e x} → In₁ e x → In₂ e x → In e x)
           → (∀ {x} → K₁ x → K x) → (∀ {x} → K₂ x → K x)
           → ParInter A merge sP sQ s
           → Prov O Kp In₁ K₁ (labels sP) → Prov O Kp In₂ K₂ (labels sQ) → Prov O Kp In K (labels s)
  Prov-par s₁ s₂ b f₁ f₂ pnil _ _ = tt
  Prov-par s₁ s₂ b f₁ f₂ (psync m pi) (h₁ , p₁) (h₂ , p₂) =
      (λ ox → case h₁ ox of λ where
                (inj₂ k) → inj₂ (f₁ k)
                (inj₁ i₁) → case h₂ ox of λ where
                  (inj₂ k)  → inj₂ (f₂ k)
                  (inj₁ i₂) → inj₁ (b i₁ i₂))
    , Prov-par s₁ s₂ b (λ { (inj₁ k) → inj₁ (f₁ k) ; (inj₂ k) → inj₂ k })
                       (λ { (inj₁ k) → inj₁ (f₂ k) ; (inj₂ k) → inj₂ k }) pi p₁ p₂
  Prov-par s₁ s₂ b f₁ f₂ (psoloL ¬m pi) (h₁ , p₁) p₂ =
      (λ ox → case h₁ ox of λ { (inj₁ i) → inj₁ (s₁ ¬m i) ; (inj₂ k) → inj₂ (f₁ k) })
    , Prov-par s₁ s₂ b (λ { (inj₁ k) → inj₁ (f₁ k) ; (inj₂ k) → inj₂ k }) (λ k → inj₁ (f₂ k)) pi p₁ p₂
  Prov-par s₁ s₂ b f₁ f₂ (psoloR ¬m pi) p₁ (h₂ , p₂) =
      (λ ox → case h₂ ox of λ { (inj₁ i) → inj₁ (s₂ ¬m i) ; (inj₂ k) → inj₂ (f₂ k) })
    , Prov-par s₁ s₂ b (λ k → inj₁ (f₁ k)) (λ { (inj₁ k) → inj₁ (f₂ k) ; (inj₂ k) → inj₂ k }) pi p₁ p₂
  Prov-par s₁ s₂ b f₁ f₂ p√ _ _ = tt

  -- … the homogeneous case (same inputs on both sides, any sync set): no side condition
  Prov-par≡ : ∀ {ℓ₁ ℓ₂ ℓs} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R₀ : Set ℓs} {A : EventSet} {merge : R₁ → R₂ → R₀}
              {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R₀)}
              {O Kp In : Event → V → Set} {K : V → Set}
            → ParInter A merge sP sQ s
            → Prov O Kp In K (labels sP) → Prov O Kp In K (labels sQ) → Prov O Kp In K (labels s)
  Prov-par≡ = Prov-par (λ _ i → i) (λ _ i → i) (λ i _ → i) id id

  -- CLOSING A CHAIN: if every known-maker is an obligation, knowledge traces back to inputs
  Prov-close : ∀ {O Kp In K K′} ls → (∀ {e x} → Kp e x → O e x) → (∀ {x} → K x → K′ x)
             → Prov O Kp In K ls → Prov O In In K′ ls
  Prov-close []       ko f _       = tt
  Prov-close (e ∷ ls) ko f (h , p) =
      (λ ox → case h ox of λ { (inj₁ i) → inj₁ i ; (inj₂ k) → inj₂ (f k) })
    , Prov-close ls ko (λ where
        (inj₁ k)  → inj₁ (f k)
        (inj₂ kp) → case h (ko kp) of λ { (inj₁ i) → inj₂ i ; (inj₂ k) → inj₁ (f k) }) p

  -- HIDING events that make nothing known keeps provenance
  Prov-hide : ∀ {ℓr} {R : Set ℓr} {O Kp In} {A : EventSet} {s′ s : List (Event√ R)}
            → (∀ {e x} → InA A e → Kp e x → ⊥) → HideTr A s′ s
            → ∀ {K} → Prov O Kp In K (labels s′) → Prov O Kp In K (labels s)
  Prov-hide nk hnil         p       = tt
  Prov-hide nk (hkeep _ h)  (o , p) = o , Prov-hide nk h p
  Prov-hide nk (hdrop m h)  (o , p) =
    Prov-hide nk h (Prov-mono _ (λ { (inj₁ k) → k ; (inj₂ kp) → ⊥-elim (nk m kp) }) p)
  Prov-hide nk h√           p       = tt

  -- THE READ-OUT: after closing (inputs = known-makers), every O-value of every label is
  -- known somewhere in the whole list (or initially)
  Prov→All : ∀ {O Kp K} ls → Prov O Kp Kp K ls → AllL (λ e → ∀ {x} → O e x → K x ⊎ Kn Kp ls x) ls
  Prov→All []       _       = []
  Prov→All {O} {Kp} {K} (e ∷ ls) (h , p) =
      (λ ox → case h ox of λ { (inj₁ i) → inj₂ (inj₁ i) ; (inj₂ k) → inj₁ k })
    ∷ AllL-map′ (Prov→All ls p)
    where
      -- re-associate the knowledge of the tail
      AllL-map′ : ∀ {ms} → AllL (λ e′ → ∀ {x} → O e′ x → (K x ⊎ Kp e x) ⊎ Kn Kp ls x) ms
                → AllL (λ e′ → ∀ {x} → O e′ x → K x ⊎ (Kp e x ⊎ Kn Kp ls x)) ms
      AllL-map′ []      = []
      AllL-map′ (q ∷ a) =
        (λ ox → case q ox of λ { (inj₁ (inj₁ k)) → inj₁ k ; (inj₁ (inj₂ c)) → inj₂ (inj₁ c)
                                ; (inj₂ c) → inj₂ (inj₂ c) })
        ∷ AllL-map′ a

  ------------------------------------------------------------------------
  -- §3. Rounds: provenance of every trace of a tree
  ------------------------------------------------------------------------

  -- every trace of `t` has provenance from `K` (a record, so the predicates unify first-order)
  record ProvT {ℓr} {R : Set ℓr} (O Kp In : Event → V → Set) (K : V → Set) (t : PTree E (ExtI E) R)
         : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
    constructor provT
    field runP : ∀ {s W} → t ⟹⟨ s ⟩ W → Prov O Kp In K (labels s)
  open ProvT public

  -- the invariant at a round's return value (a loop-back carries the new state)
  JAt : ∀ {ℓx} {Rx : Set ℓx} {A : Set ℓ} → (A → (V → Set) → Set) → A ⊎ Rx → (V → Set) → Set
  JAt J (inj₁ a) K = J a K
  JAt J (inj₂ _) K = ⊤

  module _ {O Kp In : Event → V → Set} where

    -- a return carries nothing
    ProvT-Ret : ∀ {ℓr} {R : Set ℓr} {K} {x : R} → ProvT O Kp In K (Ret x)
    ProvT-Ret = provT λ tr → case Ret-tr tr of λ { (inj₁ refl) → tt ; (inj₂ refl) → tt }

    -- `Stop` does nothing
    ProvT-Stop : ∀ {ℓr} {R : Set ℓr} {K} → ProvT O Kp In K (Stop {R = R})
    ProvT-Stop {R = R} {K} = provT go
      where
        -- the only trace is the empty one
        go : ∀ {s W} → Stop {R = R} ⟹⟨ s ⟩ W → Prov O Kp In K (labels s)
        go ⟹-refl                      = tt
        go (⟹-τ (sSil ()) _)
        go (⟹-τ (sTau refl ()) _)
        go (⟹-ev (sRet ()) _)
        go (⟹-ev (sVis refl ()) _)

    -- a prefix: its event's obligation, then the continuation with the event's values known
    ProvT-⟶ : ∀ {ℓr} {R : Set ℓr} {K} {A : Set ℓ} (e : E A) {P : A → PTree E (ExtI E) R}
            → (∀ x {y} → O (evLabel A e x) y → In (evLabel A e x) y ⊎ K y)
            → (∀ x → ProvT O Kp In (λ y → K y ⊎ Kp (evLabel A e x) y) (P x))
            → ProvT O Kp In K (e ⟶ P)
    ProvT-⟶ e h q = provT λ tr → case pfx-tr tr of λ where
      (inj₁ refl)                  → tt
      (inj₂ (x , _ , refl , rest)) → (λ {y} → h x) , runP (q x) rest

    -- an output
    ProvT-Output : ∀ {ℓr} {R : Set ℓr} {K} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (e : E A) (v : A) {P : PTree E (ExtI E) R}
                 → (∀ {y} → O (evLabel A e v) y → In (evLabel A e v) y ⊎ K y)
                 → ProvT O Kp In (λ y → K y ⊎ Kp (evLabel A e v) y) P
                 → ProvT O Kp In K (e ! v ⟶ P)
    ProvT-Output e v h q = provT λ tr → case out-tr tr of λ where
      (inj₁ refl)              → tt
      (inj₂ (_ , refl , rest)) → (λ {y} → h) , runP q rest

    -- an external choice
    ProvT-□ : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ {K} {P Q : PTree E (ExtI E) R}
            → ProvT O Kp In K P → ProvT O Kp In K Q → ProvT O Kp In K (P □ Q)
    ProvT-□ {P = P} {Q} p q = provT λ tr → case □-trace-elim P Q tr of λ where
      (inj₁ (_ , t₁)) → runP p t₁
      (inj₂ (_ , t₂)) → runP q t₂

    -- a bind whose continuation has provenance from ANY knowledge
    ProvT->>= : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} {K} {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
              → ProvT O Kp In K P → (∀ r {K′} → ProvT O Kp In K′ (k r)) → ProvT O Kp In K (P >>= k)
    ProvT->>= {P = P} {k} p q = provT λ tr → case bind-elim-aux P k tr of λ where
      (bs-live d eo) → subst (Prov O Kp In _) (labels-EvlOnly eo) (runP p d)
      (bs-term {sS = sS} {s_k = s_k} d fr eo (_ , kt) refl) →
        subst (Prov O Kp In _) (sym (labels-++ sS s_k))
          (Prov-++ (labels sS) (subst (Prov O Kp In _) (labels-EvlOnly eo) (runP p d)) (runP (q _) kt))

    -- a menu (`pchoice`): every step is justified, and so is the rest from there
    ProvT-pchoice : ∀ {ℓr} {R : Set ℓr} {K} {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  → (∀ {x t′} → pchoice v ─[ ev (evl x) ]─► t′
                       → (∀ {y} → O x y → In x y ⊎ K y) × ProvT O Kp In (λ y → K y ⊎ Kp x y) t′)
                  → ProvT O Kp In K (pchoice v)
    ProvT-pchoice {K = K} {v} f = provT go
      where
        -- by the first step
        go : ∀ {s W} → pchoice v ⟹⟨ s ⟩ W → Prov O Kp In K (labels s)
        go ⟹-refl                         = tt
        go (⟹-τ (sSil ()) _)
        go (⟹-τ (sTau refl ()) _)
        go (⟹-ev (sRet ()) _)
        go (⟹-ev {e = evl x} st rest)     = (λ {y} → proj₁ (f st)) , runP (proj₂ (f st)) rest

    ----------------------------------------------------------------------
    -- §4. Iterations
    ----------------------------------------------------------------------

    module _ {ℓx : Level} {Rx : Set ℓx} {A : Set ℓ} (k : A → PTree E (ExtI E) (A ⊎ Rx)) where

      -- STATEFUL ITERATION: a state invariant `J a K` ("state a is justified by K") that
      -- licenses every round's provenance and is re-established by every completed round
      module _ (J : A → (V → Set) → Set)
               (rP : ∀ {a K} → J a K → ProvT O Kp In K (k a))
               (rJ : ∀ {a K} → J a K → Post (λ ls x → JAt J x (λ y → K y ⊎ Kn Kp ls y)) (k a)) where

        -- along the rounds
        provInvR : ∀ {a K s} → J a K → Rounds {Rx = Rx} k (k a) s → Prov O Kp In K (labels s)
        provInvR j (rLive d eo) = subst (Prov O Kp In _) (labels-EvlOnly eo) (runP (rP j) d)
        provInvR {K = K} j (rBack {r = r} {s₁ = s₁} {s₂ = s₂} d fr eo rs) =
          subst (Prov O Kp In K) (sym (labels-++ s₁ s₂))
            (Prov-++ (labels s₁) (subst (Prov O Kp In K) (labels-EvlOnly eo) (runP (rP j) d))
              (provInvR (subst (λ ls → J _ (λ y → K y ⊎ Kn Kp ls y)) (labels-EvlOnly eo)
                           (run (rJ j) (⟹-append-√ d fr))) rs))
        provInvR {K = K} j (rDone {x = x} {s₁ = s₁} d fr eo) =
          subst (Prov O Kp In K) (sym (trans (labels-++ s₁ (√ x ∷ [])) (++-identityʳ (labels s₁))))
            (subst (Prov O Kp In K) (labels-EvlOnly eo) (runP (rP j) d))

        -- THE STATEFUL ITERATION LEMMA
        provInv : ∀ {a K s W} → J a K → iter k a ⟹⟨ s ⟩ W → Prov O Kp In K (labels s)
        provInv j tr = provInvR j (rounds {Rx = Rx} k tr)

      -- ROUND-LOCAL ITERATION: every round justifies its own outputs
      provIter : (∀ a → ProvT O Kp In (λ _ → ⊥) (k a))
               → ∀ a {K s W} → iter k a ⟹⟨ s ⟩ W → Prov O Kp In K (labels s)
      provIter pk a {K} tr =
        provInv (λ _ _ → ⊤) (λ {a} {K′} _ → provT λ d → Prov-mono _ (λ {x} ()) (runP (pk a) d))
                (λ _ → post λ {_} {x} _ → jat x) {K = K} tt tr
        where
          -- the trivial invariant holds at every return value
          jat : ∀ x {K′} → JAt (λ _ _ → ⊤) x K′
          jat (inj₁ _) = tt
          jat (inj₂ _) = tt

  ------------------------------------------------------------------------
  -- §5. Processes: provenance of every trace, from any initial knowledge
  ------------------------------------------------------------------------

  -- every trace of `P` has provenance, whatever is known initially
  record PA {ℓr} {R : Set ℓr} (O Kp In : Event → V → Set) (P : PTree E (ExtI E) R)
         : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
    constructor pa
    field runA : ∀ {K s W} → P ⟹⟨ s ⟩ W → Prov O Kp In K (labels s)
  open PA public

  -- composition through `Par`, side conditions as in `Prov-par`
  PA-par : ∀ {ℓ₁ ℓ₂ ℓs} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R₀ : Set ℓs} {A : EventSet} {merge : R₁ → R₂ → R₀}
           {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂} {O Kp In₁ In₂ In : Event → V → Set}
         → (∀ {e x} → ¬ InA A e → In₁ e x → In e x)
         → (∀ {e x} → ¬ InA A e → In₂ e x → In e x)
         → (∀ {e x} → In₁ e x → In₂ e x → In e x)
         → PA O Kp In₁ P → PA O Kp In₂ Q → PA O Kp In (Par A merge P Q)
  PA-par {A = A} {merge} {P} {Q} s₁ s₂ b pp pq = pa λ tr → case Par-trace-elim A merge P Q tr of λ where
    (_ , _ , _ , _ , tP , tQ , pi) → Prov-par s₁ s₂ b id id pi (runA pp tP) (runA pq tQ)

  -- … homogeneous
  PA-par≡ : ∀ {ℓ₁ ℓ₂ ℓs} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R₀ : Set ℓs} {A : EventSet} {merge : R₁ → R₂ → R₀}
            {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂} {O Kp In : Event → V → Set}
          → PA O Kp In P → PA O Kp In Q → PA O Kp In (Par A merge P Q)
  PA-par≡ = PA-par (λ _ i → i) (λ _ i → i) (λ i _ → i)

  -- hiding events that make nothing known
  PA-hide : ∀ {ℓr} {R : Set ℓr} {A : EventSet} {P : PTree E (ExtI E) R} {O Kp In : Event → V → Set}
          → (∀ {e x} → InA A e → Kp e x → ⊥) → PA O Kp In P → PA O Kp In (P ∖ A)
  PA-hide {A = A} {P} nk pp = pa λ tr → case Hide-trace-elim A P tr of λ where
    (_ , _ , tP , h) → Prov-hide nk h (runA pp tP)

  -- closing a chain
  PA-close : ∀ {ℓr} {R : Set ℓr} {P : PTree E (ExtI E) R} {O Kp In : Event → V → Set}
           → (∀ {e x} → Kp e x → O e x) → PA O Kp In P → PA O In In P
  PA-close ko pp = pa λ tr → Prov-close _ ko id (runA pp tr)

  -- weakening
  PA-weak : ∀ {ℓr} {R : Set ℓr} {P : PTree E (ExtI E) R} {O O′ Kp Kp′ In In′ : Event → V → Set}
          → (∀ {e x} → O′ e x → O e x) → (∀ {e x} → In e x → In′ e x) → (∀ {e x} → Kp e x → Kp′ e x)
          → PA O Kp In P → PA O′ Kp′ In′ P
  PA-weak o i k pp = pa λ tr → Prov-weak _ o i k id (runA pp tr)

  -- a return carries nothing
  PA-Ret : ∀ {ℓr} {R : Set ℓr} {x : R} {O Kp In : Event → V → Set} → PA O Kp In (Ret x)
  PA-Ret = pa λ tr → runP ProvT-Ret tr

  -- every interleaving of a mapped list
  PA-⦀⋆map : ∀ {ℓr} {A : Set} {O Kp In : Event → V → Set} (f : A → PTree E (ExtI E) (⊤′ {ℓr}))
           → (∀ x → PA O Kp In (f x)) → ∀ xs → PA O Kp In (⦀⋆ (map f xs))
  PA-⦀⋆map f pf []       = PA-Ret
  PA-⦀⋆map f pf (x ∷ xs) = PA-par≡ (pf x) (PA-⦀⋆map f pf xs)

  -- every finite interleaving
  PA-⦀Fin : ∀ {ℓr} {O Kp In : Event → V → Set} n (f : Fin n → PTree E (ExtI E) (⊤′ {ℓr}))
          → (∀ i → PA O Kp In (f i)) → PA O Kp In (⦀Fin n f)
  PA-⦀Fin zero    f pf = PA-Ret
  PA-⦀Fin (suc n) f pf = PA-par≡ (pf fzero) (PA-⦀Fin n (λ i → f (fsuc i)) (λ i → pf (fsuc i)))
