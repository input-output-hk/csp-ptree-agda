{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- More counting over traces (Leios no-livelock, Stage C, premise (a)).
-- Generic: no Leios/Cardano content.  Extends `Count` with
--   (a) `Σc-sync`, `Σc-⦀`     — weights through a synchronised / free `Par`
--   (b) `AnyE-*`, `AllL-*`     — per-label facts moved across a `Par`
--   (c) `χ`, `χ̄`, `#H≡Σc`, `Σc≤#V` — the bridge to Stage G's `#H`/`#V`
--   (d) `DpW`                 — WEIGHTED depth (an event pays its own weight)
--   (e) `*-if`, `*-maybe′`    — conditionals for every round predicate
--   (f) `ptrLoopW`, `trigLoop` — pointer loop with weights; TRIGGERED loop
--   (g) `PfxW`, `Back`, `iterPot` — the iteration POTENTIAL lemma
--   (h) `pch-tr`, `Post-pchoice`, `RoundPot`, `StepPot`, `potIter`, `slack0`, `none0`
--       — later additions: a menu-round potential lemma, and no-slack/zero-weight bounds
-- No postulate, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Bool using (Bool; true; false; if_then_else_; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ)
open import Data.Maybe using (Maybe; just; nothing; maybe′)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; _∸_; z≤n; s≤s; _≤ᵇ_)
open import Data.Nat.Properties
  using (≤ᵇ⇒≤; ≤-refl; ≤-trans; m≤m+n; m≤n+m; +-identityʳ; n≤0⇒n≡0; m≤n⇒m≤1+n; +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; +-assoc; +-comm; *-suc; *-distribˡ-+)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming (map to map⊎)
open import Function using (id; case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Laws.DivFree.CountMore {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import CSP.Laws.Traces.TraceLawsBind E-≟ using (EvlOnly; bs-live; bs-term; bind-elim-aux; ⟹-append-√)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟ using (□-trace-elim)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟ using (ParInter; pnil; psync; psoloL; psoloR; p√)
open import CSP.Laws.DivFree.Loop E-≟ using (loopStep)
open import CSP.Laws.DivFree.Count E-≟
open import CSP.Laws.FD.NoLivelock E-≟ using (#H; #V)
-- the label lies in the event set (one definition, shared with `Prov`)
open import CSP.Laws.DivFree.Prov E-≟ using (InA) public

private
  variable
    ℓr ℓs : Level
    R : Set ℓr
    S : Set ℓs

------------------------------------------------------------------------
-- Arithmetic helpers
------------------------------------------------------------------------

-- `x + (y + z) ≡ y + (x + z)`
+-swap : ∀ x y z → x + (y + z) ≡ y + (x + z)
+-swap x y z = trans (sym (+-assoc x y z)) (trans (cong (_+ z) (+-comm x y)) (+-assoc y x z))

-- `(a + b) + (c + d) ≡ (a + c) + (b + d)`
+-inter : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
+-inter a b c d = trans (+-assoc a b (c + d)) (trans (cong (a +_) (+-swap b c d)) (sym (+-assoc a c (b + d))))

-- an equation read as an inequality
≤-≡ : ∀ {x y} → x ≡ y → x ≤ y
≤-≡ refl = ≤-refl

-- the labels of a √-terminated trace are those of its body
labels-√ : (s : List (Event√ R)) {x : R} → labels (s ++ (√ x ∷ [])) ≡ labels s
labels-√ s {x} = trans (labels-++ s (√ x ∷ [])) (++-identityʳ (labels s))

------------------------------------------------------------------------
-- §1. Weights through a `Par`
------------------------------------------------------------------------

-- a weight that vanishes outside the sync set counts the same on each side as on the whole
Σc-sync : (c : Event → ℕ) {ℓ₁ ℓ₂ ℓ₀ : Level} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R₀ : Set ℓ₀}
          {A : EventSet} {merge : R₁ → R₂ → R₀}
          {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R₀)}
        → (∀ e → ¬ InA A e → c e ≡ 0) → ParInter A merge sP sQ s
        → (Σc c (labels sP) ≡ Σc c (labels s)) × (Σc c (labels sQ) ≡ Σc c (labels s))
Σc-sync c z pnil = refl , refl
Σc-sync c z (psync m pi) with Σc-sync c z pi
... | p , q = cong (c _ +_) p , cong (c _ +_) q
Σc-sync c z (psoloL {s = s} ¬m pi) with Σc-sync c z pi
... | p , q = cong (c _ +_) p , trans q (cong (_+ Σc c (labels s)) (sym (z _ ¬m)))
Σc-sync c z (psoloR {s = s} ¬m pi) with Σc-sync c z pi
... | p , q = trans p (cong (_+ Σc c (labels s)) (sym (z _ ¬m))) , cong (c _ +_) q
Σc-sync c z p√ = refl , refl

-- an interleaving is exactly additive
Σc-⦀ : (c : Event → ℕ) {ℓ₁ ℓ₂ ℓ₀ : Level} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R₀ : Set ℓ₀}
       {merge : R₁ → R₂ → R₀}
       {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R₀)}
     → ParInter ∅ES merge sP sQ s → Σc c (labels s) ≡ Σc c (labels sP) + Σc c (labels sQ)
Σc-⦀ c pnil          = refl
Σc-⦀ c (psync () _)
Σc-⦀ c (psoloL {sP = sP} {sQ} _ pi) =
  trans (cong (c _ +_) (Σc-⦀ c pi)) (sym (+-assoc (c _) (Σc c (labels sP)) (Σc c (labels sQ))))
Σc-⦀ c (psoloR {sP = sP} {sQ} _ pi) =
  trans (cong (c _ +_) (Σc-⦀ c pi)) (+-swap (c _) (Σc c (labels sP)) (Σc c (labels sQ)))
Σc-⦀ c p√            = refl

------------------------------------------------------------------------
-- §2. Per-label facts across a `Par`
------------------------------------------------------------------------

module _ {ℓ₁ ℓ₂ ℓ₀ : Level} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R₀ : Set ℓ₀}
         {A : EventSet} {merge : R₁ → R₂ → R₀} {P : Event → Set} where

  -- a left event is a composite event
  AnyE-parL : {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R₀)}
            → ParInter A merge sP sQ s → AnyE P sP → AnyE P s
  AnyE-parL pnil          ()
  AnyE-parL (psync _ pi)  (here p)  = here p
  AnyE-parL (psync _ pi)  (there a) = there (AnyE-parL pi a)
  AnyE-parL (psoloL _ pi) (here p)  = here p
  AnyE-parL (psoloL _ pi) (there a) = there (AnyE-parL pi a)
  AnyE-parL (psoloR _ pi) a         = there (AnyE-parL pi a)
  AnyE-parL p√            (here ())
  AnyE-parL p√            (there ())

  -- a right event is a composite event
  AnyE-parR : {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R₀)}
            → ParInter A merge sP sQ s → AnyE P sQ → AnyE P s
  AnyE-parR pnil          ()
  AnyE-parR (psync _ pi)  (here p)  = here p
  AnyE-parR (psync _ pi)  (there a) = there (AnyE-parR pi a)
  AnyE-parR (psoloL _ pi) a         = there (AnyE-parR pi a)
  AnyE-parR (psoloR _ pi) (here p)  = here p
  AnyE-parR (psoloR _ pi) (there a) = there (AnyE-parR pi a)
  AnyE-parR p√            (here ())
  AnyE-parR p√            (there ())

  -- a composite event comes from one of the sides
  AnyE-split : {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R₀)}
             → ParInter A merge sP sQ s → AnyE P s → AnyE P sP ⊎ AnyE P sQ
  AnyE-split pnil          ()
  AnyE-split (psync _ pi)  (here p)  = inj₁ (here p)
  AnyE-split (psync _ pi)  (there a) = map⊎ there there (AnyE-split pi a)
  AnyE-split (psoloL _ pi) (here p)  = inj₁ (here p)
  AnyE-split (psoloL _ pi) (there a) = map⊎ there id (AnyE-split pi a)
  AnyE-split (psoloR _ pi) (here p)  = inj₂ (here p)
  AnyE-split (psoloR _ pi) (there a) = map⊎ id there (AnyE-split pi a)
  AnyE-split p√            (here ())
  AnyE-split p√            (there ())

  -- an event inside the sync set on the left is also on the right
  AnyE-sync : (∀ e → P e → InA A e)
            → {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R₀)}
            → ParInter A merge sP sQ s → AnyE P sP → AnyE P sQ
  AnyE-sync h pnil           ()
  AnyE-sync h (psync _ pi)   (here p)  = here p
  AnyE-sync h (psync _ pi)   (there a) = there (AnyE-sync h pi a)
  AnyE-sync h (psoloL ¬m pi) (here p)  = ⊥-elim (¬m (h _ p))
  AnyE-sync h (psoloL _ pi)  (there a) = AnyE-sync h pi a
  AnyE-sync h (psoloR _ pi)  a         = there (AnyE-sync h pi a)
  AnyE-sync h p√             (here ())
  AnyE-sync h p√             (there ())

  -- a per-label fact of the composite holds on the left
  AllL-parL : {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R₀)}
            → ParInter A merge sP sQ s → AllL P (labels s) → AllL P (labels sP)
  AllL-parL pnil          a       = []
  AllL-parL (psync _ pi)  (p ∷ a) = p ∷ AllL-parL pi a
  AllL-parL (psoloL _ pi) (p ∷ a) = p ∷ AllL-parL pi a
  AllL-parL (psoloR _ pi) (_ ∷ a) = AllL-parL pi a
  AllL-parL p√            a       = []

  -- a per-label fact of the composite holds on the right
  AllL-parR : {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R₀)}
            → ParInter A merge sP sQ s → AllL P (labels s) → AllL P (labels sQ)
  AllL-parR pnil          a       = []
  AllL-parR (psync _ pi)  (p ∷ a) = p ∷ AllL-parR pi a
  AllL-parR (psoloL _ pi) (_ ∷ a) = AllL-parR pi a
  AllL-parR (psoloR _ pi) (p ∷ a) = p ∷ AllL-parR pi a
  AllL-parR p√            a       = []

------------------------------------------------------------------------
-- §3. The bridge to Stage G's `#H` / `#V`
------------------------------------------------------------------------

-- 1 on a label inside H, 0 outside
χ : EventSet → Event → ℕ
χ H (evLabel B e a) with H .dec (B , e) a
... | yes _ = 1
... | no  _ = 0

-- 1 on a label outside H, 0 inside
χ̄ : EventSet → Event → ℕ
χ̄ H (evLabel B e a) with H .dec (B , e) a
... | yes _ = 0
... | no  _ = 1

-- the hidden count is the χ-weight of the labels
#H≡Σc : (H : EventSet) (s : List (Event√ R)) → #H H s ≡ Σc (χ H) (labels s)
#H≡Σc H []                        = refl
#H≡Σc H (evl (evLabel B e a) ∷ s) with H .dec (B , e) a
... | yes _ = cong suc (#H≡Σc H s)
... | no  _ = #H≡Σc H s
#H≡Σc H (√ _ ∷ s)                 = #H≡Σc H s

-- the χ̄-weight of the labels is at most the visible count (which also counts `√`)
Σc≤#V : (H : EventSet) (s : List (Event√ R)) → Σc (χ̄ H) (labels s) ≤ #V H s
Σc≤#V H []                        = z≤n
Σc≤#V H (evl (evLabel B e a) ∷ s) with H .dec (B , e) a
... | yes _ = Σc≤#V H s
... | no  _ = s≤s (Σc≤#V H s)
Σc≤#V H (√ _ ∷ s)                 = m≤n⇒m≤1+n (Σc≤#V H s)

------------------------------------------------------------------------
-- §4. Weighted depth
------------------------------------------------------------------------

-- every trace of `t` has at most `n` visible events plus the weight of its labels
DpW : ℕ → (Event → ℕ) → PTree E (ExtI E) R → Set _
DpW n w t = ∀ {s W} → t ⟹⟨ s ⟩ W → #e s ≤ n + Σc w (labels s)

-- a depth is a weighted depth
Dp→DpW : {n : ℕ} {w : Event → ℕ} {t : PTree E (ExtI E) R} → Dp n t → DpW n w t
Dp→DpW {n = n} d tr = ≤-trans (d tr) (m≤m+n n _)

-- weakening
DpW-mono : {m n : ℕ} {w : Event → ℕ} {t : PTree E (ExtI E) R} → m ≤ n → DpW m w t → DpW n w t
DpW-mono le d tr = ≤-trans (d tr) (+-monoˡ-≤ _ le)

-- a return has no visible event
DpW-Ret : {n : ℕ} {w : Event → ℕ} {x : R} → DpW n w (Ret x)
DpW-Ret tr = ≤-trans (Dp-Ret tr) z≤n

-- a prefix adds one, and the event's weight is credited to the continuation
DpW-⟶ : {n : ℕ} {w : Event → ℕ} {A : Set ℓ} (e : E A) {P : A → PTree E (ExtI E) R}
      → (∀ x → DpW (n + w (evLabel A e x)) w (P x)) → DpW (suc n) w (e ⟶ P)
DpW-⟶ {n = n} {w} {A} e dp tr with pfx-tr tr
... | inj₁ refl                   = z≤n
... | inj₂ (x , s′ , refl , rest) = s≤s (subst (#e s′ ≤_) (+-assoc n (w (evLabel A e x)) (Σc w (labels s′))) (dp x rest))

-- an output adds one, and the event's weight is credited to the continuation
DpW-Output : {n : ℕ} {w : Event → ℕ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (e : E A) (v : A) {P : PTree E (ExtI E) R}
           → DpW (n + w (evLabel A e v)) w P → DpW (suc n) w (e ! v ⟶ P)
DpW-Output {n = n} {w} {A} e v dp tr with out-tr tr
... | inj₁ refl               = z≤n
... | inj₂ (s′ , refl , rest) = s≤s (subst (#e s′ ≤_) (+-assoc n (w (evLabel A e v)) (Σc w (labels s′))) (dp rest))

-- a bind adds the two depths
DpW->>= : {m n : ℕ} {w : Event → ℕ} {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
        → DpW m w P → (∀ r → DpW n w (k r)) → DpW (m + n) w (P >>= k)
DpW->>= {m = m} {n} {w} {P} {k} dp dk tr with bind-elim-aux P k tr
... | bs-live d eo =
      ≤-trans (subst₂ (λ x y → x ≤ m + Σc w y) (#e-EvlOnly eo) (labels-EvlOnly eo) (dp d))
              (+-monoˡ-≤ _ (m≤m+n m n))
... | bs-term {sS = sS} {s_k = s_k} d fr eo (_ , kt) refl =
      subst₂ _≤_ (sym (#e-++ sS s_k))
        (trans (+-inter m (Σc w (labels sS)) n (Σc w (labels s_k)))
               (cong ((m + n) +_) (trans (sym (Σc-++ w (labels sS) (labels s_k)))
                                         (cong (Σc w) (sym (labels-++ sS s_k))))))
        (+-mono-≤ (subst₂ (λ x y → x ≤ m + Σc w y) (#e-EvlOnly eo) (labels-EvlOnly eo) (dp d)) (dk _ kt))

-- an external choice is no deeper than its deeper branch
DpW-□ : ⦃ _ : DecEq R ⦄ {n : ℕ} {w : Event → ℕ} {P Q : PTree E (ExtI E) R}
      → DpW n w P → DpW n w Q → DpW n w (P □ Q)
DpW-□ {P = P} {Q} dp dq tr with □-trace-elim P Q tr
... | inj₁ (_ , tP) = dp tP
... | inj₂ (_ , tQ) = dq tQ

------------------------------------------------------------------------
-- §5. Conditionals
------------------------------------------------------------------------

-- depth of a conditional
Dp-if : {n : ℕ} {P Q : PTree E (ExtI E) R} → ∀ b → Dp n P → Dp n Q → Dp n (if b then P else Q)
Dp-if true  p q = p
Dp-if false p q = q

-- completion of a conditional
Ends-if : {a : R} {P Q : PTree E (ExtI E) R} → ∀ b → Ends a P → Ends a Q → Ends a (if b then P else Q)
Ends-if true  p q = p
Ends-if false p q = q

-- reading completion of a conditional
Cm-if : {Rd : Event → Set} {a : R} {P Q : PTree E (ExtI E) R}
      → ∀ b → Cm Rd a P → Cm Rd a Q → Cm Rd a (if b then P else Q)
Cm-if true  p q = p
Cm-if false p q = q

-- per-label invariant of a conditional
AllT-if : {Pr : Event → Set} {P Q : PTree E (ExtI E) R}
        → ∀ b → AllT Pr P → AllT Pr Q → AllT Pr (if b then P else Q)
AllT-if true  p q = p
AllT-if false p q = q

-- post-condition of a conditional
Post-if : {Q′ : List Event → R → Set} {P Q : PTree E (ExtI E) R}
        → ∀ b → Post Q′ P → Post Q′ Q → Post Q′ (if b then P else Q)
Post-if true  p q = p
Post-if false p q = q

-- weighted depth of a conditional
DpW-if : {n : ℕ} {w : Event → ℕ} {P Q : PTree E (ExtI E) R}
       → ∀ b → DpW n w P → DpW n w Q → DpW n w (if b then P else Q)
DpW-if true  p q = p
DpW-if false p q = q

-- depth of a `maybe′`
Dp-maybe′ : {X : Set ℓs} {n : ℕ} {f : X → PTree E (ExtI E) R} {y : PTree E (ExtI E) R}
          → (∀ x → Dp n (f x)) → Dp n y → ∀ m → Dp n (maybe′ f y m)
Dp-maybe′ pf py (just x) = pf x
Dp-maybe′ pf py nothing  = py

-- completion of a `maybe′`
Ends-maybe′ : {X : Set ℓs} {a : R} {f : X → PTree E (ExtI E) R} {y : PTree E (ExtI E) R}
            → (∀ x → Ends a (f x)) → Ends a y → ∀ m → Ends a (maybe′ f y m)
Ends-maybe′ pf py (just x) = pf x
Ends-maybe′ pf py nothing  = py

-- reading completion of a `maybe′`
Cm-maybe′ : {X : Set ℓs} {Rd : Event → Set} {a : R} {f : X → PTree E (ExtI E) R} {y : PTree E (ExtI E) R}
          → (∀ x → Cm Rd a (f x)) → Cm Rd a y → ∀ m → Cm Rd a (maybe′ f y m)
Cm-maybe′ pf py (just x) = pf x
Cm-maybe′ pf py nothing  = py

-- per-label invariant of a `maybe′`
AllT-maybe′ : {X : Set ℓs} {Pr : Event → Set} {f : X → PTree E (ExtI E) R} {y : PTree E (ExtI E) R}
            → (∀ x → AllT Pr (f x)) → AllT Pr y → ∀ m → AllT Pr (maybe′ f y m)
AllT-maybe′ pf py (just x) = pf x
AllT-maybe′ pf py nothing  = py

-- post-condition of a `maybe′`
Post-maybe′ : {X : Set ℓs} {Q : List Event → R → Set} {f : X → PTree E (ExtI E) R} {y : PTree E (ExtI E) R}
            → (∀ x → Post Q (f x)) → Post Q y → ∀ m → Post Q (maybe′ f y m)
Post-maybe′ pf py (just x) = pf x
Post-maybe′ pf py nothing  = py

-- weighted depth of a `maybe′`
DpW-maybe′ : {X : Set ℓs} {n : ℕ} {w : Event → ℕ} {f : X → PTree E (ExtI E) R} {y : PTree E (ExtI E) R}
           → (∀ x → DpW n w (f x)) → DpW n w y → ∀ m → DpW n w (maybe′ f y m)
DpW-maybe′ pf py (just x) = pf x
DpW-maybe′ pf py nothing  = py

------------------------------------------------------------------------
-- §6. Loops: weighted pointer loop, triggered loop
------------------------------------------------------------------------

-- arithmetic of a weighted pointer round
ptrW-arith : (D B k x y a b : ℕ) → k < B → x ≤ D + a → y ≤ D * (B ∸ suc k) + D + b
           → x + y ≤ D * (B ∸ k) + D + (a + b)
ptrW-arith D B k x y a b k<B x≤ y≤
  rewrite ∸-suc k<B | *-suc D (B ∸ suc k) =
    ≤-trans (+-mono-≤ x≤ y≤) (≤-≡ (solve 4 (λ D a P b → (D :+ a) :+ ((P :+ D) :+ b) := ((D :+ P) :+ D) :+ (a :+ b))
                                        refl D a (D * (B ∸ suc k)) b))
  where open +-*-Solver

module _ {A : Set ℓ} {body : A → PTree E (ExtI E) A} {idx : A → ℕ} {nxt : A → A}
         (idx-nxt : ∀ a → idx (nxt a) ≡ suc (idx a))
         {Rd : ℕ → Event → Set} {D B : ℕ} {w : Event → ℕ}
         (dp : ∀ a → DpW D w (loopStep {R = R} body a))
         (cm : ∀ a → Cm (Rd (idx a)) (inj₁ (nxt a)) (loopStep {R = R} body a)) where

  -- the weighted bound along the rounds, from state a
  ptrRoundsW : ∀ a {s} → Rounds {Rx = R} (loopStep body) (loopStep body a) s
             → (∀ j → AnyE (Rd j) s → j < B) → #e s ≤ D * (B ∸ idx a) + D + Σc w (labels s)
  ptrRoundsW a (rLive d eo) rb =
    ≤-trans (subst₂ (λ x y → x ≤ D + Σc w y) (#e-EvlOnly eo) (labels-EvlOnly eo) (dp a d))
            (+-monoˡ-≤ _ (m≤n+m D (D * (B ∸ idx a))))
  ptrRoundsW a (rBack {s₁ = s₁} {s₂ = s₂} d fr eo rs) rb with cm a (⟹-append-√ d fr)
  ... | rd , refl =
    subst₂ (λ x y → x ≤ D * (B ∸ idx a) + D + y) (sym (#e-++ s₁ s₂))
      (trans (sym (Σc-++ w (labels s₁) (labels s₂))) (cong (Σc w) (sym (labels-++ s₁ s₂))))
      (ptrW-arith D B (idx a) (#e s₁) (#e s₂) (Σc w (labels s₁)) (Σc w (labels s₂))
        (rb (idx a) (++⁺ˡ (AnyE-EvlOnly eo rd)))
        (subst₂ (λ x y → x ≤ D + Σc w y) (#e-EvlOnly eo) (labels-EvlOnly eo) (dp a d))
        (subst (λ i → #e s₂ ≤ D * (B ∸ i) + D + Σc w (labels s₂)) (idx-nxt a)
           (ptrRoundsW (nxt a) rs (λ j x → rb j (++⁺ʳ s₁ x)))))
  ptrRoundsW a (rDone {x = x} {s₁ = s₁} d fr eo) rb =
    subst₂ (λ u v → u ≤ D * (B ∸ idx a) + D + Σc w v)
      (sym (trans (#e-++ s₁ (√ x ∷ [])) (+-identityʳ (#e s₁)))) (sym (labels-√ s₁))
      (≤-trans (subst₂ (λ u v → u ≤ D + Σc w v) (#e-EvlOnly eo) (labels-EvlOnly eo) (dp a d))
               (+-monoˡ-≤ _ (m≤n+m D (D * (B ∸ idx a)))))

  -- THE WEIGHTED POINTER-LOOP BOUND
  ptrLoopW : ∀ a {s W} → loop {R = R} body a ⟹⟨ s ⟩ W
           → (∀ j → AnyE (Rd j) s → j < B) → #e s ≤ D * (B ∸ idx a) + D + Σc w (labels s)
  ptrLoopW a tr = ptrRoundsW a (rounds {Rx = R} (loopStep body) tr)

-- `D ≤ D * t` once `t` is positive
≤-*pos : ∀ D t → 1 ≤ t → D ≤ D * t
≤-*pos D (suc t) _ = subst (D ≤_) (sym (*-suc D t)) (m≤m+n D (D * t))

-- arithmetic of a triggered round
trig-arith : (D t₁ t₂ x y a b : ℕ) → 1 ≤ t₁ → x ≤ D + a → y ≤ D * t₂ + D + b
           → x + y ≤ D * (t₁ + t₂) + D + (a + b)
trig-arith D t₁ t₂ x y a b pos x≤ y≤ =
  ≤-trans (+-mono-≤ (≤-trans x≤ (+-monoˡ-≤ a (≤-*pos D t₁ pos))) y≤)
          (≤-≡ (solve 5 (λ D t₁ t₂ a b → (D :* t₁ :+ a) :+ ((D :* t₂ :+ D) :+ b)
                                        := (D :* (t₁ :+ t₂) :+ D) :+ (a :+ b)) refl D t₁ t₂ a b))
  where open +-*-Solver

module _ {ℓq : Level} {Rq : Set ℓq} {A : Set ℓ} {body : A → PTree E (ExtI E) A} {D : ℕ} {w cT : Event → ℕ} where

  -- the triggered bound along the rounds
  trigRounds : (∀ a → DpW D w (loopStep {R = Rq} body a))
             → (∀ a → Post (λ ls _ → 1 ≤ Σc cT ls) (loopStep {R = Rq} body a))
             → ∀ a {s} → Rounds {Rx = Rq} (loopStep body) (loopStep body a) s
             → #e s ≤ D * Σc cT (labels s) + D + Σc w (labels s)
  trigRounds dp tg a (rLive d eo) =
    ≤-trans (subst₂ (λ x y → x ≤ D + Σc w y) (#e-EvlOnly eo) (labels-EvlOnly eo) (dp a d))
            (+-monoˡ-≤ _ (m≤n+m D _))
  trigRounds dp tg a (rBack {r = r} {s₁ = s₁} {s₂ = s₂} d fr eo rs) =
    subst₂ (λ x ls → x ≤ D * Σc cT ls + D + Σc w ls) (sym (#e-++ s₁ s₂)) (sym (labels-++ s₁ s₂))
      (subst₂ (λ u v → #e s₁ + #e s₂ ≤ D * u + D + v)
        (sym (Σc-++ cT (labels s₁) (labels s₂))) (sym (Σc-++ w (labels s₁) (labels s₂)))
        (trig-arith D _ _ (#e s₁) (#e s₂) _ _
          (subst (λ ls → 1 ≤ Σc cT ls) (labels-EvlOnly eo) (run (tg a) (⟹-append-√ d fr)))
          (subst₂ (λ x y → x ≤ D + Σc w y) (#e-EvlOnly eo) (labels-EvlOnly eo) (dp a d))
          (trigRounds dp tg _ rs)))
  trigRounds dp tg a (rDone {x = x} {s₁ = s₁} d fr eo) =
    subst₂ (λ u v → u ≤ D * Σc cT v + D + Σc w v)
      (sym (trans (#e-++ s₁ (√ x ∷ [])) (+-identityʳ (#e s₁)))) (sym (labels-√ s₁))
      (≤-trans (subst₂ (λ u v → u ≤ D + Σc w v) (#e-EvlOnly eo) (labels-EvlOnly eo) (dp a d))
               (+-monoˡ-≤ _ (m≤n+m D _)))

  -- THE TRIGGERED-LOOP BOUND: every completed round performs a trigger
  trigLoop : (∀ a → DpW D w (loopStep {R = Rq} body a))
           → (∀ a → Post (λ ls _ → 1 ≤ Σc cT ls) (loopStep {R = Rq} body a))
           → ∀ a {s W} → loop {R = Rq} body a ⟹⟨ s ⟩ W
           → #e s ≤ D * Σc cT (labels s) + D + Σc w (labels s)
  trigLoop dp tg a tr = trigRounds dp tg a (rounds {Rx = Rq} (loopStep body) tr)

------------------------------------------------------------------------
-- §7. The iteration potential lemma
------------------------------------------------------------------------

-- every trace of `t` costs at most its credit plus `k`
PfxW : (Event → ℕ) → (Event → ℕ) → ℕ → PTree E (ExtI E) R → Set _
PfxW cost credit k t = ∀ {s W} → t ⟹⟨ s ⟩ W → Σc cost (labels s) ≤ Σc credit (labels s) + k

-- a completed round from `a` that loops back to `a′` pays the potential drop
Back : {A : Set ℓ} → (A → ℕ) → (Event → ℕ) → (Event → ℕ) → A → List Event → A ⊎ R → Set
Back Φ cost credit a ls (inj₁ a′) = Σc cost ls + Φ a′ ≤ Σc credit ls + Φ a
Back Φ cost credit a ls (inj₂ _)  = ⊤

-- arithmetic of a completed round followed by the rest
pot-arith : (c₁ c₂ d₁ d₂ p p′ K : ℕ) → c₁ + p′ ≤ d₁ + p → c₂ ≤ d₂ + p′ + K
          → c₁ + c₂ ≤ (d₁ + d₂) + p + K
pot-arith c₁ c₂ d₁ d₂ p p′ K h₁ h₂ =
  ≤-trans (+-monoʳ-≤ c₁ h₂)
    (≤-trans (≤-≡ (solve 4 (λ c₁ d₂ p′ K → c₁ :+ ((d₂ :+ p′) :+ K) := (c₁ :+ p′) :+ (d₂ :+ K)) refl c₁ d₂ p′ K))
      (≤-trans (+-monoˡ-≤ (d₂ + K) h₁)
        (≤-≡ (solve 4 (λ d₁ p d₂ K → (d₁ :+ p) :+ (d₂ :+ K) := ((d₁ :+ d₂) :+ p) :+ K) refl d₁ p d₂ K))))
  where open +-*-Solver

module _ {ℓx : Level} {Rx : Set ℓx} {A : Set ℓ} {k : A → PTree E (ExtI E) (A ⊎ Rx)}
         (Φ : A → ℕ) (cost credit : Event → ℕ) (K : ℕ)
         (pf : ∀ a → PfxW cost credit (Φ a + K) (k a))
         (bk : ∀ a → Post (Back Φ cost credit a) (k a)) where

  -- the potential bound along the rounds
  potRounds : ∀ a {s} → Rounds {Rx = Rx} k (k a) s
            → Σc cost (labels s) ≤ Σc credit (labels s) + Φ a + K
  potRounds a (rLive {r = r} d eo) =
    subst (λ ls → Σc cost ls ≤ Σc credit ls + Φ a + K) (labels-EvlOnly eo)
      (subst (Σc cost (labels r) ≤_) (sym (+-assoc (Σc credit (labels r)) (Φ a) K)) (pf a d))
  potRounds a (rBack {a′ = a′} {s₁ = s₁} {s₂ = s₂} d fr eo rs) =
    subst (λ ls → Σc cost ls ≤ Σc credit ls + Φ a + K) (sym (labels-++ s₁ s₂))
      (subst₂ (λ u v → u ≤ v + Φ a + K)
        (sym (Σc-++ cost (labels s₁) (labels s₂))) (sym (Σc-++ credit (labels s₁) (labels s₂)))
        (pot-arith (Σc cost (labels s₁)) (Σc cost (labels s₂)) (Σc credit (labels s₁)) (Σc credit (labels s₂))
                   (Φ a) (Φ a′) K
          (subst (λ ls → Back Φ cost credit a ls (inj₁ {B = Rx} a′)) (labels-EvlOnly eo) (run (bk a) (⟹-append-√ d fr)))
          (potRounds a′ rs)))
  potRounds a (rDone {r = r} {s₁ = s₁} d fr eo) =
    subst (λ ls → Σc cost ls ≤ Σc credit ls + Φ a + K) (sym (labels-√ s₁))
      (subst (λ ls → Σc cost ls ≤ Σc credit ls + Φ a + K) (labels-EvlOnly eo)
        (subst (Σc cost (labels r) ≤_) (sym (+-assoc (Σc credit (labels r)) (Φ a) K)) (pf a d)))

  -- THE ITERATION POTENTIAL LEMMA
  iterPot : ∀ a {s W} → iter k a ⟹⟨ s ⟩ W → Σc cost (labels s) ≤ Σc credit (labels s) + Φ a + K
  iterPot a tr = potRounds a (rounds {Rx = Rx} k tr)

------------------------------------------------------------------------
-- §8. Menu rounds for the potential lemma (Stage C Task 4).  A round's
--     obligations are BOOLEAN checks on closed label lists, so for a
--     concrete menu step they reduce to `⊤` and are filled in by eta.
------------------------------------------------------------------------

-- a weight that is zero everywhere sums to zero
Σc-0 : (ls : List Event) → Σc (λ _ → 0) ls ≡ 0
Σc-0 []       = refl
Σc-0 (_ ∷ ls) = Σc-0 ls

-- a trace of a menu is empty, or one menu step followed by a trace of where it went
pch-tr : ∀ {ℓr} {R : Set ℓr} {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))} {s W}
       → pchoice v ⟹⟨ s ⟩ W
       → (s ≡ []) ⊎ Σ[ x ∈ Event ] Σ[ t′ ∈ PTree E (ExtI E) R ] Σ[ s′ ∈ List (Event√ R) ]
                      (pchoice v ─[ ev (evl x) ]─► t′ × s ≡ evl x ∷ s′ × t′ ⟹⟨ s′ ⟩ W)
pch-tr ⟹-refl                      = inj₁ refl
pch-tr (⟹-τ (sSil ()) _)
pch-tr (⟹-τ (sTau refl ()) _)
pch-tr (⟹-ev (sRet ()) _)
pch-tr (⟹-ev {e = evl x} st rest)  = inj₂ (x , _ , _ , st , refl , rest)

-- a menu: every step's continuation meets the post-condition shifted by the step's event
Post-pchoice : ∀ {ℓr} {R : Set ℓr} {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
               {Q : List Event → R → Set}
             → (∀ {x t′} → pchoice v ─[ ev (evl x) ]─► t′ → Post (λ ls r → Q (x ∷ ls) r) t′)
             → Post Q (pchoice v)
Post-pchoice {v = v} {Q} f = post go
  where
    -- by the first step
    go : PostR Q (pchoice v)
    go {s = s} tr with pch-tr tr
    ... | inj₁ eq = ⊥-elim (++∷≢[] s eq)
    ... | inj₂ (x , t′ , s′ , st , eq , rest) with peel {s = s} eq
    ...   | s₀ , refl , refl = run (f st) rest

module _ {ℓx : Level} {Rx : Set ℓx} {A : Set ℓ} {Φ : A → ℕ} {cost credit : Event → ℕ} {K : ℕ} where

  -- what the round from state `a` owes the potential lemma
  RoundPot : A → PTree E (ExtI E) (A ⊎ Rx) → Set _
  RoundPot a t = PfxW cost credit (Φ a + K) t × Post (Back Φ cost credit a) t

  -- what a menu step from state `a`, by event `x`, to `t′` owes
  StepPot : A → Event → PTree E (ExtI E) (A ⊎ Rx) → Set _
  StepPot a x t′ = (∀ {s W} → t′ ⟹⟨ s ⟩ W → Σc cost (x ∷ labels s) ≤ Σc credit (x ∷ labels s) + (Φ a + K))
                 × Post (λ ls r → Back Φ cost credit a (x ∷ ls) r) t′

  -- the boolean prefix check of a closed label list
  okP : A → List Event → Bool
  okP a ls = Σc cost ls ≤ᵇ Σc credit ls + (Φ a + K)

  -- the boolean potential-drop check of a completed round
  okB : A → List Event → A ⊎ Rx → Bool
  okB a ls (inj₁ a′) = (Σc cost ls + Φ a′) ≤ᵇ (Σc credit ls + Φ a)
  okB a ls (inj₂ _)  = true

  -- a passed drop check is the drop
  okB→Back : ∀ {a ls} r → T (okB a ls r) → Back Φ cost credit a ls r
  okB→Back (inj₁ _) ok = ≤ᵇ⇒≤ _ _ ok
  okB→Back (inj₂ _) _  = tt

  -- a menu round, from its steps
  rp-pch : ∀ {a} {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) (A ⊎ Rx)))}
         → (∀ {x t′} → pchoice v ─[ ev (evl x) ]─► t′ → StepPot a x t′) → RoundPot a (pchoice v)
  rp-pch f = (λ tr → case pch-tr tr of λ where
                (inj₁ refl)                           → z≤n
                (inj₂ (_ , _ , _ , st , refl , rest)) → proj₁ (f st) rest)
           , Post-pchoice (λ st → proj₂ (f st))

  -- a terminal round
  rp-done : ∀ {a} {y : Rx} → RoundPot a (Ret (inj₂ y))
  rp-done = (λ tr → case Ret-tr tr of λ { (inj₁ refl) → z≤n ; (inj₂ refl) → z≤n }) , Post-Ret tt

  -- a single-output round
  rp-Out : ∀ {a} {B : Set ℓ} ⦃ _ : DecEq B ⦄ {e : E B} {v : B} {r : A ⊎ Rx}
             {ok₁ : T (okP a (evLabel B e v ∷ []))} {ok₂ : T (okB a (evLabel B e v ∷ []) r)}
         → RoundPot a (e ! v ⟶ Ret r)
  rp-Out {e = e} {v} {r} {ok₁} {ok₂} =
      (λ tr → case out-tr tr of λ where
         (inj₁ refl)              → z≤n
         (inj₂ (_ , refl , rest)) → case Ret-tr rest of λ { (inj₁ refl) → ≤ᵇ⇒≤ _ _ ok₁ ; (inj₂ refl) → ≤ᵇ⇒≤ _ _ ok₁ })
    , Post-Output e v (Post-Ret (okB→Back r ok₂))

  -- a step to a return
  sp-Ret : ∀ {a x} {r : A ⊎ Rx} {ok₁ : T (okP a (x ∷ []))} {ok₂ : T (okB a (x ∷ []) r)} → StepPot a x (Ret r)
  sp-Ret {r = r} {ok₁} {ok₂} =
      (λ tr → case Ret-tr tr of λ { (inj₁ refl) → ≤ᵇ⇒≤ _ _ ok₁ ; (inj₂ refl) → ≤ᵇ⇒≤ _ _ ok₁ })
    , Post-Ret (okB→Back r ok₂)

  -- a step to one output and a return
  sp-Out : ∀ {a x} {B : Set ℓ} ⦃ _ : DecEq B ⦄ {e : E B} {v : B} {r : A ⊎ Rx}
             {ok₁ : T (okP a (x ∷ []))} {ok₂ : T (okP a (x ∷ evLabel B e v ∷ []))}
             {ok₃ : T (okB a (x ∷ evLabel B e v ∷ []) r)}
         → StepPot a x (e ! v ⟶ Ret r)
  sp-Out {e = e} {v} {r} {ok₁} {ok₂} {ok₃} =
      (λ tr → case out-tr tr of λ where
         (inj₁ refl)              → ≤ᵇ⇒≤ _ _ ok₁
         (inj₂ (_ , refl , rest)) → case Ret-tr rest of λ { (inj₁ refl) → ≤ᵇ⇒≤ _ _ ok₂ ; (inj₂ refl) → ≤ᵇ⇒≤ _ _ ok₂ })
    , Post-Output e v (Post-Ret (okB→Back r ok₃))

  -- a step to one prefix (any value) and a return
  sp-⟶ : ∀ {a x} {B : Set ℓ} {e : E B} {r : A ⊎ Rx}
           {ok₁ : T (okP a (x ∷ []))} {ok₂ : ∀ y → T (okP a (x ∷ evLabel B e y ∷ []))}
           {ok₃ : ∀ y → T (okB a (x ∷ evLabel B e y ∷ []) r)}
       → StepPot a x (e ⟶ λ _ → Ret r)
  sp-⟶ {e = e} {r} {ok₁} {ok₂} {ok₃} =
      (λ tr → case pfx-tr tr of λ where
         (inj₁ refl)                  → ≤ᵇ⇒≤ _ _ ok₁
         (inj₂ (y , _ , refl , rest)) → case Ret-tr rest of λ { (inj₁ refl) → ≤ᵇ⇒≤ _ _ (ok₂ y) ; (inj₂ refl) → ≤ᵇ⇒≤ _ _ (ok₂ y) })
    , Post-⟶ e (λ y → Post-Ret (okB→Back r (ok₃ y)))

  -- `sp-Out` with its checks given as PROOFS (for weights that do not reduce to numerals, e.g. list lengths)
  sp-Out≤ : ∀ {a x} {B : Set ℓ} ⦃ _ : DecEq B ⦄ {e : E B} {v : B} {r : A ⊎ Rx}
          → Σc cost (x ∷ []) ≤ Σc credit (x ∷ []) + (Φ a + K)
          → Σc cost (x ∷ evLabel B e v ∷ []) ≤ Σc credit (x ∷ evLabel B e v ∷ []) + (Φ a + K)
          → Back Φ cost credit a (x ∷ evLabel B e v ∷ []) r
          → StepPot a x (e ! v ⟶ Ret r)
  sp-Out≤ {e = e} {v} ok₁ ok₂ ok₃ =
      (λ tr → case out-tr tr of λ where
         (inj₁ refl)              → ok₁
         (inj₂ (_ , refl , rest)) → case Ret-tr rest of λ { (inj₁ refl) → ok₂ ; (inj₂ refl) → ok₂ })
    , Post-Output e v (Post-Ret ok₃)

-- THE POTENTIAL LEMMA from per-state round obligations (potential and constant as one offset)
potIter : ∀ {ℓx} {Rx : Set ℓx} {A : Set ℓ} {k : A → PTree E (ExtI E) (A ⊎ Rx)}
          (Φ : A → ℕ) (cost credit : Event → ℕ) (K : ℕ)
        → (∀ a → RoundPot {Φ = Φ} {cost} {credit} {K} a (k a))
        → ∀ a {s W} → iter k a ⟹⟨ s ⟩ W → Σc cost (labels s) ≤ Σc credit (labels s) + (Φ a + K)
potIter Φ cost credit K rp a {s} tr =
  subst (Σc cost (labels s) ≤_) (+-assoc (Σc credit (labels s)) (Φ a) K) (iterPot Φ cost credit K (λ a → proj₁ (rp a)) (λ a → proj₂ (rp a)) a tr)

-- a bound with no slack
slack0 : ∀ {c d : Event → ℕ} {ls} → Σc c ls ≤ Σc d ls + 0 → Σc c ls ≤ Σc d ls
slack0 {c} {d} {ls} = subst (Σc c ls ≤_) (+-identityʳ _)

-- a bound by the zero weight: the weight sums to zero
none0 : ∀ {c : Event → ℕ} {ls} → Σc c ls ≤ Σc (λ _ → 0) ls + 0 → Σc c ls ≡ 0
none0 {c} {ls} h = n≤0⇒n≡0 (subst (Σc c ls ≤_) (cong (_+ 0) (Σc-0 ls)) h)
