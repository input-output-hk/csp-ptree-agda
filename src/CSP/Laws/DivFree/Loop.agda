{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- The guarded-loop accessibility lemma (named in `CSP.Laws.DivFree.Closure`
-- 33-40), at every reachable state and modulo H.
--
--   `loop0 Skip` diverges: the body returns at once and the loop re-enters by
--   a τ.  The missing hypothesis is that a ROUND cannot finish on τ/H steps
--   alone — `Guarded H (body a)`: no `ret` is reachable from a round start by
--   modulo-H steps.  Mid-round states (after a visible non-H event) need only
--   `MAccR H`, because the loop-back lands on a fresh guarded round start.
--
--   * `>>=`  : `MAccR->>=`, `Guarded->>=` (bind adds no τ of its own)
--   * `iter` : `MAccR-iter` (round starts may not return `inj₁`)
--   * `loop` : `MAccR-loop`, and the τ form `τ-AccReach-loop` (H = ∅ES)
--
-- No `postulate`, no `NON_TERMINATING`, no sized types.
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Class.DecEq using (DecEq; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Process_Trees

module CSP.Laws.DivFree.Loop {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Deadlock {E = E} {I = ExtI E} using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Semantics.DivergenceFree {E = E} {I = ExtI E}
  using (τ-AccReach; ret→no-τ)
open import CSP.Laws.Traces.TraceLawsBind E-≟ using (bindV-elim)
open import CSP.Laws.DivFree.Closure E-≟ using (bind-τ-elim; BindτR; bτL; bτK)
open import CSP.Laws.DivFree.ModAcc E-≟
open import CSP.Laws.DivFree.Reach E-≟ using (MAccR-Ret)

private
  variable
    ℓr ℓs : Level
    R : Set ℓr
    S : Set ℓs

------------------------------------------------------------------------
-- §1. Guardedness: no return value of the `Bad` kind is reachable by
--     modulo-H steps alone (inductive, so it is ALSO an accessibility proof)
------------------------------------------------------------------------

-- t can make only finitely many modulo-H steps, and none of them reaches a `Bad` return
data NoRetBy {ℓr} {R : Set ℓr} (Bad : R → Set) (H : EventSet) (t : PTree E (ExtI E) R)
     : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  noRet : (∀ {r} → PTree.force t ≡ ret r → ¬ Bad r)
        → (∀ {t′} → ModAStep H t t′ → NoRetBy Bad H t′)
        → NoRetBy Bad H t

-- the guard's first component: the state itself is not a bad return
noRet-here : {Bad : R → Set} {H : EventSet} {t : PTree E (ExtI E) R}
           → NoRetBy Bad H t → ∀ {r} → PTree.force t ≡ ret r → ¬ Bad r
noRet-here (noRet nr _) = nr

-- every return is bad: the loop-body guard
Guarded : ∀ {ℓr} {R : Set ℓr} → EventSet → PTree E (ExtI E) R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
Guarded = NoRetBy (λ _ → ⊤)

-- only a loop-back (`inj₁`) return is bad: the `iter`-body guard
Looping : {A : Set ℓ} → A ⊎ R → Set
Looping (inj₁ _) = ⊤
Looping (inj₂ _) = ⊥

-- a guarded state is accessible
NoRetBy→MAcc : {Bad : R → Set} {H : EventSet} {t : PTree E (ExtI E) R}
             → NoRetBy Bad H t → MAcc H t
NoRetBy→MAcc (noRet _ f) = macc λ st → NoRetBy→MAcc (f st)

-- a weaker badness predicate keeps the guard (so `Guarded` gives `NoRetBy Looping`)
NoRetBy-mono : {Bad Bad′ : R → Set} {H : EventSet} {t : PTree E (ExtI E) R}
             → (∀ r → Bad′ r → Bad r) → NoRetBy Bad H t → NoRetBy Bad′ H t
NoRetBy-mono w (noRet nr f) = noRet (λ eq b → nr eq (w _ b)) (λ st → NoRetBy-mono w (f st))

-- a return that is not bad is guarded: `Ret r` has no step at all
NoRetBy-Ret : {Bad : R → Set} {H : EventSet} {r : R} → ¬ Bad r → NoRetBy Bad H (Ret r)
NoRetBy-Ret nb = noRet (λ { refl → nb }) λ where
  (maτ st)            → ⊥-elim (ret→no-τ refl st)
  (maE _ (sVis () _))

-- `ret` and `react` are distinct node kinds; `nothing` is not `just`
private
  ret≢react : ∀ {r : R} {w τc} → _≡_ {A = NodeKind E (ExtI E) R} (ret r) (react w τc) → ⊥
  ret≢react ()
  case-nothing : ∀ {X : Set ℓr} {x : X} {Y : Set ℓs} → nothing ≡ just x → Y
  case-nothing ()

-- a stable menu node is guarded when every continuation entered on an H-event is
Guarded-react : {H : EventSet} {t : PTree E (ExtI E) R}
                {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
              → PTree.force t ≡ react v ∅t
              → (∀ {B} {e : E B} {a t′} → H .mem (B , e) a → v (B , e) a ≡ just t′ → Guarded H t′)
              → Guarded H t
Guarded-react {t = t} eqf gH = noRet (λ eq _ → ret≢react (trans (sym eq) eqf)) λ where
  (maτ (sSil eqs))    → ⊥-elim (sil≢react (trans (sym eqs) eqf))
  (maτ (sTau {i = i} {a = a} eqr br)) →
     case-nothing (trans (sym (cong (λ g → g i a) (proj₂ (react-injective (trans (sym eqr) eqf))))) br)
  (maE m∈ (sVis {at = at} {a = a} eqr br)) →
     gH m∈ (trans (sym (cong (λ g → g at a) (proj₁ (react-injective (trans (sym eqr) eqf))))) br)

-- a stable menu node is accessible at every reachable state when every continuation is
MAccR-react : {H : EventSet} {t : PTree E (ExtI E) R}
              {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
            → PTree.force t ≡ react v ∅t
            → (∀ {at a t′} → v at a ≡ just t′ → MAccR H t′)
            → MAccR H t
MAccR-react eqf rc ∖√-refl = macc λ where
  (maτ (sSil eqs))    → ⊥-elim (sil≢react (trans (sym eqs) eqf))
  (maτ (sTau {i = i} {a = a} eqr br)) →
     case-nothing (trans (sym (cong (λ g → g i a) (proj₂ (react-injective (trans (sym eqr) eqf))))) br)
  (maE m∈ (sVis {at = at} {a = a} eqr br)) →
     rc (trans (sym (cong (λ g → g at a) (proj₁ (react-injective (trans (sym eqr) eqf))))) br) ∖√-refl
MAccR-react eqf rc (∖√-τ (sSil eqs) r) = ⊥-elim (sil≢react (trans (sym eqs) eqf))
MAccR-react eqf rc (∖√-τ (sTau {i = i} {a = a} eqr br) r) =
  case-nothing (trans (sym (cong (λ g → g i a) (proj₂ (react-injective (trans (sym eqr) eqf))))) br)
MAccR-react eqf rc (∖√-ev (sVis {at = at} {a = a} eqr br) r) =
  rc (trans (sym (cong (λ g → g at a) (proj₁ (react-injective (trans (sym eqr) eqf))))) br) r

-- `Stop` offers nothing and has no τ
MAccR-Stop : {H : EventSet} → MAccR H (Stop {R = R})
MAccR-Stop = MAccR-react refl (λ ())

-- a fired prefix offer continues with `P x`
Prefix-cont-inv : {A : Set ℓ} (e : E A) (P : A → PTree E (ExtI E) R)
                  {at : AnyTypes E} {a : proj₁ at} {t′ : PTree E (ExtI E) R}
                → Prefix-cont e P at a ≡ just t′ → Σ[ x ∈ A ] t′ ≡ P x
Prefix-cont-inv {A = A} e P {at} {a} eq with E-≟ (A , e) at
... | yes refl = a , sym (just-injective eq)
... | no _     = case-nothing eq

-- a fired output offer continues with `P`
Output-cont-inv : {A : Set ℓ} ⦃ _ : DecEq A ⦄ (e : E A) (v : A) (P : PTree E (ExtI E) R)
                  {at : AnyTypes E} {a : proj₁ at} {t′ : PTree E (ExtI E) R}
                → Output-cont e v P at a ≡ just t′ → t′ ≡ P
Output-cont-inv {A = A} e v P {at} {a} eq with E-≟ (A , e) at
... | no _     = case-nothing eq
... | yes refl with a ≟ v
...   | yes _ = sym (just-injective eq)
...   | no _  = case-nothing eq

-- prefix `e ⟶ P`
MAccR-⟶ : {H : EventSet} {A : Set ℓ} (e : E A) {P : A → PTree E (ExtI E) R}
        → (∀ x → MAccR H (P x)) → MAccR H (e ⟶ P)
MAccR-⟶ e {P} rp = MAccR-react refl λ eq → go (Prefix-cont-inv e P eq)
  where
    -- the continuation is some `P x`
    go : ∀ {t′} → Σ[ x ∈ _ ] t′ ≡ P x → MAccR _ t′
    go (x , refl) = rp x

-- constant prefix `e ⟶₀ P`
MAccR-⟶₀ : {H : EventSet} {A : Set ℓ} (e : E A) {P : PTree E (ExtI E) R}
         → MAccR H P → MAccR H (e ⟶₀ P)
MAccR-⟶₀ e rp = MAccR-⟶ e (λ _ → rp)

-- output `e ! v ⟶ P`
MAccR-Output : {H : EventSet} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (e : E A) (v : A) {P : PTree E (ExtI E) R}
             → MAccR H P → MAccR H (e ! v ⟶ P)
MAccR-Output e v {P} rp = MAccR-react refl λ eq → go (Output-cont-inv e v P eq)
  where
    -- the continuation is `P`
    go : ∀ {t′} → t′ ≡ P → MAccR _ t′
    go refl = rp

-- a prefix is guarded when, for every H-value it may carry, its continuation is
Guarded-⟶ : {H : EventSet} {A : Set ℓ} (e : E A) {P : A → PTree E (ExtI E) R}
          → (∀ x → H .mem (A , e) x → Guarded H (P x)) → Guarded H (e ⟶ P)
Guarded-⟶ {H = H} {A} e {P} gp = Guarded-react refl λ {B} {e′} {a} m∈ eq → go m∈ eq
  where
    -- the fired offer is `e` itself, carrying some x
    go : ∀ {B} {e′ : E B} {a t′} → H .mem (B , e′) a → Prefix-cont e P (B , e′) a ≡ just t′ → Guarded H t′
    go {B} {e′} {a} m∈ eq with E-≟ (A , e) (B , e′)
    ... | yes refl = subst (Guarded H) (just-injective eq) (gp a m∈)
    ... | no _     = case-nothing eq

-- an output on a channel outside H is guarded outright
Guarded-Output-vis : {H : EventSet} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (e : E A) (v : A) {P : PTree E (ExtI E) R}
                   → (∀ x → ¬ H .mem (A , e) x) → Guarded H (e ! v ⟶ P)
Guarded-Output-vis {H = H} {A} e v {P} ¬h = Guarded-react refl λ {B} {e′} {a} m∈ eq → go m∈ eq
  where
    -- the fired offer is `e` itself, which is not in H
    go : ∀ {B} {e′ : E B} {a t′} → H .mem (B , e′) a → Output-cont e v P (B , e′) a ≡ just t′ → Guarded H t′
    go {B} {e′} {a} m∈ eq with E-≟ (A , e) (B , e′)
    ... | yes refl = ⊥-elim (¬h a m∈)
    ... | no _     = case-nothing eq

-- a prefix on a channel outside H is guarded outright
Guarded-⟶-vis : {H : EventSet} {A : Set ℓ} (e : E A) {P : A → PTree E (ExtI E) R}
              → (∀ x → ¬ H .mem (A , e) x) → Guarded H (e ⟶ P)
Guarded-⟶-vis e ¬h = Guarded-⟶ e (λ x m∈ → ⊥-elim (¬h x m∈))

------------------------------------------------------------------------
-- §2. Bind
------------------------------------------------------------------------

-- inversion result for a visible step out of `P >>= k`
data BindevR {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
             (k : R → PTree E (ExtI E) S) (P : PTree E (ExtI E) R)
             (M : PTree E (ExtI E) S) (e : Event) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr ⊔ ℓs) where
  beL : (c : PTree E (ExtI E) R) → P ─[ ev (evl e) ]─► c → M ≡ c >>= k → BindevR k P M e
  beK : (r : R) → PTree.force P ≡ ret r → (k r) ─[ ev (evl e) ]─► M → BindevR k P M e

-- a visible step of `P >>= k` is one of P (lifted) or, once P has returned, one of `k r`
bind-ev-elim : (k : R → PTree E (ExtI E) S) (P : PTree E (ExtI E) R)
               {M : PTree E (ExtI E) S} {e : Event}
             → (P >>= k) ─[ ev (evl e) ]─► M → BindevR k P M e
bind-ev-elim k P (sVis {at = at} {a = a} eqr br) with PTree.force P in eqP | eqr
... | ret r      | eqr′ = beK r eqP (sVis eqr′ br)
... | sil c      | ()
... | react v τc | refl with bindV-elim k (react v τc) {at = at} {a = a} br
...   | c , veq , refl = beL c (sVis eqP veq) refl

-- a bind forced to `ret` comes from P forced to `ret`
bind-ret-inv : (k : R → PTree E (ExtI E) S) (P : PTree E (ExtI E) R) {s : S}
             → PTree.force (P >>= k) ≡ ret s → Σ[ r ∈ R ] PTree.force P ≡ ret r
bind-ret-inv k P eq with PTree.force P in eqP | eq
... | ret r      | _  = r , refl
... | sil c      | ()
... | react v τc | ()

-- root accessibility of a bind
MAcc->>= : {H : EventSet} {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
         → MAcc H P → (∀ r → MAcc H (k r)) → MAcc H (P >>= k)
-- a decoded τ of the bind
MAcc->>=-τ : {H : EventSet} {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S} {M : PTree E (ExtI E) S}
           → MAcc H P → (∀ r → MAcc H (k r)) → BindτR k P M → MAcc H M
-- a decoded H-step of the bind
MAcc->>=-ev : {H : EventSet} {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S} {M : PTree E (ExtI E) S}
              {B : Set ℓ} {e : E B} {a : B}
            → MAcc H P → (∀ r → MAcc H (k r)) → H .mem (B , e) a
            → BindevR k P M (evLabel B e a) → MAcc H M

MAcc->>= {P = P} {k} ap ak = macc λ where
  (maτ st)    → MAcc->>=-τ ap ak (bind-τ-elim k P st)
  (maE m∈ st) → MAcc->>=-ev ap ak m∈ (bind-ev-elim k P st)

MAcc->>=-τ (macc f) ak (bτL c st refl) = MAcc->>= (f (maτ st)) ak
MAcc->>=-τ ap       ak (bτK r _ st)    = maccSub (ak r) (maτ st)

MAcc->>=-ev (macc f) ak m∈ (beL c st refl) = MAcc->>= (f (maE m∈ st)) ak
MAcc->>=-ev ap       ak m∈ (beK r _ st)    = maccSub (ak r) (maE m∈ st)

-- reachable states of a bind: residuals of P bound to k, or states of some `k r`
MAccR->>= : {H : EventSet} {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
          → MAccR H P → (∀ r → MAccR H (k r)) → MAccR H (P >>= k)
-- the run after a τ / a visible step of the bind
MAccR->>=-τ : {H : EventSet} {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
              {M W : PTree E (ExtI E) S} {s : List Event}
            → MAccR H P → (∀ r → MAccR H (k r)) → BindτR k P M → M ⟹∖√⟨ s ⟩ W → MAcc H W
MAccR->>=-ev : {H : EventSet} {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
               {M W : PTree E (ExtI E) S} {s : List Event} {e : Event}
             → MAccR H P → (∀ r → MAccR H (k r)) → BindevR k P M e → M ⟹∖√⟨ s ⟩ W → MAcc H W

MAccR->>= rp rk ∖√-refl = MAcc->>= (rp ∖√-refl) (λ r → rk r ∖√-refl)
MAccR->>= {P = P} {k} rp rk (∖√-τ st r)  = MAccR->>=-τ rp rk (bind-τ-elim k P st) r
MAccR->>= {P = P} {k} rp rk (∖√-ev st r) = MAccR->>=-ev rp rk (bind-ev-elim k P st) r

MAccR->>=-τ rp rk (bτL c st refl) r = MAccR->>= (λ r′ → rp (∖√-τ st r′)) rk r
MAccR->>=-τ rp rk (bτK x _ st)    r = rk x (∖√-τ st r)

MAccR->>=-ev rp rk (beL c st refl) r = MAccR->>= (λ r′ → rp (∖√-ev st r′)) rk r
MAccR->>=-ev rp rk (beK x _ st)    r = rk x (∖√-ev st r)

-- a guarded P never hands over to k on modulo-H steps, so the bind is guarded for ANY `Bad`
Guarded->>= : {H : EventSet} {Bad : S → Set} {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
            → Guarded H P → NoRetBy Bad H (P >>= k)
-- a decoded τ / H-step of the guarded bind
Guarded->>=-τ : {H : EventSet} {Bad : S → Set} {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
                {M : PTree E (ExtI E) S}
              → Guarded H P → BindτR k P M → NoRetBy Bad H M
Guarded->>=-ev : {H : EventSet} {Bad : S → Set} {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
                 {M : PTree E (ExtI E) S} {B : Set ℓ} {e : E B} {a : B}
               → Guarded H P → H .mem (B , e) a → BindevR k P M (evLabel B e a) → NoRetBy Bad H M

Guarded->>= {P = P} {k} g =
  noRet (λ eq _ → noRet-here g (proj₂ (bind-ret-inv k P eq)) tt) λ where
    (maτ st)    → Guarded->>=-τ g (bind-τ-elim k P st)
    (maE m∈ st) → Guarded->>=-ev g m∈ (bind-ev-elim k P st)

Guarded->>=-τ (noRet nr f) (bτL c st refl) = Guarded->>= (f (maτ st))
Guarded->>=-τ (noRet nr f) (bτK r eq _)    = ⊥-elim (nr eq tt)

Guarded->>=-ev (noRet nr f) m∈ (beL c st refl) = Guarded->>= (f (maE m∈ st))
Guarded->>=-ev (noRet nr f) m∈ (beK r eq _)    = ⊥-elim (nr eq tt)

------------------------------------------------------------------------
-- §3. Iteration
------------------------------------------------------------------------

-- inversion result for a τ out of `iter-bind t k`
data IterτR {ℓr} {A : Set ℓ} {R : Set ℓr}
            (t : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
            (M : PTree E (ExtI E) R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  itτ    : (t′ : PTree E (ExtI E) (A ⊎ R)) → t ─[ τ ]─► t′ → M ≡ iter-bind t′ k → IterτR t k M
  itBack : (a′ : A) → PTree.force t ≡ ret (inj₁ a′) → M ≡ iter k a′ → IterτR t k M

-- a bound iterT branch reads back to the body's τ-branch
iterT-elim : ∀ {A : Set ℓ} (k : A → PTree E (ExtI E) (A ⊎ R)) (nP : NodeKind E (ExtI E) (A ⊎ R))
               {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
           → iterT k nP i a ≡ just M
           → Σ[ t′ ∈ PTree E (ExtI E) (A ⊎ R) ] (viewT nP i a ≡ just t′ × M ≡ iter-bind t′ k)
iterT-elim k nP {i} {a} eq with viewT nP i a
... | just t′ = t′ , refl , sym (just-injective eq)
... | nothing = case-nothing eq

-- a bound iterV branch reads back to the body's visible offer
iterV-elim : ∀ {A : Set ℓ} (k : A → PTree E (ExtI E) (A ⊎ R)) (nP : NodeKind E (ExtI E) (A ⊎ R))
               {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
           → iterV k nP at a ≡ just M
           → Σ[ t′ ∈ PTree E (ExtI E) (A ⊎ R) ] (viewV nP at a ≡ just t′ × M ≡ iter-bind t′ k)
iterV-elim k nP {at} {a} eq with viewV nP at a
... | just t′ = t′ , refl , sym (just-injective eq)
... | nothing = case-nothing eq

-- a τ of `iter-bind t k` is a τ of t, or the loop-back after t returned `inj₁ a′`
iter-τ-elim : ∀ {A : Set ℓ} (t : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
              {M : PTree E (ExtI E) R}
            → iter-bind t k ─[ τ ]─► M → IterτR t k M
iter-τ-elim t k (sSil eqf) with PTree.force t in eqt | eqf
... | ret (inj₁ a′) | refl = itBack a′ eqt refl
... | ret (inj₂ r)  | ()
... | sil c         | refl = itτ c (sSil eqt) refl
... | react v τc    | ()
iter-τ-elim t k (sTau {i = i} {a = a} eqf br) with PTree.force t in eqt | eqf
... | ret (inj₁ _)  | ()
... | ret (inj₂ _)  | ()
... | sil _         | ()
... | react v τc    | refl with iterT-elim k (react v τc) {i = i} {a = a} br
...   | t′ , veq , refl = itτ t′ (sTau eqt veq) refl

-- a visible step of `iter-bind t k` is one of t
iter-ev-elim : ∀ {A : Set ℓ} (t : PTree E (ExtI E) (A ⊎ R)) (k : A → PTree E (ExtI E) (A ⊎ R))
               {M : PTree E (ExtI E) R} {e : Event}
             → iter-bind t k ─[ ev (evl e) ]─► M
             → Σ[ t′ ∈ PTree E (ExtI E) (A ⊎ R) ] (t ─[ ev (evl e) ]─► t′ × M ≡ iter-bind t′ k)
iter-ev-elim t k (sVis {at = at} {a = a} eqf br) with PTree.force t in eqt | eqf
... | ret (inj₁ _)  | ()
... | ret (inj₂ _)  | ()
... | sil _         | ()
... | react v τc    | refl with iterV-elim k (react v τc) {at = at} {a = a} br
...   | t′ , veq , refl = t′ , sVis eqt veq , refl

module _ {A : Set ℓ} {H : EventSet} {k : A → PTree E (ExtI E) (A ⊎ R)} where

  -- a round start: no loop-back is reachable on modulo-H steps
  MAcc-iter-start : {u : PTree E (ExtI E) (A ⊎ R)} → NoRetBy Looping H u → MAcc H (iter-bind u k)
  -- a decoded step from a round start
  MAcc-iter-start-τ : {u : PTree E (ExtI E) (A ⊎ R)} {M : PTree E (ExtI E) R}
                    → NoRetBy Looping H u → IterτR u k M → MAcc H M
  MAcc-iter-start-ev : {u : PTree E (ExtI E) (A ⊎ R)} {M : PTree E (ExtI E) R} {B : Set ℓ} {e : E B} {a : B}
                     → NoRetBy Looping H u → H .mem (B , e) a
                     → Σ[ u′ ∈ _ ] (u ─[ ev (evl (evLabel B e a)) ]─► u′ × M ≡ iter-bind u′ k) → MAcc H M

  MAcc-iter-start {u} g = macc λ where
    (maτ st)    → MAcc-iter-start-τ g (iter-τ-elim u k st)
    (maE m∈ st) → MAcc-iter-start-ev g m∈ (iter-ev-elim u k st)

  MAcc-iter-start-τ (noRet nr f) (itτ u′ st refl)    = MAcc-iter-start (f (maτ st))
  MAcc-iter-start-τ (noRet nr f) (itBack a′ eq refl) = ⊥-elim (nr eq tt)

  MAcc-iter-start-ev (noRet nr f) m∈ (u′ , st , refl) = MAcc-iter-start (f (maE m∈ st))

  -- mid-round: accessibility of the residual, plus guarded round starts
  MAcc-iter : {t : PTree E (ExtI E) (A ⊎ R)} → MAcc H t → (∀ a → NoRetBy Looping H (k a))
            → MAcc H (iter-bind t k)
  -- a decoded step from mid-round
  MAcc-iter-τ : {t : PTree E (ExtI E) (A ⊎ R)} {M : PTree E (ExtI E) R}
              → MAcc H t → (∀ a → NoRetBy Looping H (k a)) → IterτR t k M → MAcc H M
  MAcc-iter-ev : {t : PTree E (ExtI E) (A ⊎ R)} {M : PTree E (ExtI E) R} {B : Set ℓ} {e : E B} {a : B}
               → MAcc H t → (∀ a → NoRetBy Looping H (k a)) → H .mem (B , e) a
               → Σ[ t′ ∈ _ ] (t ─[ ev (evl (evLabel B e a)) ]─► t′ × M ≡ iter-bind t′ k) → MAcc H M

  MAcc-iter {t} at gk = macc λ where
    (maτ st)    → MAcc-iter-τ at gk (iter-τ-elim t k st)
    (maE m∈ st) → MAcc-iter-ev at gk m∈ (iter-ev-elim t k st)

  MAcc-iter-τ (macc f) gk (itτ t′ st refl)    = MAcc-iter (f (maτ st)) gk
  MAcc-iter-τ at       gk (itBack a′ _ refl)  = MAcc-iter-start (gk a′)

  MAcc-iter-ev (macc f) gk m∈ (t′ , st , refl) = MAcc-iter (f (maE m∈ st)) gk

  -- reachable states of an iteration: `iter-bind t′ k` with t′ reachable from some `k a`
  MAccR-iter-bind : {t : PTree E (ExtI E) (A ⊎ R)}
                  → MAccR H t → (∀ a → NoRetBy Looping H (k a)) → (∀ a → MAccR H (k a))
                  → MAccR H (iter-bind t k)
  -- the run after a τ / a visible step
  MAccR-iter-τ : {t : PTree E (ExtI E) (A ⊎ R)} {M W : PTree E (ExtI E) R} {s : List Event}
               → MAccR H t → (∀ a → NoRetBy Looping H (k a)) → (∀ a → MAccR H (k a))
               → IterτR t k M → M ⟹∖√⟨ s ⟩ W → MAcc H W
  MAccR-iter-ev : {t : PTree E (ExtI E) (A ⊎ R)} {M W : PTree E (ExtI E) R} {s : List Event} {e : Event}
                → MAccR H t → (∀ a → NoRetBy Looping H (k a)) → (∀ a → MAccR H (k a))
                → Σ[ t′ ∈ _ ] (t ─[ ev (evl e) ]─► t′ × M ≡ iter-bind t′ k) → M ⟹∖√⟨ s ⟩ W → MAcc H W

  MAccR-iter-bind rt gk rk ∖√-refl = MAcc-iter (rt ∖√-refl) gk
  MAccR-iter-bind {t} rt gk rk (∖√-τ st r)  = MAccR-iter-τ rt gk rk (iter-τ-elim t k st) r
  MAccR-iter-bind {t} rt gk rk (∖√-ev st r) = MAccR-iter-ev rt gk rk (iter-ev-elim t k st) r

  MAccR-iter-τ rt gk rk (itτ t′ st refl)   r = MAccR-iter-bind (λ r′ → rt (∖√-τ st r′)) gk rk r
  MAccR-iter-τ rt gk rk (itBack a′ _ refl) r = MAccR-iter-bind (rk a′) gk rk r

  MAccR-iter-ev rt gk rk (t′ , st , refl) r = MAccR-iter-bind (λ r′ → rt (∖√-ev st r′)) gk rk r

  -- THE ITERATION LEMMA: guarded round starts + reachable accessibility of every body
  MAccR-iter : (∀ a → NoRetBy Looping H (k a)) → (∀ a → MAccR H (k a)) → ∀ a → MAccR H (iter k a)
  MAccR-iter gk rk a = MAccR-iter-bind (rk a) gk rk

------------------------------------------------------------------------
-- §4. The forever loop
------------------------------------------------------------------------

-- `loop`'s where-bound round, named (definitionally what `loop` iterates)
loopStep : ∀ {A : Set ℓ} → (A → PTree E (ExtI E) A) → A → PTree E (ExtI E) (A ⊎ R)
loopStep body a = body a >>= λ a′ → Ret (inj₁ a′)

-- sanity: `loop` IS `iter` of `loopStep`, by `refl`
loop-unfold : ∀ {A : Set ℓ} (body : A → PTree E (ExtI E) A) (a : A)
            → loop {R = R} body a ≡ iter (loopStep body) a
loop-unfold body a = refl

-- THE GUARDED-LOOP LEMMA (modulo H): every round start guarded, every body state accessible
MAccR-loop : ∀ {A : Set ℓ} {H : EventSet} (body : A → PTree E (ExtI E) A)
           → (∀ a → Guarded H (body a)) → (∀ a → MAccR H (body a))
           → ∀ a → MAccR H (loop {R = R} body a)
MAccR-loop body g rb =
  MAccR-iter (λ a → Guarded->>= (g a))
             (λ a → MAccR->>= (rb a) (λ a′ → MAccR-Ret (inj₁ a′)))

-- … the τ form (H = ∅ES): the shape Stage C's loop threads discharge
τ-AccReach-loop : ∀ {A : Set ℓ} (body : A → PTree E (ExtI E) A)
                → (∀ a → Guarded ∅ES (body a)) → (∀ a → τ-AccReach (body a))
                → ∀ a → τ-AccReach (loop {R = R} body a)
τ-AccReach-loop body g rb a =
  MAccR→τ-AccReach (MAccR-loop body g (λ a′ → τ-AccReach→MAccR∅ (rb a′)) a)

-- the stateless loop `loop0`
MAccR-loop0 : ∀ {H : EventSet} {body : PTree E (ExtI E) (⊤ {ℓ})}
            → Guarded H body → MAccR H body → MAccR H (loop0 {R = R} body)
MAccR-loop0 {body = body} g rb = MAccR-loop (λ _ → body) (λ _ → g) (λ _ → rb) tt
