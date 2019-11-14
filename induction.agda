open import Agda.Primitive
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty using (⊥; ⊥-elim)

open import exp

type : {i : Level} → {T : Set i} → T → Set i
type {i} {T} t = T

assertInEmpty : {T : ctxType ∅ → Set i} → Exp ∅ T → Exp ∅ T
assertInEmpty e = e

data Lift : Set predi → Set i where
  lift : {T : Set predi} → T → Lift T

trueℕ : Exp ∅ (λ _ → (ℕ → ℕ → ℕ))
trueℕ = Lambda (Lambda (WeakerCtx InCtx)) -- λ x y . y

falseℕ : Exp ∅ (λ _ → (ℕ → ℕ → ℕ))
falseℕ = Lambda (Lambda InCtx) -- λ x y . x

𝟚 : Set i
𝟚 = (T : Set predi) → Lift T → Lift T → Lift T

false : 𝟚
false _ _ t = t

true : 𝟚
true _ t _ = t

e𝟚 : Set j
e𝟚 = Exp ∅ (λ _ → 𝟚)

efalse : e𝟚
efalse = Lambda (Lambda (Lambda InCtx)) -- λ T a b . b

etrue : e𝟚
etrue = Lambda (Lambda (Lambda (WeakerCtx InCtx)))-- λ T a b . a



idtoequiv : {i : Level} → {A B : Set i} → A ≡ B → A → B
idtoequiv refl a = a

transport : {i : Level} → {A : Set i} → {x y : A} → (P : A → Set i) → x ≡ y → P x → P y
transport P refl p = p

-- lemma1 : ∀ {C} → ∀ {A} → ¬ (λ (c : C) → (x : A c) → A c) ≡ (λ _ → 𝟚)
-- lemma1 ()
-- lemma2' : ¬ (Set₁ ≡ 𝟚)
-- lemma2' refl = ?
-- lemma2 : ¬ (λ _ → Set₁) ≡ (λ _ → 𝟚)
-- lemma2 p = lemma2' {!   !}
-- lemma3 : ∀ {C} → ∀ {A} → ¬ (λ (c : C) → (x : A c) → A c) ≡ (λ _ → 𝟚)
-- lemma3 ()
-- lemma4 : ∀ {C} → ∀ {A} → ¬ (λ (c : C) → (x : A c) → A c) ≡ (λ _ → 𝟚)
-- lemma4 ()
-- lemma5 : ∀ {C} → ∀ {A} → ¬ (λ (c : C) → (x : A c) → A c) ≡ (λ _ → 𝟚)
-- lemma5 ()
-- lemma6 : ∀ {C} → ∀ {A} → ¬ (λ (c : C) → (x : A c) → A c) ≡ (λ _ → 𝟚)
-- lemma6 ()
-- lemma7 : ∀ {C} → ∀ {A} → ¬ (λ (c : C) → (x : A c) → A c) ≡ (λ _ → 𝟚)
-- lemma7 ()

ind-𝟚-gen : (C : e𝟚 → Set) → C efalse → C etrue → {T : ctxType ∅ → Set i} →
  (x : Exp ∅ T) → (Σ (T ≡ (λ _ → 𝟚)) (λ p → C (transport (λ T → Exp ∅ T) p x))) ⊎ ¬ (T ≡ (λ _ → 𝟚))
ind-𝟚-gen C ct cf (Lambda e) = {!   !}
ind-𝟚-gen C ct cf (App e e₂) = {!   !}
ind-𝟚-gen C ct cf 𝓤 = inj₂ {!   !}
ind-𝟚-gen C ct cf (Π A B) = {!   !}

ind-𝟚-impl : (C : e𝟚 → Set) → C efalse → C etrue → (x : e𝟚) →
  ((Σ ((λ _ → 𝟚) ≡ (λ _ → 𝟚)) (λ p → C (transport (λ T → Exp ∅ T) p x))) ⊎ ¬ ((λ _ → 𝟚) ≡ (λ _ → 𝟚))) →
  C x
ind-𝟚-impl C cf ct x = {!   !}
-- ill come back to this later, above function is source of error

-- 𝟚 induction principle:
-- ind-𝟚 : (C : e𝟚 → Set) → C efalse → C etrue → (x : e𝟚) → C x
-- ind-𝟚 C cf ct x = ind-𝟚-impl C cf ct x (ind-𝟚-gen C cf ct x)
