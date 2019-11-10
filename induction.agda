open import Agda.Primitive
open import Data.Sum
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty using (⊥; ⊥-elim)

open import exp

type : {i : Level} → {T : Set i} → T → Set i
type {i} {T} t = T

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

-- 𝟚 induction principle:
ind-𝟚 : (C : e𝟚 → Set) → C efalse → C etrue → (x : e𝟚) → C x
ind-𝟚 C cf ct x = {!   !}

idtoequiv : {i : Level} → {A B : Set i} → A ≡ B → A → B
idtoequiv refl a = a

transport : {i : Level} → {A : Set i} → {x y : A} → (P : A → Set i) → x ≡ y → P x → P y
transport P refl p = p

lemma1 : ∀ {C} → ∀ {A} → ¬ (λ (c : C) → (x : A c) → A c) ≡ (λ _ → 𝟚)
lemma1 ()
-- lemma2 : ∀ {C} → ∀ {A} → ∀ {A₁} → (λ (c : C) → (x : A c) (x₁ : A₁ (c , x)) → A₁ (c , x)) ≡ (λ _ → 𝟚)
-- lemma2 ()
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

ind-𝟚-gen : (C : e𝟚 → Set) → C efalse → C etrue → (T : ctxType ∅ → Set i) →
  (x : Exp ∅ T) → (Σ (T ≡ (λ _ → 𝟚)) (λ p → C (transport (λ T → Exp ∅ T) p x))) ⊎ ¬ (T ≡ (λ _ → 𝟚))
ind-𝟚-gen C ct cf _ (Lambda InCtx) = inj₂ lemma1
ind-𝟚-gen C ct cf _ (Lambda (Lambda InCtx)) = inj₂ {!   !}
ind-𝟚-gen C ct cf _ (Lambda (Lambda (Lambda InCtx))) = inj₁ {!   !}
ind-𝟚-gen C ct cf _ (Lambda (Lambda (Lambda (Lambda e)))) = inj₂ {!   !}
ind-𝟚-gen C ct cf _ (Lambda (Lambda (Lambda (WeakerCtx InCtx)))) = inj₁ {!   !}
ind-𝟚-gen C ct cf _ (Lambda (Lambda (Lambda (WeakerCtx (Lambda e))))) = inj₂ {!   !}
ind-𝟚-gen C ct cf _ (Lambda (Lambda (Lambda (WeakerCtx (WeakerCtx e))))) = inj₂ {!   !}
ind-𝟚-gen C ct cf _ (Lambda (Lambda (WeakerCtx e))) = inj₂ {!   !}
ind-𝟚-gen C ct cf _ (Lambda (WeakerCtx e)) = inj₂ {!   !}

-- PROBLEM ABOVE: what is induction principle for Exp? Can't define function which
-- don't quantify over Γ and T
