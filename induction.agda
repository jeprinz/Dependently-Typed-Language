open import Level

open import exp

trueℕ : Exp ∅ (λ _ → (ℕ → ℕ → ℕ))
trueℕ = Lambda (Lambda (WeakerCtx InCtx)) -- λ x y . y

falseℕ : Exp ∅ (λ _ → (ℕ → ℕ → ℕ))
falseℕ = Lambda (Lambda InCtx) -- λ x y . x

𝟚 : Set i
𝟚 = (T : Set₁) → T → T → T

false : 𝟚
false _ _ t = t

true : 𝟚
true _ t _ = t

e𝟚 : Set j
e𝟚 = Exp ∅ (λ _ → 𝟚)

efalse : e𝟚
efalse = {!   !} -- Lambda ? -- can't make this work because of no universe cumulativity

etrue : e𝟚
etrue = {!   !}

-- 𝟚 induction principle:
ind-𝟚 : (C : e𝟚 → Set) → C efalse → C etrue → (x : e𝟚) → C x
ind-𝟚 = {!   !}

eℕ𝟚 = Exp ∅ (λ _ → (ℕ → ℕ → ℕ))
-- induction principle on ℕ → ℕ → ℕ because I can't figure out agda universe stuff
ind-ℕ𝟚 : (C : eℕ𝟚 → Set) → C trueℕ → C falseℕ → (x : eℕ𝟚) → C x
ind-ℕ𝟚 C ctrue cfalse = {!  !}

-- PROBLEM ABOVE: what is induction principle for Exp? Can't define function which
-- don't quantify over Γ and T
