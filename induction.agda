open import exp

𝟚 : Set₁
𝟚 = (T : Set₀) → T → T → T

false : 𝟚
false _ _ t = t

true : 𝟚
true _ t _ = t

e𝟚 : Set j
e𝟚 = Exp ∅ (λ _ → 𝟚)

efalse : e𝟚
efalse = ?

etrue : e𝟚
etrue = ?

-- 𝟚 induction principle:
ind-𝟚 : (C : e𝟚 → Set) → C efalse → C etrue → (x : e𝟚) → C x
ind-𝟚 = ?
