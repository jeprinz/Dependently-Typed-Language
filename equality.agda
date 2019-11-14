open import exp

-- eq : {Γ : Context} → (A : ctxType Γ → Set predi) → (γ : ctxType Γ) → (P : Exp Γ (λ γ → (A γ → Set predi))) →
  -- (x y : A γ) →
  -- (eval γ P) x → (eval γ P) y
-- eq A γ P x y px = {! P  !}

eq : {Γ : Context} → {A : ctxType Γ → Set predi} → (x y : (γ : ctxType Γ) → A γ) → Set j
eq {Γ} {A} x y = (γ : ctxType Γ) → (P : Exp Γ (λ γ → (A γ → Set predi))) →
                   eval γ P (x γ) → eval γ P (y γ)

funext : ∀ {Γ} → (A B : ctxType Γ → Set predi) → (f g : (γ : ctxType Γ) → (A γ → B γ)) →
  ((a : (γ : ctxType Γ) → A γ) → eq (λ γ → f γ (a γ)) (λ γ → g γ (a γ))) → eq f g
funext A B f g p γ P pf = ?-- ind-rec (eq f g) ? P
