open import Data.Nat
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality

data ⊤ : Set₁ where
  tt : ⊤

mutual
  data Context : Set₁ where
    EmptyCtx : Context
    ConsCtx : (ctx : Context) → (ctxType ctx → Set₀) → Context

  -- outputs a type representing the information contained in the context
  ctxType : Context → Set₁
  ctxType EmptyCtx = ⊤
  ctxType (ConsCtx ctx h) = Σ (ctxType ctx) (λ t → h t)

data Exp : (ctx : Context) → (ctxType ctx → Set₀) → Set₁ where
  InCtx : {ctx : Context} → {t : ctxType ctx → Set₀} → Exp (ConsCtx ctx t) (λ {(rest , _) → t rest})
  Lambda : {ctx : Context} → {A : ctxType ctx → Set₀} → {B : ctxType (ConsCtx ctx A) → Set} →
    Exp (ConsCtx ctx A) B → Exp ctx (λ c → ((x : A c) → B (c , x)))
  -- WeakerCtx : {ctx : Context} → (t : ctxType ctx → Set₀) → (f : ctxType ctx → Set₀) →
  --   Exp (ConsCtx ctx t) (λ {(rest , _) → f rest}) → Exp ctx f

--     -----------------   InCtx
--     Γ, x : T ⊢ x : T

--      Γ, x : A ⊢ e : B
--     -----------------   Lambda
--      Γ ⊢  e : A → B

eval : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set} → Exp Γ T → T γ
eval γ (InCtx) = proj₂ γ
eval γ (Lambda e) x = eval (γ , x) e
-- eval γ (WeakerCtx {ctx} t f e) = eval (γ , {!   !}) e

Γ₁ : Context
Γ₁ = ConsCtx EmptyCtx (λ _ → ℕ) -- Γ₁ = n : ℕ

e₁ : Exp Γ₁ (λ _ → ℕ)
e₁ = InCtx -- t = (λ _ → ℕ) -- Γ₁ ⊢ n : ℕ
-- note that the following does not compile:
-- e₂ : Exp Γ₁ (λ _ → Bool)
-- e₂ = InCtx

idℕ : Exp EmptyCtx (λ _ → (ℕ → ℕ))
idℕ = Lambda e₁

evaled : ℕ → ℕ
evaled = eval tt idℕ

evaluation_works : evaled ≡ λ n → n
evaluation_works = refl
