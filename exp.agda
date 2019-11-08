-- open import Data.Nat
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality
-- for universe levels
open import Agda.Primitive

data ⊤ {i : Level} : Set i where
  tt : ⊤

-- module Context {i : Level} where
i = lsuc (lsuc lzero)
j = lsuc i
mutual
  data Context : Set j where
    ∅ : Context
    ConsCtx : (ctx : Context) → (ctxType ctx → Set i) → Context

  -- outputs a type representing the information contained in the context
  ctxType : Context → Set j
  ctxType ∅ = ⊤
  ctxType (ConsCtx ctx h) = Σ (ctxType ctx) (λ t → h t)

open Context
data Exp : (ctx : Context) → (ctxType ctx → Set i) → Set j where
  InCtx : {ctx : Context} → {t : ctxType ctx → Set i} → Exp (ConsCtx ctx t) (λ {(rest , _) → t rest})
  Lambda : {ctx : Context} → {A : ctxType ctx → Set i} → {B : ctxType (ConsCtx ctx A) → Set i} →
    Exp (ConsCtx ctx A) B → Exp ctx (λ c → ((x : A c) → B (c , x)))
  WeakerCtx : {ctx : Context} → {new t : ctxType ctx → Set i} →
    Exp ctx t → Exp (ConsCtx ctx new) (λ {(rest , _) → t rest})
  -- WeakerCtx : {ctx : Context} → (t : ctxType ctx → Set i) → (f : ctxType ctx → Set i) →
    -- Exp (ConsCtx ctx t) (λ {(rest , _) → f rest}) → Exp ctx f

--     -----------------   InCtx
--     Γ, x : T ⊢ x : T

--      Γ, x : A ⊢ e : B
--     -----------------   Lambda
--      Γ ⊢ e : A → B

--      Γ ⊢ e : B
--     -----------------   WeakerCtx
--      Γ, x : A ⊢ e : B

data ℕ : Set i where

eval : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → Exp Γ T → T γ
eval γ (InCtx) = proj₂ γ
eval γ (Lambda e) = λ x → eval (γ , x) e
eval γ (WeakerCtx e) = eval (proj₁ γ) e

evalSpecific : (γ : ctxType ∅) → Exp ∅ (λ _ → (ℕ → ℕ)) → (ℕ → ℕ)
evalSpecific γ e = eval γ e -- note this can't be defined by pattern matching, only by
-- referencing a more general thing.

Γ₁ : Context
Γ₁ = ConsCtx ∅ (λ _ → ℕ) -- Γ₁ = n : ℕ

e₁ : Exp Γ₁ (λ _ → ℕ)
e₁ = InCtx -- t = (λ _ → ℕ) -- Γ₁ ⊢ n : ℕ
-- note that the following does not compile:
-- e₂ : Exp Γ₁ (λ _ → Bool)
-- e₂ = InCtx

idℕ : Exp ∅ (λ _ → (ℕ → ℕ))
idℕ = Lambda InCtx

evaled : ℕ → ℕ
evaled = eval tt idℕ

evaluation_works : evaled ≡ λ n → n
evaluation_works = refl
