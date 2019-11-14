-- open import Data.Nat
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive

data ⊤ {i : Level} : Set i where
  tt : ⊤

predpredi = lzero
predi = lsuc predpredi
i = lsuc predi
j = lsuc i
mutual
  data Context : Set j where
    ∅ : Context
    ConsCtx : (ctx : Context) → (ctxType ctx → Set i) → Context

  -- outputs a type representing the information contained in the context
  ctxType : Context → Set j
  ctxType ∅ = ⊤
  ctxType (ConsCtx ctx h) = Σ (ctxType ctx) (λ t → h t)

mutual
  data Exp : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    InCtx : {Γ : Context} → {t : ctxType Γ → Set i} → Exp (ConsCtx Γ t) (λ {(rest , _) → t rest})
    Lambda : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (ConsCtx Γ A) → Set i} →
      Exp (ConsCtx Γ A) B → Exp Γ (λ γ → ((x : A γ) → B (γ , x)))
    WeakerCtx : {Γ : Context} → {new t : ctxType Γ → Set i} →
      Exp Γ t → Exp (ConsCtx Γ new) (λ {(rest , _) → t rest})
    App : {Γ : Context} → {A : ctxType Γ → Set i} → {B : (γ : ctxType Γ) → A γ → Set i} →
      Exp Γ (λ γ → (a : A γ) → B γ a) → (x : Exp Γ A) → Exp Γ (λ γ → B γ (eval γ x))
    𝓤 : {Γ : Context} → Exp Γ (λ γ → Set predi)
    Π : {Γ : Context} → (A : ctxType Γ → Set predi) → (B : (γ : ctxType Γ) → A γ → Set predi) →
      Exp Γ (λ γ → Set predi)

  eval : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → Exp Γ T → T γ
  eval γ InCtx = proj₂ γ
  eval γ (Lambda e) = λ x → eval (γ , x) e
  eval γ (WeakerCtx e) = eval (proj₁ γ) e
  eval γ (App e₁ e₂) = (eval γ e₁) (eval γ e₂)
  eval γ 𝓤 = Set predpredi
  eval γ (Π A B) = (a : A γ) → B γ a

--     -----------------   InCtx
--     Γ, x : T ⊢ x : T

--      Γ, x : A ⊢ e : B
--     -----------------   Lambda
--      Γ ⊢ e : A → B

--      Γ ⊢ e : B
--     -----------------   WeakerCtx
--      Γ, x : A ⊢ e : B

--      Γ ⊢ f : e : (a : A) → B a  Γ ⊢ x : A
--     ---------------------------------------   App
--      Γ ⊢ f x : B x

-- ind-rec : {Γ : Context} → {T : ctxType Γ → Set i} → (P : Set) →
  -- (∀ {T'} → Exp Γ T' → P ⊎ ¬ (T ≡ T')) →
  -- Exp Γ T → P
-- ind-rec P f e with (f e)
-- ind-rec P f e    |(inj₁ p) = p
-- ind-rec P f e    |(inj₂ p) = {!   !}

data ℕ : Set i where

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
