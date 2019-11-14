-- open import Data.Nat
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Relation.Nullary
-- for universe levels
open import Agda.Primitive

open import exp

mutual

  data UnApplicable : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    InCtx : {Γ : Context} → {t : ctxType Γ → Set i} → UnApplicable (ConsCtx Γ t) (λ {(rest , _) → t rest})
    WeakerCtx : {Γ : Context} → {new t : ctxType Γ → Set i} →
      UnApplicable Γ t → UnApplicable (ConsCtx Γ new) (λ {(rest , _) → t rest})
    App : {Γ : Context} → {A : ctxType Γ → Set i} → {B : (γ : ctxType Γ) → A γ → Set i} →
      UnApplicable Γ (λ γ → (a : A γ) → B γ a) → (x : Value Γ A) → UnApplicable Γ (λ γ → B γ (evalv γ x))

  data Value : (Γ : Context) → (ctxType Γ → Set i) → Set j where
    Lambda : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (ConsCtx Γ A) → Set i} →
      Value (ConsCtx Γ A) B → Value Γ (λ γ → ((x : A γ) → B (γ , x)))
    𝓤 : {Γ : Context} → Value Γ (λ γ → Set predi)
    Π : {Γ : Context} → (A : ctxType Γ → Set predi) → (B : (γ : ctxType Γ) → A γ → Set predi) →
      Value Γ (λ γ → Set predi)
    Un : {Γ : Context} → {t : ctxType Γ → Set i} → UnApplicable Γ t → Value Γ t

  evalv : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → Value Γ T → T γ
  evalv γ (Lambda v) = λ x → evalv (γ , x) v
  evalv γ 𝓤 = Set predpredi
  evalv γ (Π A B) = (a : A γ) → B γ a
  evalv γ (Un u) = evalu γ u

  evalu : {Γ : Context} → (γ : ctxType Γ) → {T : ctxType Γ → Set i} → UnApplicable Γ T → T γ
  evalu γ InCtx = proj₂ γ
  evalu γ (WeakerCtx u) = evalu (proj₁ γ) u
  evalu γ (App u v) = (evalu γ u) (evalv γ v)

data Lift : Set predi → Set i where
  lift : {T : Set predi} → T → Lift T

𝟚 : Set i
𝟚 = (T : Set predi) → Lift T → Lift T → Lift T
e𝟚 : Set j
e𝟚 = Value ∅ (λ _ → 𝟚)
efalse : e𝟚
efalse = Lambda (Lambda (Lambda (Un InCtx))) -- λ T a b . b
etrue : e𝟚
etrue = Lambda (Lambda (Lambda (Un (WeakerCtx InCtx))))-- λ T a b . a

    -- Lambda : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (ConsCtx Γ A) → Set i} →
    --   Value (ConsCtx Γ A) B → Value Γ (λ γ → ((x : A γ) → B (γ , x)))
-- ((γ, A) , B)
rearrange : {Γ : Context} → {A B T : ctxType Γ → Set i} →
  let context = (ConsCtx (ConsCtx Γ A) (λ γ' → B (proj₁ γ'))) in
  let context' = (ConsCtx (ConsCtx Γ B) (λ γ' → A (proj₁ γ'))) in
  {T : ctxType context → Set i} →
  Exp context T →
  let T' = λ (γ : ctxType context') → T ((proj₁ (proj₁ γ) , proj₂ γ) , proj₂ (proj₁ γ)) in
  Exp context' T'
rearrange e = {! e  !}

-- substitute : {Γ : Context} → {A : ctxType Γ → Set i} → {B : ctxType (ConsCtx Γ A) → Set i} →
  -- Exp (ConsCtx Γ A) B → (e₂ : Exp Γ A) → Exp Γ (λ γ → B (γ , eval γ e₂))
-- substitute InCtx e₂ = e₂
-- substitute (Lambda e₃) e₂ = Lambda (substitute {!   !} {!   !}) -- TODO: going to need context rearranging to make this work...
-- substitute (WeakerCtx e₃) e₂ = {!   !}                          -- TODO: no, shouldn't need to change exp type to make function true/possible
-- substitute (App e₃ e₄) e₂ = {!   !}
-- substitute 𝓤 e₂ = 𝓤
-- substitute (Π A B) e₂ = (Π {!   !} {!   !})

-- evaluate : {Γ : Context} → {T : ctxType Γ → Set i} → Exp Γ T → Value Γ T
-- evaluate InCtx = Un InCtx
-- evaluate (Lambda {A} {B} e) = Lambda (evaluate e)
-- evaluate (WeakerCtx e) = let res = evaluate e in Un (WeakerCtx {!   !})
-- evaluate (App e₁ e₂) = {!   !}
-- evaluate 𝓤 = {!   !}
-- evaluate (Π A B) = {!   !}
