open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary -- ¬

data ⊤ : Set where
  tt : ⊤

data Bloo : Set₁ where
  yoogers : Bloo

data Vector : Set → ℕ → Set where
  emp : {T : Set} → Vector T 0
  cons : {T : Set} → {n : ℕ} → Vector T n → T → Vector T (suc n)

ind-vec : (P : (T : Set) → (n : ℕ) → Vector T n → Set) → ((T : Set) → P T 0 emp) →
  ((T : Set) → (n : ℕ) → (v : Vector T n) → P  T n v → (t : T) → P T (suc n)(cons v t)) →
  (T : Set) → (n : ℕ) → (v : Vector T n) → P T n v
ind-vec P Pempt Pcons T n emp = Pempt T
ind-vec P Pempt Pcons T (suc n) (cons v t) = Pcons T n v (ind-vec P Pempt Pcons T n v) t

getElm : {T : Set} → Vector T 1 → T
getElm (cons emp t) = t

lemma1 : ¬ (0 ≡ 1)
lemma1 ()
getElmUsingInd' : (T : Set) → (n : ℕ) → Vector T n → T ⊎ ¬ (n ≡ 1)
getElmUsingInd' T n v = ind-vec (λ T n v → T ⊎ ¬ (n ≡ 1))
  (λ T → inj₂ lemma1)
  (λ T n v p t → inj₁ t) -- just gives the last thing on the vector it is not empty
  T n v
getElmUsingInd : (T : Set) → Vector T 1 → T
getElmUsingInd T v with getElmUsingInd' T 1 v
getElmUsingInd T v    | (inj₁ t) = t
getElmUsingInd T v    | (inj₂ p) = ⊥-elim (p refl)

data Vector' : (⊤ → Set₁) → ℕ → Set₂ where
  oooo : {T : Set₁} → Vector' (λ _ → T) 0
  emp' : {T : ⊤ → Set₁} → Vector' T 0
  cons' : {T : ⊤ → Set₁} → {n : ℕ} → Vector' T n → T tt → Vector' T (suc n)

-- getElm' : {T : Set₁} → Vector' (λ _ → T) 1 → T
-- getElm' (cons' emp' t) = t
-- above does not work, agda can't figure out the pattern matching

getElm'' : {T : ⊤ → Set₁} → Vector' T 1 → T tt
getElm'' (cons' oooo x) = x
getElm'' (cons' emp' t) = t

-- agda can't figure out pattern matching for:
-- getTop : {T : Set₁} → Vector' (λ _ → T) 1 → T
-- getTop (cons' oooo x) = ?
-- getTop (cons' emp' t) = t

-- fact : (T : Set) → (λ _ → ⊤) ≡ (λ _ → T) → ⊤ ≡ T
-- fact = {!   !}

-- fact : (λ {x → x}) ­≡ (λ {x → x})
-- fact = ?

fact : (T : Set) → (⊤ → ⊤) ≡ (T → T) → ⊤ ≡ T
fact T = {!   !}

funky : ℕ → ℕ
funky x = x

itseq : funky ≡ λ x → x
itseq = refl
