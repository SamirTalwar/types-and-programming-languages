module Tapl.Part1.Chapter03 where

module SimpleLanguage where
  open import Data.Maybe
  open import Data.Nat using (ℕ; suc; _+_; _⊔_; _<_; _≤_)
  open import Data.Product
  open import Data.Unit
  open import Data.Vec

  data Term : Set where
    true : Term
    false : Term
    if_then_else_ : Term → Term → Term → Term
    zero : Term
    succ : Term → Term
    pred : Term → Term
    iszero : Term → Term

  data Term₀ : Set where

  data Term₊₁ (T : Set) : Set where
    true : Term₊₁ T
    false : Term₊₁ T
    if_then_else_ : (x : T) → (y : T) → (z : T) → Term₊₁ T
    zero : Term₊₁ T
    succ : (x : T) → Term₊₁ T
    pred : (x : T) → Term₊₁ T
    iszero : (x : T) → Term₊₁ T

  Term₁ = Term₊₁ Term₀
  -- There are 3 elements in Term₁: `true`, `false`, and `zero`.
  count-elements-in-Term₁ : Term₁ → ⊤
  count-elements-in-Term₁ true = tt
  count-elements-in-Term₁ false = tt
  count-elements-in-Term₁ zero = tt

  Term₂ = Term₊₁ Term₁
  -- elements of Term₂:
  --  true (1)
  --  false (1)
  --  zero (1)
  --  succ ... (3)
  --  pred ... (3)
  --  iszero ... (3)
  --  if_then_else_ ... (3 * 3 * 3 = 27)
  -- total: 39

  Term₃ = Term₊₁ Term₂
  -- elements of Term₂:
  --  true (1)
  --  false (1)
  --  zero (1)
  --  succ ... (39)
  --  pred ... (39)
  --  iszero ... (39)
  --  if_then_else_ ... (39 * 39 * 39 = 59,319)
  -- total: 59,439

  data isTermᵢ : (T : Set) → Set₁ where
    isTerm₀ : isTermᵢ Term₀
    isTermᵢ₊₁ : {T : Set} → isTermᵢ T → isTermᵢ (Term₊₁ T)

  Termᵢ⊆Termᵢ₊₁ : ∀ {T : Set} → (isTermᵢ T) → T → Term₊₁ T
  Termᵢ⊆Termᵢ₊₁ (isTermᵢ₊₁ _) true = true
  Termᵢ⊆Termᵢ₊₁ (isTermᵢ₊₁ _) false = false
  Termᵢ⊆Termᵢ₊₁ (isTermᵢ₊₁ isTerm) (if x then y else z) =
    if Termᵢ⊆Termᵢ₊₁ isTerm x then Termᵢ⊆Termᵢ₊₁ isTerm y else Termᵢ⊆Termᵢ₊₁ isTerm z
  Termᵢ⊆Termᵢ₊₁ (isTermᵢ₊₁ _) zero = zero
  Termᵢ⊆Termᵢ₊₁ (isTermᵢ₊₁ isTerm) (succ x) = succ (Termᵢ⊆Termᵢ₊₁ isTerm x)
  Termᵢ⊆Termᵢ₊₁ (isTermᵢ₊₁ isTerm) (pred x) = pred (Termᵢ⊆Termᵢ₊₁ isTerm x)
  Termᵢ⊆Termᵢ₊₁ (isTermᵢ₊₁ isTerm) (iszero x) = iszero (Termᵢ⊆Termᵢ₊₁ isTerm x)

  term-size : Term → ℕ
  term-size true = 1
  term-size false = 1
  term-size (if x then y else z) = 1 + term-size x + term-size y + term-size z
  term-size zero = 1
  term-size (succ x) = 1 + term-size x
  term-size (pred x) = 1 + term-size x
  term-size (iszero x) = 1 + term-size x

  term-depth : Term → ℕ
  term-depth true = 1
  term-depth false = 1
  term-depth (if x then y else z) = 1 + ((term-depth x) ⊔ (term-depth y) ⊔ (term-depth z))
  term-depth zero = 1
  term-depth (succ x) = 1 + term-depth x
  term-depth (pred x) = 1 + term-depth x
  term-depth (iszero x) = 1 + term-depth x
