module Tapl.Part2.Chapter09 where

module Language where
  open import Data.Fin using (Fin; #_)
  open import Data.Nat using (ℕ; suc; _≤?_)
  open import Relation.Nullary.Decidable

  infix  14 !_
  infixl 13 _$_
  infixr 12 if_then_else_
  infixr 11 fn_

  data Term (n : ℕ) : Set where
    var : Fin n → Term n
    fn_ : Term (suc n) → Term n
    _$_ : Term n → Term n → Term n
    false true : Term n
    if_then_else_ : Term n → Term n → Term n → Term n

  !_ : ∀ m {n} {m<n : True (suc m ≤? n)} → Term n
  !_ m {m<n = m<n} = var (#_ m {m<n = m<n})

module Types where
  open import Data.Fin using (Fin; zero; suc)
  open import Data.Nat using (ℕ; suc)
  open import Data.Product using (_,_; ∄-syntax)

  open Language

  infixr 8 _⇒_

  data Type : Set where
    bool : Type
    _⇒_ : Type → Type → Type

  infixl 6 _+_
  infix  5 _⊢_⦂_

  data Context : (n : ℕ) → Set where
    ∅ : Context 0
    _+_ : {n : ℕ} → Context n → Type → Context (suc n)

  infix 4 _⦂_∈_

  data _⦂_∈_ : ∀ {n} → Fin n → Type → Context n → Set where
    Z : ∀ {n} {Γ} {X}
      → zero {n} ⦂ X ∈ Γ + X
    S : ∀ {n} {Γ} {x : Fin n} {X Y}
      → x ⦂ X ∈ Γ
      → suc x ⦂ X ∈ Γ + Y

  data _⊢_⦂_ : {n : ℕ} → Context n → Term n → Type → Set where
    T-false : ∀ {n} {Γ : Context n}
      → Γ ⊢ false ⦂ bool
    T-true  : ∀ {n} {Γ : Context n}
      → Γ ⊢ true ⦂ bool

    T-abs : ∀ {n} {Γ : Context n} {y} {X Y}
      → Γ + X ⊢ y ⦂ Y
      → Γ ⊢ fn y ⦂ X ⇒ Y
    T-var : ∀ {n} {Γ : Context n} {x} {X}
      → x ⦂ X ∈ Γ
      → Γ ⊢ var x ⦂ X
    T-app : ∀ {n} {Γ : Context n} {f x} {X Y}
      → Γ ⊢ f ⦂ X ⇒ Y
      → Γ ⊢ x ⦂ X
      → Γ ⊢ f $ x ⦂ Y
    T-if : ∀ {n} {Γ : Context n} {x y z} {A}
      → Γ ⊢ x ⦂ bool
      → Γ ⊢ y ⦂ A
      → Γ ⊢ z ⦂ A
      → Γ ⊢ if x then y else z ⦂ A

  _ : ∀ {A} → ∅ ⊢ fn ! 0 ⦂ A ⇒ A
  _ = T-abs (T-var Z)

  _ : ∅ ⊢ if true then true else false ⦂ bool
  _ = T-if T-true T-true T-false

  _ : ∅ + bool ⇒ bool ⊢ ! 0 $ (if false then true else false) ⦂ bool
  _ = T-app (T-var Z) (T-if T-false T-true T-false)

  _ : ∅ + bool ⇒ bool ⊢ fn ! 1 $ (if ! 0 then false else ! 0) ⦂ bool ⇒ bool
  _ = T-abs (T-app (T-var (S Z)) (T-if (T-var Z) T-false (T-var Z)))

  _ : ∀ {n} {Γ : Context n} {A B} → Γ + A ⇒ B ⇒ bool + A + B ⊢ ! 2 $ ! 1 $ ! 0 ⦂ bool
  _ = T-app (T-app (T-var (S (S Z))) (T-var (S Z))) (T-var Z)

  -- ∄[ Γ + x ] (Γ ⊢ x $ x ⦂ A)
  -- in other words, (x $ x) is untypeable, because `x` has the type `A ⇒ B` and also `A`
  x$x : ∀ {n} {A} → ∄[ Γ ] (_⊢_⦂_ {suc n} Γ (! 0 $ ! 0) A)
  x$x = λ{ (_ , T-app (T-var Z) (T-var ())) }
