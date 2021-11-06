module Tapl.Part2.Chapter09 where

module Language where
  import Data.Nat as Nat
  open import Data.Nat using (ℕ; zero; suc)
  open import Relation.Nullary.Decidable

  infixr 8 _⇒_

  data Type : Set where
    bool : Type
    _⇒_ : Type → Type → Type

  infixl 6 _+_
  infix  5 _⊢_
  infix  5 _∈_

  data Context : (n : ℕ) → Set where
    ∅ : Context 0
    _+_ : {n : ℕ} → Context n → Type → Context (suc n)

  data _∈_ : ∀ {n} → Type → Context n → Set where
    Z : ∀ {n} {Γ : Context n} {X}
      → X ∈ Γ + X
    S : ∀ {n} {Γ : Context n} {X Y}
      → X ∈ Γ
      → X ∈ Γ + Y

  infixl 13 _$_
  infixr 12 if_then_else_
  infixr 11 fn_

  data _⊢_ : {n : ℕ} → Context n → Type → Set where
    var : ∀ {n} {Γ : Context n} {X}
      → X ∈ Γ
      → Γ ⊢ X
    fn_ : ∀ {n} {Γ : Context n} {X Y}
      → Γ + X ⊢ Y
      → Γ ⊢ X ⇒ Y
    _$_ : ∀ {n} {Γ : Context n} {X Y}
      → Γ ⊢ X ⇒ Y
      → Γ ⊢ X
      → Γ ⊢ Y

    false : ∀ {n} {Γ : Context n}
      → Γ ⊢ bool
    true  : ∀ {n} {Γ : Context n}
      → Γ ⊢ bool
    if_then_else_ : ∀ {n} {Γ : Context n} {A}
      → Γ ⊢ bool
      → Γ ⊢ A
      → Γ ⊢ A
      → Γ ⊢ A

  module Lookup where
    open import Data.Fin using (Fin; #_; zero; suc)

    infix  14 !_

    lookup : ∀ {n} (Γ : Context n) → Fin n → Type
    lookup (_ + X) zero = X
    lookup (Γ + _) (suc n) = lookup Γ n

    !_ : ∀ m {n} {m<n : True (m Nat.<? n)} {Γ : Context n} → Γ ⊢ lookup Γ (#_ m {m<n = m<n})
    !_ m {Γ = Γ} = var (at Γ (# m))
      where
      at : ∀ {n} → (Γ : Context n) → (m : Fin n) → lookup Γ m ∈ Γ
      at (_ + _) zero = Z
      at (Γ + _) (suc m) = S (at Γ m)

  open Lookup public

module TypeExamples where
  open import Data.Nat using (suc)

  open Language

  _ : ∀ {A} → ∅ ⊢ A ⇒ A
  _ = fn ! 0

  _ : ∅ ⊢ bool
  _ = if true then true else false

  _ : ∅ + bool ⇒ bool ⊢ bool
  _ = ! 0 $ (if false then true else false)

  _ : ∅ + bool ⇒ bool ⊢ bool ⇒ bool
  _ = fn ! 1 $ (if ! 0 then false else ! 0)

  _ : ∀ {n} {Γ : Context n} {A B} → Γ + A ⇒ B ⇒ bool + A + B ⊢ bool
  _ = ! 2 $ ! 1 $ ! 0

  -- because the types are intrinsic, `! 0 $ ! 0` cannot be constructed
