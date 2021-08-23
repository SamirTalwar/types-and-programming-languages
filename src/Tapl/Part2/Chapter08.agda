module Tapl.Part2.Chapter08 where

open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

import Tapl.Part1.Chapter03
open Tapl.Part1.Chapter03.SimpleLanguage using (Term; true; false; if_then_else_; zero; succ; pred; iszero)
open Tapl.Part1.Chapter03.SimpleLanguageEvaluation
open Tapl.Part1.Chapter03.SimpleLanguageEvaluation.Values

data Type : Set where
  bool : Type
  nat  : Type

infix 5 _⦂_

data _⦂_ : Term → Type → Set where
  T-true  : true ⦂ bool
  T-false : false ⦂ bool
  T-if : ∀ {x y z : Term} {T : Type}
    → (xT : x ⦂ bool)
    → (yT : y ⦂ T)
    → (zT : z ⦂ T)
    → if x then y else z ⦂ T
  T-zero : zero ⦂ nat
  T-succ : ∀ {x : Term}
    → (xT : x ⦂ nat)
    → succ x ⦂ nat
  T-pred : ∀ {x : Term}
    → (xT : x ⦂ nat)
    → pred x ⦂ nat
  T-iszero : ∀ {x : Term}
    → (xT : x ⦂ nat)
    → iszero x ⦂ bool

data Subterm : Term → Term → Set where
  S-if-condition : ∀ {x y z}
    → Subterm (if x then y else z) x
  S-if-true-clause : ∀ {x y z}
    → Subterm (if x then y else z) y
  S-if-false-clause : ∀ {x y z}
    → Subterm (if x then y else z) z
  S-succ : ∀ {x}
    → Subterm (succ x) x
  S-pred : ∀ {x}
    → Subterm (pred x) x
  S-iszero : ∀ {x}
    → Subterm (iszero x) x

a-well-typed-term-has-well-typed-subterms : ∀ {t t′} T → Subterm t t′ → t ⦂ T → ∃[ T′ ] (t′ ⦂ T′)
a-well-typed-term-has-well-typed-subterms T S-if-condition    (T-if x _ _) = bool , x
a-well-typed-term-has-well-typed-subterms T S-if-true-clause  (T-if _ y _) = T , y
a-well-typed-term-has-well-typed-subterms T S-if-false-clause (T-if _ _ z) = T , z
a-well-typed-term-has-well-typed-subterms T S-succ (T-succ x) = nat , x
a-well-typed-term-has-well-typed-subterms T S-pred (T-pred x) = nat , x
a-well-typed-term-has-well-typed-subterms T S-iszero (T-iszero x) = nat , x

each-term-has-one-type : ∀ {t} {T T′} → t ⦂ T → t ⦂ T′ → T ≡ T′
each-term-has-one-type T-true T-true = refl
each-term-has-one-type T-false T-false = refl
each-term-has-one-type (T-if _ _ z₁) (T-if _ _ z₂) = each-term-has-one-type z₁ z₂
each-term-has-one-type T-zero T-zero = refl
each-term-has-one-type (T-succ _) (T-succ _) = refl
each-term-has-one-type (T-pred _) (T-pred _) = refl
each-term-has-one-type (T-iszero _) (T-iszero _) = refl

data TypedValue : {t : Term} → Value t → Type → Set where
  V-true  : TypedValue (V-bool V-true) bool
  V-false : TypedValue (V-bool V-false) bool
  V-zero : TypedValue (V-num V-zero) nat
  V-succ : ∀ {t} {n} → TypedValue {t} (V-num n) nat → TypedValue {succ t} (V-num (V-succ n)) nat

progress : ∀ {t} {T} → t ⦂ T → ∃[ v ] (TypedValue {t} v T) ⊎ ∃[ t′ ] (t %→ t′)
progress T-true = inj₁ (V-bool V-true , V-true)
progress T-false = inj₁ (V-bool V-false , V-false)
progress (T-if x y z) with progress x
... | inj₂ (x′ , x%→x′) = inj₂ ((if x′ then _ else _) , E-if x%→x′)
... | inj₁ (V-bool V-true , V-true) = inj₂ (_ , E-ifTrue)
... | inj₁ (V-bool V-false , V-false) = inj₂ (_ , E-ifFalse)
progress T-zero = inj₁ (V-num V-zero , V-zero)
progress (T-succ t) with progress t
... | inj₁ (V-num numeric , typed) = inj₁ (V-num (V-succ numeric) , V-succ typed)
... | inj₂ (t′ , t%→t′) = inj₂ (succ t′ , E-succ t%→t′)
progress (T-pred t) with progress t
... | inj₁ (V-num V-zero , typed) = inj₂ (zero , E-predZero)
... | inj₁ (V-num (V-succ {n} numeric) , typed) = inj₂ (n , E-predSucc numeric)
... | inj₂ (t′ , t%→t′) = inj₂ (pred t′ , E-pred t%→t′)
progress (T-iszero t) with progress t
... | inj₁ (V-num .V-zero , V-zero) = inj₂ (true , E-iszeroZero)
... | inj₁ (V-num .(V-succ _) , V-succ {n = n} _) = inj₂ (false , E-iszeroSucc n)
... | inj₂ (t′ , t%→t′) = inj₂ (iszero t′ , E-iszero t%→t′)

preservation : ∀ {t t′} {T} → t ⦂ T → t %→ t′ → t′ ⦂ T
preservation (T-if x y z) E-ifTrue = y
preservation (T-if x y z) E-ifFalse = z
preservation (T-if x y z) (E-if x%→x′) with preservation x x%→x′
... | T-true = T-if T-true y z
... | T-false = T-if T-false y z
... | T-if x′ y′ z′ = T-if (T-if x′ y′ z′) y z
... | T-iszero x = T-if (T-iszero x) y z
preservation (T-succ t) (E-succ t%→t′) = T-succ (preservation t t%→t′)
preservation (T-pred T-zero) E-predZero = T-zero
preservation (T-pred _) (E-predSucc V-zero) = T-zero
preservation (T-pred (T-succ (T-succ t))) (E-predSucc (V-succ v)) = T-succ t
preservation (T-pred t) (E-pred t%→t′) = T-pred (preservation t t%→t′)
preservation (T-iszero t) E-iszeroZero = T-true
preservation (T-iszero t) (E-iszeroSucc _) = T-false
preservation (T-iszero t) (E-iszero t%→t′) = T-iszero (preservation t t%→t′)
