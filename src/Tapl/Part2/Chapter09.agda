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

    private lookup : ∀ {n} (Γ : Context n) → Fin n → Type
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

module Substitution where
  open import Data.Bool using (false; true)
  import Data.Fin as Fin
  open import Data.Fin using (Fin; zero; suc; inject₁; #_; _≟_; _≤?_)
  import Data.Fin.Properties as Finₚ
  import Data.Nat as Nat
  open import Data.Nat using (ℕ; zero; suc)
  import Data.Nat.Properties as Natₚ
  open import Relation.Binary.Definitions
  open import Relation.Nullary

  open Language

  recontextualize : ∀ {n n′} {Γ : Context n} {Γ′ : Context n′}
    → (∀ {A} → A ∈ Γ → A ∈ Γ′)
    → (∀ {A} → Γ ⊢ A → Γ′ ⊢ A)
  recontextualize ρ (var v) = var (ρ v)
  recontextualize {Γ = Γ} {Γ′ = Γ′} ρ (fn body) = fn (recontextualize extend body)
    where
    extend : ∀ {A B} → A ∈ Γ + B → A ∈ Γ′ + B
    extend    Z  = Z
    extend (S x) = S (ρ x)
  recontextualize ρ (f $ x) = recontextualize ρ f $ recontextualize ρ x
  recontextualize ρ false = false
  recontextualize ρ true = true
  recontextualize ρ (if x then y else z) = if recontextualize ρ x then recontextualize ρ y else recontextualize ρ z

  substitute : ∀ {n n′} {Γ : Context n} {Γ′ : Context n′}
    → (∀ {A} → A ∈ Γ → Γ′ ⊢ A)
    → (∀ {A} → Γ ⊢ A → Γ′ ⊢ A)
  substitute ρ (var v) = ρ v
  substitute {Γ = Γ} {Γ′ = Γ′} ρ (fn body) = fn substitute extend body
    where
    extend : ∀ {A B} → A ∈ Γ + B → Γ′ + B ⊢ A
    extend    Z  = var Z
    extend (S x) = recontextualize S (ρ x)
  substitute ρ (f $ x) = substitute ρ f $ substitute ρ x
  substitute ρ false = false
  substitute ρ true = true
  substitute ρ (if x then y else z) = if substitute ρ x then substitute ρ y else substitute ρ z

  apply : ∀ {n} {Γ : Context n} {A B}
    → Γ + A ⊢ B
    → Γ ⊢ A
    → Γ ⊢ B
  apply {Γ = Γ} {A = A} {B = B} body argument = substitute reduce body
    where
    reduce : ∀ {C} → C ∈ Γ + A → Γ ⊢ C
    reduce    Z  = argument
    reduce (S x) = var x

module Evaluation where
  open import Data.Fin using (zero)
  open import Data.Nat as Nat using (ℕ; suc)
  open import Data.Product

  open Language
  open Substitution

  data Value {n : ℕ} {Γ : Context n} : {A : Type} → Γ ⊢ A → Set where
    V-false : Value false
    V-true : Value true
    V-fn : ∀ {A B}
      → (body : Γ + A ⊢ B)
      → Value (fn body)

  infix 8 _%→_

  data _%→_ : {n : ℕ} {Γ : Context n} {A : Type} → Γ ⊢ A → Γ ⊢ A → Set where
    E-app₁ : ∀ {n} {Γ : Context n} {A B} {f f′ : Γ ⊢ A ⇒ B} {x : Γ ⊢ A}
      → f %→ f′
      → f $ x %→ f′ $ x
    E-app₂ : ∀ {n} {Γ : Context n} {A B : Type} {f : Γ ⊢ A ⇒ B} {x x′ : Γ ⊢ A}
      → Value f
      → x %→ x′
      → f $ x %→ f $ x′
    E-appAbs : ∀ {n} {Γ : Context n} {A B : Type} {body : Γ + A ⊢ B} {x : Γ ⊢ A}
      → Value (fn body)
      → Value x
      → (fn body) $ x %→ (apply body x)
    E-if : ∀ {n} {Γ : Context n} {A : Type} {x x′ : Γ ⊢ bool} {y z : Γ ⊢ A}
      → x %→ x′
      → if x then y else z %→ if x′ then y else z
    E-ifTrue : ∀ {n} {Γ : Context n} {A : Type} {y z : Γ ⊢ A}
      → if true then y else z %→ y
    E-ifFalse : ∀ {n} {Γ : Context n} {A : Type} {y z : Γ ⊢ A}
      → if false then y else z %→ z

  data Progress {n} {Γ : Context n} {X : Type} (x : Γ ⊢ X) : Set where
    continue : (x′ : Γ ⊢ X) → x %→ x′ → Progress x
    value : Value x → Progress x

  progress : ∀ {X} → (x : ∅ ⊢ X) → Progress x
  progress false = value (V-false {Γ = ∅})
  progress true = value (V-true {Γ = ∅})
  progress (fn body) = value (V-fn body)
  progress (f $ x) with progress f
  ... | continue f′ f%→f′ = continue (f′ $ x) (E-app₁ f%→f′)
  ... | value vf@(V-fn body) with progress x
  ... | continue x′ x%→x′ = continue (f $ x′) (E-app₂ vf x%→x′)
  ... | value vx = continue (apply body x) (E-appAbs vf vx)
  progress (if x then y else z) with progress x
  ... | continue x′ x%→x′ = continue (if x′ then y else z) (E-if x%→x′)
  ... | value V-true = continue y E-ifTrue
  ... | value V-false = continue z E-ifFalse

  -- preservation holds intrinsically
