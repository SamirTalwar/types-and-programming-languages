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

module BoolLanguage where
  open import Data.Empty
  open import Data.Product
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary

  data Expr : Set where
    true : Expr
    false : Expr
    if_then_else_ : (x : Expr) → (y : Expr) → (z : Expr) → Expr

  data Value : Expr → Set where
    V-true : Value true
    V-false : Value false

  infix 5 _%→_

  data _%→_ : Expr → Expr → Set where
    E-ifTrue : ∀ {y z : Expr}
      → if true then y else z %→ y

    E-ifFalse : ∀ {y z : Expr}
      → if false then y else z %→ z

    E-if : ∀ {x x′ y z : Expr}
      → x %→ x′
      → if x then y else z %→ if x′ then y else z

  _ : if true then true else (if false then false else false) %→ true
  _ = E-ifTrue

  determinacy : ∀ {t t₁ t₂} → t %→ t₁ → t %→ t₂ → t₁ ≡ t₂
  determinacy E-ifTrue E-ifTrue = refl
  determinacy E-ifFalse E-ifFalse = refl
  determinacy (E-if t%→t₁) (E-if t%→t₂) with determinacy t%→t₁ t%→t₂
  ... | refl = refl

  data NormalForm : Expr → Set where
    normal-form : (t : Expr) → ∄[ t′ ] (t %→ t′) → NormalForm t

  values-are-in-normal-form : ∀ {t : Expr} → Value t → NormalForm t
  values-are-in-normal-form V-true = normal-form true λ{ () }
  values-are-in-normal-form V-false = normal-form false λ{ () }

  terms-in-normal-form-are-values : ∀ {t : Expr} → NormalForm t → Value t
  terms-in-normal-form-are-values (normal-form true _) = V-true
  terms-in-normal-form-are-values (normal-form false _) = V-false
  terms-in-normal-form-are-values (normal-form (if true then y else _) no-evaluation) =
    ⊥-elim (no-evaluation (y , E-ifTrue))
  terms-in-normal-form-are-values (normal-form (if false then _ else z) no-evaluation) =
    ⊥-elim (no-evaluation (z , E-ifFalse))
  terms-in-normal-form-are-values (normal-form (if i@(if _ then _ else _) then y else z) no-evaluation)
    with terms-in-normal-form-are-values (normal-form i λ{
        (x@true , t%->t′)                 → no-evaluation ((if x then y else z) , E-if t%->t′)
      ; (x@false , t%->t′)                → no-evaluation ((if x then y else z) , E-if t%->t′)
      ; (x@(if _ then _ else _) , t%->t′) → no-evaluation ((if x then y else z) , E-if t%->t′)
      })
  ... | ()

  infix  5 _%↠_
  infixr 6 _%→⟨_⟩_
  infixr 6 _%↠⟨_⟩_
  infix  7 _∎

  data _%↠_ : Expr → Expr → Set where
    _∎ : (t : Expr) → t %↠ t
    %trans : (t₀ : Expr) → ∀ {t₁ t₂} → t₀ %→ t₁ → t₁ %↠ t₂ → t₀ %↠ t₂

  _%→⟨_⟩_ : (t₀ : Expr) → ∀ {t₁ t₂} → t₀ %→ t₁ → t₁ %↠ t₂ → t₀ %↠ t₂
  _%→⟨_⟩_ = %trans

  _%↠⟨_⟩_ : (t₀ : Expr) → ∀ {t₁ t₂} → t₀ %↠ t₁ → t₁ %↠ t₂ → t₀ %↠ t₂
  t₀ %↠⟨ _ ∎ ⟩ t₀%↠t₀ = t₀%↠t₀
  t₀ %↠⟨ %trans .t₀ {t₁} t₀%→t₁ t₁%↠t₂ ⟩ t₂%↠t₃ = t₀ %→⟨ t₀%→t₁ ⟩ (t₁ %↠⟨ t₁%↠t₂ ⟩ t₂%↠t₃)

  E-if↠ : ∀ {x x′ y z : Expr}
      → x %↠ x′
      → if x then y else z %↠ if x′ then y else z
  E-if↠ {x} {x′} {y} {z} (x ∎) = (if x then y else z) ∎
  E-if↠ {x} {x′} {y} {z} (%trans _ nested next) = %trans (if x then y else z) (E-if nested) (E-if↠ next)

  all-terms-terminate-in-normal-form : ∀ (t : Expr) → ∃[ t′ ] (Value t′ × t %↠ t′)
  all-terms-terminate-in-normal-form true = true , (V-true , true ∎)
  all-terms-terminate-in-normal-form false = false , (V-false , false ∎)
  all-terms-terminate-in-normal-form t@(if true then y else z) =
    map₂ (map₂ (t %→⟨ E-ifTrue ⟩_)) (all-terms-terminate-in-normal-form y)
  all-terms-terminate-in-normal-form t@(if false then y else z) =
    map₂ (map₂ (t %→⟨ E-ifFalse ⟩_)) (all-terms-terminate-in-normal-form z)
  all-terms-terminate-in-normal-form t@(if x@(if _ then _ else _) then y else z) with all-terms-terminate-in-normal-form x
  ... | true , _ , %trans .(if _ then _ else _) {x′} nested next =
    let t′ , value , x%↠end = all-terms-terminate-in-normal-form y
    in t′ , value , (if x then y else z) %→⟨ E-if nested ⟩ (if x′ then y else z) %↠⟨ E-if↠ next ⟩ (if true then y else z) %→⟨ E-ifTrue ⟩ x%↠end
  ... | false , _ , %trans .(if _ then _ else _) {x′} nested next =
    let t′ , value , x%↠end = all-terms-terminate-in-normal-form z
    in t′ , value , (if x then y else z) %→⟨ E-if nested ⟩ (if x′ then y else z) %↠⟨ E-if↠ next ⟩ (if false then y else z) %→⟨ E-ifFalse ⟩ x%↠end
