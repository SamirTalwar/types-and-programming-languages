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

module SimpleLanguageEvaluation where
  open import Data.Empty
  open import Data.Product
  open import Data.Sum
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary

  open SimpleLanguage

  data BooleanValue : Term → Set where
    V-true : BooleanValue true
    V-false : BooleanValue false

  data NumericValue : Term → Set where
    V-zero : NumericValue zero
    V-succ : {n : Term} → (numeric : NumericValue n) → NumericValue (succ n)

  data Value : Term → Set where
    V-bool : {t : Term} → (boolean : BooleanValue t) → Value t
    V-num : {t : Term} → (numeric : NumericValue t) → Value t

  infix 5 _%→_

  data _%→_ : Term → Term → Set where
    E-ifTrue : ∀ {y z : Term}
      → if true then y else z %→ y

    E-ifFalse : ∀ {y z : Term}
      → if false then y else z %→ z

    E-if : ∀ {x x′ y z : Term}
      → x %→ x′
      → if x then y else z %→ if x′ then y else z

    E-succ : ∀ {x x′ : Term}
      → x %→ x′
      → succ x %→ succ x′

    E-predZero : pred zero %→ zero

    E-predSucc : ∀ {n : Term}
      → NumericValue n
      → pred (succ n) %→ n

    E-pred : ∀ {x x′ : Term}
      → x %→ x′
      → pred x %→ pred x′

    E-iszeroZero : iszero zero %→ true

    E-iszeroSucc : ∀ {n : Term}
      → NumericValue n
      → iszero (succ n) %→ false

    E-iszero : ∀ {x x′ : Term}
      → x %→ x′
      → iszero x %→ iszero x′

  data NormalForm : Term → Set where
    normal-form : (t : Term) → ∄[ t′ ] (t %→ t′) → NormalForm t

  values-are-in-normal-form : ∀ {t : Term} → Value t → NormalForm t
  values-are-in-normal-form (V-bool V-true) = normal-form true λ{ () }
  values-are-in-normal-form (V-bool V-false) = normal-form false λ{ () }
  values-are-in-normal-form (V-num V-zero) = normal-form zero λ{ () }
  values-are-in-normal-form (V-num {succ _} (V-succ numeric)) with values-are-in-normal-form (V-num numeric)
  ... | normal-form n no-evaluation = normal-form (succ n) λ{ (succ n′ , E-succ n%→n′) → no-evaluation (n′ , n%→n′) }

  determinacy : ∀ {t t₁ t₂} → t %→ t₁ → t %→ t₂ → t₁ ≡ t₂
  determinacy E-ifTrue E-ifTrue = refl
  determinacy E-ifFalse E-ifFalse = refl
  determinacy (E-if t%→t₁) (E-if t%→t₂) rewrite determinacy t%→t₁ t%→t₂ = refl
  determinacy (E-succ t%→t₁) (E-succ t%→t₂) rewrite determinacy t%→t₁ t%→t₂ = refl
  determinacy E-predZero E-predZero = refl
  determinacy (E-predSucc _) (E-predSucc _) = refl
  determinacy (E-pred t%→t₁) (E-pred t%→t₂) rewrite determinacy t%→t₁ t%→t₂ = refl
  determinacy (E-predSucc numeric) (E-pred (E-succ {x′ = x′} t%→t₂)) with values-are-in-normal-form (V-num numeric)
  ... | normal-form _ no-evaluation = ⊥-elim (no-evaluation (x′ , t%→t₂))
  determinacy (E-pred (E-succ {x′ = x′} t%→t₁)) (E-predSucc numeric) with values-are-in-normal-form (V-num numeric)
  ... | normal-form _ no-evaluation = ⊥-elim (no-evaluation (x′ , t%→t₁))
  determinacy E-iszeroZero E-iszeroZero = refl
  determinacy (E-iszero t%→t₁) (E-iszero t%→t₂) rewrite determinacy t%→t₁ t%→t₂ = refl
  determinacy (E-iszeroSucc _) (E-iszeroSucc _) = refl
  determinacy (E-iszeroSucc numeric) (E-iszero (E-succ {x′ = x′} t%→t₂)) with values-are-in-normal-form (V-num numeric)
  ... | normal-form _ no-evaluation = ⊥-elim (no-evaluation (x′ , t%→t₂))
  determinacy (E-iszero (E-succ {x′ = x′} t%→t₁)) (E-iszeroSucc numeric) with values-are-in-normal-form (V-num numeric)
  ... | normal-form _ no-evaluation = ⊥-elim (no-evaluation (x′ , t%→t₁))

  infix  5 _%↠_
  infixr 6 _%→⟨_⟩_
  infixr 6 _%↠⟨_⟩_
  infix  7 _∎

  data _%↠_ : Term → Term → Set where
    _∎ : (t : Term) → t %↠ t
    %trans : (t₀ : Term) → ∀ {t₁ t₂} → t₀ %→ t₁ → t₁ %↠ t₂ → t₀ %↠ t₂

  _%→⟨_⟩_ : (t₀ : Term) → ∀ {t₁ t₂} → t₀ %→ t₁ → t₁ %↠ t₂ → t₀ %↠ t₂
  _%→⟨_⟩_ = %trans

  _%↠⟨_⟩_ : (t₀ : Term) → ∀ {t₁ t₂} → t₀ %↠ t₁ → t₁ %↠ t₂ → t₀ %↠ t₂
  t₀ %↠⟨ _ ∎ ⟩ t₀%↠t₀ = t₀%↠t₀
  t₀ %↠⟨ %trans .t₀ {t₁} t₀%→t₁ t₁%↠t₂ ⟩ t₂%↠t₃ = t₀ %→⟨ t₀%→t₁ ⟩ (t₁ %↠⟨ t₁%↠t₂ ⟩ t₂%↠t₃)

  E-if↠ : ∀ {x x′ y z : Term}
      → x %↠ x′
      → if x then y else z %↠ if x′ then y else z
  E-if↠ {x} {x′} {y} {z} (x ∎) = (if x then y else z) ∎
  E-if↠ {x} {x′} {y} {z} (%trans .x nested next) = %trans (if x then y else z) (E-if nested) (E-if↠ next)

  E-succ↠ : ∀ {t t′ : Term}
    → t %↠ t′
    → succ t %↠ succ t′
  E-succ↠ {t} {.t} (.t ∎) = succ t ∎
  E-succ↠ {t} {t′} (%trans .t nested next) = %trans (succ t) (E-succ nested) (E-succ↠ next)

  E-pred↠ : ∀ {t t′ : Term}
    → t %↠ t′
    → pred t %↠ pred t′
  E-pred↠ {t} {.t} (.t ∎) = pred t ∎
  E-pred↠ {t} {t′} (%trans .t nested next) = %trans (pred t) (E-pred nested) (E-pred↠ next)

  E-iszero↠ : ∀ {t t′ : Term}
    → t %↠ t′
    → iszero t %↠ iszero t′
  E-iszero↠ {t} {.t} (.t ∎) = iszero t ∎
  E-iszero↠ {t} {t′} (%trans .t nested next) = %trans (iszero t) (E-iszero nested) (E-iszero↠ next)

  infix 9 _stuck-%↠_

  data Stuck : Term → Set where
    stuck-if-num : ∀ {x y z : Term} → (numeric : NumericValue x) → Stuck (if x then y else z)
    stuck-succ-bool : ∀ {t : Term} → (boolean : BooleanValue t) → Stuck (succ t)
    stuck-pred-bool : ∀ {t : Term} → (boolean : BooleanValue t) → Stuck (pred t)
    stuck-iszero-bool : ∀ {t : Term} → (boolean : BooleanValue t) → Stuck (iszero t)
    stuck-if : ∀ {x y z : Term} → Stuck x → Stuck (if x then y else z)
    stuck-succ : ∀ {t : Term} → Stuck t → Stuck (succ t)
    stuck-pred : ∀ {t : Term} → Stuck t → Stuck (pred t)
    stuck-iszero : ∀ {t : Term} → Stuck t → Stuck (iszero t)
    _stuck-%↠_ : ∀ {t t′ : Term} → t %↠ t′ → Stuck t′ → Stuck t

  terms-in-normal-form-are-values-or-stuck : ∀ {t : Term} → NormalForm t → Stuck t ⊎ Value t
  terms-in-normal-form-are-values-or-stuck (normal-form true _) = inj₂ (V-bool V-true)
  terms-in-normal-form-are-values-or-stuck (normal-form false _) = inj₂ (V-bool V-false)
  terms-in-normal-form-are-values-or-stuck (normal-form (if true then y else _) no-evaluation) =
    ⊥-elim (no-evaluation (y , E-ifTrue))
  terms-in-normal-form-are-values-or-stuck (normal-form (if false then _ else z) no-evaluation) =
    ⊥-elim (no-evaluation (z , E-ifFalse))
  terms-in-normal-form-are-values-or-stuck (normal-form (if i@(if _ then _ else _) then y else z) no-evaluation)
    with terms-in-normal-form-are-values-or-stuck (normal-form i λ{ (i′ , i%→i′) → no-evaluation (if i′ then y else z , E-if i%→i′) })
  ... | inj₁ stuck = inj₁ (stuck-if stuck)
  ... | inj₂ (V-num ())
  terms-in-normal-form-are-values-or-stuck (normal-form (if zero then _ else _) no-evaluation) = inj₁ (stuck-if-num V-zero)
  terms-in-normal-form-are-values-or-stuck (normal-form (if succ x then y else z) no-evaluation)
    with terms-in-normal-form-are-values-or-stuck (normal-form x (λ{ (x′ , x%→x′) → no-evaluation ((if succ x′ then y else z) , E-if (E-succ x%→x′)) }))
  ... | inj₁ stuck = inj₁ (stuck-if (stuck-succ stuck))
  ... | inj₂ (V-bool boolean) = inj₁ (stuck-if (stuck-succ-bool boolean))
  ... | inj₂ (V-num numeric) = inj₁ (stuck-if-num (V-succ numeric))
  terms-in-normal-form-are-values-or-stuck (normal-form (if pred x then y else z) no-evaluation)
    with terms-in-normal-form-are-values-or-stuck (normal-form x (λ{ (x′ , x%→x′) → no-evaluation ((if pred x′ then y else z) , E-if (E-pred x%→x′)) }))
  ... | inj₁ stuck = inj₁ (stuck-if (stuck-pred stuck))
  ... | inj₂ (V-bool boolean) = inj₁ (stuck-if (stuck-pred-bool boolean))
  ... | inj₂ (V-num V-zero) = ⊥-elim (no-evaluation ((if zero then y else z) , E-if E-predZero))
  ... | inj₂ (V-num (V-succ {n} numeric)) = ⊥-elim (no-evaluation ((if n then y else z) , E-if (E-predSucc numeric)))
  terms-in-normal-form-are-values-or-stuck (normal-form (if iszero x then y else z) no-evaluation)
    with terms-in-normal-form-are-values-or-stuck (normal-form x (λ{ (x′ , x%→x′) → no-evaluation ((if iszero x′ then y else z) , E-if (E-iszero x%→x′)) }))
  ... | inj₁ stuck = inj₁ (stuck-if (stuck-iszero stuck))
  ... | inj₂ (V-bool boolean) = inj₁ (stuck-if (stuck-iszero-bool boolean))
  ... | inj₂ (V-num V-zero) = ⊥-elim (no-evaluation ((if true then y else z) , E-if E-iszeroZero))
  ... | inj₂ (V-num (V-succ numeric)) = ⊥-elim (no-evaluation ((if false then y else z) , E-if (E-iszeroSucc numeric)))
  terms-in-normal-form-are-values-or-stuck (normal-form zero no-evaluation) = inj₂ (V-num V-zero)
  terms-in-normal-form-are-values-or-stuck (normal-form (succ x) no-evaluation)
    with terms-in-normal-form-are-values-or-stuck (normal-form x λ{ (x′ , x%x′) → no-evaluation (succ x′ , E-succ x%x′) })
  ... | inj₁ stuck = inj₁ (stuck-succ stuck)
  ... | inj₂ (V-bool bool) = inj₁ (stuck-succ-bool bool)
  ... | inj₂ (V-num numeric) = inj₂ (V-num (V-succ numeric))
  terms-in-normal-form-are-values-or-stuck (normal-form (pred x) no-evaluation)
    with terms-in-normal-form-are-values-or-stuck (normal-form x λ{ (x′ , x%x′) → no-evaluation (pred x′ , E-pred x%x′) })
  ... | inj₁ stuck = inj₁ (stuck-pred stuck)
  ... | inj₂ (V-bool boolean) = inj₁ (stuck-pred-bool boolean)
  ... | inj₂ (V-num V-zero) = ⊥-elim (no-evaluation (zero , E-predZero))
  ... | inj₂ (V-num (V-succ {n} numeric)) = ⊥-elim (no-evaluation (n , E-predSucc numeric))
  terms-in-normal-form-are-values-or-stuck (normal-form (iszero x) no-evaluation)
    with terms-in-normal-form-are-values-or-stuck (normal-form x λ{ (x′ , x%x′) → no-evaluation (iszero x′ , E-iszero x%x′) })
  ... | inj₁ stuck = inj₁ (stuck-iszero stuck)
  ... | inj₂ (V-bool boolean) = inj₁ (stuck-iszero-bool boolean)
  ... | inj₂ (V-num V-zero) = ⊥-elim (no-evaluation (true , E-iszeroZero))
  ... | inj₂ (V-num (V-succ numeric)) = ⊥-elim (no-evaluation (false , E-iszeroSucc numeric))

  infix 10 _%→*_
  infix 10 _terminates-with_

  data _%→*_ : Term → Term → Set where
    _terminates-with_ : ∀ {t t′ : Term} → t %↠ t′ → Value t′ → t %→* t′

  eval : (t : Term) → Stuck t ⊎ ∃[ t′ ] (t %→* t′)
  eval true = inj₂ (true , ((true ∎) terminates-with V-bool V-true))
  eval false = inj₂ (false , ((false ∎) terminates-with V-bool V-false))
  eval (if x then y else z) with eval x
  eval (if x then y else z) | inj₁ stuck = inj₁ (stuck-if stuck)
  eval (if x then y else z) | inj₂ (.true , x%↠x′ terminates-with V-bool V-true) with eval y
  ... | inj₁ stuck = inj₁ ((if x then y else z %↠⟨ E-if↠ x%↠x′ ⟩ if true then y else z %→⟨ E-ifTrue ⟩ y ∎) stuck-%↠ stuck)
  ... | inj₂ (y′ , y%↠y′ terminates-with v) = inj₂ (y′ , (if x then y else z %↠⟨ E-if↠ x%↠x′ ⟩ if true then y else z %→⟨ E-ifTrue ⟩ y %↠⟨ y%↠y′ ⟩ y′ ∎) terminates-with v)
  eval (if x then y else z) | inj₂ (.false , x%↠x′ terminates-with V-bool V-false) with eval z
  ... | inj₁ stuck = inj₁ ((if x then y else z %↠⟨ E-if↠ x%↠x′ ⟩ if false then y else z %→⟨ E-ifFalse ⟩ z ∎) stuck-%↠ stuck)
  ... | inj₂ (z′ , z%↠z′ terminates-with v) = inj₂ (z′ , (if x then y else z %↠⟨ E-if↠ x%↠x′ ⟩ if false then y else z %→⟨ E-ifFalse ⟩ z %↠⟨ z%↠z′ ⟩ z′ ∎) terminates-with v)
  eval (if x then y else z) | inj₂ (x′ , x%↠x′ terminates-with V-num numeric) = inj₁ (E-if↠ x%↠x′ stuck-%↠ stuck-if-num numeric)
  eval zero = inj₂ (zero , ((zero ∎) terminates-with V-num V-zero))
  eval (succ x) with eval x
  ... | inj₁ stuck = inj₁ (stuck-succ stuck)
  ... | inj₂ (x′ , x%↠x′ terminates-with V-bool boolean) = inj₁ (E-succ↠ x%↠x′ stuck-%↠ stuck-succ-bool boolean)
  ... | inj₂ (x′ , x%↠x′ terminates-with V-num numeric) = inj₂ (succ x′ , E-succ↠ x%↠x′ terminates-with V-num (V-succ numeric))
  eval (pred x) with eval x
  ... | inj₁ stuck = inj₁ (stuck-pred stuck)
  ... | inj₂ (x′ , x%↠x′ terminates-with V-bool boolean) = inj₁ (E-pred↠ x%↠x′ stuck-%↠ stuck-pred-bool boolean)
  ... | inj₂ (zero , x%↠zero terminates-with V-num V-zero) = inj₂ (zero , (pred x %↠⟨ E-pred↠ x%↠zero ⟩ pred zero %→⟨ E-predZero ⟩ zero ∎) terminates-with V-num V-zero)
  ... | inj₂ (succ x′ , x%↠succ-x′ terminates-with V-num (V-succ numeric)) = inj₂ (x′ , (pred x %↠⟨ E-pred↠ x%↠succ-x′ ⟩ pred (succ x′) %→⟨ E-predSucc numeric ⟩ x′ ∎) terminates-with V-num numeric)
  eval (iszero x) with eval x
  ... | inj₁ stuck = inj₁ (stuck-iszero stuck)
  ... | inj₂ (x′ , x%↠x′ terminates-with V-bool boolean) = inj₁ (E-iszero↠ x%↠x′ stuck-%↠ stuck-iszero-bool boolean)
  ... | inj₂ (zero , x%↠zero terminates-with V-num V-zero) = inj₂ (true , (iszero x %↠⟨ E-iszero↠ x%↠zero ⟩ iszero zero %→⟨ E-iszeroZero ⟩ true ∎) terminates-with V-bool V-true)
  ... | inj₂ (succ x′ , x%↠succ-x′ terminates-with V-num (V-succ numeric)) = inj₂ (false , (iszero x %↠⟨ E-iszero↠ x%↠succ-x′ ⟩ iszero (succ x′) %→⟨ E-iszeroSucc numeric ⟩ false ∎) terminates-with V-bool V-false)
