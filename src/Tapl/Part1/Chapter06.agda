module Tapl.Part1.Chapter06 where

open import Data.Fin as Fin using (Fin; zero; suc; #_; _≟_)
open import Data.Nat as Nat using (ℕ; zero; suc)
open import Function using (_∘_)
open import Relation.Nullary.Decidable

infix 10 !_
infixl 9 _$_
infixr 8 fn_

data Term (n : ℕ) : Set where
  var : Fin n → Term n
  fn_ : Term (suc n) → Term n
  _$_ : Term n → Term n → Term n

!_ : ∀ m {n} {m<n : True (suc m Nat.≤? n)} → Term n
!_ m {m<n = m<n} = var (#_ m {m<n = m<n})

liftTerm : {n : ℕ} → Term n → Term (suc n)
liftTerm (var x) = var (Fin.inject₁ x)
liftTerm (fn t)  = fn (liftTerm t)
liftTerm (f $ x) = liftTerm f $ liftTerm x

module Conversions where
  open import Data.Bool
  open import Data.Empty
  open import Data.List as List using (List; []; _∷_)
  import Data.Maybe
  open import Data.Maybe as Maybe using (Maybe; just; nothing)
  open import Data.Product
  open import Data.String
  open import Data.Vec as Vec using (Vec; []; _∷_)
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary

  import Tapl.Part1.Chapter05
  open Tapl.Part1.Chapter05.LambdaCalculus using (Id; Lang; fn_⇒_; _$_; prim-app) renaming (!_ to !!_)

  Γ : ℕ → Set
  Γ n = Vec Id n

  append : ∀ {A : Set} {n} → A → Vec A n → Vec A (suc n)
  append x xs = Vec.reverse (x ∷ Vec.reverse xs)

  removeNames : {n : ℕ} → Γ n → Lang ⊥ → Maybe (Term n)
  removeNames free (!! x) = Maybe.map (var ∘ Fin.opposite) (removeNames′ free x)
    where
    removeNames′ : {n : ℕ} → Γ n → Id → Maybe (Fin n)
    removeNames′ [] x = nothing
    removeNames′ (_∷_ {n} x′ free) x with does (x ≈? x′)
    ... | false = Maybe.map Fin.inject₁ (removeNames′ free x)
    ... | true  = just (Fin.fromℕ n)
  removeNames free (fn x ⇒ t) = Maybe.map (fn_) (removeNames (x ∷ free) t)
  removeNames free (f $ x) =
    let open Data.Maybe using (_>>=_) in do
      f′ ← removeNames free f
      x′ ← removeNames free x
      just (f′ $ x′)
  removeNames free (prim-app _ _ _) = nothing

  restoreNames : {n : ℕ} → Γ n → List Id → Term n → Maybe (Lang ⊥)
  restoreNames {n} free fresh (var x) = just (!! Vec.lookup free x)
  restoreNames free []          (fn t) = nothing
  restoreNames free (x ∷ fresh) (fn t) = Maybe.map (fn x ⇒_) (restoreNames (x ∷ free) fresh t)
  restoreNames free fresh (f $ x) =
    let open Data.Maybe using (_>>=_) in do
      f′ ← restoreNames free fresh f
      x′ ← restoreNames free fresh x
      just (f′ $ x′)

  _ : removeNames [] (fn "s" ⇒ fn "z" ⇒ !! "z") ≡ just (fn (fn ! 0))
  _ = refl

  _ : removeNames [] (fn "s" ⇒ fn "z" ⇒ !! "z" $ (!! "s" $ !! "z")) ≡ just (fn (fn (! 0 $ (! 1 $ ! 0))))
  _ = refl

  _ : let
        t = fn "s" ⇒ fn "z" ⇒ !! "z" $ (!! "s" $ !! "z")
      in
        (removeNames [] t Maybe.>>= restoreNames [] ("s" ∷ "z" ∷ [])) ≡ just t
  _ = refl

  _ : let
        free = "x" ∷ []
        t = fn "s" ⇒ fn "z" ⇒ !! "x" $ (!! "s" $ !! "z")
      in
        (removeNames free t Maybe.>>= restoreNames free ("s" ∷ "z" ∷ [])) ≡ just t
  _ = refl

module Substitution where
  open import Data.Bool using (false; true)
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary

  infix 12 [_↦_]_

  [_↦_]_ : ∀ {n} → Fin n → Term n → Term n → Term n
  [ n ↦ s ] t = substitute n s t 0
    where
    ↑ : ∀ {n} → ℕ → Term n → Term (suc n)
    ↑ cut-off (var x) with does (Fin.toℕ x Nat.≥? cut-off)
    ... | false = var (Fin.inject₁ x)
    ... | true  = var (suc x)
    ↑ cut-off (fn t) = fn (↑ (suc cut-off) t)
    ↑ cut-off (f $ x) = ↑ cut-off f $ ↑ cut-off x
    substitute : ∀ {n} → Fin n → Term n → Term n → ℕ → Term n
    substitute n s t@(var x) cut-off with does (x ≟ n)
    ... | false = t
    ... | true  = s
    substitute n s (fn t) cut-off = fn (substitute (suc n) (↑ cut-off s) t (suc cut-off))
    substitute n s (f $ x) cut-off = (substitute n s f cut-off) $ (substitute n s x cut-off)

  _ : let
        t : Term 4
        t = ! 0
        s : Term 4
        s = ! 3
      in [ # 0 ↦ s ] t ≡ s
  _ = refl

  _ : let
        t : Term 10
        t = fn ! 0
        s : Term 10
        s = ! 7
      in [ # 0 ↦ s ] t ≡ t
  _ = refl

  _ : let
        t : Term 10
        t = fn ! 2
        s : Term 10
        s = ! 2 $ (fn ! 0)
      in [ # 1 ↦ s ] t ≡ fn (! 3 $ (fn ! 0))
  _ = refl
