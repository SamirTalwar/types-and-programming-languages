module Tapl.Part1.Chapter06 where

open import Data.Fin
open import Data.Nat

infix 10 !_
infixl 9 _$_
infixr 8 fn_

data Term (n : ℕ) : Set where
  !_ : Fin n → Term n
  fn_ : Term (suc n) → Term n
  _$_ : Term n → Term n → Term n

liftTerm : {n : ℕ} → Term n → Term (suc n)
liftTerm (! x)   = ! inject₁ x
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
  open import Function using (_∘_)
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary

  import Tapl.Part1.Chapter05
  open Tapl.Part1.Chapter05.LambdaCalculus using (Id; Lang; !_; fn_⇒_; _$_; prim-app)

  Γ : ℕ → Set
  Γ n = Vec Id n

  append : ∀ {A : Set} {n} → A → Vec A n → Vec A (suc n)
  append x xs = Vec.reverse (x ∷ Vec.reverse xs)

  removeNames : {n : ℕ} → Γ n → Lang ⊥ → Maybe (Term n)
  removeNames free (! x) = Maybe.map (!_ ∘ opposite) (removeNames′ free x)
    where
    removeNames′ : {n : ℕ} → Γ n → Id → Maybe (Fin n)
    removeNames′ [] x = nothing
    removeNames′ (_∷_ {n} x′ free) x with does (x ≈? x′)
    ... | false = Maybe.map inject₁ (removeNames′ free x)
    ... | true  = just (fromℕ n)
  removeNames free (fn x ⇒ t) = Maybe.map (fn_) (removeNames (x ∷ free) t)
  removeNames free (f $ x) =
    let open Data.Maybe using (_>>=_) in do
      f′ ← removeNames free f
      x′ ← removeNames free x
      just (f′ $ x′)
  removeNames free (prim-app _ _ _) = nothing

  restoreNames : {n : ℕ} → Γ n → List Id → Term n → Maybe (Lang ⊥)
  restoreNames {n} free fresh (! x) = just (! Vec.lookup free x)
  restoreNames free []          (fn t) = nothing
  restoreNames free (x ∷ fresh) (fn t) = Maybe.map (fn x ⇒_) (restoreNames (x ∷ free) fresh t)
  restoreNames free fresh (f $ x) =
    let open Data.Maybe using (_>>=_) in do
      f′ ← restoreNames free fresh f
      x′ ← restoreNames free fresh x
      just (f′ $ x′)

  _ : removeNames [] (fn "s" ⇒ fn "z" ⇒ ! "z") ≡ just (fn (fn (! inject (fromℕ 0))))
  _ = refl

  _ : removeNames [] (fn "s" ⇒ fn "z" ⇒ ! "z" $ (! "s" $ ! "z")) ≡ just (fn (fn (! inject (fromℕ 0) $ ((! fromℕ 1) $ (! inject (fromℕ 0))))))
  _ = refl

  _ : let
        t = fn "s" ⇒ fn "z" ⇒ ! "z" $ (! "s" $ ! "z")
      in
        (removeNames [] t Maybe.>>= restoreNames [] ("s" ∷ "z" ∷ [])) ≡ just t
  _ = refl

  _ : let
        free = "x" ∷ []
        t = fn "s" ⇒ fn "z" ⇒ ! "x" $ (! "s" $ ! "z")
      in
        (removeNames free t Maybe.>>= restoreNames free ("s" ∷ "z" ∷ [])) ≡ just t
  _ = refl
