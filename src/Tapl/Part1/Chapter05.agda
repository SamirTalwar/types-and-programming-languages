module Tapl.Part1.Chapter05 where

module LambdaCalculus where
  open import Data.Bool
  open import Data.Maybe as Maybe using (Maybe; just; nothing)
  open import Data.List using (List; []; _∷_)
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.String using (String; _≈?_)
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary

  Id : Set
  Id = String

  infix 10 !_
  infixl 9 _$_
  infixr 8 fn_⇒_

  data Term : Set where
    !_ : Id → Term              -- variable
    fn_⇒_ : Id → Term → Term  -- abstraction
    _$_ : Term → Term → Term   -- application

  -- Verify that parsing works.
  _ : Term
  _ = let x = "x" ; y = "y" in fn x ⇒ fn y ⇒ ! x $ ! y $ ! x

  -- Verify that precedence is as expected.
  _ : let x = "x" ; y = "y" in (fn x ⇒ fn y ⇒ ! x $ ! y $ ! x) ≡ (fn x ⇒ (fn y ⇒ ((! x $ ! y) $ ! x)))
  _ = refl

  substitute : Id → Term → Term → Term
  substitute id new-term old-term = substitute′ id new-term old-term []
    where
    contains : Id → List Id → Bool
    contains x [] = false
    contains x (y ∷ ys) with does (x ≈? y)
    ... | false = contains x ys
    ... | true  = true
    substitute′ : Id → Term → Term → List Id → Term
    substitute′ id new-term old-term@(! x) bound with does (id ≈? x) | contains id bound
    ... | true  | false = new-term
    ... | true  | true  = old-term
    ... | false | _     = old-term
    substitute′ id new-term (fn x ⇒ t) bound = fn x ⇒ substitute′ id new-term t (x ∷ bound)
    substitute′ id new-term (f $ x) bound = substitute′ id new-term f bound $ substitute′ id new-term x bound

  reduce₁ : Term → Maybe Term
  reduce₁ t@(! _) = nothing
  reduce₁ (fn x ⇒ t) = Maybe.map (fn x ⇒_) (reduce₁ t)
  reduce₁ (! var $ x) = Maybe.map (! var $_) (reduce₁ x) -- free variable
  reduce₁ ((fn input ⇒ output) $ x) with reduce₁ x
  ... | just x′ = just ((fn input ⇒ output) $ x′)
  ... | nothing = just (substitute input x output)
  reduce₁ (f $ x $ y) = Maybe.map (_$ y) (reduce₁ (f $ x))

  reduce : Term → ℕ → Maybe Term
  reduce _ zero = nothing
  reduce t (suc max-iterations) with reduce₁ t
  ... | nothing = just t
  ... | just t′ = reduce t′ max-iterations

  !id = fn "x" ⇒ ! "x"

  !true  = fn "t" ⇒ fn "f" ⇒ ! "t"
  !false = fn "t" ⇒ fn "f" ⇒ ! "f"
  !if = fn "x" ⇒ fn "t" ⇒ fn "f" ⇒ ! "x" $ ! "t" $ ! "f"
  !not = fn "x" ⇒ fn "f" ⇒ fn "t" ⇒ ! "x" $ ! "t" $ ! "f"
  !and = fn "x" ⇒ fn "y" ⇒ ! "x" $ ! "y" $ !false
  !or  = fn "x" ⇒ fn "y" ⇒ ! "x" $ !true $ ! "y"

  !pair = fn "first" ⇒ fn "second" ⇒ fn "select" ⇒ ! "select" $ ! "first" $ ! "second"
  !fst = fn "pair" ⇒ ! "pair" $ !true
  !snd = fn "pair" ⇒ ! "pair" $ !false

  lots-of-iterations = 1000

  _ : reduce (!if $ !true $ ! "true" $ ! "false") lots-of-iterations ≡ just (! "true")
  _ = refl

  _ : reduce (!if $ (!or $ (!not $ !true) $ (!and $ !true $ !false)) $ ! "true" $ ! "false") lots-of-iterations ≡ just (! "false")
  _ = refl

  _ : reduce (!fst $ (!pair $ ! "v" $ ! "w")) lots-of-iterations ≡ just (! "v")
  _ = refl
