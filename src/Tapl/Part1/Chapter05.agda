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

  !0 = fn "s" ⇒ fn "z" ⇒ ! "z"
  !1 = fn "s" ⇒ fn "z" ⇒ ! "s" $ ! "z"
  !2 = fn "s" ⇒ fn "z" ⇒ ! "s" $ (! "s" $ ! "z")
  !3 = fn "s" ⇒ fn "z" ⇒ ! "s" $ (! "s" $ (! "s" $ ! "z"))
  !iszero = fn "n" ⇒ ! "n" $ (fn "_" ⇒ !false) $ !true
  !succ = fn "n" ⇒ fn "s" ⇒ fn "z" ⇒ ! "s" $ (! "n" $ ! "s" $ ! "z")
  !pred = fn "n" ⇒ !fst $ (! "n" $ (fn "p" ⇒ !pair $ (!snd $ ! "p") $ (!succ $ (!snd $ ! "p"))) $ (!pair $ !0 $ !0))
  !+ = fn "m" ⇒ fn "n" ⇒ fn "s" ⇒ fn "z" ⇒ ! "m" $ ! "s" $ (! "n" $ ! "s" $ ! "z")
  !- = fn "m" ⇒ fn "n" ⇒ ! "n" $ !pred $ ! "m"
  !* = fn "m" ⇒ fn "n" ⇒ ! "n" $ (!+ $ ! "m") $ !0
  !^ = fn "m" ⇒ fn "n" ⇒ ! "n" $ (!* $ ! "m") $ !1
  !eq = fn "m" ⇒ fn "n" ⇒ !and $ (!iszero $ (!- $ ! "m" $ ! "n")) $ (!iszero $ (!- $ ! "n" $ ! "m"))

  reduce∞ : Term → Maybe Term
  reduce∞ t = reduce t 10000

  _ : reduce∞ (!if $ !true $ ! "true" $ ! "false") ≡ just (! "true")
  _ = refl

  _ : reduce∞ (!if $ (!or $ (!not $ !true) $ (!and $ !true $ !false)) $ ! "true" $ ! "false") ≡ just (! "false")
  _ = refl

  _ : reduce∞ (!fst $ (!pair $ ! "v" $ ! "w")) ≡ just (! "v")
  _ = refl

  _ : reduce∞ (!succ $ (!succ $ (!succ $ !0))) ≡ just !3
  _ = refl

  _ : reduce∞ (!pred $ !0) ≡ just !0
  _ = refl

  _ : reduce∞ (!pred $ (!succ $ (!pred $ (!succ $ (!succ $ !0))))) ≡ just !1
  _ = refl

  _ : reduce∞ (!iszero $ !0) ≡ just !true
  _ = refl

  _ : reduce∞ (!iszero $ !1) ≡ just !false
  _ = refl

  _ : reduce∞ (!+ $ !1 $ !2) ≡ just !3
  _ = refl

  _ : reduce∞ (!- $ !3 $ !2) ≡ just !1
  _ = refl

  _ : reduce∞ (!- $ !2 $ !3) ≡ just !0
  _ = refl

  _ : reduce∞ (!* $ !1 $ !3) ≡ just !3
  _ = refl

  _ : reduce∞ (!* $ !3 $ !2) ≡ reduce∞ (!+ $ !3 $ !3)
  _ = refl

  _ : reduce∞ (!iszero $ (!* $ !2 $ !0)) ≡ just !true
  _ = refl

  _ : reduce∞ (!^ $ !2 $ !1) ≡ just !2
  _ = refl

  _ : reduce∞ (!^ $ !3 $ !2) ≡ reduce∞ (!+ $ !3 $ (!+ $ !3 $ !3))
  _ = refl

  _ : reduce∞ (!eq $ !3 $ !2) ≡ just !false
  _ = refl

  _ : reduce∞ (!eq $ !2 $ !2) ≡ just !true
  _ = refl

  _ : reduce∞ (!eq $ (!+ $ !2 $ !2) $ (!* $ !2 $ !2)) ≡ just !true
  _ = refl

  _ : reduce∞ (!eq $ (!+ $ !3 $ !3) $ (!* $ !3 $ !3)) ≡ just !false
  _ = refl
