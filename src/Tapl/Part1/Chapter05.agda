module Tapl.Part1.Chapter05 where

open import Data.Bool
open import Data.Empty
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.List as List using (List; []; _∷_)
open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.Product
open import Data.String using (String; _≈?_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module LambdaCalculus where
  Id : Set
  Id = String

  infix 10 !_
  infixl 9 _$_
  infixl 9 _$p_
  infixr 8 fn_⇒_

  data Lang (Primitive : Set) : Set where
    !_ : Id → Lang Primitive                                 -- variable
    fn_⇒_ : Id → Lang Primitive → Lang Primitive           -- abstraction
    _$_ : Lang Primitive → Lang Primitive → Lang Primitive  -- application
    prim : Primitive → Lang Primitive                        -- primitive
    prim-app :                                                -- primitive application
        (Primitive → Maybe (Lang Primitive))    -- function
      → List (Id × Lang Primitive)              -- delayed substitution
      → Lang Primitive                          -- term
      → Lang Primitive

  _$p_ : ∀ {Primitive} → (Primitive → Maybe (Lang Primitive)) → Lang Primitive → Lang Primitive
  f $p x = prim-app f [] x

  -- Verify that parsing works.
  _ : ∀ {P} → Lang P
  _ = let x = "x" ; y = "y" in fn x ⇒ fn y ⇒ ! x $ ! y $ ! x

  -- Verify that precedence is as expected.
  _ : ∀ {P} →
      let
        x = "x"
        y = "y"
        f : Lang P
        f = fn x ⇒ fn y ⇒ ! x $ ! y $ ! x
        g : Lang P
        g = fn x ⇒ (fn y ⇒ ((! x $ ! y) $ ! x))
      in f ≡ g
  _ = refl

  substitute : ∀ {P} → Id → Lang P → Lang P → Lang P
  substitute id new-term old-term@(! x) with does (id ≈? x)
  ... | true  = new-term
  ... | false = old-term
  substitute id new-term t@(fn input ⇒ output) with does (id ≈? input)
  ... | true = t
  ... | false = fn input ⇒ substitute id new-term output
  substitute id new-term (f $ x) = substitute id new-term f $ substitute id new-term x
  substitute _ _ old-term@(prim _) = old-term
  substitute id new-term (prim-app f substitutions x) = prim-app f ((id , new-term) ∷ substitutions) (substitute id new-term x)

  reduce₁ : ∀ {P} → Lang P → Maybe (Lang P)
  reduce₁ (! _) = nothing
  reduce₁ (fn x ⇒ t) = Maybe.map (fn x ⇒_) (reduce₁ t)
  reduce₁ (! var $ x) = Maybe.map (! var $_) (reduce₁ x) -- free variable
  reduce₁ ((fn input ⇒ output) $ x) = just (substitute input x output)
  reduce₁ (t@(f $ x) $ y) = Maybe.map (_$ y) (reduce₁ t)
  reduce₁ (t@(prim-app f substitutions x) $ y) = Maybe.map (_$ y) (reduce₁ t)
  reduce₁ (prim _ $ _) = nothing -- invalid
  reduce₁ (prim _) = nothing
  reduce₁ (prim-app f substitutions (prim x)) = Maybe.map (λ x′ → List.foldl (λ{ t (id , new-term) → substitute id new-term t }) x′ substitutions) (f x)
  reduce₁ (prim-app f substitutions x) = Maybe.map (prim-app f substitutions) (reduce₁ x)

  reduce : ∀ {P} → Lang P → ℕ → Lang P
  reduce t zero = t
  reduce t (suc max-iterations) with reduce₁ t
  ... | nothing = t
  ... | just t′ = reduce t′ max-iterations

  !id : ∀ {P} → Lang P
  !id = fn "x" ⇒ ! "x"

  !true  : ∀ {P} → Lang P
  !true  = fn "t" ⇒ fn "f" ⇒ ! "t"
  !false : ∀ {P} → Lang P
  !false = fn "t" ⇒ fn "f" ⇒ ! "f"
  !if : ∀ {P} → Lang P
  !if = fn "x" ⇒ fn "t" ⇒ fn "f" ⇒ ! "x" $ ! "t" $ ! "f"
  !not : ∀ {P} → Lang P
  !not = fn "x" ⇒ fn "f" ⇒ fn "t" ⇒ ! "x" $ ! "t" $ ! "f"
  !and : ∀ {P} → Lang P
  !and = fn "x" ⇒ fn "y" ⇒ ! "x" $ ! "y" $ !false
  !or : ∀ {P} → Lang P
  !or  = fn "x" ⇒ fn "y" ⇒ ! "x" $ !true $ ! "y"

  !pair : ∀ {P} → Lang P
  !pair = fn "first" ⇒ fn "second" ⇒ fn "select" ⇒ ! "select" $ ! "first" $ ! "second"
  !fst : ∀ {P} → Lang P
  !fst = fn "pair" ⇒ ! "pair" $ !true
  !snd : ∀ {P} → Lang P
  !snd = fn "pair" ⇒ ! "pair" $ !false

  !0 : ∀ {P} → Lang P
  !0 = fn "s" ⇒ fn "z" ⇒ ! "z"
  !1 : ∀ {P} → Lang P
  !1 = fn "s" ⇒ fn "z" ⇒ ! "s" $ ! "z"
  !2 : ∀ {P} → Lang P
  !2 = fn "s" ⇒ fn "z" ⇒ ! "s" $ (! "s" $ ! "z")
  !3 : ∀ {P} → Lang P
  !3 = fn "s" ⇒ fn "z" ⇒ ! "s" $ (! "s" $ (! "s" $ ! "z"))
  !iszero : ∀ {P} → Lang P
  !iszero = fn "n" ⇒ ! "n" $ (fn "_" ⇒ !false) $ !true
  !succ : ∀ {P} → Lang P
  !succ = fn "n" ⇒ fn "s" ⇒ fn "z" ⇒ ! "s" $ (! "n" $ ! "s" $ ! "z")
  !pred : ∀ {P} → Lang P
  !pred = fn "n" ⇒ !fst $ (! "n" $ (fn "p" ⇒ !pair $ (!snd $ ! "p") $ (!succ $ (!snd $ ! "p"))) $ (!pair $ !0 $ !0))
  !+ : ∀ {P} → Lang P
  !+ = fn "m" ⇒ fn "n" ⇒ fn "s" ⇒ fn "z" ⇒ ! "m" $ ! "s" $ (! "n" $ ! "s" $ ! "z")
  !- : ∀ {P} → Lang P
  !- = fn "m" ⇒ fn "n" ⇒ ! "n" $ !pred $ ! "m"
  !* : ∀ {P} → Lang P
  !* = fn "m" ⇒ fn "n" ⇒ ! "n" $ (!+ $ ! "m") $ !0
  !^ : ∀ {P} → Lang P
  !^ = fn "m" ⇒ fn "n" ⇒ ! "n" $ (!* $ ! "m") $ !1
  !eq : ∀ {P} → Lang P
  !eq = fn "m" ⇒ fn "n" ⇒ !and $ (!iszero $ (!- $ ! "m" $ ! "n")) $ (!iszero $ (!- $ ! "n" $ ! "m"))

  !nil : ∀ {P} → Lang P
  !nil = fn "c" ⇒ fn "n" ⇒ ! "n"
  !cons : ∀ {P} → Lang P
  !cons = fn "x" ⇒ fn "xs" ⇒ fn "c" ⇒ fn "n" ⇒ ! "c" $ ! "x" $ (! "xs" $ ! "c" $ ! "n")
  !isnil : ∀ {P} → Lang P
  !isnil = fn "xs" ⇒ ! "xs" $ (fn "_" ⇒ fn "_" ⇒ !false) $ !true
  !head : ∀ {P} → Lang P
  !head = fn "xs" ⇒ fn "default" ⇒ ! "xs" $ (fn "x" ⇒ fn "_" ⇒ ! "x") $ ! "default"
  !tail : ∀ {P} → Lang P
  !tail = fn "xs" ⇒ !fst $ (! "xs" $ (fn "x" ⇒ fn "p" ⇒ !pair $ (!snd $ ! "p") $ (!cons $ ! "x" $ (!snd $ ! "p"))) $ (!pair $ !nil $ !nil))

  !omega : ∀ {P} → Lang P
  !omega = (fn "x" ⇒ ! "x" $ ! "x") $ (fn "x" ⇒ ! "x" $ ! "x")

  !fix : ∀ {P} → Lang P
  !fix = fn "f" ⇒ (fn "x" ⇒ ! "f" $ (! "x" $ ! "x")) $ (fn "x" ⇒ ! "f" $ (! "x" $ ! "x"))

  !factorial : ∀ {P} → Lang P
  !factorial = !fix $ (fn "recurse" ⇒ fn "n" ⇒ !if $ (!iszero $ ! "n") $ !1 $ (!* $ ! "n" $ (! "recurse" $ (!pred $ ! "n"))))

  !sum : ∀ {P} → Lang P
  !sum = fn "list" ⇒ ! "list" $ !+ $ !0

  module Examples where
    reduce∞ : Lang ⊥ → Lang ⊥
    reduce∞ t = reduce t 100

    _ : reduce∞ (!if $ !true $ ! "true" $ ! "false") ≡ ! "true"
    _ = refl

    _ : reduce∞ (!if $ (!or $ (!not $ !true) $ (!and $ !true $ !false)) $ ! "true" $ ! "false") ≡ ! "false"
    _ = refl

    _ : reduce∞ (!fst $ (!pair $ ! "v" $ ! "w")) ≡ ! "v"
    _ = refl

    _ : reduce∞ (!succ $ (!succ $ (!succ $ !0))) ≡ !3
    _ = refl

    _ : reduce∞ (!pred $ !0) ≡ !0
    _ = refl

    _ : reduce∞ (!pred $ (!succ $ (!pred $ (!succ $ (!succ $ !0))))) ≡ !1
    _ = refl

    _ : reduce∞ (!iszero $ !0) ≡ !true
    _ = refl

    _ : reduce∞ (!iszero $ !1) ≡ !false
    _ = refl

    _ : reduce∞ (!+ $ !1 $ !2) ≡ !3
    _ = refl

    _ : reduce∞ (!- $ !3 $ !2) ≡ !1
    _ = refl

    _ : reduce∞ (!- $ !2 $ !3) ≡ !0
    _ = refl

    _ : reduce∞ (!* $ !1 $ !3) ≡ !3
    _ = refl

    _ : reduce∞ (!* $ !3 $ !2) ≡ reduce∞ (!+ $ !3 $ !3)
    _ = refl

    _ : reduce∞ (!iszero $ (!* $ !2 $ !0)) ≡ !true
    _ = refl

    _ : reduce∞ (!^ $ !2 $ !1) ≡ !2
    _ = refl

    _ : reduce∞ (!^ $ !3 $ !2) ≡ reduce∞ (!+ $ !3 $ (!+ $ !3 $ !3))
    _ = refl

    _ : reduce {⊥} (!eq $ !3 $ !2) 1000 ≡ !false
    _ = refl

    _ : reduce {⊥} (!eq $ !2 $ !2) 1000 ≡ !true
    _ = refl

    _ : reduce {⊥} (!eq $ (!+ $ !2 $ !2) $ (!* $ !2 $ !2)) 1000 ≡ !true
    _ = refl

    _ : reduce {⊥} (!eq $ (!+ $ !3 $ !3) $ (!* $ !3 $ !3)) 10000 ≡ !false
    _ = refl

    _ : reduce∞ ((!cons $ !1 $ (!cons $ !2 $ (!cons $ !3 $ !nil))) $ !+ $ !0) ≡ reduce∞ (!+ $ !3 $ !3)
    _ = refl

    _ : reduce∞ (!isnil $ !nil) ≡ !true
    _ = refl

    _ : reduce∞ (!isnil $ (!cons $ !1 $ !nil)) ≡ !false
    _ = refl

    _ : reduce∞ (!head $ !nil $ !3) ≡ !3
    _ = refl

    _ : reduce∞ (!head $ (!cons $ !true $ !nil) $ !1) ≡ !true
    _ = refl

    _ : reduce∞ (!head $ (!cons $ !2 $ (!cons $ !false $ !nil)) $ !1) ≡ !2
    _ = refl

    _ : reduce∞ (!tail $ !nil) ≡ !nil
    _ = refl

    _ : reduce∞ (!tail $ (!cons $ !true $ !nil)) ≡ !nil
    _ = refl

    -- Too slow:
    -- _ : reduce∞ (!tail $ (!cons $ !2 $ (!cons $ !false $ !nil))) ≡ !cons $ !false $ !nil
    -- _ = refl
    -- _ : reduce∞ (!tail $ (!cons $ !true (!cons $ !1 $ (!cons $ !2 $ !nil)))) ≡ !cons $ !1 $ (!cons $ !2 $ !nil)
    -- _ = refl

    omega-does-not-reduce : ∀ {P} → reduce₁ {P} !omega ≡ just !omega
    omega-does-not-reduce = refl

    _ : reduce∞ (!factorial $ !0) ≡ !1
    _ = refl

    _ : reduce∞ (!factorial $ !1) ≡ !1
    _ = refl

    _ : reduce {⊥} (!factorial $ !2) 1000 ≡ !2
    _ = refl

    _ : reduce {⊥} (!factorial $ !3) 1000 ≡ reduce∞ (!+ $ !3 $ !3)
    _ = refl

    _ : reduce∞ (!sum $ (!cons $ !1 $ (!cons $ !2 $ (!cons $ !3 $ (!cons $ !2 $ (!cons $ !1 $ !nil)))))) ≡ reduce∞ (!+ $ !3 $ (!+ $ !3 $ !3))
    _ = refl

  module LangNB where
    data NB : Set where
      bool : Bool → NB
      nat : ℕ → NB

    Term = Lang NB

    !bool→^bool : Term
    !bool→^bool = fn "b" ⇒ ! "b" $ prim (bool true) $ prim (bool false)

    ^bool→!bool : Term
    ^bool→!bool = fn "b" ⇒ (λ{ (bool b) → just (if b then !true else !false) ; (nat _) → nothing }) $p ! "b"

    !nat→^nat : Term
    !nat→^nat = fn "n" ⇒ ! "n" $ (fn "x" ⇒ (λ{ (bool _) → nothing ; (nat n) → just (prim (nat (suc n))) }) $p ! "x") $ prim (nat zero)

    ^nat→!nat : Term
    ^nat→!nat = !fix $ (fn "recurse" ⇒ fn "n" ⇒ (λ{ (bool _) → nothing ; (nat zero) → just !0 ; (nat (suc n)) → just (!succ $ (! "recurse" $ prim (nat n))) }) $p ! "n")

    module LangNBExamples where
      reduce∞ : Term → Term
      reduce∞ t = reduce t 100

      !true⇢^true : reduce∞ (!bool→^bool $ !true) ≡ prim (bool true)
      !true⇢^true = refl

      !false⇢^false : reduce∞ (!bool→^bool $ !false) ≡ prim (bool false)
      !false⇢^false = refl

      ^true⇢!true : reduce∞ (^bool→!bool $ prim (bool true)) ≡ !true
      ^true⇢!true = refl

      ^false⇢!false : reduce∞ (^bool→!bool $ prim (bool false)) ≡ !false
      ^false⇢!false = refl

      !0→^0 : reduce∞ (!nat→^nat $ !0) ≡ prim (nat 0)
      !0→^0 = refl

      !3→^3 : reduce∞ (!nat→^nat $ !3) ≡ prim (nat 3)
      !3→^3 = refl

      ^0→!0 : reduce∞ (^nat→!nat $ prim (nat 0)) ≡ !0
      ^0→!0 = refl

      ^1→!1 : reduce∞ (^nat→!nat $ prim (nat 1)) ≡ !1
      ^1→!1 = refl

      ^3→!3 : reduce∞ (^nat→!nat $ prim (nat 3)) ≡ !3
      ^3→!3 = refl
