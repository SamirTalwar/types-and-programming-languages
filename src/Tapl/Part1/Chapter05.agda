module Tapl.Part1.Chapter05 where

open import Data.Bool
open import Data.Empty
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Nat as Nat using (ℕ; zero; suc)
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
    _$p_ : (Primitive → Maybe (Lang Primitive)) → Lang Primitive → Lang Primitive -- primitive application

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
  substitute id new-term (f $p x) = f $p substitute id new-term x

  reduce₁ : ∀ {P} → Lang P → Maybe (Lang P)
  reduce₁ (! _) = nothing
  reduce₁ (fn x ⇒ t) = Maybe.map (fn x ⇒_) (reduce₁ t)
  reduce₁ (! var $ x) = Maybe.map (! var $_) (reduce₁ x) -- free variable
  reduce₁ ((fn input ⇒ output) $ x) with reduce₁ x
  ... | just x′ = just ((fn input ⇒ output) $ x′)
  ... | nothing = just (substitute input x output)
  reduce₁ (f $ x $ y) = Maybe.map (_$ y) (reduce₁ (f $ x))
  reduce₁ (prim _ $ _) = nothing -- invalid
  reduce₁ (_ $p _ $ _) = nothing -- invalid
  reduce₁ (prim _) = nothing
  reduce₁ (f $p prim x) = f x
  reduce₁ (f $p x) = Maybe.map (f $p_) (reduce₁ x)

  reduce : ∀ {P} → Lang P → ℕ → Maybe (Lang P)
  reduce _ zero = nothing
  reduce t (suc max-iterations) with reduce₁ t
  ... | nothing = just t
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

  module Examples where
    reduce∞ : Lang ⊥ → Maybe (Lang ⊥)
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

    _ : reduce∞ ((!cons $ !1 $ (!cons $ !2 $ (!cons $ !3 $ !nil))) $ !+ $ !0) ≡ reduce∞ (!+ $ !3 $ !3)
    _ = refl

    _ : reduce∞ (!isnil $ !nil) ≡ just !true
    _ = refl

    _ : reduce∞ (!isnil $ (!cons $ !1 $ !nil)) ≡ just !false
    _ = refl

    _ : reduce∞ (!head $ !nil $ !3) ≡ just !3
    _ = refl

    _ : reduce∞ (!head $ (!cons $ !true $ !nil) $ !1) ≡ just !true
    _ = refl

    _ : reduce∞ (!head $ (!cons $ !2 $ (!cons $ !false $ !nil)) $ !1) ≡ just !2
    _ = refl

    _ : reduce∞ (!tail $ !nil) ≡ just !nil
    _ = refl

    _ : reduce∞ (!tail $ (!cons $ !true $ !nil)) ≡ just !nil
    _ = refl

    -- Too slow:
    -- _ : reduce∞ (!tail $ (!cons $ !2 $ (!cons $ !false $ !nil))) ≡ just (!cons $ !false $ !nil)
    -- _ = refl
    -- _ : reduce∞ (!tail $ (!cons $ !true (!cons $ !1 $ (!cons $ !2 $ !nil)))) ≡ just (!cons $ !1 $ (!cons $ !2 $ !nil))
    -- _ = refl

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

    module LangNBExamples where
      reduce∞ : Term → Maybe Term
      reduce∞ t = reduce t 10000

      !true⇢^true : reduce∞ (!bool→^bool $ !true) ≡ just (prim (bool true))
      !true⇢^true = refl

      !false⇢^false : reduce∞ (!bool→^bool $ !false) ≡ just (prim (bool false))
      !false⇢^false = refl

      ^true⇢!true : reduce∞ (^bool→!bool $ prim (bool true)) ≡ just !true
      ^true⇢!true = refl

      ^false⇢!false : reduce∞ (^bool→!bool $ prim (bool false)) ≡ just !false
      ^false⇢!false = refl

      ^bool-round-trip : ∀ (b : Bool) → reduce∞ (!bool→^bool $ (^bool→!bool $ prim (bool b))) ≡ just (prim (bool b))
      ^bool-round-trip false = refl
      ^bool-round-trip true = refl

      !0→^0 : reduce∞ (!nat→^nat $ !0) ≡ just (prim (nat 0))
      !0→^0 = refl

      !3→^3 : reduce∞ (!nat→^nat $ !3) ≡ just (prim (nat 3))
      !3→^3 = refl
