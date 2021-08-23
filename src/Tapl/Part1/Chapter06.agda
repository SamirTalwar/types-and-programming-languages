module Tapl.Part1.Chapter06 where

open import Data.Fin as Fin using (Fin; zero; suc; #_; _≟_)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
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

module Examples where
  !id : ∀ {n} → Term n
  !id = fn ! 0

  !true !false !if !not !and !or : ∀ {n} → Term n
  !true  = fn fn ! 1
  !false = fn fn ! 0
  !if = fn fn fn (! 2 $ ! 1 $ ! 0)
  !not = fn fn fn (! 2 $ ! 0 $ ! 1)
  !and = fn fn (! 1 $ ! 0 $ !false)
  !or = fn fn (! 1 $ !true $ ! 0)

  !pair !fst !snd : ∀ {n} → Term n
  !pair = fn fn fn (! 0 $ ! 2 $ ! 1)
  !fst = fn (! 0 $ !true)
  !snd = fn (! 0 $ !false)

  !ℕ0 !ℕ1 !ℕ2 !ℕ3 !iszero !succ !pred !+ !- !* !^ !eq : ∀ {n} → Term n
  !ℕ0 = fn fn ! 0
  !ℕ1 = fn fn (! 1 $ ! 0)
  !ℕ2 = fn fn (! 1 $ (! 1 $ ! 0))
  !ℕ3 = fn fn (! 1 $ (! 1 $ (! 1 $ ! 0)))
  !iszero = fn (! 0 $ (fn !false) $ !true)
  !succ = fn fn fn (! 1 $ (! 2 $ ! 1 $ ! 0))
  !pred = fn (!fst $ (! 0 $ (fn (!pair $ (!snd $ ! 0) $ (!succ $ (!snd $ ! 0)))) $ (!pair $ !ℕ0 $ !ℕ0)))
  !+ = fn fn fn fn (! 3 $ ! 1 $ (! 2 $ ! 1 $ ! 0))
  !- = fn fn (! 0 $ !pred $ ! 1)
  !* = fn fn (! 0 $ (!+ $ ! 1) $ !ℕ0)
  !^ = fn fn (! 0 $ (!* $ ! 1) $ !ℕ1)
  !eq = fn fn (!and $ (!iszero $ (!- $ ! 1 $ ! 0)) $ (!iszero $ (!- $ ! 0 $ ! 1)))

  !ℕ : ∀ {n} → ℕ → Term n
  !ℕ n = fn fn (!ℕ′ n)
    where
    !ℕ′ : ∀ {n} → ℕ → Term (suc (suc n))
    !ℕ′ zero = ! 0
    !ℕ′ (suc n) = ! 1 $ !ℕ′ n

  !nil !cons !isnil !head !tail : ∀ {n} → Term n
  !nil = fn fn ! 0
  !cons = fn fn fn fn (! 1 $ ! 3 $ (! 2 $ ! 1 $ ! 0))
  !isnil = fn (! 0 $ (fn fn !false) $ !true)
  !head = fn fn (! 1 $ (fn fn ! 1) $ ! 0)
  !tail = fn (!fst $ (! 0 $ (fn fn (!pair $ (!snd $ ! 0) $ (!cons $ ! 1 $ (!snd $ ! 0)))) $ (!pair $ !nil $ !nil)))

  !omega : ∀ {n} → Term n
  !omega = (fn (! 0 $ ! 0)) $ (fn (! 0 $ ! 0))

  !fix : ∀ {n} → Term n
  !fix = fn ((fn (! 1 $ (! 0 $ ! 0))) $ (fn (! 1 $ (! 0 $ ! 0))))

  !factorial : ∀ {n} → Term n
  !factorial = !fix $ (fn fn (!if $ (!iszero $ ! 0) $ !ℕ1 $ (!* $ ! 0 $ (! 1 $ (!pred $ ! 0)))))

  !sum : ∀ {n} → Term n
  !sum = fn (! 0 $ !+ $ !ℕ0)

module Conversions where
  open import Data.Bool
  open import Data.Empty
  open import Data.List as List using (List; []; _∷_)
  import Data.Maybe
  open import Data.Maybe as Maybe using (Maybe; just; nothing)
  open import Data.Product
  open import Data.String
  open import Data.Vec as Vec using (Vec; []; _∷_)
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

  ↑ : ∀ {n} → Term n → Term (suc n)
  ↑ = ↑′ zero
    where
    ↑′ : ∀ {n} → Fin (suc n) → Term n → Term (suc n)
    ↑′ cut-off (var x) with does (cut-off Fin.≤? Fin.inject₁ x)
    ... | false = var (Fin.inject₁ x)
    ... | true  = var (suc x)
    ↑′ cut-off (fn t) = fn (↑′ (suc cut-off) t)
    ↑′ cut-off (f $ x) = ↑′ cut-off f $ ↑′ cut-off x

  infix 12 [_↦_]_

  [_↦_]_ : ∀ {n} → Fin n → Term n → Term n → Term n
  [ n ↦ s ] t@(var x) with does (x ≟ n)
  ... | false = t
  ... | true  = s
  [ n ↦ s ] (fn t) = fn [ suc n ↦ (↑ s) ] t
  [ n ↦ s ] (f $ x) = ([ n ↦ s ] f) $ ([ n ↦ s ] x)

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

module Reduction where
  open import Data.Bool using (false; true)
  import Data.Fin.Properties as Finₚ
  import Data.Maybe
  open import Data.Maybe as Maybe using (Maybe; just; nothing)
  import Data.Nat.Properties as ℕₚ
  open import Relation.Binary.PropositionalEquality
  open import Relation.Nullary
  open Substitution
  open Examples

  data Reduction (n : ℕ) : Set where
    failed : Term n → Reduction n
    reducing : Term n → Reduction n
    reduced : Term n → Reduction n

  reduction-map : ∀ {m n} → (Term m → Term n) → Reduction m → Reduction n
  reduction-map f (failed t)   = failed (f t)
  reduction-map f (reducing t) = reducing (f t)
  reduction-map f (reduced t)  = reduced (f t)

  ↓ : ∀ {n} → Term (suc n) → Maybe (Term n)
  ↓ t = ↓′ zero t
    where
    ↓var : ∀ {n} → Fin (suc n) → Fin (suc n) → Maybe (Fin n)
    ↓var         zero          zero    = nothing
    ↓var {suc n} zero          (suc v) = just v
    ↓var {suc n} (suc cut-off) zero    = just zero
    ↓var {suc n} (suc cut-off) (suc v) = Maybe.map suc (↓var cut-off v)
    ↓′ : ∀ {n} → Fin (suc n) → Term (suc n) → Maybe (Term n)
    ↓′ cut-off (var v) = Maybe.map var (↓var cut-off v)
    ↓′ cut-off (fn t) = Maybe.map fn_ (↓′ (suc cut-off) t)
    ↓′ cut-off (f $ x) =
      let open Data.Maybe using (_>>=_) in
      do
        f′ ← ↓′ cut-off f
        x′ ← ↓′ cut-off x
        just (f′ $ x′)

  reduce : ∀ {n} → Term n → Reduction n
  reduce t@(var _) = reduced t
  reduce (fn t) = reduction-map fn_ (reduce t)
  reduce (var v $ x) = reduction-map (var v $_) (reduce x)
  reduce (t@(f $ x) $ y) = reduction-map (_$ y) (reduce t)
  reduce {n} t@((fn body) $ x) with ↓ ([ zero ↦ ↑ x ] body)
  ... | nothing = failed t
  ... | just t′ = reducing t′

  _ : reduce {1} ((fn ! 0) $ ! 0) ≡ reducing (! 0)
  _ = refl

  _ : reduce {2} ((fn ! 1 $ ! 0 $ ! 2) $ (fn ! 0)) ≡ reducing (! 0 $ (fn ! 0) $ ! 1)
  _ = refl

  _ : reduce {2} ((fn ! 1 $ ! 0 $ ! 2) $ ! 0) ≡ reducing (! 0 $ ! 0 $ ! 1)
  _ = refl

  _ : reduce {1} (fn fn ! 1 $ ((fn ! 0) $ ! 0)) ≡ reducing (fn fn ! 1 $ ! 0)
  _ = refl

  reduceₙ : ∀ {n} → ℕ → Term n → Reduction n
  reduceₙ zero t = reducing t
  reduceₙ (suc fuel) t with reduce t
  ... | failed t′   = failed t′
  ... | reducing t′ = reduceₙ fuel t′
  ... | reduced t′  = reduced t′

module ExampleReductions where
  open import Data.Maybe as Maybe using (Maybe; just; nothing)
  open import Relation.Binary.PropositionalEquality
  open Examples
  open Reduction

  reduce∞ : ∀ {n} → Term n → Reduction n
  reduce∞ t = reduceₙ 100 t

  _ : reduce∞ {0} (!if $ !true $ !ℕ2 $ !ℕ3) ≡ reduced !ℕ2
  _ = refl

  _ : reduce∞ {0} (!if $ (!or $ (!not $ !true) $ (!and $ !true $ !false)) $ !ℕ3 $ !ℕ1) ≡ reduced !ℕ1
  _ = refl

  _ : reduce∞ {10} (!fst $ (!pair $ ! 5 $ ! 2)) ≡ reduced (! 5)
  _ = refl

  _ : reduce∞ {0} (!pred $ !ℕ0) ≡ reduced !ℕ0
  _ = refl

  _ : reduce∞ {0} (!pred $ !ℕ1) ≡ reduced !ℕ0
  _ = refl

  _ : reduce∞ {0} (!pred $ !ℕ2) ≡ reduced !ℕ1
  _ = refl

  _ : reduce∞ {0} (!pred $ !ℕ3) ≡ reduced !ℕ2
  _ = refl

  _ : reduce∞ {0} (!pred $ (!succ $ (!pred $ (!succ $ (!succ $ !ℕ0))))) ≡ reduced (!ℕ1)
  _ = refl

  _ : reduce∞ {0} (!^ $ !ℕ3 $ !ℕ2) ≡ reduced (!ℕ 9)
  _ = refl

  _ : reduce∞ {0} ((!cons $ !ℕ1 $ (!cons $ !ℕ2 $ (!cons $ !ℕ3 $ !nil))) $ !+ $ !ℕ0) ≡ reduced (!ℕ 6)
  _ = refl

  omega-does-not-reduce : ∀ {n} → reduce {n} !omega ≡ reducing !omega
  omega-does-not-reduce = refl

  _ : reduce∞ {0} (!factorial $ !ℕ0) ≡ reduced !ℕ1
  _ = refl

  _ : reduce∞ {0} (!factorial $ !ℕ1) ≡ reduced !ℕ1
  _ = refl

  _ : reduceₙ {0} 1000 (!factorial $ !ℕ2) ≡ reduced !ℕ2
  _ = refl

  _ : reduceₙ {0} 1000 (!factorial $ !ℕ3) ≡ reduced (!ℕ 6)
  _ = refl

  _ : reduce∞ {0} (!sum $ (!cons $ !ℕ1 $ (!cons $ !ℕ2 $ (!cons $ !ℕ3 $ (!cons $ !ℕ2 $ (!cons $ !ℕ1 $ !nil)))))) ≡ reduced (!ℕ 9)
  _ = refl
