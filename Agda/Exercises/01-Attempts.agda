{-# OPTIONS --without-K --allow-unsolved-metas #-}

module 01-Attempts where

open import prelude hiding (not-is-involution)

_&&'_ : Bool → Bool → Bool
true &&' true = true
false &&' true = false
true &&' false = false
false &&' false = false

_xor_ : Bool → Bool → Bool
true xor b = not b
false xor b = b

_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ suc m = n * (n ^ m)

^-example : 3 ^ 4 ≡ 81
^-example = refl 81

_! : ℕ → ℕ
zero ! = 1
suc n ! = (suc n) * (n !)

!-example : 4 ! ≡ 24
!-example = refl 24

min : ℕ → ℕ → ℕ
min zero m = 0
min (suc n) zero = 0
min (suc n) (suc m) = suc (min n m)

min-example : min 5 3 ≡ 3
min-example = refl 3

map : {X Y : Type} → (X → Y) → List X → List Y
map f [] = []
map f (x :: xs) = f x :: map f xs

map-example : map (_+ 3) (1 :: 2 :: 3 :: []) ≡ 4 :: 5 :: 6 :: []
map-example = refl _

filter : {X : Type} (p : X → Bool) → List X → List X
filter p [] = []
filter p (x :: xs) = if p x
                     then x :: filter p xs
                     else filter p xs

is-non-zero : ℕ → Bool
is-non-zero zero    = false
is-non-zero (suc _) = true

filter-example : filter is-non-zero (4 :: 3 :: 0 :: 1 :: 0 :: []) ≡ 4 :: 3 :: 1 :: []
filter-example = refl _

_≣_ : Bool → Bool → Type
true ≣ true = 𝟙
false ≣ false = 𝟙
a ≣ b = 𝟘

Bool-refl : (b : Bool) → b ≣ b
Bool-refl true = ⋆
Bool-refl false = ⋆

≡-to-≣ : (a b : Bool) → a ≡ b → a ≣ b
≡-to-≣  a a (refl a) = Bool-refl a

≣-to-≡ : (a b : Bool) → a ≣ b → a ≡ b
≣-to-≡ true true ⋆ = refl true
≣-to-≡ false false ⋆ = refl false

not-is-involution : (b : Bool) → not (not b) ≡ b
not-is-involution true  = refl true
not-is-involution false = refl false

||-is-commutative : (a b : Bool) → a || b ≡ b || a
||-is-commutative true true = refl true
||-is-commutative true false = refl true
||-is-commutative false true = refl true
||-is-commutative false false = refl false

&&-is-commutative : (a b : Bool) → a && b ≡ b && a
&&-is-commutative true true = refl true
&&-is-commutative true false = refl false
&&-is-commutative false true = refl false
&&-is-commutative false false = refl false

&&-is-associative : (a b c : Bool) → a && (b && c) ≡ (a && b) && c
&&-is-associative true b c = refl (b && c)
&&-is-associative false b c = refl false

&&'-is-associative : (a b c : Bool) → a &&' (b &&' c) ≡ (a &&' b) &&' c
&&'-is-associative true true true = refl true
&&'-is-associative true true false = refl false
&&'-is-associative true false true = refl false
&&'-is-associative true false false = refl false
&&'-is-associative false true true = refl false
&&'-is-associative false true false = refl false
&&'-is-associative false false true = refl false
&&'-is-associative false false false = refl false

min-is-commutative : (n m : ℕ) → min n m ≡ min m n
min-is-commutative zero zero = refl 0
min-is-commutative zero (suc m) = refl 0
min-is-commutative (suc n) zero = refl 0
min-is-commutative (suc n) (suc m) = to-show
  where
    IH : min n m ≡ min m n
    IH = min-is-commutative n m
    to-show : suc (min n m) ≡ suc (min m n)
    to-show = ap suc IH

0-right-neutral : (n : ℕ) → n ≡ n + 0
0-right-neutral zero = refl 0
0-right-neutral (suc n) = ap suc (0-right-neutral n)

map-id : {X : Type} (xs : List X) → map id xs ≡ xs
map-id [] = refl []
map-id (x :: xs) = ap (x ::_) (map-id xs)

map-comp : {X Y Z : Type} (f : X → Y) (g : Y → Z)
           (xs : List X) → map (g ∘ f) xs ≡ map g (map f xs)
map-comp f g [] = refl []
map-comp f g (x :: xs) = ap (g (f x) ::_) (map-comp f g xs)


{-
0-left-neutral : (n : ℕ) → n ≡ 0 + n
0-left-neutral n = refl n

interleaved mutual

  +-is-commutative : (n m : ℕ) → n + m ≡ m + n
  0-right-neutral : (n : ℕ) → n ≡ n + 0

  +-is-commutative zero zero = refl 0
  +-is-commutative zero (suc m) = ap suc (0-right-neutral m)
  +-is-commutative (suc n) 0 = ap suc (+-is-commutative n 0)
  +-is-commutative (suc n) (suc m) = to-show
    where
      IH : n + m ≡ m + n
      IH = +-is-commutative n m
      to-show : suc (n + suc m) ≡ suc (m + suc n)
      to-show = ap suc ( trans (+-is-commutative n (suc m)) {!!} )  --(trans (+-is-commutative m suc n)  )

--n + suc m = m + suc n
--suc m + n = m + suc n

  0-right-neutral n = trans (0-left-neutral n) (+-is-commutative 0 n)
-}
