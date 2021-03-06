module Complexity where

-- Inductive ℕ numbers definition.
data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- Precedence and associativity of operators.
infixl 5 _≡_
infixl 6 _+_
infixl 7 _*_

-- Run-time addition function
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

{-# BUILTIN NATPLUS _+_ #-}

-- Run-time multiplication function
_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + m * n

{-# BUILTIN NATTIMES _*_ #-}

-- Lists
data List (A : Set) : Set where
  []  : List A
  _∷_ : (x : A) → (xs : List A ) → List A


-- Equality
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- Congruence
cong : {A : Set} {B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

-- Symmetry
sym : {A : Set}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- Transitivity
trans : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

-- THUNK abstract functions
abstract
  {-

    ℕ-thunk is a ℕ number with a complexity annotation, for example, if

      β : ℕ-thunk 5 it means that

    in order to "compute" β (reach WHNF) 5 units of time are required.

  -}
  ℕ-thunk : ℕ → Set
  ℕ-thunk n = ℕ

  -- ✓ (typed \checkmark) is a tick and represents + 1 units of time.
  ✓ : {n : ℕ} → ℕ-thunk n → ℕ-thunk (1 + n)
  ✓ x = x

  -- Lifting of regular data types to ℕ-thunk
  return : ℕ → ℕ-thunk 0
  return x = x

  -- Apply a function over a ℕ-thunk value and add up their complexities.
  _>>=_  : {m n : ℕ} → ℕ-thunk m → ( ℕ → ℕ-thunk n ) → ℕ-thunk (n + m)
  x >>= f = f x

  -- Extract a value from a ℕ-thunk, don't use inside ... → ℕ-thunk functions.
  force : {n : ℕ} → ℕ-thunk n  → ℕ
  force x = x

  -- Replace equal complexities, mostly used to deal with arithmetic errors.
  cast : {n₁ n₂ : ℕ} → n₁ ≡ n₂ → ℕ-thunk n₁ → ℕ-thunk n₂
  cast _ x = x

-- Run-time functions

min' : ℕ → ℕ → ℕ
min' zero _          = zero
min' _    zero       = zero
min' (suc n) (suc m) = suc (min' n m)

length' : {A : Set} → List A → ℕ
length' []       = zero
length' (_ ∷ xs) = 1 + length' xs

-- Example

-- ℕ successor function with time complexity of O(1)
suc₁ :  ℕ → ℕ-thunk 1
suc₁ n = ✓ (return ( suc n ))

-- λ x → x + 5 function with time complexity O(1 + x)
sum5 : (a : ℕ) → ℕ-thunk (1 + a)
sum5 zero    = ✓ (return 5)  -- Base case, the cost of returning zero O(1)
sum5 (suc n) = sum5 n >>= suc₁  -- Recursive case,
                                -- cost of computing sum5 n O(1 + n)
                                -- cost of suc₁ O(1)

sum : (a : ℕ) → (b : ℕ) → ℕ-thunk (1 + a)
sum zero    n = ✓ (return n)
sum (suc m) n = sum m n >>= suc₁

aux₁ : {n : ℕ} →  zero ≡ min' n zero
aux₁ {zero}  = refl
aux₁ {suc n} = refl

max : (n : ℕ) → (m : ℕ) → ℕ-thunk (1 + min' n m)
max zero    m       = ✓ (return m)
max n       zero    = ✓ (cast (aux₁ {n}) (return n))
max (suc n) (suc m) = max n m >>= suc₁

min : (n : ℕ) → (m : ℕ) → ℕ-thunk (1 + min' n m)
min zero m          =  ✓ (return zero)
min n    zero       =  ✓ (cast (aux₁ {n}) (return n))
min (suc n) (suc m) = min n m >>= suc₁
