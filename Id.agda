module Nat where


data ℕ : Set where
     zero : ℕ
     suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- infixr 10 _+_
-- _+_ : ℕ → ℕ → ℕ
-- 0 + b = b
-- suc a + b = suc (a + b)


-- infix 20 _*_
-- _*_ : ℕ → ℕ → ℕ
-- 0 * b = 0
-- (suc a) * b = b + a * b

-- id : ℕ → ℕ
-- id n = n

-- id : {A : Set} → A → A
-- id x = x

-- id'' : ℕ → ℕ
-- id'' = λ n → n

id' : (A : Set) → (x : A) → A
id' A x  = x

s1 : ℕ
s1 = id' ℕ 1

-- t2 : (x : A) → A
-- t2 = id' (ℕ → ℕ) (id' (ℕ → ℕ))

id'' : {A : Set} → (x : A) → A
id'' x = x

t1 : ℕ
t1 = id'' 1

t2 : ℕ
t2 = id'' (id'' 1)

t3 : ℕ
t3 = id'' (id'' 1)

t4 : ℕ
t4 = id'' (id'' (id'' 1))

t5 : ℕ
t5 = id'' (id'' (id'' (id'' 1)))
                                                              