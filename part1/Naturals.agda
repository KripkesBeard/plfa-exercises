{-# OPTIONS --exact-split #-}

module Naturals where

{-
--    CODE USED
-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero    * n  =  zero
(suc m) * n  =  n + (m * n)

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

infixl 6  _+_  _∸_
infixl 7  _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}


{-
--    EXERCISES
-}

{- Exercise `seven` -}
-- Write out `7` in longhand.

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))


{-E xercise `+-example` -}
-- Compute `3 + 4`, writing out your reasoning as a chain of equations, using the equations for `+`.

_ : 3 + 4 ≡ 7
_ = 
  begin
    3 + 4
  ≡⟨⟩ -- Explicit constructors rewrite
    (suc (suc (suc zero))) + (suc (suc (suc (suc zero))))
  ≡⟨⟩ -- Addition definition
    suc ((suc (suc zero)) + (suc (suc (suc (suc zero)))))
  ≡⟨⟩ -- Addition definition
    suc (suc (suc zero + (suc (suc (suc (suc zero))))))
  ≡⟨⟩ -- Addition definition
    suc (suc (suc (zero + (suc (suc (suc (suc zero)))))))
  ≡⟨⟩ -- Addition definition
    suc (suc (suc (suc (suc (suc (suc zero))))))
  ≡⟨⟩ -- Numeral rewrite
    7 
  ∎  


{- Exercise `*-example` -}
-- Compute `3 * 4`, writing out your reasoning as a chain of equations, using the equations for `*`.
-- (You do not need to step through the evaluation of `+`.)


_ : 3 * 4 ≡ 12
_ = 
  begin
    3 * 4
  ≡⟨⟩ -- Multiplication definition
     4 + (2 * 4)
  ≡⟨⟩ -- Multiplication definition
     4 + (4 + (1 * 4))
  ≡⟨⟩ -- Multiplication definition
     4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩ -- Multiplication definition
     4 + (4 + (4 + 0))
  ≡⟨⟩ -- Addition
     12
  ∎


{- Exercise `_^_` -}
-- Define exponentiation, which is given by the following equations:
--
--     m ^ 0        =  1
--     m ^ (1 + n)  =  m * (m ^ n)
-- Check that `3 ^ 4` is `81`.

_^_ : ℕ → ℕ → ℕ
m ^ zero  = 1
m ^ suc n = m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ = 
  begin
    3 ^ 4
  ≡⟨⟩ -- Exponentiation definition
    3 * (3 ^ 3)
  ≡⟨⟩ -- Exponentiation definition
    3 * (3 * (3 ^ 2))
  ≡⟨⟩ -- Exponentiation definition
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩ -- Exponentiation definition
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩ -- Exponentiation definition
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩ -- Multiplication
    81
  ∎



{- Exercise `∸-example₁` and `∸-example₂` -}
-- Compute `5 ∸ 3` and `3 ∸ 5`, writing out your reasoning as a chain of equations.


_ : 5 ∸ 3 ≡ 2
_ = 
  begin
    5 ∸ 3
  ≡⟨⟩ -- Monus definition
    4 ∸ 2
  ≡⟨⟩ -- Monus definition
    3 ∸ 1
  ≡⟨⟩ -- Monus definition
    2 ∸ 0
  ≡⟨⟩ -- Monus definition
    2
  ∎ 

_ : 3 ∸ 5 ≡ 0
_ = begin
    3 ∸ 5
  ≡⟨⟩ -- Monus definition
    2 ∸ 4
  ≡⟨⟩ -- Monus definition
    1 ∸ 3
  ≡⟨⟩ -- Monus definition
    0 ∸ 2
  ≡⟨⟩ -- Monus definition
    0
  ∎


{- Exercise `Bin` -}
-- more efficient representation of natural numbers uses a binary
-- rather than a unary system.  We represent a number as a bitstring:

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

-- For instance, the bitstring
--
--     1011

-- standing for the number eleven is encoded as

--     ⟨⟩ I O I I

-- Representations are not unique due to leading zeros.
-- Hence, eleven is also represented by `001011`, encoded as:

--     ⟨⟩ O O I O I I

-- Define a function

--     inc : Bin → Bin

-- that converts a bitstring to the bitstring for the next higher
-- number.  For example, since `1100` encodes twelve, we should have:

--     inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O

-- Confirm that this gives the correct answer for the bitstrings
--encoding zero through four.

-- Using the above, define a pair of functions to convert
-- between the two representations.

--     to   : ℕ → Bin
--     from : Bin → ℕ

-- For the former, choose the bitstring to have no leading zeros if it
-- represents a positive natural, and represent zero by `⟨⟩ O`.
-- Confirm that these both give the correct answer for zero through four.

-- increment function for binary digit representation
inc : Bin → Bin
inc ⟨⟩    = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

-- Proofs that the function works for numbers 0-4
_ : inc (⟨⟩ O) ≡ ⟨⟩ I
_ =
  begin
    inc (⟨⟩ O)
  ≡⟨⟩
    ⟨⟩ I
  ∎

_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ =
  begin
    inc (⟨⟩ I)
  ≡⟨⟩
    ((inc ⟨⟩) O)
  ≡⟨⟩
    ⟨⟩ I O
  ∎ 

_ : inc (⟨⟩ I O) ≡ ⟨⟩ I I
_ = 
  begin
    inc (⟨⟩ I O)
  ≡⟨⟩
    ⟨⟩ I I
  ∎

_ : inc (⟨⟩ I I) ≡ ⟨⟩ I O O
_ = 
  begin
    inc (⟨⟩ I I)
  ≡⟨⟩
    (inc (⟨⟩ I)) O
  ≡⟨⟩
    ((inc ⟨⟩) O) O
  ≡⟨⟩
    ((⟨⟩ I) O) O
  ≡⟨⟩
    ⟨⟩ I O O
  ∎ 

_ : inc (⟨⟩ I O O) ≡ ⟨⟩ I O I
_ = 
  begin
    inc (⟨⟩ I O O)
  ≡⟨⟩
    ⟨⟩ I O I
  ∎  


BinToℕ : Bin → ℕ
BinToℕ ⟨⟩    = 0
BinToℕ (b O) = 2 * (BinToℕ b)
BinToℕ (b I) = 2 * (BinToℕ b) + 1

_ : BinToℕ (⟨⟩ O) ≡ 0
_ = 
  begin
    BinToℕ (⟨⟩ O)
  ≡⟨⟩
    2 * (BinToℕ ⟨⟩)
  ≡⟨⟩
    2 * 0
  ≡⟨⟩
    0
  ∎ 

_ : BinToℕ (⟨⟩ I) ≡ 1
_ = 
  begin
    BinToℕ (⟨⟩ I)
  ≡⟨⟩
    2 * (BinToℕ ⟨⟩) + 1 
  ≡⟨⟩
    2 * 0 + 1
  ≡⟨⟩
    1
  ∎ 

_ : BinToℕ (⟨⟩ I O) ≡ 2
_ = 
  begin
    BinToℕ (⟨⟩ I O)
  ≡⟨⟩
    2 * (BinToℕ (⟨⟩ I))
  ≡⟨⟩
    2 * (2 * (BinToℕ ⟨⟩) + 1) 
  ≡⟨⟩
    2 * (2 * 0 + 1)
  ≡⟨⟩ 
    2 * 1
  ≡⟨⟩ 
    2
  ∎

_ : BinToℕ (⟨⟩ I I) ≡ 3
_ = 
  begin
    BinToℕ (⟨⟩ I I)
  ≡⟨⟩ 
    2 * (BinToℕ (⟨⟩ I)) + 1
  ≡⟨⟩
    2 * (2 * (BinToℕ ⟨⟩) + 1) + 1
  ≡⟨⟩
    2 * (2 * 0 + 1) + 1 
  ≡⟨⟩
    2 * 1 + 1 
  ≡⟨⟩ 
    3
  ∎

_ : BinToℕ (⟨⟩ I O O) ≡ 4
_ = 
  begin 
    BinToℕ (⟨⟩ I O O)
  ≡⟨⟩ 
    2 * (BinToℕ (⟨⟩ I O))
  ≡⟨⟩ 
    2 * (2 * (BinToℕ (⟨⟩ I)))
  ≡⟨⟩
    2 * (2 * (2 * (BinToℕ ⟨⟩) + 1))
  ≡⟨⟩
    2 * (2 * (2 * 0 + 1))
  ≡⟨⟩
    2 * (2 * (1))
  ≡⟨⟩
    4
  ∎ 


ℕToBin : ℕ → Bin
ℕToBin zero    = ⟨⟩ O
ℕToBin (suc n) = inc (ℕToBin n)

_ : ℕToBin 0 ≡ ⟨⟩ O
_ = 
  begin
    ℕToBin 0
  ≡⟨⟩
    ⟨⟩ O
  ∎

_ : ℕToBin 1 ≡ ⟨⟩ I
_ = 
  begin
    ℕToBin 1
  ≡⟨⟩
    inc (ℕToBin 0)
  ≡⟨⟩
    inc (⟨⟩ O)
  ≡⟨⟩
    ⟨⟩ I
  ∎

_ : ℕToBin 2 ≡ ⟨⟩ I O
_ =
  begin
    ℕToBin 2
  ≡⟨⟩
    inc (ℕToBin 1)
  ≡⟨⟩
    inc (inc (ℕToBin 0))
  ≡⟨⟩
    ⟨⟩ I O
  ∎

_ : ℕToBin 3 ≡ ⟨⟩ I I 
_ = 
  begin
    ℕToBin 3
  ≡⟨⟩
    inc (ℕToBin 2)
  ≡⟨⟩
    inc (inc (ℕToBin 1))
  ≡⟨⟩
    inc (inc (inc (ℕToBin 0)))
  ≡⟨⟩
    ⟨⟩ I I
  ∎

_ : ℕToBin 4 ≡ ⟨⟩ I O O
_ =
  begin
    ℕToBin 4
  ≡⟨⟩
    inc (ℕToBin 3)
  ≡⟨⟩
    inc (inc (ℕToBin 2))
  ≡⟨⟩
    inc (inc (inc (ℕToBin 1)))
  ≡⟨⟩
    inc (inc (inc (inc (ℕToBin 0))))
  ≡⟨⟩
    ⟨⟩ I O O
  ∎