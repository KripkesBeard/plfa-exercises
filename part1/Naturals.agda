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




{- Exercise `*-example` -}
-- Compute `3 * 4`, writing out your reasoning as a chain of equations, using the equations for `*`.
-- (You do not need to step through the evaluation of `+`.)



{- Exercise `_^_` -}
-- Define exponentiation, which is given by the following equations:
--
--     m ^ 0        =  1
--     m ^ (1 + n)  =  m * (m ^ n)
-- Check that `3 ^ 4` is `81`.




{- Exercise `∸-example₁` and `∸-example₂` -}
-- Compute `5 ∸ 3` and `3 ∸ 5`, writing out your reasoning as a chain of equations.





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

