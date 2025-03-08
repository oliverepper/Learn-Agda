module learn.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _^_)

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p = refl
+-assoc (suc m) n p rewrite +-assoc m n p = refl

+-identityʳ : ∀ (n : ℕ) → n + zero ≡ n
+-identityʳ zero = refl
+-identityʳ (suc n) rewrite +-identityʳ n = refl

+-lemma : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-lemma zero n = refl
+-lemma (suc m) n rewrite +-lemma m n = refl

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n rewrite +-identityʳ n = refl
+-comm (suc m) n rewrite +-lemma n m | +-comm m n = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | +-assoc p (m * p) (n * p) = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl

*-zero : ∀ (m : ℕ) → m * zero ≡ zero
*-zero zero = refl
*-zero (suc m) rewrite *-zero m = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p rewrite sym (+-assoc m n p)
  | +-comm m n
  | +-assoc n m p = refl

*-lemma : ∀ (m n : ℕ) → m * suc n ≡ m + m * n
*-lemma zero n rewrite *-zero n = refl
*-lemma (suc m) n rewrite *-lemma m n | +-swap n m (m * n) = refl

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-zero n = refl
*-comm (suc m) n rewrite *-lemma n m | *-comm m n = refl

0∸n≡0 : ∀ (n : ℕ) → 0 ∸ n ≡ 0
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc m zero p = refl
∸-+-assoc zero (suc n) p rewrite 0∸n≡0 p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

^-distribˡ-+-* : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
^-distribˡ-+-* m zero p rewrite +-identityʳ (m ^ p) = refl
^-distribˡ-+-* m (suc n) p rewrite ^-distribˡ-+-* m n p | *-assoc m (m ^ n) (m ^ p) = refl

*-swap : ∀ (m n p : ℕ) → m * (n * p) ≡ n * (m * p)
*-swap m n p rewrite sym (*-assoc m n p)
  | *-comm m n
  | *-assoc n m p = refl

^-distribʳ-* : ∀ (m n p : ℕ) → (m * n) ^ p ≡ m ^ p * n ^ p
^-distribʳ-* m n zero = refl
^-distribʳ-* m n (suc p) rewrite ^-distribʳ-* m n p
  | *-assoc m n (m ^ p * n ^ p)
  | *-swap n (m ^ p) (n ^ p)
  | *-assoc m (m ^ p) (n * n ^ p) = refl

^-*-assoc : ∀ (m n p : ℕ) → (m ^ n) ^ p ≡ m ^ (n * p)
^-*-assoc m n zero rewrite *-zero n = refl
^-*-assoc m n (suc p) rewrite ^-*-assoc m n p
  | sym (^-distribˡ-+-* m n (n * p))
  | *-lemma n p = refl

-- Bin
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to : ℕ → Bin
to zero = ⟨⟩
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = zero
from (b O) = 2 * from b
from (b I) = 2 * from b + 1

-- Bin proofs
bin-lemma : ∀ (n : ℕ) → n + 1 ≡ suc n
bin-lemma zero = refl
bin-lemma (suc n) rewrite bin-lemma n = refl

from-inc : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from-inc ⟨⟩ = refl
from-inc (b O) rewrite +-identityʳ (from b)
  | bin-lemma (from b + from b) = refl
from-inc (b I) rewrite +-identityʳ (from b)
  | +-identityʳ (from (inc b))
  | bin-lemma (from b + from b)
  | from-inc b
  | +-comm (from b) (suc (from b))
  = refl

from-to : ∀ (n : ℕ) → from (to n) ≡ n
from-to zero = refl
from-to (suc n) rewrite from-inc (to n) | from-to n = refl
