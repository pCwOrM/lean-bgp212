/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Charton, Hong, Lau, Ono, Remy, Siu, Swaminathan, Thorner, Xie,
"A New Bound for Small Gaps Between Primes", Axiom Math, preliminary draft
(September 3, 2026), §2 (admissibility), §12 (the tuple H₄₅, Lemma 12.1).
-/
module

/-! # Basic definitions for the BGP212 specification layer

Core-Lean definitions only. Each definition transcribes the source wording:

* §2: "A finite set H = {h₁, …, h_k} of distinct integers is called *admissible* if,
  for every prime p, the elements of H omit at least one residue class modulo p."
* §12: the displayed 45-tuple `H₄₅`.
* Lemma 12.1 proof: the omitted residue classes listed for the primes 2, 3, …, 43.

`IsPrime` is the textbook definition, stated in core Lean so the first challenge
carries a minimal trusted base. Elements of `H₄₅` are nonnegative, so `ℕ` carries
them faithfully. -/

@[expose] public section

namespace BGP212

/-- A natural number `p` is prime: `2 ≤ p` and its only divisors are `1` and `p`. -/
def IsPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- §2: `H` omits at least one residue class modulo every prime `p`. -/
def Admissible (H : List Nat) : Prop :=
  ∀ p : Nat, IsPrime p → ∃ r : Nat, r < p ∧ ∀ h ∈ H, h % p ≠ r

/-- §12: the admissible 45-tuple of diameter 212, transcribed in the displayed order. -/
def H45 : List Nat :=
  [0, 2, 12, 14, 24, 26, 30, 36, 44, 50, 54, 56, 60, 66, 72, 74, 80, 84, 92, 96, 102,
   110, 114, 116, 122, 126, 134, 140, 144, 150, 156, 162, 164, 170, 176, 180, 182, 186,
   192, 194, 200, 204, 206, 210, 212]

/-- Lemma 12.1 proof: pairs `(p, r)` where `H₄₅` omits the class `r` mod `p`,
transcribed from the source lists "2, 3, 5, …, 43" and "1, 1, 3, …, 3". -/
def omittedTable : List (Nat × Nat) :=
  [(2, 1), (3, 1), (5, 3), (7, 6), (11, 9), (13, 3), (17, 1), (19, 13), (23, 17),
   (29, 4), (31, 11), (37, 4), (41, 4), (43, 3)]

end BGP212
