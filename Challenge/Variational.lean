/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): (10.1) and §11 (the space B₂₁).
-/
import BGP212.Variational
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Combinatorics.Enumerative.Composition

/-! # V0: the variational space `B₂₁` has dimension 846

Statements only; proofs live in `Solution/Variational.lean`. Objects are defined in
`BGP212/Variational.lean`. -/

namespace BGP212.Challenge

open BGP212.Var

/-- The enumeration `partsLE j k` lists exactly the partitions of `j` into parts at most `k`. -/
theorem mem_partsLE (k j : ℕ) (s : Multiset ℕ) :
    s ∈ partsLE j k ↔ (∀ x ∈ s, 0 < x ∧ x ≤ k) ∧ s.sum = j :=
  sorry

/-- The enumeration has no duplicates. -/
theorem nodup_partsLE (k j : ℕ) : (partsLE j k).Nodup :=
  sorry

/-- `p(j)`, the number of partitions of `j` (`Nat.Partition`), equals the enumeration's length. -/
theorem p_eq_enumeration (j : ℕ) : p j = (partsLE j j).length :=
  sorry

/-- `p(0), …, p(10) = 1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42`. -/
theorem partition_counts :
    (List.range 11).map p = [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42] :=
  sorry

/-- **`Σ_{j ≤ 10} p(j)(22 − 2j) = 846`.** -/
theorem dimension_identity : ∑ j ∈ Finset.range 11, p j * (22 - 2 * j) = 846 :=
  sorry

/-- The explicit index type has 846 elements. -/
theorem card_B21Idx : Fintype.card B21Idx = 846 :=
  sorry

/-- Reading `λ` as an ordered tuple of positive even parts gives 4094 index pairs. -/
theorem ordered_family_count :
    ∑ j ∈ Finset.range 11, Fintype.card (Composition j) * (22 - 2 * j) = 4094 :=
  sorry

/-- **No duplicates**: distinct indices give distinct printed pairs `(a, λ)`. -/
theorem toPair_injective : Function.Injective B21Idx.toPair :=
  sorry

/-- **Coverage**: the indices realize exactly the printed pairs `(a, λ)`. -/
theorem toPair_range (a : ℕ) (lam : Multiset ℕ) :
    (∃ i : B21Idx, i.toPair = (a, lam)) ↔ IsB21Index a lam :=
  sorry

/-- `B₂₁` is the span of the indexed family. -/
theorem B21_eq_span : B21 = Submodule.span ℚ (Set.range genIdx) :=
  sorry

/-- **`P₁, …, P₄₅` are algebraically independent over `ℚ`** in 45 variables. -/
theorem power_sums_algebraically_independent :
    Function.Injective (MvPolynomial.aeval (R := ℚ) fun k : Fin 45 => P (k + 1)) :=
  sorry

/-- **The 846 spanning elements are linearly independent.** -/
theorem genIdx_linearIndependent : LinearIndependent ℚ genIdx :=
  sorry

/-- **`dim_ℚ B₂₁ = 846`** (§11). -/
theorem finrank_B21 : Module.finrank ℚ B21 = 846 :=
  sorry

/-- (10.1) with `m = 0`. -/
theorem simplexMoment_nil (R : ℚ) : simplexMoment R [] = 1 :=
  sorry

/-- (10.1) with `m = 1`: `R^{e+1}/(e+1)`. -/
theorem simplexMoment_single (R : ℚ) (e : ℕ) : simplexMoment R [e] = R ^ (e + 1) / (e + 1) :=
  sorry

/-- The Fubini step of (10.1): one more coordinate multiplies by a Beta moment. -/
theorem simplexMoment_snoc (R : ℚ) (e : List ℕ) (u : ℕ) :
    simplexMoment R (e ++ [u]) =
      ((e.map Nat.factorial).prod : ℚ) / ((e.length + e.sum).factorial : ℚ) *
        betaMoment R u (e.length + e.sum) :=
  sorry

end BGP212.Challenge
