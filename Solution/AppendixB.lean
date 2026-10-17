/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026), Table 3 (p. 39), §9.2–9.3 (p. 40), Lemma 9.1 (p. 41),
Proposition 7.8, Table 2, Lemma 7.10, Appendix B Table 6 (pp. 44–45).
Specification of record: specs/A0_parameters.yaml.
-/


import BGP212.Params
import BGP212.Ledger

/-! # Appendix B and the Table 3 parameter layer

Every statement is a finite exact-rational claim closed by `decide +kernel`, except
`definition_4_1_caps`, which adds a two-line argument for the constant tail m ≥ 11. -/



namespace BGP212.Challenge

open BGP212.Params BGP212.Ledger

theorem B_tail {m : Nat} (h : 11 ≤ m) : B m = 1081 / 5000 := by
  have h0 : m ≠ 0 := by omega
  have h10 : ¬ m ≤ 10 := by omega
  simp only [B, h0, h10, ↓reduceIte]

theorem table3_rescaled :
    4 * δ = g ∧ 4 * (A1 + εs) = L ∧ 4 * (A1 - εs) = τ ∧
    A1 + εs = 53 / 200 ∧ A1 - εs = 249 / 1000 ∧
    13 * δ ≤ B 10 ∧ B 10 < 14 * δ := by
  decide +kernel

theorem table6_derivation :
    table6.map (fun r => (r.left, r.right)) =
      [ (0, δ),
        (δ, B 1),
        (0, B 2 - B 1),
        (B 3 - B 2, δ),
        (B 1, 778 / 5000),
        (ξ2, 2 / 5),
        (ξ2, ξ3),
        (2 * ξ1 + 3 * ξ2, 2),
        (ξ1 + 9 * ξ2, 4),
        (1, 2 * ξ1 + ξ2),
        (17 * ξ2, 7),
        (δ, ξ1 - 4 * A1 + 2 / 3 - 2 * εa),
        (δ, 9 / 7 - 34 / 7 * A1 - 2 * εa),
        (0, 19 / 2 - 36 * A1 - 13 * δ - 15 * εa),
        (δ, ξ2 / 10 - 32 * A1 / 10 + 8 / 10 - 2 * εa),
        (δ, ξ2 / 4 + 11 / 16 - 3 * A1 - 2 * εa),
        (δ, 11 / 8 - 7 / 2 * A1 - 9 / 8 * ξ3 - 2 * εa),
        (3 * A1 + δ + 2 * εa, ξ2 / 4 + 11 / 16),
        (5 * (packingPairs.length : Rat), 455),
        (2 * (11 / 80 * εa), 109 / 100 * εa),
        (4 * (11 / 80 * εa), 55 / 100 * εa) ] := by
  decide +kernel

theorem table6_slack :
    table6.length = 21 ∧ ∀ r ∈ table6, r.left + r.slack = r.right ∧ 0 ≤ r.slack := by
  decide +kernel

theorem definition_4_1_caps :
    ∀ m : Nat, 1 ≤ m → δ < B m ∧ B m ≤ B (m + 1) ∧ B (m + 1) ≤ B m + δ := by
  intro m hm
  by_cases h : m < 11
  · revert hm
    revert m
    decide +kernel
  · rw [B_tail (by omega), B_tail (by omega)]
    decide +kernel

theorem cap_step_extremes :
    (∀ m : Nat, m < 10 → 1 ≤ m →
      17 / 5000 ≤ B (m + 1) - B m ∧ B (m + 1) - B m ≤ 81 / 5000) ∧
    B 2 - B 1 = 17 / 5000 ∧ B 3 - B 2 = 81 / 5000 := by
  decide +kernel

theorem packing_pairs :
    packingPairs.length = 91 ∧
    ∀ p ∈ packingPairs, 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 13 := by
  decide +kernel

theorem dominant_wall :
    ξ2 / 4 + 11 / 16 = 63 / 80 ∧
    3 * A1 + δ = 63 / 80 - 1 / 10000 ∧
    3 * A1 + δ + 2 * εa < 63 / 80 := by
  decide +kernel

theorem source_inconsistencies :
    (3 * (513 / 2000) + 179 / 10000 : Rat) = 3 * A1 + δ ∧
    (513 / 2000 : Rat) ≠ A1 ∧ (179 / 10000 : Rat) ≠ δ ∧
    C 1 = 777 / 1250 ∧ C 1 ≠ 31 / 50 ∧
    C 3 = 7 / 10 ∧ C 3 ≠ 17 / 25 ∧
    (19 / 2 - 36 * A1 - 13 * δ - 15 * εa = 69599997 / 2000000000) ∧
    (19 / 2 - 36 * A1 - 13 * δ - 9 * εa) - (19 / 2 - 36 * A1 - 13 * δ - 15 * εa) = 6 * εa ∧
    0 ≤ 19 / 2 - 36 * A1 - 13 * δ - 15 * εa := by
  decide +kernel

end BGP212.Challenge
