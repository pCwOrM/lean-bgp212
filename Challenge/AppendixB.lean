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

Statements only; the proofs live in `Solution/AppendixB.lean`. -/



namespace BGP212.Challenge

open BGP212.Params BGP212.Ledger

/-- §9.1 support, §9.3 dictionary and Lemma 7.10's range: the rescaled column of
Table 3 and the derived readings follow from the physical column. -/
theorem table3_rescaled :
    4 * δ = g ∧ 4 * (A1 + εs) = L ∧ 4 * (A1 - εs) = τ ∧
    A1 + εs = 53 / 200 ∧ A1 - εs = 249 / 1000 ∧
    13 * δ ≤ B 10 ∧ B 10 < 14 * δ :=
  sorry

/-- **Appendix B, Table 6, columns `left` and `right`.** Every printed entry equals its
formula in the Table 3 parameters: Definition 4.1 (rows 1–4), the first-rung wall
(row 5, right side as printed), Proposition 7.2 (rows 6–11), Proposition 7.8 (I)–(III)
with Aₙ = A₁ and ϵ = εₐ (rows 12–17; row 14 carries 15ϵ as printed, see SI-3), §9.2 (row 18), Lemma 7.10's 91 pairs × 5
conditions (row 19), and Table 2 at κ = (11/80)εₐ (rows 20–21). -/
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
        (4 * (11 / 80 * εa), 55 / 100 * εa) ] :=
  sorry

/-- **Appendix B, Table 6, column `slack` and orientation.** All 21 rows: the printed
slack is `right − left` and is nonnegative, so `left ≤ right` holds row by row, strictly
exactly where the slack is positive (the source's stated convention). -/
theorem table6_slack :
    table6.length = 21 ∧ ∀ r ∈ table6, r.left + r.slack = r.right ∧ 0 ≤ r.slack :=
  sorry

/-- **Definition 4.1** for the Table 3 caps, at every rough count m ≥ 1:
`δ < B₁,ₘ ≤ B₁,ₘ₊₁ ≤ B₁,ₘ + δ`. -/
theorem definition_4_1_caps :
    ∀ m : Nat, 1 ≤ m → δ < B m ∧ B m ≤ B (m + 1) ∧ B (m + 1) ≤ B m + δ :=
  sorry

/-- Rows 3–4 read the printed rungs m = 1, …, 10: the smallest rung step is 17/5000
(at m = 1) and the largest is 81/5000 (at m = 2). -/
theorem cap_step_extremes :
    (∀ m : Nat, m < 10 → 1 ≤ m →
      17 / 5000 ≤ B (m + 1) - B m ∧ B (m + 1) - B m ≤ 81 / 5000) ∧
    B 2 - B 1 = 17 / 5000 ∧ B 3 - B 2 = 81 / 5000 :=
  sorry

/-- Lemma 7.10: the pairs `1 ≤ m ≤ m′ ≤ 13` number 91; with conditions (A)–(E) this
gives the 455 root certificates. The certificates themselves are external to this file;
this statement fixes their count. -/
theorem packing_pairs :
    packingPairs.length = 91 ∧
    ∀ p ∈ packingPairs, 1 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 13 :=
  sorry

/-- **§9.2**: the active Type-II wall. The Table 3 point lies 10⁻⁴ inside the
zero-loss frontier 63/80, and inside the retreated frontier by 499999/5000000000. -/
theorem dominant_wall :
    ξ2 / 4 + 11 / 16 = 63 / 80 ∧
    3 * A1 + δ = 63 / 80 - 1 / 10000 ∧
    3 * A1 + δ + 2 * εa < 63 / 80 :=
  sorry

/-- **A0, SI-1 and SI-2**, recorded as exact facts.
SI-1 (§9.2, p. 40): the printed pair (513/2000, 179/10000) differs from Table 3's
(A₁, δ) and gives the same value of 3A₁ + δ.
SI-2 (Lemma 9.1, p. 41): Table 3 gives C(1) = 777/1250 and C(3) = 7/10, where the
printed proof states 31/50 and 17/25.
SI-3 (Proposition 7.8 (II), p. 31; derivation, p. 35; Table 6 row 14, p. 45): the
proposition states 19/2 − 36Aₙ − 13δ − 9ϵ ≥ 0; the printed ledger value equals the
same expression with 15ϵ, the reading that carries the −ϵ of the δ*(γ) bound (p. 34).
The two differ by 6εₐ, and the 15ϵ form, the stronger one, holds. -/
theorem source_inconsistencies :
    (3 * (513 / 2000) + 179 / 10000 : Rat) = 3 * A1 + δ ∧
    (513 / 2000 : Rat) ≠ A1 ∧ (179 / 10000 : Rat) ≠ δ ∧
    C 1 = 777 / 1250 ∧ C 1 ≠ 31 / 50 ∧
    C 3 = 7 / 10 ∧ C 3 ≠ 17 / 25 ∧
    (19 / 2 - 36 * A1 - 13 * δ - 15 * εa = 69599997 / 2000000000) ∧
    (19 / 2 - 36 * A1 - 13 * δ - 9 * εa) - (19 / 2 - 36 * A1 - 13 * δ - 15 * εa) = 6 * εa ∧
    0 ≤ 19 / 2 - 36 * A1 - 13 * δ - 15 * εa :=
  sorry

end BGP212.Challenge
