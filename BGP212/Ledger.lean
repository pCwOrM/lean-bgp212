/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026), Appendix B, Table 6 "Exact analytic and combinatorial slack
ledger" (pp. 44–45).
-/


/-! # Appendix B, Table 6, as printed

Each row is transcribed with its printed `left`, `right` and `slack` columns, exactly
as fractions. The source convention (Appendix B, paragraph 2): rows are "oriented so
that the required comparison is left ≤ right, and the slack is right − left". The
decimal column is a display aid and stays out of the record. -/



namespace BGP212.Ledger

/-- One printed row of Table 6. -/
structure Row where
  condition : String
  left : Rat
  right : Rat
  slack : Rat

/-- Table 6, all 21 rows in printed order. -/
def table6 : List Row :=
  [ ⟨"Support: δ > 0", 0, 41/2500, 41/2500⟩,
    ⟨"Support: B1 > δ", 41/2500, 777/5000, 139/1000⟩,
    ⟨"Support: Bm ≤ Bm+1", 0, 17/5000, 17/5000⟩,
    ⟨"Support: Bm+1 ≤ Bm + δ", 81/5000, 82/5000, 1/5000⟩,
    ⟨"First-rung cap wall", 777/5000, 778/5000, 1/5000⟩,
    ⟨"Prime decomposition: ξ2 ≤ 2/5", 2/5, 2/5, 0⟩,
    ⟨"Prime decomposition: ξ3 ≥ ξ2", 2/5, 2/5, 0⟩,
    ⟨"Prime decomposition: 2ξ1 + 3ξ2 < 2", 49/25, 2, 1/25⟩,
    ⟨"Prime decomposition: ξ1 + 9ξ2 < 4", 199/50, 4, 1/50⟩,
    ⟨"Prime decomposition: 2ξ1 + ξ2 > 1", 1, 29/25, 4/25⟩,
    ⟨"Prime decomposition: 17ξ2 < 7", 34/5, 7, 1/5⟩,
    ⟨"Type I admissibility, first wall", 41/2500, 279999997/15000000000, 33999997/15000000000⟩,
    ⟨"Type I admissibility, second wall", 41/2500, 1309999993/35000000000, 735999993/35000000000⟩,
    ⟨"Type II admissibility, first wall", 0, 69599997/2000000000, 69599997/2000000000⟩,
    ⟨"Type II admissibility, first cap wall", 41/2500, 87999999/5000000000, 5999999/5000000000⟩,
    ⟨"Type II admissibility, second cap wall", 41/2500, 82499999/5000000000, 499999/5000000000⟩,
    ⟨"Type III admissibility", 41/2500, 127499999/5000000000, 45499999/5000000000⟩,
    ⟨"Dominant Type II wall", 3937000001/5000000000, 63/80, 499999/5000000000⟩,
    ⟨"Exact packing roots A–E", 455, 455, 0⟩,
    ⟨"Half-level transition, third bin", 11/400000000000, 109/1000000000000, 163/2000000000000⟩,
    ⟨"Half-level transition, fourth bin", 11/200000000000, 11/200000000000, 0⟩ ]

/-- Lemma 7.10: the rough-count pairs `1 ≤ m ≤ m′ ≤ 13`. -/
def packingPairs : List (Nat × Nat) :=
  (List.range' 1 13).flatMap fun m => (List.range' m (14 - m)).map fun m' => (m, m')

end BGP212.Ledger
