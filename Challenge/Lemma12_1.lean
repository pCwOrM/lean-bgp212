/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026), Lemma 12.1 (§12).
-/
module

public import BGP212.Basic

/-! # Lemma 12.1: `H₄₅` is an admissible 45-tuple of diameter 212

Source statement: "The set H₄₅ is an admissible 45-tuple of diameter 212."
The four component statements follow the source proof clause by clause:
45 distinct elements; minimum 0 and maximum 212; the listed omitted classes for
p ≤ 43; admissibility for every prime. The fifth packages the lemma. -/

@[expose] public section

namespace BGP212.Challenge

open BGP212

/-- Source proof, sentence 1: "The displayed list has 45 distinct elements". -/
theorem h45_card : H45.length = 45 ∧ H45.Nodup :=
  sorry

/-- Source proof, sentence 1: "… with minimum 0 and maximum 212". -/
theorem h45_diameter : 0 ∈ H45 ∧ 212 ∈ H45 ∧ ∀ h ∈ H45, h ≤ 212 :=
  sorry

/-- Source proof, sentences 2–3: for each listed prime `p ≤ 43`, the reductions of
`H₄₅` omit the listed class. -/
theorem h45_omitted_table :
    omittedTable.map Prod.fst = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43] ∧
    ∀ q ∈ omittedTable, q.2 < q.1 ∧ ∀ h ∈ H45, h % q.1 ≠ q.2 :=
  sorry

/-- Source definition (§2) applied to `H₄₅`: it omits a class modulo every prime. -/
theorem h45_admissible : Admissible H45 :=
  sorry

/-- **Lemma 12.1.** `H₄₅` is an admissible 45-tuple of diameter 212. -/
theorem lemma_12_1 :
    (H45.length = 45 ∧ H45.Nodup) ∧
    (0 ∈ H45 ∧ 212 ∈ H45 ∧ ∀ h ∈ H45, h ≤ 212) ∧
    Admissible H45 :=
  sorry

end BGP212.Challenge
