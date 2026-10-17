/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026), Lemma 12.1 (§12).
-/
module

public import BGP212.Basic

/-! # Lemma 12.1: solution

Every finite claim is closed by `decide +kernel`, so the Lean kernel itself evaluates
it. The one infinite claim (admissibility for every prime) splits at 213:
primes below 213 form a finite check, and every larger prime exceeds every element
of `H₄₅`, so the class `1` is omitted there because `1 ∉ H₄₅`. -/

@[expose] public section

namespace BGP212.Challenge

open BGP212

theorem h45_card : H45.length = 45 ∧ H45.Nodup := by
  decide +kernel

theorem h45_diameter : 0 ∈ H45 ∧ 212 ∈ H45 ∧ ∀ h ∈ H45, h ≤ 212 := by
  decide +kernel

theorem h45_omitted_table :
    omittedTable.map Prod.fst = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43] ∧
    ∀ q ∈ omittedTable, q.2 < q.1 ∧ ∀ h ∈ H45, h % q.1 ≠ q.2 := by
  decide +kernel

/-- Finite part: every modulus `2 ≤ p < 213` (prime or composite) has an omitted class. -/
theorem h45_omits_below_213 :
    ∀ p, p < 213 → 2 ≤ p → ∃ r, r < p ∧ ∀ h ∈ H45, h % p ≠ r := by
  decide +kernel

/-- Infinite part: for `p ≥ 213`, reduction mod `p` fixes every element, and `1 ∉ H₄₅`. -/
theorem h45_omits_from_213 (p : Nat) (hp : 213 ≤ p) :
    ∃ r, r < p ∧ ∀ h ∈ H45, h % p ≠ r := by
  refine ⟨1, by omega, fun h hh => ?_⟩
  have hle : h ≤ 212 := h45_diameter.2.2 h hh
  have hne : h ≠ 1 := by
    intro h1
    subst h1
    exact absurd hh (by decide +kernel)
  rw [Nat.mod_eq_of_lt (by omega)]
  exact hne

theorem h45_admissible : Admissible H45 := by
  intro p hp
  by_cases hlt : p < 213
  · exact h45_omits_below_213 p hlt hp.1
  · exact h45_omits_from_213 p (by omega)

theorem lemma_12_1 :
    (H45.length = 45 ∧ H45.Nodup) ∧
    (0 ∈ H45 ∧ 212 ∈ H45 ∧ ∀ h ∈ H45, h ≤ 212) ∧
    Admissible H45 :=
  ⟨h45_card, h45_diameter, h45_admissible⟩

end BGP212.Challenge
