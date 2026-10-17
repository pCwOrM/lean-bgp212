/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 7.4, Proposition 7.8 (A)–(E), Lemma 7.10 (p. 36).
-/
import Solution.PackingB
import Solution.PackingCCheck

/-! # A3c: packing proofs

`certTableC_valid` runs the verified checker `rowC` (Solution/PackingCertC.lean) on all 43
certificate rows inside the kernel; `rowC_sound` turns each into its root. Together with A3a
(296 roots) and A3b (116 roots) this closes the ledger of Lemma 7.10. -/

namespace BGP212.Challenge

open BGP212.Params BGP212.Ledger BGP212.Packing BGP212.PackingCert

theorem certTableC_keys :
    certTableC.map (fun x => ((Cond.D : Cond), x.1, x.2.1)) = openRootsB := by
  decide +kernel

theorem certTableC_all : certTableC.all rowC = true := by
  simp only [certTableC, List.all_cons, List.all_nil, Bool.and_true,
    certRowC0_valid, certRowC1_valid, certRowC2_valid, certRowC3_valid, certRowC4_valid, certRowC5_valid, certRowC6_valid, certRowC7_valid, certRowC8_valid, certRowC9_valid, certRowC10_valid, certRowC11_valid, certRowC12_valid, certRowC13_valid, certRowC14_valid, certRowC15_valid, certRowC16_valid, certRowC17_valid, certRowC18_valid, certRowC19_valid, certRowC20_valid, certRowC21_valid, certRowC22_valid, certRowC23_valid, certRowC24_valid, certRowC25_valid, certRowC26_valid, certRowC27_valid, certRowC28_valid, certRowC29_valid, certRowC30_valid, certRowC31_valid, certRowC32_valid, certRowC33_valid, certRowC34_valid, certRowC35_valid, certRowC36_valid, certRowC37_valid, certRowC38_valid, certRowC39_valid, certRowC40_valid, certRowC41_valid, certRowC42_valid]

theorem certTableC_valid : ∀ x ∈ certTableC, rowC x = true :=
  fun x hx => List.all_eq_true.mp certTableC_all x hx

theorem lemma_7_10_a3c :
    openRootsB.length = 43 ∧ ∀ r ∈ openRootsB, Root r.1 r.2.1 r.2.2 := by
  refine ⟨by decide +kernel, fun r hr => ?_⟩
  rw [← certTableC_keys] at hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact rowC_sound x (certTableC_valid x hx)

theorem lemma_7_10_all :
    allRoots.length = 455 ∧ ∀ r ∈ allRoots, Root r.1 r.2.1 r.2.2 := by
  refine ⟨by decide +kernel, fun r hr => ?_⟩
  have hr' := root_ledger_b.2.2.2.symm.mem_iff.mp hr
  rcases List.mem_append.mp hr' with h | h
  · exact (lemma_7_10_proved.2 r h)
  · exact lemma_7_10_a3c.2 r h

theorem mem_allRoots (c : Cond) (m m' : Nat) (h1 : 1 ≤ m) (h2 : m ≤ m') (h3 : m' ≤ 13) :
    (c, m, m') ∈ allRoots := by
  simp only [allRoots, packingPairs, List.mem_flatMap, List.mem_map, List.mem_range']
  exact ⟨c, by cases c <;> simp, (m, m'), ⟨m, ⟨m - 1, by omega, by omega⟩,
    m', ⟨m' - m, by omega, by omega⟩, rfl⟩, rfl⟩

theorem lemma_7_10 :
    ∀ (c : Cond) (m m' : Nat), 1 ≤ m → m ≤ m' → m' ≤ 13 → Root c m m' :=
  fun c m m' h1 h2 h3 => lemma_7_10_all.2 (c, m, m') (mem_allRoots c m m' h1 h2 h3)

end BGP212.Challenge
