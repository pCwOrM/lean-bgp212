/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 7.4, Proposition 7.8 (A)–(E), Lemma 7.10 (p. 36).
-/
import BGP212.PackingLedgerB
import Solution.PackingBCheck

/-! # A3b: packing proofs

`certTableB_valid` runs the verified checker `rowB` on all 116 certificate rows inside the
kernel; `rowB_sound` (Solution/PackingCert.lean) turns each into its root. -/

namespace BGP212.Challenge

open BGP212.Params BGP212.Ledger BGP212.Packing BGP212.PackingCert

theorem root_ledger_b :
    settledRootsB.length = 116 ∧ openRootsB.length = 43 ∧
    (settledRootsB ++ openRootsB).Perm openRoots ∧
    (settledRoots ++ settledRootsB ++ openRootsB).Perm allRoots := by
  decide +kernel

theorem certTableB_keys : certTableB.map (fun x => (x.1, x.2.1, x.2.2.1)) = settledRootsB := by
  decide +kernel

theorem certTableB_all : certTableB.all rowB = true := by
  simp only [certTableB, List.all_cons, List.all_nil, Bool.and_true,
    certRow0_valid, certRow1_valid, certRow2_valid, certRow3_valid, certRow4_valid, certRow5_valid, certRow6_valid, certRow7_valid, certRow8_valid, certRow9_valid, certRow10_valid, certRow11_valid, certRow12_valid, certRow13_valid, certRow14_valid, certRow15_valid, certRow16_valid, certRow17_valid, certRow18_valid, certRow19_valid, certRow20_valid, certRow21_valid, certRow22_valid, certRow23_valid, certRow24_valid, certRow25_valid, certRow26_valid, certRow27_valid, certRow28_valid, certRow29_valid, certRow30_valid, certRow31_valid, certRow32_valid, certRow33_valid, certRow34_valid, certRow35_valid, certRow36_valid, certRow37_valid, certRow38_valid, certRow39_valid, certRow40_valid, certRow41_valid, certRow42_valid, certRow43_valid, certRow44_valid, certRow45_valid, certRow46_valid, certRow47_valid, certRow48_valid, certRow49_valid, certRow50_valid, certRow51_valid, certRow52_valid, certRow53_valid, certRow54_valid, certRow55_valid, certRow56_valid, certRow57_valid, certRow58_valid, certRow59_valid, certRow60_valid, certRow61_valid, certRow62_valid, certRow63_valid, certRow64_valid, certRow65_valid, certRow66_valid, certRow67_valid, certRow68_valid, certRow69_valid, certRow70_valid, certRow71_valid, certRow72_valid, certRow73_valid, certRow74_valid, certRow75_valid, certRow76_valid, certRow77_valid, certRow78_valid, certRow79_valid, certRow80_valid, certRow81_valid, certRow82_valid, certRow83_valid, certRow84_valid, certRow85_valid, certRow86_valid, certRow87_valid, certRow88_valid, certRow89_valid, certRow90_valid, certRow91_valid, certRow92_valid, certRow93_valid, certRow94_valid, certRow95_valid, certRow96_valid, certRow97_valid, certRow98_valid, certRow99_valid, certRow100_valid, certRow101_valid, certRow102_valid, certRow103_valid, certRow104_valid, certRow105_valid, certRow106_valid, certRow107_valid, certRow108_valid, certRow109_valid, certRow110_valid, certRow111_valid, certRow112_valid, certRow113_valid, certRow114_valid, certRow115_valid]

theorem certTableB_valid : ∀ x ∈ certTableB, rowB x = true :=
  fun x hx => List.all_eq_true.mp certTableB_all x hx

theorem lemma_7_10_a3b :
    ∀ r ∈ settledRootsB, Root r.1 r.2.1 r.2.2 := by
  intro r hr
  rw [← certTableB_keys] at hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  exact rowB_sound x (certTableB_valid x hx)

theorem lemma_7_10_proved :
    (settledRoots ++ settledRootsB).length = 412 ∧
    ∀ r ∈ settledRoots ++ settledRootsB, Root r.1 r.2.1 r.2.2 := by
  refine ⟨by decide +kernel, fun r hr => ?_⟩
  rcases List.mem_append.mp hr with h | h
  · exact lemma_7_10_settled r h
  · exact lemma_7_10_a3b r h

end BGP212.Challenge
