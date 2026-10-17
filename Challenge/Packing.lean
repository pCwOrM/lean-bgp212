/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 7.4, Proposition 7.8 (A)–(E), Lemma 7.10 (p. 36).
-/
import BGP212.Packing

/-! # A3a: packing statements

Statements only; proofs live in `Solution/Packing.lean`. -/

namespace BGP212.Challenge

open BGP212.Params BGP212.Ledger BGP212.Packing

/-- **Greedy packing.** Items each at most `s`, bins of nonnegative capacity, and a nonempty
set `sel` of distinct bins whose capacities exceed the total by the greedy loss
`(|sel| − 1)·s`: then the items pack. -/
theorem greedy_pack (caps items : List Rat) (s : Rat) (sel : List Nat)
    (hsel : sel ≠ []) (hnd : sel.Nodup) (hin : ∀ i ∈ sel, i < caps.length)
    (hcap : ∀ k, k < caps.length → 0 ≤ caps[k]!) (hs : ∀ y ∈ items, y ≤ s)
    (hT : items.sum ≤ (sel.map fun i => caps[i]!).sum - ((sel.length : Rat) - 1) * s) :
    Packs caps items :=
  sorry

/-- **The largest coordinate on a side.** With every coordinate at least `δ` and side sum at
most `Bc`, each coordinate is at most `Bc − (k − 1)δ`, `k` the number of coordinates
(Lemma 4.2's argument for a single coordinate). -/
theorem largest_coordinate (δ' Bc : Rat) (ys : List Rat) (hδ : ∀ y ∈ ys, δ' ≤ y)
    (hsum : ys.sum ≤ Bc) :
    ∀ y ∈ ys, y ≤ Bc - ((ys.length : Rat) - 1) * δ' :=
  sorry

/-- `ω(1,1)` of Proposition 7.8 equals Table 3's `ω`. -/
theorem omega_matches_table3 : ω11 = ω :=
  sorry

/-- **The A3a root ledger.** 296 settled and 159 open roots, together exactly the 455
roots of Lemma 7.10. -/
theorem root_ledger :
    settledRoots.length = 296 ∧ openRoots.length = 159 ∧
    (settledRoots ++ openRoots).Perm allRoots ∧ allRoots.length = 455 :=
  sorry

/-- **Lemma 7.10, settled roots.** Each of the 296 settled roots holds for every profile in
its domain `Ξ(B₁,ₘ, B₁,ₘ′, m, m′, δ)`; the settled (D) root uniformly over its full
`(γ, ω₀)` box. -/
theorem lemma_7_10_settled :
    ∀ r ∈ settledRoots, Root r.1 r.2.1 r.2.2 :=
  sorry

end BGP212.Challenge
