/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 7.4, Proposition 7.8 (A)–(E), Lemma 7.10 (p. 36).
-/
import BGP212.PackingLedgerB

/-! # A3b: packing statements

Statements only; proofs live in `Solution/PackingB.lean`. -/

namespace BGP212.Challenge

open BGP212.Params BGP212.Ledger BGP212.Packing

/-- **Packing is invariant under permuting the coordinates.** -/
theorem packs_perm {caps items items' : List Rat} (hp : items.Perm items')
    (h : Packs caps items) : Packs caps items' :=
  sorry

/-- **The A3b ledger.** A3a's 296 settled roots, A3b's 116, and the 43 still open are
together exactly the 455 roots of Lemma 7.10; A3b's settled and open roots are exactly A3a's
open roots. -/
theorem root_ledger_b :
    settledRootsB.length = 116 ∧ openRootsB.length = 43 ∧
    (settledRootsB ++ openRootsB).Perm openRoots ∧
    (settledRoots ++ settledRootsB ++ openRootsB).Perm allRoots :=
  sorry

/-- **Lemma 7.10, A3b roots.** Each of the 116 roots holds for every profile in its domain
`Ξ(B₁,ₘ, B₁,ₘ′, m, m′, δ)`; each (D) root uniformly over its full `(γ, ω₀)` box. -/
theorem lemma_7_10_a3b :
    ∀ r ∈ settledRootsB, Root r.1 r.2.1 r.2.2 :=
  sorry

/-- **Lemma 7.10, everything proved so far: 412 of the 455 roots.** -/
theorem lemma_7_10_proved :
    (settledRoots ++ settledRootsB).length = 412 ∧
    ∀ r ∈ settledRoots ++ settledRootsB, Root r.1 r.2.1 r.2.2 :=
  sorry

end BGP212.Challenge
