/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 4.1, Lemmas 5.3–5.7, Definitions 7.1 and 7.4,
Lemmas 7.5–7.7, Proposition 7.8 and its proof, Lemma 7.10, Theorem 7.11, Table 3.
-/
import BGP212.Theorem711

/-! # A4: from Lemma 7.10 to Theorem 7.11

Statements only; proofs live in `Solution/Theorem711.lean`. Objects are defined in
`BGP212/Theorem711.lean`. -/

namespace BGP212.Challenge

open BGP212.Params BGP212.Packing BGP212.T711

/-! ## Parameter bounds at Table 3 -/

/-- **Definition 4.1 at Table 3**: `n = 1`, `−εₛ = A₀ < A₁ < 1/2 − εₛ`, and
`δ < B₁,ₘ ≤ B₁,ₘ₊₁ ≤ B₁,ₘ + δ` for `1 ≤ m < ⌊1/δ⌋ = 60`. -/
theorem definition_4_1_table3 : SupportDatum 1 A3 B3 δ εs ∧ floorInv δ = 60 :=
  sorry

/-- `ω(1, 1) = A₁ − 1/4 = ω` (Table 3). -/
theorem omega_11_table3 : omegaJJ A3 1 1 = ω11 ∧ ω11 = ω :=
  sorry

/-- **Proposition 7.8 (I)–(III) at Table 3.** -/
theorem prop_7_8_I_III_table3 : Prop78Scalar 1 A3 δ ξ1 ξ2 ξ3 εa :=
  sorry

/-! ## The case split: Lemma 7.10 → Proposition 7.8 (A)–(E) -/

/-- **The case split.** For all `m, m′ ≥ 0`, every tuple of `Ξ(B₁,ₘ, B₁,ₘ′, m, m′, δ)`
satisfies (A)–(E). -/
theorem lemma_7_10_case_split :
    ∀ m m' ys, Xi (B m) (B m') m m' δ ys → CondsAE ξ1 ξ2 ξ3 ω11 δ εa ys :=
  sorry

/-- **Proposition 7.8 (A)–(E) at Table 3**, quantified as printed: all `j, j′ ∈ {1}`,
all `m, m′ ∈ {0, …, ⌊1/δ⌋}` with `m + m′ > 0`. -/
theorem prop_7_8_A_E_table3 : Prop78Packing 1 A3 B3 δ ξ1 ξ2 ξ3 εa :=
  sorry

/-! ## Ranges and permissible triples of the proof of Proposition 7.8 -/

/-- The Type II range `[ξ₂ − ϵ, 1/2]` is the union of the IIc, IIb and IIa ranges. -/
theorem type_II_cover :
    ξ2 - εa < gIIc ω11 δ εa ∧ gIIc ω11 δ εa < gIIa ω11 δ εa ∧ gIIa ω11 δ εa < 1 / 2 ∧
    ∀ γ, ξ2 - εa ≤ γ → γ ≤ 1 / 2 →
      γ ≤ gIIc ω11 δ εa ∨ (gIIc ω11 δ εa < γ ∧ γ < gIIa ω11 δ εa) ∨ gIIa ω11 δ εa ≤ γ :=
  sorry

/-- Lemma 5.3 (Type I, `γ ≤ 1/2`) at `δ*(γ) = γ − 4ω − 1/3 − ϵ`, margin `εₐ`; `δ ≤ δ*(γ)`. -/
theorem perm_type_I_low (γ ε : Rat) (h1 : ξ1 - εa ≤ γ) (h2 : γ ≤ 1 / 2) :
    PermI εa ω11 γ (dIlow ω11 γ εa) ε ∧ δ ≤ dIlow ω11 γ εa :=
  sorry

/-- Lemma 5.3 (Type I, `γ ∈ (1/2, 1/2 + 2ω + ε]`) at `δ* = 1/14 − 68ω/14 − ϵ`. -/
theorem perm_type_I_high (γ ε : Rat) (h1 : 1 / 2 < γ) (_h2 : γ ≤ 1 / 2 + 2 * ω11 + ε) :
    PermI εa ω11 γ (dIhigh ω11 εa) ε ∧ δ ≤ dIhigh ω11 εa :=
  sorry

/-- Lemma 5.4 (Type IIa) at `δ*(γ) = 5γ/7 − 2/7 − 24ω/7 − ϵ`. -/
theorem perm_type_IIa (γ : Rat) (h1 : gIIa ω11 δ εa ≤ γ) (h2 : γ ≤ 1 / 2) :
    PermIIa εa ω11 γ (dIIa ω11 γ εa) ∧ δ ≤ dIIa ω11 γ εa :=
  sorry

/-- Lemma 5.5 (Type IIb) at `δ*(γ) = 3γ/7 − 1/7 − 24ω/7 − ϵ`. -/
theorem perm_type_IIb (γ : Rat) (h1 : gIIc ω11 δ εa < γ) (h2 : γ < gIIa ω11 δ εa) :
    PermIIb εa ω11 γ (dIIb ω11 γ εa) ∧ δ ≤ dIIb ω11 γ εa :=
  sorry

/-- Lemma 5.6 (Type IIc) at `δ*(γ) = δ`, which lies in the printed admissible interval. -/
theorem perm_type_IIc (γ : Rat) (h1 : ξ2 - εa ≤ γ) (h2 : γ ≤ gIIc ω11 δ εa) :
    PermIIc εa ω11 γ δ ∧
    δ ≤ 1 / 4 - 2 * ω11 - γ / 2 ∧ δ ≤ γ / 10 - 32 * ω11 / 10 ∧
    δ ≤ γ / 4 - 1 / 16 - 3 * ω11 - εa :=
  sorry

/-- Lemma 5.7 (Type III) at `γ = ξ₃ + ϵ`, `δ* = dIII`; `δ < δ*`. -/
theorem perm_type_III : PermIII εa ω11 (ξ3 + εa) (dIII ω11 ξ3 εa) ∧ δ < dIII ω11 ξ3 εa :=
  sorry

/-! ## Findings -/

/-- **Type III width.** The printed `δ*` is permissible at `γ = ξ₃` and fails at
`γ = ξ₃ + ϵ`, the least `γ` covering Definition 7.1 (III); the excess is exactly `ϵ`. -/
theorem type_III_printed_gap :
    PermIII 0 ω11 ξ3 (dIIIprinted ω11 ξ3 εa) ∧
    ¬ PermIII 0 ω11 (ξ3 + εa) (dIIIprinted ω11 ξ3 εa) ∧
    28 * ω11 + 9 * (ξ3 + εa) + 8 * dIIIprinted ω11 ξ3 εa = 4 + εa :=
  sorry

/-- **Type I above 1/2.** With `δ* = δ` the second part's bound `1/2 − a` falls below (7.6)'s
capacity just above `γ = 1/2`; with `δ*` at the top of the printed interval it does not. -/
theorem type_I_high_choice :
    (1 / 2 + 1 / 1000) - 1 / 2 + δ + 3 * (εa / 3) < 1 / 14 - 68 / 14 * ω11 - 2 * εa ∧
    1 / 14 - 68 / 14 * ω11 - 2 * εa ≤ (1 / 2 + 1 / 1000) - 1 / 2 + dIhigh ω11 εa + 3 * (εa / 3) :=
  sorry

/-- **Type IIc reduction.** In the four-bin criterion, the first capacity decreases and the
third increases with the width `δ*`; replacing `δ*(γ)` by `δ` is therefore a choice
(`δ*(γ) = δ`, inside the printed admissible interval by `perm_type_IIc`), the form used
here, and the printed justification "a smaller `δ` makes these conditions easier" covers
the first bin only. -/
theorem type_IIc_mixed_monotonicity (γ ω0 d d' ϵ : Rat) (h : d ≤ d') :
    (capsDG γ ω0 d' ϵ)[0]! ≤ (capsDG γ ω0 d ϵ)[0]! ∧
    (capsDG γ ω0 d ϵ)[2]! ≤ (capsDG γ ω0 d' ϵ)[2]! :=
  sorry

/-- **Lemma 4.2's one-step hypothesis at `q = 0`.** Definition 4.1 imposes
`B_{j,m+1} ≤ B_{j,m} + δ` only where both sides are defined (`m ≥ 1`); with `B_{1,0} = 0`
the step from `0` fails at Table 3, so Lemma 4.2's iteration applies from `r ≥ 1` (the case
`I′ = ∅` is immediate). -/
theorem lemma_4_2_step_at_zero : ¬ (B 1 ≤ B 0 + δ) ∧ ∀ q : Nat, 1 ≤ q → B (q + 1) ≤ B q + δ :=
  sorry

/-! ## The containments `Q ⊆ D_X`: (A)–(E) composed with Lemmas 7.5–7.7 -/

theorem containment_I_low : ContainIlow := sorry
theorem containment_I_high : ContainIhigh := sorry
theorem containment_IIa : ContainIIa := sorry
theorem containment_IIb : ContainIIb := sorry
theorem containment_IIc : ContainIIc := sorry
theorem containment_III : ContainIII := sorry

/-! ## Theorem 7.11 -/

/-- **Theorem 7.11, combinatorial core at Table 3**: every combinatorial hypothesis its
proof uses. -/
theorem theorem_7_11_core :
    SupportDatum 1 A3 B3 δ εs ∧ Prop78Scalar 1 A3 δ ξ1 ξ2 ξ3 εa ∧
    Prop78Packing 1 A3 B3 δ ξ1 ξ2 ξ3 εa ∧
    ContainIlow ∧ ContainIhigh ∧ ContainIIa ∧ ContainIIb ∧ ContainIIc ∧ ContainIII :=
  sorry

/-- **Theorem 7.11, relative to its named analytic inputs** (Lemmas 5.3–5.7, the assembly
step of Proposition 7.8, Theorem 8.3). -/
theorem theorem_7_11 (H : AnalyticInputs) : H.PositiveLevel ∧ H.HalfLevel :=
  sorry

end BGP212.Challenge
