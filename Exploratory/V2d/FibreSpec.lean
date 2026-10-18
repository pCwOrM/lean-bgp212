/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 4.1 (p. 4), Definition 4.6 (p. 6), §9.3 dictionary (p. 40),
§9.4, Lemma 9.1, Lemma 9.2 and the display of `J_T` (p. 41), Proposition 10.2 (p. 42).
-/
import BGP212.GramEntry

/-! # V2d-Spec (exploratory): the `J_T` fibre geometry and Lemma 9.2

EXPLORATORY: this file belongs to no `lean_lib`, no Challenge/Solution pair and no Comparator
suite; check it with `lake env lean Exploratory/V2d/FibreSpec.lean`.

Four kinds of content, labelled in each docstring:

* **Definition** — the objects: `hatSupport` (`T̂`), `roughCount`, `roughMass`, `endpoint` (`U`),
  `CapStep`, `marginalJ` (Definition 4.6's marginal on a supported `F`) and `jT` (§9.4's `J_T`).
* **Statement (type-checked `Prop`, unproved)** — the obligations of V2d and its successor:
  `FibreEquiv`, `EmptyFibreCap`, `EmptyFibreNeg`, `MarginalAgrees`, `InnerIntegral`.
* **Proved theorem** — small Table 3 facts (`g_nonneg`, `tau_le_L`, `capStep_table3`,
  `C_zero_table3`, `capStep_zero_fails_table3`) and the reduction `table3_of_general`; they
  discharge the hypotheses of the statements at Table 3.
* **Remaining obligation** — every `Prop` above; `ROADMAP.md` gives the proof plan.

Geometry. Write the `N = n + 1` coordinates as `(x̂, u)` with `x̂ ∈ ℝⁿ` and `u` last
(`Fin.snoc x̂ u`). For `x̂` put `S = Σ x̂ᵢ`, `s = #{i : x̂ᵢ > g}`, `ρ₁ = Σ_{x̂ᵢ > g} x̂ᵢ`. Then

  `T̂ = {x̂ ≥ 0 : S ≤ τ, ρ₁ ≤ C(s)}`,   `U(x̂) = min (L − S) (max g (C(s+1) − ρ₁))`,

and Lemma 9.2 says the fibre `{u : (x̂, u) ∈ T̃}` is the interval `[0, U(x̂)]` for `x̂ ∈ T̂`.
Every statement is parametric in the cap function `C : ℕ → ℝ`; Table 3 is instantiated
separately (`table3_*`). -/

namespace BGP212.V2d

open BGP212.Gram MeasureTheory

/-! ## Definitions -/

/-- **Definition.** `s(x̂) = #{i : x̂ᵢ > g}`. -/
noncomputable def roughCount {n : ℕ} (g : ℝ) (x : Fin n → ℝ) : ℕ := (roughSet g x).card

/-- **Definition.** `ρ₁(x̂) = Σ_{x̂ᵢ > g} x̂ᵢ`. -/
noncomputable def roughMass {n : ℕ} (g : ℝ) (x : Fin n → ℝ) : ℝ := ∑ i ∈ roughSet g x, x i

/-- **Definition.** Lemma 9.2's outer support `T̂ = {x̂ ≥ 0 : S ≤ τ, ρ₁ ≤ C(s)}`, with marginal
cutoff `τ` (rescaled `A₁ − ε`). -/
def hatSupport (n : ℕ) (g τ : ℝ) (C : ℕ → ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ τ ∧ roughMass g x ≤ C (roughCount g x)}

/-- **Definition.** Lemma 9.2's moving endpoint `U(x̂) = min{L − S, max{g, C(s+1) − ρ₁}}`. -/
noncomputable def endpoint {n : ℕ} (g L : ℝ) (C : ℕ → ℝ) (x : Fin n → ℝ) : ℝ :=
  min (L - ∑ i, x i) (max g (C (roughCount g x + 1) - roughMass g x))

/-- **Definition.** The cap-step condition: from `m ≥ 1` rough coordinates, one more raises the cap
by at most `g` (Definition 4.1's `B_{m+1} ≤ B_m + δ`, which it imposes "whenever both sides are
defined", i.e. from `m = 1`, rescaled by 4). The step `0 → 1` is excluded: Table 3 has
`C(1) = 777/1250 > C(0) + g` (see `capStep_zero_fails_table3`), and it is not needed, because
with no rough coordinate the rough mass is `0`. -/
def CapStep (g : ℝ) (C : ℕ → ℝ) : Prop := ∀ m, 1 ≤ m → C (m + 1) ≤ C m + g

/-- **Definition.** Definition 4.6's marginal functional on a function `F` supported on `T̃`
(one band, `k = n + 1` coordinates, marginal in the last coordinate, cutoff `S ≤ τ`), multiplied
by `k` as in §9.4 (`J_T = k · J` for symmetric `F`). -/
noncomputable def marginalJ (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (F : (Fin (n + 1) → ℝ) → ℝ) : ℝ :=
  (n + 1 : ℝ) * ∫ x in {x : Fin n → ℝ | ∑ i, x i ≤ τ},
    (∫ u, (supportT (n + 1) g L C).indicator F (Fin.snoc x u)) ^ 2

/-- **Definition.** §9.4's `J_T(F) = 45 ∫_{T̂} (∫₀^{U(x̂)} F(x̂, u) du)² dx̂`, for any `n`. -/
noncomputable def jT (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (F : (Fin (n + 1) → ℝ) → ℝ) : ℝ :=
  (n + 1 : ℝ) * ∫ x in hatSupport n g τ C,
    (∫ u in (0 : ℝ)..(endpoint g L C x), F (Fin.snoc x u)) ^ 2

/-! ## Statements (type-checked, unproved obligations) -/

/-- **Statement (obligation, V2d).** Lemma 9.2, fibre equivalence: for `x̂ ∈ T̂` (and `τ ≤ L`),
`(x̂, u) ∈ T̃ ↔ 0 ≤ u ≤ U(x̂)`. No cap-step hypothesis is needed in this direction: `ρ₁ ≤ C(s)`
is part of `T̂`. -/
def FibreEquiv : Prop :=
  ∀ (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ), 0 ≤ g → τ ≤ L →
    ∀ x ∈ hatSupport n g τ C, ∀ u : ℝ,
      Fin.snoc x u ∈ supportT (n + 1) g L C ↔ 0 ≤ u ∧ u ≤ endpoint g L C x

/-- **Statement (obligation, V2d).** Empty fibre, cap side: if the rough mass of `x̂` already
exceeds its cap, no `u` completes it to a point of `T̃`. This direction needs `CapStep`: a rough
`u > g` raises the mass by more than `g` while the cap rises by at most `g`. The case `s = 0`
needs only `0 ≤ C 0` (the mass is `0`, so it cannot exceed a nonnegative cap). -/
def EmptyFibreCap : Prop :=
  ∀ (n : ℕ) (g L : ℝ) (C : ℕ → ℝ), CapStep g C → 0 ≤ C 0 →
    ∀ x : Fin n → ℝ, C (roughCount g x) < roughMass g x →
      ∀ u : ℝ, Fin.snoc x u ∉ supportT (n + 1) g L C

/-- **Statement (obligation, V2d).** Empty fibre, sign side: a negative coordinate of `x̂` leaves
the fibre empty. -/
def EmptyFibreNeg : Prop :=
  ∀ (n : ℕ) (g L : ℝ) (C : ℕ → ℝ) (x : Fin n → ℝ), (∃ i, x i < 0) →
    ∀ u : ℝ, Fin.snoc x u ∉ supportT (n + 1) g L C

/-- **Statement (obligation, V2d).** Definition 4.6's marginal of `1_{T̃} · P` is §9.4's `J_T(P)`:
the consequence of the three fibre statements (and `CapStep`, `0 ≤ g`, `τ ≤ L`) used in
Theorem 11.1's `J_T(F⋆) = J_T(P⋆)`. Stated for continuous `P`. -/
def MarginalAgrees : Prop :=
  ∀ (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ), 0 ≤ g → τ ≤ L → CapStep g C → 0 ≤ C 0 →
    ∀ P : (Fin (n + 1) → ℝ) → ℝ, Continuous P →
      marginalJ n g L τ C P = jT n g L τ C P

/-- **Statement (obligation, J_T bridge).** The inner integral of a monomial in `u` with the
weight `(M − u)^p`: the one-variable building block of `∫₀^{U} F du` for `F` in `B₂₁`
(the weight `L − S − u` with `M = L − S`). -/
def InnerIntegral : Prop :=
  ∀ (U M : ℝ) (p t : ℕ),
    ∫ u in (0 : ℝ)..U, (M - u) ^ p * u ^ t =
      ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) * M ^ (p - j) * (-1) ^ j * U ^ (t + j + 1) /
        (t + j + 1)

/-! ## Table 3 instances -/

/-- **Proved.** `g = 41/625 ≥ 0`. -/
theorem g_nonneg : (0 : ℝ) ≤ (BGP212.Params.g : ℝ) := by
  norm_num [BGP212.Params.g]

/-- **Proved.** `τ = 249/250 ≤ L = 53/50` (so `L − S ≥ L − τ = 8/125 > 0` on `T̂`). -/
theorem tau_le_L : (BGP212.Params.τ : ℝ) ≤ (BGP212.Params.L : ℝ) := by
  norm_num [BGP212.Params.τ, BGP212.Params.L]

/-- **Proved.** Table 3's caps satisfy the cap-step condition (rescaled `B_{m+1} ≤ B_m + δ`;
the tightest step is `C(3) − C(2) = 81/1250 < g = 82/1250`). -/
theorem capStep_table3 :
    CapStep (BGP212.Params.g : ℝ) (fun m => (BGP212.Params.C m : ℝ)) := by
  intro m hm
  have key : BGP212.Params.C (m + 1) ≤ BGP212.Params.C m + BGP212.Params.g := by
    rcases Nat.lt_or_ge m 10 with h10 | h10
    · interval_cases m <;> decide +kernel
    · have h1 : BGP212.Params.C (m + 1) = 4 * (1081 / 5000) := by
        simp only [BGP212.Params.C, BGP212.Params.B]
        rw [if_neg (by omega), if_neg (by omega)]
      have h2 : BGP212.Params.C m = 4 * (1081 / 5000) := by
        rcases Nat.lt_or_ge m 11 with h11 | h11
        · have : m = 10 := by omega
          subst this; decide +kernel
        · simp only [BGP212.Params.C, BGP212.Params.B]
          rw [if_neg (by omega), if_neg (by omega)]
      rw [h1, h2]
      norm_num [BGP212.Params.g]
  show ((BGP212.Params.C (m + 1) : ℚ) : ℝ) ≤ (BGP212.Params.C m : ℝ) + (BGP212.Params.g : ℝ)
  exact_mod_cast key

/-- **Proved.** The step `0 → 1` is not a cap step at Table 3: `C(1) = 777/1250 > 0 + g`. -/
theorem capStep_zero_fails_table3 :
    (BGP212.Params.C 0 : ℝ) + (BGP212.Params.g : ℝ) < (BGP212.Params.C 1 : ℝ) := by
  have : BGP212.Params.C 0 + BGP212.Params.g < BGP212.Params.C 1 := by decide +kernel
  exact_mod_cast this

/-- **Proved.** `C(0) = 0` at Table 3. -/
theorem C_zero_table3 : (0 : ℝ) ≤ (BGP212.Params.C 0 : ℝ) := by
  have : (0 : ℚ) ≤ BGP212.Params.C 0 := by decide +kernel
  exact_mod_cast this

/-- **Statement (obligation).** Lemma 9.2 at Table 3 (`g = 41/625`, `L = 53/50`, `τ = 249/250`,
`C = 4B₁,ₘ`); follows from `FibreEquiv` with `g_nonneg` and `tau_le_L`. -/
def FibreEquivTable3 : Prop :=
  ∀ x ∈ hatSupport 44 (BGP212.Params.g : ℝ) (BGP212.Params.τ : ℝ) (fun m => (BGP212.Params.C m : ℝ)),
    ∀ u : ℝ, Fin.snoc x u ∈ supportT 45 (BGP212.Params.g : ℝ) (BGP212.Params.L : ℝ)
        (fun m => (BGP212.Params.C m : ℝ)) ↔
      0 ≤ u ∧ u ≤ endpoint (BGP212.Params.g : ℝ) (BGP212.Params.L : ℝ)
        (fun m => (BGP212.Params.C m : ℝ)) x

/-- **Statement (obligation).** The Table 3 marginal identity (`J_T(1_{T̃} P) = J_T(P)` with
`k = 45`); follows from `MarginalAgrees` with the three proved facts above. -/
def MarginalAgreesTable3 : Prop :=
  ∀ P : (Fin 45 → ℝ) → ℝ, Continuous P →
    marginalJ 44 (BGP212.Params.g : ℝ) (BGP212.Params.L : ℝ) (BGP212.Params.τ : ℝ)
        (fun m => (BGP212.Params.C m : ℝ)) P =
      jT 44 (BGP212.Params.g : ℝ) (BGP212.Params.L : ℝ) (BGP212.Params.τ : ℝ)
        (fun m => (BGP212.Params.C m : ℝ)) P

/-- **Proved (reduction).** The general statements imply their Table 3 instances. -/
theorem table3_of_general (hF : FibreEquiv) (hM : MarginalAgrees) :
    FibreEquivTable3 ∧ MarginalAgreesTable3 :=
  ⟨fun x hx u => hF 44 _ _ _ _ g_nonneg tau_le_L x hx u,
   fun P hP => hM 44 _ _ _ _ g_nonneg tau_le_L capStep_table3 C_zero_table3 P hP⟩

end BGP212.V2d

#print axioms BGP212.V2d.capStep_table3
#print axioms BGP212.V2d.table3_of_general
