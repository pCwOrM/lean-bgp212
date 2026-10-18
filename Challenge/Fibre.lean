/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 4.1 (p. 4), Definition 4.6 (p. 6), §9.4, Lemma 9.2 and the
display of `J_T` (p. 41).
-/
import BGP212.Fibre
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # V2d: Lemma 9.2, the `J_T` fibre theorem

Statements only; proofs live in `Solution/Fibre.lean`. Objects are defined in `BGP212/Fibre.lean`
(and V2b's `BGP212/GramEntry.lean`). Every general statement keeps the cap function `C` as a
parameter; Table 3 enters only through `BGP212.Params` in the last five statements. -/

namespace BGP212.Challenge

open BGP212.Gram BGP212.V2d MeasureTheory

/-- **Appending a coordinate**: the rough set of `(x̂, u)` is that of `x̂` plus the last coordinate exactly when `g < u`. -/
theorem roughSet_snoc {n : ℕ} (g : ℝ) (x : Fin n → ℝ) (u : ℝ) :
    roughSet g (Fin.snoc x u : Fin (n + 1) → ℝ) =
      (roughSet g x).map Fin.castSuccEmb ∪ (if g < u then {Fin.last n} else ∅) :=
  sorry

/-- The rough count after appending `u`: `s` or `s + 1`. -/
theorem roughCount_snoc {n : ℕ} (g : ℝ) (x : Fin n → ℝ) (u : ℝ) :
    roughCount g (Fin.snoc x u : Fin (n + 1) → ℝ) = roughCount g x + if g < u then 1 else 0 :=
  sorry

/-- The rough mass after appending `u`: `ρ₁` or `ρ₁ + u`. -/
theorem roughMass_snoc {n : ℕ} (g : ℝ) (x : Fin n → ℝ) (u : ℝ) :
    roughMass g (Fin.snoc x u : Fin (n + 1) → ℝ) = roughMass g x + if g < u then u else 0 :=
  sorry

/-- **Lemma 9.2**: for `x̂ ∈ T̂`, `(x̂, u) ∈ T̃ ↔ 0 ≤ u ≤ U(x̂)` (cap function `C`). -/
theorem fibre_equiv (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hτ : τ ≤ L) (x : Fin n → ℝ) (hx : x ∈ hatSupport n g τ C) (u : ℝ) :
    Fin.snoc x u ∈ supportT (n + 1) g L C ↔ 0 ≤ u ∧ u ≤ endpoint g L C x :=
  sorry

/-- **Empty fibre, sign side.** -/
theorem empty_fibre_neg (n : ℕ) (g L : ℝ) (C : ℕ → ℝ) (x : Fin n → ℝ) (hneg : ∃ i, x i < 0) (u : ℝ) :
    Fin.snoc x u ∉ supportT (n + 1) g L C :=
  sorry

/-- **Empty fibre, cap side** (cap step from `m = 1`, and `0 ≤ C 0`). -/
theorem empty_fibre_cap (n : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hstep : CapStep g C) (hC0 : 0 ≤ C 0) (x : Fin n → ℝ) (hcap : C (roughCount g x) < roughMass g x) (u : ℝ) :
    Fin.snoc x u ∉ supportT (n + 1) g L C :=
  sorry

/-- On `T̂` the fibre integral of `1_{T̃} P` is the interval integral up to `U(x̂)`. -/
theorem fibre_integral (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hτ : τ ≤ L) (P : (Fin (n + 1) → ℝ) → ℝ) (x : Fin n → ℝ) (hx : x ∈ hatSupport n g τ C) :
    ∫ u, (supportT (n + 1) g L C).indicator P (Fin.snoc x u) =
      ∫ u in (0 : ℝ)..(endpoint g L C x), P (Fin.snoc x u) :=
  sorry

/-- **The marginal identity**: Definition 4.6's marginal of `1_{T̃} P` is §9.4's `J_T(P)`. -/
theorem marginal_agrees (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hτ : τ ≤ L) (hstep : CapStep g C) (hC0 : 0 ≤ C 0) (P : (Fin (n + 1) → ℝ) → ℝ) (hP : Continuous P) :
    marginalJ n g L τ C P = jT n g L τ C P :=
  sorry

/-- **The inner `u`-integral** `∫₀^U (M − u)^p u^t du` in closed form. -/
theorem inner_integral (U M : ℝ) (p t : ℕ) :
    ∫ u in (0 : ℝ)..U, (M - u) ^ p * u ^ t =
      ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) * M ^ (p - j) * (-1) ^ j * U ^ (t + j + 1) /
        (t + j + 1) :=
  sorry

/-- Table 3: `τ = 249/250 ≤ L = 53/50`. -/
theorem tau_le_L :
    (BGP212.Params.τ : ℝ) ≤ (BGP212.Params.L : ℝ) :=
  sorry

/-- Table 3: `C(0) = 0`. -/
theorem C_zero_table3 :
    (0 : ℝ) ≤ (BGP212.Params.C 0 : ℝ) :=
  sorry

/-- Table 3's caps satisfy the cap step from `m = 1`. -/
theorem capStep_table3 :
    CapStep (BGP212.Params.g : ℝ) (fun m => (BGP212.Params.C m : ℝ)) :=
  sorry

/-- The step `0 → 1` is not a cap step at Table 3. -/
theorem capStep_zero_fails_table3 :
    (BGP212.Params.C 0 : ℝ) + (BGP212.Params.g : ℝ) < (BGP212.Params.C 1 : ℝ) :=
  sorry

/-- **Every specification `Prop` of V2d-Spec**, including the Table 3 instances. -/
theorem v2d_spec_discharged :
    FibreEquiv ∧ EmptyFibreCap ∧ EmptyFibreNeg ∧ MarginalAgrees ∧ InnerIntegral ∧
      FibreEquivTable3 ∧ MarginalAgreesTable3 :=
  sorry

end BGP212.Challenge
