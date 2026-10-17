/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): (10.1) and Lemma 10.1 (pp. 41–42).
-/
import BGP212.SimplexMoment
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # V1: the simplex moment identity (10.1) as an integral

Statements only; proofs live in `Solution/SimplexMoment.lean`. Objects are defined in
`BGP212/SimplexMoment.lean`. V0's `simplexMoment` and `betaMoment` are the rational right-hand
sides; the theorems here are the integral identities they evaluate. -/

namespace BGP212.Challenge

open BGP212.Var MeasureTheory

/-- The simplex is compact (closed and inside `[0, |R|]^m`). -/
theorem simplex_isCompact (m : ℕ) (R : ℝ) : IsCompact (simplex m R) :=
  sorry

/-- For `R < 0` the simplex is empty. -/
theorem simplex_empty (m : ℕ) (R : ℝ) (hR : R < 0) : simplex m R = ∅ :=
  sorry

/-- The Fubini slice: `(x, w) ∈ simplex (m+1) R ↔ x ≥ 0 ∧ w ∈ simplex m (R − x)`. -/
theorem cons_mem_simplex (m : ℕ) (R x : ℝ) (w : Fin m → ℝ) :
    (Fin.cons x w : Fin (m + 1) → ℝ) ∈ simplex (m + 1) R ↔ 0 ≤ x ∧ w ∈ simplex m (R - x) :=
  sorry

/-- **The Beta moment**: `∫₀^R z^u (R − z)^v dz = R^{u+v+1} u! v! / (u+v+1)!` for every real `R`. -/
theorem beta_integral (R : ℝ) (v u : ℕ) :
    ∫ x in (0 : ℝ)..R, x ^ u * (R - x) ^ v = betaR R u v :=
  sorry

/-- **(10.1)**: `∫_{z ≥ 0, Σ zᵢ ≤ R} ∏ zᵢ^{eᵢ} dz = R^{m + Σ eᵢ} ∏ eᵢ! / (m + Σ eᵢ)!` for `R ≥ 0`. -/
theorem simplex_integral (m : ℕ) (R : ℝ) (e : Fin m → ℕ) (hR : 0 ≤ R) :
    ∫ z in simplex m R, ∏ i, z i ^ e i = momentR m R e :=
  sorry

/-- `m = 0`: the integral is `1` (a point of measure `1`). -/
theorem simplex_integral_zero_dim (R : ℝ) (hR : 0 ≤ R) :
    ∫ z in simplex 0 R, ∏ i, z i ^ (Fin.elim0 i : ℕ) = 1 :=
  sorry

/-- `R < 0`: every moment is `0`. -/
theorem simplex_integral_neg (m : ℕ) (R : ℝ) (e : Fin m → ℕ) (hR : R < 0) :
    ∫ z in simplex m R, ∏ i, z i ^ e i = 0 :=
  sorry

/-- `R = 0`, `m ≥ 1`: every moment is `0`. -/
theorem simplex_integral_radius_zero (m : ℕ) (e : Fin (m + 1) → ℕ) :
    ∫ z in simplex (m + 1) 0, ∏ i, z i ^ e i = 0 :=
  sorry

/-- The volume of the simplex is `R^m / m!`. -/
theorem simplex_volume (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∫ _ in simplex m R, (1 : ℝ) = R ^ m / (m.factorial : ℝ) :=
  sorry

/-- At a rational radius the Beta integral's value is V0's `betaMoment`. -/
theorem betaR_eq_betaMoment (R : ℚ) (u v : ℕ) : betaR (R : ℝ) u v = (betaMoment R u v : ℝ) :=
  sorry

/-- At a rational radius the value of (10.1) is V0's `simplexMoment`. -/
theorem momentR_eq_simplexMoment (m : ℕ) (R : ℚ) (e : Fin m → ℕ) :
    momentR m (R : ℝ) e = (simplexMoment R (List.ofFn e) : ℝ) :=
  sorry

/-- **(10.1) at a rational radius**: the integral is the rational `simplexMoment R e`. -/
theorem simplex_integral_rat (m : ℕ) (R : ℚ) (hR : 0 ≤ R) (e : Fin m → ℕ) :
    ∫ z in simplex m (R : ℝ), ∏ i, z i ^ e i = (simplexMoment R (List.ofFn e) : ℝ) :=
  sorry

/-- **Lemma 10.1 on the simplex**: a rational polynomial integrates to `polyIntegralQ R G ∈ ℚ`. -/
theorem poly_integral (m : ℕ) (R : ℚ) (hR : 0 ≤ R) (G : MvPolynomial (Fin m) ℚ) :
    ∫ z in simplex m (R : ℝ), MvPolynomial.eval₂ (algebraMap ℚ ℝ) z G = (polyIntegralQ R G : ℝ) :=
  sorry

end BGP212.Challenge
