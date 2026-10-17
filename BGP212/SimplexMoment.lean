/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): (10.1), Lemma 10.1 and Proposition 10.2 (pp. 41–42).
-/
import BGP212.Variational
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.MvPolynomial.Eval

/-! # V1: the simplex moment identity (10.1) as an integral

Track B (Mathlib measure theory). V0 defined the right side of (10.1) as the rational
`simplexMoment` and proved its algebraic identities; V1 proves the integral identity itself:

  `∫_{z ∈ ℝ^m, z ≥ 0, Σ zᵢ ≤ R} ∏ zᵢ^{eᵢ} dz = R^{m + Σ eᵢ} ∏ eᵢ! / (m + Σ eᵢ)!`

with respect to Lebesgue measure (`volume` on `Fin m → ℝ`).

* `simplex m R`: the closed simplex `{z | ∀ i, 0 ≤ zᵢ, Σ zᵢ ≤ R}`.
* `momentR m R e`: the right side of (10.1) over `ℝ`.
* `betaR R u v`: the right side of the Beta moment `∫₀^R z^u (R − z)^v dz`.
* `polyIntegralQ R G`: the rational value `Σ_d G_d · simplexMoment R d` assigned to a rational
  polynomial `G`; Lemma 10.1 for the simplex is that it equals the integral of `G`. -/

namespace BGP212.Var

open MeasureTheory

/-- The closed simplex `{z ∈ ℝ^m : zᵢ ≥ 0, Σ zᵢ ≤ R}`. -/
def simplex (m : ℕ) (R : ℝ) : Set (Fin m → ℝ) := {z | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ R}

/-- The right side of (10.1) over `ℝ`. -/
noncomputable def momentR (m : ℕ) (R : ℝ) (e : Fin m → ℕ) : ℝ :=
  R ^ (m + ∑ i, e i) * (∏ i, ((e i).factorial : ℝ)) / ((m + ∑ i, e i).factorial : ℝ)

/-- The right side of the Beta moment over `ℝ`. -/
noncomputable def betaR (R : ℝ) (u v : ℕ) : ℝ :=
  R ^ (u + v + 1) * (u.factorial : ℝ) * (v.factorial : ℝ) / ((u + v + 1).factorial : ℝ)

/-- The exponent vector `d` as V0's list of exponents. -/
def expList {m : ℕ} (d : Fin m →₀ ℕ) : List ℕ := List.ofFn fun i => d i

/-- The rational value of `∫_{simplex m R} G` for `G ∈ ℚ[z₁, …, z_m]`: each monomial `z^d`
contributes `simplexMoment R d`. -/
noncomputable def polyIntegralQ {m : ℕ} (R : ℚ) (G : MvPolynomial (Fin m) ℚ) : ℚ :=
  ∑ d ∈ G.support, G.coeff d * simplexMoment R (expList d)

end BGP212.Var
