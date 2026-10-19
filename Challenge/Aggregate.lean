/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): §9.4, Lemma 9.2 (p. 41), (10.1), Lemma 10.1, Proposition 10.2 (pp. 41–42).
-/
import BGP212.Aggregate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # V2e-A: two-aggregate Dirichlet integration

Statements only; proofs live in `Solution/Aggregate.lean`. Objects are defined in
`BGP212/Aggregate.lean` (with V2b's `simplexF`, `shiftV`, `roughSet`, V2d's `endpoint` and V1's
`polyIntegralQ`). Every statement is parametric: no Table 3 constant enters this pair. -/

namespace BGP212.Challenge

open BGP212.Gram BGP212.V2d BGP212.V2e MeasureTheory

/-- One aggregate: `∫_{z ≥ 0, Σ z ≤ R} zᵉ h(Σ z) = aggConst ι e · ∫_{[0,R]} s^{aggExp ι e} h(s)`. -/
theorem one_group {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (R : ℝ) (e : ι → ℕ) (h : ℝ → ℝ) (hm : Measurable h) (B : ℝ)
    (hb : ∀ s ∈ Set.Icc 0 R, |h s| ≤ B) :
    ∫ z in simplexF ι R, (∏ i, z i ^ e i) * h (∑ i, z i) =
      aggConst ι e * ∫ s in Set.Icc 0 R, s ^ aggExp ι e * h s :=
  sorry

/-- **Two-aggregate Dirichlet integration** (`h` measurable, bounded on `tri R`). -/
theorem two_group {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J] (R : ℝ) (a : I → ℕ) (b : J → ℕ)
    (h : ℝ × ℝ → ℝ) (hm : Measurable h) (B : ℝ) (hb : ∀ q ∈ tri R, |h q| ≤ B) :
    ∫ p in quad I J R, (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) * h (∑ i, p.1 i, ∑ j, p.2 j) =
      aggConst I a * aggConst J b *
        ∫ q in tri R, q.1 ^ aggExp I a * q.2 ^ aggExp J b * h q :=
  sorry

/-- The same on `Fin N`, with rough aggregate `u₁ = aggR R y` and smooth aggregate `u₂ = aggS R y`. -/
theorem two_group_fin {N : ℕ} (R : Finset (Fin N)) (hR : R.Nonempty) (hRc : Rᶜ.Nonempty) (M : ℝ)
    (t : Fin N → ℕ) (h : ℝ × ℝ → ℝ) (hm : Measurable h) (B : ℝ) (hb : ∀ q ∈ tri M, |h q| ≤ B) :
    ∫ y in simplexF (Fin N) M, (∏ i, y i ^ t i) * h (aggR R y, aggS R y) =
      aggConst {i // i ∈ R} (fun i => t i) * aggConst {i // i ∉ R} (fun i => t i) *
        ∫ q in tri M, q.1 ^ aggExp {i // i ∈ R} (fun i => t i) *
          q.2 ^ aggExp {i // i ∉ R} (fun i => t i) * h q :=
  sorry

/-- Empty group: the integral is `h 0`. -/
theorem one_group_empty {ι : Type*} [Fintype ι] [IsEmpty ι] (R : ℝ) (hR : 0 ≤ R) (e : ι → ℕ)
    (h : ℝ → ℝ) :
    ∫ z in simplexF ι R, (∏ i, z i ^ e i) * h (∑ i, z i) = h 0 :=
  sorry

/-- Empty smooth group (`u₂ = 0`). -/
theorem two_group_right_empty {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [Nonempty I] [IsEmpty J] (R : ℝ) (a : I → ℕ)
    (b : J → ℕ) (h : ℝ × ℝ → ℝ) (hm : Measurable h) (B : ℝ) (hb : ∀ q ∈ tri R, |h q| ≤ B) :
    ∫ p in quad I J R, (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) * h (∑ i, p.1 i, ∑ j, p.2 j) =
      aggConst I a * ∫ u in Set.Icc 0 R, u ^ aggExp I a * h (u, 0) :=
  sorry

/-- Empty rough group (`u₁ = 0`). -/
theorem two_group_left_empty {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J] [IsEmpty I] [Nonempty J] (R : ℝ) (a : I → ℕ)
    (b : J → ℕ) (h : ℝ × ℝ → ℝ) (hm : Measurable h) (B : ℝ) (hb : ∀ q ∈ tri R, |h q| ≤ B) :
    ∫ p in quad I J R, (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) * h (∑ i, p.1 i, ∑ j, p.2 j) =
      aggConst J b * ∫ u in Set.Icc 0 R, u ^ aggExp J b * h (0, u) :=
  sorry

/-- Both groups empty: the value `h (0, 0)`. -/
theorem two_group_both_empty {I J : Type*} [Fintype I] [Fintype J] [IsEmpty I] [IsEmpty J] (R : ℝ) (hR : 0 ≤ R) (a : I → ℕ)
    (b : J → ℕ) (h : ℝ × ℝ → ℝ) :
    ∫ p in quad I J R, (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) * h (∑ i, p.1 i, ∑ j, p.2 j) =
      h (0, 0) :=
  sorry

/-- Zero exponents. -/
theorem aggConst_zero (ι : Type*) [Fintype ι] :
    aggConst ι (fun _ => 0) = 1 / ((Fintype.card ι - 1).factorial : ℝ) :=
  sorry

/-- Monomials on the triangle (V1's (10.1) in dimension 2). -/
theorem tri_monomial (R : ℝ) (hR : 0 ≤ R) (α β : ℕ) :
    ∫ q in tri R, q.1 ^ α * q.2 ^ β =
      R ^ (2 + α + β) * (α.factorial : ℝ) * (β.factorial : ℝ) / ((2 + α + β).factorial : ℝ) :=
  sorry

/-- Rational polynomials on the triangle (V1's Lemma 10.1 in dimension 2). -/
theorem tri_poly (R : ℚ) (hR : 0 ≤ R) (G : MvPolynomial (Fin 2) ℚ) :
    ∫ q in tri (R : ℝ), MvPolynomial.eval₂ (algebraMap ℚ ℝ) ![q.1, q.2] G = (BGP212.Var.polyIntegralQ R G : ℝ) :=
  sorry

/-- Rational polynomial specialization of the two-aggregate theorem. -/
theorem two_group_poly {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (R : ℚ) (hR : 0 ≤ R) (a : I → ℕ) (b : J → ℕ) (P : MvPolynomial (Fin 2) ℚ) :
    ∫ p in quad I J (R : ℝ), (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) ![∑ i, p.1 i, ∑ j, p.2 j] P =
      ((aggConstQ I a * aggConstQ J b *
        BGP212.Var.polyIntegralQ R (MvPolynomial.X 0 ^ aggExp I a * MvPolynomial.X 1 ^ aggExp J b * P) : ℚ) : ℝ) :=
  sorry

/-- Consistency with (10.1): `h = 1` gives the simplex moment of the combined monomial. -/
theorem two_group_const {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J] (R : ℝ) (hR : 0 ≤ R) (a : I → ℕ) (b : J → ℕ) :
    ∫ p in quad I J R, (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) =
      R ^ (Fintype.card I + ∑ i, a i + (Fintype.card J + ∑ j, b j)) *
        (∏ i, ((a i).factorial : ℝ)) * (∏ j, ((b j).factorial : ℝ)) /
          ((Fintype.card I + ∑ i, a i + (Fintype.card J + ∑ j, b j)).factorial : ℝ) :=
  sorry

/-- On a translated piece the rough mass is `|R| g + u₁`. -/
theorem aggR_shift {N : ℕ} (g : ℝ) (R K : Finset (Fin N)) (y : Fin N → ℝ) :
    aggR R (y + shiftV g (R ∪ K)) = R.card * g + aggR R y :=
  sorry

/-- On a translated piece the remaining mass is `|K| g + u₂`. -/
theorem aggS_shift {N : ℕ} (g : ℝ) (R K : Finset (Fin N)) (hRK : Disjoint R K) (y : Fin N → ℝ) :
    aggS R (y + shiftV g (R ∪ K)) = K.card * g + aggS R y :=
  sorry

/-- On the stratum `roughSet g x = R`, Lemma 9.2's endpoint is the stratum endpoint. -/
theorem endpoint_eq_stratum {n : ℕ} (g L : ℝ) (C : ℕ → ℝ) (x : Fin n → ℝ) (R : Finset (Fin n))
    (hR : roughSet g x = R) :
    endpoint g L C x = stratumEndpoint g L C R x :=
  sorry

/-- The endpoint on a translated piece is a function of the two aggregates. -/
theorem stratumEndpoint_shift {n : ℕ} (g L : ℝ) (C : ℕ → ℝ) (R K : Finset (Fin n))
    (hRK : Disjoint R K) (y : Fin n → ℝ) :
    stratumEndpoint g L C R (y + shiftV g (R ∪ K)) =
      endpointAgg g L C R.card K.card (aggR R y) (aggS R y) :=
  sorry

/-- One cut `u₁ ≤ c` of the triangle, in closed form. -/
theorem tri_cut (R c : ℝ) (hc : 0 ≤ c) (hcR : c ≤ R) (α β : ℕ) :
    ∫ q in tri R, q.1 ^ α * q.2 ^ β * (Set.Iic c).indicator (fun _ => (1 : ℝ)) q.1 =
      (∑ j ∈ Finset.range (β + 1 + 1), ((β + 1).choose j : ℝ) * R ^ (β + 1 - j) * (-1) ^ j *
        c ^ (α + j + 1) / (α + j + 1)) / (β + 1) :=
  sorry

/-- **The worked example**: `∫_{y ∈ ℝ³, y ≥ 0, Σ y ≤ 1} y₀ y₂² 1[y₀ ≤ 1/2] = 19/7680`. -/
theorem example_value :
    exampleLHS (1 / 2) 1 = 19 / 7680 :=
  sorry

end BGP212.Challenge
