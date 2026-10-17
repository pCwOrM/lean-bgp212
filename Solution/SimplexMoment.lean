/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): (10.1), Lemma 10.1 (pp. 41–42).
-/
import BGP212.SimplexMoment
import Solution.Variational
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp

/-! # V1: (10.1) as an integral (proofs)

* `beta_integral`: `∫₀^R z^u (R − z)^v dz = R^{u+v+1} u! v! / (u+v+1)!` for every real `R`, by
  induction on `v`: the derivative of `z^{u+1}(R − z)^{v+1}` integrates to `0` over `[0, R]`.
* `simplex_integral`: (10.1) for `R ≥ 0`, by induction on `m`: split off the first coordinate
  (`measurePreserving_piFinSuccAbove`), apply Fubini (`integral_prod`), integrate the inner
  `m`-dimensional simplex of radius `R − x` by induction, and close with the Beta moment.
* Boundary cases, the rational form `= simplexMoment R e`, and exact integration of rational
  polynomials (Lemma 10.1 on the simplex). -/

namespace BGP212.Var

open MeasureTheory

theorem simplex_zero (R : ℝ) (hR : 0 ≤ R) : simplex 0 R = Set.univ := by
  ext z; simp [simplex, hR]

theorem zero_dim (R : ℝ) (e : Fin 0 → ℕ) (hR : 0 ≤ R) :
    ∫ z in simplex 0 R, ∏ i, z i ^ e i = momentR 0 R e := by
  rw [simplex_zero R hR, Measure.restrict_univ]
  simp [momentR, Measure.real, volume_pi, Measure.pi_empty_univ]

theorem simplex_isClosed (m : ℕ) (R : ℝ) : IsClosed (simplex m R) := by
  have h1 : IsClosed {z : Fin m → ℝ | ∀ i, 0 ≤ z i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {z : Fin m → ℝ | ∑ i, z i ≤ R} :=
    isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  exact h1.inter h2

theorem simplex_subset_Icc (m : ℕ) (R : ℝ) : simplex m R ⊆ Set.Icc 0 (fun _ => |R|) := by
  rintro z ⟨h0, hs⟩
  refine ⟨fun i => h0 i, fun i => ?_⟩
  have : z i ≤ ∑ j, z j := Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
  exact le_trans this (le_trans hs (le_abs_self R))

theorem simplex_isCompact (m : ℕ) (R : ℝ) : IsCompact (simplex m R) :=
  isCompact_Icc.of_isClosed_subset (simplex_isClosed m R) (simplex_subset_Icc m R)

theorem simplex_measurableSet (m : ℕ) (R : ℝ) : MeasurableSet (simplex m R) :=
  (simplex_isClosed m R).measurableSet

theorem simplex_empty (m : ℕ) (R : ℝ) (hR : R < 0) : simplex m R = ∅ := by
  ext z
  simp only [simplex, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
  intro h0
  exact lt_of_lt_of_le hR (Finset.sum_nonneg fun i _ => h0 i)

theorem cons_mem_simplex (m : ℕ) (R x : ℝ) (w : Fin m → ℝ) :
    (Fin.cons x w : Fin (m + 1) → ℝ) ∈ simplex (m + 1) R ↔ 0 ≤ x ∧ w ∈ simplex m (R - x) := by
  simp only [simplex, Set.mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.sum_univ_succ]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, by linarith⟩

theorem integrableOn_monomial (m : ℕ) (R : ℝ) (e : Fin m → ℕ) :
    IntegrableOn (fun z : Fin m → ℝ => ∏ i, z i ^ e i) (simplex m R) :=
  (by fun_prop : Continuous fun z : Fin m → ℝ => ∏ i, z i ^ e i).continuousOn.integrableOn_compact
    (simplex_isCompact m R)

/-- The inner integral over the last `m` coordinates, at a fixed first coordinate `x`. -/
theorem inner_eq (m : ℕ) (R : ℝ) (e : Fin (m + 1) → ℕ)
    (ih : ∀ r, 0 ≤ r → ∫ w in simplex m r, ∏ j, w j ^ e j.succ = momentR m r (fun j : Fin m => e j.succ))
    (x : ℝ) :
    ∫ w : Fin m → ℝ, (simplex (m + 1) R).indicator (fun z => ∏ i, z i ^ e i) (Fin.cons x w) =
      (Set.Icc 0 R).indicator (fun x => x ^ e 0 * momentR m (R - x) (fun j : Fin m => e j.succ)) x := by
  by_cases hx : 0 ≤ x ∧ x ≤ R
  · rw [Set.indicator_of_mem (show x ∈ Set.Icc 0 R from hx)]
    have : (fun w : Fin m → ℝ => (simplex (m + 1) R).indicator (fun z => ∏ i, z i ^ e i)
        (Fin.cons x w)) = fun w => x ^ e 0 *
          (simplex m (R - x)).indicator (fun w => ∏ j, w j ^ e j.succ) w := by
      funext w
      by_cases hw : w ∈ simplex m (R - x)
      · rw [Set.indicator_of_mem ((cons_mem_simplex m R x w).mpr ⟨hx.1, hw⟩),
          Set.indicator_of_mem hw, Fin.prod_univ_succ]
        simp
      · rw [Set.indicator_of_notMem (fun h => hw ((cons_mem_simplex m R x w).mp h).2),
          Set.indicator_of_notMem hw, mul_zero]
    rw [this, MeasureTheory.integral_const_mul, integral_indicator (simplex_measurableSet m _),
      ih (R - x) (by linarith [hx.2])]
  · rw [Set.indicator_of_notMem (show x ∉ Set.Icc 0 R from hx)]
    have : (fun w : Fin m → ℝ => (simplex (m + 1) R).indicator (fun z => ∏ i, z i ^ e i)
        (Fin.cons x w)) = fun _ => 0 := by
      funext w
      refine Set.indicator_of_notMem (fun h => hx ?_) _
      obtain ⟨h1, h2⟩ := (cons_mem_simplex m R x w).mp h
      refine ⟨h1, ?_⟩
      by_contra hlt
      rw [simplex_empty m (R - x) (by linarith)] at h2
      exact h2
    rw [this, MeasureTheory.integral_zero]

theorem beta_step (R : ℝ) (u v : ℕ) :
    ((u : ℝ) + 1) * ∫ x in (0 : ℝ)..R, x ^ u * (R - x) ^ (v + 1) =
      ((v : ℝ) + 1) * ∫ x in (0 : ℝ)..R, x ^ (u + 1) * (R - x) ^ v := by
  have hG : ∀ x ∈ Set.uIcc (0 : ℝ) R, HasDerivAt (fun x => x ^ (u + 1) * (R - x) ^ (v + 1))
      (((u : ℝ) + 1) * (x ^ u * (R - x) ^ (v + 1)) - ((v : ℝ) + 1) * (x ^ (u + 1) * (R - x) ^ v)) x := by
    intro x _
    have h1 := hasDerivAt_pow (u + 1) x
    have h2 := (hasDerivAt_pow (v + 1) (R - x)).comp x ((hasDerivAt_id x).const_sub R)
    refine HasDerivAt.congr_deriv (h1.mul h2) ?_
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  have hint : IntervalIntegrable (fun x : ℝ => ((u : ℝ) + 1) * (x ^ u * (R - x) ^ (v + 1)) -
      ((v : ℝ) + 1) * (x ^ (u + 1) * (R - x) ^ v)) volume 0 R :=
    (by fun_prop : Continuous fun x : ℝ => ((u : ℝ) + 1) * (x ^ u * (R - x) ^ (v + 1)) -
      ((v : ℝ) + 1) * (x ^ (u + 1) * (R - x) ^ v)).intervalIntegrable 0 R
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hG hint
  rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at this
  · simp at this
    linarith
  · exact ((by fun_prop : Continuous fun x : ℝ => ((u : ℝ) + 1) * (x ^ u * (R - x) ^ (v + 1)))).intervalIntegrable 0 R
  · exact ((by fun_prop : Continuous fun x : ℝ => ((v : ℝ) + 1) * (x ^ (u + 1) * (R - x) ^ v))).intervalIntegrable 0 R

theorem beta_integral (R : ℝ) : ∀ (v u : ℕ), ∫ x in (0 : ℝ)..R, x ^ u * (R - x) ^ v = betaR R u v
  | 0, u => by
      simp only [pow_zero, mul_one, integral_pow, betaR, Nat.factorial_zero, Nat.cast_one]
      rw [Nat.factorial_succ]
      have : (u.factorial : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      simp
  | v + 1, u => by
      have h := beta_step R u v
      rw [beta_integral R v (u + 1)] at h
      have hu : ((u : ℝ) + 1) ≠ 0 := by positivity
      rw [show (∫ x in (0 : ℝ)..R, x ^ u * (R - x) ^ (v + 1)) =
        ((v : ℝ) + 1) * betaR R (u + 1) v / ((u : ℝ) + 1) by field_simp; linarith]
      simp only [betaR]
      rw [show u + 1 + v + 1 = u + (v + 1) + 1 by omega, Nat.factorial_succ u, Nat.factorial_succ v]
      push_cast
      field_simp

theorem moment_cons (m : ℕ) (R : ℝ) (e : Fin (m + 1) → ℕ) :
    momentR (m + 1) R e =
      (∏ j : Fin m, ((e j.succ).factorial : ℝ)) / ((m + ∑ j : Fin m, e j.succ).factorial : ℝ) *
        betaR R (e 0) (m + ∑ j : Fin m, e j.succ) := by
  simp only [momentR, betaR, Fin.sum_univ_succ, Fin.prod_univ_succ]
  rw [show m + 1 + (e 0 + ∑ j : Fin m, e j.succ) = e 0 + (m + ∑ j : Fin m, e j.succ) + 1 by omega]
  have : ((m + ∑ j : Fin m, e j.succ).factorial : ℝ) ≠ 0 := by positivity
  field_simp

/-- **(10.1)**: `∫_{z ≥ 0, Σ z ≤ R} ∏ zᵢ^{eᵢ} dz = R^{m + Σ eᵢ} ∏ eᵢ! / (m + Σ eᵢ)!` for `R ≥ 0`. -/
theorem simplex_integral : ∀ (m : ℕ) (R : ℝ) (e : Fin m → ℕ), 0 ≤ R →
    ∫ z in simplex m R, ∏ i, z i ^ e i = momentR m R e
  | 0, R, e, hR => zero_dim R e hR
  | m + 1, R, e, hR => by
      have ih := fun r hr => simplex_integral m r (fun j : Fin m => e j.succ) hr
      have hE := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => (volume : Measure ℝ)) 0)
      have hint : Integrable ((simplex (m + 1) R).indicator fun z : Fin (m + 1) → ℝ =>
          ∏ i, z i ^ e i) (Measure.pi fun _ => volume) := by
        rw [← volume_pi, integrable_indicator_iff (simplex_measurableSet _ _)]
        exact integrableOn_monomial _ _ _
      rw [← integral_indicator (simplex_measurableSet _ _), volume_pi,
        ← hE.symm.integral_comp', integral_prod _ ?_]
      · simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Equiv.coe_fn_mk, Fin.insertNth_zero']
        simp_rw [← volume_pi]
        simp_rw [inner_eq m R e ih]
        rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le hR]
        simp only [momentR]
        have : (fun x : ℝ => x ^ e 0 * ((R - x) ^ (m + ∑ j : Fin m, e j.succ) *
            (∏ j : Fin m, ((e j.succ).factorial : ℝ)) / ((m + ∑ j : Fin m, e j.succ).factorial : ℝ))) =
            fun x => (∏ j : Fin m, ((e j.succ).factorial : ℝ)) / ((m + ∑ j : Fin m, e j.succ).factorial : ℝ) *
              (x ^ e 0 * (R - x) ^ (m + ∑ j : Fin m, e j.succ)) := by
          funext x; ring
        rw [this, intervalIntegral.integral_const_mul, beta_integral, ← moment_cons]
        rfl
      · exact (hE.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hint


/-! ## Boundary cases -/

/-- `m = 0`: the simplex in `ℝ⁰` is the single point when `R ≥ 0`, of measure `1`. -/
theorem simplex_integral_zero_dim (R : ℝ) (hR : 0 ≤ R) :
    ∫ z in simplex 0 R, ∏ i, z i ^ (Fin.elim0 i : ℕ) = 1 := by
  rw [simplex_integral 0 R _ hR]; simp [momentR]

/-- `R < 0`: the simplex is empty and every moment vanishes. -/
theorem simplex_integral_neg (m : ℕ) (R : ℝ) (e : Fin m → ℕ) (hR : R < 0) :
    ∫ z in simplex m R, ∏ i, z i ^ e i = 0 := by
  rw [simplex_empty m R hR, Measure.restrict_empty, integral_zero_measure]

/-- `R = 0`, `m ≥ 1`: the simplex is a point of measure zero. -/
theorem simplex_integral_radius_zero (m : ℕ) (e : Fin (m + 1) → ℕ) :
    ∫ z in simplex (m + 1) 0, ∏ i, z i ^ e i = 0 := by
  rw [simplex_integral (m + 1) 0 e le_rfl]
  simp [momentR]

/-- The volume of the simplex: `R^m / m!`. -/
theorem simplex_volume (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∫ _ in simplex m R, (1 : ℝ) = R ^ m / (m.factorial : ℝ) := by
  have := simplex_integral m R (fun _ => 0) hR
  simp only [pow_zero, Finset.prod_const_one] at this
  rw [this]; simp [momentR]

/-! ## The integral identity and V0's algebraic formula -/

/-- `betaR` at a rational radius is V0's `betaMoment`. -/
theorem betaR_eq_betaMoment (R : ℚ) (u v : ℕ) : betaR (R : ℝ) u v = (betaMoment R u v : ℝ) := by
  simp [betaR, betaMoment]

/-- `momentR` at a rational radius is V0's `simplexMoment` of the exponent list. -/
theorem momentR_eq_simplexMoment (m : ℕ) (R : ℚ) (e : Fin m → ℕ) :
    momentR m (R : ℝ) e = (simplexMoment R (List.ofFn e) : ℝ) := by
  simp only [momentR, simplexMoment, List.length_ofFn, List.sum_ofFn, List.map_ofFn,
    List.prod_ofFn, Function.comp_def]
  push_cast
  ring

/-- **(10.1) at a rational radius**: the integral equals V0's rational `simplexMoment`. -/
theorem simplex_integral_rat (m : ℕ) (R : ℚ) (hR : 0 ≤ R) (e : Fin m → ℕ) :
    ∫ z in simplex m (R : ℝ), ∏ i, z i ^ e i = (simplexMoment R (List.ofFn e) : ℝ) := by
  rw [simplex_integral _ _ _ (by exact_mod_cast hR), momentR_eq_simplexMoment]

/-! ## Rational polynomials on the simplex (Lemma 10.1) -/

/-- **Lemma 10.1 on the simplex**: for `G ∈ ℚ[z₁, …, z_m]` and rational `R ≥ 0`, the integral of
`G` over the simplex is the rational number `polyIntegralQ R G`. -/
theorem poly_integral (m : ℕ) (R : ℚ) (hR : 0 ≤ R) (G : MvPolynomial (Fin m) ℚ) :
    ∫ z in simplex m (R : ℝ), MvPolynomial.eval₂ (algebraMap ℚ ℝ) z G = (polyIntegralQ R G : ℝ) := by
  simp only [MvPolynomial.eval₂_eq', polyIntegralQ]
  rw [integral_finsetSum]
  · push_cast
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [MeasureTheory.integral_const_mul, simplex_integral _ _ _ (by exact_mod_cast hR)]
    congr 1
    exact momentR_eq_simplexMoment m R d
  · intro d _
    exact (integrableOn_monomial m _ _).const_mul _

end BGP212.Var

namespace BGP212.Challenge

open BGP212.Var MeasureTheory

theorem simplex_isCompact (m : ℕ) (R : ℝ) : IsCompact (simplex m R) :=
  BGP212.Var.simplex_isCompact m R

theorem simplex_empty (m : ℕ) (R : ℝ) (hR : R < 0) : simplex m R = ∅ :=
  BGP212.Var.simplex_empty m R hR

theorem cons_mem_simplex (m : ℕ) (R x : ℝ) (w : Fin m → ℝ) :
    (Fin.cons x w : Fin (m + 1) → ℝ) ∈ simplex (m + 1) R ↔ 0 ≤ x ∧ w ∈ simplex m (R - x) :=
  BGP212.Var.cons_mem_simplex m R x w

theorem beta_integral (R : ℝ) (v u : ℕ) :
    ∫ x in (0 : ℝ)..R, x ^ u * (R - x) ^ v = betaR R u v :=
  BGP212.Var.beta_integral R v u

theorem simplex_integral (m : ℕ) (R : ℝ) (e : Fin m → ℕ) (hR : 0 ≤ R) :
    ∫ z in simplex m R, ∏ i, z i ^ e i = momentR m R e :=
  BGP212.Var.simplex_integral m R e hR

theorem simplex_integral_zero_dim (R : ℝ) (hR : 0 ≤ R) :
    ∫ z in simplex 0 R, ∏ i, z i ^ (Fin.elim0 i : ℕ) = 1 :=
  BGP212.Var.simplex_integral_zero_dim R hR

theorem simplex_integral_neg (m : ℕ) (R : ℝ) (e : Fin m → ℕ) (hR : R < 0) :
    ∫ z in simplex m R, ∏ i, z i ^ e i = 0 :=
  BGP212.Var.simplex_integral_neg m R e hR

theorem simplex_integral_radius_zero (m : ℕ) (e : Fin (m + 1) → ℕ) :
    ∫ z in simplex (m + 1) 0, ∏ i, z i ^ e i = 0 :=
  BGP212.Var.simplex_integral_radius_zero m e

theorem simplex_volume (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∫ _ in simplex m R, (1 : ℝ) = R ^ m / (m.factorial : ℝ) :=
  BGP212.Var.simplex_volume m R hR

theorem betaR_eq_betaMoment (R : ℚ) (u v : ℕ) : betaR (R : ℝ) u v = (betaMoment R u v : ℝ) :=
  BGP212.Var.betaR_eq_betaMoment R u v

theorem momentR_eq_simplexMoment (m : ℕ) (R : ℚ) (e : Fin m → ℕ) :
    momentR m (R : ℝ) e = (simplexMoment R (List.ofFn e) : ℝ) :=
  BGP212.Var.momentR_eq_simplexMoment m R e

theorem simplex_integral_rat (m : ℕ) (R : ℚ) (hR : 0 ≤ R) (e : Fin m → ℕ) :
    ∫ z in simplex m (R : ℝ), ∏ i, z i ^ e i = (simplexMoment R (List.ofFn e) : ℝ) :=
  BGP212.Var.simplex_integral_rat m R hR e

theorem poly_integral (m : ℕ) (R : ℚ) (hR : 0 ≤ R) (G : MvPolynomial (Fin m) ℚ) :
    ∫ z in simplex m (R : ℝ), MvPolynomial.eval₂ (algebraMap ℚ ℝ) z G = (polyIntegralQ R G : ℝ) :=
  BGP212.Var.poly_integral m R hR G

end BGP212.Challenge
