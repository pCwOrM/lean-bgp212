/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.4, Lemma 9.2 (p. 41), Proposition 10.2 (pp. 41–42).
-/
import BGP212.CapCell
import Solution.Aggregate

/-! # V2e-B: polygon cells of the cap branch (proofs)

PROVED INTEGRAL IDENTITIES; one COMPUTATIONAL CERTIFICATE (`capPieceT3_value`).

1. `boxTri_integral`: Fubini on a cell `{0 ≤ u₁ ≤ A, 0 ≤ u₂ ≤ B, u₁ + u₂ ≤ D}`.
2. `box_monomial`: `∫_{cell} u₁^α u₂^β = boxVal A B D α β`, splitting `[0, A]` at
   `E = max 0 (min A (D − B))` and `F = max 0 (min A D)` (fibre length `B`, then `D − u₁`, then `0`)
   and V2d's `inner_integral`.
3. Rational values and boundary cases: `boxVal_cast`, `boxVal_empty`, `boxVal_nonpos`,
   `boxVal_rect`; polynomial integrands `box_capPow`, `box_poly`.
4. The branches of the endpoint on a piece (`endpointAgg_cap`, `endpointAgg_gBranch`,
   `endpointAgg_LBranch_cap`, `endpointAgg_LBranch_g`), the cap cell (`mem_capCell`,
   `endpointAgg_on_capCell`), the inactive τ constraint (`cap_total_le`, `capCell_rect`) and empty
   cells (`capCell_empty`); the inner integral on the cap cell (`cap_inner`).
5. `cap_branch_piece`: the cap branch of a piece through V2e-A's `two_group_fin`; `cap_branch_r0`
   for the stratum with no rough coordinates (V2e-A's `one_group`).
6. Table 3: `tau_ge_table3`, `capCell_rect_table3`, `capCell_empty_table3`, and the certificate
   `capPieceT3_value` (`decide +kernel` on the rational `capPowVal`). -/

namespace BGP212.V2e

open BGP212.Gram BGP212.V2d MeasureTheory

/-! ## The cell `boxTri` -/

theorem boxTri_isClosed (A B D : ℝ) : IsClosed (boxTri A B D) := by
  have : boxTri A B D = {q : ℝ × ℝ | 0 ≤ q.1} ∩ ({q | q.1 ≤ A} ∩ ({q | 0 ≤ q.2} ∩
      ({q | q.2 ≤ B} ∩ {q | q.1 + q.2 ≤ D}))) := by
    ext q; simp [boxTri]
  rw [this]
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_fst continuous_const).inter
      ((isClosed_le continuous_const continuous_snd).inter
        ((isClosed_le continuous_snd continuous_const).inter
          (isClosed_le (by fun_prop) continuous_const))))

theorem boxTri_isCompact (A B D : ℝ) : IsCompact (boxTri A B D) := by
  refine (isCompact_Icc (a := ((0 : ℝ), (0 : ℝ))) (b := (|A|, |B|))).of_isClosed_subset
    (boxTri_isClosed A B D) ?_
  rintro ⟨u, s⟩ ⟨h1, h2, h3, h4, -⟩
  exact ⟨⟨h1, h3⟩, ⟨le_trans h2 (le_abs_self A), le_trans h4 (le_abs_self B)⟩⟩

theorem boxTri_subset_tri (A B D : ℝ) : boxTri A B D ⊆ tri D :=
  fun _ h => ⟨h.1, h.2.2.1, h.2.2.2.2⟩

theorem boxTri_empty (A B D : ℝ) (h : ¬(0 ≤ A ∧ 0 ≤ B)) : boxTri A B D = ∅ := by
  ext q
  simp only [boxTri, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1 h2 h3 h4 _
  exact h ⟨le_trans h1 h2, le_trans h3 h4⟩

/-- **Fubini on a cell**: `∫_{boxTri A B D} f = ∫_{[0,A]} ∫_{[0, min B (D − u)]} f(u, s) ds du`. -/
theorem boxTri_integral (A B D : ℝ) (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
    ∫ q in boxTri A B D, f q =
      ∫ u in Set.Icc 0 A, ∫ s in Set.Icc 0 (min B (D - u)), f (u, s) := by
  have hm := (boxTri_isClosed A B D).measurableSet
  have hint : Integrable ((boxTri A B D).indicator f) (volume.prod volume) := by
    rw [integrable_indicator_iff hm]
    exact hf.continuousOn.integrableOn_compact (boxTri_isCompact A B D)
  rw [← integral_indicator hm, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    integral_prod _ hint, ← integral_indicator measurableSet_Icc]
  congr 1
  funext u
  by_cases hu : u ∈ Set.Icc 0 A
  · rw [Set.indicator_of_mem hu, ← integral_indicator measurableSet_Icc]
    congr 1
    funext s
    have hmem : (u, s) ∈ boxTri A B D ↔ s ∈ Set.Icc 0 (min B (D - u)) := by
      simp only [boxTri, Set.mem_ofPred_eq, Set.mem_Icc, le_min_iff]
      constructor
      · rintro ⟨-, -, h3, h4, h5⟩; exact ⟨h3, h4, by linarith⟩
      · rintro ⟨h3, h4, h5⟩; exact ⟨hu.1, hu.2, h3, h4, by linarith⟩
    by_cases hs : s ∈ Set.Icc 0 (min B (D - u))
    · rw [Set.indicator_of_mem (hmem.mpr hs), Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem (fun h' => hs (hmem.mp h')), Set.indicator_of_notMem hs]
  · rw [Set.indicator_of_notMem hu]
    have : (fun s => (boxTri A B D).indicator f (u, s)) = fun _ => 0 := by
      funext s
      refine Set.indicator_of_notMem ?_ _
      rintro ⟨h1, h2, -⟩
      exact hu ⟨h1, h2⟩
    rw [this, integral_zero]

/-- The fibre length `max 0 (min B (D − u))` and the inner monomial integral. -/
theorem inner_box (B D u : ℝ) (β : ℕ) :
    ∫ s in Set.Icc 0 (min B (D - u)), s ^ β = (max 0 (min B (D - u))) ^ (β + 1) / (β + 1) := by
  by_cases h : 0 ≤ min B (D - u)
  · rw [integral_Icc_pow _ h, max_eq_right h]
  · push Not at h
    rw [Set.Icc_eq_empty (by linarith), Measure.restrict_empty, integral_zero_measure,
      max_eq_left h.le]
    simp

theorem innerVal_eq (X D : ℝ) (p t : ℕ) :
    ∫ u in (0 : ℝ)..X, (D - u) ^ p * u ^ t = innerVal X D p t := by
  rw [inner_integral X D p t, innerVal]

/-- **Monomials on a cell**: `∫_{boxTri A B D} u₁^α u₂^β = boxVal A B D α β`. -/
theorem box_monomial (A B D : ℝ) (α β : ℕ) :
    ∫ q in boxTri A B D, q.1 ^ α * q.2 ^ β = boxVal A B D α β := by
  by_cases hAB : 0 ≤ A ∧ 0 ≤ B
  swap
  · rw [boxTri_empty A B D hAB, Measure.restrict_empty, integral_zero_measure, boxVal, if_neg hAB]
  obtain ⟨hA, hB⟩ := hAB
  rw [boxVal, if_pos ⟨hA, hB⟩, boxTri_integral A B D _ (by fun_prop)]
  set ℓ : ℝ → ℝ := fun u => max 0 (min B (D - u))
  have hin : ∀ u, ∫ s in Set.Icc 0 (min B (D - u)), u ^ α * s ^ β =
      ℓ u ^ (β + 1) * u ^ α / (β + 1) := by
    intro u
    rw [integral_const_mul, inner_box]; ring
  simp_rw [hin]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hA]
  set E := max 0 (min A (D - B))
  set F := max 0 (min A D)
  have hE0 : 0 ≤ E := le_max_left _ _
  have hEF : E ≤ F := max_le_max le_rfl (min_le_min le_rfl (by linarith))
  have hFA : F ≤ A := max_le hA (min_le_left _ _)
  have hcont : Continuous fun u => ℓ u ^ (β + 1) * u ^ α / (β + 1) := by
    simp only [ℓ]; fun_prop
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun u => ℓ u ^ (β + 1) * u ^ α / (β + 1)) volume a b :=
    fun a b => hcont.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 E) (hi E A),
    ← intervalIntegral.integral_add_adjacent_intervals (hi E F) (hi F A)]
  -- on (0, E]: ℓ = B
  have h1 : ∫ u in (0 : ℝ)..E, ℓ u ^ (β + 1) * u ^ α / (β + 1) =
      ∫ u in (0 : ℝ)..E, B ^ (β + 1) * u ^ α / (β + 1) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun u hu => ?_)
    rw [Set.uIoc_of_le hE0] at hu
    have hE : E = min A (D - B) := max_eq_right (le_trans (le_of_lt hu.1) hu.2 |> fun h => by
      by_contra hc; push Not at hc
      have : E = 0 := max_eq_left hc.le
      linarith [hu.1, hu.2])
    have hu2 : u ≤ D - B := le_trans hu.2 (hE ▸ min_le_right _ _)
    simp only [ℓ]
    rw [min_eq_left (by linarith), max_eq_right hB]
  -- on (E, F]: ℓ = D − u
  have h2 : ∫ u in E..F, ℓ u ^ (β + 1) * u ^ α / (β + 1) =
      ∫ u in E..F, (D - u) ^ (β + 1) * u ^ α / (β + 1) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun u hu => ?_)
    rw [Set.uIoc_of_le hEF] at hu
    have hupos : 0 < u := lt_of_le_of_lt hE0 hu.1
    have huA : u ≤ A := le_trans hu.2 hFA
    have hF : F = min A D := max_eq_right (by
      by_contra hc; push Not at hc
      have : F = 0 := max_eq_left hc.le
      linarith [hu.2])
    have huD : u ≤ D := le_trans hu.2 (hF ▸ min_le_right _ _)
    have huDB : D - B < u := by
      by_contra hc; push Not at hc
      have : u ≤ min A (D - B) := le_min huA hc
      linarith [hu.1, le_max_right 0 (min A (D - B))]
    simp only [ℓ]
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
  -- on (F, A]: ℓ = 0
  have h3 : ∫ u in F..A, ℓ u ^ (β + 1) * u ^ α / (β + 1) = 0 := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ))
      (Filter.Eventually.of_forall fun u hu => ?_), intervalIntegral.integral_zero]
    rw [Set.uIoc_of_le hFA] at hu
    have hDu : D < u := by
      by_contra hc; push Not at hc
      have : u ≤ min A D := le_min hu.2 hc
      linarith [hu.1, le_max_right 0 (min A D)]
    simp only [ℓ]
    rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    simp
  rw [h1, h2, h3, add_zero]
  have h1' : ∫ u in (0 : ℝ)..E, B ^ (β + 1) * u ^ α / (β + 1) =
      B ^ (β + 1) * E ^ (α + 1) / (α + 1) / (β + 1) := by
    simp only [mul_div_assoc]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div, integral_pow]
    simp
  have h2' : ∫ u in E..F, (D - u) ^ (β + 1) * u ^ α / (β + 1) =
      (innerVal F D (β + 1) α - innerVal E D (β + 1) α) / (β + 1) := by
    rw [intervalIntegral.integral_div, ← innerVal_eq, ← innerVal_eq,
      intervalIntegral.integral_interval_sub_left]
    · exact (by fun_prop : Continuous fun u : ℝ => (D - u) ^ (β + 1) * u ^ α).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun u : ℝ => (D - u) ^ (β + 1) * u ^ α).intervalIntegrable _ _
  rw [h1', h2']
  ring

/-! ## Rational values and boundary cases -/

theorem innerVal_cast (X D : ℚ) (p t : ℕ) :
    ((innerVal X D p t : ℚ) : ℝ) = innerVal (X : ℝ) (D : ℝ) p t := by
  simp [innerVal]

/-- `boxVal` commutes with the cast `ℚ → ℝ`: over `ℚ` it is the computable certificate value. -/
theorem boxVal_cast (A B D : ℚ) (α β : ℕ) :
    ((boxVal A B D α β : ℚ) : ℝ) = boxVal (A : ℝ) (B : ℝ) (D : ℝ) α β := by
  unfold boxVal
  by_cases h : 0 ≤ A ∧ 0 ≤ B
  · have h' : 0 ≤ (A : ℝ) ∧ 0 ≤ (B : ℝ) := ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    rw [if_pos h, if_pos h']
    push_cast [innerVal_cast, Rat.cast_max, Rat.cast_min]
    rfl
  · have h' : ¬(0 ≤ (A : ℝ) ∧ 0 ≤ (B : ℝ)) := fun h' => h ⟨by exact_mod_cast h'.1, by exact_mod_cast h'.2⟩
    rw [if_neg h, if_neg h']
    simp

theorem capPowVal_cast (A B D a : ℚ) (α β m : ℕ) :
    ((capPowVal A B D a α β m : ℚ) : ℝ) = capPowVal (A : ℝ) (B : ℝ) (D : ℝ) (a : ℝ) α β m := by
  simp [capPowVal, boxVal_cast]

/-- **Empty cell** (`A < 0` or `B < 0`). -/
theorem boxVal_empty (A B D : ℝ) (α β : ℕ) (h : A < 0 ∨ B < 0) : boxVal A B D α β = 0 := by
  rw [boxVal, if_neg]
  rintro ⟨hA, hB⟩
  rcases h with h | h <;> linarith

/-- **Cell beyond the diagonal** (`D ≤ 0`): only the null set `u₁ = u₂ = 0` remains. -/
theorem boxVal_nonpos (A B D : ℝ) (α β : ℕ) (hD : D ≤ 0) : boxVal A B D α β = 0 := by
  unfold boxVal
  split_ifs with h
  · have hE : max 0 (min A (D - B)) = 0 :=
      max_eq_left (le_trans (min_le_right _ _) (by linarith [h.2]))
    have hF : max 0 (min A D) = 0 := max_eq_left (le_trans (min_le_right _ _) hD)
    rw [hE, hF]
    simp
  · rfl

/-- **Rectangular cell** (`A + B ≤ D`, the anti-diagonal inactive): the product of two
one-variable moments. -/
theorem boxVal_rect (A B D : ℝ) (α β : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : A + B ≤ D) :
    boxVal A B D α β = A ^ (α + 1) / (α + 1) * (B ^ (β + 1) / (β + 1)) := by
  rw [boxVal, if_pos ⟨hA, hB⟩, min_eq_left (by linarith : A ≤ D - B), min_eq_left (by linarith),
    max_eq_right hA]
  ring

/-! ## The cap power and polynomial integrands -/

/-- `∫_{boxTri A B D} u₁^α u₂^β (a − u₁)^m = capPowVal A B D a α β m`. -/
theorem box_capPow (A B D a : ℝ) (α β m : ℕ) :
    ∫ q in boxTri A B D, q.1 ^ α * q.2 ^ β * (a - q.1) ^ m = capPowVal A B D a α β m := by
  have hexp : ∀ q : ℝ × ℝ, q.1 ^ α * q.2 ^ β * (a - q.1) ^ m =
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * a ^ (m - i) * (-1) ^ i *
        (q.1 ^ (α + i) * q.2 ^ β) := by
    intro q
    rw [show a - q.1 = -q.1 + a by ring, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [neg_pow]; ring
  simp_rw [hexp]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, box_monomial]
  · intro i _
    exact (by fun_prop : Continuous fun q : ℝ × ℝ => (m.choose i : ℝ) * a ^ (m - i) * (-1) ^ i *
      (q.1 ^ (α + i) * q.2 ^ β)).continuousOn.integrableOn_compact (boxTri_isCompact A B D)

/-- **Rational polynomials on a cell**: for `P ∈ ℚ[u₁, u₂]`,
`∫_{boxTri A B D} P(u₁, u₂) = Σ_d coeff_d(P) · boxVal A B D d₀ d₁`. -/
theorem box_poly (A B D : ℝ) (P : MvPolynomial (Fin 2) ℚ) :
    ∫ q in boxTri A B D, MvPolynomial.eval₂ (algebraMap ℚ ℝ) ![q.1, q.2] P =
      ∑ d ∈ P.support, ((P.coeff d : ℚ) : ℝ) * boxVal A B D (d 0) (d 1) := by
  simp only [MvPolynomial.eval₂_eq', Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [integral_const_mul, box_monomial]
    rfl
  · intro d _
    exact (by fun_prop : Continuous fun q : ℝ × ℝ => (algebraMap ℚ ℝ) (P.coeff d) *
      (q.1 ^ d 0 * q.2 ^ d 1)).continuousOn.integrableOn_compact (boxTri_isCompact A B D)

/-! ## The branches of the endpoint on a piece -/

section Branches

variable (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (u₁ u₂ : ℝ)

/-- **Cap branch**: `u₁ ≤ C(r+1) − (r+1) g` and `u₂ ≤ L − k g − C(r+1)` give
`U = C(r+1) − r g − u₁`. -/
theorem endpointAgg_cap (h₁ : u₁ ≤ C (r + 1) - (r + 1) * g) (h₂ : u₂ ≤ L - k * g - C (r + 1)) :
    endpointAgg g L C r k u₁ u₂ = C (r + 1) - (r * g + u₁) := by
  rw [endpointAgg, max_eq_right (by linarith), min_eq_right (by linarith)]

/-- **`g` branch**: `u₁ ≥ C(r+1) − (r+1) g` and `u₁ + u₂ ≤ L − (r+k+1) g` give `U = g`. -/
theorem endpointAgg_gBranch (h₁ : C (r + 1) - (r + 1) * g ≤ u₁)
    (h₂ : u₁ + u₂ ≤ L - (r + k + 1) * g) : endpointAgg g L C r k u₁ u₂ = g := by
  rw [endpointAgg, max_eq_left (by linarith), min_eq_right (by linarith)]

/-- **`L − S` branch**, cap side: `u₁ ≤ C(r+1) − (r+1) g` and `u₂ ≥ L − k g − C(r+1)`. -/
theorem endpointAgg_LBranch_cap (h₁ : u₁ ≤ C (r + 1) - (r + 1) * g)
    (h₂ : L - k * g - C (r + 1) ≤ u₂) :
    endpointAgg g L C r k u₁ u₂ = L - ((r + k) * g + u₁ + u₂) := by
  rw [endpointAgg, max_eq_right (by linarith), min_eq_left (by linarith)]

/-- **`L − S` branch**, `g` side: `u₁ ≥ C(r+1) − (r+1) g` and `u₁ + u₂ ≥ L − (r+k+1) g`. -/
theorem endpointAgg_LBranch_g (h₁ : C (r + 1) - (r + 1) * g ≤ u₁)
    (h₂ : L - (r + k + 1) * g ≤ u₁ + u₂) :
    endpointAgg g L C r k u₁ u₂ = L - ((r + k) * g + u₁ + u₂) := by
  rw [endpointAgg, max_eq_left (by linarith), min_eq_left (by linarith)]

/-- **The τ constraint is inactive on the cap branch**: there `g ≤ U ≤ L − S`, so
`S = (r+k) g + u₁ + u₂ ≤ L − g`. -/
theorem cap_total_le (h₁ : u₁ ≤ C (r + 1) - (r + 1) * g) (h₂ : u₂ ≤ L - k * g - C (r + 1)) :
    (r + k) * g + u₁ + u₂ ≤ L - g := by linarith

end Branches

theorem mem_capCell (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ) (q : ℝ × ℝ) :
    q ∈ capCell g L C r k c M ↔ q ∈ tri M ∧ q.1 ≤ c ∧ q.1 ≤ C (r + 1) - (r + 1) * g ∧
      q.2 ≤ L - k * g - C (r + 1) := by
  simp only [capCell, boxTri, tri, Set.mem_ofPred_eq, le_min_iff]
  tauto

/-- On the cap cell the endpoint takes the cap value. -/
theorem endpointAgg_on_capCell (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ) (q : ℝ × ℝ)
    (hq : q ∈ capCell g L C r k c M) :
    endpointAgg g L C r k q.1 q.2 = C (r + 1) - (r * g + q.1) := by
  rw [mem_capCell] at hq
  exact endpointAgg_cap g L C r k q.1 q.2 hq.2.2.1 hq.2.2.2

/-- **Rectangular cap cells**: if `L − g ≤ τ`, the piece total `M = τ − (r+k) g` never cuts the
cap cell (`A + B ≤ M`). -/
theorem capCell_rect (g L τ : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c : ℝ) (hτ : L - g ≤ τ) :
    min c (C (r + 1) - (r + 1) * g) + (L - k * g - C (r + 1)) ≤ τ - (r + k) * g := by
  have := min_le_right c (C (r + 1) - (r + 1) * g)
  linarith

/-- **Empty cap cells**: if `L − k g < C(r+1)` the cap branch is empty on the piece. -/
theorem capCell_empty (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ) (h : L - k * g < C (r + 1)) :
    capCell g L C r k c M = ∅ :=
  boxTri_empty _ _ _ (fun h' => by linarith [h'.2])

/-- **The inner integral on the cap cell**, a polynomial in `(u₁, u₂)`:
`∫₀^U (L − S − u)^p u^t du` with `U = C(r+1) − r g − u₁`, `L − S = L − (r+k) g − u₁ − u₂`. -/
theorem cap_inner (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ) (q : ℝ × ℝ)
    (hq : q ∈ capCell g L C r k c M) (p t : ℕ) :
    ∫ u in (0 : ℝ)..endpointAgg g L C r k q.1 q.2, (L - ((r + k) * g + q.1 + q.2) - u) ^ p * u ^ t =
      innerVal (C (r + 1) - (r * g + q.1)) (L - ((r + k) * g + q.1 + q.2)) p t := by
  rw [endpointAgg_on_capCell g L C r k c M q hq, innerVal_eq]

/-! ## Cap-branch integrals on a piece -/

/-- On a piece, restricting to the cap cell makes the piece constraints automatic:
the integral over `pieceSet N R c M` equals the integral over the simplex `Σ y ≤ M`. -/
theorem piece_cap_eq {N : ℕ} (R : Finset (Fin N)) (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ)
    (G : (Fin N → ℝ) → ℝ) (Φ : ℝ × ℝ → ℝ) :
    ∫ y in pieceSet N R c M, G y * (capCell g L C r k c M).indicator Φ (aggR R y, aggS R y) =
      ∫ y in simplexF (Fin N) M, G y * (capCell g L C r k c M).indicator Φ (aggR R y, aggS R y) := by
  refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (simplexF_measurableSet M)
    (pieceSet_subset_simplexF N R c M) fun y hy => ?_).symm
  rw [Set.indicator_of_notMem, mul_zero]
  intro hq
  rw [mem_capCell] at hq
  exact hy.2 ⟨hy.1.1, hq.2.1, hy.1.2⟩

/-- **The cap branch on a piece.** For a piece `(R, K)` of V2b's decomposition (`R`, `Rᶜ`
nonempty, `k = |K|`, piece cap `c`, piece total `M`), a monomial weight `yᵗ` and the `m`-th power
of the endpoint restricted to the cap branch:
`∫_{pieceSet} yᵗ · 1_cap · U^m = aggConst R t · aggConst Rᶜ t ·
capPowVal (min c c₁) c₂ M (C(r+1) − r g) (aggExp R t) (aggExp Rᶜ t) m`. -/
theorem cap_branch_piece {N : ℕ} (R : Finset (Fin N)) (hR : R.Nonempty) (hRc : Rᶜ.Nonempty)
    (g L : ℝ) (C : ℕ → ℝ) (k : ℕ) (c M : ℝ) (t : Fin N → ℕ) (m : ℕ) :
    ∫ y in pieceSet N R c M, (∏ i, y i ^ t i) *
        (capCell g L C R.card k c M).indicator
          (fun q => (endpointAgg g L C R.card k q.1 q.2) ^ m) (aggR R y, aggS R y) =
      aggConst {i // i ∈ R} (fun i => t i) * aggConst {i // i ∉ R} (fun i => t i) *
        capPowVal (min c (C (R.card + 1) - (R.card + 1) * g)) (L - k * g - C (R.card + 1)) M
          (C (R.card + 1) - R.card * g) (aggExp {i // i ∈ R} (fun i => t i))
          (aggExp {i // i ∉ R} (fun i => t i)) m := by
  set Z := capCell g L C R.card k c M
  set a := C (R.card + 1) - R.card * g
  -- on the cell, `U^m = (a − u₁)^m`
  have hΦ : Z.indicator (fun q => (endpointAgg g L C R.card k q.1 q.2) ^ m) =
      Z.indicator (fun q => (a - q.1) ^ m) := by
    funext q
    by_cases hq : q ∈ Z
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq,
        endpointAgg_on_capCell g L C R.card k c M q hq]
      congr 1; ring
    · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
  have hZm : MeasurableSet Z := (boxTri_isClosed _ _ _).measurableSet
  obtain ⟨Bd, hBd⟩ := (tri_isCompact M).exists_bound_of_continuousOn
    (by fun_prop : Continuous fun q : ℝ × ℝ => (a - q.1) ^ m).continuousOn
  rw [piece_cap_eq, hΦ,
    two_group_fin R hR hRc M t _ ((by fun_prop : Measurable fun q : ℝ × ℝ => (a - q.1) ^ m).indicator hZm)
      Bd (fun q hq => by
        rw [← Real.norm_eq_abs, norm_indicator_eq_indicator_norm]
        by_cases h : q ∈ Z
        · rw [Set.indicator_of_mem h]; exact hBd q hq
        · rw [Set.indicator_of_notMem h]; exact le_trans (norm_nonneg _) (hBd q hq))]
  congr 1
  rw [← box_capPow]
  have hsub : Z ⊆ tri M := boxTri_subset_tri _ _ _
  rw [show (fun q : ℝ × ℝ => q.1 ^ aggExp {i // i ∈ R} (fun i => t i) *
      q.2 ^ aggExp {i // i ∉ R} (fun i => t i) * Z.indicator (fun q => (a - q.1) ^ m) q) =
      Z.indicator (fun q : ℝ × ℝ => q.1 ^ aggExp {i // i ∈ R} (fun i => t i) *
        q.2 ^ aggExp {i // i ∉ R} (fun i => t i) * (a - q.1) ^ m) from by
    funext q; by_cases h : q ∈ Z
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero],
    setIntegral_indicator hZm, Set.inter_eq_right.mpr hsub]
  rfl

/-! ## The stratum with no rough coordinates (`R = ∅`) -/

/-- **`r = 0`**: with no rough coordinates `u₁ = 0` and `U = C(1)` on the cap branch; the piece
integral is a one-aggregate integral over `u₂ ∈ [0, min c₂ M]`. -/
theorem cap_branch_r0 {N : ℕ} (hN : 0 < N) (g L : ℝ) (C : ℕ → ℝ) (k : ℕ) (c M : ℝ)
    (t : Fin N → ℕ) (m : ℕ) (hc : 0 ≤ c) (hc₁ : 0 ≤ C 1 - g) :
    ∫ y in pieceSet N ∅ c M, (∏ i, y i ^ t i) *
        (capCell g L C 0 k c M).indicator
          (fun q => (endpointAgg g L C 0 k q.1 q.2) ^ m) (aggR ∅ y, aggS ∅ y) =
      aggConst (Fin N) t * (C 1 ^ m *
        ((max 0 (min (L - k * g - C 1) (M - 0))) ^ (aggExp (Fin N) t + 1) /
          (aggExp (Fin N) t + 1))) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  set Z := capCell g L C 0 k c M
  set B := L - k * g - C 1
  have hZm : MeasurableSet Z := (boxTri_isClosed _ _ _).measurableSet
  have hagg : ∀ y : Fin N → ℝ, (aggR ∅ y, aggS ∅ y) = ((0 : ℝ), ∑ i, y i) := by
    intro y; simp [aggR, aggS]
  -- the slice `u₁ = 0` of the cell
  have hslice : ∀ s ∈ Set.Icc (0 : ℝ) M, Z.indicator
      (fun q => (endpointAgg g L C 0 k q.1 q.2) ^ m) (0, s) =
      (Set.Iic B).indicator (fun _ => C 1 ^ m) s := by
    intro s hs
    have hmem : ((0 : ℝ), s) ∈ Z ↔ s ∈ Set.Iic B := by
      rw [mem_capCell]
      simp only [tri, Set.mem_ofPred_eq, Set.mem_Iic, Nat.cast_zero, zero_add, one_mul]
      constructor
      · rintro ⟨-, -, -, h⟩; simpa [B] using h
      · intro h; exact ⟨⟨le_rfl, hs.1, by linarith [hs.2]⟩, hc, by linarith, by simpa [B] using h⟩
    by_cases h : s ∈ Set.Iic B
    · rw [Set.indicator_of_mem (hmem.mpr h), Set.indicator_of_mem h,
        endpointAgg_on_capCell g L C 0 k c M _ (hmem.mpr h)]
      simp
    · rw [Set.indicator_of_notMem (fun h' => h (hmem.mp h')), Set.indicator_of_notMem h]
  rw [piece_cap_eq]
  simp_rw [hagg]
  obtain ⟨Bd, hBd⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := M)).exists_bound_of_continuousOn
    (continuous_const : Continuous fun _ : ℝ => C 1 ^ m).continuousOn
  rw [one_group M t (fun s => Z.indicator (fun q => (endpointAgg g L C 0 k q.1 q.2) ^ m) (0, s))
    (((Continuous.measurable (by unfold endpointAgg; fun_prop) :
      Measurable fun q : ℝ × ℝ => (endpointAgg g L C 0 k q.1 q.2) ^ m).indicator
      hZm).comp (by fun_prop)) (|C 1 ^ m|) (fun s hs => by
        rw [hslice s hs]
        by_cases h : s ∈ Set.Iic B
        · rw [Set.indicator_of_mem h]
        · rw [Set.indicator_of_notMem h, abs_zero]; exact abs_nonneg _)]
  congr 1
  rw [setIntegral_congr_fun measurableSet_Icc (fun s hs => by
    rw [hslice s hs])]
  have hfun : (fun s => s ^ aggExp (Fin N) t * (Set.Iic B).indicator (fun _ => C 1 ^ m) s) =
      (Set.Iic B).indicator (fun s => C 1 ^ m * s ^ aggExp (Fin N) t) := by
    funext s; by_cases h : s ∈ Set.Iic B
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; ring
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  rw [hfun, setIntegral_indicator measurableSet_Iic,
    show Set.Icc (0 : ℝ) M ∩ Set.Iic B = Set.Icc 0 (min B (M - 0)) by
      ext s; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic, le_min_iff, sub_zero]
      tauto,
    integral_const_mul, inner_box]

/-! ## Table 3 -/

/-- At Table 3, `L − g ≤ τ` (`τ − (L − g) = 1/625`). -/
theorem tau_ge_table3 : BGP212.Params.L - BGP212.Params.g ≤ BGP212.Params.τ := by decide +kernel

/-- **Every Table 3 cap cell is a rectangle**: the piece total `τ − (r+k) g` never cuts it. -/
theorem capCell_rect_table3 (r k : ℕ) (c : ℝ) :
    min c (C3 (r + 1) - (r + 1) * g3) + (L3 - k * g3 - C3 (r + 1)) ≤ τ3 - (r + k) * g3 :=
  capCell_rect g3 L3 τ3 C3 r k c (by
    have := tau_ge_table3
    simp only [g3, L3, τ3]; exact_mod_cast this)

/-- **Empty Table 3 cap cells**: with one rough coordinate the cap branch is empty once
`k ≥ 7` (`L − 7 g = 751/1250 < C(2) = 794/1250`). -/
theorem capCell_empty_table3 (k : ℕ) (hk : 7 ≤ k) (c M : ℝ) : capCell g3 L3 C3 1 k c M = ∅ := by
  refine capCell_empty g3 L3 C3 1 k c M ?_
  have hC : BGP212.Params.C 2 = 794 / 1250 := by decide +kernel
  have hk' : (7 : ℝ) ≤ k := by exact_mod_cast hk
  simp only [g3, L3, C3, hC, BGP212.Params.g, BGP212.Params.L]
  push_cast
  nlinarith

/-- **The worked certificate**: the cap-branch part of `J_T(1)` on the Table 3 piece
`({0}, ∅)` of `T̂` (`N = 44`) is the explicit rational
`V = (L − C(2))⁴³ ((C(2) − g)³ − g³) / (3 · 43!) ≈ 1.0464 × 10⁻⁷⁰`. -/
theorem capPieceT3_value : capPieceT3 =
    ((2257149812841095726960561293190503471927130196106096204396001203694562350987314959143203078094677121622739446201 / 21569915559007524956605042855904290630373696306163850230268666519073406107054324820637702941894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  have hR : ({0} : Finset (Fin 44)).Nonempty := Finset.singleton_nonempty 0
  have hRc : ({0} : Finset (Fin 44))ᶜ.Nonempty := ⟨1, by decide⟩
  have key := cap_branch_piece {0} hR hRc g3 L3 C3 0 (C3 1 - g3) (τ3 - g3) (fun _ => 0) 2
  have hcard : ({0} : Finset (Fin 44)).card = 1 := rfl
  rw [hcard] at key
  simp only [pow_zero, Finset.prod_const_one, one_mul] at key
  rw [capPieceT3, key]
  have e1 : ∀ inst : Fintype {i // i ∈ ({0} : Finset (Fin 44))},
      @aggExp _ inst (fun _ => 0) = 0 := by
    intro inst; rw [Subsingleton.elim inst (Subtype.fintype _)]; decide
  have e2 : ∀ inst : Fintype {i // i ∉ ({0} : Finset (Fin 44))},
      @aggExp _ inst (fun _ => 0) = 42 := by
    intro inst; rw [Subsingleton.elim inst (Subtype.fintype _)]; decide
  have c1 : ∀ inst : Fintype {i // i ∈ ({0} : Finset (Fin 44))},
      @aggConstQ _ inst (fun _ => 0) = 1 := by
    intro inst; rw [Subsingleton.elim inst (Subtype.fintype _)]; decide +kernel
  have c2 : ∀ inst : Fintype {i // i ∉ ({0} : Finset (Fin 44))},
      @aggConstQ _ inst (fun _ => 0) = 1 / (Nat.factorial 42 : ℚ) := by
    intro inst; rw [Subsingleton.elim inst (Subtype.fintype _)]; decide +kernel
  rw [e1, e2, aggConst_eq_cast, aggConst_eq_cast, c1, c2]
  have hq : capPowVal (min (BGP212.Params.C 1 - BGP212.Params.g)
      (BGP212.Params.C (1 + 1) - ((1 : ℕ) + 1) * BGP212.Params.g))
      (BGP212.Params.L - (0 : ℕ) * BGP212.Params.g - BGP212.Params.C (1 + 1))
      (BGP212.Params.τ - BGP212.Params.g) (BGP212.Params.C (1 + 1) - (1 : ℕ) * BGP212.Params.g)
      0 42 2 = (4535855578938127061125476602777163187372821390110619208482296371527927786449988572669541167369031308548379262320291035943043 / 30850986990575172633456830505710793546266246912353371231003615338117640476411907002329826354980468750000000000000000000000000000000000000000000 : ℚ) := by
    decide +kernel
  have hc := capPowVal_cast (min (BGP212.Params.C 1 - BGP212.Params.g)
      (BGP212.Params.C (1 + 1) - ((1 : ℕ) + 1) * BGP212.Params.g))
      (BGP212.Params.L - (0 : ℕ) * BGP212.Params.g - BGP212.Params.C (1 + 1))
      (BGP212.Params.τ - BGP212.Params.g) (BGP212.Params.C (1 + 1) - (1 : ℕ) * BGP212.Params.g)
      0 42 2
  rw [hq] at hc
  push_cast [Rat.cast_min] at hc
  simp only [g3, L3, τ3, C3]
  push_cast
  rw [← hc]
  norm_num [Nat.factorial]

end BGP212.V2e

/-! ## Comparator wrappers -/

namespace BGP212.Challenge

open BGP212.Gram BGP212.V2d BGP212.V2e MeasureTheory

theorem boxTri_integral (A B D : ℝ) (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
    ∫ q in boxTri A B D, f q =
      ∫ u in Set.Icc 0 A, ∫ s in Set.Icc 0 (min B (D - u)), f (u, s) := by
  apply BGP212.V2e.boxTri_integral <;> assumption

theorem box_monomial (A B D : ℝ) (α β : ℕ) :
    ∫ q in boxTri A B D, q.1 ^ α * q.2 ^ β = boxVal A B D α β := by
  apply BGP212.V2e.box_monomial <;> assumption

theorem boxVal_cast (A B D : ℚ) (α β : ℕ) :
    ((boxVal A B D α β : ℚ) : ℝ) = boxVal (A : ℝ) (B : ℝ) (D : ℝ) α β := by
  apply BGP212.V2e.boxVal_cast <;> assumption

theorem boxVal_empty (A B D : ℝ) (α β : ℕ) (h : A < 0 ∨ B < 0) : boxVal A B D α β = 0 := by
  apply BGP212.V2e.boxVal_empty <;> assumption

theorem boxVal_nonpos (A B D : ℝ) (α β : ℕ) (hD : D ≤ 0) : boxVal A B D α β = 0 := by
  apply BGP212.V2e.boxVal_nonpos <;> assumption

theorem boxVal_rect (A B D : ℝ) (α β : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : A + B ≤ D) :
    boxVal A B D α β = A ^ (α + 1) / (α + 1) * (B ^ (β + 1) / (β + 1)) := by
  apply BGP212.V2e.boxVal_rect <;> assumption

theorem box_capPow (A B D a : ℝ) (α β m : ℕ) :
    ∫ q in boxTri A B D, q.1 ^ α * q.2 ^ β * (a - q.1) ^ m = capPowVal A B D a α β m := by
  apply BGP212.V2e.box_capPow <;> assumption

theorem box_poly (A B D : ℝ) (P : MvPolynomial (Fin 2) ℚ) :
    ∫ q in boxTri A B D, MvPolynomial.eval₂ (algebraMap ℚ ℝ) ![q.1, q.2] P =
      ∑ d ∈ P.support, ((P.coeff d : ℚ) : ℝ) * boxVal A B D (d 0) (d 1) := by
  apply BGP212.V2e.box_poly <;> assumption

theorem endpointAgg_cap (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (u₁ u₂ : ℝ) (h₁ : u₁ ≤ C (r + 1) - (r + 1) * g) (h₂ : u₂ ≤ L - k * g - C (r + 1)) :
    endpointAgg g L C r k u₁ u₂ = C (r + 1) - (r * g + u₁) := by
  apply BGP212.V2e.endpointAgg_cap <;> assumption

theorem endpointAgg_gBranch (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (u₁ u₂ : ℝ) (h₁ : C (r + 1) - (r + 1) * g ≤ u₁)
    (h₂ : u₁ + u₂ ≤ L - (r + k + 1) * g) : endpointAgg g L C r k u₁ u₂ = g := by
  apply BGP212.V2e.endpointAgg_gBranch <;> assumption

theorem endpointAgg_LBranch_cap (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (u₁ u₂ : ℝ) (h₁ : u₁ ≤ C (r + 1) - (r + 1) * g)
    (h₂ : L - k * g - C (r + 1) ≤ u₂) :
    endpointAgg g L C r k u₁ u₂ = L - ((r + k) * g + u₁ + u₂) := by
  apply BGP212.V2e.endpointAgg_LBranch_cap <;> assumption

theorem endpointAgg_LBranch_g (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (u₁ u₂ : ℝ) (h₁ : C (r + 1) - (r + 1) * g ≤ u₁)
    (h₂ : L - (r + k + 1) * g ≤ u₁ + u₂) :
    endpointAgg g L C r k u₁ u₂ = L - ((r + k) * g + u₁ + u₂) := by
  apply BGP212.V2e.endpointAgg_LBranch_g <;> assumption

theorem cap_total_le (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (u₁ u₂ : ℝ) (h₁ : u₁ ≤ C (r + 1) - (r + 1) * g) (h₂ : u₂ ≤ L - k * g - C (r + 1)) :
    (r + k) * g + u₁ + u₂ ≤ L - g := by
  apply BGP212.V2e.cap_total_le <;> assumption

theorem mem_capCell (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ) (q : ℝ × ℝ) :
    q ∈ capCell g L C r k c M ↔ q ∈ tri M ∧ q.1 ≤ c ∧ q.1 ≤ C (r + 1) - (r + 1) * g ∧
      q.2 ≤ L - k * g - C (r + 1) := by
  apply BGP212.V2e.mem_capCell <;> assumption

theorem endpointAgg_on_capCell (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ) (q : ℝ × ℝ)
    (hq : q ∈ capCell g L C r k c M) :
    endpointAgg g L C r k q.1 q.2 = C (r + 1) - (r * g + q.1) := by
  apply BGP212.V2e.endpointAgg_on_capCell <;> assumption

theorem capCell_rect (g L τ : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c : ℝ) (hτ : L - g ≤ τ) :
    min c (C (r + 1) - (r + 1) * g) + (L - k * g - C (r + 1)) ≤ τ - (r + k) * g := by
  apply BGP212.V2e.capCell_rect <;> assumption

theorem capCell_empty (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ) (h : L - k * g < C (r + 1)) :
    capCell g L C r k c M = ∅ := by
  apply BGP212.V2e.capCell_empty <;> assumption

theorem cap_inner (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ) (q : ℝ × ℝ)
    (hq : q ∈ capCell g L C r k c M) (p t : ℕ) :
    ∫ u in (0 : ℝ)..endpointAgg g L C r k q.1 q.2, (L - ((r + k) * g + q.1 + q.2) - u) ^ p * u ^ t =
      innerVal (C (r + 1) - (r * g + q.1)) (L - ((r + k) * g + q.1 + q.2)) p t := by
  apply BGP212.V2e.cap_inner <;> assumption

theorem piece_cap_eq {N : ℕ} (R : Finset (Fin N)) (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ)
    (G : (Fin N → ℝ) → ℝ) (Φ : ℝ × ℝ → ℝ) :
    ∫ y in pieceSet N R c M, G y * (capCell g L C r k c M).indicator Φ (aggR R y, aggS R y) =
      ∫ y in simplexF (Fin N) M, G y * (capCell g L C r k c M).indicator Φ (aggR R y, aggS R y) := by
  apply BGP212.V2e.piece_cap_eq <;> assumption

theorem cap_branch_piece {N : ℕ} (R : Finset (Fin N)) (hR : R.Nonempty) (hRc : Rᶜ.Nonempty)
    (g L : ℝ) (C : ℕ → ℝ) (k : ℕ) (c M : ℝ) (t : Fin N → ℕ) (m : ℕ) :
    ∫ y in pieceSet N R c M, (∏ i, y i ^ t i) *
        (capCell g L C R.card k c M).indicator
          (fun q => (endpointAgg g L C R.card k q.1 q.2) ^ m) (aggR R y, aggS R y) =
      aggConst {i // i ∈ R} (fun i => t i) * aggConst {i // i ∉ R} (fun i => t i) *
        capPowVal (min c (C (R.card + 1) - (R.card + 1) * g)) (L - k * g - C (R.card + 1)) M
          (C (R.card + 1) - R.card * g) (aggExp {i // i ∈ R} (fun i => t i))
          (aggExp {i // i ∉ R} (fun i => t i)) m := by
  apply BGP212.V2e.cap_branch_piece <;> assumption

theorem cap_branch_r0 {N : ℕ} (hN : 0 < N) (g L : ℝ) (C : ℕ → ℝ) (k : ℕ) (c M : ℝ)
    (t : Fin N → ℕ) (m : ℕ) (hc : 0 ≤ c) (hc₁ : 0 ≤ C 1 - g) :
    ∫ y in pieceSet N ∅ c M, (∏ i, y i ^ t i) *
        (capCell g L C 0 k c M).indicator
          (fun q => (endpointAgg g L C 0 k q.1 q.2) ^ m) (aggR ∅ y, aggS ∅ y) =
      aggConst (Fin N) t * (C 1 ^ m *
        ((max 0 (min (L - k * g - C 1) (M - 0))) ^ (aggExp (Fin N) t + 1) /
          (aggExp (Fin N) t + 1))) := by
  apply BGP212.V2e.cap_branch_r0 <;> assumption

theorem tau_ge_table3 : BGP212.Params.L - BGP212.Params.g ≤ BGP212.Params.τ := by
  apply BGP212.V2e.tau_ge_table3 <;> assumption

theorem capCell_rect_table3 (r k : ℕ) (c : ℝ) :
    min c (C3 (r + 1) - (r + 1) * g3) + (L3 - k * g3 - C3 (r + 1)) ≤ τ3 - (r + k) * g3 := by
  apply BGP212.V2e.capCell_rect_table3 <;> assumption

theorem capCell_empty_table3 (k : ℕ) (hk : 7 ≤ k) (c M : ℝ) : capCell g3 L3 C3 1 k c M = ∅ := by
  apply BGP212.V2e.capCell_empty_table3 <;> assumption

theorem capPieceT3_value : capPieceT3 =
    ((2257149812841095726960561293190503471927130196106096204396001203694562350987314959143203078094677121622739446201 / 21569915559007524956605042855904290630373696306163850230268666519073406107054324820637702941894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  apply BGP212.V2e.capPieceT3_value <;> assumption

end BGP212.Challenge
