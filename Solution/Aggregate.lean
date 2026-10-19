/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): §9.4, Lemma 9.2 (p. 41), (10.1), Proposition 10.2 (pp. 41–42).
-/
import BGP212.Aggregate
import Solution.Fibre

/-! # V2e-A: two-aggregate Dirichlet integration (proofs)

PROVED INTEGRAL IDENTITIES (no kernel arithmetic beyond the example's small constants).

1. `core_integral`: on `(κ → ℝ) × ℝ`, the shear `(w, x) ↦ (w, Σ w + x)` (`shear`, measure
   preserving by `MeasurePreserving.skew_product`), Fubini with the aggregate `s` outside
   (`integral_prod_symm`), and V2b's weighted simplex moment `weighted_simplexF` on each slice.
2. `one_group`: any nonempty group, by splitting off one coordinate
   (`volume_preserving_piEquivPiSubtypeProd`, `volume_preserving_funUnique`).
3. `two_group`: Fubini over the two groups (`integral_prod`), `one_group` for the inner group
   with `h(Σ z, ·)`, then for the outer group with the parametric inner integral `innerAgg`
   (measurable by `StronglyMeasurable.integral_prod_right'`, bounded by
   `norm_setIntegral_le_of_norm_le_const`), and Fubini on the triangle (`tri_integral`).
4. `two_group_fin`: the rough/smooth split `y ↦ (y|_R, y|_{Rᶜ})` of V2b (`split_sums`).
5. Boundary cases: `one_group_empty`, `two_group_right_empty`, `two_group_left_empty`,
   `two_group_both_empty` (Dirac measure on an empty product), `aggConst_zero`, `tri_eq_empty`,
   `quad_eq_empty`.
6. Rational specializations: the triangle is V1's 2-simplex (`tri_eq_simplex`,
   `volume_preserving_finTwoArrow`), so `tri_monomial` and `tri_poly` are V1's (10.1) and Lemma
   10.1; `two_group_poly` (rational value), `two_group_const` (consistency with (10.1)).
7. Link to V2d: `aggR_shift`, `aggS_shift`, `endpoint_eq_stratum`, `stratumEndpoint_shift`.
8. A branch-type cut `tri_cut` (via V2d's `inner_integral`) and the worked example
   `example_value`. -/

namespace BGP212.V2e

open BGP212.Gram BGP212.V2d MeasureTheory

/-! ## Integrability of bounded integrands on compact sets -/

theorem integrableOn_cont_mul {X : Type*} [MeasureSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [IsFiniteMeasureOnCompacts (volume : Measure X)]
    {S : Set X} (hS : IsCompact S) (hSm : MeasurableSet S) {P k : X → ℝ} (hP : Continuous P)
    (hk : Measurable k) {B : ℝ} (hb : ∀ x ∈ S, |k x| ≤ B) :
    IntegrableOn (fun x => P x * k x) S := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hP.continuousOn
  refine Measure.integrableOn_of_bounded (M := C * B) hS.measure_lt_top.ne
    (hP.measurable.mul hk).aestronglyMeasurable ?_
  refine (ae_restrict_iff' hSm).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  rw [norm_mul]
  have h1 := hC x hx
  have h2 : ‖k x‖ ≤ B := by rw [Real.norm_eq_abs]; exact hb x hx
  exact mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)

/-! ## The shear `(w, s) ↦ (w, s − Σ w)` -/

variable (κ : Type*) [Fintype κ]

/-- The shear on `(κ → ℝ) × ℝ`. -/
def shear : ((κ → ℝ) × ℝ) ≃ᵐ ((κ → ℝ) × ℝ) where
  toFun q := (q.1, q.2 - ∑ i, q.1 i)
  invFun p := (p.1, p.2 + ∑ i, p.1 i)
  left_inv q := by simp
  right_inv p := by simp
  measurable_toFun := show Measurable (fun q : (κ → ℝ) × ℝ => (q.1, q.2 - ∑ i, q.1 i)) from by
    fun_prop
  measurable_invFun := show Measurable (fun p : (κ → ℝ) × ℝ => (p.1, p.2 + ∑ i, p.1 i)) from by
    fun_prop

theorem shear_measurePreserving : MeasurePreserving (shear κ) volume volume := by
  have h := MeasurePreserving.skew_product (μa := (volume : Measure (κ → ℝ)))
    (μc := (volume : Measure ℝ)) (μd := (volume : Measure ℝ)) (MeasurePreserving.id volume)
    (g := fun w s => s - ∑ i, w i) (by fun_prop)
    (Filter.Eventually.of_forall fun w => by
      simp only [sub_eq_add_neg]
      exact map_add_right_eq_self volume _)
  exact h

/-- The region `{(w, x) : w ≥ 0, x ≥ 0, Σ w + x ≤ R}`. -/
def coreSet (R : ℝ) : Set ((κ → ℝ) × ℝ) :=
  {p | (∀ i, 0 ≤ p.1 i) ∧ 0 ≤ p.2 ∧ ∑ i, p.1 i + p.2 ≤ R}

theorem coreSet_isClosed (R : ℝ) : IsClosed (coreSet κ R) := by
  have h1 : IsClosed {p : (κ → ℝ) × ℝ | ∀ i, 0 ≤ p.1 i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const
      ((continuous_apply i).comp continuous_fst)
  have h2 : IsClosed {p : (κ → ℝ) × ℝ | 0 ≤ p.2} := isClosed_le continuous_const continuous_snd
  have h3 : IsClosed {p : (κ → ℝ) × ℝ | ∑ i, p.1 i + p.2 ≤ R} :=
    isClosed_le (by fun_prop) continuous_const
  have : coreSet κ R = {p | ∀ i, 0 ≤ p.1 i} ∩ ({p | 0 ≤ p.2} ∩ {p | ∑ i, p.1 i + p.2 ≤ R}) := by
    ext p; simp [coreSet]
  rw [this]; exact h1.inter (h2.inter h3)

theorem coreSet_isCompact (R : ℝ) : IsCompact (coreSet κ R) := by
  refine (isCompact_Icc (a := ((0 : κ → ℝ), (0 : ℝ))) (b := (fun _ => |R|, |R|))).of_isClosed_subset
    (coreSet_isClosed κ R) ?_
  rintro ⟨w, x⟩ ⟨hw, hx, hs⟩
  have hsum : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => hw i
  refine ⟨⟨fun i => hw i, hx⟩, ⟨fun i => ?_, ?_⟩⟩
  · have : w i ≤ ∑ j, w j := Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
    show w i ≤ |R|
    linarith [le_abs_self R]
  · show x ≤ |R|
    linarith [le_abs_self R]

/-- **Core lemma** (one aggregate, one coordinate split off): for `h` measurable and bounded on
`[0, R]`, `∫_{w ≥ 0, x ≥ 0, Σ w + x ≤ R} wᵉ x^f h(Σ w + x) = ∏ eᵢ! f! / m! · ∫₀^R s^m h(s)`,
`m = |κ| + Σ e + f`. Proof: the shear `s = Σ w + x` (`shear_measurePreserving`), Fubini with `s`
outside, and V2b's weighted simplex moment `weighted_simplexF` on each slice. -/
theorem core_integral (R : ℝ) (e : κ → ℕ) (f : ℕ) (h : ℝ → ℝ) (hm : Measurable h) (B : ℝ)
    (hb : ∀ s ∈ Set.Icc 0 R, |h s| ≤ B) :
    ∫ p in coreSet κ R, (∏ i, p.1 i ^ e i) * p.2 ^ f * h (∑ i, p.1 i + p.2) =
      (∏ i, ((e i).factorial : ℝ)) * (f.factorial : ℝ) /
          ((Fintype.card κ + ∑ i, e i + f).factorial : ℝ) *
        ∫ s in Set.Icc 0 R, s ^ (Fintype.card κ + ∑ i, e i + f) * h s := by
  set m := Fintype.card κ + ∑ i, e i + f
  set K := (∏ i, ((e i).factorial : ℝ)) * (f.factorial : ℝ) / (m.factorial : ℝ)
  set G : (κ → ℝ) × ℝ → ℝ := fun p => (∏ i, p.1 i ^ e i) * p.2 ^ f * h (∑ i, p.1 i + p.2)
  have hmeasE := (coreSet_isClosed κ R).measurableSet
  -- integrability of the original integrand
  have hint : Integrable ((coreSet κ R).indicator G) := by
    rw [integrable_indicator_iff hmeasE]
    refine integrableOn_cont_mul (coreSet_isCompact κ R) hmeasE (by fun_prop)
      (hm.comp (by fun_prop)) (B := B) ?_
    rintro ⟨w, x⟩ ⟨hw, hx, hs⟩
    exact hb _ ⟨by linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hw i], hs⟩
  -- the sheared integrand
  set E' : Set ((κ → ℝ) × ℝ) := {q | q.1 ∈ simplexF κ q.2 ∧ q.2 ≤ R}
  set G' : (κ → ℝ) × ℝ → ℝ := fun q => (∏ i, q.1 i ^ e i) * (q.2 - ∑ i, q.1 i) ^ f * h q.2
  have hshear : ∀ q, (coreSet κ R).indicator G (shear κ q) = E'.indicator G' q := by
    rintro ⟨w, s⟩
    have hmem : shear κ (w, s) ∈ coreSet κ R ↔ (w, s) ∈ E' := by
      simp only [shear, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, coreSet, Set.mem_ofPred_eq, E',
        simplexF]
      constructor
      · rintro ⟨hw, hx, hs⟩; exact ⟨⟨hw, by linarith⟩, by linarith⟩
      · rintro ⟨⟨hw, hx⟩, hs⟩; exact ⟨hw, by linarith, by linarith⟩
    by_cases hq : (w, s) ∈ E'
    · rw [Set.indicator_of_mem (hmem.mpr hq), Set.indicator_of_mem hq]
      simp only [G, G', shear, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
      congr 2; ring
    · rw [Set.indicator_of_notMem (fun h' => hq (hmem.mp h')), Set.indicator_of_notMem hq]
  have hint' : Integrable (E'.indicator G') (volume.prod volume) := by
    have := ((shear_measurePreserving κ).integrable_comp_emb
      (shear κ).measurableEmbedding).mpr hint
    have heq : (coreSet κ R).indicator G ∘ ⇑(shear κ) = E'.indicator G' := funext hshear
    rwa [heq] at this
  -- slices
  have hslice : ∀ s : ℝ, ∫ w, E'.indicator G' (w, s) =
      (Set.Icc 0 R).indicator (fun s => K * (s ^ m * h s)) s := by
    intro s
    by_cases hs : 0 ≤ s ∧ s ≤ R
    · rw [Set.indicator_of_mem (show s ∈ Set.Icc 0 R from hs)]
      have hfun : (fun w => E'.indicator G' (w, s)) =
          (simplexF κ s).indicator (fun w => ((∏ i, w i ^ e i) * (s - ∑ i, w i) ^ f) * h s) := by
        funext w
        by_cases hw : w ∈ simplexF κ s
        · rw [Set.indicator_of_mem (show (w, s) ∈ E' from ⟨hw, hs.2⟩), Set.indicator_of_mem hw]
        · rw [Set.indicator_of_notMem (fun h' => hw h'.1), Set.indicator_of_notMem hw]
      rw [hfun, integral_indicator (simplexF_measurableSet s), integral_mul_const,
        weighted_simplexF s hs.1 e f]
      simp only [K, m]
      ring
    · rw [Set.indicator_of_notMem (show s ∉ Set.Icc 0 R from hs)]
      have hfun : (fun w => E'.indicator G' (w, s)) = fun _ => 0 := by
        funext w
        refine Set.indicator_of_notMem ?_ _
        rintro ⟨⟨hw, hws⟩, hsR⟩
        exact hs ⟨le_trans (Finset.sum_nonneg fun i _ => hw i) hws, hsR⟩
      rw [hfun, integral_zero]
  have hcomp := (shear_measurePreserving κ).integral_comp' ((coreSet κ R).indicator G)
  rw [← integral_indicator hmeasE, ← hcomp]
  simp_rw [hshear]
  rw [show (volume : Measure ((κ → ℝ) × ℝ)) = volume.prod volume from rfl,
    integral_prod_symm _ hint']
  simp_rw [hslice]
  rw [integral_indicator measurableSet_Icc, ← integral_const_mul]

/-! ## One aggregate over any nonempty group -/

section OneGroup

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

instance uniqueEq (i₀ : ι) : Unique {i // ¬ i ≠ i₀} where
  default := ⟨i₀, by simp⟩
  uniq := fun ⟨j, hj⟩ => by simp only [ne_eq, not_not] at hj; subst hj; rfl

/-- Split off the coordinate `i₀`: `(ι → ℝ) ≃ ({i // i ≠ i₀} → ℝ) × ℝ`, measure preserving. -/
def splitOff (i₀ : ι) : ((ι → ℝ)) ≃ᵐ (({i // i ≠ i₀} → ℝ) × ℝ) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (· ≠ i₀)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.funUnique {i // ¬ i ≠ i₀} ℝ))

theorem splitOff_measurePreserving (i₀ : ι) :
    MeasurePreserving (splitOff i₀) volume volume := by
  have h1 := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℝ) (· ≠ i₀)
  have hu := volume_preserving_funUnique {i // ¬ i ≠ i₀} ℝ
  rw [show (Unique.fintype : Fintype {i // ¬ i ≠ i₀}) = Subtype.fintype _ from
    Subsingleton.elim _ _] at hu
  have h2 := (MeasurePreserving.id (volume : Measure ({i // i ≠ i₀} → ℝ))).prod hu
  have h1' : MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (· ≠ i₀))
      volume ((volume : Measure ({i // i ≠ i₀} → ℝ)).prod
        (volume : Measure ({i // ¬ i ≠ i₀} → ℝ))) := h1
  exact h2.comp h1'

theorem splitOff_symm_apply (i₀ : ι) (w : {i // i ≠ i₀} → ℝ) (x : ℝ) :
    (splitOff i₀).symm (w, x) = fun i => if hi : i ≠ i₀ then w ⟨i, hi⟩ else x := by
  funext i
  by_cases hi : i ≠ i₀
  · simp [splitOff, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply, hi,
      MeasurableEquiv.prodCongr, Equiv.prodCongr]
  · simp [splitOff, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply, hi,
      MeasurableEquiv.prodCongr, Equiv.prodCongr, MeasurableEquiv.funUnique,
      MeasurableEquiv.piUnique, Equiv.piUnique]

theorem sum_splitOff (i₀ : ι) (f : ι → ℝ) :
    ∑ i, f i = ∑ i : {i // i ≠ i₀}, f i + f i₀ := by
  have h1 := Fintype.sum_subtype_add_sum_subtype (fun i => i ≠ i₀) f
  have h2 : ∑ i : {i // ¬ i ≠ i₀}, f i = f i₀ := by
    rw [Fintype.sum_unique (fun i : {i // ¬ i ≠ i₀} => f i)]; rfl
  rw [← h1, h2]

theorem prod_splitOff (i₀ : ι) (f : ι → ℝ) :
    ∏ i, f i = (∏ i : {i // i ≠ i₀}, f i) * f i₀ := by
  have h1 := Fintype.prod_subtype_mul_prod_subtype (fun i => i ≠ i₀) f
  have h2 : ∏ i : {i // ¬ i ≠ i₀}, f i = f i₀ := by
    rw [Fintype.prod_unique (fun i : {i // ¬ i ≠ i₀} => f i)]; rfl
  rw [← h1, h2]

theorem sum_splitOff_nat (i₀ : ι) (f : ι → ℕ) :
    ∑ i, f i = ∑ i : {i // i ≠ i₀}, f i + f i₀ := by
  have h1 := Fintype.sum_subtype_add_sum_subtype (fun i => i ≠ i₀) f
  have h2 : ∑ i : {i // ¬ i ≠ i₀}, f i = f i₀ := by
    rw [Fintype.sum_unique (fun i : {i // ¬ i ≠ i₀} => f i)]; rfl
  rw [← h1, h2]

theorem card_splitOff (i₀ : ι) : Fintype.card {i // i ≠ i₀} + 1 = Fintype.card ι := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i₀⟩
  omega

/-- **One-aggregate Dirichlet integration.** For a nonempty group `ι`, an exponent vector `e`,
and `h` measurable and bounded on `[0, R]`:
`∫_{z ≥ 0, Σ z ≤ R} zᵉ h(Σ z) dz = aggConst ι e · ∫_{[0, R]} s^{aggExp ι e} h(s) ds`. -/
theorem one_group [Nonempty ι] (R : ℝ) (e : ι → ℕ) (h : ℝ → ℝ) (hm : Measurable h) (B : ℝ)
    (hb : ∀ s ∈ Set.Icc 0 R, |h s| ≤ B) :
    ∫ z in simplexF ι R, (∏ i, z i ^ e i) * h (∑ i, z i) =
      aggConst ι e * ∫ s in Set.Icc 0 R, s ^ aggExp ι e * h s := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hT := (splitOff_measurePreserving i₀).symm
  rw [← integral_indicator (simplexF_measurableSet R), ← hT.integral_comp']
  have hfun : ∀ q : ({i // i ≠ i₀} → ℝ) × ℝ, (simplexF ι R).indicator
      (fun z => (∏ i, z i ^ e i) * h (∑ i, z i)) ((splitOff i₀).symm q) =
      (coreSet {i // i ≠ i₀} R).indicator (fun p => (∏ i, p.1 i ^ e i) * p.2 ^ e i₀ * h (∑ i, p.1 i + p.2)) q := by
    rintro ⟨w, x⟩
    rw [splitOff_symm_apply]
    have hs : ∑ i, (fun i => if hi : i ≠ i₀ then w ⟨i, hi⟩ else x) i = ∑ i, w i + x := by
      rw [sum_splitOff i₀]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by simp [j.2]
      · simp
    have hp : ∏ i, (fun i => if hi : i ≠ i₀ then w ⟨i, hi⟩ else x) i ^ e i =
        (∏ i, w i ^ e i) * x ^ e i₀ := by
      rw [prod_splitOff i₀ (fun i => (fun i => if hi : i ≠ i₀ then w ⟨i, hi⟩ else x) i ^ e i)]
      congr 1
      · exact Finset.prod_congr rfl fun j _ => by simp [j.2]
      · simp
    have hmem : (fun i => if hi : i ≠ i₀ then w ⟨i, hi⟩ else x) ∈ simplexF ι R ↔
        (w, x) ∈ coreSet {i // i ≠ i₀} R := by
      simp only [simplexF, coreSet, Set.mem_ofPred_eq]
      rw [hs]
      constructor
      · rintro ⟨h0, hR⟩
        refine ⟨fun i => ?_, ?_, hR⟩
        · have := h0 i; simpa [i.2] using this
        · have := h0 i₀; simpa using this
      · rintro ⟨hw, hx, hR⟩
        refine ⟨fun i => ?_, hR⟩
        by_cases hi : i ≠ i₀
        · simpa [hi] using hw ⟨i, hi⟩
        · simpa [hi] using hx
    by_cases hq : (w, x) ∈ coreSet {i // i ≠ i₀} R
    · rw [Set.indicator_of_mem (hmem.mpr hq), Set.indicator_of_mem hq, hs, hp]
    · rw [Set.indicator_of_notMem (fun h' => hq (hmem.mp h')), Set.indicator_of_notMem hq]
  simp_rw [hfun]
  rw [integral_indicator (coreSet_isClosed {i // i ≠ i₀} R).measurableSet,
    core_integral {i // i ≠ i₀} R (fun i => e i) (e i₀) h hm B hb]
  have hexp : Fintype.card {i // i ≠ i₀} + ∑ i : {i // i ≠ i₀}, e i + e i₀ = aggExp ι e := by
    rw [aggExp, sum_splitOff_nat i₀ e, ← card_splitOff i₀]; omega
  have hfac : (∏ i : {i // i ≠ i₀}, ((e i).factorial : ℝ)) * ((e i₀).factorial : ℝ) =
      ∏ i, ((e i).factorial : ℝ) := (prod_splitOff i₀ (fun i => ((e i).factorial : ℝ))).symm
  rw [hexp, hfac, aggConst]

end OneGroup

/-! ## Two aggregates -/

section TwoGroup

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
theorem quad_isClosed (R : ℝ) : IsClosed (quad I J R) := by
  have h1 : IsClosed {p : (I → ℝ) × (J → ℝ) | ∀ i, 0 ≤ p.1 i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const
      ((continuous_apply i).comp continuous_fst)
  have h2 : IsClosed {p : (I → ℝ) × (J → ℝ) | ∀ j, 0 ≤ p.2 j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const
      ((continuous_apply j).comp continuous_snd)
  have h3 : IsClosed {p : (I → ℝ) × (J → ℝ) | ∑ i, p.1 i + ∑ j, p.2 j ≤ R} :=
    isClosed_le (by fun_prop) continuous_const
  have : quad I J R = {p | ∀ i, 0 ≤ p.1 i} ∩ ({p | ∀ j, 0 ≤ p.2 j} ∩
      {p | ∑ i, p.1 i + ∑ j, p.2 j ≤ R}) := by
    ext p; simp [quad]
  rw [this]; exact h1.inter (h2.inter h3)

omit [DecidableEq I] [DecidableEq J] in
theorem quad_isCompact (R : ℝ) : IsCompact (quad I J R) := by
  refine (isCompact_Icc (a := ((0 : I → ℝ), (0 : J → ℝ)))
    (b := (fun _ => |R|, fun _ => |R|))).of_isClosed_subset (quad_isClosed R) ?_
  rintro ⟨z, w⟩ ⟨hz, hw, hs⟩
  have hz' : 0 ≤ ∑ i, z i := Finset.sum_nonneg fun i _ => hz i
  have hw' : 0 ≤ ∑ j, w j := Finset.sum_nonneg fun j _ => hw j
  refine ⟨⟨fun i => hz i, fun j => hw j⟩, ⟨fun i => ?_, fun j => ?_⟩⟩
  · have : z i ≤ ∑ k, z k := Finset.single_le_sum (fun k _ => hz k) (Finset.mem_univ i)
    show z i ≤ |R|
    linarith [le_abs_self R]
  · have : w j ≤ ∑ k, w k := Finset.single_le_sum (fun k _ => hw k) (Finset.mem_univ j)
    show w j ≤ |R|
    linarith [le_abs_self R]

theorem tri_isClosed (R : ℝ) : IsClosed (tri R) := by
  have : tri R = {q : ℝ × ℝ | 0 ≤ q.1} ∩ ({q | 0 ≤ q.2} ∩ {q | q.1 + q.2 ≤ R}) := by
    ext q; simp [tri]
  rw [this]
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter (isClosed_le (by fun_prop) continuous_const))

theorem tri_isCompact (R : ℝ) : IsCompact (tri R) := by
  refine (isCompact_Icc (a := ((0 : ℝ), (0 : ℝ))) (b := (|R|, |R|))).of_isClosed_subset
    (tri_isClosed R) ?_
  rintro ⟨u, s⟩ ⟨hu, hs, hR⟩
  exact ⟨⟨hu, hs⟩, ⟨show u ≤ |R| by linarith [le_abs_self R], show s ≤ |R| by linarith [le_abs_self R]⟩⟩

/-- The inner aggregate integral `u ↦ ∫_{[0, R − u]} s^k h(u, s) ds`. -/
noncomputable def innerAgg (R : ℝ) (k : ℕ) (h : ℝ × ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ s in Set.Icc 0 (R - u), s ^ k * h (u, s)

theorem innerAgg_eq (R : ℝ) (k : ℕ) (h : ℝ × ℝ → ℝ) (u : ℝ) :
    innerAgg R k h u =
      ∫ s, {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ R - q.1}.indicator (fun q => q.2 ^ k * h q) (u, s) := by
  rw [innerAgg, ← integral_indicator measurableSet_Icc]
  rfl

theorem innerAgg_measurable (R : ℝ) (k : ℕ) (h : ℝ × ℝ → ℝ) (hm : Measurable h) :
    Measurable (innerAgg R k h) := by
  have hset : MeasurableSet {q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ R - q.1} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_const.sub measurable_fst))
  have hsm : StronglyMeasurable ({q : ℝ × ℝ | 0 ≤ q.2 ∧ q.2 ≤ R - q.1}.indicator
      (fun q => q.2 ^ k * h q)) :=
    (((by fun_prop : Measurable fun q : ℝ × ℝ => q.2 ^ k).mul hm).indicator hset).stronglyMeasurable
  have := (hsm.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  convert this using 1
  funext u
  exact innerAgg_eq R k h u

theorem innerAgg_bound (R : ℝ) (k : ℕ) (h : ℝ × ℝ → ℝ) (B : ℝ) (hb : ∀ q ∈ tri R, |h q| ≤ B) :
    ∀ u ∈ Set.Icc 0 R, |innerAgg R k h u| ≤ |R| ^ k * |B| * |R| := by
  intro u hu
  rw [← Real.norm_eq_abs, innerAgg]
  refine le_trans (norm_setIntegral_le_of_norm_le_const (C := |R| ^ k * |B|) measure_Icc_lt_top
    fun s hs => ?_) ?_
  · rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |s| ^ k ≤ |R| ^ k := pow_le_pow_left₀ (abs_nonneg s)
      (by rw [abs_of_nonneg hs.1]; linarith [le_abs_self R, hs.2, hu.1]) k
    have h2 : |h (u, s)| ≤ |B| := le_trans (hb _ ⟨hu.1, hs.1, by linarith [hs.2]⟩) (le_abs_self B)
    exact mul_le_mul h1 h2 (abs_nonneg _) (pow_nonneg (abs_nonneg _) _)
  · rw [Real.volume_real_Icc_of_le (by linarith [hu.2])]
    exact mul_le_mul_of_nonneg_left (by linarith [le_abs_self R, hu.1])
      (mul_nonneg (pow_nonneg (abs_nonneg _) _) (abs_nonneg _))

/-- The triangle integral as an iterated integral, aggregate `u₁` outside. -/
theorem tri_integral (R : ℝ) (k₁ k₂ : ℕ) (h : ℝ × ℝ → ℝ) (hm : Measurable h) (B : ℝ)
    (hb : ∀ q ∈ tri R, |h q| ≤ B) :
    ∫ q in tri R, q.1 ^ k₁ * q.2 ^ k₂ * h q =
      ∫ u in Set.Icc 0 R, u ^ k₁ * innerAgg R k₂ h u := by
  have hTm := (tri_isClosed R).measurableSet
  have hint : Integrable ((tri R).indicator fun q : ℝ × ℝ => q.1 ^ k₁ * q.2 ^ k₂ * h q)
      (volume.prod volume) := by
    rw [integrable_indicator_iff hTm]
    exact integrableOn_cont_mul (tri_isCompact R) hTm (P := fun q : ℝ × ℝ => q.1 ^ k₁ * q.2 ^ k₂)
      (by fun_prop) hm hb
  rw [← integral_indicator hTm, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    integral_prod _ hint, ← integral_indicator measurableSet_Icc]
  congr 1
  funext u
  by_cases hu : u ∈ Set.Icc 0 R
  · rw [Set.indicator_of_mem hu, innerAgg, ← integral_const_mul,
      ← integral_indicator measurableSet_Icc]
    congr 1
    funext s
    by_cases hs : s ∈ Set.Icc 0 (R - u)
    · rw [Set.indicator_of_mem (show (u, s) ∈ tri R from ⟨hu.1, hs.1, by linarith [hs.2]⟩),
        Set.indicator_of_mem hs]
      ring
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem]
      rintro ⟨-, h1, h2⟩
      exact hs ⟨h1, by linarith⟩
  · rw [Set.indicator_of_notMem hu]
    have : (fun s => (tri R).indicator (fun q : ℝ × ℝ => q.1 ^ k₁ * q.2 ^ k₂ * h q) (u, s)) =
        fun _ => 0 := by
      funext s
      refine Set.indicator_of_notMem ?_ _
      rintro ⟨h1, h2, h3⟩
      exact hu ⟨h1, by linarith⟩
    rw [this, integral_zero]

/-- **Two-aggregate Dirichlet integration.** For nonempty groups `I`, `J`, exponent vectors
`a`, `b`, and `h : ℝ × ℝ → ℝ` measurable and bounded on the triangle `tri R`:
`∫_{z, w ≥ 0, Σ z + Σ w ≤ R} zᵃ wᵇ h(Σ z, Σ w) = aggConst I a · aggConst J b ·
∫_{tri R} u₁^{aggExp I a} u₂^{aggExp J b} h(u₁, u₂)`. -/
theorem two_group [Nonempty I] [Nonempty J] (R : ℝ) (a : I → ℕ) (b : J → ℕ)
    (h : ℝ × ℝ → ℝ) (hm : Measurable h) (B : ℝ) (hb : ∀ q ∈ tri R, |h q| ≤ B) :
    ∫ p in quad I J R, (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) * h (∑ i, p.1 i, ∑ j, p.2 j) =
      aggConst I a * aggConst J b *
        ∫ q in tri R, q.1 ^ aggExp I a * q.2 ^ aggExp J b * h q := by
  set G : (I → ℝ) × (J → ℝ) → ℝ :=
    fun p => (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) * h (∑ i, p.1 i, ∑ j, p.2 j)
  have hQm := (quad_isClosed (I := I) (J := J) R).measurableSet
  have hint : Integrable ((quad I J R).indicator G) (volume.prod volume) := by
    rw [integrable_indicator_iff hQm]
    refine integrableOn_cont_mul (quad_isCompact R) hQm
      (P := fun p : (I → ℝ) × (J → ℝ) => (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j))
      (by fun_prop) (hm.comp (by fun_prop)) (B := B) ?_
    rintro ⟨z, w⟩ ⟨hz, hw, hs⟩
    exact hb _ ⟨Finset.sum_nonneg fun i _ => hz i, Finset.sum_nonneg fun j _ => hw j, hs⟩
  have hslice : ∀ z : I → ℝ, ∫ w, (quad I J R).indicator G (z, w) =
      (simplexF I R).indicator
        (fun z => (∏ i, z i ^ a i) * (aggConst J b * innerAgg R (aggExp J b) h (∑ i, z i))) z := by
    intro z
    by_cases hz : z ∈ simplexF I R
    · rw [Set.indicator_of_mem hz]
      have hfun : (fun w => (quad I J R).indicator G (z, w)) =
          (simplexF J (R - ∑ i, z i)).indicator
            (fun w => (∏ i, z i ^ a i) * ((∏ j, w j ^ b j) * h (∑ i, z i, ∑ j, w j))) := by
        funext w
        have hmem : (z, w) ∈ quad I J R ↔ w ∈ simplexF J (R - ∑ i, z i) := by
          simp only [quad, simplexF, Set.mem_ofPred_eq]
          constructor
          · rintro ⟨-, hw, hs⟩; exact ⟨hw, by linarith⟩
          · rintro ⟨hw, hs⟩; exact ⟨hz.1, hw, by linarith⟩
        by_cases hw : w ∈ simplexF J (R - ∑ i, z i)
        · rw [Set.indicator_of_mem (hmem.mpr hw), Set.indicator_of_mem hw]
          simp only [G]; ring
        · rw [Set.indicator_of_notMem (fun h' => hw (hmem.mp h')), Set.indicator_of_notMem hw]
      have hz0 : 0 ≤ ∑ i, z i := Finset.sum_nonneg fun i _ => hz.1 i
      rw [hfun, integral_indicator (simplexF_measurableSet _), integral_const_mul,
        one_group (R - ∑ i, z i) b (fun s => h (∑ i, z i, s)) (hm.comp (by fun_prop)) B
          (fun s hs => hb _ ⟨hz0, hs.1, by linarith [hs.2]⟩)]
      rfl
    · rw [Set.indicator_of_notMem hz]
      have : (fun w => (quad I J R).indicator G (z, w)) = fun _ => 0 := by
        funext w
        refine Set.indicator_of_notMem ?_ _
        rintro ⟨hz0, hw0, hs⟩
        exact hz ⟨hz0, by linarith [Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hw0 j]⟩
      rw [this, integral_zero]
  rw [← integral_indicator hQm, show (volume : Measure ((I → ℝ) × (J → ℝ))) = volume.prod volume
    from rfl, integral_prod _ hint]
  simp_rw [hslice]
  rw [integral_indicator (simplexF_measurableSet R),
    one_group R a (fun u => aggConst J b * innerAgg R (aggExp J b) h u)
      ((innerAgg_measurable R _ h hm).const_mul _) (|aggConst J b| * (|R| ^ aggExp J b * |B| * |R|))
      (fun u hu => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (innerAgg_bound R _ h B hb u hu) (abs_nonneg _)),
    tri_integral R _ _ h hm B hb, ← integral_const_mul, ← integral_const_mul]
  congr 1
  funext u
  ring

end TwoGroup

/-! ## The Fin N form: rough and smooth aggregates -/

section FinForm

theorem sum_compl_subtype {N : ℕ} (R : Finset (Fin N)) (y : Fin N → ℝ) :
    ∑ i ∈ Rᶜ, y i = ∑ i : {i // i ∉ R}, y i :=
  Finset.sum_subtype Rᶜ (fun _ => Finset.mem_compl) y

/-- **Two-aggregate Dirichlet integration on `Fin N`.** For a rough set `R` with `R` and `Rᶜ`
nonempty, `u₁ = aggR R y = Σ_{i ∈ R} yᵢ`, `u₂ = aggS R y = Σ_{i ∉ R} yᵢ`:
`∫_{y ≥ 0, Σ y ≤ M} yᵗ h(u₁, u₂) = aggConst R t · aggConst Rᶜ t ·
∫_{tri M} u₁^{aggExp R t} u₂^{aggExp Rᶜ t} h(u₁, u₂)`. -/
theorem two_group_fin {N : ℕ} (R : Finset (Fin N)) (hR : R.Nonempty) (hRc : Rᶜ.Nonempty) (M : ℝ)
    (t : Fin N → ℕ) (h : ℝ × ℝ → ℝ) (hm : Measurable h) (B : ℝ) (hb : ∀ q ∈ tri M, |h q| ≤ B) :
    ∫ y in simplexF (Fin N) M, (∏ i, y i ^ t i) * h (aggR R y, aggS R y) =
      aggConst {i // i ∈ R} (fun i => t i) * aggConst {i // i ∉ R} (fun i => t i) *
        ∫ q in tri M, q.1 ^ aggExp {i // i ∈ R} (fun i => t i) *
          q.2 ^ aggExp {i // i ∉ R} (fun i => t i) * h q := by
  have : Nonempty {i // i ∈ R} := hR.to_subtype
  have : Nonempty {i // i ∉ R} := by
    obtain ⟨i, hi⟩ := hRc; exact ⟨⟨i, Finset.mem_compl.mp hi⟩⟩
  set Φ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => ℝ) (· ∈ R) with hΦdef
  have hΦ : MeasurePreserving Φ.symm volume volume := by
    convert (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin N => ℝ) (· ∈ R)).symm Φ <;> rfl
  rw [← two_group M (fun i : {i // i ∈ R} => t i) (fun i : {i // i ∉ R} => t i) h hm B hb,
    ← integral_indicator (simplexF_measurableSet M), ← hΦ.integral_comp',
    ← integral_indicator (quad_isClosed M).measurableSet]
  congr 1
  funext ⟨z, w⟩
  obtain ⟨h1, h2, hR', hall⟩ := split_sums N R z w
  rw [← hΦdef] at h1 h2 hR' hall
  have hS : aggS R (Φ.symm (z, w)) = ∑ i, w i := by
    rw [aggS, sum_compl_subtype]
    exact Finset.sum_congr rfl fun i _ => h2 i
  have hP : ∏ i, Φ.symm (z, w) i ^ t i = (∏ i, z i ^ t i) * (∏ i, w i ^ t i) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (· ∈ R)]
    congr 1
    · exact Finset.prod_congr (by congr; exact Subsingleton.elim _ _) fun i _ => by rw [h1 i]
    · exact Finset.prod_congr (by congr) fun i _ => by rw [h2 i]
  have hmem : Φ.symm (z, w) ∈ simplexF (Fin N) M ↔ (z, w) ∈ quad {i // i ∈ R} {i // i ∉ R} M := by
    simp only [simplexF, quad, Set.mem_ofPred_eq, hall]
    constructor
    · rintro ⟨h0, hs⟩
      exact ⟨fun i => by rw [← h1 i]; exact h0 _, fun i => by rw [← h2 i]; exact h0 _, hs⟩
    · rintro ⟨hz, hw, hs⟩
      refine ⟨fun i => ?_, hs⟩
      by_cases hi : i ∈ R
      · have := h1 ⟨i, hi⟩; simp only at this; rw [this]; exact hz _
      · have := h2 ⟨i, hi⟩; simp only at this; rw [this]; exact hw _
  by_cases hq : (z, w) ∈ quad {i // i ∈ R} {i // i ∉ R} M
  · rw [Set.indicator_of_mem (hmem.mpr hq), Set.indicator_of_mem hq, hP, hS, aggR, hR']
  · rw [Set.indicator_of_notMem (fun h' => hq (hmem.mp h')), Set.indicator_of_notMem hq]

end FinForm

/-! ## Boundary cases -/

section Boundary

variable {I J : Type*} [Fintype I] [Fintype J]

theorem volume_isEmpty {κ : Type*} [Fintype κ] [IsEmpty κ] (x : κ → ℝ) :
    (volume : Measure (κ → ℝ)) = Measure.dirac x := by
  rw [volume_pi]; exact Measure.pi_of_empty _ x

/-- **Empty group.** With no coordinates the "simplex" is a point: the integral is `h 0`. -/
theorem one_group_empty {ι : Type*} [Fintype ι] [IsEmpty ι] (R : ℝ) (hR : 0 ≤ R) (e : ι → ℕ)
    (h : ℝ → ℝ) : ∫ z in simplexF ι R, (∏ i, z i ^ e i) * h (∑ i, z i) = h 0 := by
  have huniv : simplexF ι R = Set.univ := by
    ext z; simp [simplexF, hR]
  rw [huniv, Measure.restrict_univ, volume_isEmpty (isEmptyElim : ι → ℝ), integral_dirac]
  simp

omit [Fintype J] in
theorem quad_integrable [Fintype J] (R : ℝ) (a : I → ℕ) (b : J → ℕ) (h : ℝ × ℝ → ℝ)
    (hm : Measurable h) (B : ℝ) (hb : ∀ q ∈ tri R, |h q| ≤ B) :
    Integrable ((quad I J R).indicator fun p : (I → ℝ) × (J → ℝ) =>
      (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) * h (∑ i, p.1 i, ∑ j, p.2 j)) (volume.prod volume) := by
  have hQm := (quad_isClosed (I := I) (J := J) R).measurableSet
  rw [integrable_indicator_iff hQm]
  refine integrableOn_cont_mul (quad_isCompact R) hQm
    (P := fun p : (I → ℝ) × (J → ℝ) => (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j))
    (by fun_prop) (hm.comp (by fun_prop)) (B := B) ?_
  rintro ⟨z, w⟩ ⟨hz, hw, hs⟩
  exact hb _ ⟨Finset.sum_nonneg fun i _ => hz i, Finset.sum_nonneg fun j _ => hw j, hs⟩

/-- **Empty smooth group** (`J = ∅`): one aggregate, `u₂ = 0`. -/
theorem two_group_right_empty [DecidableEq I] [Nonempty I] [IsEmpty J] (R : ℝ) (a : I → ℕ)
    (b : J → ℕ) (h : ℝ × ℝ → ℝ) (hm : Measurable h) (B : ℝ) (hb : ∀ q ∈ tri R, |h q| ≤ B) :
    ∫ p in quad I J R, (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) * h (∑ i, p.1 i, ∑ j, p.2 j) =
      aggConst I a * ∫ u in Set.Icc 0 R, u ^ aggExp I a * h (u, 0) := by
  rw [← integral_indicator (quad_isClosed R).measurableSet,
    show (volume : Measure ((I → ℝ) × (J → ℝ))) = volume.prod volume from rfl,
    integral_prod _ (quad_integrable R a b h hm B hb)]
  have hslice : ∀ z : I → ℝ, ∫ w, (quad I J R).indicator (fun p : (I → ℝ) × (J → ℝ) =>
      (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) * h (∑ i, p.1 i, ∑ j, p.2 j)) (z, w) =
      (simplexF I R).indicator (fun z => (∏ i, z i ^ a i) * h (∑ i, z i, 0)) z := by
    intro z
    rw [volume_isEmpty (isEmptyElim : J → ℝ), integral_dirac]
    by_cases hz : z ∈ simplexF I R
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (show (z, (isEmptyElim : J → ℝ)) ∈ quad I J R
        from ⟨hz.1, isEmptyElim, by simpa using hz.2⟩)]
      simp
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem]
      rintro ⟨h0, -, hs⟩
      exact hz ⟨h0, by simpa using hs⟩
  simp_rw [hslice]
  rw [integral_indicator (simplexF_measurableSet R),
    one_group R a (fun u => h (u, 0)) (hm.comp (by fun_prop)) B
      (fun u hu => hb _ ⟨hu.1, le_refl 0, by simpa using hu.2⟩)]

/-- **Empty rough group** (`I = ∅`): one aggregate, `u₁ = 0`. -/
theorem two_group_left_empty [DecidableEq J] [IsEmpty I] [Nonempty J] (R : ℝ) (a : I → ℕ)
    (b : J → ℕ) (h : ℝ × ℝ → ℝ) (hm : Measurable h) (B : ℝ) (hb : ∀ q ∈ tri R, |h q| ≤ B) :
    ∫ p in quad I J R, (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) * h (∑ i, p.1 i, ∑ j, p.2 j) =
      aggConst J b * ∫ u in Set.Icc 0 R, u ^ aggExp J b * h (0, u) := by
  rw [← integral_indicator (quad_isClosed R).measurableSet,
    show (volume : Measure ((I → ℝ) × (J → ℝ))) = volume.prod volume from rfl,
    integral_prod_symm _ (quad_integrable R a b h hm B hb)]
  have hslice : ∀ w : J → ℝ, ∫ z, (quad I J R).indicator (fun p : (I → ℝ) × (J → ℝ) =>
      (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) * h (∑ i, p.1 i, ∑ j, p.2 j)) (z, w) =
      (simplexF J R).indicator (fun w => (∏ j, w j ^ b j) * h (0, ∑ j, w j)) w := by
    intro w
    rw [volume_isEmpty (isEmptyElim : I → ℝ), integral_dirac]
    by_cases hw : w ∈ simplexF J R
    · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (show ((isEmptyElim : I → ℝ), w) ∈ quad I J R
        from ⟨isEmptyElim, hw.1, by simpa using hw.2⟩)]
      simp
    · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem]
      rintro ⟨-, h0, hs⟩
      exact hw ⟨h0, by simpa using hs⟩
  simp_rw [hslice]
  rw [integral_indicator (simplexF_measurableSet R),
    one_group R b (fun u => h (0, u)) (hm.comp (by fun_prop)) B
      (fun u hu => hb _ ⟨le_refl 0, hu.1, by simpa using hu.2⟩)]

/-- **Both groups empty**: the region is the point `0` (for `R ≥ 0`). -/
theorem two_group_both_empty [IsEmpty I] [IsEmpty J] (R : ℝ) (hR : 0 ≤ R) (a : I → ℕ)
    (b : J → ℕ) (h : ℝ × ℝ → ℝ) :
    ∫ p in quad I J R, (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) * h (∑ i, p.1 i, ∑ j, p.2 j) =
      h (0, 0) := by
  have huniv : quad I J R = Set.univ := by ext p; simp [quad, hR]
  rw [huniv, Measure.restrict_univ, show (volume : Measure ((I → ℝ) × (J → ℝ))) =
    volume.prod volume from rfl, volume_isEmpty (isEmptyElim : I → ℝ),
    volume_isEmpty (isEmptyElim : J → ℝ), Measure.dirac_prod_dirac, integral_dirac]
  simp

/-- **Zero exponents.** -/
theorem aggExp_zero (ι : Type*) [Fintype ι] : aggExp ι (fun _ => 0) = Fintype.card ι - 1 := by
  simp [aggExp]

theorem aggConst_zero (ι : Type*) [Fintype ι] :
    aggConst ι (fun _ => 0) = 1 / ((Fintype.card ι - 1).factorial : ℝ) := by
  simp [aggConst, aggExp_zero]

/-- **Empty region** (`R < 0`). -/
theorem tri_eq_empty (R : ℝ) (hR : R < 0) : tri R = ∅ := by
  ext q; simp only [tri, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1 h2 h3; linarith

omit [Fintype I] [Fintype J] in
theorem quad_eq_empty [Fintype I] [Fintype J] (R : ℝ) (hR : R < 0) : quad I J R = ∅ := by
  ext p
  simp only [quad, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hz hw hs
  linarith [Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => hz i,
    Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hw j]

end Boundary

/-! ## The triangle as V1's two-dimensional simplex; rational specializations -/

section Rational

open BGP212.Var

theorem tri_eq_simplex (R : ℝ) (F : ℝ × ℝ → ℝ) :
    ∫ q in tri R, F q = ∫ z in simplex 2 R, F (z 0, z 1) := by
  have hT := volume_preserving_finTwoArrow ℝ
  rw [← integral_indicator (tri_isClosed R).measurableSet, ← hT.integral_comp',
    ← integral_indicator (simplex_measurableSet 2 R)]
  congr 1
  funext z
  have hz : MeasurableEquiv.finTwoArrow z = (z 0, z 1) := rfl
  have hmem : (z 0, z 1) ∈ tri R ↔ z ∈ simplex 2 R := by
    simp only [tri, simplex, Set.mem_ofPred_eq, Fin.forall_fin_two, Fin.sum_univ_two]
    tauto
  rw [hz]
  by_cases h : z ∈ simplex 2 R
  · rw [Set.indicator_of_mem (hmem.mpr h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun h' => h (hmem.mp h')), Set.indicator_of_notMem h]

/-- **Monomials on the triangle** (V1's (10.1) in dimension 2):
`∫_{tri R} u₁^α u₂^β = R^{2+α+β} α! β! / (2+α+β)!`. -/
theorem tri_monomial (R : ℝ) (hR : 0 ≤ R) (α β : ℕ) :
    ∫ q in tri R, q.1 ^ α * q.2 ^ β =
      R ^ (2 + α + β) * (α.factorial : ℝ) * (β.factorial : ℝ) / ((2 + α + β).factorial : ℝ) := by
  rw [tri_eq_simplex]
  have := simplex_integral 2 R ![α, β] hR
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
  rw [this, momentR]
  simp only [Fin.sum_univ_two, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [add_assoc]; ring

/-- **Rational polynomials on the triangle** (V1's Lemma 10.1 in dimension 2). -/
theorem tri_poly (R : ℚ) (hR : 0 ≤ R) (G : MvPolynomial (Fin 2) ℚ) :
    ∫ q in tri (R : ℝ), MvPolynomial.eval₂ (algebraMap ℚ ℝ) ![q.1, q.2] G = (polyIntegralQ R G : ℝ) := by
  rw [tri_eq_simplex]
  have hv : ∀ z : Fin 2 → ℝ, ![z 0, z 1] = z := fun z => by
    funext i; fin_cases i <;> rfl
  simp_rw [hv]
  exact poly_integral 2 R hR G

theorem aggConst_eq_cast (ι : Type*) [Fintype ι] (e : ι → ℕ) :
    aggConst ι e = (aggConstQ ι e : ℝ) := by
  simp [aggConst, aggConstQ]

theorem continuous_evalPoly (P : MvPolynomial (Fin 2) ℚ) :
    Continuous fun q : ℝ × ℝ => MvPolynomial.eval₂ (algebraMap ℚ ℝ) ![q.1, q.2] P := by
  simp only [MvPolynomial.eval₂_eq']
  refine continuous_finsetSum _ fun d _ => continuous_const.mul ?_
  refine continuous_finsetProd _ fun i _ => ?_
  fin_cases i
  · exact continuous_fst.pow _
  · exact continuous_snd.pow _

/-- **Rational polynomial specialization.** For `h` a polynomial with rational coefficients in
the two aggregates and rational `R ≥ 0`, the two-group integral is an explicit rational:
`aggConstQ I a · aggConstQ J b · polyIntegralQ R (X₀^{aggExp I a} X₁^{aggExp J b} P)`. -/
theorem two_group_poly {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J] (R : ℚ) (hR : 0 ≤ R) (a : I → ℕ) (b : J → ℕ)
    (P : MvPolynomial (Fin 2) ℚ) :
    ∫ p in quad I J (R : ℝ), (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) ![∑ i, p.1 i, ∑ j, p.2 j] P =
      ((aggConstQ I a * aggConstQ J b *
        polyIntegralQ R (MvPolynomial.X 0 ^ aggExp I a * MvPolynomial.X 1 ^ aggExp J b * P) : ℚ) : ℝ) := by
  obtain ⟨B, hB⟩ := (tri_isCompact (R : ℝ)).exists_bound_of_continuousOn
    (continuous_evalPoly P).continuousOn
  have := two_group (R : ℝ) a b (fun q => MvPolynomial.eval₂ (algebraMap ℚ ℝ) ![q.1, q.2] P)
    (continuous_evalPoly P).measurable B (fun q hq => by rw [← Real.norm_eq_abs]; exact hB q hq)
  simp only at this
  have hG : ∫ q in tri (R : ℝ), q.1 ^ aggExp I a * q.2 ^ aggExp J b *
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) ![q.1, q.2] P =
      ∫ q in tri (R : ℝ), MvPolynomial.eval₂ (algebraMap ℚ ℝ) ![q.1, q.2]
        (MvPolynomial.X 0 ^ aggExp I a * MvPolynomial.X 1 ^ aggExp J b * P) := by
    congr 1; funext q
    simp [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X]
  rw [this, hG, tri_poly R hR, aggConst_eq_cast, aggConst_eq_cast]
  push_cast; ring

/-- **Consistency with (10.1).** With `h = 1` the two-aggregate formula reproduces the simplex
moment of the combined monomial: `R^{n} ∏ aᵢ! ∏ bⱼ! / n!`, `n = |I| + Σ a + |J| + Σ b`. -/
theorem two_group_const {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Nonempty I] [Nonempty J] (R : ℝ) (hR : 0 ≤ R) (a : I → ℕ) (b : J → ℕ) :
    ∫ p in quad I J R, (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) =
      R ^ (Fintype.card I + ∑ i, a i + (Fintype.card J + ∑ j, b j)) *
        (∏ i, ((a i).factorial : ℝ)) * (∏ j, ((b j).factorial : ℝ)) /
          ((Fintype.card I + ∑ i, a i + (Fintype.card J + ∑ j, b j)).factorial : ℝ) := by
  have := two_group R a b (fun _ => 1) measurable_const 1 (fun _ _ => by simp)
  simp only [mul_one] at this
  rw [this, tri_monomial R hR]
  have hI : 1 ≤ Fintype.card I := Fintype.card_pos
  have hJ : 1 ≤ Fintype.card J := Fintype.card_pos
  have hn : 2 + aggExp I a + aggExp J b = Fintype.card I + ∑ i, a i + (Fintype.card J + ∑ j, b j) := by
    simp only [aggExp]; omega
  rw [hn, aggConst, aggConst]
  have h1 : ((aggExp I a).factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((aggExp J b).factorial : ℝ) ≠ 0 := by positivity
  field_simp

end Rational

/-! ## The aggregates of V2d's marginal problem -/

section Link

theorem sum_eq_aggR_add_aggS {N : ℕ} (R : Finset (Fin N)) (x : Fin N → ℝ) :
    ∑ i, x i = aggR R x + aggS R x := (Finset.sum_add_sum_compl R x).symm

/-- On a translated piece `x = y + g·1_{R ∪ K}`: the rough mass is `|R| g + u₁`. -/
theorem aggR_shift {N : ℕ} (g : ℝ) (R K : Finset (Fin N)) (y : Fin N → ℝ) :
    aggR R (y + shiftV g (R ∪ K)) = R.card * g + aggR R y := by
  simp only [aggR, Pi.add_apply, Finset.sum_add_distrib]
  rw [sum_shiftV g _ _ Finset.subset_union_left]; ring

/-- On a translated piece `x = y + g·1_{R ∪ K}` (`R`, `K` disjoint): the remaining mass is
`|K| g + u₂`. -/
theorem aggS_shift {N : ℕ} (g : ℝ) (R K : Finset (Fin N)) (hRK : Disjoint R K) (y : Fin N → ℝ) :
    aggS R (y + shiftV g (R ∪ K)) = K.card * g + aggS R y := by
  have htot := sum_add_shiftV g R K hRK y
  have h1 := sum_eq_aggR_add_aggS R (y + shiftV g (R ∪ K))
  have h2 := sum_eq_aggR_add_aggS R y
  have h3 := aggR_shift g R K y
  linarith

/-- On the stratum `roughSet g x = R`, Lemma 9.2's endpoint is the stratum endpoint. -/
theorem endpoint_eq_stratum {n : ℕ} (g L : ℝ) (C : ℕ → ℝ) (x : Fin n → ℝ) (R : Finset (Fin n))
    (hR : roughSet g x = R) : endpoint g L C x = stratumEndpoint g L C R x := by
  simp only [endpoint, stratumEndpoint, roughCount, roughMass, hR, aggR]

/-- **The aggregate form of the endpoint.** On V2b's translated piece `x = y + g·1_{R ∪ K}` the
stratum endpoint depends on `y` only through `u₁ = aggR R y` (rough mass `ρ₁ = |R| g + u₁`) and
`u₂ = aggS R y` (remaining mass `S − ρ₁ = |K| g + u₂`). -/
theorem stratumEndpoint_shift {n : ℕ} (g L : ℝ) (C : ℕ → ℝ) (R K : Finset (Fin n))
    (hRK : Disjoint R K) (y : Fin n → ℝ) :
    stratumEndpoint g L C R (y + shiftV g (R ∪ K)) =
      endpointAgg g L C R.card K.card (aggR R y) (aggS R y) := by
  rw [stratumEndpoint, endpointAgg, sum_eq_aggR_add_aggS R, aggR_shift g R K y,
    aggS_shift g R K hRK y]
  congr 2; ring

end Link

/-! ## A branch-type cut, and the worked example -/

section Example

theorem integral_Icc_pow (X : ℝ) (hX : 0 ≤ X) (k : ℕ) :
    ∫ s in Set.Icc 0 X, s ^ k = X ^ (k + 1) / (k + 1) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hX, integral_pow]
  simp

/-- **One cut of the triangle** (`u₁ ≤ c`, the shape of one branch of `U`), in closed form via
V2d's `inner_integral`. -/
theorem tri_cut (R c : ℝ) (hc : 0 ≤ c) (hcR : c ≤ R) (α β : ℕ) :
    ∫ q in tri R, q.1 ^ α * q.2 ^ β * (Set.Iic c).indicator (fun _ => (1 : ℝ)) q.1 =
      (∑ j ∈ Finset.range (β + 1 + 1), ((β + 1).choose j : ℝ) * R ^ (β + 1 - j) * (-1) ^ j *
        c ^ (α + j + 1) / (α + j + 1)) / (β + 1) := by
  have hm : Measurable fun q : ℝ × ℝ => (Set.Iic c).indicator (fun _ => (1 : ℝ)) q.1 :=
    (measurable_const.indicator measurableSet_Iic).comp measurable_fst
  rw [tri_integral R α β _ hm 1 (fun q _ => by
    simp only [Set.indicator]; split_ifs <;> simp)]
  have hinner : ∀ u ∈ Set.Icc 0 R, u ^ α * innerAgg R β
      (fun q : ℝ × ℝ => (Set.Iic c).indicator (fun _ => (1 : ℝ)) q.1) u =
      (Set.Iic c).indicator (fun u => (R - u) ^ (β + 1) * u ^ α / (β + 1)) u := by
    intro u hu
    simp only [innerAgg]
    by_cases huc : u ∈ Set.Iic c
    · simp only [Set.indicator_of_mem huc, mul_one]
      rw [integral_Icc_pow (R - u) (by linarith [hu.2])]; ring
    · simp only [Set.indicator_of_notMem huc, mul_zero, integral_zero]
  rw [setIntegral_congr_fun measurableSet_Icc hinner, setIntegral_indicator measurableSet_Iic,
    show Set.Icc (0 : ℝ) R ∩ Set.Iic c = Set.Icc 0 c by
      ext u; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
      constructor
      · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2 hcR⟩, h2⟩,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hc,
    intervalIntegral.integral_div, inner_integral c R (β + 1) α]

/-- **The worked example.** In dimension 3 with rough set `R = {0}` and exponents `(1, 0, 2)`,
`∫_{y ≥ 0, Σ y ≤ 1} y₀ y₂² 1[y₀ ≤ 1/2] dy = 19/7680`: the aggregate theorem reduces it to
`(1/3) ∫_{tri 1, u₁ ≤ 1/2} u₁ u₂³`, evaluated by `tri_cut`. -/
theorem example_value : exampleLHS (1 / 2) 1 = 19 / 7680 := by
  have hR : ({0} : Finset (Fin 3)).Nonempty := Finset.singleton_nonempty 0
  have hRc : ({0} : Finset (Fin 3))ᶜ.Nonempty := ⟨1, by decide⟩
  have hm : Measurable fun q : ℝ × ℝ => (Set.Iic (1 / 2 : ℝ)).indicator (fun _ => (1 : ℝ)) q.1 :=
    (measurable_const.indicator measurableSet_Iic).comp measurable_fst
  have key := two_group_fin {0} hR hRc 1 ![1, 0, 2] _ hm 1 (fun q _ => by
    simp only [Set.indicator]; split_ifs <;> simp)
  have hlhs : exampleLHS (1 / 2) 1 = ∫ y in simplexF (Fin 3) 1, (∏ i, y i ^ (![1, 0, 2] : Fin 3 → ℕ) i) *
      (Set.Iic (1 / 2 : ℝ)).indicator (fun _ => (1 : ℝ)) (aggR {0} y, aggS {0} y).1 := by
    rw [exampleLHS]
    congr 1; funext y
    simp [Fin.prod_univ_three, aggR]
  have e1 : ∀ inst : Fintype {i // i ∈ ({0} : Finset (Fin 3))},
      @aggExp _ inst (fun i => (![1, 0, 2] : Fin 3 → ℕ) i) = 1 := by
    intro inst; rw [Subsingleton.elim inst (Subtype.fintype _)]; decide
  have e2 : ∀ inst : Fintype {i // i ∉ ({0} : Finset (Fin 3))},
      @aggExp _ inst (fun i => (![1, 0, 2] : Fin 3 → ℕ) i) = 3 := by
    intro inst; rw [Subsingleton.elim inst (Subtype.fintype _)]; decide
  have c1 : ∀ inst : Fintype {i // i ∈ ({0} : Finset (Fin 3))},
      @aggConstQ _ inst (fun i => (![1, 0, 2] : Fin 3 → ℕ) i) = 1 := by
    intro inst; rw [Subsingleton.elim inst (Subtype.fintype _)]; decide +kernel
  have c2 : ∀ inst : Fintype {i // i ∉ ({0} : Finset (Fin 3))},
      @aggConstQ _ inst (fun i => (![1, 0, 2] : Fin 3 → ℕ) i) = 1 / 3 := by
    intro inst; rw [Subsingleton.elim inst (Subtype.fintype _)]; decide +kernel
  rw [hlhs, key, e1, e2, aggConst_eq_cast, aggConst_eq_cast, c1, c2,
    tri_cut 1 (1 / 2) (by norm_num) (by norm_num) 1 3]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [Nat.choose]

end Example

end BGP212.V2e

/-! ## Comparator wrappers -/

namespace BGP212.Challenge

open BGP212.Gram BGP212.V2d BGP212.V2e MeasureTheory

/-- One aggregate: `∫_{z ≥ 0, Σ z ≤ R} zᵉ h(Σ z) = aggConst ι e · ∫_{[0,R]} s^{aggExp ι e} h(s)`. -/
theorem one_group {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (R : ℝ) (e : ι → ℕ) (h : ℝ → ℝ) (hm : Measurable h) (B : ℝ)
    (hb : ∀ s ∈ Set.Icc 0 R, |h s| ≤ B) :
    ∫ z in simplexF ι R, (∏ i, z i ^ e i) * h (∑ i, z i) =
      aggConst ι e * ∫ s in Set.Icc 0 R, s ^ aggExp ι e * h s :=
  BGP212.V2e.one_group R e h hm B hb

/-- **Two-aggregate Dirichlet integration** (`h` measurable, bounded on `tri R`). -/
theorem two_group {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J] (R : ℝ) (a : I → ℕ) (b : J → ℕ)
    (h : ℝ × ℝ → ℝ) (hm : Measurable h) (B : ℝ) (hb : ∀ q ∈ tri R, |h q| ≤ B) :
    ∫ p in quad I J R, (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) * h (∑ i, p.1 i, ∑ j, p.2 j) =
      aggConst I a * aggConst J b *
        ∫ q in tri R, q.1 ^ aggExp I a * q.2 ^ aggExp J b * h q :=
  BGP212.V2e.two_group R a b h hm B hb

/-- The same on `Fin N`, with rough aggregate `u₁ = aggR R y` and smooth aggregate `u₂ = aggS R y`. -/
theorem two_group_fin {N : ℕ} (R : Finset (Fin N)) (hR : R.Nonempty) (hRc : Rᶜ.Nonempty) (M : ℝ)
    (t : Fin N → ℕ) (h : ℝ × ℝ → ℝ) (hm : Measurable h) (B : ℝ) (hb : ∀ q ∈ tri M, |h q| ≤ B) :
    ∫ y in simplexF (Fin N) M, (∏ i, y i ^ t i) * h (aggR R y, aggS R y) =
      aggConst {i // i ∈ R} (fun i => t i) * aggConst {i // i ∉ R} (fun i => t i) *
        ∫ q in tri M, q.1 ^ aggExp {i // i ∈ R} (fun i => t i) *
          q.2 ^ aggExp {i // i ∉ R} (fun i => t i) * h q :=
  BGP212.V2e.two_group_fin R hR hRc M t h hm B hb

/-- Empty group: the integral is `h 0`. -/
theorem one_group_empty {ι : Type*} [Fintype ι] [IsEmpty ι] (R : ℝ) (hR : 0 ≤ R) (e : ι → ℕ)
    (h : ℝ → ℝ) :
    ∫ z in simplexF ι R, (∏ i, z i ^ e i) * h (∑ i, z i) = h 0 :=
  BGP212.V2e.one_group_empty R hR e h

/-- Empty smooth group (`u₂ = 0`). -/
theorem two_group_right_empty {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [Nonempty I] [IsEmpty J] (R : ℝ) (a : I → ℕ)
    (b : J → ℕ) (h : ℝ × ℝ → ℝ) (hm : Measurable h) (B : ℝ) (hb : ∀ q ∈ tri R, |h q| ≤ B) :
    ∫ p in quad I J R, (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) * h (∑ i, p.1 i, ∑ j, p.2 j) =
      aggConst I a * ∫ u in Set.Icc 0 R, u ^ aggExp I a * h (u, 0) :=
  BGP212.V2e.two_group_right_empty R a b h hm B hb

/-- Empty rough group (`u₁ = 0`). -/
theorem two_group_left_empty {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J] [IsEmpty I] [Nonempty J] (R : ℝ) (a : I → ℕ)
    (b : J → ℕ) (h : ℝ × ℝ → ℝ) (hm : Measurable h) (B : ℝ) (hb : ∀ q ∈ tri R, |h q| ≤ B) :
    ∫ p in quad I J R, (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) * h (∑ i, p.1 i, ∑ j, p.2 j) =
      aggConst J b * ∫ u in Set.Icc 0 R, u ^ aggExp J b * h (0, u) :=
  BGP212.V2e.two_group_left_empty R a b h hm B hb

/-- Both groups empty: the value `h (0, 0)`. -/
theorem two_group_both_empty {I J : Type*} [Fintype I] [Fintype J] [IsEmpty I] [IsEmpty J] (R : ℝ) (hR : 0 ≤ R) (a : I → ℕ)
    (b : J → ℕ) (h : ℝ × ℝ → ℝ) :
    ∫ p in quad I J R, (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) * h (∑ i, p.1 i, ∑ j, p.2 j) =
      h (0, 0) :=
  BGP212.V2e.two_group_both_empty R hR a b h

/-- Zero exponents. -/
theorem aggConst_zero (ι : Type*) [Fintype ι] :
    aggConst ι (fun _ => 0) = 1 / ((Fintype.card ι - 1).factorial : ℝ) :=
  BGP212.V2e.aggConst_zero ι

/-- Monomials on the triangle (V1's (10.1) in dimension 2). -/
theorem tri_monomial (R : ℝ) (hR : 0 ≤ R) (α β : ℕ) :
    ∫ q in tri R, q.1 ^ α * q.2 ^ β =
      R ^ (2 + α + β) * (α.factorial : ℝ) * (β.factorial : ℝ) / ((2 + α + β).factorial : ℝ) :=
  BGP212.V2e.tri_monomial R hR α β

/-- Rational polynomials on the triangle (V1's Lemma 10.1 in dimension 2). -/
theorem tri_poly (R : ℚ) (hR : 0 ≤ R) (G : MvPolynomial (Fin 2) ℚ) :
    ∫ q in tri (R : ℝ), MvPolynomial.eval₂ (algebraMap ℚ ℝ) ![q.1, q.2] G = (BGP212.Var.polyIntegralQ R G : ℝ) :=
  BGP212.V2e.tri_poly R hR G

/-- Rational polynomial specialization of the two-aggregate theorem. -/
theorem two_group_poly {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (R : ℚ) (hR : 0 ≤ R) (a : I → ℕ) (b : J → ℕ) (P : MvPolynomial (Fin 2) ℚ) :
    ∫ p in quad I J (R : ℝ), (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) ![∑ i, p.1 i, ∑ j, p.2 j] P =
      ((aggConstQ I a * aggConstQ J b *
        BGP212.Var.polyIntegralQ R (MvPolynomial.X 0 ^ aggExp I a * MvPolynomial.X 1 ^ aggExp J b * P) : ℚ) : ℝ) :=
  BGP212.V2e.two_group_poly R hR a b P

/-- Consistency with (10.1): `h = 1` gives the simplex moment of the combined monomial. -/
theorem two_group_const {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J] (R : ℝ) (hR : 0 ≤ R) (a : I → ℕ) (b : J → ℕ) :
    ∫ p in quad I J R, (∏ i, p.1 i ^ a i) * (∏ j, p.2 j ^ b j) =
      R ^ (Fintype.card I + ∑ i, a i + (Fintype.card J + ∑ j, b j)) *
        (∏ i, ((a i).factorial : ℝ)) * (∏ j, ((b j).factorial : ℝ)) /
          ((Fintype.card I + ∑ i, a i + (Fintype.card J + ∑ j, b j)).factorial : ℝ) :=
  BGP212.V2e.two_group_const R hR a b

/-- On a translated piece the rough mass is `|R| g + u₁`. -/
theorem aggR_shift {N : ℕ} (g : ℝ) (R K : Finset (Fin N)) (y : Fin N → ℝ) :
    aggR R (y + shiftV g (R ∪ K)) = R.card * g + aggR R y :=
  BGP212.V2e.aggR_shift g R K y

/-- On a translated piece the remaining mass is `|K| g + u₂`. -/
theorem aggS_shift {N : ℕ} (g : ℝ) (R K : Finset (Fin N)) (hRK : Disjoint R K) (y : Fin N → ℝ) :
    aggS R (y + shiftV g (R ∪ K)) = K.card * g + aggS R y :=
  BGP212.V2e.aggS_shift g R K hRK y

/-- On the stratum `roughSet g x = R`, Lemma 9.2's endpoint is the stratum endpoint. -/
theorem endpoint_eq_stratum {n : ℕ} (g L : ℝ) (C : ℕ → ℝ) (x : Fin n → ℝ) (R : Finset (Fin n))
    (hR : roughSet g x = R) :
    endpoint g L C x = stratumEndpoint g L C R x :=
  BGP212.V2e.endpoint_eq_stratum g L C x R hR

/-- The endpoint on a translated piece is a function of the two aggregates. -/
theorem stratumEndpoint_shift {n : ℕ} (g L : ℝ) (C : ℕ → ℝ) (R K : Finset (Fin n))
    (hRK : Disjoint R K) (y : Fin n → ℝ) :
    stratumEndpoint g L C R (y + shiftV g (R ∪ K)) =
      endpointAgg g L C R.card K.card (aggR R y) (aggS R y) :=
  BGP212.V2e.stratumEndpoint_shift g L C R K hRK y

/-- One cut `u₁ ≤ c` of the triangle, in closed form. -/
theorem tri_cut (R c : ℝ) (hc : 0 ≤ c) (hcR : c ≤ R) (α β : ℕ) :
    ∫ q in tri R, q.1 ^ α * q.2 ^ β * (Set.Iic c).indicator (fun _ => (1 : ℝ)) q.1 =
      (∑ j ∈ Finset.range (β + 1 + 1), ((β + 1).choose j : ℝ) * R ^ (β + 1 - j) * (-1) ^ j *
        c ^ (α + j + 1) / (α + j + 1)) / (β + 1) :=
  BGP212.V2e.tri_cut R c hc hcR α β

/-- **The worked example**: `∫_{y ∈ ℝ³, y ≥ 0, Σ y ≤ 1} y₀ y₂² 1[y₀ ≤ 1/2] = 19/7680`. -/
theorem example_value :
    exampleLHS (1 / 2) 1 = 19 / 7680 :=
  BGP212.V2e.example_value

end BGP212.Challenge
