/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Lemma 9.1 (p. 41), (10.1), Lemma 10.1, Proposition 10.2 (pp. 41–42).
-/
import BGP212.GramEntry
import Solution.GramEntryCert
import Solution.SimplexMoment
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.MvPolynomial.CommRing


/-! # V2b: the Gram entry as a Lebesgue integral (proofs)

PROVED INTEGRAL IDENTITIES. The chain from the support to the closed form `gramFormula`:

1. `simplexF_integral`: V1's (10.1) transported to any finite index type.
2. `integral_fibred`: Fubini on `{(z, w) : z ∈ A, w ∈ simplexF κ (M − Σ z)}`.
3. `weighted_simplexF`: `∫ zᵉ (c − Σ z)^p`, from (10.1) on `ι ⊕ Unit` and step 2.
4. `piece_integral_mem` / `piece_integral_notMem`: a piece `{y ≥ 0 : Σ_R y ≤ c, Σ y ≤ M}` split as
   `(y|_R, y|_{Rᶜ})` (`volume_preserving_piEquivPiSubtypeProd`), inner block by step 3, outer block
   by expanding `(M − Σ z)^q` around `min c M` and step 3 again.
5. `indicator_supportT`: stratification by the rough set and inclusion–exclusion over the smooth
   bounds, as a pointwise identity of indicators (`Finset.sum_powerset_neg_one_pow_card`).
6. `integral_Qset`: translation `x = y + g·1_{R∪K}` (`integral_add_right_eq_self`) and the null
   faces `yᵢ = 0` (`Measure.pi_hyperplane`).
7. `count_pieces`: grouping the `(R, K)` sum by cardinalities (`Finset.sum_powerset_insert`,
   `Finset.sum_powerset_apply_card`).
8. `integral_supportT`, `gram_entry_integral_general`: the closed form for every `N`, `g ≥ 0`,
   `L`, cap function `C`; boundary cases `R = ∅`, `R = univ`, `N = 0`, empty index types.

The Table 3 value comes from the computational certificate `Solution/GramEntryCert.lean`. -/

namespace BGP212.Gram

open MeasureTheory BGP212.Var

variable {ι : Type*} [Fintype ι]

theorem simplexF_isClosed (R : ℝ) : IsClosed (simplexF ι R) := by
  have h1 : IsClosed {z : ι → ℝ | ∀ i, 0 ≤ z i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {z : ι → ℝ | ∑ i, z i ≤ R} :=
    isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  exact h1.inter h2

theorem simplexF_subset_Icc (R : ℝ) : simplexF ι R ⊆ Set.Icc 0 (fun _ => |R|) := by
  rintro z ⟨h0, hs⟩
  refine ⟨fun i => h0 i, fun i => ?_⟩
  have : z i ≤ ∑ j, z j := Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
  exact le_trans this (le_trans hs (le_abs_self R))

theorem simplexF_isCompact (R : ℝ) : IsCompact (simplexF ι R) :=
  isCompact_Icc.of_isClosed_subset (simplexF_isClosed R) (simplexF_subset_Icc R)

theorem simplexF_measurableSet (R : ℝ) : MeasurableSet (simplexF ι R) :=
  (simplexF_isClosed R).measurableSet

/-- Reindexing along `σ : Fin m ≃ ι`: integrals over `ι → ℝ` are integrals over `Fin m → ℝ`. -/
theorem integral_reindex {m : ℕ} (σ : Fin m ≃ ι) (F : (ι → ℝ) → ℝ) :
    ∫ z, F z = ∫ w : Fin m → ℝ, F (fun i => w (σ.symm i)) := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : ι => ℝ) σ
  have := h.integral_comp' F
  rw [← this]
  congr 1
  funext w
  congr 1
  funext i
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]

/-- **(10.1) over any finite index type** (V1 transported along `Fintype.equivFin`). -/
theorem simplexF_integral (R : ℝ) (hR : 0 ≤ R) (e : ι → ℕ) :
    ∫ z in simplexF ι R, ∏ i, z i ^ e i = momentF ι R e := by
  set σ : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  rw [← integral_indicator (simplexF_measurableSet R), integral_reindex σ]
  have hset : ∀ w : Fin (Fintype.card ι) → ℝ,
      ((fun i => w (σ.symm i)) ∈ simplexF ι R ↔ w ∈ simplex (Fintype.card ι) R) := by
    intro w
    simp only [simplexF, simplex, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h0, hs⟩
      refine ⟨fun j => by simpa using h0 (σ j), ?_⟩
      rwa [Equiv.sum_comp σ.symm w] at hs
    · rintro ⟨h0, hs⟩
      exact ⟨fun i => h0 _, by rwa [Equiv.sum_comp σ.symm (fun j => w j)]⟩
  have hfun : (fun w : Fin (Fintype.card ι) → ℝ =>
      (simplexF ι R).indicator (fun z => ∏ i, z i ^ e i) (fun i => w (σ.symm i))) =
      (simplex (Fintype.card ι) R).indicator (fun w => ∏ j, w j ^ e (σ j)) := by
    funext w
    by_cases hw : w ∈ simplex (Fintype.card ι) R
    · rw [Set.indicator_of_mem ((hset w).mpr hw), Set.indicator_of_mem hw]
      exact (Equiv.prod_comp σ (fun i => w (σ.symm i) ^ e i)).symm.trans (by simp)
    · rw [Set.indicator_of_notMem (fun h => hw ((hset w).mp h)), Set.indicator_of_notMem hw]
  rw [hfun, integral_indicator (simplex_measurableSet _ _), simplex_integral _ _ _ hR]
  simp only [momentR, momentF]
  rw [Equiv.sum_comp σ e, Equiv.prod_comp σ (fun i => ((e i).factorial : ℝ))]


/-! ## Fubini over a product of a set `A` and a simplex fibre -/

variable {κ : Type*} [Fintype κ]

/-- The region `{(z, w) : z ∈ A, w ∈ simplexF κ (M − Σ z)}`. -/
def fibred (A : Set (ι → ℝ)) (κ : Type*) [Fintype κ] (M : ℝ) : Set ((ι → ℝ) × (κ → ℝ)) :=
  {p | p.1 ∈ A ∧ p.2 ∈ simplexF κ (M - ∑ i, p.1 i)}

theorem fibred_isClosed {A : Set (ι → ℝ)} (hA : IsClosed A) (M : ℝ) :
    IsClosed (fibred A κ M) := by
  have h1 : IsClosed {p : (ι → ℝ) × (κ → ℝ) | p.1 ∈ A} := hA.preimage continuous_fst
  have h2 : IsClosed {p : (ι → ℝ) × (κ → ℝ) | ∀ j, 0 ≤ p.2 j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const
      ((continuous_apply j).comp continuous_snd)
  have h3 : IsClosed {p : (ι → ℝ) × (κ → ℝ) | ∑ j, p.2 j ≤ M - ∑ i, p.1 i} :=
    isClosed_le (continuous_finsetSum _ fun j _ => (continuous_apply j).comp continuous_snd)
      (continuous_const.sub (continuous_finsetSum _ fun i _ => (continuous_apply i).comp continuous_fst))
  have : fibred A κ M = {p | p.1 ∈ A} ∩ ({p | ∀ j, 0 ≤ p.2 j} ∩ {p | ∑ j, p.2 j ≤ M - ∑ i, p.1 i}) := by
    ext p; simp [fibred, simplexF]
  rw [this]
  exact h1.inter (h2.inter h3)

theorem fibred_isCompact {A : Set (ι → ℝ)} (hA : IsCompact A) (hA0 : ∀ z ∈ A, ∀ i, 0 ≤ z i)
    (M : ℝ) : IsCompact (fibred A κ M) := by
  refine (hA.prod (simplexF_isCompact (ι := κ) |M|)).of_isClosed_subset
    (fibred_isClosed hA.isClosed M) ?_
  rintro ⟨z, w⟩ ⟨hz, hw0, hws⟩
  refine ⟨hz, hw0, le_trans hws ?_⟩
  have : 0 ≤ ∑ i, z i := Finset.sum_nonneg fun i _ => hA0 z hz i
  linarith [le_abs_self M]

/-- **Fubini on a fibred region**: integrate the simplex fibre first. -/
theorem integral_fibred {A : Set (ι → ℝ)} (hA : IsCompact A) (hA0 : ∀ z ∈ A, ∀ i, 0 ≤ z i)
    (M : ℝ) (F : (ι → ℝ) × (κ → ℝ) → ℝ) (hF : Continuous F) :
    ∫ p, (fibred A κ M).indicator F p =
      ∫ z in A, ∫ w in simplexF κ (M - ∑ i, z i), F (z, w) := by
  have hmeas : MeasurableSet (fibred A κ M) := (fibred_isClosed hA.isClosed M).measurableSet
  have hint : Integrable ((fibred A κ M).indicator F) (volume.prod volume) := by
    rw [integrable_indicator_iff hmeas]
    exact hF.continuousOn.integrableOn_compact (fibred_isCompact hA hA0 M)
  rw [show (volume : Measure ((ι → ℝ) × (κ → ℝ))) = volume.prod volume from rfl,
    integral_prod _ hint, ← integral_indicator hA.isClosed.measurableSet]
  congr 1
  funext z
  by_cases hz : z ∈ A
  · rw [Set.indicator_of_mem hz, ← integral_indicator (simplexF_measurableSet _)]
    congr 1
    funext w
    by_cases hw : w ∈ simplexF κ (M - ∑ i, z i)
    · rw [Set.indicator_of_mem (show (z, w) ∈ fibred A κ M from ⟨hz, hw⟩), Set.indicator_of_mem hw]
    · rw [Set.indicator_of_notMem (fun h => hw h.2), Set.indicator_of_notMem hw]
  · rw [Set.indicator_of_notMem hz]
    have : (fun w => (fibred A κ M).indicator F (z, w)) = fun _ => 0 := by
      funext w; exact Set.indicator_of_notMem (fun h => hz h.1) _
    rw [this, integral_zero]


/-! ## Weighted simplex moments -/

theorem momentF_unit (r : ℝ) (q : ℕ) :
    momentF Unit r (fun _ => q) = r ^ (q + 1) * (q.factorial : ℝ) / ((q + 1).factorial : ℝ) := by
  simp [momentF, add_comm]

/-- `∫_{simplexF ι c} zᵉ (c − Σ z)^{q+1} = c^{|ι| + Σe + q + 1} ∏ eᵢ! (q+1)! / (|ι| + Σe + q + 1)!`,
from (10.1) on `ι ⊕ Unit` and Fubini. -/
theorem weighted_succ (c : ℝ) (hc : 0 ≤ c) (e : ι → ℕ) (q : ℕ) :
    ∫ z in simplexF ι c, (∏ i, z i ^ e i) * (c - ∑ i, z i) ^ (q + 1) =
      c ^ (Fintype.card ι + ∑ i, e i + (q + 1)) * (∏ i, ((e i).factorial : ℝ)) *
        ((q + 1).factorial : ℝ) / ((Fintype.card ι + ∑ i, e i + (q + 1)).factorial : ℝ) := by
  -- (10.1) on `ι ⊕ Unit`
  have hY := simplexF_integral (ι := ι ⊕ Unit) c hc (Sum.elim e fun _ => q)
  have hΦ := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : ι ⊕ Unit => ℝ)
  rw [← integral_indicator (simplexF_measurableSet _), ← hΦ.integral_comp'] at hY
  have hfun : (fun p : (ι → ℝ) × (Unit → ℝ) => (simplexF (ι ⊕ Unit) c).indicator
      (fun y => ∏ i, y i ^ (Sum.elim e (fun _ => q)) i)
      ((MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ Unit => ℝ).symm p)) =
      (fibred (simplexF ι c) Unit c).indicator (fun p => (∏ i, p.1 i ^ e i) * p.2 () ^ q) := by
    funext ⟨z, w⟩
    have hmem : (MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ Unit => ℝ).symm (z, w) ∈
        simplexF (ι ⊕ Unit) c ↔ (z, w) ∈ fibred (simplexF ι c) Unit c := by
      simp only [simplexF, fibred, Set.mem_ofPred_eq, Sum.forall, Fintype.sum_sum_type,
        MeasurableEquiv.coe_sumPiEquivProdPi_symm, Equiv.sumPiEquivProdPi_symm_apply,
        Fintype.univ_unit, Finset.sum_singleton]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, by linarith [h2 ()]⟩, h2, by linarith⟩
      · rintro ⟨⟨h1, _⟩, h2, h3⟩
        exact ⟨⟨h1, h2⟩, by linarith⟩
    by_cases h : (z, w) ∈ fibred (simplexF ι c) Unit c
    · rw [Set.indicator_of_mem (hmem.mpr h), Set.indicator_of_mem h]
      simp [Fintype.prod_sum_type, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
        Equiv.sumPiEquivProdPi_symm_apply]
    · rw [Set.indicator_of_notMem (fun h' => h (hmem.mp h')), Set.indicator_of_notMem h]
  rw [hfun, integral_fibred (simplexF_isCompact c) (fun z hz => hz.1) c _ (by fun_prop)] at hY
  have hinner : ∀ z ∈ simplexF ι c,
      ∫ w in simplexF Unit (c - ∑ i, z i), (∏ i, z i ^ e i) * w () ^ q =
        (q.factorial : ℝ) / ((q + 1).factorial : ℝ) * ((∏ i, z i ^ e i) * (c - ∑ i, z i) ^ (q + 1)) := by
    intro z hz
    have h0 : 0 ≤ c - ∑ i, z i := by linarith [hz.2]
    rw [MeasureTheory.integral_const_mul]
    have := simplexF_integral (ι := Unit) (c - ∑ i, z i) h0 (fun _ => q)
    simp only [Fintype.univ_unit, Finset.prod_singleton] at this
    rw [this, momentF_unit]
    ring
  rw [setIntegral_congr_fun (simplexF_measurableSet c) hinner, MeasureTheory.integral_const_mul] at hY
  have hq : ((q.factorial : ℝ) / ((q + 1).factorial : ℝ)) ≠ 0 := by positivity
  rw [← mul_right_inj' hq, hY]
  simp only [momentF, Fintype.card_sum, Fintype.card_unit, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Fintype.univ_unit, Finset.sum_singleton, Fintype.prod_sum_type,
    Finset.prod_singleton]
  rw [show Fintype.card ι + 1 + (∑ i, e i + q) = Fintype.card ι + ∑ i, e i + (q + 1) by ring]
  rw [Nat.factorial_succ q]
  push_cast
  field_simp

/-- **Weighted simplex moment**: `∫_{simplexF ι c} zᵉ (c − Σ z)^p
= c^{|ι| + Σe + p} ∏ eᵢ! p! / (|ι| + Σe + p)!` for `c ≥ 0`. -/
theorem weighted_simplexF (c : ℝ) (hc : 0 ≤ c) (e : ι → ℕ) (p : ℕ) :
    ∫ z in simplexF ι c, (∏ i, z i ^ e i) * (c - ∑ i, z i) ^ p =
      c ^ (Fintype.card ι + ∑ i, e i + p) * (∏ i, ((e i).factorial : ℝ)) *
        (p.factorial : ℝ) / ((Fintype.card ι + ∑ i, e i + p).factorial : ℝ) := by
  cases p with
  | zero =>
      simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, add_zero]
      exact simplexF_integral c hc e
  | succ q => exact weighted_succ c hc e q


/-- A weight `(M − Σ z)^q` with `M ≥ c` expands around `c`:
`∫_{simplexF ι c} zᵉ (M − Σ z)^q = Σⱼ C(q, j) (M − c)^{q−j} ∫ zᵉ (c − Σ z)^j`. -/
theorem shifted_weighted (c M : ℝ) (hc : 0 ≤ c) (e : ι → ℕ) (q : ℕ) :
    ∫ z in simplexF ι c, (∏ i, z i ^ e i) * (M - ∑ i, z i) ^ q =
      ∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * (M - c) ^ (q - j) *
        (c ^ (Fintype.card ι + ∑ i, e i + j) * (∏ i, ((e i).factorial : ℝ)) * (j.factorial : ℝ) /
          ((Fintype.card ι + ∑ i, e i + j).factorial : ℝ)) := by
  have hexp : ∀ z : ι → ℝ, (∏ i, z i ^ e i) * (M - ∑ i, z i) ^ q =
      ∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * (M - c) ^ (q - j) *
        ((∏ i, z i ^ e i) * (c - ∑ i, z i) ^ j) := by
    intro z
    rw [show M - ∑ i, z i = (c - ∑ i, z i) + (M - c) by ring, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [MeasureTheory.integral_const_mul, weighted_simplexF c hc e j]
  · intro j _
    exact ((by fun_prop : Continuous fun z : ι → ℝ => (q.choose j : ℝ) * (M - c) ^ (q - j) *
      ((∏ i, z i ^ e i) * (c - ∑ i, z i) ^ j)).continuousOn.integrableOn_compact
        (simplexF_isCompact c))


/-! ## The two-group pieces over `Fin N` -/

theorem pieceSet_measurableSet (N : ℕ) (R : Finset (Fin N)) (c M : ℝ) :
    MeasurableSet (pieceSet N R c M) := by
  have h1 : IsClosed {y : Fin N → ℝ | ∀ i, 0 ≤ y i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {y : Fin N → ℝ | ∑ i ∈ R, y i ≤ c} :=
    isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  have h3 : IsClosed {y : Fin N → ℝ | ∑ i, y i ≤ M} :=
    isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  exact (h1.inter (h2.inter h3)).measurableSet

theorem pieceSet_empty (N : ℕ) (R : Finset (Fin N)) (c M : ℝ) (h : ¬(0 ≤ c ∧ 0 ≤ M)) :
    pieceSet N R c M = ∅ := by
  ext y
  simp only [pieceSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro h0 hR hM
  exact h ⟨le_trans (Finset.sum_nonneg fun i _ => h0 i) hR,
    le_trans (Finset.sum_nonneg fun i _ => h0 i) hM⟩

/-- The split `y ↦ (y|_R, y|_{Rᶜ})` and its effect on the sums. -/
theorem split_sums (N : ℕ) (R : Finset (Fin N)) (z : {i // i ∈ R} → ℝ) (w : {i // i ∉ R} → ℝ) :
    let y := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => ℝ) (· ∈ R)).symm (z, w)
    (∀ i : {i // i ∈ R}, y i = z i) ∧ (∀ i : {i // i ∉ R}, y i = w i) ∧
      ∑ i ∈ R, y i = ∑ i, z i ∧ ∑ i, y i = ∑ i, z i + ∑ i, w i := by
  intro y
  have h1 : ∀ i : {i // i ∈ R}, y i = z i := fun i => by
    simp [y, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply, i.2]
  have h2 : ∀ i : {i // i ∉ R}, y i = w i := fun i => by
    simp [y, MeasurableEquiv.piEquivPiSubtypeProd_symm_apply, i.2]
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [Finset.sum_subtype R (fun _ => Iff.rfl) y]
    exact Finset.sum_congr rfl fun i _ => h1 i
  · rw [← Fintype.sum_subtype_add_sum_subtype (· ∈ R) y]
    have e1 : ∑ i : {i // i ∈ R}, y i = ∑ i, z i := Finset.sum_congr rfl fun i _ => h1 i
    have e2 : ∑ i : {i // i ∉ R}, y i = ∑ i, w i := Finset.sum_congr rfl fun i _ => h2 i
    rw [← e1, ← e2]
    congr 1
    exact Finset.sum_congr (by congr; exact Subsingleton.elim _ _) fun _ _ => rfl

theorem card_compl_subtype (N : ℕ) (R : Finset (Fin N)) :
    Fintype.card {i // i ∉ R} = N - R.card := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

/-- Integrals over a piece become fibred integrals over `(y|_R, y|_{Rᶜ})`. -/
theorem piece_as_fibred (N : ℕ) (R : Finset (Fin N)) (c M : ℝ) (G : (Fin N → ℝ) → ℝ) :
    ∫ y in pieceSet N R c M, G y =
      ∫ p, (fibred (simplexF {i // i ∈ R} (min c M)) {i // i ∉ R} M).indicator
        (fun p => G ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => ℝ) (· ∈ R)).symm p)) p := by
  set Φ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => ℝ) (· ∈ R) with hΦdef
  have hΦ : MeasurePreserving Φ.symm volume volume := by
    convert (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin N => ℝ) (· ∈ R)).symm Φ <;> rfl
  rw [← integral_indicator (pieceSet_measurableSet N R c M), ← hΦ.integral_comp']
  congr 1
  funext ⟨z, w⟩
  obtain ⟨-, -, hR, hall⟩ := split_sums N R z w
  rw [← hΦdef] at hR hall
  have hmem : Φ.symm (z, w) ∈ pieceSet N R c M ↔
      (z, w) ∈ fibred (simplexF {i // i ∈ R} (min c M)) {i // i ∉ R} M := by
    simp only [pieceSet, fibred, simplexF, Set.mem_ofPred_eq, hR, hall, le_min_iff]
    constructor
    · rintro ⟨h0, hc, hM⟩
      have hz : ∀ i, 0 ≤ z i := fun i => by
        have := h0 i; rwa [(split_sums N R z w).1 i] at this
      have hw : ∀ i, 0 ≤ w i := fun i => by
        have := h0 i; rwa [(split_sums N R z w).2.1 i] at this
      have : 0 ≤ ∑ i, w i := Finset.sum_nonneg fun i _ => hw i
      exact ⟨⟨hz, hc, by linarith⟩, hw, by linarith⟩
    · rintro ⟨⟨hz, hc, -⟩, hw, hM⟩
      refine ⟨fun i => ?_, hc, by linarith⟩
      by_cases hi : i ∈ R
      · have := (split_sums N R z w).1 ⟨i, hi⟩; simp only at this; rw [this]; exact hz _
      · have := (split_sums N R z w).2.1 ⟨i, hi⟩; simp only at this; rw [this]; exact hw _
  by_cases h : (z, w) ∈ fibred (simplexF {i // i ∈ R} (min c M)) {i // i ∉ R} M
  · rw [Set.indicator_of_mem (hmem.mpr h), Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem (fun h' => h (hmem.mp h')), Set.indicator_of_notMem h]


theorem single_facts {κ : Type*} [Fintype κ] [DecidableEq κ] (b : κ) (t : ℕ) (x : κ → ℝ) :
    (∏ i, x i ^ (if i = b then t else 0)) = x b ^ t ∧
      (∑ i, (if i = b then t else 0)) = t ∧
      (∏ i, (((if i = b then t else 0).factorial : ℕ) : ℝ)) = (t.factorial : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [pow_zero, Finset.prod_ite_eq']
  · simp [Finset.sum_ite_eq']
  · simp [apply_ite Nat.factorial, Finset.prod_ite_eq']

/-- **A piece, special coordinate rough** (`a ∈ R`). -/
theorem piece_integral_mem (N : ℕ) (R : Finset (Fin N)) (a : Fin N) (ha : a ∈ R) (t p : ℕ)
    (c M : ℝ) :
    ∫ y in pieceSet N R c M, y a ^ t * (M - ∑ i, y i) ^ p =
      twoGroup (N - R.card) R.card t 0 p c M := by
  classical
  by_cases h : 0 ≤ c ∧ 0 ≤ M
  swap
  · rw [pieceSet_empty N R c M h, Measure.restrict_empty, integral_zero_measure, twoGroup, if_neg h]
  have hc' : 0 ≤ min c M := le_min h.1 h.2
  rw [piece_as_fibred]
  have hF : (fun pr : ({i // i ∈ R} → ℝ) × ({i // i ∉ R} → ℝ) =>
      ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => ℝ) (· ∈ R)).symm pr) a ^ t *
        (M - ∑ i, ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => ℝ) (· ∈ R)).symm pr) i) ^ p) =
      fun pr => pr.1 ⟨a, ha⟩ ^ t * ((M - ∑ i, pr.1 i) - ∑ i, pr.2 i) ^ p := by
    funext ⟨z, w⟩
    obtain ⟨h1, -, -, hall⟩ := split_sums N R z w
    rw [hall, show M - (∑ i, z i + ∑ i, w i) = (M - ∑ i, z i) - ∑ i, w i by ring]
    have := h1 ⟨a, ha⟩
    simp only at this
    rw [this]
  rw [hF, integral_fibred (simplexF_isCompact _) (fun z hz => hz.1) M _ (by fun_prop)]
  have hinner : ∀ z ∈ simplexF {i // i ∈ R} (min c M),
      ∫ w in simplexF {i // i ∉ R} (M - ∑ i, z i), z ⟨a, ha⟩ ^ t * ((M - ∑ i, z i) - ∑ i, w i) ^ p =
        (p.factorial : ℝ) / ((N - R.card + p).factorial : ℝ) *
          ((∏ i, z i ^ (if i = ⟨a, ha⟩ then t else 0)) * (M - ∑ i, z i) ^ (N - R.card + 0 + p)) := by
    intro z hz
    have h0 : 0 ≤ M - ∑ i, z i := by linarith [hz.2, min_le_right c M]
    rw [MeasureTheory.integral_const_mul]
    have hw := weighted_simplexF (ι := {i // i ∉ R}) (M - ∑ i, z i) h0 (fun _ => 0) p
    simp only [pow_zero, Finset.prod_const_one, one_mul, Finset.sum_const_zero, add_zero,
      Nat.factorial_zero, Nat.cast_one, mul_one, card_compl_subtype] at hw
    rw [hw, (single_facts (⟨a, ha⟩ : {i // i ∈ R}) t z).1]
    ring
  rw [setIntegral_congr_fun (simplexF_measurableSet _) hinner, MeasureTheory.integral_const_mul,
    shifted_weighted (min c M) M hc']
  obtain ⟨-, hsum, hprod⟩ := single_facts (⟨a, ha⟩ : {i // i ∈ R}) t (fun _ => (0 : ℝ))
  rw [hsum, hprod, twoGroup, if_pos h, Fintype.card_coe]
  simp only [add_zero, Nat.factorial_zero, Nat.cast_one, one_mul, wsVal]

/-- **A piece, special coordinate smooth** (`a ∉ R`). -/
theorem piece_integral_notMem (N : ℕ) (R : Finset (Fin N)) (a : Fin N) (ha : a ∉ R) (t p : ℕ)
    (c M : ℝ) :
    ∫ y in pieceSet N R c M, y a ^ t * (M - ∑ i, y i) ^ p =
      twoGroup (N - R.card) R.card 0 t p c M := by
  classical
  by_cases h : 0 ≤ c ∧ 0 ≤ M
  swap
  · rw [pieceSet_empty N R c M h, Measure.restrict_empty, integral_zero_measure, twoGroup, if_neg h]
  have hc' : 0 ≤ min c M := le_min h.1 h.2
  rw [piece_as_fibred]
  have hF : (fun pr : ({i // i ∈ R} → ℝ) × ({i // i ∉ R} → ℝ) =>
      ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => ℝ) (· ∈ R)).symm pr) a ^ t *
        (M - ∑ i, ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => ℝ) (· ∈ R)).symm pr) i) ^ p) =
      fun pr => pr.2 ⟨a, ha⟩ ^ t * ((M - ∑ i, pr.1 i) - ∑ i, pr.2 i) ^ p := by
    funext ⟨z, w⟩
    obtain ⟨-, h2, -, hall⟩ := split_sums N R z w
    rw [hall, show M - (∑ i, z i + ∑ i, w i) = (M - ∑ i, z i) - ∑ i, w i by ring]
    have := h2 ⟨a, ha⟩
    simp only at this
    rw [this]
  rw [hF, integral_fibred (simplexF_isCompact _) (fun z hz => hz.1) M _ (by fun_prop)]
  have hinner : ∀ z ∈ simplexF {i // i ∈ R} (min c M),
      ∫ w in simplexF {i // i ∉ R} (M - ∑ i, z i), w ⟨a, ha⟩ ^ t * ((M - ∑ i, z i) - ∑ i, w i) ^ p =
        (t.factorial : ℝ) * (p.factorial : ℝ) / ((N - R.card + t + p).factorial : ℝ) *
          ((∏ i, z i ^ (fun _ => 0 : {i // i ∈ R} → ℕ) i) * (M - ∑ i, z i) ^ (N - R.card + t + p)) := by
    intro z hz
    have h0 : 0 ≤ M - ∑ i, z i := by linarith [hz.2, min_le_right c M]
    have hw := weighted_simplexF (ι := {i // i ∉ R}) (M - ∑ i, z i) h0
      (fun i => if i = ⟨a, ha⟩ then t else 0) p
    obtain ⟨-, hs1, hf1⟩ := single_facts (⟨a, ha⟩ : {i // i ∉ R}) t (fun _ => (0 : ℝ))
    simp only [hs1, hf1, card_compl_subtype] at hw
    have hp : ∀ w : {i // i ∉ R} → ℝ, w ⟨a, ha⟩ ^ t * ((M - ∑ i, z i) - ∑ i, w i) ^ p =
        (∏ i, w i ^ (if i = ⟨a, ha⟩ then t else 0)) * ((M - ∑ i, z i) - ∑ i, w i) ^ p := by
      intro w; rw [(single_facts (⟨a, ha⟩ : {i // i ∉ R}) t w).1]
    simp_rw [hp]
    rw [hw]
    simp only [pow_zero, Finset.prod_const_one, one_mul]
    ring
  rw [setIntegral_congr_fun (simplexF_measurableSet _) hinner, MeasureTheory.integral_const_mul,
    shifted_weighted (min c M) M hc']
  rw [twoGroup, if_pos h, Fintype.card_coe]
  simp only [Finset.sum_const_zero, add_zero, Finset.prod_const, Nat.factorial_zero, Nat.cast_one,
    one_pow, mul_one, wsVal]


/-! ## The support, its pieces, and inclusion–exclusion -/

theorem mem_roughSet {N : ℕ} (g : ℝ) (x : Fin N → ℝ) (i : Fin N) : i ∈ roughSet g x ↔ g < x i := by
  classical
  unfold roughSet
  simp

theorem Qset_measurableSet {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (R K : Finset (Fin N)) :
    MeasurableSet (Qset g L C R K) := by
  have h1 : IsClosed {x : Fin N → ℝ | ∀ i, 0 ≤ x i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsOpen {x : Fin N → ℝ | ∀ i ∈ R ∪ K, g < x i} := by
    have : {x : Fin N → ℝ | ∀ i ∈ R ∪ K, g < x i} = ⋂ i ∈ R ∪ K, {x | g < x i} := by
      ext x; simp
    rw [this]
    exact isOpen_biInter_finset fun i _ => isOpen_lt continuous_const (continuous_apply i)
  have h3 : IsClosed {x : Fin N → ℝ | ∑ i, x i ≤ L} :=
    isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  have h4 : IsClosed {x : Fin N → ℝ | ∑ i ∈ R, x i ≤ C R.card} :=
    isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
  have : Qset g L C R K = {x | ∀ i, 0 ≤ x i} ∩ ({x | ∀ i ∈ R ∪ K, g < x i} ∩
      ({x | ∑ i, x i ≤ L} ∩ {x | ∑ i ∈ R, x i ≤ C R.card})) := by
    ext x; simp [Qset]
  rw [this]
  exact h1.measurableSet.inter (h2.measurableSet.inter (h3.measurableSet.inter h4.measurableSet))

theorem supportT_measurableSet (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) :
    MeasurableSet (supportT N g L C) := by
  classical
  have hR : ∀ R : Finset (Fin N), MeasurableSet {x : Fin N → ℝ | roughSet g x = R} := by
    intro R
    have : {x : Fin N → ℝ | roughSet g x = R} =
        ⋂ i, {x | (g < x i) ↔ i ∈ R} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.ext_iff, mem_roughSet]
    rw [this]
    refine MeasurableSet.iInter fun i => ?_
    by_cases hi : i ∈ R
    · simpa [hi] using measurableSet_lt measurable_const (measurable_pi_apply i)
    · simpa [hi] using measurableSet_le (measurable_pi_apply i) measurable_const
  have : supportT N g L C = {x | ∀ i, 0 ≤ x i} ∩ ({x | ∑ i, x i ≤ L} ∩
      ⋃ R : Finset (Fin N), ({x | roughSet g x = R} ∩ {x | ∑ i ∈ R, x i ≤ C R.card})) := by
    ext x
    simp only [supportT, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iUnion]
    constructor
    · rintro ⟨h0, hL, hC⟩; exact ⟨h0, hL, roughSet g x, rfl, hC⟩
    · rintro ⟨h0, hL, R, rfl, hC⟩; exact ⟨h0, hL, hC⟩
  rw [this]
  have h1 : MeasurableSet {x : Fin N → ℝ | ∀ i, 0 ≤ x i} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i)
  have h2 : MeasurableSet {x : Fin N → ℝ | ∑ i, x i ≤ L} :=
    measurableSet_le (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const
  refine h1.inter (h2.inter (MeasurableSet.iUnion fun R => (hR R).inter ?_))
  exact measurableSet_le (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const

/-- `Σ_{K ⊆ S} (−1)^{|K|} = [S = ∅]` over `ℝ`. -/
theorem sum_powerset_neg_one {α : Type*} [DecidableEq α] (S : Finset α) :
    ∑ K ∈ S.powerset, ((-1 : ℝ) ^ K.card) = if S = ∅ then 1 else 0 := by
  have h := congrArg (Int.cast : ℤ → ℝ) (Finset.sum_powerset_neg_one_pow_card (x := S))
  push_cast at h
  rw [h]

/-- **Pointwise inclusion–exclusion.** The indicator of the support is the signed sum of the
indicators of the pieces `Qset R K`, `K ⊆ Rᶜ`. -/
theorem indicator_supportT {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (F : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    (supportT N g L C).indicator F x =
      ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * (Qset g L C R K).indicator F x := by
  classical
  set R0 := roughSet g x with hR0
  have hrow : ∀ R : Finset (Fin N),
      ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * (Qset g L C R K).indicator F x =
        if R = R0 then (if (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ L ∧ ∑ i ∈ R, x i ≤ C R.card then F x else 0)
        else 0 := by
    intro R
    have hmem : ∀ K, x ∈ Qset g L C R K ↔
        ((∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ L ∧ ∑ i ∈ R, x i ≤ C R.card ∧ R ⊆ R0) ∧ K ⊆ R0 := by
      intro K
      simp only [Qset, Set.mem_setOf_eq, Finset.mem_union]
      constructor
      · rintro ⟨h0, hg, hL, hC⟩
        exact ⟨⟨h0, hL, hC, fun i hi => (mem_roughSet g x i).mpr (hg i (Or.inl hi))⟩,
          fun i hi => (mem_roughSet g x i).mpr (hg i (Or.inr hi))⟩
      · rintro ⟨⟨h0, hL, hC, hRs⟩, hKs⟩
        refine ⟨h0, fun i hi => ?_, hL, hC⟩
        rcases hi with hi | hi
        · exact (mem_roughSet g x i).mp (hRs hi)
        · exact (mem_roughSet g x i).mp (hKs hi)
    by_cases hb : (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ L ∧ ∑ i ∈ R, x i ≤ C R.card ∧ R ⊆ R0
    · have hsum : ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * (Qset g L C R K).indicator F x =
          F x * ∑ K ∈ (Rᶜ ∩ R0).powerset, (-1 : ℝ) ^ K.card := by
        rw [Finset.mul_sum]
        have hfilt : (Rᶜ ∩ R0).powerset = Rᶜ.powerset.filter (· ⊆ R0) := by
          ext K; simp [Finset.subset_inter_iff]
        rw [hfilt, Finset.sum_filter]
        refine Finset.sum_congr rfl fun K _ => ?_
        by_cases hK : K ⊆ R0
        · rw [Set.indicator_of_mem ((hmem K).mpr ⟨hb, hK⟩), if_pos hK]; ring
        · rw [Set.indicator_of_notMem (fun h => hK ((hmem K).mp h).2), if_neg hK]; ring
      rw [hsum, sum_powerset_neg_one]
      have hiff : Rᶜ ∩ R0 = ∅ ↔ R = R0 := by
        constructor
        · intro h
          refine Finset.Subset.antisymm hb.2.2.2 fun i hi => ?_
          by_contra hiR
          have : i ∈ Rᶜ ∩ R0 := Finset.mem_inter.mpr ⟨Finset.mem_compl.mpr hiR, hi⟩
          rw [h] at this; simp at this
        · rintro rfl; ext i; simp
      by_cases hRR : R = R0
      · rw [if_pos (hiff.mpr hRR), if_pos hRR, if_pos ⟨hb.1, hb.2.1, hb.2.2.1⟩, mul_one]
      · rw [if_neg (fun h => hRR (hiff.mp h)), if_neg hRR, mul_zero]
    · have hz : ∀ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * (Qset g L C R K).indicator F x = 0 := by
        intro K _
        rw [Set.indicator_of_notMem (fun h => hb ((hmem K).mp h).1), mul_zero]
      rw [Finset.sum_eq_zero hz]
      by_cases hRR : R = R0
      · subst hRR
        rw [if_pos rfl, if_neg]
        rintro ⟨h0, hL, hC⟩
        exact hb ⟨h0, hL, hC, Finset.Subset.refl _⟩
      · rw [if_neg hRR]
  rw [Finset.sum_congr rfl fun R _ => hrow R, Finset.sum_ite_eq' Finset.univ R0]
  simp only [Finset.mem_univ, if_true, Set.indicator_apply, supportT, Set.mem_setOf_eq, ← hR0]


/-! ## Translation of a piece -/

theorem sum_shiftV {N : ℕ} (g : ℝ) (S T : Finset (Fin N)) (hT : T ⊆ S) :
    ∑ i ∈ T, shiftV g S i = T.card * g := by
  classical
  unfold shiftV
  rw [Finset.sum_congr rfl fun i hi => if_pos (hT hi)]
  simp

theorem pieceSet_subset_simplexF (N : ℕ) (R : Finset (Fin N)) (c M : ℝ) :
    pieceSet N R c M ⊆ simplexF (Fin N) M := fun _ hy => ⟨hy.1, hy.2.2⟩

theorem integrableOn_pieceSet (N : ℕ) (R : Finset (Fin N)) (c M : ℝ) (G : (Fin N → ℝ) → ℝ)
    (hG : Continuous G) : IntegrableOn G (pieceSet N R c M) :=
  (hG.continuousOn.integrableOn_compact (simplexF_isCompact (ι := Fin N) M)).mono_set
    (pieceSet_subset_simplexF N R c M)

/-- **Translation**: a piece `Qset R K` (`K ⊆ Rᶜ`) is, after `x = y + g·1_{R∪K}`, the closed piece
`pieceSet R (C|R| − |R|g) (L − (|R| + |K|)g)` up to the null faces `yᵢ = 0`. -/
theorem integral_Qset {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (R K : Finset (Fin N))
    (hRK : Disjoint R K) (F : (Fin N → ℝ) → ℝ) :
    ∫ x, (Qset g L C R K).indicator F x =
      ∫ y in pieceSet N R (C R.card - R.card * g) (L - (R.card + K.card) * g),
        F (y + shiftV g (R ∪ K)) := by
  classical
  set v := shiftV g (R ∪ K) with hv
  set S := R ∪ K
  rw [← integral_add_right_eq_self (μ := volume) (fun x => (Qset g L C R K).indicator F x) v]
  set Q' := {y : Fin N → ℝ | y + v ∈ Qset g L C R K} with hQ'
  have hQ'meas : MeasurableSet Q' :=
    (Qset_measurableSet g L C R K).preimage (measurable_id.add_const v)
  have hfun : (fun y => (Qset g L C R K).indicator F (y + v)) = Q'.indicator (fun y => F (y + v)) := by
    funext y
    by_cases h : y + v ∈ Qset g L C R K
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show y ∈ Q' from h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show y ∉ Q' from h)]
  rw [hfun, integral_indicator hQ'meas]
  have hcard : (S.card : ℝ) = R.card + K.card := by
    rw [Finset.card_union_of_disjoint hRK]; push_cast; ring
  have hsumAll : ∀ y : Fin N → ℝ, ∑ i, (y + v) i = ∑ i, y i + (R.card + K.card) * g := by
    intro y
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [show ∑ i, v i = ∑ i ∈ Finset.univ, shiftV g S i from rfl]
    rw [show (∑ i ∈ Finset.univ, shiftV g S i) = ∑ i ∈ S, shiftV g S i by
      rw [← Finset.sum_subset (Finset.subset_univ S)]
      intro i _ hi; simp [shiftV, hi]]
    rw [sum_shiftV g S S (Finset.Subset.refl _), hcard]
  have hsumR : ∀ y : Fin N → ℝ, ∑ i ∈ R, (y + v) i = ∑ i ∈ R, y i + R.card * g := by
    intro y
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    rw [sum_shiftV g S R Finset.subset_union_left]
  have hvS : ∀ i, i ∈ S → v i = g := fun i hi => by simp [hv, shiftV, hi]
  have hvS' : ∀ i, i ∉ S → v i = 0 := fun i hi => by simp [hv, shiftV, hi]
  -- `Q' ⊆ pieceSet` and the difference lies in the null faces
  have hsub : Q' ⊆ pieceSet N R (C R.card - R.card * g) (L - (R.card + K.card) * g) := by
    rintro y ⟨h0, hgt, hL, hC⟩
    refine ⟨fun i => ?_, ?_, ?_⟩
    · by_cases hi : i ∈ S
      · have := hgt i hi; simp only [Pi.add_apply, hvS i hi] at this; linarith
      · have := h0 i; simp only [Pi.add_apply, hvS' i hi] at this; linarith
    · rw [hsumR] at hC; linarith
    · rw [hsumAll] at hL; linarith
  have hdiff : pieceSet N R (C R.card - R.card * g) (L - (R.card + K.card) * g) \ Q' ⊆
      ⋃ i, {y : Fin N → ℝ | y i = 0} := by
    rintro y ⟨⟨h0, hC, hL⟩, hnot⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hall
    push_neg at hall
    apply hnot
    refine ⟨fun i => ?_, fun i hi => ?_, ?_, ?_⟩
    · by_cases hi : i ∈ S
      · simp only [Pi.add_apply, hvS i hi]; linarith [h0 i]
      · simp only [Pi.add_apply, hvS' i hi]; linarith [h0 i]
    · simp only [Pi.add_apply, hvS i hi]
      have := lt_of_le_of_ne (h0 i) (Ne.symm (hall i))
      linarith
    · rw [hsumAll]; linarith
    · rw [hsumR]; linarith
  have hnull : volume (⋃ i, {y : Fin N → ℝ | y i = 0}) = 0 := by
    refine measure_iUnion_null fun i => ?_
    rw [volume_pi]
    exact Measure.pi_hyperplane _ i 0
  have hae : Q' =ᵐ[volume] pieceSet N R (C R.card - R.card * g) (L - (R.card + K.card) * g) := by
    refine Filter.EventuallyLE.antisymm (Filter.Eventually.of_forall fun y hy => hsub hy) ?_
    rw [ae_le_set]
    exact measure_mono_null hdiff hnull
  exact setIntegral_congr_set hae


theorem sum_add_shiftV {N : ℕ} (g : ℝ) (R K : Finset (Fin N)) (hRK : Disjoint R K) (y : Fin N → ℝ) :
    ∑ i, (y + shiftV g (R ∪ K)) i = ∑ i, y i + (R.card + K.card) * g := by
  classical
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  rw [show (∑ i, shiftV g (R ∪ K) i) = ∑ i ∈ R ∪ K, shiftV g (R ∪ K) i by
    rw [← Finset.sum_subset (Finset.subset_univ (R ∪ K))]
    intro i _ hi; simp [shiftV, hi]]
  rw [sum_shiftV g _ _ (Finset.Subset.refl _), Finset.card_union_of_disjoint hRK]
  push_cast; ring

/-- The value of one inclusion–exclusion piece `(R, K)` for the integrand
`(L − Σ x)^p x_a^e`. -/
noncomputable def pieceTerm {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (a : Fin N) (e p : ℕ)
    (R K : Finset (Fin N)) : ℝ := by
  classical exact
  ∑ t ∈ Finset.range (e + 1), (e.choose t : ℝ) * (if a ∈ R ∪ K then g else 0) ^ (e - t) *
    (if a ∈ R then
      twoGroup (N - R.card) R.card t 0 p (C R.card - R.card * g) (L - (R.card + K.card) * g)
    else twoGroup (N - R.card) R.card 0 t p (C R.card - R.card * g) (L - (R.card + K.card) * g))

theorem integral_Qset_term {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (a : Fin N) (e p : ℕ)
    (R K : Finset (Fin N)) (hRK : Disjoint R K) :
    ∫ x, (Qset g L C R K).indicator (fun x => (L - ∑ i, x i) ^ p * x a ^ e) x =
      pieceTerm g L C a e p R K := by
  classical
  rw [integral_Qset g L C hg R K hRK]
  set M := L - (R.card + K.card) * g
  set c := C R.card - R.card * g
  have hexp : ∀ y : Fin N → ℝ, (L - ∑ i, (y + shiftV g (R ∪ K)) i) ^ p *
      (y + shiftV g (R ∪ K)) a ^ e =
      ∑ t ∈ Finset.range (e + 1), (e.choose t : ℝ) * (if a ∈ R ∪ K then g else 0) ^ (e - t) *
        (y a ^ t * (M - ∑ i, y i) ^ p) := by
    intro y
    rw [sum_add_shiftV g R K hRK, show L - (∑ i, y i + (R.card + K.card) * g) = M - ∑ i, y i by
      simp only [M]; ring]
    rw [Pi.add_apply, show shiftV g (R ∪ K) a = (if a ∈ R ∪ K then g else 0) by simp [shiftV],
      add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum]
  · unfold pieceTerm
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [MeasureTheory.integral_const_mul]
    congr 1
    by_cases ha : a ∈ R
    · rw [if_pos ha]; exact piece_integral_mem N R a ha t p c M
    · rw [if_neg ha]; exact piece_integral_notMem N R a ha t p c M
  · intro t _
    exact integrableOn_pieceSet N R c M _ (by fun_prop)

/-- **The integral over the support, unreduced**: a signed sum over all rough sets `R` and
inclusion–exclusion sets `K ⊆ Rᶜ`. -/
theorem integral_supportT_unreduced (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (a : Fin N)
    (e p : ℕ) :
    ∫ x in supportT N g L C, (L - ∑ i, x i) ^ p * x a ^ e =
      ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * pieceTerm g L C a e p R K := by
  classical
  rw [← integral_indicator (supportT_measurableSet N g L C)]
  simp_rw [indicator_supportT g L C]
  have hint : ∀ R K, Integrable ((Qset g L C R K).indicator
      (fun x : Fin N → ℝ => (L - ∑ i, x i) ^ p * x a ^ e)) := by
    intro R K
    rw [integrable_indicator_iff (Qset_measurableSet g L C R K)]
    refine ((by fun_prop : Continuous fun x : Fin N → ℝ => (L - ∑ i, x i) ^ p * x a ^ e).continuousOn.integrableOn_compact
      (simplexF_isCompact (ι := Fin N) L)).mono_set ?_
    exact fun x hx => ⟨hx.1, hx.2.2.1⟩
  rw [integral_finsetSum _ fun R _ => integrable_finset_sum _ fun K _ => (hint R K).const_mul _]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [integral_finsetSum _ fun K _ => (hint R K).const_mul _]
  refine Finset.sum_congr rfl fun K hK => ?_
  rw [MeasureTheory.integral_const_mul, integral_Qset_term g L C hg a e p R K]
  exact Finset.disjoint_left.mpr fun i hiR hiK =>
    (Finset.mem_compl.mp (Finset.mem_powerset.mp hK hiK)) hiR


/-! ## Counting: the sum over `(R, K)` by cardinalities -/

/-- Grouping a signed sum over rough sets `R` and `K ⊆ Rᶜ` by `|R|`, `|K|` and the position of a
distinguished coordinate `a` (in `R`, in `K`, or in neither). -/
theorem count_pieces (N : ℕ) (a : Fin N) (Hin Hk Hout : ℕ → ℕ → ℝ) :
    ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card *
        (if a ∈ R then Hin R.card K.card else if a ∈ K then Hk R.card K.card else Hout R.card K.card) =
      ∑ r ∈ Finset.range (N - 1 + 1), ((N - 1).choose r : ℝ) *
        ∑ k ∈ Finset.range (N - 1 - r + 1), ((N - 1 - r).choose k : ℝ) *
          ((-1 : ℝ) ^ k * Hin (r + 1) k + (-1 : ℝ) ^ k * Hout r k - (-1 : ℝ) ^ k * Hk r (k + 1)) := by
  classical
  set E := (Finset.univ : Finset (Fin N)).erase a with hEdef
  have haE : a ∉ E := Finset.notMem_erase a _
  have hEcard : E.card = N - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
  have huniv : (Finset.univ : Finset (Fin N)) = insert a E := (Finset.insert_erase (Finset.mem_univ a)).symm
  rw [show (∑ R : Finset (Fin N), _) = ∑ R ∈ (Finset.univ : Finset (Fin N)).powerset, _ by
    rw [Finset.powerset_univ]]
  rw [huniv, Finset.sum_powerset_insert haE, ← Finset.sum_add_distrib]
  -- each `R ⊆ E` contributes a function of `|R|`
  have hrow : ∀ R ∈ E.powerset,
      (∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card *
          (if a ∈ R then Hin R.card K.card else if a ∈ K then Hk R.card K.card else Hout R.card K.card)) +
        (∑ K ∈ (insert a R)ᶜ.powerset, (-1 : ℝ) ^ K.card *
          (if a ∈ insert a R then Hin (insert a R).card K.card
            else if a ∈ K then Hk (insert a R).card K.card else Hout (insert a R).card K.card)) =
      ∑ k ∈ Finset.range (N - 1 - R.card + 1), ((N - 1 - R.card).choose k : ℝ) *
        ((-1 : ℝ) ^ k * Hin (R.card + 1) k + (-1 : ℝ) ^ k * Hout R.card k -
          (-1 : ℝ) ^ k * Hk R.card (k + 1)) := by
    intro R hR
    have hRE : R ⊆ E := Finset.mem_powerset.mp hR
    have haR : a ∉ R := fun h => haE (hRE h)
    have hD : (E \ R).card = N - 1 - R.card := by rw [Finset.card_sdiff_of_subset hRE, hEcard]
    have haD : a ∉ E \ R := fun h => haE (Finset.mem_sdiff.mp h).1
    have hc1 : Rᶜ = insert a (E \ R) := by
      ext i
      by_cases hi : i = a
      · subst hi; simp [haR]
      · simp [hEdef, hi]
    have hc2 : (insert a R)ᶜ = E \ R := by
      ext i
      by_cases hi : i = a
      · subst hi; simp [hEdef]
      · simp [hEdef, hi]
    rw [hc1, hc2, Finset.sum_powerset_insert haD]
    have hcardI : (insert a R).card = R.card + 1 := Finset.card_insert_of_notMem haR
    -- three sums over `K ⊆ E \ R`, each a function of `|K|`
    have s1 : ∑ K ∈ (E \ R).powerset, (-1 : ℝ) ^ K.card *
        (if a ∈ R then Hin R.card K.card else if a ∈ K then Hk R.card K.card else Hout R.card K.card) =
        ∑ K ∈ (E \ R).powerset, (fun k => (-1 : ℝ) ^ k * Hout R.card k) K.card := by
      refine Finset.sum_congr rfl fun K hK => ?_
      have haK : a ∉ K := fun h => haD (Finset.mem_powerset.mp hK h)
      simp [haR, haK]
    have s2 : ∑ K ∈ (E \ R).powerset, (-1 : ℝ) ^ (insert a K).card *
        (if a ∈ R then Hin R.card (insert a K).card
          else if a ∈ insert a K then Hk R.card (insert a K).card else Hout R.card (insert a K).card) =
        ∑ K ∈ (E \ R).powerset, (fun k => -((-1 : ℝ) ^ k * Hk R.card (k + 1))) K.card := by
      refine Finset.sum_congr rfl fun K hK => ?_
      have haK : a ∉ K := fun h => haD (Finset.mem_powerset.mp hK h)
      simp only [haR, if_false, Finset.mem_insert_self, if_true, Finset.card_insert_of_notMem haK]
      ring
    have s3 : ∑ K ∈ (E \ R).powerset, (-1 : ℝ) ^ K.card *
        (if a ∈ insert a R then Hin (insert a R).card K.card
          else if a ∈ K then Hk (insert a R).card K.card else Hout (insert a R).card K.card) =
        ∑ K ∈ (E \ R).powerset, (fun k => (-1 : ℝ) ^ k * Hin (R.card + 1) k) K.card := by
      refine Finset.sum_congr rfl fun K _ => ?_
      simp [hcardI]
    rw [s1, s2, s3,
      Finset.sum_powerset_apply_card (fun k => (-1 : ℝ) ^ k * Hout R.card k) (x := E \ R),
      Finset.sum_powerset_apply_card (fun k => -((-1 : ℝ) ^ k * Hk R.card (k + 1))) (x := E \ R),
      Finset.sum_powerset_apply_card (fun k => (-1 : ℝ) ^ k * Hin (R.card + 1) k) (x := E \ R),
      hD, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hrow]
  rw [Finset.sum_powerset_apply_card (fun r => ∑ k ∈ Finset.range (N - 1 - r + 1),
    ((N - 1 - r).choose k : ℝ) * ((-1 : ℝ) ^ k * Hin (r + 1) k + (-1 : ℝ) ^ k * Hout r k -
      (-1 : ℝ) ^ k * Hk r (k + 1))), hEcard]
  simp only [nsmul_eq_mul]


/-! ## The closed form -/

theorem pieceTerm_eq {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (a : Fin N) (e p : ℕ) (R K : Finset (Fin N)) :
    pieceTerm g L C a e p R K =
      if a ∈ R then Hin N g L C e p R.card K.card
      else if a ∈ K then Hk N g L C e p R.card K.card else Hout N g L C e p R.card K.card := by
  classical
  unfold pieceTerm Hin Hk Hout
  by_cases ha : a ∈ R
  · simp [ha]
  · by_cases hK : a ∈ K
    · simp [ha, hK]
    · simp [ha, hK]

/-- **The integral over the support in closed form**, for any cap function `C`, any `g ≥ 0`,
any `L`, and any coordinate `a`. -/
theorem integral_supportT (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (a : Fin N) (e p : ℕ) :
    ∫ x in supportT N g L C, (L - ∑ i, x i) ^ p * x a ^ e = gramFormula N g L C e p := by
  rw [integral_supportT_unreduced N g L C hg a e p]
  simp_rw [pieceTerm_eq g L C a e p]
  rw [count_pieces N a (Hin N g L C e p) (Hk N g L C e p) (Hout N g L C e p)]
  rfl


/-! ## Boundary cases (zero-dimensional blocks) -/

/-- **Zero-dimensional simplex**: over an empty index type the simplex is the single point of
`ℝ⁰`, of measure one. -/
theorem simplexF_integral_isEmpty [IsEmpty ι] (R : ℝ) (hR : 0 ≤ R) (e : ι → ℕ) :
    ∫ z in simplexF ι R, ∏ i, z i ^ e i = 1 := by
  rw [simplexF_integral R hR e]
  simp [momentF, Fintype.card_eq_zero]

/-- **Empty rough set** (`R = ∅`): the cap of `R` is vacuous and the piece is the full simplex
of radius `M`; the value is the one-group weighted moment. -/
theorem piece_integral_empty (N : ℕ) (a : Fin N) (t p : ℕ) (c M : ℝ) (hc : 0 ≤ c) (hM : 0 ≤ M) :
    ∫ y in pieceSet N ∅ c M, y a ^ t * (M - ∑ i, y i) ^ p =
      M ^ (N + t + p) * (t.factorial : ℝ) * (p.factorial : ℝ) / ((N + t + p).factorial : ℝ) := by
  rw [piece_integral_notMem N ∅ a (Finset.notMem_empty a), Finset.card_empty, Nat.sub_zero,
    twoGroup, if_pos ⟨hc, hM⟩]
  set c' := min c M
  have hs : ∑ j ∈ Finset.range (N + t + p + 1), ((N + t + p).choose j : ℝ) *
      (M - c') ^ (N + t + p - j) * wsVal 0 0 j c' = M ^ (N + t + p) := by
    have h := add_pow c' (M - c') (N + t + p)
    rw [show c' + (M - c') = M by ring] at h
    rw [h]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : (j.factorial : ℝ) ≠ 0 := by positivity
    simp only [wsVal, zero_add, Nat.factorial_zero, Nat.cast_one, mul_one]
    field_simp
  rw [hs]
  ring

/-- **Full rough set** (`R = univ`): the complement block is `ℝ⁰`. -/
theorem piece_integral_univ (N : ℕ) (a : Fin N) (t p : ℕ) (c M : ℝ) :
    ∫ y in pieceSet N Finset.univ c M, y a ^ t * (M - ∑ i, y i) ^ p =
      twoGroup 0 N t 0 p c M := by
  rw [piece_integral_mem N Finset.univ a (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin,
    Nat.sub_self]

/-- **Zero-dimensional support**: in `ℝ⁰` the support is everything or nothing. -/
theorem supportT_zero_dim (g L : ℝ) (C : ℕ → ℝ) :
    supportT 0 g L C = {_x | 0 ≤ L ∧ 0 ≤ C 0} := by
  ext x
  have : roughSet g x = ∅ := Finset.eq_empty_of_forall_notMem fun i => Fin.elim0 i
  simp [supportT, this]

theorem integral_supportT_zero_dim (g L : ℝ) (C : ℕ → ℝ) (p : ℕ) :
    ∫ x in supportT 0 g L C, (L - ∑ i, x i) ^ p = if 0 ≤ L ∧ 0 ≤ C 0 then L ^ p else 0 := by
  rw [supportT_zero_dim]
  by_cases h : 0 ≤ L ∧ 0 ≤ C 0
  · rw [if_pos h, show {_x : Fin 0 → ℝ | 0 ≤ L ∧ 0 ≤ C 0} = Set.univ from Set.eq_univ_of_forall
      fun _ => h, Measure.restrict_univ]
    simp [Measure.real, volume_pi, Measure.pi_empty_univ]
  · rw [if_neg h, show {_x : Fin 0 → ℝ | 0 ≤ L ∧ 0 ≤ C 0} = ∅ from Set.eq_empty_of_forall_notMem
      fun _ hx => h hx, Measure.restrict_empty, integral_zero_measure]

/-- Smaller caps give a smaller support. -/
theorem supportT_mono (N : ℕ) (g L : ℝ) (C C' : ℕ → ℝ) (h : ∀ m, C' m ≤ C m) :
    supportT N g L C' ⊆ supportT N g L C :=
  fun _ ⟨h0, hL, hC⟩ => ⟨h0, hL, hC.trans (h _)⟩

/-! ## The Gram entry -/

theorem supportT_subset_simplexF (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) :
    supportT N g L C ⊆ simplexF (Fin N) L := fun _ hx => ⟨hx.1, hx.2.1⟩

/-- **The Gram entry `∫_{T̃} (L − P₁) P₂` for any `N`, `g ≥ 0`, `L` and cap function `C`.** -/
theorem gram_entry_integral_general (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) :
    ∫ x in supportT N g L C, (L - ∑ i, x i) * ∑ i, x i ^ 2 = N * gramFormula N g L C 2 1 := by
  have hfun : ∀ x : Fin N → ℝ, (L - ∑ i, x i) * ∑ i, x i ^ 2 = ∑ a, (L - ∑ i, x i) ^ 1 * x a ^ 2 := by
    intro x; rw [Finset.mul_sum]; simp
  simp_rw [hfun]
  rw [integral_finsetSum]
  · simp_rw [integral_supportT N g L C hg _ 2 1]
    simp
  · intro a _
    exact ((by fun_prop : Continuous fun x : Fin N → ℝ => (L - ∑ i, x i) ^ 1 * x a ^ 2).continuousOn.integrableOn_compact
      (simplexF_isCompact (ι := Fin N) L)).mono_set (supportT_subset_simplexF N g L C)

/-! ## From `ℚ` to `ℝ` -/

theorem twoGroup_ratCast (n r A B p : ℕ) (c M : ℚ) :
    ((twoGroup n r A B p c M : ℚ) : ℝ) = twoGroup n r A B p (c : ℝ) (M : ℝ) := by
  unfold twoGroup wsVal
  by_cases h : 0 ≤ c ∧ 0 ≤ M
  · have h' : (0 : ℝ) ≤ c ∧ (0 : ℝ) ≤ M := ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    rw [if_pos h, if_pos h']
    push_cast [Rat.cast_min]
    rfl
  · have h' : ¬((0 : ℝ) ≤ c ∧ (0 : ℝ) ≤ M) := fun h' => h ⟨by exact_mod_cast h'.1, by exact_mod_cast h'.2⟩
    rw [if_neg h, if_neg h', Rat.cast_zero]

theorem gramFormula_ratCast (N : ℕ) (g L : ℚ) (C : ℕ → ℚ) (e p : ℕ) :
    ((gramFormula N g L C e p : ℚ) : ℝ) = gramFormula N (g : ℝ) (L : ℝ) (fun m => (C m : ℝ)) e p := by
  unfold gramFormula gramRow Hin Hk Hout
  push_cast [twoGroup_ratCast]
  rfl

/-- **The Table 3 Gram entry as a Lebesgue integral**: `I_T[(1, ∅), (0, (2))]` over the rescaled
support with Table 3's caps equals the rational `gramEntryQ`. -/
theorem gram_entry_integral :
    ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ)),
      ((53 / 50 : ℝ) - ∑ i, x i) * ∑ i, x i ^ 2 = (gramEntryQ : ℝ) := by
  have h := gram_entry_integral_general 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ))
    (by norm_num)
  rw [h, gramEntryQ]
  push_cast [gramFormula_ratCast]
  norm_num [BGP212.Params.g, BGP212.Params.L]

/-- The same integral, with the value written out. -/
theorem gram_entry_integral_value :
    ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ)),
      ((53 / 50 : ℝ) - ∑ i, x i) * ∑ i, x i ^ 2 =
        ((56548202531757829081112222776094322482195301797337957431658942826121654659702465348240408258861490443138056811762103934848460333484729132412243771531 /
          475777117431212313155109340694822167006580726288213730520562203252425237214040532052194976131431758403778076171875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  rw [gram_entry_integral, gramEntryQ_eq]

/-- **The entry in V0's basis**: the generators `gen 1 ∅ = L − P₁` and `gen 0 {2} = P₂` of `B₂₁`,
evaluated at `x` and integrated over the Table 3 support. -/
theorem gram_entry_B21 :
    ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ)),
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 1 0) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}) = (gramEntryQ : ℝ) := by
  rw [← gram_entry_integral]
  congr 1
  funext x
  have e1 : MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 1 0) = 53 / 50 - ∑ i, x i := by
    simp [BGP212.Var.gen, BGP212.Var.Plam, BGP212.Var.P, MvPolynomial.psum, BGP212.Params.L,
      MvPolynomial.eval₂_sub, MvPolynomial.eval₂_C, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_X]
  have e2 : MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}) = ∑ i, x i ^ 2 := by
    simp [BGP212.Var.gen, BGP212.Var.Plam, BGP212.Var.P, MvPolynomial.psum,
      MvPolynomial.eval₂_sum, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X]
  rw [e1, e2]

end BGP212.Gram

/-! ## Comparator wrappers -/

namespace BGP212.Challenge

open BGP212.Gram MeasureTheory

theorem simplexF_integral {ι : Type*} [Fintype ι] (R : ℝ) (hR : 0 ≤ R) (e : ι → ℕ) :
    ∫ z in simplexF ι R, ∏ i, z i ^ e i = momentF ι R e :=
  BGP212.Gram.simplexF_integral R hR e

theorem simplexF_integral_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι] (R : ℝ) (hR : 0 ≤ R) (e : ι → ℕ) :
    ∫ z in simplexF ι R, ∏ i, z i ^ e i = 1 :=
  BGP212.Gram.simplexF_integral_isEmpty R hR e

theorem weighted_simplexF {ι : Type*} [Fintype ι] (c : ℝ) (hc : 0 ≤ c) (e : ι → ℕ) (p : ℕ) :
    ∫ z in simplexF ι c, (∏ i, z i ^ e i) * (c - ∑ i, z i) ^ p =
      c ^ (Fintype.card ι + ∑ i, e i + p) * (∏ i, ((e i).factorial : ℝ)) *
        (p.factorial : ℝ) / ((Fintype.card ι + ∑ i, e i + p).factorial : ℝ) :=
  BGP212.Gram.weighted_simplexF c hc e p

theorem indicator_supportT {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (F : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    (supportT N g L C).indicator F x =
      ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * (Qset g L C R K).indicator F x :=
  BGP212.Gram.indicator_supportT g L C F x

theorem integral_Qset {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (R K : Finset (Fin N)) (hRK : Disjoint R K) (F : (Fin N → ℝ) → ℝ) :
    ∫ x, (Qset g L C R K).indicator F x =
      ∫ y in pieceSet N R (C R.card - R.card * g) (L - (R.card + K.card) * g),
        F (y + shiftV g (R ∪ K)) :=
  BGP212.Gram.integral_Qset g L C hg R K hRK F

theorem pieceSet_empty (N : ℕ) (R : Finset (Fin N)) (c M : ℝ) (h : ¬(0 ≤ c ∧ 0 ≤ M)) :
    pieceSet N R c M = ∅ :=
  BGP212.Gram.pieceSet_empty N R c M h

theorem piece_integral_mem (N : ℕ) (R : Finset (Fin N)) (a : Fin N) (ha : a ∈ R) (t p : ℕ) (c M : ℝ) :
    ∫ y in pieceSet N R c M, y a ^ t * (M - ∑ i, y i) ^ p =
      twoGroup (N - R.card) R.card t 0 p c M :=
  BGP212.Gram.piece_integral_mem N R a ha t p c M

theorem piece_integral_notMem (N : ℕ) (R : Finset (Fin N)) (a : Fin N) (ha : a ∉ R) (t p : ℕ) (c M : ℝ) :
    ∫ y in pieceSet N R c M, y a ^ t * (M - ∑ i, y i) ^ p =
      twoGroup (N - R.card) R.card 0 t p c M :=
  BGP212.Gram.piece_integral_notMem N R a ha t p c M

theorem piece_integral_empty (N : ℕ) (a : Fin N) (t p : ℕ) (c M : ℝ) (hc : 0 ≤ c) (hM : 0 ≤ M) :
    ∫ y in pieceSet N ∅ c M, y a ^ t * (M - ∑ i, y i) ^ p =
      M ^ (N + t + p) * (t.factorial : ℝ) * (p.factorial : ℝ) / ((N + t + p).factorial : ℝ) :=
  BGP212.Gram.piece_integral_empty N a t p c M hc hM

theorem piece_integral_univ (N : ℕ) (a : Fin N) (t p : ℕ) (c M : ℝ) :
    ∫ y in pieceSet N Finset.univ c M, y a ^ t * (M - ∑ i, y i) ^ p =
      twoGroup 0 N t 0 p c M :=
  BGP212.Gram.piece_integral_univ N a t p c M

theorem supportT_zero_dim (g L : ℝ) (C : ℕ → ℝ) :
    supportT 0 g L C = {_x | 0 ≤ L ∧ 0 ≤ C 0} :=
  BGP212.Gram.supportT_zero_dim g L C

theorem integral_supportT_zero_dim (g L : ℝ) (C : ℕ → ℝ) (p : ℕ) :
    ∫ x in supportT 0 g L C, (L - ∑ i, x i) ^ p = if 0 ≤ L ∧ 0 ≤ C 0 then L ^ p else 0 :=
  BGP212.Gram.integral_supportT_zero_dim g L C p

theorem count_pieces (N : ℕ) (a : Fin N) (Hin Hk Hout : ℕ → ℕ → ℝ) :
    ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card *
        (if a ∈ R then Hin R.card K.card else if a ∈ K then Hk R.card K.card else Hout R.card K.card) =
      ∑ r ∈ Finset.range (N - 1 + 1), ((N - 1).choose r : ℝ) *
        ∑ k ∈ Finset.range (N - 1 - r + 1), ((N - 1 - r).choose k : ℝ) *
          ((-1 : ℝ) ^ k * Hin (r + 1) k + (-1 : ℝ) ^ k * Hout r k - (-1 : ℝ) ^ k * Hk r (k + 1)) :=
  BGP212.Gram.count_pieces N a Hin Hk Hout

theorem integral_supportT (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (a : Fin N) (e p : ℕ) :
    ∫ x in supportT N g L C, (L - ∑ i, x i) ^ p * x a ^ e = gramFormula N g L C e p :=
  BGP212.Gram.integral_supportT N g L C hg a e p

theorem supportT_mono (N : ℕ) (g L : ℝ) (C C' : ℕ → ℝ) (h : ∀ m, C' m ≤ C m) :
    supportT N g L C' ⊆ supportT N g L C :=
  BGP212.Gram.supportT_mono N g L C C' h

theorem gram_entry_integral_general (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) :
    ∫ x in supportT N g L C, (L - ∑ i, x i) * ∑ i, x i ^ 2 = N * gramFormula N g L C 2 1 :=
  BGP212.Gram.gram_entry_integral_general N g L C hg

theorem gramFormula_ratCast (N : ℕ) (g L : ℚ) (C : ℕ → ℚ) (e p : ℕ) :
    ((gramFormula N g L C e p : ℚ) : ℝ) = gramFormula N (g : ℝ) (L : ℝ) (fun m => (C m : ℝ)) e p :=
  BGP212.Gram.gramFormula_ratCast N g L C e p

theorem gramEntryQ_eq :
    gramEntryQ = (56548202531757829081112222776094322482195301797337957431658942826121654659702465348240408258861490443138056811762103934848460333484729132412243771531 /
          475777117431212313155109340694822167006580726288213730520562203252425237214040532052194976131431758403778076171875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) :=
  BGP212.Gram.gramEntryQ_eq

theorem gram_entry_integral :
    ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ)),
      ((53 / 50 : ℝ) - ∑ i, x i) * ∑ i, x i ^ 2 = (gramEntryQ : ℝ) :=
  BGP212.Gram.gram_entry_integral

theorem gram_entry_integral_value :
    ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ)),
      ((53 / 50 : ℝ) - ∑ i, x i) * ∑ i, x i ^ 2 = ((56548202531757829081112222776094322482195301797337957431658942826121654659702465348240408258861490443138056811762103934848460333484729132412243771531 /
          475777117431212313155109340694822167006580726288213730520562203252425237214040532052194976131431758403778076171875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) :=
  BGP212.Gram.gram_entry_integral_value

theorem gram_entry_B21 :
    ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ)),
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 1 0) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}) = (gramEntryQ : ℝ) :=
  BGP212.Gram.gram_entry_B21

end BGP212.Challenge
