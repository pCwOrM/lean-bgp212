/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Definition 4.1 (p. 4), Definition 4.6 (p. 6), §9.3 dictionary (p. 40),
§9.4, Lemma 9.2 and the display of `J_T` (p. 41).
-/
import BGP212.Fibre
import Solution.GramEntry

/-! # V2d: Lemma 9.2, the `J_T` fibre theorem (proofs)

PROVED THEOREMS (no kernel arithmetic beyond the ten Table 3 cap steps):

* `roughSet_snoc`, `roughCount_snoc`, `roughMass_snoc`: appending `u` adds the last coordinate
  to the rough set exactly when `g < u`.
* `fibre_equiv` (Lemma 9.2): on `T̂`, `(x̂, u) ∈ T̃ ↔ 0 ≤ u ≤ U(x̂)`.
* `empty_fibre_neg`, `empty_fibre_cap`: empty fibres off `T̂` (cap step from `m = 1`, `0 ≤ C 0`).
* `marginal_agrees`: Definition 4.6's marginal of `1_{T̃} P` equals §9.4's `J_T(P)`.
* `inner_integral`: `∫₀^U (M − u)^p u^t du` in closed form.
* Table 3: `g_nonneg`, `tau_le_L`, `C_zero_table3`, `capStep_table3`,
  `capStep_zero_fails_table3`; `v2d_spec_discharged` proves every specification `Prop` of
  `BGP212/Fibre.lean`, including the Table 3 instances. -/

namespace BGP212.V2d

open BGP212.Gram MeasureTheory

/-! ## Rough count and rough mass after appending a coordinate -/

theorem roughCount_eq {n : ℕ} (g : ℝ) (x : Fin n → ℝ) :
    roughCount g x = ∑ i, if g < x i then 1 else 0 := by
  classical
  unfold roughCount roughSet
  rw [Finset.card_filter]

theorem roughMass_eq {n : ℕ} (g : ℝ) (x : Fin n → ℝ) :
    roughMass g x = ∑ i, if g < x i then x i else 0 := by
  classical
  unfold roughMass roughSet
  rw [Finset.sum_filter]

/-- **`roughSet_snoc`**: the rough coordinates of `(x̂, u)` are those of `x̂` (moved by
`castSucc`) together with the last coordinate exactly when `g < u`. -/
theorem roughSet_snoc {n : ℕ} (g : ℝ) (x : Fin n → ℝ) (u : ℝ) :
    roughSet g (Fin.snoc x u : Fin (n + 1) → ℝ) =
      (roughSet g x).map Fin.castSuccEmb ∪ (if g < u then {Fin.last n} else ∅) := by
  classical
  ext i
  rw [mem_roughSet, Finset.mem_union]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    constructor
    · intro h; right; simp [h]
    · rintro (h | h)
      · obtain ⟨j, -, hj⟩ := Finset.mem_map.mp h
        exact absurd hj (Fin.castSucc_ne_last j)
      · by_contra hu; simp [hu] at h
  · simp only [Fin.snoc_castSucc]
    constructor
    · intro h; left
      exact Finset.mem_map.mpr ⟨j, (mem_roughSet g x j).mpr h, rfl⟩
    · rintro (h | h)
      · obtain ⟨k, hk, hkj⟩ := Finset.mem_map.mp h
        have : k = j := Fin.castSucc_injective _ hkj
        subst this
        exact (mem_roughSet g x k).mp hk
      · split_ifs at h with hu
        · simp at h
        · simp at h

/-- The rough count after appending `u`: `s` or `s + 1`. -/
theorem roughCount_snoc {n : ℕ} (g : ℝ) (x : Fin n → ℝ) (u : ℝ) :
    roughCount g (Fin.snoc x u : Fin (n + 1) → ℝ) = roughCount g x + if g < u then 1 else 0 := by
  rw [roughCount_eq, roughCount_eq, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- The rough mass after appending `u`: `ρ₁` or `ρ₁ + u`. -/
theorem roughMass_snoc {n : ℕ} (g : ℝ) (x : Fin n → ℝ) (u : ℝ) :
    roughMass g (Fin.snoc x u : Fin (n + 1) → ℝ) = roughMass g x + if g < u then u else 0 := by
  rw [roughMass_eq, roughMass_eq, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem sum_snoc {n : ℕ} (x : Fin n → ℝ) (u : ℝ) :
    ∑ i, (Fin.snoc x u : Fin (n + 1) → ℝ) i = ∑ i, x i + u := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem nonneg_snoc {n : ℕ} (x : Fin n → ℝ) (u : ℝ) :
    (∀ i, 0 ≤ (Fin.snoc x u : Fin (n + 1) → ℝ) i) ↔ (∀ i, 0 ≤ x i) ∧ 0 ≤ u := by
  constructor
  · intro h
    exact ⟨fun i => by simpa using h (Fin.castSucc i), by simpa using h (Fin.last n)⟩
  · rintro ⟨hx, hu⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hu
    · simpa using hx j

/-- Membership in `T̃` in terms of `S`, `s`, `ρ₁` of `x̂` and the new coordinate `u`. -/
theorem mem_supportT_snoc {n : ℕ} (g L : ℝ) (C : ℕ → ℝ) (x : Fin n → ℝ) (u : ℝ) :
    Fin.snoc x u ∈ supportT (n + 1) g L C ↔
      ((∀ i, 0 ≤ x i) ∧ 0 ≤ u) ∧ ∑ i, x i + u ≤ L ∧
        roughMass g x + (if g < u then u else 0) ≤
          C (roughCount g x + if g < u then 1 else 0) := by
  have h1 := roughMass_snoc g x u
  have h2 := roughCount_snoc g x u
  unfold roughMass at h1
  unfold roughCount at h2
  simp only [supportT, Set.mem_ofPred_eq, nonneg_snoc, sum_snoc, h1, h2]
  rfl

/-! ## Lemma 9.2 -/

/-- **Lemma 9.2 (fibre equivalence).** For `x̂ ∈ T̂`, `(x̂, u) ∈ T̃ ↔ 0 ≤ u ≤ U(x̂)`. -/
theorem fibre_equiv (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hτ : τ ≤ L)
    (x : Fin n → ℝ) (hx : x ∈ hatSupport n g τ C) (u : ℝ) :
    Fin.snoc x u ∈ supportT (n + 1) g L C ↔ 0 ≤ u ∧ u ≤ endpoint g L C x := by
  obtain ⟨hx0, hS, hcap⟩ := hx
  rw [mem_supportT_snoc, endpoint, le_min_iff, le_max_iff]
  by_cases hu : g < u
  · simp only [if_pos hu]
    constructor
    · rintro ⟨⟨-, h0⟩, hL, hc⟩
      exact ⟨h0, by linarith, Or.inr (by linarith)⟩
    · rintro ⟨h0, hL, hgc | hgc⟩
      · exact absurd hgc (not_le.mpr hu)
      · exact ⟨⟨hx0, h0⟩, by linarith, by linarith⟩
  · simp only [if_neg hu, add_zero]
    constructor
    · rintro ⟨⟨-, h0⟩, hL, -⟩
      exact ⟨h0, by linarith, Or.inl (not_lt.mp hu)⟩
    · rintro ⟨h0, hL, -⟩
      exact ⟨⟨hx0, h0⟩, by linarith, hcap⟩

/-- **Empty fibre, sign side.** -/
theorem empty_fibre_neg (n : ℕ) (g L : ℝ) (C : ℕ → ℝ) (x : Fin n → ℝ) (hneg : ∃ i, x i < 0)
    (u : ℝ) : Fin.snoc x u ∉ supportT (n + 1) g L C := by
  intro h
  obtain ⟨i, hi⟩ := hneg
  have := ((mem_supportT_snoc g L C x u).mp h).1.1 i
  linarith

theorem roughMass_of_count_zero {n : ℕ} (g : ℝ) (x : Fin n → ℝ) (h : roughCount g x = 0) :
    roughMass g x = 0 := by
  unfold roughCount at h
  unfold roughMass
  rw [Finset.card_eq_zero.mp h, Finset.sum_empty]

/-- **Empty fibre, cap side.** With the cap step from `m = 1` and `0 ≤ C 0`, an `x̂` whose rough
mass exceeds its cap has an empty fibre. -/
theorem empty_fibre_cap (n : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hstep : CapStep g C) (hC0 : 0 ≤ C 0)
    (x : Fin n → ℝ) (hcap : C (roughCount g x) < roughMass g x) (u : ℝ) :
    Fin.snoc x u ∉ supportT (n + 1) g L C := by
  intro h
  obtain ⟨-, -, hc⟩ := (mem_supportT_snoc g L C x u).mp h
  by_cases hs : roughCount g x = 0
  · rw [roughMass_of_count_zero g x hs, hs] at hcap
    linarith
  by_cases hu : g < u
  · simp only [if_pos hu] at hc
    have := hstep (roughCount g x) (Nat.one_le_iff_ne_zero.mpr hs)
    linarith
  · simp only [if_neg hu, add_zero] at hc
    linarith


/-! ## The marginal identity -/

theorem hatSupport_eq (n : ℕ) (g τ : ℝ) (C : ℕ → ℝ) :
    hatSupport n g τ C = supportT n g τ C := rfl

theorem hatSupport_measurableSet (n : ℕ) (g τ : ℝ) (C : ℕ → ℝ) :
    MeasurableSet (hatSupport n g τ C) := by
  rw [hatSupport_eq]; exact supportT_measurableSet n g τ C

theorem endpoint_nonneg {n : ℕ} (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hτ : τ ≤ L)
    (x : Fin n → ℝ) (hx : x ∈ hatSupport n g τ C) : 0 ≤ endpoint g L C x := by
  obtain ⟨-, hS, -⟩ := hx
  exact le_min (by linarith) (le_trans hg (le_max_left _ _))

/-- The fibre integral of `1_{T̃} P` on `T̂` is the interval integral up to `U(x̂)`. -/
theorem fibre_integral (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hτ : τ ≤ L)
    (P : (Fin (n + 1) → ℝ) → ℝ) (x : Fin n → ℝ) (hx : x ∈ hatSupport n g τ C) :
    ∫ u, (supportT (n + 1) g L C).indicator P (Fin.snoc x u) =
      ∫ u in (0 : ℝ)..(endpoint g L C x), P (Fin.snoc x u) := by
  have hfun : (fun u => (supportT (n + 1) g L C).indicator P (Fin.snoc x u)) =
      (Set.Icc 0 (endpoint g L C x)).indicator (fun u => P (Fin.snoc x u)) := by
    funext u
    by_cases h : Fin.snoc x u ∈ supportT (n + 1) g L C
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem
        (show u ∈ Set.Icc 0 (endpoint g L C x) from (fibre_equiv n g L τ C hg hτ x hx u).mp h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem
        (show u ∉ Set.Icc 0 (endpoint g L C x) from
          fun h' => h ((fibre_equiv n g L τ C hg hτ x hx u).mpr h'))]
  rw [hfun, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (endpoint_nonneg g L τ C hg hτ x hx)]

/-- Off `T̂` (within the cutoff `S ≤ τ`) the fibre integral vanishes. -/
theorem fibre_integral_zero (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (hstep : CapStep g C)
    (hC0 : 0 ≤ C 0) (P : (Fin (n + 1) → ℝ) → ℝ) (x : Fin n → ℝ) (hS : ∑ i, x i ≤ τ)
    (hx : x ∉ hatSupport n g τ C) :
    ∫ u, (supportT (n + 1) g L C).indicator P (Fin.snoc x u) = 0 := by
  have hempty : ∀ u, Fin.snoc x u ∉ supportT (n + 1) g L C := by
    by_cases hneg : ∃ i, x i < 0
    · exact empty_fibre_neg n g L C x hneg
    · push_neg at hneg
      have hcap : C (roughCount g x) < roughMass g x := by
        by_contra h
        exact hx ⟨hneg, hS, not_lt.mp h⟩
      exact empty_fibre_cap n g L C hstep hC0 x hcap
  have : (fun u => (supportT (n + 1) g L C).indicator P (Fin.snoc x u)) = fun _ => 0 := by
    funext u; exact Set.indicator_of_notMem (hempty u) _
  rw [this, integral_zero]

/-- **The marginal identity**: Definition 4.6's marginal of `1_{T̃} P` (cutoff `S ≤ τ`) is §9.4's
`J_T(P)`. -/
theorem marginal_agrees (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hτ : τ ≤ L)
    (hstep : CapStep g C) (hC0 : 0 ≤ C 0) (P : (Fin (n + 1) → ℝ) → ℝ) (_hP : Continuous P) :
    marginalJ n g L τ C P = jT n g L τ C P := by
  unfold marginalJ jT
  congr 1
  have hA : MeasurableSet {x : Fin n → ℝ | ∑ i, x i ≤ τ} :=
    measurableSet_le (Finset.measurable_sum _ fun i _ => measurable_pi_apply i) measurable_const
  have key : Set.EqOn (fun x => (∫ u, (supportT (n + 1) g L C).indicator P (Fin.snoc x u)) ^ 2)
      ((hatSupport n g τ C).indicator
        (fun x => (∫ u in (0 : ℝ)..(endpoint g L C x), P (Fin.snoc x u)) ^ 2))
      {x | ∑ i, x i ≤ τ} := by
    intro x hS
    dsimp only
    by_cases hx : x ∈ hatSupport n g τ C
    · rw [Set.indicator_of_mem hx, fibre_integral n g L τ C hg hτ P x hx]
    · rw [Set.indicator_of_notMem hx, fibre_integral_zero n g L τ C hstep hC0 P x hS hx]
      ring
  rw [setIntegral_congr_fun hA key, setIntegral_indicator (hatSupport_measurableSet n g τ C),
    Set.inter_eq_right.mpr (fun x hx => hx.2.1)]

/-! ## The inner integral -/

/-- **The inner `u`-integral** `∫₀^U (M − u)^p u^t du` in closed form. -/
theorem inner_integral (U M : ℝ) (p t : ℕ) :
    ∫ u in (0 : ℝ)..U, (M - u) ^ p * u ^ t =
      ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) * M ^ (p - j) * (-1) ^ j * U ^ (t + j + 1) /
        (t + j + 1) := by
  have hexp : ∀ u : ℝ, (M - u) ^ p * u ^ t =
      ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) * M ^ (p - j) * (-1) ^ j * u ^ (t + j) := by
    intro u
    rw [show M - u = -u + M by ring, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [neg_pow, pow_add]
    ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have : ((t + j : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    rw [show t + j + 1 = (t + j) + 1 from rfl]
    simp
    ring
  · intro j _
    exact (by fun_prop : Continuous fun u : ℝ =>
      (p.choose j : ℝ) * M ^ (p - j) * (-1) ^ j * u ^ (t + j)).intervalIntegrable _ _

/-! ## Table 3 -/

/-- `g = 41/625 ≥ 0`. -/
theorem g_nonneg : (0 : ℝ) ≤ (BGP212.Params.g : ℝ) := by
  norm_num [BGP212.Params.g]

/-- `τ = 249/250 ≤ L = 53/50` (so `L − S ≥ L − τ = 8/125 > 0` on `T̂`). -/
theorem tau_le_L : (BGP212.Params.τ : ℝ) ≤ (BGP212.Params.L : ℝ) := by
  norm_num [BGP212.Params.τ, BGP212.Params.L]

/-- Table 3's caps satisfy the cap-step condition (rescaled `B_{m+1} ≤ B_m + δ`;
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

/-- The step `0 → 1` is not a cap step at Table 3: `C(1) = 777/1250 > 0 + g`. -/
theorem capStep_zero_fails_table3 :
    (BGP212.Params.C 0 : ℝ) + (BGP212.Params.g : ℝ) < (BGP212.Params.C 1 : ℝ) := by
  have : BGP212.Params.C 0 + BGP212.Params.g < BGP212.Params.C 1 := by decide +kernel
  exact_mod_cast this

/-- `C(0) = 0` at Table 3. -/
theorem C_zero_table3 : (0 : ℝ) ≤ (BGP212.Params.C 0 : ℝ) := by
  have : (0 : ℚ) ≤ BGP212.Params.C 0 := by decide +kernel
  exact_mod_cast this

/-- **The specification of V2d-Spec, discharged.** -/
theorem v2d_spec_discharged :
    FibreEquiv ∧ EmptyFibreCap ∧ EmptyFibreNeg ∧ MarginalAgrees ∧ InnerIntegral ∧
      FibreEquivTable3 ∧ MarginalAgreesTable3 := by
  refine ⟨fun n g L τ C hg hτ x hx u => fibre_equiv n g L τ C hg hτ x hx u,
    fun n g L C hs h0 x hc u => empty_fibre_cap n g L C hs h0 x hc u,
    fun n g L C x hn u => empty_fibre_neg n g L C x hn u,
    fun n g L τ C hg hτ hs h0 P hP => marginal_agrees n g L τ C hg hτ hs h0 P hP,
    fun U M p t => inner_integral U M p t,
    fun x hx u => fibre_equiv 44 _ _ _ _ g_nonneg tau_le_L x hx u,
    fun P hP => marginal_agrees 44 _ _ _ _ g_nonneg tau_le_L capStep_table3 C_zero_table3 P hP⟩

end BGP212.V2d

/-! ## Comparator wrappers -/

namespace BGP212.Challenge

open BGP212.Gram BGP212.V2d MeasureTheory

theorem roughSet_snoc {n : ℕ} (g : ℝ) (x : Fin n → ℝ) (u : ℝ) :
    roughSet g (Fin.snoc x u : Fin (n + 1) → ℝ) =
      (roughSet g x).map Fin.castSuccEmb ∪ (if g < u then {Fin.last n} else ∅) :=
  BGP212.V2d.roughSet_snoc g x u

theorem roughCount_snoc {n : ℕ} (g : ℝ) (x : Fin n → ℝ) (u : ℝ) :
    roughCount g (Fin.snoc x u : Fin (n + 1) → ℝ) = roughCount g x + if g < u then 1 else 0 :=
  BGP212.V2d.roughCount_snoc g x u

theorem roughMass_snoc {n : ℕ} (g : ℝ) (x : Fin n → ℝ) (u : ℝ) :
    roughMass g (Fin.snoc x u : Fin (n + 1) → ℝ) = roughMass g x + if g < u then u else 0 :=
  BGP212.V2d.roughMass_snoc g x u

theorem fibre_equiv (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hτ : τ ≤ L) (x : Fin n → ℝ) (hx : x ∈ hatSupport n g τ C) (u : ℝ) :
    Fin.snoc x u ∈ supportT (n + 1) g L C ↔ 0 ≤ u ∧ u ≤ endpoint g L C x :=
  BGP212.V2d.fibre_equiv n g L τ C hg hτ x hx u

theorem empty_fibre_neg (n : ℕ) (g L : ℝ) (C : ℕ → ℝ) (x : Fin n → ℝ) (hneg : ∃ i, x i < 0) (u : ℝ) :
    Fin.snoc x u ∉ supportT (n + 1) g L C :=
  BGP212.V2d.empty_fibre_neg n g L C x hneg u

theorem empty_fibre_cap (n : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hstep : CapStep g C) (hC0 : 0 ≤ C 0) (x : Fin n → ℝ) (hcap : C (roughCount g x) < roughMass g x) (u : ℝ) :
    Fin.snoc x u ∉ supportT (n + 1) g L C :=
  BGP212.V2d.empty_fibre_cap n g L C hstep hC0 x hcap u

theorem fibre_integral (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hτ : τ ≤ L) (P : (Fin (n + 1) → ℝ) → ℝ) (x : Fin n → ℝ) (hx : x ∈ hatSupport n g τ C) :
    ∫ u, (supportT (n + 1) g L C).indicator P (Fin.snoc x u) =
      ∫ u in (0 : ℝ)..(endpoint g L C x), P (Fin.snoc x u) :=
  BGP212.V2d.fibre_integral n g L τ C hg hτ P x hx

theorem marginal_agrees (n : ℕ) (g L τ : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (hτ : τ ≤ L) (hstep : CapStep g C) (hC0 : 0 ≤ C 0) (P : (Fin (n + 1) → ℝ) → ℝ) (hP : Continuous P) :
    marginalJ n g L τ C P = jT n g L τ C P :=
  BGP212.V2d.marginal_agrees n g L τ C hg hτ hstep hC0 P hP

theorem inner_integral (U M : ℝ) (p t : ℕ) :
    ∫ u in (0 : ℝ)..U, (M - u) ^ p * u ^ t =
      ∑ j ∈ Finset.range (p + 1), (p.choose j : ℝ) * M ^ (p - j) * (-1) ^ j * U ^ (t + j + 1) /
        (t + j + 1) :=
  BGP212.V2d.inner_integral U M p t

theorem tau_le_L :
    (BGP212.Params.τ : ℝ) ≤ (BGP212.Params.L : ℝ) :=
  BGP212.V2d.tau_le_L

theorem C_zero_table3 :
    (0 : ℝ) ≤ (BGP212.Params.C 0 : ℝ) :=
  BGP212.V2d.C_zero_table3

theorem capStep_table3 :
    CapStep (BGP212.Params.g : ℝ) (fun m => (BGP212.Params.C m : ℝ)) :=
  BGP212.V2d.capStep_table3

theorem capStep_zero_fails_table3 :
    (BGP212.Params.C 0 : ℝ) + (BGP212.Params.g : ℝ) < (BGP212.Params.C 1 : ℝ) :=
  BGP212.V2d.capStep_zero_fails_table3

theorem v2d_spec_discharged :
    FibreEquiv ∧ EmptyFibreCap ∧ EmptyFibreNeg ∧ MarginalAgrees ∧ InnerIntegral ∧
      FibreEquivTable3 ∧ MarginalAgreesTable3 :=
  BGP212.V2d.v2d_spec_discharged

end BGP212.Challenge
