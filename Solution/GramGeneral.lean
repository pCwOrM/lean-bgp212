/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Lemma 9.1 (p. 41), (10.1), Lemma 10.1, Proposition 10.2 (pp. 41–42),
§11 (p. 42).
-/
import BGP212.GramGeneral
import Solution.GramEntry
import Solution.GramGeneralCert


/-! # V2c: the general monomial integral bridge (proofs)

PROVED INTEGRAL IDENTITIES, reusing V2b's stratification (`indicator_supportT`), translation
(`integral_Qset`), Fubini on fibred regions and weighted simplex moments (V1):

1. `piece_integral_general`: a piece integrates any monomial `yᵗ (M − Σ y)^p` to `twoGroupW`.
2. `integral_supportT_unreduced_gen`: the signed sum over `(R, K)` for `(L − Σ x)^p ∏ xᵢ^{eᵢ}`,
   after expanding `∏ (yᵢ + g·1_{R∪K})^{eᵢ}` over exponent vectors `t ≤ e`.
3. Counting: `sig_insert` (one coordinate is rough, in `K`, or neither), `sig_union` (the
   distinguished coordinates `D` split off from the rest), `sig_card` (binomial multiplicities),
   and `pieceTermGen_eq` (a piece depends on `(R, K)` only through `R ∩ D`, `K ∩ D`, `|R|`, `|K|`).
4. `integral_supportT_gen`: `∫_{T̃} (L − Σ x)^p ∏ xᵢ^{eᵢ} = gramGen N g L C e p` for every `N`,
   `g ≥ 0`, `L`, cap function `C`, exponent vector `e`, weight `p`.
5. Symmetry (`integral_supportT_perm`, `gramGen_perm`), rationality (`gramGen_ratCast`),
   consistency with V2b (`gramGen_single`), and transport to `Fin d` (`gramGen_extend`).
6. Generators: `prod_power_sums`, `eval_gen`, `gram_entry_gen_list` (every `I_T` entry of
   `B₂₁` generators in closed form, cap function `C`), `gram_entry_B21_rat` (every Table 3 entry
   is an explicit rational).
7. The worked example `gram_entry_example`; its value comes from the computational certificate
   `Solution/GramGeneralCert.lean`. -/

namespace BGP212.Gram

open MeasureTheory


theorem split_prods (N : ℕ) (R : Finset (Fin N)) (t : Fin N → ℕ) (z : {i // i ∈ R} → ℝ)
    (w : {i // i ∉ R} → ℝ) :
    let y := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => ℝ) (· ∈ R)).symm (z, w)
    ∏ i, y i ^ t i = (∏ i : {i // i ∈ R}, z i ^ t i) * ∏ i : {i // i ∉ R}, w i ^ t i := by
  intro y
  obtain ⟨h1, h2, -, -⟩ := split_sums N R z w
  rw [← Fintype.prod_subtype_mul_prod_subtype (· ∈ R) (fun i => y i ^ t i)]
  have e1 : ∏ i : {i // i ∈ R}, y i ^ t i = ∏ i : {i // i ∈ R}, z i ^ t i :=
    Finset.prod_congr rfl fun i _ => congrArg (fun v => v ^ t i) (h1 i)
  have e2 : ∏ i : {i // i ∉ R}, y i ^ t i = ∏ i : {i // i ∉ R}, w i ^ t i :=
    Finset.prod_congr rfl fun i _ => congrArg (fun v => v ^ t i) (h2 i)
  rw [← e1, ← e2]
  congr 1
  exact Finset.prod_congr (by congr; exact Subsingleton.elim _ _) fun _ _ => rfl

theorem sum_subtype_mem {N : ℕ} (R : Finset (Fin N)) (t : Fin N → ℕ) :
    ∑ i : {i // i ∈ R}, t i = ∑ i ∈ R, t i :=
  (Finset.sum_subtype R (fun _ => Iff.rfl) t).symm

theorem sum_subtype_notMem {N : ℕ} (R : Finset (Fin N)) (t : Fin N → ℕ) :
    ∑ i : {i // i ∉ R}, t i = ∑ i ∈ Rᶜ, t i :=
  (Finset.sum_subtype Rᶜ (fun _ => Finset.mem_compl) t).symm

theorem prod_fact_split {N : ℕ} (R : Finset (Fin N)) (t : Fin N → ℕ) :
    (∏ i : {i // i ∈ R}, ((t i).factorial : ℝ)) * (∏ i : {i // i ∉ R}, ((t i).factorial : ℝ)) =
      ∏ i, ((t i).factorial : ℝ) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (· ∈ R) (fun i => ((t i).factorial : ℝ))]
  congr 1
  exact Finset.prod_congr (by congr; exact Subsingleton.elim _ _) fun _ _ => rfl

/-- **A piece, any monomial**: `∫_{pieceSet R c M} yᵗ (M − Σ y)^p` is the two-group value with
`A = Σ_R t`, `B = Σ_{Rᶜ} t` and weight `∏ tᵢ!`. -/
theorem piece_integral_general (N : ℕ) (R : Finset (Fin N)) (t : Fin N → ℕ) (p : ℕ) (c M : ℝ) :
    ∫ y in pieceSet N R c M, (∏ i, y i ^ t i) * (M - ∑ i, y i) ^ p =
      twoGroupW (N - R.card) R.card (∑ i ∈ R, t i) (∑ i ∈ Rᶜ, t i) p
        (∏ i, ((t i).factorial : ℝ)) c M := by
  classical
  by_cases h : 0 ≤ c ∧ 0 ≤ M
  swap
  · rw [pieceSet_empty N R c M h, Measure.restrict_empty, integral_zero_measure, twoGroupW,
      if_neg h]
  have hc' : 0 ≤ min c M := le_min h.1 h.2
  rw [piece_as_fibred]
  have hF : (fun pr : ({i // i ∈ R} → ℝ) × ({i // i ∉ R} → ℝ) =>
      (∏ i, ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => ℝ) (· ∈ R)).symm pr) i ^ t i) *
        (M - ∑ i, ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin N => ℝ) (· ∈ R)).symm pr) i) ^ p) =
      fun pr => (∏ i : {i // i ∈ R}, pr.1 i ^ t i) *
        ((∏ i : {i // i ∉ R}, pr.2 i ^ t i) * ((M - ∑ i, pr.1 i) - ∑ i, pr.2 i) ^ p) := by
    funext ⟨z, w⟩
    obtain ⟨-, -, -, hall⟩ := split_sums N R z w
    rw [hall, split_prods N R t z w, show M - (∑ i, z i + ∑ i, w i) = (M - ∑ i, z i) - ∑ i, w i by
      ring]
    ring
  rw [hF, integral_fibred (simplexF_isCompact _) (fun z hz => hz.1) M _ (by fun_prop)]
  have hinner : ∀ z ∈ simplexF {i // i ∈ R} (min c M),
      ∫ w in simplexF {i // i ∉ R} (M - ∑ i, z i), (∏ i : {i // i ∈ R}, z i ^ t i) *
        ((∏ i : {i // i ∉ R}, w i ^ t i) * ((M - ∑ i, z i) - ∑ i, w i) ^ p) =
        (∏ i : {i // i ∉ R}, ((t i).factorial : ℝ)) * (p.factorial : ℝ) /
            ((N - R.card + ∑ i ∈ Rᶜ, t i + p).factorial : ℝ) *
          ((∏ i : {i // i ∈ R}, z i ^ t i) * (M - ∑ i, z i) ^ (N - R.card + ∑ i ∈ Rᶜ, t i + p)) := by
    intro z hz
    have h0 : 0 ≤ M - ∑ i, z i := by linarith [hz.2, min_le_right c M]
    rw [MeasureTheory.integral_const_mul]
    have hw := weighted_simplexF (ι := {i // i ∉ R}) (M - ∑ i, z i) h0 (fun i => t i) p
    rw [card_compl_subtype, sum_subtype_notMem] at hw
    rw [hw]
    ring
  rw [setIntegral_congr_fun (simplexF_measurableSet _) hinner, MeasureTheory.integral_const_mul,
    shifted_weighted (min c M) M hc', twoGroupW, if_pos h, Fintype.card_coe, sum_subtype_mem,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← prod_fact_split R t]
  ring


/-! ## The unreduced sum for a general monomial -/


theorem prod_add_pow_expand {N : ℕ} (y v : Fin N → ℝ) (e : Fin N → ℕ) :
    ∏ i, (y i + v i) ^ e i =
      ∑ t ∈ Fintype.piFinset (fun i => Finset.range (e i + 1)),
        (∏ i, ((e i).choose (t i) : ℝ) * v i ^ (e i - t i)) * ∏ i, y i ^ t i := by
  simp_rw [add_pow]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

theorem integral_Qset_term_gen {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (e : Fin N → ℕ) (p : ℕ)
    (R K : Finset (Fin N)) (hRK : Disjoint R K) :
    ∫ x, (Qset g L C R K).indicator (fun x => (L - ∑ i, x i) ^ p * ∏ i, x i ^ e i) x =
      pieceTermGen g L C e p R K := by
  classical
  rw [integral_Qset g L C hg R K hRK]
  set M := L - (R.card + K.card) * g
  set c := C R.card - R.card * g
  have hexp : ∀ y : Fin N → ℝ, (L - ∑ i, (y + shiftV g (R ∪ K)) i) ^ p *
      ∏ i, (y + shiftV g (R ∪ K)) i ^ e i =
      ∑ t ∈ Fintype.piFinset (fun i => Finset.range (e i + 1)),
        (∏ i, ((e i).choose (t i) : ℝ) * shiftV g (R ∪ K) i ^ (e i - t i)) *
          ((∏ i, y i ^ t i) * (M - ∑ i, y i) ^ p) := by
    intro y
    rw [sum_add_shiftV g R K hRK, show L - (∑ i, y i + (R.card + K.card) * g) = M - ∑ i, y i by
      simp only [M]; ring]
    simp only [Pi.add_apply]
    rw [prod_add_pow_expand y (shiftV g (R ∪ K)) e, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum]
  · unfold pieceTermGen
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [MeasureTheory.integral_const_mul, piece_integral_general]
  · intro t _
    exact integrableOn_pieceSet N R c M _ (by fun_prop)

/-- **Unreduced integral, general monomial.** -/
theorem integral_supportT_unreduced_gen (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g)
    (e : Fin N → ℕ) (p : ℕ) :
    ∫ x in supportT N g L C, (L - ∑ i, x i) ^ p * ∏ i, x i ^ e i =
      ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * pieceTermGen g L C e p R K := by
  classical
  rw [← integral_indicator (supportT_measurableSet N g L C)]
  simp_rw [indicator_supportT g L C]
  have hint : ∀ R K, Integrable ((Qset g L C R K).indicator
      (fun x : Fin N → ℝ => (L - ∑ i, x i) ^ p * ∏ i, x i ^ e i)) := by
    intro R K
    rw [integrable_indicator_iff (Qset_measurableSet g L C R K)]
    refine ((by fun_prop : Continuous fun x : Fin N → ℝ => (L - ∑ i, x i) ^ p * ∏ i, x i ^ e i).continuousOn.integrableOn_compact
      (simplexF_isCompact (ι := Fin N) L)).mono_set ?_
    exact fun x hx => ⟨hx.1, hx.2.2.1⟩
  rw [integral_finsetSum _ fun R _ => integrable_finset_sum _ fun K _ => (hint R K).const_mul _]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [integral_finsetSum _ fun K _ => (hint R K).const_mul _]
  refine Finset.sum_congr rfl fun K hK => ?_
  rw [MeasureTheory.integral_const_mul, integral_Qset_term_gen g L C hg e p R K]
  exact Finset.disjoint_left.mpr fun i hiR hiK =>
    (Finset.mem_compl.mp (Finset.mem_powerset.mp hK hiK)) hiR


/-! ## Counting placements of distinguished coordinates -/

section Sig
variable {N : ℕ}


theorem sig_univ (G : Finset (Fin N) → Finset (Fin N) → ℝ) :
    ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * G R K = Sig Finset.univ G := by
  unfold Sig
  rw [Finset.powerset_univ]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [Finset.compl_eq_univ_sdiff]

theorem sig_congr (U : Finset (Fin N)) (G G' : Finset (Fin N) → Finset (Fin N) → ℝ)
    (h : ∀ R ⊆ U, ∀ K ⊆ U \ R, G R K = G' R K) : Sig U G = Sig U G' := by
  unfold Sig
  refine Finset.sum_congr rfl fun R hR => Finset.sum_congr rfl fun K hK => ?_
  rw [h R (Finset.mem_powerset.mp hR) K (Finset.mem_powerset.mp hK)]

/-- Adding one coordinate `a` to the pool: it is rough, in `K`, or neither. -/
theorem sig_insert (U : Finset (Fin N)) (a : Fin N) (ha : a ∉ U)
    (G : Finset (Fin N) → Finset (Fin N) → ℝ) :
    Sig (insert a U) G = Sig U G + Sig U (fun R K => G (insert a R) K) -
      Sig U (fun R K => G R (insert a K)) := by
  unfold Sig
  rw [Finset.sum_powerset_insert ha]
  have h1 : ∀ R ∈ U.powerset, ∑ K ∈ (insert a U \ R).powerset, (-1 : ℝ) ^ K.card * G R K =
      ∑ K ∈ (U \ R).powerset, (-1 : ℝ) ^ K.card * G R K -
        ∑ K ∈ (U \ R).powerset, (-1 : ℝ) ^ K.card * G R (insert a K) := by
    intro R hR
    have haR : a ∉ R := fun h => ha (Finset.mem_powerset.mp hR h)
    have haD : a ∉ U \ R := fun h => ha (Finset.mem_sdiff.mp h).1
    rw [show insert a U \ R = insert a (U \ R) from Finset.insert_sdiff_of_notMem _ haR,
      Finset.sum_powerset_insert haD, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun K hK => ?_
    have haK : a ∉ K := fun h => haD (Finset.mem_powerset.mp hK h)
    rw [Finset.card_insert_of_notMem haK, pow_succ]
    ring
  have h2 : ∀ R ∈ U.powerset, ∑ K ∈ (insert a U \ insert a R).powerset, (-1 : ℝ) ^ K.card *
      G (insert a R) K = ∑ K ∈ (U \ R).powerset, (-1 : ℝ) ^ K.card * G (insert a R) K := by
    intro R _
    rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem ha]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_sub_distrib]
  ring

/-- **Splitting off the distinguished coordinates** `D` from a disjoint pool `E`: each
`a ∈ D` is placed in `R` (set `A`), in `K` (set `B`), or neither. -/
theorem sig_union (E : Finset (Fin N)) :
    ∀ (D : Finset (Fin N)), Disjoint D E → ∀ G : Finset (Fin N) → Finset (Fin N) → ℝ,
      Sig (D ∪ E) G = ∑ A ∈ D.powerset, ∑ B ∈ (D \ A).powerset,
        (-1 : ℝ) ^ B.card * Sig E (fun R K => G (A ∪ R) (B ∪ K)) := by
  intro D
  induction D using Finset.induction_on with
  | empty =>
      intro _ G
      simp
  | insert a D haD ih =>
      intro hdisj G
      have haE : a ∉ E := Finset.disjoint_left.mp hdisj (Finset.mem_insert_self a D)
      have hDE : Disjoint D E := Finset.disjoint_of_subset_left (Finset.subset_insert a D) hdisj
      have haDE : a ∉ D ∪ E := by simp [haD, haE]
      rw [Finset.insert_union, sig_insert _ a haDE, ih hDE, ih hDE, ih hDE]
      rw [Finset.sum_powerset_insert haD]
      -- `A ⊆ D`: `a` in `K` or neither; `A = insert a A'`: `a` rough
      have hA1 : ∀ A ∈ D.powerset, ∑ B ∈ (insert a D \ A).powerset,
          (-1 : ℝ) ^ B.card * Sig E (fun R K => G (A ∪ R) (B ∪ K)) =
          ∑ B ∈ (D \ A).powerset, (-1 : ℝ) ^ B.card * Sig E (fun R K => G (A ∪ R) (B ∪ K)) -
            ∑ B ∈ (D \ A).powerset, (-1 : ℝ) ^ B.card *
              Sig E (fun R K => G (A ∪ R) (insert a (B ∪ K))) := by
        intro A hA
        have haA : a ∉ A := fun h => haD (Finset.mem_powerset.mp hA h)
        have haDA : a ∉ D \ A := fun h => haD (Finset.mem_sdiff.mp h).1
        rw [show insert a D \ A = insert a (D \ A) from Finset.insert_sdiff_of_notMem _ haA,
          Finset.sum_powerset_insert haDA, sub_eq_add_neg, ← Finset.sum_neg_distrib]
        congr 1
        refine Finset.sum_congr rfl fun B hB => ?_
        have haB : a ∉ B := fun h => haDA (Finset.mem_powerset.mp hB h)
        rw [Finset.card_insert_of_notMem haB, pow_succ]
        simp only [Finset.insert_union]
        ring
      have hA2 : ∀ A ∈ D.powerset, ∑ B ∈ (insert a D \ insert a A).powerset,
          (-1 : ℝ) ^ B.card * Sig E (fun R K => G (insert a A ∪ R) (B ∪ K)) =
          ∑ B ∈ (D \ A).powerset, (-1 : ℝ) ^ B.card *
            Sig E (fun R K => G (insert a (A ∪ R)) (B ∪ K)) := by
        intro A _
        rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem haD]
        simp only [Finset.insert_union]
      rw [Finset.sum_congr rfl hA1, Finset.sum_congr rfl hA2, Finset.sum_sub_distrib]
      ring

/-- A signed sum depending only on `|R|` and `|K|` collapses to binomial multiplicities. -/
theorem sig_card (E : Finset (Fin N)) (φ : ℕ → ℕ → ℝ) :
    Sig E (fun R K => φ R.card K.card) =
      ∑ r ∈ Finset.range (E.card + 1), (E.card.choose r : ℝ) *
        ∑ k ∈ Finset.range (E.card - r + 1), ((E.card - r).choose k : ℝ) *
          ((-1 : ℝ) ^ k * φ r k) := by
  unfold Sig
  have hrow : ∀ R ∈ E.powerset, ∑ K ∈ (E \ R).powerset, (-1 : ℝ) ^ K.card * φ R.card K.card =
      ∑ k ∈ Finset.range (E.card - R.card + 1), ((E.card - R.card).choose k : ℝ) *
        ((-1 : ℝ) ^ k * φ R.card k) := by
    intro R hR
    rw [Finset.sum_powerset_apply_card (fun k => (-1 : ℝ) ^ k * φ R.card k) (x := E \ R),
      Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hR)]
    simp only [nsmul_eq_mul]
  rw [Finset.sum_congr rfl hrow, Finset.sum_powerset_apply_card (fun r =>
    ∑ k ∈ Finset.range (E.card - r + 1), ((E.card - r).choose k : ℝ) * ((-1 : ℝ) ^ k * φ r k))]
  simp only [nsmul_eq_mul]

end Sig


/-! ## The closed form for a general monomial -/


theorem le_of_mem_piFinset {N : ℕ} {e t : Fin N → ℕ}
    (ht : t ∈ Fintype.piFinset (fun i => Finset.range (e i + 1))) (i : Fin N) : t i ≤ e i := by
  have := Fintype.mem_piFinset.mp ht i
  rw [Finset.mem_range] at this
  omega

theorem sum_inter_supp {N : ℕ} {e t : Fin N → ℕ} (hte : ∀ i, t i ≤ e i) (S S' : Finset (Fin N))
    (h : S ∩ suppE e = S' ∩ suppE e) : ∑ i ∈ S, t i = ∑ i ∈ S', t i := by
  have key : ∀ S : Finset (Fin N), ∑ i ∈ S, t i = ∑ i ∈ S ∩ suppE e, t i := by
    intro S
    refine (Finset.sum_subset Finset.inter_subset_left fun i hi hn => ?_).symm
    have : e i = 0 := by
      by_contra h0
      exact hn (Finset.mem_inter.mpr ⟨hi, by simp [suppE, h0]⟩)
    have := hte i
    omega
  rw [key S, key S', h]

/-- Each piece depends on `(R, K)` only through `R ∩ D`, `K ∩ D`, `|R|`, `|K|`. -/
theorem pieceTermGen_eq {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (e : Fin N → ℕ) (p : ℕ)
    (R K : Finset (Fin N)) :
    pieceTermGen g L C e p R K =
      phiGen N g L C e p (R ∩ suppE e) (K ∩ suppE e) R.card K.card := by
  classical
  unfold pieceTermGen phiGen
  refine Finset.sum_congr rfl fun t ht => ?_
  have hte := le_of_mem_piFinset ht
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    by_cases hD : e i = 0
    · have : t i = 0 := by have := hte i; omega
      simp [hD, this]
    · have hiD : i ∈ suppE e := by simp [suppE, hD]
      by_cases h : i ∈ R ∪ K
      · have h' : i ∈ R ∩ suppE e ∪ K ∩ suppE e := by
          rcases Finset.mem_union.mp h with h | h <;> simp [h, hiD]
        simp [shiftV, h, h']
      · have h' : i ∉ R ∩ suppE e ∪ K ∩ suppE e := by
          intro h''; apply h
          rcases Finset.mem_union.mp h'' with h'' | h'' <;>
            simp [(Finset.mem_inter.mp h'').1]
        simp [shiftV, h, h']
  · congr 1
    · exact sum_inter_supp hte R (R ∩ suppE e) (by ext; simp)
    · exact sum_inter_supp hte Rᶜ (R ∩ suppE e)ᶜ (by ext; simp; tauto)

/-- **Proposition 10.2 for every monomial**: for every `N`, `g ≥ 0`, `L`, cap function `C`,
exponent vector `e` and weight `p`, `∫_{T̃} (L − Σ x)^p ∏ xᵢ^{eᵢ} = gramGen N g L C e p`. -/
theorem integral_supportT_gen (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (e : Fin N → ℕ)
    (p : ℕ) :
    ∫ x in supportT N g L C, (L - ∑ i, x i) ^ p * ∏ i, x i ^ e i = gramGen N g L C e p := by
  classical
  set D := suppE e with hD
  rw [integral_supportT_unreduced_gen N g L C hg e p, sig_univ]
  rw [sig_congr _ _ (fun R K => phiGen N g L C e p (R ∩ D) (K ∩ D) R.card K.card)
    (fun R _ K _ => pieceTermGen_eq g L C e p R K)]
  rw [show (Finset.univ : Finset (Fin N)) = D ∪ Dᶜ from (Finset.union_compl D).symm,
    sig_union Dᶜ D disjoint_compl_right]
  unfold gramGen
  rw [← hD]
  refine Finset.sum_congr rfl fun A hA => Finset.sum_congr rfl fun B hB => ?_
  have hAD : A ⊆ D := Finset.mem_powerset.mp hA
  have hBD : B ⊆ D := fun i hi => (Finset.mem_sdiff.mp (Finset.mem_powerset.mp hB hi)).1
  congr 1
  rw [sig_congr _ _ (fun R K => phiGen N g L C e p A B (A.card + R.card) (B.card + K.card)),
    sig_card Dᶜ (fun r k => phiGen N g L C e p A B (A.card + r) (B.card + k))]
  intro R hR K hK
  have hRD : Disjoint A R := Finset.disjoint_of_subset_left hAD
    (Finset.disjoint_of_subset_right hR disjoint_compl_right)
  have hKs : K ⊆ Dᶜ := fun i hi => (Finset.mem_sdiff.mp (hK hi)).1
  have hKD : Disjoint B K := Finset.disjoint_of_subset_left hBD
    (Finset.disjoint_of_subset_right hKs disjoint_compl_right)
  have e1 : (A ∪ R) ∩ D = A := by
    ext i; constructor
    · intro h
      rcases Finset.mem_union.mp (Finset.mem_inter.mp h).1 with h' | h'
      · exact h'
      · exact absurd (Finset.mem_inter.mp h).2 (Finset.mem_compl.mp (hR h'))
    · intro h; exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ h, hAD h⟩
  have e2 : (B ∪ K) ∩ D = B := by
    ext i; constructor
    · intro h
      rcases Finset.mem_union.mp (Finset.mem_inter.mp h).1 with h' | h'
      · exact h'
      · exact absurd (Finset.mem_inter.mp h).2 (Finset.mem_compl.mp (hKs h'))
    · intro h; exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ h, hBD h⟩
  simp only [e1, e2, Finset.card_union_of_disjoint hRD, Finset.card_union_of_disjoint hKD]


/-! ## Symmetry, rationality, and consistency with V2b -/

theorem supportT_comp_perm {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (τ : Equiv.Perm (Fin N))
    (x : Fin N → ℝ) : (fun i => x (τ i)) ∈ supportT N g L C ↔ x ∈ supportT N g L C := by
  classical
  have hsum : ∑ i, x (τ i) = ∑ i, x i := Equiv.sum_comp τ x
  have hcard : (roughSet g (fun i => x (τ i))).card = (roughSet g x).card := by
    unfold roughSet
    simp only [Finset.card_filter]
    exact Equiv.sum_comp τ (fun j => if g < x j then 1 else 0)
  have hR : ∑ i ∈ roughSet g (fun i => x (τ i)), x (τ i) = ∑ i ∈ roughSet g x, x i := by
    unfold roughSet
    simp only [Finset.sum_filter]
    exact Equiv.sum_comp τ (fun j => if g < x j then x j else 0)
  simp only [supportT, Set.mem_ofPred_eq, hsum, hcard, hR]
  constructor
  · rintro ⟨h0, h1, h2⟩; exact ⟨fun j => by simpa using h0 (τ.symm j), h1, h2⟩
  · rintro ⟨h0, h1, h2⟩; exact ⟨fun i => h0 (τ i), h1, h2⟩

/-- **Permutation invariance**: integrals over the support do not see the order of the
coordinates. -/
theorem integral_supportT_perm {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (τ : Equiv.Perm (Fin N))
    (f : (Fin N → ℝ) → ℝ) :
    ∫ x in supportT N g L C, f (fun i => x (τ i)) = ∫ x in supportT N g L C, f x := by
  rw [← integral_indicator (supportT_measurableSet N g L C),
    ← integral_indicator (supportT_measurableSet N g L C), integral_reindex τ]
  congr 1
  funext w
  by_cases hw : w ∈ supportT N g L C
  · have : (fun i => w (τ.symm i)) ∈ supportT N g L C := by
      rw [← supportT_comp_perm g L C τ]; simpa using hw
    rw [Set.indicator_of_mem this, Set.indicator_of_mem hw]
    simp
  · have : (fun i => w (τ.symm i)) ∉ supportT N g L C := by
      rw [← supportT_comp_perm g L C τ]; simpa using hw
    rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hw]

/-- The closed form is symmetric under permuting the exponent vector. -/
theorem gramGen_perm {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (e : Fin N → ℕ) (p : ℕ)
    (τ : Equiv.Perm (Fin N)) :
    gramGen N g L C (fun i => e (τ i)) p = gramGen N g L C e p := by
  rw [← integral_supportT_gen N g L C hg, ← integral_supportT_gen N g L C hg]
  have := integral_supportT_perm g L C τ.symm
    (fun x => (L - ∑ i, x i) ^ p * ∏ i, x i ^ e i)
  rw [← this]
  congr 1
  funext x
  congr 1
  · rw [Equiv.sum_comp τ.symm x]
  · rw [← Equiv.prod_comp τ (fun j => x (τ.symm j) ^ e j)]
    simp

theorem twoGroupW_ratCast (n r A B p : ℕ) (W c M : ℚ) :
    ((twoGroupW n r A B p W c M : ℚ) : ℝ) = twoGroupW n r A B p (W : ℝ) (c : ℝ) (M : ℝ) := by
  unfold twoGroupW
  by_cases h : 0 ≤ c ∧ 0 ≤ M
  · have h' : (0 : ℝ) ≤ c ∧ (0 : ℝ) ≤ M := ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
    rw [if_pos h, if_pos h']
    push_cast [Rat.cast_min]
    rfl
  · have h' : ¬((0 : ℝ) ≤ c ∧ (0 : ℝ) ≤ M) :=
      fun h' => h ⟨by exact_mod_cast h'.1, by exact_mod_cast h'.2⟩
    rw [if_neg h, if_neg h', Rat.cast_zero]

/-- The closed form commutes with `ℚ → ℝ`: at rational data every value is rational. -/
theorem gramGen_ratCast (N : ℕ) (g L : ℚ) (C : ℕ → ℚ) (e : Fin N → ℕ) (p : ℕ) :
    ((gramGen N g L C e p : ℚ) : ℝ) = gramGen N (g : ℝ) (L : ℝ) (fun m => (C m : ℝ)) e p := by
  unfold gramGen phiGen
  push_cast [twoGroupW_ratCast, apply_ite (Rat.cast : ℚ → ℝ)]
  rfl

/-- **Consistency with V2b**: for one distinguished coordinate the general closed form is V2b's. -/
theorem gramGen_single (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (a : Fin N) (e p : ℕ) :
    gramGen N g L C (fun i => if i = a then e else 0) p = gramFormula N g L C e p := by
  rw [← integral_supportT_gen N g L C hg, ← integral_supportT N g L C hg a e p]
  congr 1
  funext x
  congr 1
  simp [Finset.prod_ite_eq']


/-! ## Products of power sums and the generators of `B₂₁` -/


/-- `∏_{q ∈ qs} P_q(x) = Σ_φ ∏ᵢ xᵢ^{expo qs φ i}`: a product of power sums is a sum of monomials
indexed by placements of its parts. -/
theorem prod_power_sums {N : ℕ} (qs : List ℕ) (x : Fin N → ℝ) :
    (qs.map (fun q => ∑ i, x i ^ q)).prod =
      ∑ φ : Fin qs.length → Fin N, ∏ i, x i ^ expo qs φ i := by
  classical
  rw [← Fin.prod_univ_fun_getElem, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun φ _ => ?_
  unfold expo
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [← Finset.prod_fiberwise Finset.univ φ (fun j => x (φ j) ^ qs[j.1])]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j hj => ?_
  rw [(Finset.mem_filter.mp hj).2]

/-- V0's generator `(L − P₁)^a P_λ` evaluated at `x`. -/
theorem eval_gen (a : ℕ) (lam : Multiset ℕ) (x : Fin 45 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a lam) =
      (53 / 50 - ∑ i, x i) ^ a * (lam.map (fun q => ∑ i, x i ^ q)).prod := by
  rw [← MvPolynomial.coe_eval₂Hom]
  simp only [BGP212.Var.gen, BGP212.Var.Plam, map_mul, map_pow, map_sub, map_multiset_prod,
    Multiset.map_map, Function.comp_def, BGP212.Var.P, MvPolynomial.psum, map_sum,
    MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, BGP212.Params.L]
  norm_num

/-- **An `I_T` Gram entry on `B₂₁` in closed form** (cap function `C`, any `g ≥ 0`): for parts
`qs`, `qs'` the entry `∫_{T̃} gen a qs · gen a' qs'` is the sum over placements `φ` of the parts
of `gramGen` with weight `(L − P₁)^{a + a'}`. -/
theorem gram_entry_gen_list (g : ℝ) (hg : 0 ≤ g) (C : ℕ → ℝ) (a a' : ℕ) (qs qs' : List ℕ) :
    ∫ x in supportT 45 g (53 / 50) C,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a ↑qs) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a' ↑qs') =
      ∑ φ : Fin (qs ++ qs').length → Fin 45,
        gramGen 45 g (53 / 50) C (expo (qs ++ qs') φ) (a + a') := by
  have hfun : ∀ x : Fin 45 → ℝ,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a ↑qs) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a' ↑qs') =
      ∑ φ : Fin (qs ++ qs').length → Fin 45,
        (53 / 50 - ∑ i, x i) ^ (a + a') * ∏ i, x i ^ expo (qs ++ qs') φ i := by
    intro x
    rw [eval_gen, eval_gen, ← Finset.mul_sum, ← prod_power_sums, List.map_append, List.prod_append]
    simp only [Multiset.map_coe, Multiset.prod_coe]
    ring
  simp_rw [hfun]
  rw [integral_finsetSum]
  · exact Finset.sum_congr rfl fun φ _ => integral_supportT_gen 45 g (53 / 50) C hg _ _
  · intro φ _
    exact ((by fun_prop : Continuous fun x : Fin 45 → ℝ =>
      (53 / 50 - ∑ i, x i) ^ (a + a') * ∏ i, x i ^ expo (qs ++ qs') φ i).continuousOn.integrableOn_compact
      (simplexF_isCompact (ι := Fin 45) (53 / 50))).mono_set (supportT_subset_simplexF 45 g _ C)

/-- **Every `I_T` Gram entry on `B₂₁` is an explicit rational** (Proposition 10.2 for `I_T`):
at Table 3 the entry of the basis elements `i`, `j` (`B21Idx`) is the cast of a finite sum of
rational closed forms. -/
theorem gram_entry_B21_rat (i j : BGP212.Var.B21Idx) :
    ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ)),
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.genIdx i) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.genIdx j) =
      ((∑ φ : Fin (i.lam.toList ++ j.lam.toList).length → Fin 45,
        gramGen 45 BGP212.Params.g BGP212.Params.L BGP212.Params.C
          (expo (i.lam.toList ++ j.lam.toList) φ) (i.a + j.a) : ℚ) : ℝ) := by
  unfold BGP212.Var.genIdx
  have h := gram_entry_gen_list (41 / 625) (by norm_num) (fun m => (BGP212.Params.C m : ℝ))
    i.a j.a i.lam.toList j.lam.toList
  simp only [Multiset.coe_toList] at h
  rw [h, Rat.cast_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [gramGen_ratCast]
  norm_num [BGP212.Params.g, BGP212.Params.L]


/-! ## Transport to the distinguished coordinates -/

section Transport
variable {K : Type*} [Field K] [LinearOrder K] {N d : ℕ}

/-- Reindexing subsets of `s.map ι` by subsets of `s`. -/
theorem sum_powerset_map {M : Type*} [AddCommMonoid M] (ι : Fin d ↪ Fin N) (s : Finset (Fin d))
    (F : Finset (Fin N) → M) :
    ∑ A ∈ (s.map ι).powerset, F A = ∑ A' ∈ s.powerset, F (A'.map ι) := by
  classical
  refine (Finset.sum_nbij' (fun A' => A'.map ι) (fun A => s.filter (fun j => ι j ∈ A))
    ?_ ?_ ?_ ?_ ?_).symm
  · intro A' hA'
    simp only [Finset.mem_coe, Finset.mem_powerset] at hA' ⊢
    exact Finset.map_subset_map.mpr hA'
  · intro A _; simp [Finset.filter_subset]
  · intro A' hA'
    simp only [Finset.mem_coe, Finset.mem_powerset] at hA'
    ext j; rw [Finset.mem_filter, Finset.mem_map' ι]
    exact ⟨fun h => h.2, fun h => ⟨hA' h, h⟩⟩
  · intro A hA
    simp only [Finset.mem_coe, Finset.mem_powerset] at hA
    ext x; constructor
    · intro hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hx
      exact (Finset.mem_filter.mp hj).2
    · intro hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp (hA hx)
      exact Finset.mem_map_of_mem ι (Finset.mem_filter.mpr ⟨hj, hx⟩)
  · intro A' _; rfl

theorem extend_apply_emb (ι : Fin d ↪ Fin N) (f : Fin d → ℕ) (j : Fin d) :
    Function.extend ι f 0 (ι j) = f j := ι.injective.extend_apply f 0 j

theorem extend_apply_notMem (ι : Fin d ↪ Fin N) (f : Fin d → ℕ) (i : Fin N)
    (hi : i ∉ Finset.univ.map ι) : Function.extend ι f 0 i = 0 := by
  exact Function.extend_apply' _ _ _ (by
    rintro ⟨j, rfl⟩; exact hi (Finset.mem_map_of_mem ι (Finset.mem_univ j)))

/-- Products over `Fin N` of factors equal to one off the image of `ι`. -/
theorem prod_over_emb {M : Type*} [CommMonoid M] (ι : Fin d ↪ Fin N) (F : Fin N → M)
    (h1 : ∀ i ∉ Finset.univ.map ι, F i = 1) : ∏ i, F i = ∏ j, F (ι j) := by
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.map ι)) (fun i _ hi => h1 i hi),
    Finset.prod_map]

theorem suppE_extend (ι : Fin d ↪ Fin N) (es : Fin d → ℕ) (hes : ∀ j, es j ≠ 0) :
    suppE (Function.extend ι es 0) = Finset.univ.map ι := by
  classical
  ext i
  simp only [suppE, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    by_contra hi
    exact h (extend_apply_notMem ι es i hi)
  · intro hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
    rw [extend_apply_emb]; exact hes j

/-- Extension by zero along `ι`, as an embedding of exponent vectors. -/
noncomputable def extendEmb (ι : Fin d ↪ Fin N) : (Fin d → ℕ) ↪ (Fin N → ℕ) :=
  ⟨fun t => Function.extend ι t 0, fun t t' h => by
    funext j; have := congrFun h (ι j); simp only at this
    rwa [extend_apply_emb, extend_apply_emb] at this⟩

theorem extendEmb_apply (ι : Fin d ↪ Fin N) (t : Fin d → ℕ) :
    extendEmb ι t = Function.extend ι t 0 := rfl

/-- The exponent vectors below `extend ι es` are the extensions of those below `es`. -/
theorem piFinset_extend (ι : Fin d ↪ Fin N) (es : Fin d → ℕ) :
    Fintype.piFinset (fun i => Finset.range (Function.extend ι es 0 i + 1)) =
      (Fintype.piFinset (fun j => Finset.range (es j + 1))).map (extendEmb ι) := by
  classical
  ext t
  simp only [Fintype.mem_piFinset, Finset.mem_range, Finset.mem_map, extendEmb_apply]
  constructor
  · intro ht
    refine ⟨fun j => t (ι j), fun j => by simpa [extend_apply_emb] using ht (ι j), ?_⟩
    funext i
    by_cases hi : i ∈ Finset.univ.map ι
    · obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
      rw [extend_apply_emb]
    · rw [extend_apply_notMem ι _ i hi]
      have := ht i
      rw [extend_apply_notMem ι es i hi] at this
      omega
  · rintro ⟨t', ht', rfl⟩ i
    by_cases hi : i ∈ Finset.univ.map ι
    · obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
      rw [extend_apply_emb, extend_apply_emb]; exact ht' j
    · rw [extend_apply_notMem ι _ i hi, extend_apply_notMem ι _ i hi]; omega

theorem phiGen_extend (ι : Fin d ↪ Fin N) (es : Fin d → ℕ) (g L : K) (C : ℕ → K) (p : ℕ)
    (A B : Finset (Fin d)) (ρ κ : ℕ) :
    phiGen N g L C (Function.extend ι es 0) p (A.map ι) (B.map ι) ρ κ =
      phiFin N d g L C es p A B ρ κ := by
  classical
  unfold phiGen phiFin
  rw [piFinset_extend, Finset.sum_map]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [extendEmb_apply]
  have hout : ∀ i ∉ Finset.univ.map ι, Function.extend ι t 0 i = 0 :=
    fun i hi => extend_apply_notMem ι t i hi
  have hout' : ∀ i ∉ Finset.univ.map ι, Function.extend ι es 0 i = 0 :=
    fun i hi => extend_apply_notMem ι es i hi
  congr 1
  · rw [prod_over_emb ι]
    · refine Finset.prod_congr rfl fun j _ => ?_
      simp only [extend_apply_emb, ← Finset.map_union, Finset.mem_map' ι]
    · intro i hi; simp [hout i hi, hout' i hi]
  · have hA : ∑ i ∈ A.map ι, Function.extend ι t 0 i = ∑ j ∈ A, t j := by
      rw [Finset.sum_map]; exact Finset.sum_congr rfl fun j _ => extend_apply_emb ι t j
    have hall : ∑ i, Function.extend ι t 0 i = ∑ j, t j := by
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ι))
        (fun i _ hi => hout i hi), Finset.sum_map]
      exact Finset.sum_congr rfl fun j _ => extend_apply_emb ι t j
    have hAc : ∑ i ∈ (A.map ι)ᶜ, Function.extend ι t 0 i = ∑ j ∈ Aᶜ, t j := by
      have h1 := Finset.sum_add_sum_compl (A.map ι) (fun i => Function.extend ι t 0 i)
      have h2 := Finset.sum_add_sum_compl A t
      rw [hA, hall] at h1
      omega
    have hW : ∏ i, ((Function.extend ι t 0 i).factorial : K) = ∏ j, ((t j).factorial : K) := by
      rw [prod_over_emb ι]
      · exact Finset.prod_congr rfl fun j _ => by rw [extend_apply_emb]
      · intro i hi; simp [hout i hi]
    rw [hA, hAc, hW]

/-- **Transport**: the closed form of a monomial whose exponents `es` sit on the image of an
embedding `ι : Fin d ↪ Fin N` is the `d`-indexed closed form `gramFin`. -/
theorem gramGen_extend (ι : Fin d ↪ Fin N) (es : Fin d → ℕ) (hes : ∀ j, es j ≠ 0) (g L : K)
    (C : ℕ → K) (p : ℕ) :
    gramGen N g L C (Function.extend ι es 0) p = gramFin N d g L C es p := by
  classical
  have hcard : (Finset.univ.map ι)ᶜ.card = N - d := by
    rw [Finset.card_compl, Finset.card_map, Finset.card_univ, Fintype.card_fin, Fintype.card_fin]
  unfold gramGen gramFin finRow finCell
  rw [suppE_extend ι es hes, hcard, sum_powerset_map ι Finset.univ]
  simp_rw [← Finset.map_sdiff]
  simp_rw [sum_powerset_map ι (Finset.univ \ _), Finset.card_map, phiGen_extend ι es g L C p]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [Finset.sum_comm]

end Transport


/-! ## The worked example: `I_T[(1, (2)), (0, (2))] = ∫_{T̃} (L − P₁) P₂²` -/

theorem pairExp_comp_perm {N : ℕ} (π : Equiv.Perm (Fin N)) (a b : Fin N) (x y : ℕ) :
    (fun k => pairExp (π a) (π b) x y (π k)) = pairExp a b x y := by
  funext k; simp [pairExp, π.injective.eq_iff]

theorem gramGen_pair_perm {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (π : Equiv.Perm (Fin N))
    (a b : Fin N) (x y p : ℕ) :
    gramGen N g L C (pairExp (π a) (π b) x y) p = gramGen N g L C (pairExp a b x y) p := by
  rw [← gramGen_perm g L C hg (pairExp (π a) (π b) x y) p π, pairExp_comp_perm]

theorem perm_pair (i j : Fin 45) (hij : i ≠ j) : ∃ π : Equiv.Perm (Fin 45), π 0 = i ∧ π 1 = j := by
  set j' := Equiv.swap 0 i j with hj'
  have hj'0 : j' ≠ 0 := by
    intro h
    apply hij
    have : Equiv.swap 0 i j' = Equiv.swap 0 i 0 := by rw [h]
    rw [hj', Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    exact this.symm
  refine ⟨Equiv.swap 0 i * Equiv.swap 1 j', ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hj'0),
      Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hj', Equiv.swap_apply_self]

theorem mem_map_castLE {d N : ℕ} (h : d ≤ N) (k : Fin N) :
    k ∈ Finset.univ.map (Fin.castLEEmb h) ↔ k.val < d := by
  constructor
  · intro hk
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hk
    simp
  · intro hk
    exact Finset.mem_map.mpr ⟨⟨k.val, hk⟩, Finset.mem_univ _, by ext; simp⟩

theorem pairExp00_eq_extend :
    pairExp (0 : Fin 45) 0 2 2 = Function.extend (Fin.castLEEmb (by norm_num : 1 ≤ 45)) ![4] 0 := by
  funext k
  by_cases hk : k.val < 1
  · have : k = Fin.castLEEmb (by norm_num : 1 ≤ 45) 0 := by ext; simp; omega
    rw [this, extend_apply_emb]
    simp [pairExp]
  · rw [extend_apply_notMem _ _ _ (fun h => hk ((mem_map_castLE _ k).mp h))]
    have : (0 : Fin 45) ≠ k := by intro h; apply hk; rw [← h]; simp
    simp [pairExp, this]

theorem pairExp01_eq_extend :
    pairExp (0 : Fin 45) 1 2 2 = Function.extend (Fin.castLEEmb (by norm_num : 2 ≤ 45)) ![2, 2] 0 := by
  funext k
  by_cases hk : k.val < 2
  · rcases (show k.val = 0 ∨ k.val = 1 by omega) with h | h
    · have : k = Fin.castLEEmb (by norm_num : 2 ≤ 45) 0 := by ext; simp; omega
      rw [this, extend_apply_emb]
      simp [pairExp]
    · have : k = Fin.castLEEmb (by norm_num : 2 ≤ 45) 1 := by ext; simp; omega
      rw [this, extend_apply_emb]
      simp [pairExp]
  · rw [extend_apply_notMem _ _ _ (fun h => hk ((mem_map_castLE _ k).mp h))]
    have h0 : (0 : Fin 45) ≠ k := by intro h; apply hk; rw [← h]; simp
    have h1 : (1 : Fin 45) ≠ k := by intro h; apply hk; rw [← h]; simp
    simp [pairExp, h0, h1]

theorem expo_two (φ : Fin 2 → Fin 45) : expo [2, 2] φ = pairExp (φ 0) (φ 1) 2 2 := by
  funext k
  simp only [expo, pairExp, Finset.sum_filter, Fin.sum_univ_two]
  rfl

/-- **The worked example as a Lebesgue integral**: the Gram entry of the `B₂₁` generators
`gen 1 (2) = (L − P₁) P₂` and `gen 0 (2) = P₂` over Table 3's support equals the rational
`gramExampleQ = 45 · gramFin 45 1 … ![4] 1 + 1980 · gramFin 45 2 … ![2, 2] 1`. -/
theorem gram_entry_example :
    ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ)),
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 1 {2}) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}) = (gramExampleQ : ℝ) := by
  have hg : (0 : ℝ) ≤ 41 / 625 := by norm_num
  set C' : ℕ → ℝ := fun m => (BGP212.Params.C m : ℝ)
  have h := gram_entry_gen_list (41 / 625) hg C' 1 0 [2] [2]
  simp only [Multiset.coe_singleton] at h
  rw [h]
  change ∑ φ : Fin 2 → Fin 45, gramGen 45 (41 / 625) (53 / 50) C' (expo [2, 2] φ) 1 = _
  simp_rw [expo_two]
  rw [Fintype.sum_equiv (piFinTwoEquiv fun _ => Fin 45)
    (fun φ : Fin 2 → Fin 45 => gramGen 45 (41 / 625) (53 / 50) C' (pairExp (φ 0) (φ 1) 2 2) 1)
    (fun q => gramGen 45 (41 / 625) (53 / 50) C' (pairExp q.1 q.2 2 2) 1) (fun φ => rfl),
    Fintype.sum_prod_type]
  -- every diagonal term is the `x₀⁴` term, every off-diagonal term the `x₀² x₁²` term
  set V4 := gramGen 45 (41 / 625) (53 / 50) C' (pairExp (0 : Fin 45) 0 2 2) 1 with hV4
  set V22 := gramGen 45 (41 / 625) (53 / 50) C' (pairExp (0 : Fin 45) 1 2 2) 1 with hV22
  have hrow : ∀ i : Fin 45, ∑ j, gramGen 45 (41 / 625) (53 / 50) C' (pairExp i j 2 2) 1 =
      V4 + 44 * V22 := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hd : gramGen 45 (41 / 625) (53 / 50) C' (pairExp i i 2 2) 1 = V4 := by
      have := gramGen_pair_perm (41 / 625) (53 / 50) C' hg (Equiv.swap 0 i) 0 0 2 2 1
      rwa [Equiv.swap_apply_left] at this
    have ho : ∀ j ∈ Finset.univ.erase i,
        gramGen 45 (41 / 625) (53 / 50) C' (pairExp i j 2 2) 1 = V22 := by
      intro j hj
      obtain ⟨π, h0, h1⟩ := perm_pair i j (Finset.ne_of_mem_erase hj).symm
      have := gramGen_pair_perm (41 / 625) (53 / 50) C' hg π 0 1 2 2 1
      rwa [h0, h1] at this
    rw [hd, Finset.sum_congr rfl ho, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  -- the two closed forms are rational and transport to `gramFin`
  have hcast : ∀ e : Fin 45 → ℕ, gramGen 45 (41 / 625) (53 / 50) C' e 1 =
      ((gramGen 45 BGP212.Params.g BGP212.Params.L BGP212.Params.C e 1 : ℚ) : ℝ) := by
    intro e
    rw [gramGen_ratCast]
    norm_num [BGP212.Params.g, BGP212.Params.L, C']
  rw [hV4, hV22, hcast, hcast, pairExp00_eq_extend, pairExp01_eq_extend,
    gramGen_extend _ _ (by decide), gramGen_extend _ _ (by decide), gramExampleQ]
  push_cast
  ring


/-! ## Boundary cases and the example's value -/

/-- **No distinguished coordinates**: the weight alone. -/
theorem integral_supportT_gen_zero (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (p : ℕ) :
    ∫ x in supportT N g L C, (L - ∑ i, x i) ^ p = gramGen N g L C (fun _ => 0) p := by
  have := integral_supportT_gen N g L C hg (fun _ => 0) p
  simpa using this

/-- **Transport with `d = 0`**: no distinguished coordinates means `ℝ⁰`-indexed placements. -/
theorem gramGen_zero_eq_gramFin {K : Type*} [Field K] [LinearOrder K] (N : ℕ) (g L : K)
    (C : ℕ → K) (p : ℕ) :
    gramGen N g L C (fun _ => 0) p = gramFin N 0 g L C (fun j => Fin.elim0 j) p := by
  have h := gramGen_extend (Function.Embedding.ofIsEmpty : Fin 0 ↪ Fin N) (fun j => Fin.elim0 j)
    (fun j => Fin.elim0 j) g L C p
  rw [← h]
  congr 1
  funext i
  rw [Function.extend_apply' _ _ _ (by rintro ⟨j, _⟩; exact Fin.elim0 j)]; rfl

/-- The worked example with its value written out. -/
theorem gram_entry_example_value :
    ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ)),
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 1 {2}) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}) =
      ((137298584564364583040656350685550336257431495996990751744468934280064336098260362229316931024625739589775233656525053362941567700763204912417959573912272077 /
        25188665542194335395595466258527403622273264847539240886103567442802100740138282822244697456426365533843636512756347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) := by
  rw [gram_entry_example, gramExampleQ_eq]

end BGP212.Gram

/-! ## Comparator wrappers -/

namespace BGP212.Challenge

open BGP212.Gram MeasureTheory

theorem piece_integral_general (N : ℕ) (R : Finset (Fin N)) (t : Fin N → ℕ) (p : ℕ) (c M : ℝ) :
    ∫ y in pieceSet N R c M, (∏ i, y i ^ t i) * (M - ∑ i, y i) ^ p =
      twoGroupW (N - R.card) R.card (∑ i ∈ R, t i) (∑ i ∈ Rᶜ, t i) p
        (∏ i, ((t i).factorial : ℝ)) c M :=
  BGP212.Gram.piece_integral_general N R t p c M

theorem integral_supportT_unreduced_gen (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (e : Fin N → ℕ) (p : ℕ) :
    ∫ x in supportT N g L C, (L - ∑ i, x i) ^ p * ∏ i, x i ^ e i =
      ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * pieceTermGen g L C e p R K :=
  BGP212.Gram.integral_supportT_unreduced_gen N g L C hg e p

theorem sig_insert {N : ℕ} (U : Finset (Fin N)) (a : Fin N) (ha : a ∉ U) (G : Finset (Fin N) → Finset (Fin N) → ℝ) :
    Sig (insert a U) G = Sig U G + Sig U (fun R K => G (insert a R) K) -
      Sig U (fun R K => G R (insert a K)) :=
  BGP212.Gram.sig_insert U a ha G

theorem sig_union {N : ℕ} (E D : Finset (Fin N)) (hDE : Disjoint D E) (G : Finset (Fin N) → Finset (Fin N) → ℝ) :
    Sig (D ∪ E) G = ∑ A ∈ D.powerset, ∑ B ∈ (D \ A).powerset,
      (-1 : ℝ) ^ B.card * Sig E (fun R K => G (A ∪ R) (B ∪ K)) :=
  BGP212.Gram.sig_union E D hDE G

theorem sig_card {N : ℕ} (E : Finset (Fin N)) (φ : ℕ → ℕ → ℝ) :
    Sig E (fun R K => φ R.card K.card) =
      ∑ r ∈ Finset.range (E.card + 1), (E.card.choose r : ℝ) *
        ∑ k ∈ Finset.range (E.card - r + 1), ((E.card - r).choose k : ℝ) *
          ((-1 : ℝ) ^ k * φ r k) :=
  BGP212.Gram.sig_card E φ

theorem pieceTermGen_eq {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (e : Fin N → ℕ) (p : ℕ) (R K : Finset (Fin N)) :
    pieceTermGen g L C e p R K =
      phiGen N g L C e p (R ∩ suppE e) (K ∩ suppE e) R.card K.card :=
  BGP212.Gram.pieceTermGen_eq g L C e p R K

theorem integral_supportT_gen (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (e : Fin N → ℕ) (p : ℕ) :
    ∫ x in supportT N g L C, (L - ∑ i, x i) ^ p * ∏ i, x i ^ e i = gramGen N g L C e p :=
  BGP212.Gram.integral_supportT_gen N g L C hg e p

theorem integral_supportT_gen_zero (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (p : ℕ) :
    ∫ x in supportT N g L C, (L - ∑ i, x i) ^ p = gramGen N g L C (fun _ => 0) p :=
  BGP212.Gram.integral_supportT_gen_zero N g L C hg p

theorem integral_supportT_perm {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (τ : Equiv.Perm (Fin N)) (f : (Fin N → ℝ) → ℝ) :
    ∫ x in supportT N g L C, f (fun i => x (τ i)) = ∫ x in supportT N g L C, f x :=
  BGP212.Gram.integral_supportT_perm g L C τ f

theorem gramGen_perm {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (e : Fin N → ℕ) (p : ℕ) (τ : Equiv.Perm (Fin N)) :
    gramGen N g L C (fun i => e (τ i)) p = gramGen N g L C e p :=
  BGP212.Gram.gramGen_perm g L C hg e p τ

theorem gramGen_ratCast (N : ℕ) (g L : ℚ) (C : ℕ → ℚ) (e : Fin N → ℕ) (p : ℕ) :
    ((gramGen N g L C e p : ℚ) : ℝ) = gramGen N (g : ℝ) (L : ℝ) (fun m => (C m : ℝ)) e p :=
  BGP212.Gram.gramGen_ratCast N g L C e p

theorem gramGen_single (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (a : Fin N) (e p : ℕ) :
    gramGen N g L C (fun i => if i = a then e else 0) p = gramFormula N g L C e p :=
  BGP212.Gram.gramGen_single N g L C hg a e p

theorem gramGen_extend {K : Type*} [Field K] [LinearOrder K] {N d : ℕ} (ι : Fin d ↪ Fin N) (es : Fin d → ℕ) (hes : ∀ j, es j ≠ 0) (g L : K) (C : ℕ → K) (p : ℕ) :
    gramGen N g L C (Function.extend ι es 0) p = gramFin N d g L C es p :=
  BGP212.Gram.gramGen_extend ι es hes g L C p

theorem gramGen_zero_eq_gramFin {K : Type*} [Field K] [LinearOrder K] (N : ℕ) (g L : K) (C : ℕ → K) (p : ℕ) :
    gramGen N g L C (fun _ => 0) p = gramFin N 0 g L C (fun j => Fin.elim0 j) p :=
  BGP212.Gram.gramGen_zero_eq_gramFin N g L C p

theorem prod_power_sums {N : ℕ} (qs : List ℕ) (x : Fin N → ℝ) :
    (qs.map (fun q => ∑ i, x i ^ q)).prod =
      ∑ φ : Fin qs.length → Fin N, ∏ i, x i ^ expo qs φ i :=
  BGP212.Gram.prod_power_sums qs x

theorem eval_gen (a : ℕ) (lam : Multiset ℕ) (x : Fin 45 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a lam) =
      (53 / 50 - ∑ i, x i) ^ a * (lam.map (fun q => ∑ i, x i ^ q)).prod :=
  BGP212.Gram.eval_gen a lam x

theorem gram_entry_gen_list (g : ℝ) (hg : 0 ≤ g) (C : ℕ → ℝ) (a a' : ℕ) (qs qs' : List ℕ) :
    ∫ x in supportT 45 g (53 / 50) C,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a ↑qs) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a' ↑qs') =
      ∑ φ : Fin (qs ++ qs').length → Fin 45,
        gramGen 45 g (53 / 50) C (expo (qs ++ qs') φ) (a + a') :=
  BGP212.Gram.gram_entry_gen_list g hg C a a' qs qs'

theorem gram_entry_B21_rat (i j : BGP212.Var.B21Idx) :
    ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ)),
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.genIdx i) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.genIdx j) =
      ((∑ φ : Fin (i.lam.toList ++ j.lam.toList).length → Fin 45,
        gramGen 45 BGP212.Params.g BGP212.Params.L BGP212.Params.C
          (expo (i.lam.toList ++ j.lam.toList) φ) (i.a + j.a) : ℚ) : ℝ) :=
  BGP212.Gram.gram_entry_B21_rat i j

theorem gramExampleQ_eq :
    gramExampleQ = (137298584564364583040656350685550336257431495996990751744468934280064336098260362229316931024625739589775233656525053362941567700763204912417959573912272077 /
        25188665542194335395595466258527403622273264847539240886103567442802100740138282822244697456426365533843636512756347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) :=
  BGP212.Gram.gramExampleQ_eq

theorem gram_entry_example :
    ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ)),
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 1 {2}) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}) = (gramExampleQ : ℝ) :=
  BGP212.Gram.gram_entry_example

theorem gram_entry_example_value :
    ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ)),
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 1 {2}) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}) =
      ((137298584564364583040656350685550336257431495996990751744468934280064336098260362229316931024625739589775233656525053362941567700763204912417959573912272077 /
        25188665542194335395595466258527403622273264847539240886103567442802100740138282822244697456426365533843636512756347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) :=
  BGP212.Gram.gram_entry_example_value

end BGP212.Challenge
