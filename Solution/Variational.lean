/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): (10.1) and §11 (the space B₂₁).
-/
import BGP212.Variational
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.FieldSimp

/-! # V0: `dim B₂₁ = 846` (proofs) -/

namespace BGP212.Var

open MvPolynomial

/-! ## Partitions: the enumeration `partsLE` -/

theorem mem_partsLE : ∀ (k j : ℕ) (s : Multiset ℕ),
    s ∈ partsLE j k ↔ (∀ x ∈ s, 0 < x ∧ x ≤ k) ∧ s.sum = j
  | 0, j, s => by
      by_cases hj : j = 0
      · subst hj
        simp only [partsLE, ite_true, List.mem_singleton]
        constructor
        · rintro rfl; simp
        · rintro ⟨h, -⟩
          exact Multiset.eq_zero_of_forall_notMem fun x hx => by have := h x hx; omega
      · simp only [partsLE, hj, ite_false, List.not_mem_nil, false_iff, not_and]
        intro h hs
        have : s = 0 := Multiset.eq_zero_of_forall_notMem fun x hx => by have := h x hx; omega
        subst this; simp at hs; omega
  | k + 1, j, s => by
      simp only [partsLE, List.mem_flatMap, List.mem_range, List.mem_map]
      constructor
      · rintro ⟨c, hc, t, ht, rfl⟩
        obtain ⟨ht1, ht2⟩ := (mem_partsLE k _ t).mp ht
        have hcj : c * (k + 1) ≤ j := by
          have := Nat.div_mul_le_self j (k + 1)
          have : c * (k + 1) ≤ j / (k + 1) * (k + 1) := Nat.mul_le_mul_right _ (by omega)
          omega
        refine ⟨fun x hx => ?_, ?_⟩
        · rcases Multiset.mem_add.mp hx with h | h
          · rw [Multiset.eq_of_mem_replicate h]; omega
          · have := ht1 x h; omega
        · simp [Multiset.sum_replicate, ht2]; omega
      · rintro ⟨h1, h2⟩
        have hdec : s = Multiset.replicate (s.count (k + 1)) (k + 1) + s.filter (· ≠ k + 1) := by
          rw [← Multiset.filter_eq', Multiset.filter_add_not]
        have hsum : s.count (k + 1) * (k + 1) + (s.filter (· ≠ k + 1)).sum = j := by
          rw [← h2]; conv_rhs => rw [hdec]
          simp [Multiset.sum_replicate]
        refine ⟨s.count (k + 1), ?_, s.filter (· ≠ k + 1), ?_, hdec.symm⟩
        · exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le (by omega)).mpr (by omega))
        · refine (mem_partsLE k _ _).mpr ⟨fun x hx => ?_, by omega⟩
          obtain ⟨hx1, hx2⟩ := Multiset.mem_filter.mp hx
          have := h1 x hx1; omega

theorem nodup_partsLE : ∀ (k j : ℕ), (partsLE j k).Nodup
  | 0, j => by by_cases hj : j = 0 <;> simp [partsLE, hj]
  | k + 1, j => by
      simp only [partsLE]
      refine List.nodup_flatMap.mpr ⟨fun c _ => (nodup_partsLE k _).map
        (fun s t h => add_left_cancel h), ?_⟩
      refine (List.nodup_range).pairwise_of_forall_ne fun c _ d _ hcd => ?_
      rw [Function.onFun, List.disjoint_left]
      intro s hs ht
      obtain ⟨t1, ht1, rfl⟩ := List.mem_map.mp hs
      obtain ⟨t2, ht2, he⟩ := List.mem_map.mp ht
      have hc1 : (k + 1) ∉ t1 := fun h => by
        have := ((mem_partsLE k _ t1).mp ht1).1 _ h; omega
      have hc2 : (k + 1) ∉ t2 := fun h => by
        have := ((mem_partsLE k _ t2).mp ht2).1 _ h; omega
      have := congrArg (Multiset.count (k + 1)) he
      simp [Multiset.count_eq_zero.mpr hc1, Multiset.count_eq_zero.mpr hc2] at this
      exact hcd this.symm

/-- `p(j)` equals the length of the explicit enumeration. -/
theorem p_eq (j : ℕ) : p j = (partsLE j j).length := by
  classical
  have e : Nat.Partition j ≃ {s // s ∈ (partsLE j j).toFinset} :=
    { toFun := fun μ => ⟨μ.parts, List.mem_toFinset.mpr ((mem_partsLE j j _).mpr
        ⟨fun x hx => ⟨μ.parts_pos hx, μ.parts_sum ▸ Multiset.le_sum_of_mem hx⟩, μ.parts_sum⟩)⟩
      invFun := fun s => ⟨s.1, fun hx => ((mem_partsLE j j _).mp
        (List.mem_toFinset.mp s.2)).1 _ hx |>.1, ((mem_partsLE j j _).mp
        (List.mem_toFinset.mp s.2)).2⟩
      left_inv := fun μ => by ext; rfl
      right_inv := fun s => rfl }
  rw [p, Fintype.card_congr e, Fintype.card_coe, List.toFinset_card_of_nodup (nodup_partsLE j j)]

/-! ## Counting -/

theorem partition_counts :
    (List.range 11).map p = [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42] := by
  rw [show (List.range 11).map p = (List.range 11).map (fun j => (partsLE j j).length) from
    List.map_congr_left fun j _ => p_eq j]
  decide +kernel

theorem dimension_identity : ∑ j ∈ Finset.range 11, p j * (22 - 2 * j) = 846 := by
  rw [Finset.sum_congr rfl fun j _ => by rw [p_eq j]]
  decide +kernel

theorem card_B21Idx : Fintype.card B21Idx = 846 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [← dimension_identity, ← Fin.sum_univ_eq_sum_range (fun j => p j * (22 - 2 * j)) 11]
  rfl

/-- The ordered reading: `λ` as a sequence of positive even parts (a composition of `|λ|/2`)
gives 4094 index pairs; identifying reorderings gives the 846 of `card_B21Idx`. -/
theorem ordered_family_count :
    ∑ j ∈ Finset.range 11, Fintype.card (Composition j) * (22 - 2 * j) = 4094 := by
  simp only [composition_card]
  decide

/-! ## Indexing -/

theorem lam_sum (i : B21Idx) : i.lam.sum = 2 * (i.1 : ℕ) := by
  show (i.2.1.parts.map (2 * ·)).sum = _
  rw [Multiset.sum_map_mul_left, Multiset.map_id', i.2.1.parts_sum]

/-- **No duplicates**: distinct indices give distinct printed pairs `(a, λ)`. -/
theorem toPair_injective : Function.Injective B21Idx.toPair := by
  rintro ⟨j, μ, a⟩ ⟨j', μ', a'⟩ h
  simp only [B21Idx.toPair, Prod.mk.injEq] at h
  obtain ⟨ha, hl⟩ := h
  have hj : (j : ℕ) = j' := by
    have e1 := lam_sum ⟨j, μ, a⟩
    have e2 := lam_sum ⟨j', μ', a'⟩
    rw [hl] at e1
    dsimp only at e1 e2
    omega
  have hj' : j = j' := Fin.ext hj
  subst hj'
  have hμ : μ = μ' := by
    apply Nat.Partition.ext
    exact Multiset.map_injective (fun x y h => by simpa using h) hl
  subst hμ
  have : a = a' := Fin.ext ha
  subst this
  rfl

/-- **Coverage**: the printed pairs of `B21Idx` are exactly the pairs `(a, λ)` with positive even
parts and `a + |λ| ≤ 21`. -/
theorem toPair_range (a : ℕ) (lam : Multiset ℕ) :
    (∃ i : B21Idx, i.toPair = (a, lam)) ↔ IsB21Index a lam := by
  constructor
  · rintro ⟨⟨j, μ, a'⟩, h⟩
    simp only [B21Idx.toPair, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨fun x hx => ?_, ?_⟩
    · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      exact ⟨by have := μ.parts_pos hy; omega, ⟨y, by ring⟩⟩
    · rw [lam_sum ⟨j, μ, a'⟩]; simp only [B21Idx.a]; have := a'.2; omega
  · rintro ⟨hev, hle⟩
    have hhalf : lam = (lam.map (· / 2)).map (2 * ·) := by
      rw [Multiset.map_map]
      conv_lhs => rw [← Multiset.map_id lam]
      exact Multiset.map_congr rfl fun x hx => by
        obtain ⟨_, k, hk⟩ := hev x hx; simp only [id_eq, Function.comp_apply]; omega
    set μs := lam.map (· / 2)
    have hpos : ∀ x ∈ μs, 0 < x := fun x hx => by
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      obtain ⟨h1, k, hk⟩ := hev y hy; omega
    have hsum : lam.sum = 2 * μs.sum := by
      conv_lhs => rw [hhalf]
      rw [Multiset.sum_map_mul_left, Multiset.map_id']
    have hj : μs.sum < 11 := by omega
    refine ⟨⟨⟨μs.sum, hj⟩, ⟨μs, fun hx => hpos _ hx, rfl⟩, ⟨a, by simp; omega⟩⟩, ?_⟩
    simp only [B21Idx.toPair, B21Idx.a, B21Idx.lam, Prod.mk.injEq, true_and]
    exact hhalf.symm

/-- `B₂₁` is the span of the indexed family. -/
theorem B21_eq_span : B21 = Submodule.span ℚ (Set.range genIdx) := by
  unfold B21
  congr 1
  refine Set.ext fun f => ?_
  show (∃ a lam, IsB21Index a lam ∧ f = gen a lam) ↔ ∃ i, genIdx i = f
  constructor
  · rintro ⟨a, lam, hI, rfl⟩
    obtain ⟨i, hi⟩ := (toPair_range a lam).mpr hI
    simp only [B21Idx.toPair, Prod.mk.injEq] at hi
    exact ⟨i, by rw [genIdx, hi.1, hi.2]⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.a, i.lam, (toPair_range _ _).mp ⟨i, rfl⟩, rfl⟩

/-! ## The power sums `P₁, …, P₄₅` are algebraically independent -/

/-- A surjective endomorphism of a Noetherian ring is injective (the kernels of the iterates
stabilize). -/
theorem injective_of_surjective_endo {A : Type*} [CommRing A] [IsNoetherianRing A]
    (f : A →+* A) (hf : Function.Surjective f) : Function.Injective f := by
  have hmono : Monotone fun n : ℕ => RingHom.ker (f ^ n) := by
    refine monotone_nat_of_le_succ fun n x hx => ?_
    rw [RingHom.mem_ker] at hx ⊢
    simp only [pow_succ', RingHom.mul_def, RingHom.comp_apply, hx, map_zero]
  obtain ⟨N, hN⟩ := (monotone_stabilizes_iff_noetherian (R := A) (M := A)).mpr inferInstance
    ⟨_, hmono⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ : ∃ y, (f ^ N) y = x := by
    rw [RingHom.coe_pow]; exact (hf.iterate N) x
  have hy : y ∈ RingHom.ker (f ^ (N + 1)) := by
    simp only [RingHom.mem_ker, pow_succ', RingHom.mul_def, RingHom.comp_apply, hx]
  have := hN (N + 1) (Nat.le_succ N)
  simp only [OrderHom.coe_mk] at this
  rw [← this] at hy
  exact hy

/-- `y_k ↦ P_{k+1}`. -/
noncomputable def psi : Poly →ₐ[ℚ] Poly := aeval fun k : Fin 45 => P (k + 1)

theorem psum_mem_range (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ 45) : psum (Fin 45) ℚ j ∈ psi.range :=
  ⟨X ⟨j - 1, by omega⟩, by
    show (aeval fun k : Fin 45 => P (k + 1)) (X ⟨j - 1, by omega⟩) = psum (Fin 45) ℚ j
    rw [aeval_X, P]
    congr 1
    show j - 1 + 1 = j
    omega⟩

/-- Newton's identities: every `e_k`, `k ≤ 45`, is a polynomial in `P₁, …, P₄₅` over `ℚ`. -/
theorem esymm_mem_range : ∀ k, k ≤ 45 → esymm (Fin 45) ℚ k ∈ psi.range := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases k with _ | k
    · rw [esymm_zero]; exact Subalgebra.one_mem _
    have hneg : (-1 : Poly) ∈ psi.range := Subalgebra.neg_mem _ (Subalgebra.one_mem _)
    have hsum : (∑ a ∈ Finset.antidiagonal (k + 1) with a.1 < k + 1,
        (-1 : Poly) ^ a.1 * esymm (Fin 45) ℚ a.1 * psum (Fin 45) ℚ a.2) ∈ psi.range := by
      refine Subalgebra.sum_mem _ fun a ha => ?_
      simp only [Finset.mem_filter, Finset.mem_antidiagonal] at ha
      refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hneg _)
        (ih a.1 ha.2 (by omega))) (psum_mem_range a.2 (by omega) (by omega))
    have hkey : ((k + 1 : ℕ) : Poly) * esymm (Fin 45) ℚ (k + 1) ∈ psi.range := by
      rw [mul_esymm_eq_sum]
      exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hneg _) hsum
    have heq : esymm (Fin 45) ℚ (k + 1) =
        ((k + 1 : ℕ) : ℚ)⁻¹ • (((k + 1 : ℕ) : Poly) * esymm (Fin 45) ℚ (k + 1)) := by
      rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by positivity),
        one_smul]
    rw [heq]
    exact Subalgebra.smul_mem _ hkey _

theorem psi_range_symmetric : psi.range ≤ symmetricSubalgebra (Fin 45) ℚ := by
  rw [psi, ← Algebra.adjoin_range_eq_range_aeval]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨k, rfl⟩
  exact psum_isSymmetric _ _ _

/-- **The power sums `P₁, …, P₄₅` are algebraically independent over `ℚ`.** -/
theorem psi_injective : Function.Injective psi := by
  set S := symmetricSubalgebra (Fin 45) ℚ
  let ψS : Poly →ₐ[ℚ] S := psi.codRestrict S fun x => psi_range_symmetric ⟨x, rfl⟩
  let e := esymmAlgEquiv (Fin 45) ℚ (Fintype.card_fin 45)
  let φ : Poly →ₐ[ℚ] Poly := e.symm.toAlgHom.comp ψS
  have hφs : Function.Surjective φ := by
    rw [← AlgHom.range_eq_top, eq_top_iff, ← adjoin_range_X]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨y, hy⟩ := esymm_mem_range (i + 1) (by omega)
    refine ⟨y, ?_⟩
    have : ψS y = ⟨esymm (Fin 45) ℚ (i + 1), esymm_isSymmetric _ _ _⟩ := Subtype.ext hy
    show e.symm (ψS y) = X i
    rw [this]
    exact esymmAlgEquiv_symm_apply ℚ (Fintype.card_fin 45) i
  have hφi : Function.Injective φ :=
    injective_of_surjective_endo φ.toRingHom hφs
  intro x y hxy
  apply hφi
  simp only [φ, AlgHom.comp_apply]
  congr 1
  exact Subtype.ext hxy

/-! ## The family as images of distinct monomials -/

/-- The variable `y_{2q}` (0-based index `2q − 1`) carrying `P_{2q}`. -/
def idx (q : ℕ) : Fin 45 := ⟨(2 * q - 1) % 45, Nat.mod_lt _ (by norm_num)⟩

/-- The exponent vector of the monomial `y₁^a ∏_{q ∈ μ} y_{2q}`. -/
noncomputable def expo (i : B21Idx) : Fin 45 →₀ ℕ :=
  Finsupp.single 0 i.a + (i.2.1.parts.map fun q => Finsupp.single (idx q) 1).sum

/-- `y₁ ↦ L − y₁`, `y_k ↦ y_k` otherwise. -/
noncomputable def sigma : Poly →ₐ[ℚ] Poly :=
  aeval fun k : Fin 45 => if k = 0 then C BGP212.Params.L - X 0 else X k

theorem sigma_sigma (f : Poly) : sigma (sigma f) = f := by
  have : sigma.comp sigma = AlgHom.id ℚ Poly := by
    apply MvPolynomial.algHom_ext
    intro k
    by_cases hk : k = 0
    · subst hk; simp [sigma, aeval_X, map_sub, MvPolynomial.algebraMap_eq]
    · simp [sigma, aeval_X, hk]
  exact congrArg (fun φ : Poly →ₐ[ℚ] Poly => φ f) this

theorem sigma_injective : Function.Injective sigma :=
  Function.LeftInverse.injective sigma_sigma

theorem part_bounds (i : B21Idx) : ∀ q ∈ i.2.1.parts, 1 ≤ q ∧ q ≤ 10 := fun q hq =>
  ⟨i.2.1.parts_pos hq, by
    have := Multiset.le_sum_of_mem hq; rw [i.2.1.parts_sum] at this; have := i.1.2; omega⟩

theorem idx_val (q : ℕ) (h1 : 1 ≤ q) (h2 : q ≤ 10) : ((idx q : Fin 45) : ℕ) = 2 * q - 1 := by
  simp only [idx]; omega

theorem monomial_multiset (s : Multiset ℕ) :
    monomial ((s.map fun q => Finsupp.single (idx q) 1).sum) (1 : ℚ) =
      (s.map fun q => X (idx q)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons q s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons]
      rw [← ih, show (X (idx q) : Poly) = monomial (Finsupp.single (idx q) 1) 1 from rfl,
        monomial_mul_monomial, one_mul]

theorem genIdx_eq (i : B21Idx) : genIdx i = psi (sigma (monomial (expo i) 1)) := by
  have hsplit : monomial (expo i) (1 : ℚ) =
      X 0 ^ i.a * (i.2.1.parts.map fun q => X (idx q)).prod := by
    rw [expo, ← monomial_multiset, X_pow_eq_monomial, monomial_mul_monomial, one_mul]
  rw [hsplit, map_mul, map_mul, map_pow, map_pow, map_multiset_prod, map_multiset_prod,
    Multiset.map_map, Multiset.map_map]
  have hs0 : sigma (X 0) = C BGP212.Params.L - X 0 := by simp [sigma, aeval_X]
  have hsq : ∀ q ∈ i.2.1.parts, ((psi ∘ sigma) ∘ fun q => X (idx q)) q = P (2 * q) := by
    intro q hq
    obtain ⟨h1, h2⟩ := part_bounds i q hq
    have hne : idx q ≠ 0 := fun h => by
      have := congrArg Fin.val h; rw [idx_val q h1 h2] at this; simp at this; omega
    simp only [Function.comp_apply, sigma, aeval_X, hne, ite_false, psi]
    congr 1
    rw [idx_val q h1 h2]; omega
  rw [Multiset.map_congr rfl hsq, hs0]
  simp only [genIdx, gen, Plam, B21Idx.lam, B21Idx.a, Multiset.map_map, map_sub, psi, aeval_X,
    aeval_C, MvPolynomial.algebraMap_eq]
  rfl

theorem sum_single_apply (s : Multiset ℕ) (x : Fin 45) :
    (s.map fun q => Finsupp.single (idx q) 1).sum x = (s.filter fun q => idx q = x).card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons q s ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Finsupp.add_apply, ih,
        Multiset.filter_cons]
      by_cases h : idx q = x
      · simp [h]; omega
      · simp [h]

theorem expo_injective : Function.Injective expo := by
  intro i i' h
  apply toPair_injective
  have hb := part_bounds i
  have hb' := part_bounds i'
  have h0 : i.a = i'.a := by
    have := congrArg (fun f => f 0) h
    simp only [expo, Finsupp.add_apply, Finsupp.single_eq_same, sum_single_apply] at this
    have hz : ∀ q, 1 ≤ q → q ≤ 10 → idx q ≠ 0 := fun q h1 h2 e => by
      have hv := idx_val q h1 h2
      rw [e, Fin.val_zero] at hv
      omega
    have e1 : (i.2.1.parts.filter fun q => idx q = 0) = 0 := Multiset.filter_eq_nil.mpr
      fun q hq => hz q (hb q hq).1 (hb q hq).2
    have e2 : (i'.2.1.parts.filter fun q => idx q = 0) = 0 := Multiset.filter_eq_nil.mpr
      fun q hq => hz q (hb' q hq).1 (hb' q hq).2
    rw [e1, e2] at this; simpa using this
  have hparts : i.2.1.parts = i'.2.1.parts := by
    ext r
    by_cases hr : 1 ≤ r ∧ r ≤ 10
    · have := congrArg (fun f => f (idx r)) h
      simp only [expo, Finsupp.add_apply, sum_single_apply] at this
      have hr0 : (Finsupp.single (0 : Fin 45) i.a) (idx r) = 0 := by
        rw [Finsupp.single_apply, ite_eq_right_iff.mpr]; intro e; exfalso
        have := idx_val r hr.1 hr.2; rw [← e] at this; simp at this; omega
      have hr0' : (Finsupp.single (0 : Fin 45) i'.a) (idx r) = 0 := by
        rw [Finsupp.single_apply, ite_eq_right_iff.mpr]; intro e; exfalso
        have := idx_val r hr.1 hr.2; rw [← e] at this; simp at this; omega
      rw [hr0, hr0', zero_add, zero_add] at this
      have key : ∀ (s : Multiset ℕ), (∀ q ∈ s, 1 ≤ q ∧ q ≤ 10) →
          (s.filter fun q => idx q = idx r) = s.filter (· = r) := fun s hs =>
        Multiset.filter_congr fun q hq => by
          constructor
          · intro e; have := congrArg Fin.val e
            rw [idx_val q (hs q hq).1 (hs q hq).2, idx_val r hr.1 hr.2] at this; omega
          · rintro rfl; rfl
      rw [key _ hb, key _ hb', Multiset.filter_eq', Multiset.filter_eq'] at this
      simpa using this
    · have c1 : i.2.1.parts.count r = 0 := Multiset.count_eq_zero.mpr fun hm => hr (hb r hm)
      have c2 : i'.2.1.parts.count r = 0 := Multiset.count_eq_zero.mpr fun hm => hr (hb' r hm)
      rw [c1, c2]
  simp only [B21Idx.toPair, B21Idx.lam, h0, hparts]

/-- **The 846 spanning elements are linearly independent over `ℚ`.** -/
theorem genIdx_linearIndependent : LinearIndependent ℚ genIdx := by
  have hmono : LinearIndependent ℚ fun i : B21Idx => monomial (expo i) (1 : ℚ) := by
    have := (basisMonomials (Fin 45) ℚ).linearIndependent.comp expo expo_injective
    rw [coe_basisMonomials] at this
    exact this
  have hinj : Function.Injective (psi.comp sigma) := psi_injective.comp sigma_injective
  have heq : genIdx = (psi.comp sigma).toLinearMap ∘ fun i => monomial (expo i) (1 : ℚ) :=
    funext genIdx_eq
  rw [heq]
  exact hmono.map' (psi.comp sigma).toLinearMap (LinearMap.ker_eq_bot.mpr hinj)

/-- **`dim_ℚ B₂₁ = 846`.** -/
theorem finrank_B21 : Module.finrank ℚ B21 = 846 := by
  rw [B21_eq_span, finrank_span_eq_card genIdx_linearIndependent, card_B21Idx]

/-! ## Preparing V1: the algebra of (10.1) -/

theorem simplexMoment_nil (R : ℚ) : simplexMoment R [] = 1 := by
  simp [simplexMoment]

/-- `m = 1`: `∫₀^R z^e dz = R^{e+1}/(e+1)`. -/
theorem simplexMoment_single (R : ℚ) (e : ℕ) : simplexMoment R [e] = R ^ (e + 1) / (e + 1) := by
  simp only [simplexMoment, List.length_singleton, List.sum_singleton, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [show 1 + e = e + 1 by omega, Nat.factorial_succ]
  have : (e.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- **The Fubini step of (10.1).** Adding a coordinate `z` with exponent `u` multiplies the
`m`-dimensional moment, read as `c · (R − z)^{m + s}` with `c = ∏ eᵢ! / (m + s)!`, by the Beta
moment: `M_{m+1}(R; e, u) = c · ∫₀^R z^u (R − z)^{m+s} dz`. -/
theorem simplexMoment_snoc (R : ℚ) (e : List ℕ) (u : ℕ) :
    simplexMoment R (e ++ [u]) =
      ((e.map Nat.factorial).prod : ℚ) / ((e.length + e.sum).factorial : ℚ) *
        betaMoment R u (e.length + e.sum) := by
  simp only [simplexMoment, betaMoment, List.length_append, List.length_singleton,
    List.sum_append, List.sum_singleton, List.map_append, List.map_cons, List.map_nil,
    List.prod_append, List.prod_cons, List.prod_nil, mul_one]
  have h1 : e.length + 1 + (e.sum + u) = u + (e.length + e.sum) + 1 := by omega
  rw [h1]
  have : ((e.length + e.sum).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

end BGP212.Var

namespace BGP212.Challenge

open BGP212.Var

theorem mem_partsLE (k j : ℕ) (s : Multiset ℕ) :
    s ∈ partsLE j k ↔ (∀ x ∈ s, 0 < x ∧ x ≤ k) ∧ s.sum = j :=
  BGP212.Var.mem_partsLE k j s

theorem nodup_partsLE (k j : ℕ) : (partsLE j k).Nodup :=
  BGP212.Var.nodup_partsLE k j

theorem p_eq_enumeration (j : ℕ) : p j = (partsLE j j).length :=
  BGP212.Var.p_eq j

theorem partition_counts :
    (List.range 11).map p = [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42] :=
  BGP212.Var.partition_counts

theorem dimension_identity : ∑ j ∈ Finset.range 11, p j * (22 - 2 * j) = 846 :=
  BGP212.Var.dimension_identity

theorem card_B21Idx : Fintype.card B21Idx = 846 :=
  BGP212.Var.card_B21Idx

theorem ordered_family_count :
    ∑ j ∈ Finset.range 11, Fintype.card (Composition j) * (22 - 2 * j) = 4094 :=
  BGP212.Var.ordered_family_count

theorem toPair_injective : Function.Injective B21Idx.toPair :=
  BGP212.Var.toPair_injective

theorem toPair_range (a : ℕ) (lam : Multiset ℕ) :
    (∃ i : B21Idx, i.toPair = (a, lam)) ↔ IsB21Index a lam :=
  BGP212.Var.toPair_range a lam

theorem B21_eq_span : B21 = Submodule.span ℚ (Set.range genIdx) :=
  BGP212.Var.B21_eq_span

theorem power_sums_algebraically_independent :
    Function.Injective (MvPolynomial.aeval (R := ℚ) fun k : Fin 45 => P (k + 1)) :=
  BGP212.Var.psi_injective

theorem genIdx_linearIndependent : LinearIndependent ℚ genIdx :=
  BGP212.Var.genIdx_linearIndependent

theorem finrank_B21 : Module.finrank ℚ B21 = 846 :=
  BGP212.Var.finrank_B21

theorem simplexMoment_nil (R : ℚ) : simplexMoment R [] = 1 :=
  BGP212.Var.simplexMoment_nil R

theorem simplexMoment_single (R : ℚ) (e : ℕ) : simplexMoment R [e] = R ^ (e + 1) / (e + 1) :=
  BGP212.Var.simplexMoment_single R e

theorem simplexMoment_snoc (R : ℚ) (e : List ℕ) (u : ℕ) :
    simplexMoment R (e ++ [u]) =
      ((e.map Nat.factorial).prod : ℚ) / ((e.length + e.sum).factorial : ℚ) *
        betaMoment R u (e.length + e.sum) :=
  BGP212.Var.simplexMoment_snoc R e u

end BGP212.Challenge
