/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Specification of record: specs/B0_multishift_gdt.yaml (Track B, phase B1).
Extends: thinkthoughts/general-divisor-theorem v1.0.0 (commit cef9605).
-/
import BGP212.MultiShift
import BGP212.GDTv1
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! # Multi-shift GDT (B1): proofs

The structure follows GDT v1.0.0's own proof, reusing its verified lemmas
(`d_mul_R_eq_rad`, `coprime_d_R`, `coprime_m_R`, `R_pos`, `R_squarefree`,
`exists_repr_mod_R`, `repr_unique`, `periodic_window_card_eq`, `card_filter_Ico_split`).
The new ingredients are:

* `gcd_eq_one_iff`: `gcd(x, N) = 1` exactly when no prime of `N` divides `x`;
* `acceptedH_iff`: under multi-shift admissibility, only the primes of `R` constrain `n`;
* `card_filter_crt`: the Chinese remainder theorem as a product of counts;
* `count_avoid`: over `[0, ∏ P)`, avoiding the classes of `H` at each prime of `P`
  leaves exactly `∏_{p ∈ P} (p − ν_p(H))` residues. -/

namespace BGP212.MultiShift

open GDT BGP212.GDTv1

/-! ## Primes of `N`, `d` and `R` -/

lemma coprime_iff_forall_primeFactors {k n : ℕ} (hn : n ≠ 0) :
    Nat.Coprime k n ↔ ∀ p ∈ n.primeFactors, ¬ p ∣ k := by
  constructor
  · intro hcop p hp hpk
    have hpn := Nat.dvd_of_mem_primeFactors hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have h1 : p ∣ Nat.gcd k n := Nat.dvd_gcd hpk hpn
    rw [hcop] at h1
    exact hpr.one_lt.ne' (Nat.eq_one_of_dvd_one h1)
  · intro h
    apply Nat.coprime_of_dvd
    intro p hpr hpk hpn
    exact h p (Nat.mem_primeFactors.mpr ⟨hpr, hpn, hn⟩) hpk

lemma gcd_eq_one_iff {N : ℕ} (hN : 0 < N) (x : ℤ) :
    Int.gcd x (N : ℤ) = 1 ↔ ∀ p ∈ N.primeFactors, ¬ (p : ℤ) ∣ x := by
  have : Int.gcd x (N : ℤ) = Nat.gcd x.natAbs N := by
    simp [Int.gcd]
  rw [this]
  change Nat.Coprime x.natAbs N ↔ _
  rw [coprime_iff_forall_primeFactors hN.ne']
  simp only [Int.natCast_dvd]

lemma primeFactors_rad (n : ℕ) : (rad n).primeFactors = n.primeFactors := by
  unfold rad
  exact Nat.primeFactors_prod_primeFactors n

lemma rad_ne_zero (n : ℕ) : rad n ≠ 0 := (rad_pos n).ne'

lemma primeFactors_N {N m : ℕ} (hN : 0 < N) :
    N.primeFactors = (d N m).primeFactors ∪ (R N m).primeFactors := by
  rw [← primeFactors_rad N, ← d_mul_R_eq_rad hN]
  exact Nat.primeFactors_mul (by unfold d; exact rad_ne_zero _) (R_pos hN).ne'

lemma dvd_m_of_mem_d {N m p : ℕ} (hp : p ∈ (d N m).primeFactors) : p ∣ m := by
  unfold d at hp
  rw [primeFactors_rad] at hp
  exact (Nat.dvd_of_mem_primeFactors hp).trans (Nat.gcd_dvd_left m N)

lemma dvd_N_of_mem_d {N m p : ℕ} (hp : p ∈ (d N m).primeFactors) : p ∣ N := by
  unfold d at hp
  rw [primeFactors_rad] at hp
  exact (Nat.dvd_of_mem_primeFactors hp).trans (Nat.gcd_dvd_right m N)

/-! ## Reduction to the primes of `R` -/

/-- For `n ≡ a (mod m)`, a prime `p ∣ m` divides `n + h` exactly when it divides `a + h`. -/
lemma dvd_shift_iff_of_modEq {m p : ℕ} (hpm : p ∣ m) {n : ℕ} {a h : ℤ}
    (hmod : (n : ℤ) ≡ a [ZMOD (m : ℤ)]) :
    (p : ℤ) ∣ (n : ℤ) + h ↔ (p : ℤ) ∣ a + h := by
  have hdiff : (p : ℤ) ∣ (n : ℤ) - a :=
    (Int.natCast_dvd_natCast.mpr hpm).trans (Int.ModEq.dvd hmod.symm)
  have heq : (n : ℤ) + h = (a + h) + ((n : ℤ) - a) := by ring
  rw [heq]
  exact dvd_add_left hdiff

/-- The `R`-condition: no prime of `R` divides any `n + h`. -/
def condR (N m : ℕ) (H : Finset ℤ) (n : ℕ) : Prop :=
  ∀ p ∈ (R N m).primeFactors, ∀ h ∈ H, ¬ ((p : ℤ) ∣ (n : ℤ) + h)

instance condRDecidable (N m : ℕ) (H : Finset ℤ) : DecidablePred (condR N m H) := by
  intro n; unfold condR; infer_instance

lemma acceptedH_iff {N m : ℕ} (hN : 0 < N) {a : ℤ} {H : Finset ℤ}
    (h : AdmissibleH N m a H) (n : ℕ) :
    acceptedH N m a H n ↔ (n : ℤ) ≡ a [ZMOD (m : ℤ)] ∧ condR N m H n := by
  unfold acceptedH condR
  constructor
  · rintro ⟨hmod, hg⟩
    refine ⟨hmod, fun p hp k hk => ?_⟩
    have := (gcd_eq_one_iff hN _).mp (hg k hk) p
    exact this (by rw [primeFactors_N (m := m) hN]; exact Finset.mem_union_right _ hp)
  · rintro ⟨hmod, hc⟩
    refine ⟨hmod, fun k hk => (gcd_eq_one_iff hN _).mpr fun p hp => ?_⟩
    rw [primeFactors_N (m := m) hN, Finset.mem_union] at hp
    rcases hp with hpd | hpR
    · rw [dvd_shift_iff_of_modEq (dvd_m_of_mem_d hpd) hmod]
      exact h p hpd k hk
    · exact hc p hpR k hk

/-! ## Moving a condition through `n mod k` -/

lemma dvd_add_iff_mod {k p : ℕ} (hpk : p ∣ k) (n : ℕ) (h : ℤ) :
    (p : ℤ) ∣ (n : ℤ) + h ↔ (p : ℤ) ∣ ((n % k : ℕ) : ℤ) + h := by
  have hsplit : (n : ℤ) + h = (((n % k : ℕ) : ℤ) + h) + (k : ℤ) * ((n / k : ℕ) : ℤ) := by
    have := Nat.mod_add_div n k
    have : ((n % k + k * (n / k) : ℕ) : ℤ) = (n : ℤ) := by rw [this]
    push_cast at this ⊢
    linarith
  rw [hsplit]
  exact dvd_add_left (Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr hpk) _)

lemma condR_mod {N m : ℕ} (H : Finset ℤ) (n : ℕ) :
    condR N m H n ↔ condR N m H (n % R N m) := by
  unfold condR
  constructor
  · intro hc p hp k hk hdvd
    exact hc p hp k hk ((dvd_add_iff_mod (Nat.dvd_of_mem_primeFactors hp) n k).mpr hdvd)
  · intro hc p hp k hk hdvd
    exact hc p hp k hk ((dvd_add_iff_mod (Nat.dvd_of_mem_primeFactors hp) n k).mp hdvd)

/-! ## The Chinese remainder theorem as a product of counts -/

lemma card_filter_crt {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (hcop : Nat.Coprime u v)
    (A B : ℕ → Prop) [DecidablePred A] [DecidablePred B] :
    ((Finset.range (u * v)).filter (fun t => A (t % u) ∧ B (t % v))).card =
      ((Finset.range u).filter A).card * ((Finset.range v).filter B).card := by
  rw [← Finset.card_product]
  apply Finset.card_bij (fun t _ => (t % u, t % v))
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_range] at ht
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range]
    exact ⟨⟨Nat.mod_lt t hu, ht.2.1⟩, ⟨Nat.mod_lt t hv, ht.2.2⟩⟩
  · intro t1 ht1 t2 ht2 heq
    simp only [Finset.mem_filter, Finset.mem_range] at ht1 ht2
    simp only [Prod.mk.injEq] at heq
    have hmod : t1 ≡ t2 [MOD u * v] :=
      (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨heq.1, heq.2⟩
    unfold Nat.ModEq at hmod
    rwa [Nat.mod_eq_of_lt ht1.1, Nat.mod_eq_of_lt ht2.1] at hmod
  · rintro ⟨x, y⟩ hxy
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hxy
    obtain ⟨⟨hx, hAx⟩, ⟨hy, hBy⟩⟩ := hxy
    let k := Nat.chineseRemainder hcop x y
    have hk1 : k.1 % u = x := by rw [k.2.1]; exact Nat.mod_eq_of_lt hx
    have hk2 : k.1 % v = y := by rw [k.2.2]; exact Nat.mod_eq_of_lt hy
    refine ⟨k.1, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.chineseRemainder_lt_mul hcop x y hu.ne' hv.ne', by rw [hk1]; exact hAx,
        by rw [hk2]; exact hBy⟩
    · simp [hk1, hk2]

/-! ## Counting residues that avoid the classes of `H` -/

lemma nu_le {p : ℕ} (hp : 0 < p) (H : Finset ℤ) : nu p H ≤ p := by
  unfold nu
  have hsub : H.image (fun h => (-h) % (p : ℤ)) ⊆
      (Finset.range p).image (fun k : ℕ => (k : ℤ)) := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨h, -, rfl⟩ := hx
    have h0 : 0 ≤ (-h) % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
    have h1 : (-h) % (p : ℤ) < p := Int.emod_lt_of_pos _ (by exact_mod_cast hp)
    simp only [Finset.mem_image, Finset.mem_range]
    exact ⟨((-h) % (p : ℤ)).toNat, by omega, Int.toNat_of_nonneg h0⟩
  calc (H.image fun h => (-h) % (p : ℤ)).card
      ≤ ((Finset.range p).image (fun k : ℕ => (k : ℤ))).card := Finset.card_le_card hsub
    _ ≤ (Finset.range p).card := Finset.card_image_le
    _ = p := Finset.card_range p

/-- For `x < p`: `p ∣ x + h` exactly when `x` is the class `−h mod p`. -/
lemma dvd_iff_eq_class {p x : ℕ} (_hp : 0 < p) (hx : x < p) (h : ℤ) :
    (p : ℤ) ∣ (x : ℤ) + h ↔ (x : ℤ) = (-h) % (p : ℤ) := by
  have hxmod : (x : ℤ) % (p : ℤ) = x :=
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hx)
  have key : (p : ℤ) ∣ (x : ℤ) + h ↔ (x : ℤ) ≡ -h [ZMOD (p : ℤ)] := by
    rw [Int.modEq_iff_dvd, show -h - (x : ℤ) = -((x : ℤ) + h) by ring, dvd_neg]
  rw [key]
  unfold Int.ModEq
  rw [hxmod]

lemma count_one_prime {p : ℕ} (hp : 0 < p) (H : Finset ℤ) :
    ((Finset.range p).filter (fun x : ℕ => ∀ h ∈ H, ¬ ((p : ℤ) ∣ (x : ℤ) + h))).card =
      p - nu p H := by
  set F := H.image (fun h => (-h) % (p : ℤ)) with hF
  have hcond : ∀ x ∈ Finset.range p,
      ((∀ h ∈ H, ¬ ((p : ℤ) ∣ (x : ℤ) + h)) ↔ ¬ ((x : ℤ) ∈ F)) := by
    intro x hx
    rw [Finset.mem_range] at hx
    simp only [hF, Finset.mem_image, not_exists, not_and]
    constructor
    · intro hall k hk heq
      exact hall k hk ((dvd_iff_eq_class hp hx k).mpr heq.symm)
    · intro hall k hk hd
      exact hall k hk ((dvd_iff_eq_class hp hx k).mp hd).symm
  rw [Finset.filter_congr hcond]
  have hin : ((Finset.range p).filter (fun x : ℕ => (x : ℤ) ∈ F)).card = F.card := by
    apply Finset.card_bij (fun (x : ℕ) _ => (x : ℤ))
    · intro x hx; exact (Finset.mem_filter.mp hx).2
    · intro x1 _ x2 _ h; exact_mod_cast h
    · intro y hy
      have hy' : y ∈ H.image (fun h => (-h) % (p : ℤ)) := hy
      obtain ⟨h, -, rfl⟩ := Finset.mem_image.mp hy'
      have h0 : 0 ≤ (-h) % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
      have h1 : (-h) % (p : ℤ) < p := Int.emod_lt_of_pos _ (by exact_mod_cast hp)
      refine ⟨((-h) % (p : ℤ)).toNat, ?_, Int.toNat_of_nonneg h0⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨(Int.toNat_lt h0).mpr h1, ?_⟩
      rw [Int.toNat_of_nonneg h0]; exact hy
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.range p) (fun x : ℕ => (x : ℤ) ∈ F)
  rw [Finset.card_range, hin] at hsplit
  unfold nu
  rw [← hF]
  omega

/-- Over `[0, ∏ P)`, the residues avoiding the classes of `H` at every prime of `P` number
`∏_{p ∈ P} (p − ν_p(H))`. -/
lemma count_avoid (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (H : Finset ℤ) :
    ((Finset.range (∏ p ∈ P, p)).filter
        (fun t : ℕ => ∀ p ∈ P, ∀ h ∈ H, ¬ ((p : ℤ) ∣ (t : ℤ) + h))).card =
      ∏ p ∈ P, (p - nu p H) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert q P hq ih =>
      have hqp : q.Prime := hP q (Finset.mem_insert_self q P)
      have hP' : ∀ p ∈ P, p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
      have hM : 0 < ∏ p ∈ P, p := Finset.prod_pos fun p hp => (hP' p hp).pos
      have hcop : Nat.Coprime q (∏ p ∈ P, p) := by
        apply Nat.Coprime.prod_right
        intro p hp
        exact (Nat.coprime_primes hqp (hP' p hp)).mpr (fun h => hq (h ▸ hp))
      rw [Finset.prod_insert hq, Finset.prod_insert hq]
      have hcond : ∀ t ∈ Finset.range (q * ∏ p ∈ P, p),
          ((∀ p ∈ insert q P, ∀ h ∈ H, ¬ ((p : ℤ) ∣ (t : ℤ) + h)) ↔
            ((fun x : ℕ => ∀ h ∈ H, ¬ ((q : ℤ) ∣ (x : ℤ) + h)) (t % q) ∧
             (fun y : ℕ => ∀ p ∈ P, ∀ h ∈ H, ¬ ((p : ℤ) ∣ (y : ℤ) + h))
               (t % ∏ p ∈ P, p))) := by
        intro t _
        simp only [Finset.mem_insert, forall_eq_or_imp]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨fun k hk hd => h1 k hk ((dvd_add_iff_mod (dvd_refl q) t k).mpr hd),
            fun p hp k hk hd => h2 p hp k hk ?_⟩
          exact (dvd_add_iff_mod (Finset.dvd_prod_of_mem _ hp) t k).mpr hd
        · rintro ⟨h1, h2⟩
          refine ⟨fun k hk hd => h1 k hk ((dvd_add_iff_mod (dvd_refl q) t k).mp hd),
            fun p hp k hk hd => h2 p hp k hk ?_⟩
          exact (dvd_add_iff_mod (Finset.dvd_prod_of_mem _ hp) t k).mp hd
      rw [Finset.filter_congr hcond,
        card_filter_crt hqp.pos hM hcop (fun x : ℕ => ∀ h ∈ H, ¬ ((q : ℤ) ∣ (x : ℤ) + h))
          (fun y : ℕ => ∀ p ∈ P, ∀ h ∈ H, ¬ ((p : ℤ) ∣ (y : ℤ) + h)),
        count_one_prime hqp.pos H, ih hP']

/-! ## The canonical window -/

lemma canonical_window_count {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ} {H : Finset ℤ}
    (h : AdmissibleH N m a H) :
    ((Finset.Ico 0 (Tmin N m)).filter (acceptedH N m a H)).card = localCount N m H := by
  rw [Finset.filter_congr (fun n _ => acceptedH_iff hN h n)]
  have hbij : ((Finset.Ico 0 (Tmin N m)).filter
      (fun n : ℕ => (n : ℤ) ≡ a [ZMOD (m : ℤ)] ∧ condR N m H n)).card =
      ((Finset.range (R N m)).filter (condR N m H)).card := by
    apply Finset.card_bij (fun n _ => n % R N m)
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.mod_lt n (R_pos hN), (condR_mod H n).mp hn.2.2⟩
    · intro n1 hn1 n2 hn2 heq
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn1 hn2
      exact repr_unique hN hm hn1.1.2 hn2.1.2 hn1.2.1 hn2.2.1 heq
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_range] at hr
      obtain ⟨n, hnlt, hnmod, hnR⟩ := exists_repr_mod_R (a := a) hN hm hr.1
      refine ⟨n, ?_, hnR⟩
      simp only [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨Nat.zero_le n, hnlt⟩, hnmod, by rw [condR_mod, hnR]; exact hr.2⟩
  rw [hbij]
  have hR : ∏ p ∈ (R N m).primeFactors, p = R N m :=
    Nat.prod_primeFactors_of_squarefree (R_squarefree hN)
  have := count_avoid (R N m).primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp) H
  rw [hR] at this
  unfold localCount
  rw [← this]
  rfl

end BGP212.MultiShift

namespace BGP212.Challenge

open GDT BGP212.GDTv1 BGP212.MultiShift

theorem gdtH_empty {N m L : ℕ} (hN : 0 < N) (_hm : 0 < m) {a : ℤ} {H : Finset ℤ}
    (h : ¬ AdmissibleH N m a H) :
    SH N L m a H = ∅ := by
  simp only [AdmissibleH, not_forall, Classical.not_not] at h
  obtain ⟨p, hp, k, hk, hpk⟩ := h
  unfold SH
  apply Finset.filter_false_of_mem
  intro n _ hacc
  obtain ⟨hmod, hg⟩ := hacc
  have := (gcd_eq_one_iff hN _).mp (hg k hk) p
    (by rw [primeFactors_N (m := m) hN]; exact Finset.mem_union_left _ hp)
  exact this ((dvd_shift_iff_of_modEq (dvd_m_of_mem_d hp) hmod).mpr hpk)

theorem gdtH_periodic {N m : ℕ} (hN : 0 < N) (_hm : 0 < m) {a : ℤ} {H : Finset ℤ}
    (h : AdmissibleH N m a H) :
    IsPeriodH N m a H (Tmin N m) := by
  intro n
  rw [acceptedH_iff hN h, acceptedH_iff hN h]
  have hmodT : ((n + Tmin N m : ℕ) : ℤ) ≡ (n : ℤ) [ZMOD (m : ℤ)] := by
    unfold Int.ModEq Tmin
    push_cast
    exact Int.add_mul_emod_self_left _ _ _
  have hcond : condR N m H (n + Tmin N m) ↔ condR N m H n := by
    rw [condR_mod H (n + Tmin N m), condR_mod H n]
    unfold Tmin
    rw [Nat.add_mul_mod_self_right]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨hmodT.symm.trans h1, hcond.mp h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨hmodT.trans h1, hcond.mpr h2⟩

theorem gdtH_count_per_period {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ} {H : Finset ℤ}
    (h : AdmissibleH N m a H) (b : ℕ) :
    ((Finset.Ico b (b + Tmin N m)).filter (acceptedH N m a H)).card = localCount N m H := by
  rw [periodic_window_card_eq (gdtH_periodic hN hm h) b]
  exact canonical_window_count hN hm h

lemma SH_eq_filter_Ico (N L m : ℕ) (a : ℤ) (H : Finset ℤ) :
    SH N L m a H = (Finset.Ico 1 (L + 1)).filter (acceptedH N m a H) := by
  unfold SH
  congr 1

theorem gdtH_density {N m q s : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ} {H : Finset ℤ}
    (h : AdmissibleH N m a H) (_hs : s < Tmin N m) :
    (SH N (q * Tmin N m + s) m a H).card = q * localCount N m H + (SH N s m a H).card := by
  induction q with
  | zero => simp
  | succ k ih =>
      have hsplit : (k + 1) * Tmin N m + s = (k * Tmin N m + s) + Tmin N m := by ring
      rw [hsplit, SH_eq_filter_Ico]
      rw [card_filter_Ico_split (a := 1) (b := k * Tmin N m + s + 1)
        (c := k * Tmin N m + s + Tmin N m + 1) (by omega) (by omega)]
      have hfirst : ((Finset.Ico 1 (k * Tmin N m + s + 1)).filter
          (acceptedH N m a H)).card = k * localCount N m H + (SH N s m a H).card := by
        rw [← SH_eq_filter_Ico]; exact ih
      have hsecond : ((Finset.Ico (k * Tmin N m + s + 1)
          (k * Tmin N m + s + Tmin N m + 1)).filter (acceptedH N m a H)).card =
          localCount N m H := by
        rw [show k * Tmin N m + s + Tmin N m + 1 = (k * Tmin N m + s + 1) + Tmin N m by ring]
        exact gdtH_count_per_period hN hm h _
      rw [hfirst, hsecond]
      ring

theorem gdtH_density_formula {N m : ℕ} (hN : 0 < N) (hm : 0 < m) (H : Finset ℤ) :
    (localCount N m H : ℚ) / (Tmin N m : ℚ) =
      (1 / (m : ℚ)) * ∏ p ∈ (R N m).primeFactors, (1 - (nu p H : ℚ) / (p : ℚ)) := by
  have hR : ∏ p ∈ (R N m).primeFactors, p = R N m :=
    Nat.prod_primeFactors_of_squarefree (R_squarefree hN)
  have hpos : ∀ p ∈ (R N m).primeFactors, (0 : ℚ) < p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have hterm : ∀ p ∈ (R N m).primeFactors,
      (1 - (nu p H : ℚ) / (p : ℚ)) = (((p - nu p H : ℕ) : ℚ)) / (p : ℚ) := by
    intro p hp
    have hle := nu_le (Nat.prime_of_mem_primeFactors hp).pos H
    rw [Nat.cast_sub hle]
    field_simp [(hpos p hp).ne']
  have hRq : (∏ p ∈ (R N m).primeFactors, (p : ℚ)) = ((R N m : ℕ) : ℚ) := by
    rw [← Nat.cast_prod, hR]
  rw [Finset.prod_congr rfl hterm, Finset.prod_div_distrib, hRq]
  unfold localCount Tmin
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hR' : ((R N m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (R_pos (m := m) hN).ne'
  rw [Nat.cast_prod, Nat.cast_mul]
  field_simp

theorem gdtH_single_shift {N m : ℕ} (hN : 0 < N) (a : ℤ) :
    (AdmissibleH N m a {0} ↔ Admissible N m a) ∧
    (∀ n : ℕ, acceptedH N m a {0} n ↔ accepted N m a n) ∧
    localCount N m {0} = Nat.totient (R N m) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold AdmissibleH Admissible
    rw [show Nat.gcd a.natAbs (d N m) = 1 ↔ Nat.Coprime a.natAbs (d N m) from Iff.rfl,
      coprime_iff_forall_primeFactors (by unfold d; exact rad_ne_zero _)]
    simp only [Finset.mem_singleton, forall_eq, add_zero, Int.natCast_dvd]
  · intro n
    unfold acceptedH accepted
    simp only [Finset.mem_singleton, forall_eq, add_zero]
    rw [Int.gcd_natCast_natCast]
  · unfold localCount
    have hnu : ∀ p ∈ (R N m).primeFactors, p - nu p {0} = p - 1 := by
      intro p _; unfold nu; simp
    rw [Finset.prod_congr rfl hnu]
    have hsq := R_squarefree (m := m) hN
    have h1 := Nat.totient_mul_prod_primeFactors (R N m)
    rw [Nat.prod_primeFactors_of_squarefree hsq] at h1
    have hpos := R_pos (m := m) hN
    exact (Nat.eq_of_mul_eq_mul_right hpos (by rw [h1]; ring)).symm

theorem gdt_count_per_period_via_multishift {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : Admissible N m a) (b : ℕ) :
    ((Finset.Ico b (b + Tmin N m)).filter (accepted N m a)).card =
      Nat.totient (R N m) := by
  obtain ⟨hadm, hacc, hcount⟩ := gdtH_single_shift (m := m) hN a
  rw [← hcount, ← gdtH_count_per_period hN hm (hadm.mpr h) b]
  congr 1
  exact Finset.filter_congr fun n _ => (hacc n).symm

/-- **Gate B.** The re-derived statement is GDT v1.0.0's `gdt_count_per_period`
statement exactly: the two theorem types agree definitionally, checked at build time. -/
example :
    (type_of% @gdt_count_per_period_via_multishift) =
      (type_of% @BGP212.GDTv1.gdt_count_per_period) := rfl

end BGP212.Challenge
