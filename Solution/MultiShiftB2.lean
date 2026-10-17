/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Specification of record: specs/B0_multishift_gdt.yaml (Track B, phase B2).
Extends: thinkthoughts/general-divisor-theorem v1.0.0 (commit cef9605), vendored in
BGP212/GDTv1Basic.lean. W-trick source: Axiom Math, Definition 4.5 and §12.
-/
import BGP212.WTrick
import Solution.MultiShift
import Solution.Lemma12_1
import Mathlib.Tactic.LinearCombination

/-! # Multi-shift GDT (B2): proofs

Built on B1 (`Solution/MultiShift.lean`) and on Lemma 12.1 (`Solution/Lemma12_1.lean`).

* Relative density is B1's absolute density times `m`.
* Local positivity reads the per-period count `∏ (p − ν_p(H))` of B1.
* Minimal period: from one accepted `n₀`, a period `t` keeps every `n₀ + k t` accepted.
  If a prime `p ∣ R` failed to divide `t`, the values `n₀ + k t` would reach every class
  mod `p`, including a class `H` forbids (`exists_hit`). -/

namespace BGP212.MultiShift

open GDT BGP212.GDTv1

/-! ## Small facts about `rad`, `d`, `R` -/

lemma rad_one' : rad 1 = 1 := by unfold rad; simp

lemma rad_prime {p : ℕ} (hp : p.Prime) : rad p = p := by
  unfold rad; rw [hp.primeFactors]; simp

lemma d_one (N : ℕ) : d N 1 = 1 := by
  unfold d; rw [Nat.gcd_one_left, rad_one']

lemma rad_of_squarefree {W : ℕ} (hsf : Squarefree W) : rad W = W := by
  unfold rad
  exact Nat.prod_primeFactors_of_squarefree hsf

lemma R_one_of_squarefree {W : ℕ} (hsf : Squarefree W) : R W 1 = W := by
  unfold R; rw [d_one, Nat.div_one, rad_of_squarefree hsf]

lemma admissibleH_one (N : ℕ) (a : ℤ) (H : Finset ℤ) : AdmissibleH N 1 a H := by
  intro p hp
  rw [d_one] at hp
  simp at hp

/-! ## Acceptance fails without admissibility -/

lemma not_acceptedH_of_not_admissible {N m : ℕ} (hN : 0 < N) {a : ℤ} {H : Finset ℤ}
    (h : ¬ AdmissibleH N m a H) (n : ℕ) : ¬ acceptedH N m a H n := by
  simp only [AdmissibleH, not_forall, Classical.not_not] at h
  obtain ⟨p, hp, k, hk, hpk⟩ := h
  rintro ⟨hmod, hg⟩
  have := (gcd_eq_one_iff hN _).mp (hg k hk) p
    (by rw [primeFactors_N (m := m) hN]; exact Finset.mem_union_left _ hp)
  exact this ((dvd_shift_iff_of_modEq (dvd_m_of_mem_d hp) hmod).mpr hpk)

/-! ## A period, iterated -/

lemma period_iter {N m : ℕ} {a : ℤ} {H : Finset ℤ} {t : ℕ} (hper : IsPeriodH N m a H t)
    {n : ℕ} (hn : acceptedH N m a H n) : ∀ k : ℕ, acceptedH N m a H (n + k * t)
  | 0 => by simpa using hn
  | k + 1 => by
      have ih := period_iter hper hn k
      rw [show n + (k + 1) * t = (n + k * t) + t by ring]
      exact (hper _).mpr ih

/-- If a prime `p` does not divide `t`, then `c + k t` reaches `0 mod p` for some `k`. -/
lemma exists_hit {p t : ℕ} (hp : p.Prime) (hpt : ¬ p ∣ t) (c : ℤ) :
    ∃ k : ℕ, (p : ℤ) ∣ c + (k : ℤ) * (t : ℤ) := by
  have hcop : Nat.Coprime t p := Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).mpr hpt)
  have hg : Int.gcd (t : ℤ) (p : ℤ) = 1 := by rw [Int.gcd_natCast_natCast]; exact hcop
  have hb := Int.gcd_eq_gcd_ab (t : ℤ) (p : ℤ)
  rw [hg] at hb
  push_cast at hb
  set u := Int.gcdA (t : ℤ) (p : ℤ)
  set v := Int.gcdB (t : ℤ) (p : ℤ)
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have h0 : 0 ≤ (-c * u) % (p : ℤ) := Int.emod_nonneg _ hp0.ne'
  refine ⟨((-c * u) % (p : ℤ)).toNat, ?_⟩
  rw [Int.toNat_of_nonneg h0, Int.emod_def]
  refine ⟨c * v - ((-c * u) / p) * t, ?_⟩
  linear_combination c * hb

end BGP212.MultiShift

namespace BGP212.Challenge

open GDT BGP212.GDTv1 BGP212.MultiShift BGP212.WTrick

/-! ## Relative density -/

theorem gdtH_relative_density {N m : ℕ} (hN : 0 < N) (hm : 0 < m) (H : Finset ℤ) :
    (m : ℚ) * ((localCount N m H : ℚ) / (Tmin N m : ℚ)) =
      ∏ p ∈ (R N m).primeFactors, (1 - (nu p H : ℚ) / (p : ℚ)) ∧
    (localCount N m H : ℚ) / (R N m : ℚ) =
      ∏ p ∈ (R N m).primeFactors, (1 - (nu p H : ℚ) / (p : ℚ)) := by
  have habs := gdtH_density_formula hN hm H
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  have hR' : (R N m : ℚ) ≠ 0 := by exact_mod_cast (R_pos (m := m) hN).ne'
  have h1 : (m : ℚ) * ((localCount N m H : ℚ) / (Tmin N m : ℚ)) =
      ∏ p ∈ (R N m).primeFactors, (1 - (nu p H : ℚ) / (p : ℚ)) := by
    rw [habs]; field_simp
  refine ⟨h1, ?_⟩
  rw [← h1]
  unfold Tmin
  push_cast
  field_simp

/-! ## Local positivity -/

theorem gdtH_local_positivity {N m : ℕ} (hN : 0 < N) (hm : 0 < m) (a : ℤ) (H : Finset ℤ) :
    (∃ n : ℕ, acceptedH N m a H n) ↔
      AdmissibleH N m a H ∧ ∀ p ∈ (R N m).primeFactors, nu p H < p := by
  constructor
  · rintro ⟨n0, hn0⟩
    have hadm : AdmissibleH N m a H := by
      by_contra hna
      exact not_acceptedH_of_not_admissible hN hna n0 hn0
    refine ⟨hadm, ?_⟩
    have hcount := gdtH_count_per_period hN hm hadm n0
    have hmem : n0 ∈ (Finset.Ico n0 (n0 + Tmin N m)).filter (acceptedH N m a H) := by
      simp only [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨le_refl _, by have := R_pos (m := m) hN; unfold Tmin; nlinarith⟩, hn0⟩
    have hpos : 0 < localCount N m H := by
      rw [← hcount]; exact Finset.card_pos.mpr ⟨n0, hmem⟩
    intro p hp
    have hne : localCount N m H ≠ 0 := hpos.ne'
    unfold localCount at hne
    have := (Finset.prod_ne_zero_iff.mp hne) p hp
    omega
  · rintro ⟨hadm, hpos⟩
    have hcount := gdtH_count_per_period hN hm hadm 0
    have hlc : 0 < localCount N m H := by
      unfold localCount
      exact Finset.prod_pos fun p hp => by have := hpos p hp; omega
    rw [← hcount] at hlc
    obtain ⟨n, hn⟩ := Finset.card_pos.mp hlc
    exact ⟨n, (Finset.mem_filter.mp hn).2⟩

/-! ## Minimal period -/

theorem gdtH_minimal_period {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ} {H : Finset ℤ}
    (hH : H.Nonempty) (hadm : AdmissibleH N m a H) (hpos : ∀ p ∈ (R N m).primeFactors, nu p H < p)
    {t : ℕ} (_ht : 0 < t) (hper : IsPeriodH N m a H t) :
    Tmin N m ∣ t := by
  obtain ⟨n0, hn0⟩ := (gdtH_local_positivity hN hm a H).mpr ⟨hadm, hpos⟩
  have hiter := period_iter hper hn0
  -- `m ∣ t`: both `n₀` and `n₀ + t` lie in the class `a mod m`
  have hmt : m ∣ t := by
    have h1 := (hiter 1).1
    have h0 := hn0.1
    rw [one_mul] at h1
    have hd := Int.ModEq.dvd (h0.trans h1.symm)
    push_cast at hd
    rw [show (n0 : ℤ) + t - n0 = t by ring] at hd
    exact_mod_cast hd
  -- `p ∣ t` for every prime `p ∣ R`
  have hpt : ∀ p ∈ (R N m).primeFactors, p ∣ t := by
    intro p hp
    by_contra hnd
    obtain ⟨h0, hh0⟩ := hH
    have hpr := Nat.prime_of_mem_primeFactors hp
    obtain ⟨k, hk⟩ := exists_hit hpr hnd ((n0 : ℤ) + h0)
    have hacc := hiter k
    have hcond := ((acceptedH_iff hN hadm _).mp hacc).2 p hp h0 hh0
    apply hcond
    push_cast
    rw [show (n0 : ℤ) + (k : ℤ) * (t : ℤ) + h0 = (n0 : ℤ) + h0 + (k : ℤ) * (t : ℤ) by ring]
    exact hk
  -- `R ∣ t`, since `R` is the product of its primes
  have hRt : R N m ∣ t := by
    have := Finset.prod_primes_dvd t (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) hpt
    rwa [Nat.prod_primeFactors_of_squarefree (R_squarefree hN)] at this
  unfold Tmin
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_m_R hN) hmt hRt

/-! ## Both extra hypotheses are necessary -/

theorem gdtH_minimal_period_needs_shift :
    IsPeriodH 5 2 0 ∅ 2 ∧ Tmin 5 2 = 10 ∧ ¬ (10 ∣ 2) := by
  refine ⟨?_, ?_, by decide⟩
  · intro n
    unfold acceptedH Int.ModEq
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, and_true]
    push_cast
    omega
  · unfold Tmin R d
    rw [show Nat.gcd 2 5 = 1 by decide, rad_one', rad_prime (by decide)]

theorem gdtH_minimal_period_needs_nonempty :
    (¬ ∃ n : ℕ, acceptedH 2 1 0 {0, 1} n) ∧
    IsPeriodH 2 1 0 {0, 1} 1 ∧ Tmin 2 1 = 2 ∧ ¬ (2 ∣ 1) := by
  have hnone : ¬ ∃ n : ℕ, acceptedH 2 1 0 {0, 1} n := by
    rintro ⟨n, -, hg⟩
    have g0 : Int.gcd ((n : ℤ) + 0) 2 = 1 := by simpa using hg 0 (by simp)
    have g1 : Int.gcd ((n : ℤ) + 1) 2 = 1 := by simpa using hg 1 (by simp)
    rcases Int.emod_two_eq_zero_or_one (n : ℤ) with h | h
    · have h2 : (2 : ℤ) ∣ (n : ℤ) + 0 := by omega
      have := Int.dvd_gcd h2 (dvd_refl (2 : ℤ))
      rw [g0] at this
      exact absurd this (by decide)
    · have h2 : (2 : ℤ) ∣ (n : ℤ) + 1 := by omega
      have := Int.dvd_gcd h2 (dvd_refl (2 : ℤ))
      rw [g1] at this
      exact absurd this (by decide)
  refine ⟨hnone, ?_, ?_, by decide⟩
  · intro n
    constructor
    · intro h; exact absurd ⟨_, h⟩ hnone
    · intro h; exact absurd ⟨_, h⟩ hnone
  · unfold Tmin R d
    rw [show Nat.gcd 1 2 = 1 by decide, rad_one', rad_prime (by decide)]

/-! ## The W-trick -/

theorem wtrick_count {W : ℕ} (hW : 0 < W) (hsf : Squarefree W) (H : Finset ℤ) :
    ((Finset.range W).filter
        (fun b : ℕ => ∀ h ∈ H, Int.gcd ((b : ℤ) + h) (W : ℤ) = 1)).card =
      ∏ p ∈ W.primeFactors, (p - nu p H) := by
  have hcount := gdtH_count_per_period hW Nat.one_pos (admissibleH_one W 0 H) 0
  have hT : Tmin W 1 = W := by unfold Tmin; rw [one_mul, R_one_of_squarefree hsf]
  rw [zero_add, hT] at hcount
  unfold localCount at hcount
  rw [R_one_of_squarefree hsf] at hcount
  rw [← hcount, Finset.range_eq_Ico]
  congr 1
  apply Finset.filter_congr
  intro b _
  unfold acceptedH
  simp [Int.modEq_one]

theorem admissible_iff_local_factors (H : List ℕ) :
    BGP212.Admissible H ↔
      ∀ p : ℕ, p.Prime → nu p ((H.map (fun h : ℕ => (h : ℤ))).toFinset) < p := by
  set HZ := (H.map (fun h : ℕ => (h : ℤ))).toFinset with hHZ
  have hmemZ : ∀ x : ℤ, x ∈ HZ ↔ ∃ h ∈ H, (h : ℤ) = x := by
    intro x; simp [hHZ, List.mem_map]
  -- the forbidden classes, as naturals below `p`
  have key : ∀ p : ℕ, p.Prime →
      ((∃ r, r < p ∧ ∀ h ∈ H, h % p ≠ r) ↔ nu p HZ < p) := by
    intro p hp
    have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
    set F := HZ.image (fun h => (-h) % (p : ℤ)) with hF
    have hFsub : F ⊆ (Finset.range p).image (fun k : ℕ => (k : ℤ)) := by
      intro x hx
      obtain ⟨h, -, rfl⟩ := Finset.mem_image.mp hx
      have h0 : 0 ≤ (-h) % (p : ℤ) := Int.emod_nonneg _ hp0.ne'
      have h1 : (-h) % (p : ℤ) < p := Int.emod_lt_of_pos _ hp0
      simp only [Finset.mem_image, Finset.mem_range]
      exact ⟨((-h) % (p : ℤ)).toNat, (Int.toNat_lt h0).mpr h1, Int.toNat_of_nonneg h0⟩
    have hcardImg : ((Finset.range p).image (fun k : ℕ => (k : ℤ))).card = p := by
      rw [Finset.card_image_of_injective _ (fun a b h => by exact_mod_cast h)]
      exact Finset.card_range p
    -- `h % p = r` (naturals, `r < p`) iff `(−h) % p = (−r) % p` (integers)
    have hclass : ∀ h r : ℕ, r < p →
        (h % p = r ↔ (-(h : ℤ)) % (p : ℤ) = (-(r : ℤ)) % (p : ℤ)) := by
      intro h r hr
      constructor
      · intro hh
        have : (h : ℤ) ≡ (r : ℤ) [ZMOD (p : ℤ)] := by
          unfold Int.ModEq
          rw [← Int.natCast_mod, hh, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hr)]
        exact this.neg
      · intro hh
        have : (h : ℤ) ≡ (r : ℤ) [ZMOD (p : ℤ)] := by
          have h2 : (-(h : ℤ)) ≡ (-(r : ℤ)) [ZMOD (p : ℤ)] := hh
          simpa using h2.neg
        unfold Int.ModEq at this
        rw [← Int.natCast_mod, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hr)] at this
        exact_mod_cast this
    unfold nu
    rw [← hF]
    constructor
    · rintro ⟨r, hr, hrH⟩
      have hc : (-(r : ℤ)) % (p : ℤ) ∉ F := by
        intro hcF
        obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hcF
        obtain ⟨h, hh, rfl⟩ := (hmemZ x).mp hx
        exact hrH h hh ((hclass h r hr).mpr hxe)
      have hcIn : (-(r : ℤ)) % (p : ℤ) ∈ (Finset.range p).image (fun k : ℕ => (k : ℤ)) := by
        have h0 : 0 ≤ (-(r : ℤ)) % (p : ℤ) := Int.emod_nonneg _ hp0.ne'
        have h1 : (-(r : ℤ)) % (p : ℤ) < p := Int.emod_lt_of_pos _ hp0
        simp only [Finset.mem_image, Finset.mem_range]
        exact ⟨_, (Int.toNat_lt h0).mpr h1, Int.toNat_of_nonneg h0⟩
      have hssub : F ⊂ (Finset.range p).image (fun k : ℕ => (k : ℤ)) :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hFsub, fun he => hc (he ▸ hcIn)⟩
      have := Finset.card_lt_card hssub
      rwa [hcardImg] at this
    · intro hlt
      by_contra hall
      simp only [not_exists, not_and, not_forall, Classical.not_not] at hall
      have hsup : (Finset.range p).image (fun k : ℕ => (k : ℤ)) ⊆ F := by
        intro y hy
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
        rw [Finset.mem_range] at hk
        set r := ((-(k : ℤ)) % (p : ℤ)).toNat with hr
        have h0 : 0 ≤ (-(k : ℤ)) % (p : ℤ) := Int.emod_nonneg _ hp0.ne'
        have hrlt : r < p := (Int.toNat_lt h0).mpr (Int.emod_lt_of_pos _ hp0)
        obtain ⟨h, hh, hhr⟩ := hall r hrlt
        refine Finset.mem_image.mpr ⟨(h : ℤ), (hmemZ _).mpr ⟨h, hh, rfl⟩, ?_⟩
        have e1 := (hclass h r hrlt).mp hhr
        have hrz : (r : ℤ) = (-(k : ℤ)) % (p : ℤ) := by rw [hr, Int.toNat_of_nonneg h0]
        have hmk : (-(r : ℤ)) ≡ (k : ℤ) [ZMOD (p : ℤ)] := by
          rw [hrz]; simpa using (Int.mod_modEq (-(k : ℤ)) (p : ℤ)).neg
        show (-(h : ℤ)) % (p : ℤ) = (k : ℤ)
        rw [e1]
        unfold Int.ModEq at hmk
        rw [hmk, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hk)]
      have := Finset.card_le_card hsup
      rw [hcardImg] at this
      omega
  constructor
  · intro hadm p hp
    exact (key p hp).mp (hadm p (Nat.prime_def.mp hp))
  · intro hall p hp
    have hpr : p.Prime := Nat.prime_def.mpr hp
    exact (key p hpr).mpr (hall p hpr)

/-- `H₄₅`'s integer and natural forms give the same gcd conditions. -/
lemma h45_int_iff_nat (b W : ℕ) :
    (∀ h ∈ H45Z, Int.gcd ((b : ℤ) + h) (W : ℤ) = 1) ↔
      ∀ h ∈ BGP212.H45, Nat.gcd (b + h) W = 1 := by
  unfold H45Z
  simp only [List.mem_toFinset, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  apply forall₂_congr
  intro h _
  rw [show (b : ℤ) + (h : ℤ) = ((b + h : ℕ) : ℤ) by push_cast; rfl, Int.gcd_natCast_natCast]

theorem h45_wtrick_exists :
    ∀ W : ℕ, 0 < W → ∃ b : ℕ, ∀ h ∈ BGP212.H45, Nat.gcd (b + h) W = 1 := by
  intro W hW
  have hlf := (admissible_iff_local_factors BGP212.H45).mp BGP212.Challenge.h45_admissible
  obtain ⟨b, hb⟩ := (gdtH_local_positivity hW Nat.one_pos 0 H45Z).mpr
    ⟨admissibleH_one W 0 H45Z, fun p hp => hlf p (Nat.prime_of_mem_primeFactors hp)⟩
  exact ⟨b, (h45_int_iff_nat b W).mp hb.2⟩

theorem h45_wtrick_W23 :
    localCount W23 1 H45Z = 1 ∧
    ∀ b : ℕ, b < W23 → ((∀ h ∈ BGP212.H45, Nat.gcd (b + h) W23 = 1) ↔ b = 74549147) := by
  have hS : ∀ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ), p.Prime := by decide
  have hW : W23 = ∏ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ), p := by decide
  have hpf : W23.primeFactors = ({2, 3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ) := by
    rw [hW]; exact Nat.primeFactors_prod hS
  have hsf : Squarefree W23 := by rw [hW]; exact prod_primes_squarefree hS
  have hlc : localCount W23 1 H45Z = 1 := by
    unfold localCount
    rw [R_one_of_squarefree hsf, hpf]
    decide
  refine ⟨hlc, ?_⟩
  have hcount := wtrick_count (by decide : 0 < W23) hsf H45Z
  have hlc' : ∏ p ∈ W23.primeFactors, (p - nu p H45Z) = 1 := by
    rw [hpf]; decide
  rw [hlc'] at hcount
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcount
  have hb : (74549147 : ℕ) ∈ (Finset.range W23).filter
      (fun b : ℕ => ∀ h ∈ H45Z, Int.gcd ((b : ℤ) + h) (W23 : ℤ) = 1) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by decide, (h45_int_iff_nat _ _).mpr (by decide)⟩
  rw [hx, Finset.mem_singleton] at hb
  intro b hbW
  constructor
  · intro hgcd
    have hmem : b ∈ (Finset.range W23).filter
        (fun b : ℕ => ∀ h ∈ H45Z, Int.gcd ((b : ℤ) + h) (W23 : ℤ) = 1) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hbW, (h45_int_iff_nat _ _).mpr hgcd⟩
    rw [hx, Finset.mem_singleton] at hmem
    rw [hmem, hb]
  · rintro rfl
    exact (by decide : ∀ h ∈ BGP212.H45, Nat.gcd (74549147 + h) W23 = 1)

end BGP212.Challenge
