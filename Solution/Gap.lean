/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): §2, Definition 4.5, Lemma 4.9, Theorem 4.10, Lemma 12.1, §12.
-/
import BGP212.Gap
import Solution.Lemma12_1
import Solution.MultiShiftB2
import Solution.Theorem711
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Prime.Int

/-! # B3: proofs

* `dhl_implies_gap`: DHL[k, 2] and one admissible `k`-tuple of diameter `D` give `H₁ ≤ D`.
* `wtrick_coprime`: the coprimality step of Lemma 4.9.
* `final_deduction`: DHL[45, 2] and `H₁ ≤ 212` from the named inputs of Theorems 4.10,
  7.11 and 11.1. -/

namespace BGP212.Gap

open BGP212.Params BGP212.T711 Filter

/-! ## Primes and consecutive gaps -/

theorem primes_infinite : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime

/-- Two primes `p < q` give a consecutive gap at index `count p` of size at most `q − p`. -/
theorem gap_le_of_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p ∧
      primeGap (Nat.count Nat.Prime p) ≤ q - p := by
  have h1 : Nat.nth Nat.Prime (Nat.count Nat.Prime p) = p := Nat.nth_count hp
  refine ⟨h1, ?_⟩
  have hc : Nat.count Nat.Prime p + 1 ≤ Nat.count Nat.Prime q := by
    have := Nat.count_monotone Nat.Prime (Nat.succ_le_of_lt hpq)
    rw [Nat.count_succ] at this
    simpa [hp] using this
  have h2 : Nat.nth Nat.Prime (Nat.count Nat.Prime p + 1) ≤ q := by
    have := (Nat.nth_le_nth primes_infinite).mpr hc
    rwa [Nat.nth_count hq] at this
  unfold primeGap
  omega

/-- **`H₁` as a lim inf.** For the natural-valued sequence of gaps, `H1Le D` gives
`liminf (p_{n+1} − p_n) ≤ D`. -/
theorem h1_liminf {D : ℕ} (h : H1Le D) : Filter.liminf primeGap atTop ≤ D :=
  Filter.liminf_le_of_frequently_le h

/-- Primes `p < q` with `q − p ≤ D` and `p` arbitrarily large give `H₁ ≤ D`. -/
theorem h1_of_pairs {D : ℕ}
    (h : ∀ M : ℕ, ∃ p q : ℕ, M ≤ p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q - p ≤ D) : H1Le D := by
  rw [H1Le, Filter.frequently_atTop]
  intro N
  obtain ⟨p, q, hM, hp, hq, hpq, hD⟩ := h (Nat.nth Nat.Prime N)
  obtain ⟨h1, h2⟩ := gap_le_of_primes hp hq hpq
  refine ⟨Nat.count Nat.Prime p, ?_, le_trans h2 hD⟩
  by_contra hlt
  have := (Nat.nth_strictMono primes_infinite) (lt_of_not_ge hlt)
  omega

/-! ## DHL[k, 2] ⇒ H₁ ≤ D -/

/-- At least two primes among the `n + h` give `h < h′` in `H` with both `n + h`, `n + h′`
prime. -/
theorem two_primes {H : Finset ℤ} {n : ℤ}
    (h : 2 ≤ (H.filter fun h => PrimeZ (n + h)).card) :
    ∃ a ∈ H, ∃ b ∈ H, a < b ∧ PrimeZ (n + a) ∧ PrimeZ (n + b) := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Finset.one_lt_card (s := H.filter fun h => PrimeZ (n + h))).mp (by omega)
  simp only [Finset.mem_filter] at ha hb
  rcases lt_or_gt_of_ne hab with h1 | h1
  · exact ⟨a, ha.1, b, hb.1, h1, ha.2, hb.2⟩
  · exact ⟨b, hb.1, a, ha.1, h1, hb.2, ha.2⟩

/-- **DHL[k, 2] ⇒ H₁ ≤ D**, for any admissible `k`-tuple `H` of diameter at most `D`: the
infinitely many translates `n + H` containing two primes are bounded below (a prime is
positive), hence unbounded above, and each gives primes `p < q` with `q − p ≤ D`. -/
theorem dhl_implies_gap (k D : ℕ) (H : Finset ℤ) (hcard : H.card = k) (hadm : AdmissibleZ H)
    (hdiam : ∀ a ∈ H, ∀ b ∈ H, b - a ≤ D) (hdhl : DHL k 2) : H1Le D := by
  have hinf := hdhl H hcard hadm
  apply h1_of_pairs
  intro M
  -- every n in the set exceeds −max |h|
  have hne : H.Nonempty := by
    obtain ⟨n0, hn0⟩ := hinf.nonempty
    have h0 : 2 ≤ (H.filter fun h => PrimeZ (n0 + h)).card := hn0
    have h1 := Finset.card_filter_le H (fun h => PrimeZ (n0 + h))
    exact Finset.card_pos.mp (by omega)
  set c : ℤ := H.sup' hne (fun h => |h|)
  obtain ⟨n, hn, hnM⟩ : ∃ n ∈ {n : ℤ | 2 ≤ (H.filter fun h => PrimeZ (n + h)).card},
      (M : ℤ) + c ≤ n := by
    by_contra hcon
    push Not at hcon
    apply hinf
    apply (Set.finite_Icc (-c) ((M : ℤ) + c)).subset
    intro n hn
    obtain ⟨a, ha, -, -, -, hpa, -⟩ := two_primes hn
    have hac := abs_le.mp (Finset.le_sup' (fun h => |h|) ha : |a| ≤ c)
    have := hpa.1
    exact ⟨by omega, le_of_lt (hcon n hn)⟩
  obtain ⟨a, ha, b, hb, hab, hpa, hpb⟩ := two_primes hn
  have hac := abs_le.mp (Finset.le_sup' (fun h => |h|) ha : |a| ≤ c)
  have ha0 := hpa.1
  have hb0 := hpb.1
  have hd := hdiam a ha b hb
  refine ⟨(n + a).toNat, (n + b).toNat, by omega, hpa.2, hpb.2, by omega, by omega⟩

/-! ## H₄₅ -/

theorem h45Z_card : BGP212.WTrick.H45Z.card = 45 := by decide

/-- Lemma 12.1's admissibility, transported to `ℤ`-shifts. -/
theorem h45Z_admissible : AdmissibleZ BGP212.WTrick.H45Z := by
  intro p hp
  obtain ⟨r, hr, hom⟩ := BGP212.Challenge.h45_admissible p (Nat.prime_def.mp hp)
  refine ⟨r, fun h hh hdvd => ?_⟩
  simp only [BGP212.WTrick.H45Z, List.mem_toFinset, List.mem_map] at hh
  obtain ⟨h0, hh0, rfl⟩ := hh
  have hmod : r ≡ h0 [MOD p] := (Nat.modEq_iff_dvd).mpr (by simpa using hdvd)
  have : h0 % p = r := by
    have := hmod.symm
    unfold Nat.ModEq at this
    rw [this, Nat.mod_eq_of_lt hr]
  exact hom h0 hh0 this

theorem h45Z_diameter : ∀ a ∈ BGP212.WTrick.H45Z, ∀ b ∈ BGP212.WTrick.H45Z, b - a ≤ 212 := by
  decide

/-- **DHL[45, 2] ⇒ H₁ ≤ 212** (Theorem 1.1's last step): apply DHL[45, 2] to `H₄₅`. -/
theorem dhl_45_implies_gap : DHL 45 2 → H1Le 212 :=
  dhl_implies_gap 45 212 BGP212.WTrick.H45Z h45Z_card h45Z_admissible h45Z_diameter

/-! ## Lemma 4.9: the W-trick coprimality step -/

/-- **The W-trick coprimality step, prime-factor form.** Let every prime `p ≤ w` divide `W`,
let `gcd(b + h, W) = 1` for every shift `h ∈ H`, and let every prime dividing a difference of
two distinct shifts be at most `w`. If some `n ≡ b (mod W)` satisfies `n ≡ −h (mod D_h)` for
every `h ∈ H`, then every `D_h` is coprime to `W` and the `D_h` for distinct shifts are
pairwise coprime. -/
theorem wtrick_coprime_of_primes (H : Finset ℤ) (D : ℤ → ℕ) (n b : ℤ) (W w : ℕ)
    (hW : ∀ p : ℕ, p.Prime → p ≤ w → p ∣ W)
    (hb : ∀ h ∈ H, Int.gcd (b + h) W = 1)
    (hn : (W : ℤ) ∣ n - b) (hD : ∀ h ∈ H, (D h : ℤ) ∣ n + h)
    (hdiff : ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → ∀ p : ℕ, p.Prime → (p : ℤ) ∣ h - h' → p ≤ w) :
    (∀ h ∈ H, Nat.Coprime (D h) W) ∧
      ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → Nat.Coprime (D h) (D h') := by
  have hcopW : ∀ h ∈ H, Nat.Coprime (D h) W := by
    intro h hh
    apply Nat.coprime_of_dvd
    intro p hp hpD hpW
    have h1 : (p : ℤ) ∣ n + h := (Int.natCast_dvd_natCast.mpr hpD).trans (hD h hh)
    have h2 : (p : ℤ) ∣ n - b := (Int.natCast_dvd_natCast.mpr hpW).trans hn
    have h3 : (p : ℤ) ∣ b + h := by
      have := dvd_sub h1 h2
      rwa [show n + h - (n - b) = b + h by ring] at this
    have h4 : p ∣ Int.gcd (b + h) W :=
      Int.natCast_dvd_natCast.mp (by
        rw [Int.gcd_eq_gcd_ab (b + h) W]
        exact dvd_add (dvd_mul_of_dvd_left h3 _)
          (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hpW) _))
    rw [hb h hh] at h4
    exact hp.one_lt.ne' (Nat.dvd_one.mp h4)
  refine ⟨hcopW, fun h hh h' hh' hne => ?_⟩
  apply Nat.coprime_of_dvd
  intro p hp hp1 hp2
  have h1 : (p : ℤ) ∣ n + h := (Int.natCast_dvd_natCast.mpr hp1).trans (hD h hh)
  have h2 : (p : ℤ) ∣ n + h' := (Int.natCast_dvd_natCast.mpr hp2).trans (hD h' hh')
  have h3 : (p : ℤ) ∣ h - h' := by
    have := dvd_sub h1 h2
    rwa [show n + h - (n + h') = h - h' by ring] at this
  have hpw : p ≤ w := hdiff h hh h' hh' hne p hp h3
  exact Nat.Coprime.coprime_dvd_left hp1 (hcopW h hh) |>.eq_one_of_dvd (hW p hp hpw) |>
    fun e => hp.one_lt.ne' e

/-- **The W-trick coprimality step (Lemma 4.9).** As printed: the shifts differ by at most
`w` ("once x is large enough that |hᵢ − hᵢ′| < log log log x"). -/
theorem wtrick_coprime (H : Finset ℤ) (D : ℤ → ℕ) (n b : ℤ) (W w : ℕ)
    (hW : ∀ p : ℕ, p.Prime → p ≤ w → p ∣ W)
    (hb : ∀ h ∈ H, Int.gcd (b + h) W = 1)
    (hn : (W : ℤ) ∣ n - b) (hD : ∀ h ∈ H, (D h : ℤ) ∣ n + h)
    (hsmall : ∀ h ∈ H, ∀ h' ∈ H, (h - h').natAbs ≤ w) :
    (∀ h ∈ H, Nat.Coprime (D h) W) ∧
      ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → Nat.Coprime (D h) (D h') :=
  wtrick_coprime_of_primes H D n b W w hW hb hn hD fun h hh h' hh' hne _ _ hp =>
    le_trans (Nat.le_of_dvd (Int.natAbs_pos.mpr (sub_ne_zero.mpr hne)) (Int.natCast_dvd.mp hp))
      (hsmall h hh h' hh')

/-- The W-trick at `W = ∏_{p ≤ w} p` (Definition 4.5, with `w = log log log x`). -/
theorem wtrick_coprime_primorial (H : Finset ℤ) (D : ℤ → ℕ) (n b : ℤ) (w : ℕ)
    (hb : ∀ h ∈ H, Int.gcd (b + h) (primorial w) = 1)
    (hn : (primorial w : ℤ) ∣ n - b) (hD : ∀ h ∈ H, (D h : ℤ) ∣ n + h)
    (hsmall : ∀ h ∈ H, ∀ h' ∈ H, (h - h').natAbs ≤ w) :
    (∀ h ∈ H, Nat.Coprime (D h) (primorial w)) ∧
      ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → Nat.Coprime (D h) (D h') :=
  wtrick_coprime H D n b (primorial w) w (fun _ hp hpw => (hp.dvd_primorial_iff).mpr hpw)
    hb hn hD hsmall

/-- The combined modulus `q = W · ∏_h D_h` of Lemma 4.9 is squarefree when `W` and every
`D_h` are, given the coprimality of `wtrick_coprime`. -/
theorem wtrick_modulus_squarefree (H : Finset ℤ) (D : ℤ → ℕ) (W : ℕ) (hW : Squarefree W)
    (hD : ∀ h ∈ H, Squarefree (D h)) (hcopW : ∀ h ∈ H, Nat.Coprime (D h) W)
    (hcop : ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → Nat.Coprime (D h) (D h')) :
    Squarefree (W * ∏ h ∈ H, D h) := by
  induction H using Finset.induction_on with
  | empty => simpa using hW
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, show W * (D a * ∏ h ∈ s, D h) = D a * (W * ∏ h ∈ s, D h) by ring]
      have ih' := ih (fun h hh => hD h (Finset.mem_insert_of_mem hh))
        (fun h hh => hcopW h (Finset.mem_insert_of_mem hh))
        (fun h hh h' hh' hne' => hcop h (Finset.mem_insert_of_mem hh) h'
          (Finset.mem_insert_of_mem hh') hne')
      refine Nat.squarefree_mul_iff.mpr ⟨?_, hD a (Finset.mem_insert_self a s), ih'⟩
      refine Nat.Coprime.mul_right (hcopW a (Finset.mem_insert_self a s)) ?_
      exact Nat.Coprime.prod_right fun h hh =>
        hcop a (Finset.mem_insert_self a s) h (Finset.mem_insert_of_mem hh)
          (fun e => ha (e ▸ hh))

theorem h45Z_even : ∀ a ∈ BGP212.WTrick.H45Z, (2 : ℤ) ∣ a := by decide

/-- **The primes dividing differences of `H₄₅` are at most 103.** Every element is even and
every difference is at most 212 in size, so a prime dividing a nonzero difference `2e` is `2`
or divides `e`, `|e| ≤ 106`; and 104, 105, 106 are composite. -/
theorem h45_diff_primes : ∀ a ∈ BGP212.WTrick.H45Z, ∀ c ∈ BGP212.WTrick.H45Z, a ≠ c →
    ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a - c → p ≤ 103 := by
  intro a ha c hc hne p hp hdvd
  obtain ⟨e, he⟩ : (2 : ℤ) ∣ a - c := dvd_sub (h45Z_even a ha) (h45Z_even c hc)
  have hd1 := h45Z_diameter a ha c hc
  have hd2 := h45Z_diameter c hc a ha
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rw [he] at hdvd
  rcases hpz.dvd_or_dvd hdvd with h2 | he'
  · have : p ∣ 2 := Int.natCast_dvd_natCast.mp h2
    have := Nat.le_of_dvd (by norm_num) this
    omega
  · have hepos : 0 < e.natAbs := Int.natAbs_pos.mpr (by rintro rfl; apply hne; omega)
    have hle : p ≤ e.natAbs := Nat.le_of_dvd hepos (Int.natCast_dvd.mp he')
    have he106 : e.natAbs ≤ 106 := by omega
    by_contra hgt
    have : p = 104 ∨ p = 105 ∨ p = 106 := by omega
    rcases this with rfl | rfl | rfl <;> exact absurd hp (by decide)

/-- **The W-trick for `H₄₅`** (B2 → Lemma 4.9): for every `w ≥ 103`, B2's residue class gives
`b` with `gcd(b + h, ∏_{p ≤ w} p) = 1` on `H₄₅`, and then every compatible system of
congruences has moduli pairwise coprime and coprime to `W`. -/
theorem h45_wtrick_coprime (w : ℕ) (hw : 103 ≤ w) :
    ∃ b : ℕ, (∀ h ∈ BGP212.H45, Nat.gcd (b + h) (primorial w) = 1) ∧
      ∀ (n : ℤ) (D : ℤ → ℕ), (primorial w : ℤ) ∣ n - b →
        (∀ h ∈ BGP212.WTrick.H45Z, (D h : ℤ) ∣ n + h) →
        (∀ h ∈ BGP212.WTrick.H45Z, Nat.Coprime (D h) (primorial w)) ∧
          ∀ h ∈ BGP212.WTrick.H45Z, ∀ h' ∈ BGP212.WTrick.H45Z, h ≠ h' →
            Nat.Coprime (D h) (D h') := by
  obtain ⟨b, hb⟩ := BGP212.Challenge.h45_wtrick_exists (primorial w) (primorial_pos w)
  refine ⟨b, hb, fun n D hn hD => wtrick_coprime_of_primes _ D n b (primorial w) w
    (fun _ hp hpw => (hp.dvd_primorial_iff).mpr hpw) ?_ hn hD ?_⟩
  · intro h hh
    simp only [BGP212.WTrick.H45Z, List.mem_toFinset, List.mem_map] at hh
    obtain ⟨h0, hh0, rfl⟩ := hh
    rw [show (b : ℤ) + (h0 : ℤ) = ((b + h0 : ℕ) : ℤ) by push_cast; ring, Int.gcd_natCast_natCast]
    exact hb h0 hh0
  · intro a ha c hc hne p hp hdvd
    exact le_trans (h45_diff_primes a ha c hc hne p hp hdvd) hw

/-- **103 is sharp.** At `w = 102`, for every `b` there are `n ≡ b (mod ∏_{p ≤ 102} p)` and
moduli `D_h | n + h` with `D_0 = D_206 = 103`, not coprime: the prime 103 divides
`206 − 0`. -/
theorem h45_wtrick_sharp (b : ℕ) :
    ∃ (n : ℤ) (D : ℤ → ℕ), (primorial 102 : ℤ) ∣ n - b ∧
      (∀ h ∈ BGP212.WTrick.H45Z, (D h : ℤ) ∣ n + h) ∧
      (0 : ℤ) ∈ BGP212.WTrick.H45Z ∧ (206 : ℤ) ∈ BGP212.WTrick.H45Z ∧
      ¬ Nat.Coprime (D 0) (D 206) := by
  have hp : Nat.Prime 103 := by decide
  have co : Nat.Coprime (primorial 102) 103 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr (by
      rw [hp.dvd_primorial_iff]; omega))
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder co b 0
  refine ⟨k, fun h => if h = 0 ∨ h = 206 then 103 else 1, ?_, ?_, by decide, by decide, by decide⟩
  · have := (Nat.modEq_iff_dvd).mp hk1.symm
    simpa using this
  · intro h _
    have h103 : (103 : ℤ) ∣ (k : ℤ) := by
      have := (Nat.modEq_iff_dvd).mp hk2.symm
      simpa using this
    by_cases h0 : h = 0 ∨ h = 206
    · simp only [h0, ite_true]
      rcases h0 with rfl | rfl
      · simpa using h103
      · exact dvd_add h103 ⟨2, by norm_num⟩
    · simp [h0]

/-- Without the prime bound on differences the coprimality fails: `H = {0, 6}`, `W = 2`,
`w = 2`, `b = 1`, `n = 3`, `D_0 = 3`, `D_6 = 9`. -/
theorem wtrick_needs_prime_bound :
    ∃ (H : Finset ℤ) (D : ℤ → ℕ) (n b : ℤ) (W w : ℕ),
      (∀ p : ℕ, p.Prime → p ≤ w → p ∣ W) ∧ (∀ h ∈ H, Int.gcd (b + h) W = 1) ∧
      (W : ℤ) ∣ n - b ∧ (∀ h ∈ H, (D h : ℤ) ∣ n + h) ∧
      ∃ h ∈ H, ∃ h' ∈ H, h ≠ h' ∧ ¬ Nat.Coprime (D h) (D h') := by
  refine ⟨{0, 6}, fun h => if h = 0 then 3 else 9, 3, 1, 2, 2, ?_, by decide, by decide,
    by decide, 0, by decide, 6, by decide, by decide, by decide⟩
  intro p hp hp2
  have : p = 2 := by have := hp.two_le; omega
  subst this; exact dvd_refl 2

/-- Without `gcd(b + h, W) = 1` a modulus can share a prime with `W`: `H = {0}`, `W = 2`,
`b = n = 0`, `D_0 = 2`. -/
theorem wtrick_needs_coprime_residue :
    ∃ (H : Finset ℤ) (D : ℤ → ℕ) (n b : ℤ) (W w : ℕ),
      (∀ p : ℕ, p.Prime → p ≤ w → p ∣ W) ∧ (W : ℤ) ∣ n - b ∧ (∀ h ∈ H, (D h : ℤ) ∣ n + h) ∧
      ∃ h ∈ H, ¬ Nat.Coprime (D h) W := by
  refine ⟨{0}, fun _ => 2, 0, 0, 2, 2, ?_, by decide, by decide, 0, by decide, by decide⟩
  intro p hp hp2
  have : p = 2 := by have := hp.two_le; omega
  subst this; exact dvd_refl 2

/-! ## Theorem 4.10 at Table 3, and the final deduction -/

theorem table3_valid : table3Support.Valid := ⟨by decide, support_datum_table3.1⟩

/-- The origin lies in Table 3's support set `T₄₅` (band `j = 1`, no rough coordinates). -/
theorem zero_mem_table3Support : (fun _ => (0 : ℝ)) ∈ table3Support.supportSet := by
  refine ⟨fun _ => ⟨le_refl 0, zero_le_one⟩, 1, le_refl 1, le_refl 1, ?_, ?_, ?_⟩
  · have : (A3 (1 - 1) + εs : ℚ) = 0 := by decide +kernel
    simp only [table3Support] at *
    rw [this]; simp
  · have : (0 : ℚ) < A3 1 + εs := by decide +kernel
    simp only [table3Support, Finset.sum_const_zero]
    exact_mod_cast this
  · have hB : ∀ m, (0 : ℚ) ≤ B m := by
      intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp [B]
      · exact le_trans (by decide +kernel) (BGP212.T711.B_pos m hm)
    simp only [Finset.sum_const_zero]
    exact_mod_cast hB _

/-- **The final deduction, relative to its named inputs.** A4's `theorem_7_11` supplies the
two conclusions that `equidistributed_of_coverage` turns into Definition 4.4 at Table 3;
`theorem_11_1` supplies the variational inequality; Theorem 4.10 gives DHL[45, 2]; and
`dhl_45_implies_gap` gives `H₁ ≤ 212`. -/
theorem final_deduction (A : AnalyticInputs) (S : SieveInputs A) : DHL 45 2 ∧ H1Le 212 := by
  have h711 := BGP212.T711.theorem_7_11 A
  have hdist : S.Equidistributed table3Support := S.equidistributed_of_coverage h711.1 h711.2
  have hdhl : DHL 45 2 := S.theorem_4_10 table3Support table3_valid hdist S.theorem_11_1
  exact ⟨hdhl, dhl_45_implies_gap hdhl⟩

end BGP212.Gap

namespace BGP212.Challenge

open BGP212.Params BGP212.T711 BGP212.Gap Filter

theorem h1_liminf {D : ℕ} (h : H1Le D) : Filter.liminf primeGap atTop ≤ D :=
  BGP212.Gap.h1_liminf h

theorem dhl_implies_gap (k D : ℕ) (H : Finset ℤ) (hcard : H.card = k) (hadm : AdmissibleZ H)
    (hdiam : ∀ a ∈ H, ∀ b ∈ H, b - a ≤ D) (hdhl : DHL k 2) : H1Le D :=
  BGP212.Gap.dhl_implies_gap k D H hcard hadm hdiam hdhl

theorem h45Z_facts :
    BGP212.WTrick.H45Z.card = 45 ∧ AdmissibleZ BGP212.WTrick.H45Z ∧
      ∀ a ∈ BGP212.WTrick.H45Z, ∀ b ∈ BGP212.WTrick.H45Z, b - a ≤ 212 :=
  ⟨h45Z_card, h45Z_admissible, h45Z_diameter⟩

theorem dhl_45_implies_gap : DHL 45 2 → H1Le 212 := BGP212.Gap.dhl_45_implies_gap

theorem wtrick_coprime_of_primes (H : Finset ℤ) (D : ℤ → ℕ) (n b : ℤ) (W w : ℕ)
    (hW : ∀ p : ℕ, p.Prime → p ≤ w → p ∣ W)
    (hb : ∀ h ∈ H, Int.gcd (b + h) W = 1)
    (hn : (W : ℤ) ∣ n - b) (hD : ∀ h ∈ H, (D h : ℤ) ∣ n + h)
    (hdiff : ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → ∀ p : ℕ, p.Prime → (p : ℤ) ∣ h - h' → p ≤ w) :
    (∀ h ∈ H, Nat.Coprime (D h) W) ∧
      ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → Nat.Coprime (D h) (D h') :=
  BGP212.Gap.wtrick_coprime_of_primes H D n b W w hW hb hn hD hdiff

theorem wtrick_coprime (H : Finset ℤ) (D : ℤ → ℕ) (n b : ℤ) (W w : ℕ)
    (hW : ∀ p : ℕ, p.Prime → p ≤ w → p ∣ W)
    (hb : ∀ h ∈ H, Int.gcd (b + h) W = 1)
    (hn : (W : ℤ) ∣ n - b) (hD : ∀ h ∈ H, (D h : ℤ) ∣ n + h)
    (hsmall : ∀ h ∈ H, ∀ h' ∈ H, (h - h').natAbs ≤ w) :
    (∀ h ∈ H, Nat.Coprime (D h) W) ∧
      ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → Nat.Coprime (D h) (D h') :=
  BGP212.Gap.wtrick_coprime H D n b W w hW hb hn hD hsmall

theorem wtrick_coprime_primorial (H : Finset ℤ) (D : ℤ → ℕ) (n b : ℤ) (w : ℕ)
    (hb : ∀ h ∈ H, Int.gcd (b + h) (primorial w) = 1)
    (hn : (primorial w : ℤ) ∣ n - b) (hD : ∀ h ∈ H, (D h : ℤ) ∣ n + h)
    (hsmall : ∀ h ∈ H, ∀ h' ∈ H, (h - h').natAbs ≤ w) :
    (∀ h ∈ H, Nat.Coprime (D h) (primorial w)) ∧
      ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → Nat.Coprime (D h) (D h') :=
  BGP212.Gap.wtrick_coprime_primorial H D n b w hb hn hD hsmall

theorem wtrick_modulus_squarefree (H : Finset ℤ) (D : ℤ → ℕ) (W : ℕ) (hW : Squarefree W)
    (hD : ∀ h ∈ H, Squarefree (D h)) (hcopW : ∀ h ∈ H, Nat.Coprime (D h) W)
    (hcop : ∀ h ∈ H, ∀ h' ∈ H, h ≠ h' → Nat.Coprime (D h) (D h')) :
    Squarefree (W * ∏ h ∈ H, D h) :=
  BGP212.Gap.wtrick_modulus_squarefree H D W hW hD hcopW hcop

theorem h45_diff_primes : ∀ a ∈ BGP212.WTrick.H45Z, ∀ c ∈ BGP212.WTrick.H45Z, a ≠ c →
    ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a - c → p ≤ 103 :=
  BGP212.Gap.h45_diff_primes

theorem h45_wtrick_coprime (w : ℕ) (hw : 103 ≤ w) :
    ∃ b : ℕ, (∀ h ∈ BGP212.H45, Nat.gcd (b + h) (primorial w) = 1) ∧
      ∀ (n : ℤ) (D : ℤ → ℕ), (primorial w : ℤ) ∣ n - b →
        (∀ h ∈ BGP212.WTrick.H45Z, (D h : ℤ) ∣ n + h) →
        (∀ h ∈ BGP212.WTrick.H45Z, Nat.Coprime (D h) (primorial w)) ∧
          ∀ h ∈ BGP212.WTrick.H45Z, ∀ h' ∈ BGP212.WTrick.H45Z, h ≠ h' →
            Nat.Coprime (D h) (D h') :=
  BGP212.Gap.h45_wtrick_coprime w hw

theorem h45_wtrick_sharp (b : ℕ) :
    ∃ (n : ℤ) (D : ℤ → ℕ), (primorial 102 : ℤ) ∣ n - b ∧
      (∀ h ∈ BGP212.WTrick.H45Z, (D h : ℤ) ∣ n + h) ∧
      (0 : ℤ) ∈ BGP212.WTrick.H45Z ∧ (206 : ℤ) ∈ BGP212.WTrick.H45Z ∧
      ¬ Nat.Coprime (D 0) (D 206) :=
  BGP212.Gap.h45_wtrick_sharp b

theorem wtrick_needs_prime_bound :
    ∃ (H : Finset ℤ) (D : ℤ → ℕ) (n b : ℤ) (W w : ℕ),
      (∀ p : ℕ, p.Prime → p ≤ w → p ∣ W) ∧ (∀ h ∈ H, Int.gcd (b + h) W = 1) ∧
      (W : ℤ) ∣ n - b ∧ (∀ h ∈ H, (D h : ℤ) ∣ n + h) ∧
      ∃ h ∈ H, ∃ h' ∈ H, h ≠ h' ∧ ¬ Nat.Coprime (D h) (D h') :=
  BGP212.Gap.wtrick_needs_prime_bound

theorem wtrick_needs_coprime_residue :
    ∃ (H : Finset ℤ) (D : ℤ → ℕ) (n b : ℤ) (W w : ℕ),
      (∀ p : ℕ, p.Prime → p ≤ w → p ∣ W) ∧ (W : ℤ) ∣ n - b ∧ (∀ h ∈ H, (D h : ℤ) ∣ n + h) ∧
      ∃ h ∈ H, ¬ Nat.Coprime (D h) W :=
  BGP212.Gap.wtrick_needs_coprime_residue

theorem table3_valid : table3Support.Valid := BGP212.Gap.table3_valid

theorem zero_mem_table3Support : (fun _ => (0 : ℝ)) ∈ table3Support.supportSet :=
  BGP212.Gap.zero_mem_table3Support

theorem final_deduction (A : AnalyticInputs) (S : SieveInputs A) : DHL 45 2 ∧ H1Le 212 :=
  BGP212.Gap.final_deduction A S

end BGP212.Challenge
