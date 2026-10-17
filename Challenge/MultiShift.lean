/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Specification of record: specs/B0_multishift_gdt.yaml (Track B, phase B1).
Extends: thinkthoughts/general-divisor-theorem v1.0.0 (commit cef9605).
-/
import BGP212.MultiShift

/-! # Multi-shift GDT (B1): statements

Statements only; proofs live in `Solution/MultiShift.lean`. -/

namespace BGP212.Challenge

open GDT BGP212.MultiShift

/-- **Dichotomy.** Without multi-shift admissibility the accepted set is empty, for
every `L`. Mirrors `gdt_empty`. -/
theorem gdtH_empty {N m L : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ} {H : Finset ℤ}
    (h : ¬ AdmissibleH N m a H) :
    SH N L m a H = ∅ :=
  sorry

/-- **Period.** `Tmin = mR` is a period. Mirrors `gdt_periodic`. -/
theorem gdtH_periodic {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ} {H : Finset ℤ}
    (h : AdmissibleH N m a H) :
    IsPeriodH N m a H (Tmin N m) :=
  sorry

/-- **Exact count.** Every window `[b, b + Tmin)` holds exactly
`∏_{p ∣ R} (p − ν_p(H))` accepted values. Mirrors `gdt_count_per_period`. -/
theorem gdtH_count_per_period {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ} {H : Finset ℤ}
    (h : AdmissibleH N m a H) (b : ℕ) :
    ((Finset.Ico b (b + Tmin N m)).filter (acceptedH N m a H)).card = localCount N m H :=
  sorry

/-- **Density, exact form.** With `L = q·Tmin + s`, the count up to `L` is `q` full
periods plus the count up to `s`. Mirrors `gdt_density`. -/
theorem gdtH_density {N m q s : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ} {H : Finset ℤ}
    (h : AdmissibleH N m a H) (hs : s < Tmin N m) :
    (SH N (q * Tmin N m + s) m a H).card = q * localCount N m H + (SH N s m a H).card :=
  sorry

/-- **Absolute density.** The per-period count over the period is
`(1/m) ∏_{p ∣ R} (1 − ν_p(H)/p)`; the factor `1/m` matches GDT v1.0.0's `φ(R)/(mR)`. -/
theorem gdtH_density_formula {N m : ℕ} (hN : 0 < N) (hm : 0 < m) (H : Finset ℤ) :
    (localCount N m H : ℚ) / (Tmin N m : ℚ) =
      (1 / (m : ℚ)) * ∏ p ∈ (R N m).primeFactors, (1 - (nu p H : ℚ) / (p : ℚ)) :=
  sorry

/-- **Specialization `H = {0}`.** Admissibility, acceptance and the count reduce to
GDT v1.0.0's `Admissible`, `accepted` and `φ(R)`. -/
theorem gdtH_single_shift {N m : ℕ} (hN : 0 < N) (a : ℤ) :
    (AdmissibleH N m a {0} ↔ Admissible N m a) ∧
    (∀ n : ℕ, acceptedH N m a {0} n ↔ accepted N m a n) ∧
    localCount N m {0} = Nat.totient (R N m) :=
  sorry

/-- **GDT v1.0.0's `gdt_count_per_period`, re-derived.** The statement is
`gdt_count_per_period` verbatim; the proof goes through the multi-shift theorem. -/
theorem gdt_count_per_period_via_multishift {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ}
    (h : Admissible N m a) (b : ℕ) :
    ((Finset.Ico b (b + Tmin N m)).filter (accepted N m a)).card =
      Nat.totient (R N m) :=
  sorry

end BGP212.Challenge
