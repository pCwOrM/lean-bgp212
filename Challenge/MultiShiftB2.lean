/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Specification of record: specs/B0_multishift_gdt.yaml (Track B, phase B2).
Extends: thinkthoughts/general-divisor-theorem v1.0.0 (commit cef9605), vendored in
BGP212/GDTv1Basic.lean. W-trick source: Axiom Math, Definition 4.5 and §12.
-/
import BGP212.WTrick

/-! # Multi-shift GDT (B2): statements

Statements only; proofs live in `Solution/MultiShiftB2.lean`. -/

namespace BGP212.Challenge

open GDT BGP212.MultiShift BGP212.WTrick

/-- **Relative density.** Within the class `n ≡ a (mod m)`, the density is
`∏_{p ∣ R}(1 − ν_p(H)/p)`: B1's absolute density times `m`, equivalently the per-period
count over the `R` class members per period. -/
theorem gdtH_relative_density {N m : ℕ} (hN : 0 < N) (hm : 0 < m) (H : Finset ℤ) :
    (m : ℚ) * ((localCount N m H : ℚ) / (Tmin N m : ℚ)) =
      ∏ p ∈ (R N m).primeFactors, (1 - (nu p H : ℚ) / (p : ℚ)) ∧
    (localCount N m H : ℚ) / (R N m : ℚ) =
      ∏ p ∈ (R N m).primeFactors, (1 - (nu p H : ℚ) / (p : ℚ)) :=
  sorry

/-- **Local positivity.** The accepted set is nonempty exactly when the class is
compatible at the shared primes (`AdmissibleH`) and every local factor `p − ν_p(H)`
at the remaining primes `p ∣ R` is positive. -/
theorem gdtH_local_positivity {N m : ℕ} (hN : 0 < N) (hm : 0 < m) (a : ℤ) (H : Finset ℤ) :
    (∃ n : ℕ, acceptedH N m a H n) ↔
      AdmissibleH N m a H ∧ ∀ p ∈ (R N m).primeFactors, nu p H < p :=
  sorry

/-- **Minimal period.** For a nonempty shift set and a nonempty accepted set, every
positive period is a multiple of `Tmin = mR`, so `Tmin` is the least positive period.
Mirrors `gdt_minimal_period`; the two hypotheses beyond GDT's are both necessary
(`gdtH_minimal_period_needs_shift`, `gdtH_minimal_period_needs_nonempty`). -/
theorem gdtH_minimal_period {N m : ℕ} (hN : 0 < N) (hm : 0 < m) {a : ℤ} {H : Finset ℤ}
    (hH : H.Nonempty) (hadm : AdmissibleH N m a H) (hpos : ∀ p ∈ (R N m).primeFactors, nu p H < p)
    {t : ℕ} (ht : 0 < t) (hper : IsPeriodH N m a H t) :
    Tmin N m ∣ t :=
  sorry

/-- **Counterexample, empty shift set.** `N = 5, m = 2, a = 0, H = ∅`: the accepted set is
the even numbers, with period `2`, while `Tmin = 10`. -/
theorem gdtH_minimal_period_needs_shift :
    IsPeriodH 5 2 0 ∅ 2 ∧ Tmin 5 2 = 10 ∧ ¬ (10 ∣ 2) :=
  sorry

/-- **Counterexample, empty accepted set.** `N = 2, m = 1, a = 0, H = {0, 1}`: `ν₂(H) = 2`,
the accepted set is empty, and so `1` is a period, while `Tmin = 2`. -/
theorem gdtH_minimal_period_needs_nonempty :
    (¬ ∃ n : ℕ, acceptedH 2 1 0 {0, 1} n) ∧
    IsPeriodH 2 1 0 {0, 1} 1 ∧ Tmin 2 1 = 2 ∧ ¬ (2 ∣ 1) :=
  sorry

/-- **The W-trick count (Definition 4.5).** For a squarefree modulus `W`, the residues
`b mod W` with `gcd(b + h, W) = 1` for every `h ∈ H` number exactly
`∏_{p ∣ W}(p − ν_p(H))`: B1 at `N = W, m = 1`. -/
theorem wtrick_count {W : ℕ} (hW : 0 < W) (hsf : Squarefree W) (H : Finset ℤ) :
    ((Finset.range W).filter
        (fun b : ℕ => ∀ h ∈ H, Int.gcd ((b : ℤ) + h) (W : ℤ) = 1)).card =
      ∏ p ∈ W.primeFactors, (p - nu p H) :=
  sorry

/-- **Lemma 12.1 as local factors (the Join).** A tuple is admissible in the sense of
§2 exactly when every local factor `p − ν_p(H)` is positive. -/
theorem admissible_iff_local_factors (H : List ℕ) :
    BGP212.Admissible H ↔
      ∀ p : ℕ, p.Prime → nu p ((H.map (fun h : ℕ => (h : ℤ))).toFinset) < p :=
  sorry

/-- **The W-trick for `H₄₅`, every modulus.** For every `W > 0` some `b` has
`gcd(b + h, W) = 1` for all `h ∈ H₄₅`: the residue class Definition 4.5 requires exists for
every `W`, from Lemma 12.1 through local positivity. -/
theorem h45_wtrick_exists :
    ∀ W : ℕ, 0 < W → ∃ b : ℕ, ∀ h ∈ BGP212.H45, Nat.gcd (b + h) W = 1 :=
  sorry

/-- **The W-trick for `H₄₅` at `W = 2·3·…·23`.** Every local factor is `1`, so the
residue is unique: `b ≡ 74549147 (mod 223092870)`. -/
theorem h45_wtrick_W23 :
    localCount W23 1 H45Z = 1 ∧
    ∀ b : ℕ, b < W23 → ((∀ h ∈ BGP212.H45, Nat.gcd (b + h) W23 = 1) ↔ b = 74549147) :=
  sorry

end BGP212.Challenge
