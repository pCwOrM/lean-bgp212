/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Specification of record: specs/B0_multishift_gdt.yaml.
Extends: thinkthoughts/general-divisor-theorem v1.0.0 (commit cef9605), vendored in BGP212/GDTv1Basic.lean,
reusing its definitions `rad`, `d`, `R`, `Tmin`, `Admissible`, `accepted` verbatim.
-/
import BGP212.GDTv1Basic

/-! # Multi-shift General Divisor Theorem: definitions

GDT v1.0.0 counts `n ≡ a (mod m)` with `gcd(n, N) = 1`. Here one shift becomes a finite
set `H` of integer shifts: `n ≡ a (mod m)` with `gcd(n + h, N) = 1` for every `h ∈ H`.
`H = {0}` is GDT v1.0.0 exactly (`gdtH_single_shift`). -/

namespace BGP212.MultiShift

open GDT

/-- `ν_p(H) = |{ −h mod p : h ∈ H }|`: the residue classes mod `p` that `H` forbids. -/
def nu (p : ℕ) (H : Finset ℤ) : ℕ :=
  (H.image fun h => (-h) % (p : ℤ)).card

/-- `n ≡ a (mod m)` and `gcd(n + h, N) = 1` for every shift `h ∈ H`. -/
def acceptedH (N m : ℕ) (a : ℤ) (H : Finset ℤ) (n : ℕ) : Prop :=
  (n : ℤ) ≡ a [ZMOD (m : ℤ)] ∧ ∀ h ∈ H, Int.gcd ((n : ℤ) + h) (N : ℤ) = 1

instance acceptedHDecidable (N m : ℕ) (a : ℤ) (H : Finset ℤ) :
    DecidablePred (acceptedH N m a H) := by
  intro n
  unfold acceptedH
  infer_instance

/-- Compatibility at the primes shared by `m` and `N`: no prime `p ∣ d` divides `a + h`. -/
def AdmissibleH (N m : ℕ) (a : ℤ) (H : Finset ℤ) : Prop :=
  ∀ p ∈ (d N m).primeFactors, ∀ h ∈ H, ¬ ((p : ℤ) ∣ a + h)

/-- The accepted integers in `[1, L]`, mirroring GDT's `S`. -/
def SH (N L m : ℕ) (a : ℤ) (H : Finset ℤ) : Finset ℕ :=
  (Finset.Icc 1 L).filter (acceptedH N m a H)

/-- `t` is a period of the accepted set, mirroring GDT's `IsPeriod`. -/
def IsPeriodH (N m : ℕ) (a : ℤ) (H : Finset ℤ) (t : ℕ) : Prop :=
  ∀ n : ℕ, acceptedH N m a H (n + t) ↔ acceptedH N m a H n

/-- The exact count per period: `∏_{p ∣ R} (p − ν_p(H))`. -/
def localCount (N m : ℕ) (H : Finset ℤ) : ℕ :=
  ∏ p ∈ (R N m).primeFactors, (p - nu p H)

end BGP212.MultiShift
