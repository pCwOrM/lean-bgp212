/-
Vendored from thinkthoughts/general-divisor-theorem, release v1.0.0 (commit cef9605),
file GeneralDivisorTheorem/Basic.lean, sha256 4adb0144dfb1822cbff45e13978034e381002c440ec168f1d8fbd3faf4640f39.
Copyright (c) 2026 Dan Hawkley. Released under the Apache 2.0 license of that repository.

Mechanical changes only: module-system syntax (`module`, `public import`,
`@[expose] public section`) replaced by plain imports. The namespace `GDT` and every
definition are unchanged, so `GDT.rad`, `GDT.d`, `GDT.R`, `GDT.Tmin`, `GDT.Admissible`
and `GDT.accepted` are GDT v1.0.0's definitions exactly.
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic

/-!
# General Divisor Theorem: Core Definitions

Core definitions used by the formalization of the General Divisor Theorem.
-/


namespace GDT

def rad (n : ℕ) : ℕ := n.primeFactors.prod id

def d (N m : ℕ) : ℕ := rad (Nat.gcd m N)

def R (N m : ℕ) : ℕ := rad N / d N m

def Tmin (N m : ℕ) : ℕ := m * R N m

def Admissible (N m : ℕ) (a : ℤ) : Prop :=
  Nat.gcd a.natAbs (d N m) = 1

def accepted (N m : ℕ) (a : ℤ) (n : ℕ) : Prop :=
  (n : ℤ) ≡ a [ZMOD (m : ℤ)] ∧ Nat.gcd n N = 1

instance acceptedDecidable (N m : ℕ) (a : ℤ) :
    DecidablePred (accepted N m a) := by
  intro n
  unfold accepted
  apply instDecidableAnd

def S (N L m : ℕ) (a : ℤ) : Finset ℕ :=
  (Finset.Icc 1 L).filter (accepted N m a)

def IsPeriod (N m : ℕ) (a : ℤ) (t : ℕ) : Prop :=
  ∀ n : ℕ, accepted N m a (n + t) ↔ accepted N m a n

end GDT
