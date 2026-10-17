/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): §9.3 (L = 53/50), (10.1) (p. 41), §11 (the space B₂₁, p. 42).
-/
import BGP212.Params
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.LinearAlgebra.Span.Defs

/-! # V0: the variational space `B₂₁`

Track B (Mathlib). §11: "if `λ = (λ₁, …, λ_r)` is a partition all of whose parts are positive
and even, write `|λ| = λ₁ + ⋯ + λ_r` and `P_λ = ∏ⱼ P_{λⱼ}`, with `P_∅ = 1`. We use the space

  `B₂₁ = span_ℚ {(L − P₁)^a P_λ : a ≥ 0, λⱼ ∈ 2ℤ_{>0}, a + |λ| ≤ 21}`.

After repeated monomials are identified, the displayed family has dimension 846."

* `P j` is the power sum `Σᵢ xᵢ^j` in the 45 rescaled coordinates (§9.4), over `ℚ`.
* A partition is a multiset of positive parts (`Multiset ℕ`), so reorderings of `λ` are the
  same index; `IsB21Index a λ` is the printed side condition.
* `B21Idx` is an explicit finite index type: `j ≤ 10`, a partition `μ ⊢ j` (with `λ = 2μ`), and
  `a < 22 − 2j`.
* `simplexMoment` is the right side of (10.1), prepared for V1. -/

namespace BGP212.Var

open MvPolynomial

/-- The 45 rescaled coordinates `x₁, …, x₄₅`. -/
abbrev Poly := MvPolynomial (Fin 45) ℚ

/-- The power sum `P_j = Σᵢ xᵢ^j`. -/
noncomputable def P (j : ℕ) : Poly := psum (Fin 45) ℚ j

/-- `P_λ = ∏ⱼ P_{λⱼ}` for a partition given by its multiset of parts; `P_∅ = 1`. -/
noncomputable def Plam (lam : Multiset ℕ) : Poly := (lam.map P).prod

/-- The parts of `λ` lie in `2ℤ_{>0}`. -/
def EvenParts (lam : Multiset ℕ) : Prop := ∀ x ∈ lam, 0 < x ∧ Even x

/-- The printed index condition: `λⱼ ∈ 2ℤ_{>0}` and `a + |λ| ≤ 21` (`a ≥ 0` as `a : ℕ`). -/
def IsB21Index (a : ℕ) (lam : Multiset ℕ) : Prop := EvenParts lam ∧ a + lam.sum ≤ 21

/-- The spanning element `(L − P₁)^a P_λ`, with `L = 53/50` (§9.3). -/
noncomputable def gen (a : ℕ) (lam : Multiset ℕ) : Poly := (C BGP212.Params.L - P 1) ^ a * Plam lam

/-- **The space `B₂₁`** (§11). -/
noncomputable def B21 : Submodule ℚ Poly :=
  Submodule.span ℚ {f | ∃ a lam, IsB21Index a lam ∧ f = gen a lam}

/-- The explicit index type: `j ∈ {0, …, 10}`, a partition `μ ⊢ j` (`λ = 2μ`, so `|λ| = 2j`),
and `a ∈ {0, …, 21 − 2j}`. -/
abbrev B21Idx := Σ j : Fin 11, Nat.Partition j × Fin (22 - 2 * j)

/-- The exponent `a` of an index. -/
def B21Idx.a (i : B21Idx) : ℕ := i.2.2

/-- The partition `λ = 2μ` of an index. -/
def B21Idx.lam (i : B21Idx) : Multiset ℕ := i.2.1.parts.map (2 * ·)

/-- The index as a printed pair `(a, λ)`. -/
def B21Idx.toPair (i : B21Idx) : ℕ × Multiset ℕ := (i.a, i.lam)

/-- The basis family indexed by `B21Idx`. -/
noncomputable def genIdx (i : B21Idx) : Poly := gen i.a i.lam

/-- The number of partitions of `j`. -/
def p (j : ℕ) : ℕ := Fintype.card (Nat.Partition j)

/-- An explicit enumeration of the partitions of `j` with every part at most `k`, as multisets
of parts: `c` copies of the part `k + 1` and a partition of the rest into parts at most `k`. -/
def partsLE : ℕ → ℕ → List (Multiset ℕ)
  | j, 0 => if j = 0 then [0] else []
  | j, k + 1 => (List.range (j / (k + 1) + 1)).flatMap fun c =>
      (partsLE (j - c * (k + 1)) k).map fun s => Multiset.replicate c (k + 1) + s

/-- The right side of (10.1): `R^{m + Σ eᵢ} ∏ eᵢ! / (m + Σ eᵢ)!`, for exponents `e` (a list of
length `m`). -/
def simplexMoment (R : ℚ) (e : List ℕ) : ℚ :=
  R ^ (e.length + e.sum) * ((e.map Nat.factorial).prod : ℚ) / ((e.length + e.sum).factorial : ℚ)

/-- The one-variable Beta moment `∫₀^R z^u (R − z)^v dz = R^{u+v+1} u! v! / (u + v + 1)!`
(right side; the integral itself is V1's subject). -/
def betaMoment (R : ℚ) (u v : ℕ) : ℚ :=
  R ^ (u + v + 1) * (u.factorial : ℚ) * (v.factorial : ℚ) / ((u + v + 1).factorial : ℚ)

end BGP212.Var
