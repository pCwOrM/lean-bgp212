/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): §9.4, Lemma 9.2 and the display of `J_T` (p. 41), (10.1),
Proposition 10.2 (pp. 41–42).
-/
import BGP212.Fibre

/-! # V2e-A: two-aggregate Dirichlet integration (definitions)

Track B. The objects of the aggregate Dirichlet theorem; the theorems are proved in
`Solution/Aggregate.lean`.

For a finite index type `ι` and an exponent vector `e : ι → ℕ`, the **Dirichlet exponent** and
**Dirichlet constant** of the group are

  `aggExp ι e = |ι| + Σ eᵢ − 1`,   `aggConst ι e = ∏ eᵢ! / (|ι| + Σ eᵢ − 1)!`,

so that, for a nonempty group, `∫_{z ≥ 0, Σ z ≤ R} zᵉ h(Σ z) dz = aggConst ι e ·
∫₀^R s^{aggExp ι e} h(s) ds` (one aggregate). With two groups `I`, `J`, the two group sums
`u₁ = Σ_I`, `u₂ = Σ_J` range over the triangle `tri R = {u₁, u₂ ≥ 0, u₁ + u₂ ≤ R}`.

For V2d's marginal problem the groups are the rough and the smooth coordinates of a V2b piece:
`aggR R y = Σ_{i ∈ R} yᵢ` and `aggS R y = Σ_{i ∉ R} yᵢ` (`Solution/Aggregate.lean`,
`stratumEndpoint_shift`, expresses Lemma 9.2's endpoint through them). -/

namespace BGP212.V2e

open BGP212.Gram BGP212.V2d MeasureTheory

/-- **Definition.** The Dirichlet exponent `|ι| + Σ eᵢ − 1` of a group. -/
def aggExp (ι : Type*) [Fintype ι] (e : ι → ℕ) : ℕ := Fintype.card ι + ∑ i, e i - 1

/-- **Definition.** The Dirichlet constant `∏ eᵢ! / (|ι| + Σ eᵢ − 1)!` of a group. -/
noncomputable def aggConst (ι : Type*) [Fintype ι] (e : ι → ℕ) : ℝ :=
  (∏ i, ((e i).factorial : ℝ)) / ((aggExp ι e).factorial : ℝ)

/-- **Definition.** The two-group region `{z ≥ 0, w ≥ 0, Σ z + Σ w ≤ R}`. -/
def quad (I J : Type*) [Fintype I] [Fintype J] (R : ℝ) : Set ((I → ℝ) × (J → ℝ)) :=
  {p | (∀ i, 0 ≤ p.1 i) ∧ (∀ j, 0 ≤ p.2 j) ∧ ∑ i, p.1 i + ∑ j, p.2 j ≤ R}

/-- **Definition.** The aggregate triangle `{(u₁, u₂) : u₁, u₂ ≥ 0, u₁ + u₂ ≤ R}`. -/
def tri (R : ℝ) : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ R}

/-- **Definition.** The rough aggregate `u₁ = Σ_{i ∈ R} yᵢ`. -/
def aggR {N : ℕ} (R : Finset (Fin N)) (y : Fin N → ℝ) : ℝ := ∑ i ∈ R, y i

/-- **Definition.** The smooth aggregate `u₂ = Σ_{i ∉ R} yᵢ`. -/
def aggS {N : ℕ} (R : Finset (Fin N)) (y : Fin N → ℝ) : ℝ := ∑ i ∈ Rᶜ, y i

/-- **Definition.** The Dirichlet constant over `ℚ`. -/
def aggConstQ (ι : Type*) [Fintype ι] (e : ι → ℕ) : ℚ :=
  (∏ i, ((e i).factorial : ℚ)) / ((aggExp ι e).factorial : ℚ)

/-- **Definition.** Lemma 9.2's endpoint as a function of the aggregates of a translated piece:
with `r = |R|` rough and `k = |K|` inclusion–exclusion coordinates shifted by `g`, the rough mass
is `ρ₁ = r g + u₁` and the total is `S = (r + k) g + u₁ + u₂`, so
`U = min (L − S) (max g (C(r + 1) − ρ₁))`. -/
noncomputable def endpointAgg (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (u₁ u₂ : ℝ) : ℝ :=
  min (L - ((r + k) * g + u₁ + u₂)) (max g (C (r + 1) - (r * g + u₁)))

/-- **Definition.** Lemma 9.2's endpoint with the cap index taken from a given rough set `R`
(the stratum of V2b's decomposition): `U_R(x) = min (L − Σ x) (max g (C(|R| + 1) − Σ_R x))`.
On the stratum `roughSet g x = R` it is `endpoint g L C x`. -/
noncomputable def stratumEndpoint {n : ℕ} (g L : ℝ) (C : ℕ → ℝ) (R : Finset (Fin n))
    (x : Fin n → ℝ) : ℝ :=
  min (L - ∑ i, x i) (max g (C (R.card + 1) - aggR R x))

/-- **Definition.** The worked example's integrand on `ℝ³` (`R = {0}`): `y₀ y₂² · 1[y₀ ≤ c]`,
the rough coordinate cut at `c` (a branch-type constraint on `u₁`). -/
noncomputable def exampleLHS (c R : ℝ) : ℝ :=
  ∫ y in simplexF (Fin 3) R, y 0 * y 2 ^ 2 * (Set.Iic c).indicator (fun _ => (1 : ℝ)) (y 0)

end BGP212.V2e
