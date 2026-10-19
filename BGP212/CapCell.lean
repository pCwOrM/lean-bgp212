/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.4, Lemma 9.2 and the display of `J_T` (p. 41),
Proposition 10.2 (pp. 41–42).
-/
import BGP212.Aggregate
import BGP212.Params

/-! # V2e-B: polygon cells of the cap branch (definitions)

Track B. The objects of the cap-branch cell integration; the theorems are proved in
`Solution/CapCell.lean`.

On a V2b piece `(R, K)` with `r = |R|`, `k = |K|`, aggregates `u₁ = Σ_R y`, `u₂ = Σ_{Rᶜ} y`, the
endpoint of Lemma 9.2 is `U = endpointAgg g L C r k u₁ u₂` (V2e-A). It takes the **cap value**
`U = C(r+1) − r g − u₁` exactly on

  `u₁ ≤ c₁ = C(r+1) − (r+1) g`   (the `max` picks the cap, `U ≥ g`),
  `u₂ ≤ c₂ = L − k g − C(r+1)`   (the `min` picks the cap, `U ≤ L − S`).

Intersected with the piece (`u₁ ≤ c`, `u₁ + u₂ ≤ M`) this is the cell

  `capCell = boxTri (min c c₁) c₂ M`,   `boxTri A B D = {0 ≤ u₁ ≤ A, 0 ≤ u₂ ≤ B, u₁ + u₂ ≤ D}`,

a polygon with at most five sides. `boxVal A B D α β` is the exact value of
`∫_{boxTri A B D} u₁^α u₂^β` over any ordered field (so over `ℚ` it is computable). -/

namespace BGP212.V2e

open BGP212.Gram BGP212.V2d MeasureTheory

/-- **Definition.** The cell `{0 ≤ u₁ ≤ A, 0 ≤ u₂ ≤ B, u₁ + u₂ ≤ D}` (a box cut by an
anti-diagonal). -/
def boxTri (A B D : ℝ) : Set (ℝ × ℝ) :=
  {q | 0 ≤ q.1 ∧ q.1 ≤ A ∧ 0 ≤ q.2 ∧ q.2 ≤ B ∧ q.1 + q.2 ≤ D}

section Formula

variable {K : Type*} [Field K] [LinearOrder K]

/-- `∫₀^X (D − u)^p u^t du`, expanded (V2d's `inner_integral`). -/
def innerVal (X D : K) (p t : ℕ) : K :=
  ∑ j ∈ Finset.range (p + 1),
    (p.choose j : K) * D ^ (p - j) * (-1) ^ j * X ^ (t + j + 1) / (t + j + 1)

/-- **Definition.** The exact value of `∫_{boxTri A B D} u₁^α u₂^β`: with
`E = max 0 (min A (D − B))` (end of the full-height part) and `F = max 0 (min A D)` (end of the
cell), `(B^{β+1} E^{α+1}/(α+1) + ∫_E^F u^α (D − u)^{β+1} du) / (β + 1)`; zero if `A < 0` or
`B < 0`. -/
def boxVal (A B D : K) (α β : ℕ) : K :=
  if 0 ≤ A ∧ 0 ≤ B then
    (B ^ (β + 1) * (max 0 (min A (D - B))) ^ (α + 1) / (α + 1) +
      (innerVal (max 0 (min A D)) D (β + 1) α - innerVal (max 0 (min A (D - B))) D (β + 1) α)) /
      (β + 1)
  else 0

/-- **Definition.** `∫_{boxTri A B D} u₁^α u₂^β (a − u₁)^m`, by the binomial expansion of the
cap power. -/
def capPowVal (A B D a : K) (α β m : ℕ) : K :=
  ∑ i ∈ Finset.range (m + 1), (m.choose i : K) * a ^ (m - i) * (-1) ^ i * boxVal A B D (α + i) β

end Formula

/-- **Definition.** The cap-branch cell of a piece: `r` rough and `k` inclusion–exclusion
coordinates, piece cap `c` (`Σ_R y ≤ c`) and piece total `M` (`Σ y ≤ M`). -/
noncomputable def capCell (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ) : Set (ℝ × ℝ) :=
  boxTri (min c (C (r + 1) - (r + 1) * g)) (L - k * g - C (r + 1)) M

/-! ## Table 3 data and the worked certificate -/

/-- Table 3's `g`, `L`, `τ` and cap function over `ℝ`. -/
noncomputable def g3 : ℝ := (BGP212.Params.g : ℝ)
noncomputable def L3 : ℝ := (BGP212.Params.L : ℝ)
noncomputable def τ3 : ℝ := (BGP212.Params.τ : ℝ)
noncomputable def C3 (m : ℕ) : ℝ := (BGP212.Params.C m : ℝ)

/-- **Definition (worked certificate).** The cap-branch part of `J_T(1)` on the piece
`(R, K) = ({0}, ∅)` of `T̂ = supportT 44 g τ C` (V2b's decomposition, translated): the integral
over `pieceSet 44 {0} (C(1) − g) (τ − g)` of `U²` (the squared fibre length `(∫₀^U 1 du)²`)
restricted to the cap branch. -/
noncomputable def capPieceT3 : ℝ :=
  ∫ y in pieceSet 44 {0} (C3 1 - g3) (τ3 - g3),
    (capCell g3 L3 C3 1 0 (C3 1 - g3) (τ3 - g3)).indicator
      (fun q => (endpointAgg g3 L3 C3 1 0 q.1 q.2) ^ 2) (aggR {0} y, aggS {0} y)

end BGP212.V2e
