/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Lemma 9.1 (p. 41), (10.1), Lemma 10.1, Proposition 10.2 (pp. 41–42),
§11 (B₂₁, p. 42).
-/
import BGP212.GramEntry

/-! # V2c: the general monomial integral bridge

Track B. V2b proved the closed form for one distinguished coordinate. V2c proves it for every
monomial `(L − Σ x)^p ∏ xᵢ^{eᵢ}`, with the distinguished coordinates `D = suppE e` placed in the
rough set (`A`), in the inclusion–exclusion set (`B`), or neither:

* `twoGroupW`: the two-group value of a piece with weight `W = ∏ tᵢ!`;
* `pieceTermGen`, `Sig`: one inclusion–exclusion piece, and the signed sum over rough sets
  `R ⊆ U` and `K ⊆ U \ R` (the counting statements are about `Sig`);
* `phiGen`: one placement `(A, B)` at `|R| = ρ`, `|K| = κ`;
* `gramGen`: the closed form (placements, then binomial multiplicities over the `N − |D|`
  coordinates outside `D`);
* `expo qs φ`: the exponent vector of a placement `φ` of power-sum parts `qs`, so that
  `∏_{q ∈ qs} P_q = Σ_φ ∏ xᵢ^{expo qs φ i}`;
* `phiFin`, `finCell`, `finRow`, `gramFin`: the same closed form indexed by `Fin d` (the transport
  theorem `gramGen_extend`), with loops of size `d`; the kernel evaluates these;
* `pairExp i j a b`, `gramExampleQ`: the worked example.

All closed forms are defined over any linearly ordered field (evaluated over `ℚ` by the kernel,
used over `ℝ` in the integral theorems); every integral statement keeps the cap function `C` as a
parameter. -/

namespace BGP212.Gram

/-- Two-group value with a general weight `W` (the product of the factorials of all exponents). -/
def twoGroupW {K : Type*} [Field K] [LinearOrder K] (n r A B p : ℕ) (W c M : K) : K :=
  if 0 ≤ c ∧ 0 ≤ M then
    W * (p.factorial : K) / ((n + B + p).factorial : K) *
      ∑ j ∈ Finset.range (n + B + p + 1), ((n + B + p).choose j : K) *
        (M - min c M) ^ (n + B + p - j) *
          ((min c M) ^ (r + A + j) * (j.factorial : K) / ((r + A + j).factorial : K))
  else 0

section FormulaGen
variable {K : Type*} [Field K] [LinearOrder K]

/-- The distinguished coordinates: the support of the exponent vector. -/
def suppE {N : ℕ} (e : Fin N → ℕ) : Finset (Fin N) := Finset.univ.filter fun i => e i ≠ 0

/-- One placement `(A, B)` of the distinguished coordinates (`A` rough, `B` in the
inclusion–exclusion set), with `ρ = |R|`, `κ = |K|`. -/
def phiGen (N : ℕ) (g L : K) (C : ℕ → K) (e : Fin N → ℕ) (p : ℕ) (A B : Finset (Fin N))
    (ρ κ : ℕ) : K :=
  ∑ t ∈ Fintype.piFinset (fun i => Finset.range (e i + 1)),
    (∏ i, ((e i).choose (t i) : K) * (if i ∈ A ∪ B then g else 0) ^ (e i - t i)) *
      twoGroupW (N - ρ) ρ (∑ i ∈ A, t i) (∑ i ∈ Aᶜ, t i) p (∏ i, ((t i).factorial : K))
        (C ρ - ρ * g) (L - ((ρ : K) + κ) * g)

/-- **The closed form** of `∫_{T̃} (L − Σ x)^p ∏ xᵢ^{eᵢ}`: placements of the distinguished
coordinates, then binomial multiplicities over the remaining `N − |D|`. -/
def gramGen (N : ℕ) (g L : K) (C : ℕ → K) (e : Fin N → ℕ) (p : ℕ) : K :=
  ∑ A ∈ (suppE e).powerset, ∑ B ∈ (suppE e \ A).powerset, (-1 : K) ^ B.card *
    ∑ r ∈ Finset.range ((suppE e)ᶜ.card + 1), (((suppE e)ᶜ.card).choose r : K) *
      ∑ k ∈ Finset.range ((suppE e)ᶜ.card - r + 1), (((suppE e)ᶜ.card - r).choose k : K) *
        ((-1 : K) ^ k * phiGen N g L C e p A B (A.card + r) (B.card + k))

end FormulaGen

/-- The exponent vector of a placement `φ` of the parts `qs` on coordinates:
`expo qs φ i = Σ_{j : φ j = i} qs[j]`. -/
def expo {N : ℕ} (qs : List ℕ) (φ : Fin qs.length → Fin N) : Fin N → ℕ :=
  fun i => ∑ j ∈ Finset.univ.filter (fun j => φ j = i), qs[j.1]

/-- Two distinguished coordinates: exponent `a` at `i` plus exponent `b` at `j`
(`a + b` at `i` when `i = j`). -/
def pairExp {N : ℕ} (i j : Fin N) (a b : ℕ) : Fin N → ℕ :=
  fun k => (if i = k then a else 0) + (if j = k then b else 0)


/-! ## Pieces and signed sums over `(R, K)` (real-valued) -/

/-- The value of one inclusion–exclusion piece `(R, K)` for `(L − Σ x)^p ∏ xᵢ^{eᵢ}`. -/
noncomputable def pieceTermGen {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (e : Fin N → ℕ) (p : ℕ)
    (R K : Finset (Fin N)) : ℝ :=
  ∑ t ∈ Fintype.piFinset (fun i => Finset.range (e i + 1)),
    (∏ i, ((e i).choose (t i) : ℝ) * shiftV g (R ∪ K) i ^ (e i - t i)) *
      twoGroupW (N - R.card) R.card (∑ i ∈ R, t i) (∑ i ∈ Rᶜ, t i) p (∏ i, ((t i).factorial : ℝ))
        (C R.card - R.card * g) (L - (R.card + K.card) * g)

/-- The signed sum over rough sets `R ⊆ U` and inclusion–exclusion sets `K ⊆ U \ R`. -/
noncomputable def Sig {N : ℕ} (U : Finset (Fin N)) (G : Finset (Fin N) → Finset (Fin N) → ℝ) : ℝ :=
  ∑ R ∈ U.powerset, ∑ K ∈ (U \ R).powerset, (-1 : ℝ) ^ K.card * G R K

section Fin
variable {K : Type*} [Field K] [LinearOrder K]

/-- `phiGen` with the distinguished coordinates indexed by `Fin d` (exponents `es`, all
positive): loops of size `d` instead of `N`. -/
def phiFin (N d : ℕ) (g L : K) (C : ℕ → K) (es : Fin d → ℕ) (p : ℕ) (A B : Finset (Fin d))
    (ρ κ : ℕ) : K :=
  ∑ t ∈ Fintype.piFinset (fun j => Finset.range (es j + 1)),
    (∏ j, ((es j).choose (t j) : K) * (if j ∈ A ∪ B then g else 0) ^ (es j - t j)) *
      twoGroupW (N - ρ) ρ (∑ j ∈ A, t j) (∑ j ∈ Aᶜ, t j) p (∏ j, ((t j).factorial : K))
        (C ρ - ρ * g) (L - ((ρ : K) + κ) * g)

/-- One cell of `gramFin`: row `r` (rough coordinates outside the distinguished ones) and one
placement `(A, B)` of the distinguished coordinates. -/
def finCell (N d : ℕ) (g L : K) (C : ℕ → K) (es : Fin d → ℕ) (p r : ℕ) (A B : Finset (Fin d)) :
    K :=
  (-1 : K) ^ B.card * (((N - d).choose r : K) *
    ∑ k ∈ Finset.range (N - d - r + 1), ((N - d - r).choose k : K) *
      ((-1 : K) ^ k * phiFin N d g L C es p A B (A.card + r) (B.card + k)))

/-- One row of `gramFin`: the cells over all placements. -/
def finRow (N d : ℕ) (g L : K) (C : ℕ → K) (es : Fin d → ℕ) (p r : ℕ) : K :=
  ∑ A ∈ (Finset.univ : Finset (Fin d)).powerset, ∑ B ∈ (Finset.univ \ A).powerset,
    finCell N d g L C es p r A B

/-- **The closed form indexed by the distinguished coordinates** (`gramGen` transported along
an embedding `Fin d ↪ Fin N`; see `gramGen_extend`). -/
def gramFin (N d : ℕ) (g L : K) (C : ℕ → K) (es : Fin d → ℕ) (p : ℕ) : K :=
  ∑ r ∈ Finset.range (N - d + 1), finRow N d g L C es p r

end Fin

/-- **The worked example** `I_T[(1, (2)), (0, (2))] = ∫_{T̃} (L − P₁) P₂²` at Table 3, as a
rational: `45 · ∫ (L − P₁) x₀⁴ + 45·44 · ∫ (L − P₁) x₀² x₁²`. -/
def gramExampleQ : ℚ :=
  45 * gramFin 45 1 BGP212.Params.g BGP212.Params.L BGP212.Params.C ![4] 1 +
    1980 * gramFin 45 2 BGP212.Params.g BGP212.Params.L BGP212.Params.C ![2, 2] 1

end BGP212.Gram
