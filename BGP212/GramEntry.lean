/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.3–§9.4 and Lemma 9.1 (pp. 40–41), (10.1), Lemma 10.1
and Proposition 10.2 (pp. 41–42), §11 (B₂₁, p. 42).
-/
import BGP212.SimplexMoment
import BGP212.Params
import Mathlib.Algebra.Order.Field.Rat

/-! # V2b: one Gram entry of `I_T` as a Lebesgue integral

Track B (Mathlib measure theory). V2a computed the Gram entry
`I_T[(1, ∅), (0, (2))] = ∫_{T̃} (L − P₁) P₂ dx` as an exact rational by Proposition 10.2's
decomposition. V2b proves that decomposition is the Lebesgue integral.

Objects (all parametrized by the cap function `C : ℕ → ℝ`, as V2a's cap audit recommends):

* `supportT N g L C`: Lemma 9.1's rescaled support `{x ≥ 0 : Σ xᵢ ≤ L, R_g(x) ≤ C(s(x))}`, with
  `roughSet g x = {i : g < xᵢ}`, `s(x) = |roughSet g x|`, `R_g(x) = Σ_{roughSet} xᵢ`.
* `Qset g L C R K`: an inclusion–exclusion piece (coordinates in `R ∪ K` exceed `g`, cap of `R`).
* `pieceSet N R c M`: a translated piece `{y ≥ 0 : Σ_R y ≤ c, Σ y ≤ M}`; `shiftV g S = g · 1_S`.
* `simplexF ι R`, `momentF ι R e`: (10.1) over any finite index type.
* `wsVal`, `twoGroup`, `Hin`, `Hk`, `Hout`, `gramRow`, `gramFormula`: the closed form, defined over
  any linearly ordered field, so the same definition is evaluated over `ℚ` by the kernel and
  used over `ℝ` in the integral theorems.
* `gramEntryQ`: the Table 3 instance, `45 · gramFormula 45 (41/625) (53/50) C 2 1 : ℚ`. -/

namespace BGP212.Gram

/-! ## Sets -/

/-- The simplex `{z ≥ 0, Σ z ≤ R}` over a finite index type. -/
def simplexF (ι : Type*) [Fintype ι] (R : ℝ) : Set (ι → ℝ) := {z | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ R}

/-- The right side of (10.1) over a finite index type. -/
noncomputable def momentF (ι : Type*) [Fintype ι] (R : ℝ) (e : ι → ℕ) : ℝ :=
  R ^ (Fintype.card ι + ∑ i, e i) * (∏ i, ((e i).factorial : ℝ)) /
    ((Fintype.card ι + ∑ i, e i).factorial : ℝ)

/-- The rough coordinates `{i : g < xᵢ}`. -/
noncomputable def roughSet {N : ℕ} (g : ℝ) (x : Fin N → ℝ) : Finset (Fin N) :=
  by classical exact Finset.univ.filter fun i => g < x i

/-- **Lemma 9.1's rescaled support** with cap function `C`:
`{x ≥ 0 : Σ xᵢ ≤ L, R_g(x) ≤ C(s(x))}`. -/
def supportT (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) : Set (Fin N → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ L ∧ ∑ i ∈ roughSet g x, x i ≤ C (roughSet g x).card}

/-- An inclusion–exclusion piece before translation. -/
def Qset {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (R K : Finset (Fin N)) : Set (Fin N → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∀ i ∈ R ∪ K, g < x i) ∧ ∑ i, x i ≤ L ∧ ∑ i ∈ R, x i ≤ C R.card}

/-- A translated piece `{y ≥ 0 : Σ_{i ∈ R} yᵢ ≤ c, Σ yᵢ ≤ M}`. -/
def pieceSet (N : ℕ) (R : Finset (Fin N)) (c M : ℝ) : Set (Fin N → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∑ i ∈ R, y i ≤ c ∧ ∑ i, y i ≤ M}

/-- The shift `g · 1_S`. -/
noncomputable def shiftV {N : ℕ} (g : ℝ) (S : Finset (Fin N)) : Fin N → ℝ :=
  by classical exact fun i => if i ∈ S then g else 0

/-! ## The closed form -/

section Formula
variable {K : Type*} [Field K] [LinearOrder K]

/-- `c^{r + A + j} A! j! / (r + A + j)!`: a weighted simplex moment
`∫_{simplex_r(c)} z_a^A (c − Σ z)^j`. -/
def wsVal (r A j : ℕ) (c : K) : K :=
  c ^ (r + A + j) * (A.factorial : K) * (j.factorial : K) / ((r + A + j).factorial : K)

/-- The two-group value of a piece with `r` coordinates in `R` and `n` outside: exponent `A` on
a coordinate in `R` or `B` on one outside, weight `(M − Σ y)^p`, caps `Σ_R y ≤ c`, `Σ y ≤ M`. -/
def twoGroup (n r A B p : ℕ) (c M : K) : K :=
  if 0 ≤ c ∧ 0 ≤ M then
    (B.factorial : K) * (p.factorial : K) / ((n + B + p).factorial : K) *
      ∑ j ∈ Finset.range (n + B + p + 1), ((n + B + p).choose j : K) *
        (M - min c M) ^ (n + B + p - j) * wsVal r A j (min c M)
  else 0

/-- Pieces with the distinguished coordinate rough (`|R| = r`, `|K| = k`). -/
def Hin (N : ℕ) (g L : K) (C : ℕ → K) (e p r k : ℕ) : K :=
  ∑ t ∈ Finset.range (e + 1), (e.choose t : K) * g ^ (e - t) *
    twoGroup (N - r) r t 0 p (C r - r * g) (L - ((r : K) + k) * g)

/-- Pieces with the distinguished coordinate in the inclusion–exclusion set. -/
def Hk (N : ℕ) (g L : K) (C : ℕ → K) (e p r k : ℕ) : K :=
  ∑ t ∈ Finset.range (e + 1), (e.choose t : K) * g ^ (e - t) *
    twoGroup (N - r) r 0 t p (C r - r * g) (L - ((r : K) + k) * g)

/-- Pieces with the distinguished coordinate smooth and unshifted. -/
def Hout (N : ℕ) (g L : K) (C : ℕ → K) (e p r k : ℕ) : K :=
  ∑ t ∈ Finset.range (e + 1), (e.choose t : K) * (0 : K) ^ (e - t) *
    twoGroup (N - r) r 0 t p (C r - r * g) (L - ((r : K) + k) * g)

/-- One row (`r` rough coordinates besides the distinguished one) of the closed form. -/
def gramRow (N : ℕ) (g L : K) (C : ℕ → K) (e p r : ℕ) : K :=
  ((N - 1).choose r : K) *
    ∑ k ∈ Finset.range (N - 1 - r + 1), ((N - 1 - r).choose k : K) *
      ((-1 : K) ^ k * Hin N g L C e p (r + 1) k + (-1 : K) ^ k * Hout N g L C e p r k -
        (-1 : K) ^ k * Hk N g L C e p r (k + 1))

/-- **The closed form** of `∫_{T̃} (L − Σ x)^p x_a^e` (Proposition 10.2 made explicit). -/
def gramFormula (N : ℕ) (g L : K) (C : ℕ → K) (e p : ℕ) : K :=
  ∑ r ∈ Finset.range (N - 1 + 1), gramRow N g L C e p r

end Formula

/-- **The Table 3 Gram entry** `I_T[(1, ∅), (0, (2))]`, as a rational:
`45 · gramFormula 45 g L C 2 1` with Table 3's `g = 41/625`, `L = 53/50`, `C(m) = 4B₁,ₘ`
(`BGP212.Params`). -/
def gramEntryQ : ℚ :=
  45 * gramFormula 45 BGP212.Params.g BGP212.Params.L BGP212.Params.C 2 1

end BGP212.Gram
