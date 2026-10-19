/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), §9.4, Lemma 9.2 (p. 41), Proposition 10.2 (pp. 41–42).
-/
import BGP212.CapCell
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # V2e-B: polygon cells of the cap branch

Statements only; proofs live in `Solution/CapCell.lean`. Objects are defined in
`BGP212/CapCell.lean` (with V2e-A's `tri`, `aggR`, `aggS`, `aggExp`, `aggConst`, `endpointAgg`,
V2b's `simplexF`, `pieceSet`). The general statements keep `g`, `L`, `C` as parameters; Table 3
enters only through `BGP212.Params` in the last four statements. -/

namespace BGP212.Challenge

open BGP212.Gram BGP212.V2d BGP212.V2e MeasureTheory

/-- **Fubini on a cell**: `∫_{boxTri A B D} f = ∫_{[0,A]} ∫_{[0, min B (D − u)]} f(u, s) ds du`. -/
theorem boxTri_integral (A B D : ℝ) (f : ℝ × ℝ → ℝ) (hf : Continuous f) :
    ∫ q in boxTri A B D, f q =
      ∫ u in Set.Icc 0 A, ∫ s in Set.Icc 0 (min B (D - u)), f (u, s) :=
  sorry

/-- **Monomials on a cell**: `∫_{boxTri A B D} u₁^α u₂^β = boxVal A B D α β`. -/
theorem box_monomial (A B D : ℝ) (α β : ℕ) :
    ∫ q in boxTri A B D, q.1 ^ α * q.2 ^ β = boxVal A B D α β :=
  sorry

/-- `boxVal` commutes with the cast `ℚ → ℝ`: over `ℚ` it is the computable certificate value. -/
theorem boxVal_cast (A B D : ℚ) (α β : ℕ) :
    ((boxVal A B D α β : ℚ) : ℝ) = boxVal (A : ℝ) (B : ℝ) (D : ℝ) α β :=
  sorry

/-- **Empty cell** (`A < 0` or `B < 0`). -/
theorem boxVal_empty (A B D : ℝ) (α β : ℕ) (h : A < 0 ∨ B < 0) : boxVal A B D α β = 0 :=
  sorry

/-- **Cell beyond the diagonal** (`D ≤ 0`): only the null set `u₁ = u₂ = 0` remains. -/
theorem boxVal_nonpos (A B D : ℝ) (α β : ℕ) (hD : D ≤ 0) : boxVal A B D α β = 0 :=
  sorry

/-- **Rectangular cell** (`A + B ≤ D`, the anti-diagonal inactive): the product of two
one-variable moments. -/
theorem boxVal_rect (A B D : ℝ) (α β : ℕ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : A + B ≤ D) :
    boxVal A B D α β = A ^ (α + 1) / (α + 1) * (B ^ (β + 1) / (β + 1)) :=
  sorry

/-- `∫_{boxTri A B D} u₁^α u₂^β (a − u₁)^m = capPowVal A B D a α β m`. -/
theorem box_capPow (A B D a : ℝ) (α β m : ℕ) :
    ∫ q in boxTri A B D, q.1 ^ α * q.2 ^ β * (a - q.1) ^ m = capPowVal A B D a α β m :=
  sorry

/-- **Rational polynomials on a cell**: for `P ∈ ℚ[u₁, u₂]`,
`∫_{boxTri A B D} P(u₁, u₂) = Σ_d coeff_d(P) · boxVal A B D d₀ d₁`. -/
theorem box_poly (A B D : ℝ) (P : MvPolynomial (Fin 2) ℚ) :
    ∫ q in boxTri A B D, MvPolynomial.eval₂ (algebraMap ℚ ℝ) ![q.1, q.2] P =
      ∑ d ∈ P.support, ((P.coeff d : ℚ) : ℝ) * boxVal A B D (d 0) (d 1) :=
  sorry

/-- **Cap branch**: `u₁ ≤ C(r+1) − (r+1) g` and `u₂ ≤ L − k g − C(r+1)` give
`U = C(r+1) − r g − u₁`. -/
theorem endpointAgg_cap (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (u₁ u₂ : ℝ) (h₁ : u₁ ≤ C (r + 1) - (r + 1) * g) (h₂ : u₂ ≤ L - k * g - C (r + 1)) :
    endpointAgg g L C r k u₁ u₂ = C (r + 1) - (r * g + u₁) :=
  sorry

/-- **`g` branch**: `u₁ ≥ C(r+1) − (r+1) g` and `u₁ + u₂ ≤ L − (r+k+1) g` give `U = g`. -/
theorem endpointAgg_gBranch (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (u₁ u₂ : ℝ) (h₁ : C (r + 1) - (r + 1) * g ≤ u₁)
    (h₂ : u₁ + u₂ ≤ L - (r + k + 1) * g) : endpointAgg g L C r k u₁ u₂ = g :=
  sorry

/-- **`L − S` branch**, cap side: `u₁ ≤ C(r+1) − (r+1) g` and `u₂ ≥ L − k g − C(r+1)`. -/
theorem endpointAgg_LBranch_cap (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (u₁ u₂ : ℝ) (h₁ : u₁ ≤ C (r + 1) - (r + 1) * g)
    (h₂ : L - k * g - C (r + 1) ≤ u₂) :
    endpointAgg g L C r k u₁ u₂ = L - ((r + k) * g + u₁ + u₂) :=
  sorry

/-- **`L − S` branch**, `g` side: `u₁ ≥ C(r+1) − (r+1) g` and `u₁ + u₂ ≥ L − (r+k+1) g`. -/
theorem endpointAgg_LBranch_g (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (u₁ u₂ : ℝ) (h₁ : C (r + 1) - (r + 1) * g ≤ u₁)
    (h₂ : L - (r + k + 1) * g ≤ u₁ + u₂) :
    endpointAgg g L C r k u₁ u₂ = L - ((r + k) * g + u₁ + u₂) :=
  sorry

/-- **The τ constraint is inactive on the cap branch**: there `g ≤ U ≤ L − S`, so
`S = (r+k) g + u₁ + u₂ ≤ L − g`. -/
theorem cap_total_le (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (u₁ u₂ : ℝ) (h₁ : u₁ ≤ C (r + 1) - (r + 1) * g) (h₂ : u₂ ≤ L - k * g - C (r + 1)) :
    (r + k) * g + u₁ + u₂ ≤ L - g :=
  sorry


theorem mem_capCell (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ) (q : ℝ × ℝ) :
    q ∈ capCell g L C r k c M ↔ q ∈ tri M ∧ q.1 ≤ c ∧ q.1 ≤ C (r + 1) - (r + 1) * g ∧
      q.2 ≤ L - k * g - C (r + 1) :=
  sorry

/-- On the cap cell the endpoint takes the cap value. -/
theorem endpointAgg_on_capCell (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ) (q : ℝ × ℝ)
    (hq : q ∈ capCell g L C r k c M) :
    endpointAgg g L C r k q.1 q.2 = C (r + 1) - (r * g + q.1) :=
  sorry

/-- **Rectangular cap cells**: if `L − g ≤ τ`, the piece total `M = τ − (r+k) g` never cuts the
cap cell (`A + B ≤ M`). -/
theorem capCell_rect (g L τ : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c : ℝ) (hτ : L - g ≤ τ) :
    min c (C (r + 1) - (r + 1) * g) + (L - k * g - C (r + 1)) ≤ τ - (r + k) * g :=
  sorry

/-- **Empty cap cells**: if `L − k g < C(r+1)` the cap branch is empty on the piece. -/
theorem capCell_empty (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ) (h : L - k * g < C (r + 1)) :
    capCell g L C r k c M = ∅ :=
  sorry

/-- **The inner integral on the cap cell**, a polynomial in `(u₁, u₂)`:
`∫₀^U (L − S − u)^p u^t du` with `U = C(r+1) − r g − u₁`, `L − S = L − (r+k) g − u₁ − u₂`. -/
theorem cap_inner (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ) (q : ℝ × ℝ)
    (hq : q ∈ capCell g L C r k c M) (p t : ℕ) :
    ∫ u in (0 : ℝ)..endpointAgg g L C r k q.1 q.2, (L - ((r + k) * g + q.1 + q.2) - u) ^ p * u ^ t =
      innerVal (C (r + 1) - (r * g + q.1)) (L - ((r + k) * g + q.1 + q.2)) p t :=
  sorry

/-- On a piece, restricting to the cap cell makes the piece constraints automatic:
the integral over `pieceSet N R c M` equals the integral over the simplex `Σ y ≤ M`. -/
theorem piece_cap_eq {N : ℕ} (R : Finset (Fin N)) (g L : ℝ) (C : ℕ → ℝ) (r k : ℕ) (c M : ℝ)
    (G : (Fin N → ℝ) → ℝ) (Φ : ℝ × ℝ → ℝ) :
    ∫ y in pieceSet N R c M, G y * (capCell g L C r k c M).indicator Φ (aggR R y, aggS R y) =
      ∫ y in simplexF (Fin N) M, G y * (capCell g L C r k c M).indicator Φ (aggR R y, aggS R y) :=
  sorry

/-- **The cap branch on a piece.** For a piece `(R, K)` of V2b's decomposition (`R`, `Rᶜ`
nonempty, `k = |K|`, piece cap `c`, piece total `M`), a monomial weight `yᵗ` and the `m`-th power
of the endpoint restricted to the cap branch:
`∫_{pieceSet} yᵗ · 1_cap · U^m = aggConst R t · aggConst Rᶜ t ·
capPowVal (min c c₁) c₂ M (C(r+1) − r g) (aggExp R t) (aggExp Rᶜ t) m`. -/
theorem cap_branch_piece {N : ℕ} (R : Finset (Fin N)) (hR : R.Nonempty) (hRc : Rᶜ.Nonempty)
    (g L : ℝ) (C : ℕ → ℝ) (k : ℕ) (c M : ℝ) (t : Fin N → ℕ) (m : ℕ) :
    ∫ y in pieceSet N R c M, (∏ i, y i ^ t i) *
        (capCell g L C R.card k c M).indicator
          (fun q => (endpointAgg g L C R.card k q.1 q.2) ^ m) (aggR R y, aggS R y) =
      aggConst {i // i ∈ R} (fun i => t i) * aggConst {i // i ∉ R} (fun i => t i) *
        capPowVal (min c (C (R.card + 1) - (R.card + 1) * g)) (L - k * g - C (R.card + 1)) M
          (C (R.card + 1) - R.card * g) (aggExp {i // i ∈ R} (fun i => t i))
          (aggExp {i // i ∉ R} (fun i => t i)) m :=
  sorry

/-- **`r = 0`**: with no rough coordinates `u₁ = 0` and `U = C(1)` on the cap branch; the piece
integral is a one-aggregate integral over `u₂ ∈ [0, min c₂ M]`. -/
theorem cap_branch_r0 {N : ℕ} (hN : 0 < N) (g L : ℝ) (C : ℕ → ℝ) (k : ℕ) (c M : ℝ)
    (t : Fin N → ℕ) (m : ℕ) (hc : 0 ≤ c) (hc₁ : 0 ≤ C 1 - g) :
    ∫ y in pieceSet N ∅ c M, (∏ i, y i ^ t i) *
        (capCell g L C 0 k c M).indicator
          (fun q => (endpointAgg g L C 0 k q.1 q.2) ^ m) (aggR ∅ y, aggS ∅ y) =
      aggConst (Fin N) t * (C 1 ^ m *
        ((max 0 (min (L - k * g - C 1) (M - 0))) ^ (aggExp (Fin N) t + 1) /
          (aggExp (Fin N) t + 1))) :=
  sorry

/-- At Table 3, `L − g ≤ τ` (`τ − (L − g) = 1/625`). -/
theorem tau_ge_table3 : BGP212.Params.L - BGP212.Params.g ≤ BGP212.Params.τ :=
  sorry

/-- **Every Table 3 cap cell is a rectangle**: the piece total `τ − (r+k) g` never cuts it. -/
theorem capCell_rect_table3 (r k : ℕ) (c : ℝ) :
    min c (C3 (r + 1) - (r + 1) * g3) + (L3 - k * g3 - C3 (r + 1)) ≤ τ3 - (r + k) * g3 :=
  sorry

/-- **Empty Table 3 cap cells**: with one rough coordinate the cap branch is empty once
`k ≥ 7` (`L − 7 g = 751/1250 < C(2) = 794/1250`). -/
theorem capCell_empty_table3 (k : ℕ) (hk : 7 ≤ k) (c M : ℝ) : capCell g3 L3 C3 1 k c M = ∅ :=
  sorry

/-- **The worked certificate**: the cap-branch part of `J_T(1)` on the Table 3 piece
`({0}, ∅)` of `T̂` (`N = 44`) is the explicit rational
`V = (L − C(2))⁴³ ((C(2) − g)³ − g³) / (3 · 43!) ≈ 1.0464 × 10⁻⁷⁰`. -/
theorem capPieceT3_value : capPieceT3 =
    ((2257149812841095726960561293190503471927130196106096204396001203694562350987314959143203078094677121622739446201 / 21569915559007524956605042855904290630373696306163850230268666519073406107054324820637702941894531250000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) :=
  sorry

end BGP212.Challenge
