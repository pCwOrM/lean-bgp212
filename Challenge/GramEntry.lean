/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Table 3 (p. 39), Lemma 9.1 (p. 41), (10.1), Lemma 10.1, Proposition 10.2
(pp. 41–42), §11 (p. 42).
-/
import BGP212.GramEntry
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # V2b: one Gram entry of `I_T` as a Lebesgue integral

Statements only; proofs live in `Solution/GramEntry.lean` (integral identities) and
`Solution/GramEntryCert.lean` (the kernel-evaluated rational certificate). Objects are defined in
`BGP212/GramEntry.lean`; every integral statement is parametrized by the cap function `C`,
except the three Table 3 instances at the end. -/

namespace BGP212.Challenge

open BGP212.Gram MeasureTheory

/-- **(10.1) over any finite index type** (V1 transported along `Fintype.equivFin`). -/
theorem simplexF_integral {ι : Type*} [Fintype ι] (R : ℝ) (hR : 0 ≤ R) (e : ι → ℕ) :
    ∫ z in simplexF ι R, ∏ i, z i ^ e i = momentF ι R e :=
  sorry

/-- **Zero-dimensional simplex**: over an empty index type the simplex is the point `ℝ⁰`, of measure one. -/
theorem simplexF_integral_isEmpty {ι : Type*} [Fintype ι] [IsEmpty ι] (R : ℝ) (hR : 0 ≤ R) (e : ι → ℕ) :
    ∫ z in simplexF ι R, ∏ i, z i ^ e i = 1 :=
  sorry

/-- **Weighted simplex moment**: `∫_{simplexF ι c} zᵉ (c − Σ z)^p = c^{|ι| + Σe + p} ∏ eᵢ! p! / (|ι| + Σe + p)!` (from (10.1) on `ι ⊕ Unit` and Fubini). -/
theorem weighted_simplexF {ι : Type*} [Fintype ι] (c : ℝ) (hc : 0 ≤ c) (e : ι → ℕ) (p : ℕ) :
    ∫ z in simplexF ι c, (∏ i, z i ^ e i) * (c - ∑ i, z i) ^ p =
      c ^ (Fintype.card ι + ∑ i, e i + p) * (∏ i, ((e i).factorial : ℝ)) *
        (p.factorial : ℝ) / ((Fintype.card ι + ∑ i, e i + p).factorial : ℝ) :=
  sorry

/-- **Stratification and inclusion–exclusion, pointwise**: the indicator of the support is the signed sum, over rough sets `R` and `K ⊆ Rᶜ`, of the indicators of the pieces `Qset R K` (no null sets are discarded at this step). -/
theorem indicator_supportT {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (F : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    (supportT N g L C).indicator F x =
      ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * (Qset g L C R K).indicator F x :=
  sorry

/-- **Translation**: for `g ≥ 0` and disjoint `R`, `K`, the piece `Qset R K` becomes, after `x = y + g·1_{R∪K}`, the closed piece `pieceSet R (C|R| − |R|g) (L − (|R| + |K|)g)` up to the null faces `yᵢ = 0`. -/
theorem integral_Qset {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (R K : Finset (Fin N)) (hRK : Disjoint R K) (F : (Fin N → ℝ) → ℝ) :
    ∫ x, (Qset g L C R K).indicator F x =
      ∫ y in pieceSet N R (C R.card - R.card * g) (L - (R.card + K.card) * g),
        F (y + shiftV g (R ∪ K)) :=
  sorry

/-- Pieces with a negative cap or radius are empty. -/
theorem pieceSet_empty (N : ℕ) (R : Finset (Fin N)) (c M : ℝ) (h : ¬(0 ≤ c ∧ 0 ≤ M)) :
    pieceSet N R c M = ∅ :=
  sorry

/-- **Two-group Dirichlet, distinguished coordinate rough** (`a ∈ R`): Fubini over `(y|_R, y|_{Rᶜ})`, (10.1) on each block. -/
theorem piece_integral_mem (N : ℕ) (R : Finset (Fin N)) (a : Fin N) (ha : a ∈ R) (t p : ℕ) (c M : ℝ) :
    ∫ y in pieceSet N R c M, y a ^ t * (M - ∑ i, y i) ^ p =
      twoGroup (N - R.card) R.card t 0 p c M :=
  sorry

/-- **Two-group Dirichlet, distinguished coordinate smooth** (`a ∉ R`). -/
theorem piece_integral_notMem (N : ℕ) (R : Finset (Fin N)) (a : Fin N) (ha : a ∉ R) (t p : ℕ) (c M : ℝ) :
    ∫ y in pieceSet N R c M, y a ^ t * (M - ∑ i, y i) ^ p =
      twoGroup (N - R.card) R.card 0 t p c M :=
  sorry

/-- **Boundary `R = ∅`**: the rough block is `ℝ⁰`; the piece is the full simplex of radius `M`. -/
theorem piece_integral_empty (N : ℕ) (a : Fin N) (t p : ℕ) (c M : ℝ) (hc : 0 ≤ c) (hM : 0 ≤ M) :
    ∫ y in pieceSet N ∅ c M, y a ^ t * (M - ∑ i, y i) ^ p =
      M ^ (N + t + p) * (t.factorial : ℝ) * (p.factorial : ℝ) / ((N + t + p).factorial : ℝ) :=
  sorry

/-- **Boundary `R = univ`**: the complement block is `ℝ⁰`. -/
theorem piece_integral_univ (N : ℕ) (a : Fin N) (t p : ℕ) (c M : ℝ) :
    ∫ y in pieceSet N Finset.univ c M, y a ^ t * (M - ∑ i, y i) ^ p =
      twoGroup 0 N t 0 p c M :=
  sorry

/-- **Boundary `N = 0`**: in `ℝ⁰` the support is everything or nothing. -/
theorem supportT_zero_dim (g L : ℝ) (C : ℕ → ℝ) :
    supportT 0 g L C = {_x | 0 ≤ L ∧ 0 ≤ C 0} :=
  sorry

/-- **Boundary `N = 0`**, integrated. -/
theorem integral_supportT_zero_dim (g L : ℝ) (C : ℕ → ℝ) (p : ℕ) :
    ∫ x in supportT 0 g L C, (L - ∑ i, x i) ^ p = if 0 ≤ L ∧ 0 ≤ C 0 then L ^ p else 0 :=
  sorry

/-- **Counting**: a signed sum over rough sets `R` and `K ⊆ Rᶜ` whose terms depend only on `|R|`, `|K|` and the position of a coordinate `a` groups into binomial multiplicities. -/
theorem count_pieces (N : ℕ) (a : Fin N) (Hin Hk Hout : ℕ → ℕ → ℝ) :
    ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card *
        (if a ∈ R then Hin R.card K.card else if a ∈ K then Hk R.card K.card else Hout R.card K.card) =
      ∑ r ∈ Finset.range (N - 1 + 1), ((N - 1).choose r : ℝ) *
        ∑ k ∈ Finset.range (N - 1 - r + 1), ((N - 1 - r).choose k : ℝ) *
          ((-1 : ℝ) ^ k * Hin (r + 1) k + (-1 : ℝ) ^ k * Hout r k - (-1 : ℝ) ^ k * Hk r (k + 1)) :=
  sorry

/-- **Proposition 10.2 for `(L − Σ x)^p x_a^e`**: the integral over the support equals the closed form, for every `N`, `g ≥ 0`, `L`, cap function `C` and coordinate `a`. -/
theorem integral_supportT (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (a : Fin N) (e p : ℕ) :
    ∫ x in supportT N g L C, (L - ∑ i, x i) ^ p * x a ^ e = gramFormula N g L C e p :=
  sorry

/-- Smaller caps give a smaller support (the two-cap datum of Lemma 9.1's proof lies inside Table 3's). -/
theorem supportT_mono (N : ℕ) (g L : ℝ) (C C' : ℕ → ℝ) (h : ∀ m, C' m ≤ C m) :
    supportT N g L C' ⊆ supportT N g L C :=
  sorry

/-- **The Gram entry `∫_{T̃} (L − P₁) P₂`** for every `N`, `g ≥ 0`, `L` and cap function `C`. -/
theorem gram_entry_integral_general (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) :
    ∫ x in supportT N g L C, (L - ∑ i, x i) * ∑ i, x i ^ 2 = N * gramFormula N g L C 2 1 :=
  sorry

/-- The closed form commutes with `ℚ → ℝ`. -/
theorem gramFormula_ratCast (N : ℕ) (g L : ℚ) (C : ℕ → ℚ) (e p : ℕ) :
    ((gramFormula N g L C e p : ℚ) : ℝ) = gramFormula N (g : ℝ) (L : ℝ) (fun m => (C m : ℝ)) e p :=
  sorry

/-- **Computational certificate**: the closed form at Table 3, evaluated by the kernel row by row. -/
theorem gramEntryQ_eq :
    gramEntryQ = (56548202531757829081112222776094322482195301797337957431658942826121654659702465348240408258861490443138056811762103934848460333484729132412243771531 /
          475777117431212313155109340694822167006580726288213730520562203252425237214040532052194976131431758403778076171875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) :=
  sorry

/-- **The Table 3 Gram entry as a Lebesgue integral**: `I_T[(1, ∅), (0, (2))] = ∫_{T̃} (L − P₁) P₂ dx = gramEntryQ` over the rescaled support with Table 3's caps. -/
theorem gram_entry_integral :
    ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ)),
      ((53 / 50 : ℝ) - ∑ i, x i) * ∑ i, x i ^ 2 = (gramEntryQ : ℝ) :=
  sorry

/-- The same integral with the value written out (V2a's `entry_45`). -/
theorem gram_entry_integral_value :
    ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ)),
      ((53 / 50 : ℝ) - ∑ i, x i) * ∑ i, x i ^ 2 = ((56548202531757829081112222776094322482195301797337957431658942826121654659702465348240408258861490443138056811762103934848460333484729132412243771531 /
          475777117431212313155109340694822167006580726288213730520562203252425237214040532052194976131431758403778076171875000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) :=
  sorry

/-- **The entry in V0's basis of `B₂₁`**: `∫_{T̃} gen 1 ∅ · gen 0 {2}`, the generators evaluated at `x`. -/
theorem gram_entry_B21 :
    ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ)),
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 1 0) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}) = (gramEntryQ : ℝ) :=
  sorry

end BGP212.Challenge
