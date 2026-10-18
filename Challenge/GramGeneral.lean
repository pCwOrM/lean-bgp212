/-
Copyright (c) 2026 thinkthoughts. All rights reserved.
Released under MIT license as described in the file LICENSE.
Source: Axiom Math, "A New Bound for Small Gaps Between Primes", preliminary draft
(September 3, 2026): Lemma 9.1 (p. 41), (10.1), Lemma 10.1, Proposition 10.2 (pp. 41–42),
§11 (p. 42).
-/
import BGP212.GramGeneral
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # V2c: the general monomial integral bridge

Statements only; proofs live in `Solution/GramGeneral.lean` (integral identities) and
`Solution/GramGeneralCert.lean` (the kernel-evaluated certificate of the worked example). Objects
are defined in `BGP212/GramEntry.lean` (V2b) and `BGP212/GramGeneral.lean`. Every integral
statement keeps the cap function `C` as a parameter except the Table 3 instances at the end. -/

namespace BGP212.Challenge

open BGP212.Gram MeasureTheory

/-- **A piece, any monomial** (Fubini over `(y|_R, y|_{Rᶜ})` and V1's (10.1) on each block). -/
theorem piece_integral_general (N : ℕ) (R : Finset (Fin N)) (t : Fin N → ℕ) (p : ℕ) (c M : ℝ) :
    ∫ y in pieceSet N R c M, (∏ i, y i ^ t i) * (M - ∑ i, y i) ^ p =
      twoGroupW (N - R.card) R.card (∑ i ∈ R, t i) (∑ i ∈ Rᶜ, t i) p
        (∏ i, ((t i).factorial : ℝ)) c M :=
  sorry

/-- The integral over the support as a signed sum over rough sets `R` and `K ⊆ Rᶜ`. -/
theorem integral_supportT_unreduced_gen (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (e : Fin N → ℕ) (p : ℕ) :
    ∫ x in supportT N g L C, (L - ∑ i, x i) ^ p * ∏ i, x i ^ e i =
      ∑ R : Finset (Fin N), ∑ K ∈ Rᶜ.powerset, (-1 : ℝ) ^ K.card * pieceTermGen g L C e p R K :=
  sorry

/-- **Counting, one coordinate**: a new coordinate is rough, in `K`, or neither. -/
theorem sig_insert {N : ℕ} (U : Finset (Fin N)) (a : Fin N) (ha : a ∉ U) (G : Finset (Fin N) → Finset (Fin N) → ℝ) :
    Sig (insert a U) G = Sig U G + Sig U (fun R K => G (insert a R) K) -
      Sig U (fun R K => G R (insert a K)) :=
  sorry

/-- **Counting, placements**: the distinguished coordinates `D` split off from a disjoint pool `E`. -/
theorem sig_union {N : ℕ} (E D : Finset (Fin N)) (hDE : Disjoint D E) (G : Finset (Fin N) → Finset (Fin N) → ℝ) :
    Sig (D ∪ E) G = ∑ A ∈ D.powerset, ∑ B ∈ (D \ A).powerset,
      (-1 : ℝ) ^ B.card * Sig E (fun R K => G (A ∪ R) (B ∪ K)) :=
  sorry

/-- **Counting, multiplicities**: a signed sum depending only on `|R|`, `|K|` is binomial. -/
theorem sig_card {N : ℕ} (E : Finset (Fin N)) (φ : ℕ → ℕ → ℝ) :
    Sig E (fun R K => φ R.card K.card) =
      ∑ r ∈ Finset.range (E.card + 1), (E.card.choose r : ℝ) *
        ∑ k ∈ Finset.range (E.card - r + 1), ((E.card - r).choose k : ℝ) *
          ((-1 : ℝ) ^ k * φ r k) :=
  sorry

/-- Each piece depends on `(R, K)` only through `R ∩ D`, `K ∩ D`, `|R|`, `|K|` (`D = suppE e`). -/
theorem pieceTermGen_eq {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (e : Fin N → ℕ) (p : ℕ) (R K : Finset (Fin N)) :
    pieceTermGen g L C e p R K =
      phiGen N g L C e p (R ∩ suppE e) (K ∩ suppE e) R.card K.card :=
  sorry

/-- **Proposition 10.2 for every monomial**: for every `N`, `g ≥ 0`, `L`, cap function `C`, exponent vector `e` and weight `p`, `∫_{T̃} (L − Σ x)^p ∏ xᵢ^{eᵢ} = gramGen N g L C e p`. -/
theorem integral_supportT_gen (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (e : Fin N → ℕ) (p : ℕ) :
    ∫ x in supportT N g L C, (L - ∑ i, x i) ^ p * ∏ i, x i ^ e i = gramGen N g L C e p :=
  sorry

/-- **Boundary: no distinguished coordinates.** -/
theorem integral_supportT_gen_zero (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (p : ℕ) :
    ∫ x in supportT N g L C, (L - ∑ i, x i) ^ p = gramGen N g L C (fun _ => 0) p :=
  sorry

/-- **Symmetry**: integrals over the support do not see the order of the coordinates. -/
theorem integral_supportT_perm {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (τ : Equiv.Perm (Fin N)) (f : (Fin N → ℝ) → ℝ) :
    ∫ x in supportT N g L C, f (fun i => x (τ i)) = ∫ x in supportT N g L C, f x :=
  sorry

/-- The closed form is symmetric under permuting the exponent vector. -/
theorem gramGen_perm {N : ℕ} (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (e : Fin N → ℕ) (p : ℕ) (τ : Equiv.Perm (Fin N)) :
    gramGen N g L C (fun i => e (τ i)) p = gramGen N g L C e p :=
  sorry

/-- **Rationality**: the closed form commutes with `ℚ → ℝ`. -/
theorem gramGen_ratCast (N : ℕ) (g L : ℚ) (C : ℕ → ℚ) (e : Fin N → ℕ) (p : ℕ) :
    ((gramGen N g L C e p : ℚ) : ℝ) = gramGen N (g : ℝ) (L : ℝ) (fun m => (C m : ℝ)) e p :=
  sorry

/-- **Consistency with V2b**: one distinguished coordinate gives V2b's closed form. -/
theorem gramGen_single (N : ℕ) (g L : ℝ) (C : ℕ → ℝ) (hg : 0 ≤ g) (a : Fin N) (e p : ℕ) :
    gramGen N g L C (fun i => if i = a then e else 0) p = gramFormula N g L C e p :=
  sorry

/-- **Transport**: exponents on the image of `ι : Fin d ↪ Fin N` give the `d`-indexed closed form `gramFin` (loops of size `d`). -/
theorem gramGen_extend {K : Type*} [Field K] [LinearOrder K] {N d : ℕ} (ι : Fin d ↪ Fin N) (es : Fin d → ℕ) (hes : ∀ j, es j ≠ 0) (g L : K) (C : ℕ → K) (p : ℕ) :
    gramGen N g L C (Function.extend ι es 0) p = gramFin N d g L C es p :=
  sorry

/-- **Boundary `d = 0`** of the transport. -/
theorem gramGen_zero_eq_gramFin {K : Type*} [Field K] [LinearOrder K] (N : ℕ) (g L : K) (C : ℕ → K) (p : ℕ) :
    gramGen N g L C (fun _ => 0) p = gramFin N 0 g L C (fun j => Fin.elim0 j) p :=
  sorry

/-- A product of power sums is a sum of monomials indexed by placements of its parts. -/
theorem prod_power_sums {N : ℕ} (qs : List ℕ) (x : Fin N → ℝ) :
    (qs.map (fun q => ∑ i, x i ^ q)).prod =
      ∑ φ : Fin qs.length → Fin N, ∏ i, x i ^ expo qs φ i :=
  sorry

/-- V0's generator `(L − P₁)^a P_λ` evaluated at `x`. -/
theorem eval_gen (a : ℕ) (lam : Multiset ℕ) (x : Fin 45 → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a lam) =
      (53 / 50 - ∑ i, x i) ^ a * (lam.map (fun q => ∑ i, x i ^ q)).prod :=
  sorry

/-- **Every `I_T` entry of `B₂₁` generators in closed form** (cap function `C`, any `g ≥ 0`): a sum over placements of the parts. -/
theorem gram_entry_gen_list (g : ℝ) (hg : 0 ≤ g) (C : ℕ → ℝ) (a a' : ℕ) (qs qs' : List ℕ) :
    ∫ x in supportT 45 g (53 / 50) C,
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a ↑qs) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen a' ↑qs') =
      ∑ φ : Fin (qs ++ qs').length → Fin 45,
        gramGen 45 g (53 / 50) C (expo (qs ++ qs') φ) (a + a') :=
  sorry

/-- **Every Table 3 `I_T` entry on the 846-element basis is an explicit rational** (Proposition 10.2 for `I_T`). -/
theorem gram_entry_B21_rat (i j : BGP212.Var.B21Idx) :
    ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ)),
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.genIdx i) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.genIdx j) =
      ((∑ φ : Fin (i.lam.toList ++ j.lam.toList).length → Fin 45,
        gramGen 45 BGP212.Params.g BGP212.Params.L BGP212.Params.C
          (expo (i.lam.toList ++ j.lam.toList) φ) (i.a + j.a) : ℚ) : ℝ) :=
  sorry

/-- **Computational certificate** for the worked example (cell-by-cell kernel evaluation). -/
theorem gramExampleQ_eq :
    gramExampleQ = (137298584564364583040656350685550336257431495996990751744468934280064336098260362229316931024625739589775233656525053362941567700763204912417959573912272077 /
        25188665542194335395595466258527403622273264847539240886103567442802100740138282822244697456426365533843636512756347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) :=
  sorry

/-- **The worked example as a Lebesgue integral**: `I_T[(1, (2)), (0, (2))] = ∫_{T̃} (L − P₁) P₂² = gramExampleQ` at Table 3 (two distinguished coordinates). -/
theorem gram_entry_example :
    ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ)),
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 1 {2}) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}) = (gramExampleQ : ℝ) :=
  sorry

/-- The worked example with its value written out. -/
theorem gram_entry_example_value :
    ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (BGP212.Params.C m : ℝ)),
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 1 {2}) *
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}) =
      ((137298584564364583040656350685550336257431495996990751744468934280064336098260362229316931024625739589775233656525053362941567700763204912417959573912272077 /
        25188665542194335395595466258527403622273264847539240886103567442802100740138282822244697456426365533843636512756347656250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ) : ℝ) :=
  sorry

end BGP212.Challenge
