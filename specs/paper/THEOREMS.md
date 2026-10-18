# Theorem Inventory

**Working paper:** *Exact Rational Integration over Constrained Simplices*  
**Project:** [translatepi.ai](https://translatepi.ai/) · [Lean repository](https://github.com/thinkthoughts/lean-bgp212)  
**Baseline:** V2d, provenance commit [`90055db`](https://github.com/thinkthoughts/lean-bgp212/commit/90055db); proof commit `52fd36a`.  
**Verification:** 15/15 Comparator suites accepted on the VPS; V2d: four positive controls accepted and four negative controls rejected.  
**Purpose:** Inventory the central mathematical statements for the paper, with source locations and explicit scope. These are independent formalization results motivated by the bounded-prime-gap argument; the unconditional bound is not claimed here.

## 1. Exact simplex moments

**Lean:** `simplex_integral` — `Solution/SimplexMoment.lean:160`  
**Definitions:** `simplex`, `momentR` — `BGP212/SimplexMoment.lean`

For `m : ℕ`, `R : ℝ`, `e : Fin m → ℕ`, and `0 ≤ R`, the simplex

$$
\Delta_m(R)=\{x\in\mathbb R^m:x_i\ge0,\ \sum_i x_i\le R\}
$$

satisfies

$$
\int_{\Delta_m(R)}\prod_{i=1}^m x_i^{e_i}\,dx
=\frac{R^{m+\sum_i e_i}\prod_i e_i!}{(m+\sum_i e_i)!}.
$$

The Lean statement identifies the integral with `momentR m R e`; the displayed closed form follows from that definition. The development includes dimension-zero, negative-radius, zero-radius, volume, and rational-polynomial cases (`poly_integral`, `Solution/SimplexMoment.lean:237`).

## 2. The polynomial basis B₂₁

**Lean:** `genIdx_linearIndependent`, `finrank_B21` — `Solution/Variational.lean:398,410`  
**Definitions:** `gen`, `genIdx`, `B21`, `B21Idx` — `BGP212/Variational.lean`

The indexed generators `genIdx : B21Idx → Poly` are linearly independent over `ℚ`, and

$$
\dim_{\mathbb Q}(B_{21})=846.
$$

The proof combines an injective exponent encoding, independence of distinct monomials, and injectivity of polynomial transformations. The rank theorem uses `B21_eq_span` and `card_B21Idx`. **Scope:** dimension of the specified rational polynomial subspace, not a claim about every polynomial on 45 variables.

## 3. General monomial integration over constrained support

**Lean:** `integral_supportT_gen` — `Solution/GramGeneral.lean:344`  
**Definitions:** `supportT` — `BGP212/GramEntry.lean`; `gramGen` — `BGP212/GramGeneral.lean`

For arbitrary `N : ℕ`, `g L : ℝ`, `C : ℕ → ℝ`, `e : Fin N → ℕ`, `p : ℕ`, and **`0 ≤ g`**,

$$
\int_{\mathrm{supportT}(N,g,L,C)}
 (L-\sum_i x_i)^p\prod_i x_i^{e_i}\,dx
=\mathrm{gramGen}(N,g,L,C,e,p).
$$

The right side is an explicit finite closed-form expression defined in Lean. It uses rough-set decomposition, inclusion–exclusion, group integrals, and the placement-counting identities `sig_insert`, `sig_union`, and `sig_card`. No specific Table 3 cap function is required for the general theorem.

**Related:** `gramGen_extend` (`Solution/GramGeneral.lean:667`) reduces evaluation to the coordinates with nonzero exponents. This reduction is proved; it does not assert that computing all Gram entries is inexpensive.

## 4. Explicit rational Gram representation

**Lean:** `gram_entry_B21_rat` — `Solution/GramGeneral.lean:522`  
**Related:** `gram_entry_gen_list`, `gram_entry_example`, `gram_entry_example_value` — `Solution/GramGeneral.lean:496,753,821`

For all `i j : BGP212.Var.B21Idx`, the integral of the product of the corresponding polynomial generators over the **Table 3, 45-coordinate** constrained support equals the real cast of an explicit finite sum of rational `gramGen` expressions:

$$
\int_{T} \mathrm{eval}(\mathrm{genIdx}(i))
\mathrm{eval}(\mathrm{genIdx}(j))\,dx
=\left(\sum_{\varphi}\mathrm{gramGen}_{\mathbb Q}(\mathrm{expo}(\varphi),i.a+j.a)\right)_{\mathbb R}.
$$

The sum runs over placements of the combined power-sum parts into the 45 coordinates, as specified by the Lean theorem. This is **an exact rational representation for each entry**, not a generated or certified full 846 × 846 matrix. A worked example has an exact rational certificate.

## 5. Marginal-fibre equivalence

**Lean:** `fibre_equiv` — `Solution/Fibre.lean:115`  
**Definitions:** `hatSupport`, `endpoint`, `roughCount`, `roughMass` — `BGP212/Fibre.lean`

For `n : ℕ`, `g L τ : ℝ`, `C : ℕ → ℝ`, **`0 ≤ g`**, **`τ ≤ L`**, `x ∈ hatSupport n g τ C`, and any `u : ℝ`,

$$
\mathrm{Fin.snoc}(x,u)\in\mathrm{supportT}(n+1,g,L,C)
\iff 0\le u\le U(x),
$$

where

$$
U(x)=\min\bigl(L-\sum_i x_i,\ \max(g,C(s+1)-\rho_1)\bigr),
$$

with `s = roughCount g x` and `ρ₁ = roughMass g x`.

**Related:** `empty_fibre_neg` and `empty_fibre_cap` (`Solution/Fibre.lean:136,151`) address empty fibres. The cap-violation case additionally requires `CapStep g C` for indices `m ≥ 1` and `0 ≤ C 0`. The Table 3 cap-step facts are separately proved; no zero-to-one cap-step assumption is introduced.

## 6. Marginal identity and inner polynomial integral

**Lean:** `marginal_agrees`, `inner_integral` — `Solution/Fibre.lean:217,240`  
**Definitions:** `marginalJ`, `jT` — `BGP212/Fibre.lean`

For `0 ≤ g`, `τ ≤ L`, `CapStep g C`, `0 ≤ C 0`, and continuous `P : (Fin (n+1) → ℝ) → ℝ`, Lean proves

$$
\mathrm{marginalJ}(n,g,L,\tau,C,P)=jT(n,g,L,\tau,C,P).
$$

For arbitrary `U M : ℝ` and `p t : ℕ`, Lean also proves the interval-integral identity

$$
\int_0^U(M-u)^p u^t\,du
=\sum_{j=0}^{p}\binom pj M^{p-j}(-1)^j\frac{U^{t+j+1}}{t+j+1}.
$$

This proves the geometry-to-marginal bridge and the inner polynomial integration step. It **does not yet** compute general `J_T` Gram entries.

## Formal verification and provenance

- **Source:** [`thinkthoughts/lean-bgp212`](https://github.com/thinkthoughts/lean-bgp212)
- **Proof commit for V2d:** `52fd36a`; **VPS verification/provenance commit:** `90055db`.
- **Toolchain:** Lean `v4.34.0-rc2`; mathlib pinned at `85e3a25` (see repository result YAML files).
- **VPS:** 15/15 Comparator suites accepted. For V2d, four positive controls accepted, four negative controls rejected with unsolved-goal proof diagnostics.
- **Trusted axioms reported for V2d:** `propext`, `Quot.sound`, `Classical.choice`.
- **Result records:** [`specs/results`](https://github.com/thinkthoughts/lean-bgp212/tree/main/specs/results).

## Beyond the current theorems

The following are **outstanding**, not conclusions of this inventory:

1. Aggregate Dirichlet integration and piecewise endpoint branch geometry for general `J_T` evaluation (V2e/V2f).
2. Exact optimized polynomial coefficient data and direct positivity certificates.
3. Remaining analytic/variational hypotheses needed for `DHL[45,2]`.

The project has formally verified the **conditional implication** `DHL[45,2] → H₁ ≤ 212`; it does **not** yet furnish an unconditional Lean proof of `H₁ ≤ 212`.

---

*Admissible generalizations trail leading specifications. · PiπΠ*
