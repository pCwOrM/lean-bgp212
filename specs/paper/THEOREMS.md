# Theorem Inventory

**Working paper:** *Exact Rational Integration over Constrained Simplices*  
**Project:** [translatepi.ai](https://translatepi.ai/) · [Lean repository](https://github.com/thinkthoughts/lean-bgp212)  
**Baseline:** V2e-A, proof commit [`01644e6`](https://github.com/thinkthoughts/lean-bgp212/commit/01644e6); VPS verification/provenance commit [`38606c0`](https://github.com/thinkthoughts/lean-bgp212/commit/38606c0).  
**Verification:** 16/16 Comparator suites accepted on the VPS; V2e-A: five positive controls accepted and four negative controls rejected.  
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

## 7. Two-aggregate Dirichlet integration (V2e-A)

**Lean:** `two_group`, `two_group_fin`, `two_group_poly` — `Solution/Aggregate.lean`  
**Related:** `one_group`, `tri_cut`, `aggR_shift`, `aggS_shift`, `stratumEndpoint_shift` — `Solution/Aggregate.lean`  
**Definitions:** `aggExp`, `aggConst`, `endpointAgg` — `BGP212/Aggregate.lean`

Partition the `N` coordinates into a nonempty group `R` and a nonempty complement `Rᶜ`. For an exponent vector `t : Fin N → ℕ`, define

$$
\alpha_R=|R|+\sum_{i\in R}t_i-1,\qquad
A_R=\frac{\prod_{i\in R}t_i!}{\alpha_R!}.
$$

with analogous definitions for `Rᶜ`. Let `u₁ = ∑_{i ∈ R} yᵢ` and `u₂ = ∑_{i ∈ Rᶜ} yᵢ`. For a measurable function `h : ℝ × ℝ → ℝ` bounded in absolute value on the aggregate triangle, `two_group_fin` establishes

$$
\int_{\Delta_N(M)}\left(\prod_i y_i^{t_i}\right)h(u_1,u_2)\,dy
=A_R A_{R^c}\int_{\Delta_2(M)}
v_1^{\alpha_R}v_2^{\alpha_{R^c}}h(v_1,v_2)\,dv_1\,dv_2.
$$

Here `v₁, v₂` are integration variables on the two-dimensional triangle; `M` is the real simplex radius. The proof uses Fubini and the one-group weighted simplex identity. **Scope:** both groups must be nonempty for this main identity; separately proved boundary theorems handle one or both groups empty, while `tri_eq_empty` and `quad_eq_empty` address negative radii.

**Exact rational specialization:** `tri_poly` and `two_group_poly` evaluate polynomial aggregate weights in rational arithmetic. `two_group_const` recovers the simplex-moment formula when `h = 1`.

**Worked certificate:** `example_value` evaluates the integral of `y₀ y₂²` over the three-coordinate simplex of radius `1`, restricted by `y₀ ≤ 1/2`, as **`19/7680`**. The controls independently compare that value with the uncut integral `1/360` and reject the incorrect aggregate exponent obtained by dropping the `−1`.

**Endpoint bridge:** On a translated stratum `x = y + g·1_{R∪K}`, the proven shifts express rough mass and remaining mass in terms of `u₁,u₂`. The theorem `stratumEndpoint_shift` expresses the fibre endpoint as

$$
U=\min\bigl(L-(r+k)g-u_1-u_2,\ \max(g,C(r+1)-rg-u_1)\bigr),
$$

where `r = |R|` and `k = |K|`. The cap index comes from the **stratum `R`**, rather than the translated point's rough set `R ∪ K`. A Table 3 control distinguishes the correct stratum endpoint `587/1250` from the union-based value `461/1250`.

`tri_cut` supplies an exact closed form for an aggregate triangle cut by one coordinate threshold. This prepares the polygon-cell integrations of V2e-B; **general `J_T` Gram entries and positivity certificates are not yet proved**.

## Formal verification and provenance

- **Source:** [`thinkthoughts/lean-bgp212`](https://github.com/thinkthoughts/lean-bgp212)
- **V2d:** proof commit `52fd36a`; provenance commit `90055db`.
- **V2e-A:** [proof commit `01644e6`](https://github.com/thinkthoughts/lean-bgp212/commit/01644e6); [VPS provenance commit `38606c0`](https://github.com/thinkthoughts/lean-bgp212/commit/38606c0).
- **Toolchain:** Lean `v4.34.0-rc2`; mathlib pinned at `85e3a25` (see repository result YAML files).
- **VPS:** 16/16 Comparator suites accepted. V2d: four positive controls accepted and four negative controls rejected; V2e-A: five positive controls accepted and four negative controls rejected.
- **Trusted axioms reported for V2d and V2e-A:** `propext`, `Quot.sound`, `Classical.choice`.
- **Result records:** [`specs/results`](https://github.com/thinkthoughts/lean-bgp212/tree/main/specs/results).

## Beyond the current theorems

The following are **outstanding**, not conclusions of this inventory:

1. Polygon-cell integration for the endpoint branches and general `J_T` evaluation (V2e-B/V2f). The two-aggregate Dirichlet identity (V2e-A) is proved.
2. Exact optimized polynomial coefficient data and direct positivity certificates.
3. Remaining analytic/variational hypotheses needed for `DHL[45,2]`.

The project has formally verified the **conditional implication** `DHL[45,2] → H₁ ≤ 212`; it does **not** yet furnish an unconditional Lean proof of `H₁ ≤ 212`.

---

*Admissible generalizations trail leading specifications. · PiπΠ*
