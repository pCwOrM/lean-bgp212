# V2e roadmap: from the aggregate Dirichlet theorem to `J_T` Gram entries

Status:
- **V2e-A is proved** (sixteenth pair, `Solution/Aggregate.lean`).
- This file is the plan for V2e-B and V2f.
- Statements marked *exploratory* were checked numerically, not in the kernel.

## 1. What V2e-A provides (kernel-checked)

**Dirichlet exponent and constant.**
- `aggExp ι e = |ι| + Σ e − 1`.
- `aggConst ι e = ∏ eᵢ! / (aggExp ι e)!`.

**The two-aggregate identity, `two_group_fin`.** For a rough set `R` with `R` and `Rᶜ` nonempty, and `h` measurable and bounded on the triangle:

```text
∫_{y ≥ 0, Σ y ≤ M} yᵗ h(u₁, u₂) dy = aggConst R t · aggConst Rᶜ t · ∫_{tri M} u₁^{aggExp R t} u₂^{aggExp Rᶜ t} h(u₁, u₂)
```

Here `u₁ = Σ_R y`, `u₂ = Σ_{Rᶜ} y`, and `tri M = {u₁, u₂ ≥ 0, u₁ + u₂ ≤ M}`.

**Boundary cases.**
- A single group: `one_group`.
- An empty group: `one_group_empty`, `two_group_left_empty`, `two_group_right_empty` and `two_group_both_empty`.
- Zero exponents.
- `R < 0`.

**Rational specializations.**
- `tri_poly` and `two_group_poly` give the rational value for polynomial `h`, via V1's Lemma 10.1.
- `two_group_const` shows consistency with (10.1).

**The endpoint as a function of the aggregates.**
- On V2b's translated piece `x = y + g·1_{R ∪ K}`, with `r = |R|` and `k = |K|`:
  - rough mass `ρ₁ = r g + u₁` (`aggR_shift`);
  - remaining mass `S − ρ₁ = k g + u₂` (`aggS_shift`).
- `stratumEndpoint_shift` then gives `U = endpointAgg g L C r k u₁ u₂ = min(L − (r+k)g − u₁ − u₂, max(g, C(r+1) − r g − u₁))`.
- The cap index is `r + 1`, taken from the stratum `R`.
  - The translated point's own rough set is `R ∪ K`, since the `K` coordinates are also shifted by `g`.
  - Using it gives a different endpoint. The control `nc_union` records this: 461/1250 instead of 587/1250 at Table 3.
  - `endpoint_eq_stratum` identifies the two on the stratum itself.

**Prototype of a branch integral.**
- `tri_cut` integrates `u₁^α u₂^β` over the triangle cut by `u₁ ≤ c`.
- It is closed-form, via V2d's `inner_integral`.

## 2. The cells of one piece (exploratory, verified exactly at 20 000 random points)

Fix a piece `(R, K)` with `r = |R|` and `k = |K|`. The branches of `U` switch along three lines in the `(u₁, u₂)` plane:

| switch | line | type |
|---|---|---|
| `max`: `g` vs `C(r+1) − ρ₁` | `u₁ = c₁ := C(r+1) − (r+1) g` | vertical |
| `min`, cap side (`u₁ ≤ c₁`): `L − S` vs `C(r+1) − ρ₁` | `u₂ = c₂ := L − k g − C(r+1)` | horizontal (`u₁` cancels) |
| `min`, `g` side (`u₁ ≥ c₁`): `L − S` vs `g` | `u₁ + u₂ = c₃ := L − (r+k+1) g` | anti-diagonal |

On each cell `U` is affine, with three possible values:
- `L − (r+k) g − u₁ − u₂`;
- `C(r+1) − r g − u₁`;
- `g`.

The support constraints of `T̂ = supportT 44 g τ C` (V2d's `hatSupport_eq`) on the piece are:
- `u₁ + u₂ ≤ τ − (r+k) g`;
- `u₁ ≤ C(r) − r g`.

These lines are of the same three types. So every cell is a polygon bounded by vertical, horizontal and anti-diagonal lines with rational offsets.

Every cell integral is therefore an iterated one-variable polynomial integral with rational limits, the shape of `tri_cut`.

## 3. V2e-B: one branch, polygon cells

1. **The `J_T` integrand on a piece.** For generators `(L − S − u)^a ∏_q (P̂_q + u^q)`, V2d's `inner_integral` makes `∫₀^U F du` a polynomial in:
   - `U`;
   - `M = L − S`;
   - power sums of `x̂`.

   Expanding the power sums and the square gives `Σ (monomial in x̂) · poly(U, M)`. After the translation `x̂ = y + g·1_{R∪K}`, the monomials become monomials in `y` times powers of `g`.

   So each term has exactly the form `yᵗ h(u₁, u₂)` of `two_group_fin`, with:

   ```text
   h = 1_cell · poly(endpointAgg, L − S)
   ```
2. **Cell integrals.** Generalize `tri_cut` to polynomial `h` and to cells cut by one vertical, one horizontal or one anti-diagonal line. Take one branch first, the cap branch `U = C(r+1) − ρ₁`, on `{u₁ ≤ c₁, u₂ ≤ c₂}`.
3. **Measurability and boundedness** of `h` are immediate: polynomials times indicators of closed half-planes, on the compact triangle.

## 4. V2f: all branches and `J_T` entries

1. **All three branches.** Sum the cells of each piece, with null boundaries handled as in V2b.
2. **Counting.** Use V2c's placement machinery (`Sig`, `sig_union`, `sig_card`) over the 44 outer coordinates. The placements now also carry the branch cells, and symmetry gives the factor 45 (V2d, `marginal_agrees`).
3. **One `J_T` Gram entry at Table 3,** as an exact rational with a small kernel certificate. Then certify `J_T(P⋆) − 4 I_T(P⋆)` directly. The full 846 × 846 matrix stays uncertified.

## 5. Costs observed in V2e-A

- **Elaboration:** `Solution/Aggregate.lean` elaborates in about 6 s, with a 3.15 GB peak, which is mostly the import baseline.
- **New Mathlib modules:** none.
- **Kernel arithmetic:** none beyond the worked example's small constants (`decide +kernel` on four `ℚ`/`ℕ` values).
