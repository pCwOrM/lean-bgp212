# V2e roadmap: from the aggregate Dirichlet theorem to `J_T` Gram entries

Status:
- **V2e-A is proved** (sixteenth pair, `Solution/Aggregate.lean`).
- **V2e-B is proved** (seventeenth pair, `Solution/CapCell.lean`): the cap branch, see §3.
- This file is the plan for V2f.
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

## 2. The cells of one piece (kernel-checked in V2e-B; first verified exactly at 20 000 random points)

Fix a piece `(R, K)` with `r = |R|` and `k = |K|`. The branches of `U` switch along three lines in the `(u₁, u₂)` plane:

| switch | line | type |
|---|---|---|
| `max`: `g` vs `C(r+1) − ρ₁` | `u₁ = c₁ := C(r+1) − (r+1) g` | vertical |
| `min`, cap side (`u₁ ≤ c₁`): `L − S` vs `C(r+1) − ρ₁` | `u₂ = c₂ := L − k g − C(r+1)` | horizontal (`u₁` cancels) |
| `min`, `g` side (`u₁ ≥ c₁`): `L − S` vs `g` | `u₁ + u₂ = c₃ := L − (r+k+1) g` | anti-diagonal |

The four branch lemmas `endpointAgg_cap`, `endpointAgg_gBranch`, `endpointAgg_LBranch_cap` and `endpointAgg_LBranch_g` (V2e-B) prove this classification.

On each cell `U` is affine, with three possible values:
- `L − (r+k) g − u₁ − u₂`;
- `C(r+1) − r g − u₁`;
- `g`.

The support constraints of `T̂ = supportT 44 g τ C` (V2d's `hatSupport_eq`) on the piece are:
- `u₁ + u₂ ≤ τ − (r+k) g`;
- `u₁ ≤ C(r) − r g`.

These lines are of the same three types. So every cell is a polygon bounded by vertical, horizontal and anti-diagonal lines with rational offsets.

Every cell integral is therefore an iterated one-variable polynomial integral with rational limits, the shape of `tri_cut`.

## 3. V2e-B: the cap branch (done)

**Cells.** `boxTri A B D = {0 ≤ u₁ ≤ A, 0 ≤ u₂ ≤ B, u₁ + u₂ ≤ D}`.
- `box_monomial` gives `∫_{boxTri} u₁^α u₂^β = boxVal A B D α β` exactly.
  - `boxVal` splits `[0, A]` at `E = max 0 (min A (D − B))` and `F = max 0 (min A D)`.
  - It is computable over `ℚ`, and `boxVal_cast` transports it to `ℝ`.
- `box_capPow` handles the cap power `(a − u₁)^m`, and `box_poly` any `P ∈ ℚ[u₁, u₂]`.
- Boundary cases:
  - `boxVal_empty`: `A < 0` or `B < 0`;
  - `boxVal_nonpos`: `D ≤ 0`;
  - `boxVal_rect`: `A + B ≤ D`.
- Independent check: polygon clipping, at 300 random cells and in the controls.

**The cap cell.** `capCell = boxTri (min c c₁) c₂ M`, where `c` and `M` are the piece cap and total.
- `endpointAgg_on_capCell`: on it, `U = C(r+1) − r g − u₁`.
- `cap_inner`: the inner integral `∫₀^U (L − S − u)^p u^t du` there is an explicit polynomial in `(u₁, u₂)`.

**Piece integrals.**
- `cap_branch_piece`: `∫_{piece} yᵗ 1_cap U^m` in closed form, through `two_group_fin`.
- `cap_branch_r0`: the stratum with no rough coordinates, through `one_group`.
- `piece_cap_eq`: the piece constraints are automatic on the cell.

**Findings.**
- **The τ constraint is inactive on the cap branch.**
  - There `g ≤ U ≤ L − S`, so `S ≤ L − g` (`cap_total_le`).
  - At Table 3, `τ − (L − g) = 1/625 > 0` (`tau_ge_table3`).
  - So every Table 3 cap cell is a rectangle `[0, A] × [0, B]` (`capCell_rect_table3`).
- **Few nonempty cap cells (exploratory, exact enumeration).** At Table 3, the cap cell is nonempty only for 59 cardinality classes `(r, k)`:
  - `r ≤ 12`;
  - `k ≤ 6`, with `k ≤ 2` once `r ≥ 9`.

  For `r = 1` it is empty from `k = 7` on (`capCell_empty_table3`).
- **Certificate.** `capPieceT3_value` gives the cap-branch part of `J_T(1)` on the piece `({0}, ∅)` as:

  ```text
  (L − C(2))⁴³ ((C(2) − g)³ − g³) / (3 · 43!) ≈ 1.0464 × 10⁻⁷⁰
  ```

  It is kernel-checked, and a direct 3-dimensional grid integration of the analogous `N = 3` piece agrees.

## 4. V2f: all branches and `J_T` entries

1. **The other two branches as signed `boxTri` cells.** Each remaining cell is a difference of cells of the V2e-B shape, so `boxVal` covers them.

   With `A' = min c (C(r) − r g)`:
   - **`g` branch** (`U = g`): the cell is `{c₁ ≤ u₁ ≤ A', u₁ + u₂ ≤ min(c₃, M)}`, which equals:

     ```text
     boxTri A' ∞ (min c₃ M) − boxTri (min c₁ A') ∞ (min c₃ M)
     ```

     Here `∞` means any `B ≥ M`. Each lower bound is clamped, as in `min c₁ A'`, so that an empty cell contributes 0, not a negative difference.
   - **`L − S` branch, cap side:** `{u₁ ≤ min(A', c₁), u₂ ≥ c₂, u₁ + u₂ ≤ M}` is a full-height cell minus the cap cell.
   - **`L − S` branch, `g` side:** `{c₁ ≤ u₁ ≤ A', c₃ ≤ u₁ + u₂ ≤ M}` is a difference of four cells.

   On both sides of the `L − S` branch, lower bounds are clamped the same way (`min c₁ A'`, `min c₂ M`). This branch is where the τ constraint (`D = M`) is active.
2. **The `J_T` integrand.** For generators `(L − S − u)^a ∏_q (P̂_q + u^q)`, `inner_integral` turns `∫₀^U F` into a polynomial in:
   - `U`;
   - `L − S`;
   - power sums of `x̂`.

   After the translation and V2c's placements, each term is `yᵗ` times a polynomial in `(u₁, u₂)` on each cell. `two_group_fin` and `box_poly` then give exact rationals.
3. **Counting.** Use V2c's `Sig`, `sig_union` and `sig_card` over the 44 outer coordinates, with the cell data indexed by `(r, k)`.
   - Only the 59 cap classes above, and the analogous lists for the other branches, contribute.
   - Symmetry gives the factor 45 (V2d's `marginal_agrees`).
4. **One `J_T` Gram entry at Table 3,** as an exact rational with a small kernel certificate. Then certify `J_T(P⋆) − 4 I_T(P⋆)` directly; the 846 × 846 matrix stays uncertified.

## 5. Costs observed in V2e-A and V2e-B

- **Elaboration:** `Solution/Aggregate.lean` elaborates in about 6 s, with a 3.15 GB peak, which is mostly the import baseline.
- **New Mathlib modules:** none.
- **Kernel arithmetic:** none beyond the worked example's small constants (`decide +kernel` on four `ℚ`/`ℕ` values).
- **V2e-B:**
  - `Solution/CapCell.lean` elaborates in about 5 s, peaking at 3.19 GB.
  - The Comparator suite takes about 115 s, peaking at 3.16 GB.
  - Kernel arithmetic is only the certificate's `capPowVal` and a few small constants.
