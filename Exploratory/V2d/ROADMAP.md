# V2d-Spec: the `J_T` fibre geometry (Lemma 9.2) and the road to the `J_T` bridge

Status: **exploratory specification**, on branch `v2d-spec` from `08e5f42`.
- It adds two files under `Exploratory/V2d/`.
- No `lean_lib`, Challenge/Solution pair or Comparator suite changes.
- A0–V2c and the 14 published suites are untouched.

Check it with:

```text
lake env lean Exploratory/V2d/FibreSpec.lean
```

## 1. Geometry (paper, §9.4 and Lemma 9.2)

**Coordinates.** A point of ℝ⁴⁵ is `(x̂, u)`:
- `x̂ ∈ ℝ⁴⁴`, with `u` the last coordinate (`Fin.snoc x̂ u`);
- `S = Σ x̂ᵢ`;
- `s = #{i : x̂ᵢ > g}`;
- `ρ₁ = Σ_{x̂ᵢ > g} x̂ᵢ`.

**Sets and the endpoint.**
- `T̂ = {x̂ ≥ 0 : S ≤ τ, ρ₁ ≤ C(s)}`, where `τ = A₁ − ε` rescaled is `249/250`.
- `U(x̂) = min{L − S, max{g, C(s+1) − ρ₁}}`.

**The functional.**
- `J_T(F) = 45 ∫_{T̂} (∫₀^{U(x̂)} F(x̂, u) du)² dx̂`.
- For symmetric `F`, this is `k = 45` times Definition 4.6's single marginal, which is B3's finding F3.

**Fibre theorem.**
- For `x̂ ∈ T̂`: `(x̂, u) ∈ T̃ ⇔ 0 ≤ u ≤ U(x̂)`.
  - When `u ≤ g`, the rough set of `(x̂, u)` is that of `x̂`, and `ρ₁ ≤ C(s)` holds.
  - When `u > g`, the count becomes `s + 1` and the mass `ρ₁ + u`.
  - Intersecting with `S + u ≤ L` gives the minimum.
  - This direction is exact: no null sets and no cap-step hypothesis.
- **Empty-fibre cases** (needed for Definition 4.6's form):
  - If some `x̂ᵢ < 0`, the fibre is empty.
  - If `ρ₁ > C(s)`, no `u` completes `x̂`:
    - `u ≤ g` keeps the violated cap;
    - `u > g` adds more than `g` to the mass while the cap grows by at most `g`.
  - This second case is where the **cap-step hypothesis** enters.

## 2. Finding: the cap step holds from `m = 1`, not from `m = 0`

Table 3 has `C(0) = 0` and `C(1) = 777/1250`, so `C(1) > C(0) + g`. This is `capStep_zero_fails_table3`, proved.

Definition 4.1 imposes `B_{m+1} ≤ B_m + δ` only "whenever both sides are defined", that is, from `m = 1`. The empty-fibre argument needs nothing more:
- with `s = 0` the rough mass is `0`, so `ρ₁ > C(0)` is impossible once `C(0) ≥ 0`;
- with `s ≥ 1` the step from `s` applies.

The specification therefore states:
- `CapStep g C := ∀ m ≥ 1, C(m+1) ≤ C(m) + g`;
- and separately `0 ≤ C 0`.

Both are proved at Table 3. The tightest step is `C(3) − C(2) = 81/1250 < g = 82/1250`.

## 3. What the patch contains

| kind | name | content |
|---|---|---|
| **definition** | `roughCount`, `roughMass` | `s(x̂)`, `ρ₁(x̂)` (via V2b's `roughSet`) |
| **definition** | `hatSupport n g τ C` | `T̂` |
| **definition** | `endpoint g L C x̂` | `U(x̂)` |
| **definition** | `CapStep g C` | `∀ m ≥ 1, C(m+1) ≤ C(m) + g` |
| **definition** | `marginalJ n g L τ C F` | Definition 4.6's marginal of `F` supported on `T̃` (indicator form, cutoff `S ≤ τ`), times `k = n + 1` |
| **definition** | `jT n g L τ C F` | §9.4's `J_T` (integral over `T̂` of the squared fibre integral `∫₀^U`) |
| **statement** (type-checked, unproved) | `FibreEquiv` | Lemma 9.2: fibre `= [0, U]` on `T̂` (cap-parametric; `0 ≤ g`, `τ ≤ L`) |
| **statement** | `EmptyFibreCap` | `ρ₁ > C(s)` ⇒ empty fibre (`CapStep`, `0 ≤ C 0`) |
| **statement** | `EmptyFibreNeg` | a negative coordinate ⇒ empty fibre |
| **statement** | `MarginalAgrees` | `marginalJ (1_{T̃} P) = jT P` for continuous `P` (Theorem 11.1's `J_T(F⋆) = J_T(P⋆)`) |
| **statement** | `InnerIntegral` | `∫₀^U (M − u)^p u^t du` in closed form (first block of the bridge) |
| **statement** | `FibreEquivTable3`, `MarginalAgreesTable3` | the Table 3 instances (`N = 45`, `g`, `L`, `τ`, `C` from `BGP212.Params`) |
| **proved** | `g_nonneg`, `tau_le_L`, `C_zero_table3` | Table 3 hypotheses |
| **proved** | `capStep_table3` | `CapStep` at Table 3 (kernel `decide` for `m ≤ 9`, constant caps from `m = 10`) |
| **proved** | `capStep_zero_fails_table3` | the finding of §2 |
| **proved** | `table3_of_general` | `FibreEquiv ∧ MarginalAgrees ⇒` their Table 3 instances |

**Remaining obligations:** `FibreEquiv`, `EmptyFibreCap`, `EmptyFibreNeg`, `MarginalAgrees`, `InnerIntegral`.

Each statement was also checked by hand as true as stated, not merely well-typed:
- `FibreEquiv` does not need `τ ≤ L`, but it is kept to match the paper.
- `EmptyFibreCap` holds with no sign hypothesis on `x̂`.

## 4. Roadmap

### V2d (fifteenth pair): the fibre theorem

All of it is elementary set algebra plus one integral identity. No kernel arithmetic and no certificate are needed.

1. **`roughSet_snoc`:** `roughSet g (Fin.snoc x̂ u) = (roughSet g x̂).map castSucc ∪ (if g < u then {last} else ∅)`.
   - Corollaries: `roughCount` is `s` or `s + 1`, and `roughMass` is `ρ₁` or `ρ₁ + u`.
   - Uses `Fin.sum_univ_castSucc`, `Finset.card_map` and `Finset.sum_map`.
2. **`FibreEquiv`:** case split on `u ≤ g`, then `min`/`max` order lemmas.
3. **`EmptyFibreNeg`:** immediate.
4. **`EmptyFibreCap`:**
   - case `s = 0` via `0 ≤ C 0`;
   - case `s ≥ 1` via `CapStep` and `linarith`.
5. **`MarginalAgrees`:**
   - Show `T̂` is measurable, by the same unions as V2b's `supportT_measurableSet`.
   - Show `U(x̂) ≥ 0` on `T̂`, from `L − S ≥ L − τ ≥ 0` and `g ≥ 0`.
   - The inner integral of `1_{T̃} P` over `ℝ` equals `∫₀^U P` on `T̂` (fibre theorem plus `integral_Icc_eq_integral_Ioc` and `intervalIntegral.integral_of_le`).
   - It is `0` on `{S ≤ τ} \ T̂` (empty fibres).
   - Finish with `setIntegral_indicator`.
6. **`InnerIntegral`:** `add_pow`, `intervalIntegral.integral_finsetSum` and `integral_pow`, as in V1's Beta step.
7. **Table 3 instances:** `table3_of_general`, already proved.

**Estimate.** About the size of V2b's translation and inclusion–exclusion steps:
- no new Mathlib modules;
- seconds to elaborate;
- the Comparator suite in minutes.

The Challenge statements are the five obligations plus their Table 3 instances. The controls would be:
- **dimension 1 (`n = 0`):** the fibre is `[0, min(L, max(g, C(1)))]`, which can be checked against the definition;
- **a negative control:** `U` with `C(s)` in place of `C(s+1)`;
- **a statement-level control:** the usual altered-statement check.

### After V2d: the `J_T` integral bridge (V2e and later)

1. **Inner integral of `B₂₁` generators.**
   - The factor is `(L − S − u)^a ∏_{q ∈ λ} (P̂_q + u^q)`.
   - Its integral `∫₀^U` is a polynomial in `U`, `M = L − S` and the `P̂_q`, built from `InnerIntegral`.
   - The product of two such polynomials expands into monomials of `x̂` times powers of `U` and `M`.
2. **Cells by branch of `U`.** On a V2b/V2c piece (rough set `R`, inclusion–exclusion set `K` among the 44 coordinates), put `u₁ = Σ_R y` and `u₂ = Σ_{Rᶜ} y`. Then:
   - `S = (|R| + |K|) g + u₁ + u₂`;
   - `ρ₁ = |R| g + u₁`.

   So the three branches `U = L − S`, `U = g` and `U = C(s+1) − ρ₁` are separated by lines in the `(u₁, u₂)` plane, and every cell is a rational polygon.
3. **A Dirichlet lemma with a function of the aggregates.** For `h` continuous on the plane:
   - `∫_{piece} yᵗ h(u₁, u₂) = const · ∫∫ u₁^{r−1+A} u₂^{n−1+B} h(u₁, u₂) du₁ du₂`.
   - This generalizes V2b's `weighted_simplexF`.
   - It follows from the fibred Fubini plus a one-variable "Dirichlet with a function of the sum" lemma, proved by induction like V1's `simplex_integral`.
   - It is the main new piece of machinery.
4. **Polygon integrals.** Integrals of `u₁^a u₂^b` times affine powers over rational polygons are rational, via iterated interval integrals. The incomplete Beta forms are already available from `InnerIntegral`.
5. **Counting.** V2c's `Sig`, `sig_union` and `sig_card` over the 44 outer coordinates.
   - The placements now also track the branch of `U`.
   - Symmetry gives the factor 45 (B3's finding F3).
6. **Certificates.** Only after the symmetry-collapsed placement sums and integer arithmetic. Then certify `J_T(P⋆) − 4 I_T(P⋆)` directly; the full 846 × 846 matrix stays uncertified.

**Size.** Steps 1–5 are about two to three times V2c's proof. Step 3 is the critical path. Splitting into two verified milestones is recommended:
- V2e: the aggregate Dirichlet lemma, plus the cells for one branch;
- V2f: all three branches and the counting.

## 5. Dependencies and costs of this patch

- **Imports:** `BGP212.GramEntry` (V2b's `supportT` and `roughSet`) and `BGP212.Params`.
- **Mathlib:** no new modules; interval integrals are already in the build.
- **Verification:** one `lake env lean` of `FibreSpec.lean`, about 3 s with cached imports. The memory is that of loading the imports, about 2.9 GB.
- **Not run:** no certificates, no numerical tables, and no Comparator suites.

Admissible generalizations trail leading specifications.
