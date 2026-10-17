# BGP212

Specification layer and Lean verification artifacts for the exact and combinatorial
parts of Axiom Math's *A New Bound for Small Gaps Between Primes* (H₁ ≤ 212,
preliminary draft of September 3, 2026).

## Scope

This repository verifies the exact and combinatorial layer of the H₁ ≤ 212 deduction.
The analytic estimates (Type I/II/III, Bombieri–Vinogradov, the Harman decomposition)
and the variational certificate stay imported as hypotheses, matching the boundary of
Axiom's own Lean certificate. The priorities are kernel verification and exact
theorem-to-source correspondence.

## Two tracks

- **Track A — specification audit.** `specs/A0_parameters.yaml` fixes Table 3 as the
  specification of record and records two source inconsistencies verbatim (SI-1, SI-2)
  plus one editorial note (ED-1). Lean statements are formalized against A0.
- **Track B — multi-shift GDT.** `specs/B0_multishift_gdt.yaml` extends the General
  Divisor Theorem (github.com/thinkthoughts/general-divisor-theorem, v1.0.0) from one
  shift to a tuple H, with absolute density (1/m)·∏_{p | R}(1 − ν_p(H)/p).

The tracks join at Lemma 12.1: admissibility of H₄₅ equals positivity of every local factor.

## Formal Challenge

The first Challenge/Solution pair is Lemma 12.1 (`Challenge/Lemma12_1.lean`,
`Solution/Lemma12_1.lean`), in core Lean with no Mathlib dependency. Five statements:

1. `h45_card` — 45 distinct elements
2. `h45_diameter` — minimum 0, maximum 212
3. `h45_omitted_table` — the source's listed omitted classes for p ≤ 43
4. `h45_admissible` — an omitted class modulo every prime
5. `lemma_12_1` — the packaged lemma

## Comparator Verification

```text
./verify.sh
```

builds the project and runs Lean Comparator on `Comparator/lemma_12_1.json`.
A successful run ends with:

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

Axioms used: `propext`, `Quot.sound`. The record of the first run, including its
sandbox note and negative control, is `specs/results/A1_lemma_12_1.yaml`.

## Source

Place Axiom Math's PDF at `Source/bgp212.pdf` (kept outside version control). sha256 `2b307ae26046dffd2153fe7466e5a9a302976dc3ba5142151a8a8104a37b3d80`.
