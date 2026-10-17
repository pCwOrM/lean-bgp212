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
  specification of record and records three source inconsistencies verbatim (SI-1, SI-2, SI-3)
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

The second pair is the Table 3 parameter layer and Appendix B (`Challenge/AppendixB.lean`,
`Solution/AppendixB.lean`, data in `BGP212/Params.lean` and `BGP212/Ledger.lean`). Its
central statement, `table6_derivation`, equates every printed left and right entry of
Table 6 with its formula in the Table 3 parameters. That check found a third source
inconsistency (SI-3, Proposition 7.8 (II) versus Table 6 row 14), recorded in
`specs/A0_parameters.yaml`.

The third pair is A2, the combinatorial layer (`Challenge/A2Combinatorial.lean`,
`Solution/A2Combinatorial.lean`): Lemma 4.2, the §7.2 smooth-insertion mechanism,
the factor-extraction Lemmas 7.5–7.7 in log-size form, Table 2, Lemma 8.2 and
Lemma 9.2. Scope notes and the source hypotheses the proofs leave unused are in
`specs/results/A2_combinatorial.yaml`.

The fourth pair is B1, the multi-shift GDT counting theorem (`Challenge/MultiShift.lean`,
`Solution/MultiShift.lean`). It counts `n ≡ a (mod m)` with `gcd(n + h, N) = 1` for every
shift `h ∈ H`: each period `Tmin = mR` holds exactly `∏_{p | R} (p − ν_p(H))` such
values, absolute density `(1/m)·∏_{p | R}(1 − ν_p(H)/p)`. With `H = {0}` it re-derives GDT
v1.0.0's `gdt_count_per_period`, statement for statement (Gate B). It uses Mathlib and
vendors GDT v1.0.0's definitions and lemmas in `BGP212/GDTv1Basic.lean` and
`BGP212/GDTv1.lean`, with provenance hashes in their headers.

The fifth pair is B2 (`Challenge/MultiShiftB2.lean`, `Solution/MultiShiftB2.lean`):
relative density; local positivity (the accepted set is nonempty exactly when every local
factor is positive); a minimal-period theorem extending GDT v1.0.0's to every nonempty shift
set, with kernel-checked counterexamples showing both of its extra hypotheses are needed;
and the W-trick of Definition 4.5. Through `admissible_iff_local_factors`, Lemma 12.1 gives
a residue `b` with `gcd(b + h, W) = 1` for all `h ∈ H₄₅` and every `W`; at
`W = 2·3·…·23` that residue is unique, `b = 74549147`.

The sixth pair is A3a (`Challenge/Packing.lean`, `Solution/Packing.lean`), the first part
of Lemma 7.10's factor packing: a generic greedy packing lemma and 296 of the 455 packing
roots, each proved for every rough profile in its domain (the settled condition-(D) root
uniformly over its full (γ, ω₀) box). Certificates are in
`specs/certificates/packing_a3a.json`; the kernel re-checks every inequality. The other 159
roots are listed in `openRoots` and stay outside the proved scope until A3b.

The seventh pair is A3b (`Challenge/PackingB.lean`, `Solution/PackingB.lean`), a verified
certificate checker for Lemma 7.10 (Farkas certificates over subdivision trees of sorted
cells, `Solution/PackingCert.lean`) and 116 further roots: all remaining (A), (C), (E) roots
and 47 of the 90 (D) roots, uniformly over the (γ, ω₀) box. With A3a, **412 of the 455
roots** are proved. The 43 remaining (D) roots are listed in `openRootsB`.

## What is proved, imported, and external

- **Proved here, kernel-checked:** Lemma 12.1; the Table 3 parameter layer and every
  Appendix B row as a formula in those parameters; the A2 combinatorial lemmas; the
  multi-shift GDT counting theorem (B1); density, positivity, minimal period and the
  W-trick for H₄₅ (B2); 412 of the 455 packing roots of Lemma 7.10 (A3a, A3b).
- **Imported analytic hypotheses (taken as hypotheses in Axiom's certificate too):** the
  Type I/II/III equidistribution estimates (Lemmas 5.3–5.7), bilinear Bombieri–Vinogradov
  (Lemma 8.1), and the Harman decomposition (Proposition 7.2).
- **Covered by Axiom's own Lean certificate, outside this repository:** the sieve
  criterion (Theorem 4.10) and the deduction of Theorem 1.1.
- **Open, outside the proved scope:** the 43 condition-(D) packing roots of Lemma 7.10
  listed in `openRootsB`, and the exact variational certificate of Theorem 11.1.

## Comparator Verification

Track B uses Mathlib, so fetch its build cache first:

```text
lake exe cache get
```

Then

```text
./verify.sh
```

To regenerate and cross-check the A3a certificate data (exploratory, outside the kernel):

```text
python3 -I specs/checks/packing_ledger.py specs/certificates/packing_a3a.json
python3 -I specs/checks/packing_certificates_match.py
```

For A3b (the generator needs SciPy; it proposes candidates only):

```text
python3 -I specs/checks/packing_a3b_generate.py specs/certificates/packing_a3a.json /tmp/a3b.json
cmp /tmp/a3b.json specs/certificates/packing_a3b.json
python3 -I specs/checks/packing_a3b_emit.py specs/certificates/packing_a3b.json . --check
```

builds the project and runs Lean Comparator on each config in `Comparator/`.
A successful run ends with:

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

Axioms used: `propext` and `Quot.sound` for Lemma 12.1; `propext`, `Quot.sound` and
`Classical.choice` for the other pairs (all within the permitted set). Each pair's
run, sandbox provenance and negative controls are recorded in `specs/results/`.

## Source

Place Axiom Math's PDF at `Source/bgp212.pdf` (kept outside version control). sha256 `2b307ae26046dffd2153fe7466e5a9a302976dc3ba5142151a8a8104a37b3d80`.
