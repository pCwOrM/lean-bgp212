#!/usr/bin/env python3
"""Positive and negative controls for V2c (the general monomial integral bridge).

Writes Lean files into the given directory (default /tmp/v2c_ctl). Each `ok_*` file must be
accepted and each `nc_*` file rejected:

  ok_N2_pair / nc_N2_pair     two distinguished coordinates in dimension 2:
                              gramFin 2 2 … ![2, 2] 1 equals ∫_{T̃₂} (L − x − y) x² y², computed
                              here by an independent method (exact rational polygon clipping of
                              each stratum, triangle fans; no inclusion–exclusion, no Dirichlet
                              formula); the nc file uses the two-level caps of Lemma 9.1's proof.
  ok_consistency_N3           the general closed form with one distinguished coordinate equals
                              V2b's (`gramFin 3 1 … ![2] 1 = gramFormula 3 … 2 1`).
  ok_example / nc_example_*   the worked example ∫_{T̃} (L − P₁) P₂² equals gramExampleQ's value;
                              nc_example_ordered counts the diagonal twice (45·F4 + 2025·F22),
                              nc_example_uncapped claims the uncapped-simplex value.

Usage: python3 -I specs/checks/gram_general_v2c_controls.py [dir]
Check: for f in DIR/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
"""
import os
import sys
from fractions import Fraction as Fr
from math import factorial as fact

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gram_general_v2c_emit as E  # noqa: E402

OUT = sys.argv[1] if len(sys.argv) > 1 else "/tmp/v2c_ctl"
os.makedirs(OUT, exist_ok=True)
L, G, C = E.L, E.G, E.C


# ---- independent exact integration in dimension 2 (polygon clipping) -------------------------
def clip(poly, a, b, c):
    out = []
    n = len(poly)
    for i in range(n):
        P, Q = poly[i], poly[(i + 1) % n]
        fP = a * P[0] + b * P[1] - c
        fQ = a * Q[0] + b * Q[1] - c
        if fP <= 0:
            out.append(P)
        if (fP < 0 < fQ) or (fQ < 0 < fP):
            t = fP / (fP - fQ)
            out.append((P[0] + t * (Q[0] - P[0]), P[1] + t * (Q[1] - P[1])))
    return out


def pmul(p, q):
    out = {}
    for (a, b), c in p.items():
        for (d, e), f in q.items():
            out[(a + d, b + e)] = out.get((a + d, b + e), 0) + c * f
    return out


def ppow(p, n):
    out = {(0, 0): Fr(1)}
    for _ in range(n):
        out = pmul(out, p)
    return out


def tri_integral(f, A, B, Cc):
    xs = {(0, 0): A[0], (1, 0): B[0] - A[0], (0, 1): Cc[0] - A[0]}
    ys = {(0, 0): A[1], (1, 0): B[1] - A[1], (0, 1): Cc[1] - A[1]}
    jac = abs((B[0] - A[0]) * (Cc[1] - A[1]) - (Cc[0] - A[0]) * (B[1] - A[1]))
    tot = Fr(0)
    for (i, j), c in f.items():
        for (u, v), w in pmul(ppow(xs, i), ppow(ys, j)).items():
            tot += c * w * Fr(fact(u) * fact(v), fact(u + v + 2))
    return jac * tot


def polygon_integral_N2(f, caps):
    big = Fr(10)
    box = [(Fr(0), Fr(0)), (big, Fr(0)), (big, big), (Fr(0), big)]
    total = Fr(0)
    for R in [(), (0,), (1,), (0, 1)]:
        P = list(box)
        for i in range(2):
            a, b = (1, 0) if i == 0 else (0, 1)
            P = clip(P, -a, -b, -G) if i in R else clip(P, a, b, G)
        P = clip(P, 1, 1, L)
        if R:
            P = clip(P, 1 if 0 in R else 0, 1 if 1 in R else 0, caps(len(R)))
        if len(P) >= 3:
            total += sum(tri_integral(f, P[0], P[i], P[i + 1]) for i in range(1, len(P) - 1))
    return total


def two_cap(m):
    if m == 0:
        return Fr(0)
    return Fr(31, 50) if m <= 2 else Fr(17, 25)


# (L − x − y) x² y²
F = pmul({(0, 0): L, (1, 0): Fr(-1), (0, 1): Fr(-1)}, {(2, 2): Fr(1)})
v_pair = polygon_integral_N2(F, C)
v_pair_two = polygon_integral_N2(F, two_cap)
assert v_pair != v_pair_two

# the general closed form in dimension 2 reproduces the polygon value (checked here too)
E_N = E.N
E.N = 2
assert sum(sum(E.fin_cell([2, 2], r, A, B) for A, B in E.CELLS[2]) for r in range(1)) == v_pair
E.N = E_N

f4 = sum(sum(E.fin_cell([4], r, A, B) for A, B in E.CELLS[1]) for r in range(45))
f22 = sum(sum(E.fin_cell([2, 2], r, A, B) for A, B in E.CELLS[2]) for r in range(44))
example = 45 * f4 + 1980 * f22
example_ordered = 45 * f4 + 2025 * f22
# uncapped simplex {Σ x ≤ L}: ∫ xᵃ (L − Σx)^p = L^{N+|a|+p} ∏a! p! / (N+|a|+p)!
example_uncapped = (45 * L ** 50 * fact(4) / Fr(fact(50))
                    + 1980 * L ** 50 * fact(2) * fact(2) / Fr(fact(50)))


def q(x):
    x = Fr(x)
    return f"({x.numerator} / {x.denominator} : ℚ)"


HEAD = "import Solution.GramGeneral\n\nopen BGP212.Gram BGP212.Params MeasureTheory\n\n"
PAIR = """def twoCap (m : ℕ) : ℚ := if m = 0 then 0 else if m ≤ 2 then 31 / 50 else 17 / 25

theorem ctl : gramFin 2 2 (41 / 625 : ℚ) (53 / 50) {CAP} ![2, 2] 1 = {V} := by decide +kernel
"""
CONS = """theorem ctl : gramFin 3 1 (41 / 625 : ℚ) (53 / 50) C ![2] 1 =
    gramFormula 3 (41 / 625 : ℚ) (53 / 50) C 2 1 := by decide +kernel
"""
EX = """theorem ctl : ∫ x in supportT 45 (41 / 625) (53 / 50) (fun m => (C m : ℝ)),
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 1 {2}) *
      MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (BGP212.Var.gen 0 {2}) = (({V} : ℚ) : ℝ) := by
  rw [gram_entry_example, gramExampleQ_eq]
  all_goals norm_num
"""
files = {
    "ok_N2_pair": PAIR.replace("{CAP}", "C").replace("{V}", q(v_pair)),
    "nc_N2_pair": PAIR.replace("{CAP}", "twoCap").replace("{V}", q(v_pair)),
    "ok_consistency_N3": CONS,
    "ok_example": EX.replace("{V}", q(example)),
    "nc_example_ordered": EX.replace("{V}", q(example_ordered)),
    "nc_example_uncapped": EX.replace("{V}", q(example_uncapped)),
}
for name, body in files.items():
    open(os.path.join(OUT, name + ".lean"), "w").write(HEAD + body)
print("wrote", len(files), "control files to", OUT)
print("N = 2 pair value", v_pair, " two-cap", v_pair_two)
print("uncapped/capped − 1 =", float(example_uncapped / example - 1))
