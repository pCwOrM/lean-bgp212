#!/usr/bin/env python3
"""Positive and negative controls for V2e-B (polygon cells of the cap branch).

Writes Lean files into the given directory (default /tmp/v2eb_ctl). Each `ok_*` file must be
accepted and each `nc_*` file rejected. Independent checks run here first:

  * every `boxVal` used below is compared with exact polygon clipping (triangle fans, no
    case analysis), including cells cut by the anti-diagonal;
  * the worked certificate is compared with the rectangle closed form
    (L − C(2))⁴³ ((C(2) − g)³ − g³) / (3 · 43!);
  * a three-dimensional analogue of the certificate (N = 3, R = {0}, same Table 3 data) is
    integrated numerically on a grid directly in y (no aggregate change of variables) and
    compared with the aggregate formula.

  ok_box_diag / nc_box_rect     boxVal for a cell cut by the diagonal (A = 1/2, B = 2/3, D = 1,
                                u₁² u₂) equals the clipping value; the rectangle product is rejected.
  ok_box_integral               the same as a Lebesgue integral (box_monomial, boxVal_cast).
  ok_cert / nc_cert_capindex /  the certificate capPieceT3; the values with the cap index C(r)
  nc_cert_nojac                 in place of C(r+1), and with the aggregate exponent without −1.
  ok_branch / nc_branch         the endpoint at a cap-cell point is the cap value; at a point
                                with u₂ > c₂ (the L − S branch) the cap value is rejected.
  ok_empty / nc_empty           the Table 3 cap cell with r = 1, k = 7 is empty; with k = 6 the
                                emptiness inequality L − 6g < C(2) is rejected.

Usage: python3 -I specs/checks/capcell_v2eb_controls.py [dir]
Check: for f in DIR/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
"""
import os
import sys
from fractions import Fraction as Fr
from math import comb, factorial as fact

OUT = sys.argv[1] if len(sys.argv) > 1 else "/tmp/v2eb_ctl"
os.makedirs(OUT, exist_ok=True)

G, L, TAU = Fr(41, 625), Fr(53, 50), Fr(249, 250)
BNUM = [777, 794, 875, 917, 953, 983, 1016, 1042, 1063, 1081]


def C(m):
    return Fr(0) if m == 0 else 4 * Fr(BNUM[min(m, 10) - 1], 5000)


def inner(X, D, p, t):
    return sum(comb(p, j) * D ** (p - j) * (-1) ** j * X ** (t + j + 1) / (t + j + 1)
               for j in range(p + 1))


def boxval(A, B, D, a, b):
    if not (A >= 0 and B >= 0):
        return Fr(0)
    E = max(Fr(0), min(A, D - B))
    F = max(Fr(0), min(A, D))
    return (B ** (b + 1) * E ** (a + 1) / (a + 1) + (inner(F, D, b + 1, a) - inner(E, D, b + 1, a))) / (b + 1)


def cappow(A, B, D, a, al, be, m):
    return sum(comb(m, i) * a ** (m - i) * (-1) ** i * boxval(A, B, D, al + i, be) for i in range(m + 1))


# ---- independent: polygon clipping --------------------------------------------------------------
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
    o = {}
    for (a, b), c in p.items():
        for (d, e), f in q.items():
            o[(a + d, b + e)] = o.get((a + d, b + e), 0) + c * f
    return o


def ppow(p, n):
    o = {(0, 0): Fr(1)}
    for _ in range(n):
        o = pmul(o, p)
    return o


def tri_int(f, A, B, Cc):
    xs = {(0, 0): A[0], (1, 0): B[0] - A[0], (0, 1): Cc[0] - A[0]}
    ys = {(0, 0): A[1], (1, 0): B[1] - A[1], (0, 1): Cc[1] - A[1]}
    jac = abs((B[0] - A[0]) * (Cc[1] - A[1]) - (Cc[0] - A[0]) * (B[1] - A[1]))
    tot = Fr(0)
    for (i, j), c in f.items():
        for (u, v), w in pmul(ppow(xs, i), ppow(ys, j)).items():
            tot += c * w * Fr(fact(u) * fact(v), fact(u + v + 2))
    return jac * tot


def clipval(A, B, D, a, b):
    big = Fr(10)
    P = [(Fr(0), Fr(0)), (big, Fr(0)), (big, big), (Fr(0), big)]
    for (x, y, c) in [(1, 0, A), (0, 1, B), (1, 1, D), (-1, 0, 0), (0, -1, 0)]:
        P = clip(P, x, y, c)
    if len(P) < 3:
        return Fr(0)
    return sum(tri_int({(a, b): Fr(1)}, P[0], P[i], P[i + 1]) for i in range(1, len(P) - 1))


A0, B0, D0 = Fr(1, 2), Fr(2, 3), Fr(1)
v_diag = boxval(A0, B0, D0, 2, 1)
assert v_diag == clipval(A0, B0, D0, 2, 1)
v_rect_wrong = A0 ** 3 / 3 * B0 ** 2 / 2
assert v_rect_wrong != v_diag

# ---- the worked certificate ------------------------------------------------------------------------
A = min(C(1) - G, C(2) - 2 * G)
B = L - C(2)
M = TAU - G
a = C(2) - G
V = cappow(A, B, M, a, 0, 42, 2) / fact(42)
assert V == B ** 43 * (a ** 3 - G ** 3) / (3 * fact(43))
assert boxval(A, B, M, 2, 42) == clipval(A, B, M, 2, 42)
# cap index C(r) instead of C(r+1)
A1, B1, a1 = min(C(1) - G, C(1) - 2 * G), L - C(1), C(1) - G
V_capindex = cappow(A1, B1, M, a1, 0, 42, 2) / fact(42)
# aggregate exponent without −1 (u₂^43, constant 1/43!)
V_nojac = cappow(A, B, M, a, 0, 43, 2) / fact(43)
assert len({V, V_capindex, V_nojac}) == 3

# ---- three-dimensional analogue, integrated directly in y (numerical) -----------------------------
# N = 3, R = {0}, K = ∅: pieceSet {y ≥ 0, y₀ ≤ C(1) − g, Σ y ≤ τ − g}, cap branch, integrand U².
def direct3(n=240):
    c1, c2 = C(2) - 2 * G, L - C(2)
    cpc, Mt = float(C(1) - G), float(M)
    tot = 0.0
    h = float(Mt) / n
    for i in range(n):
        y0 = (i + 0.5) * h
        if y0 > cpc or y0 > float(c1):
            continue
        Uc = float(C(2) - G) - y0
        for j in range(n):
            y1 = (j + 0.5) * h
            for k in range(n):
                y2 = (k + 0.5) * h
                if y0 + y1 + y2 > Mt or y1 + y2 > float(c2):
                    continue
                tot += Uc * Uc
    return tot * h ** 3


V3 = cappow(A, B, M, a, 0, 1, 2) / fact(1)        # aggConst {0} = 1, aggConst Rᶜ = 1/1!
d3 = direct3()
assert abs(d3 - float(V3)) / float(V3) < 2e-2, (d3, float(V3))


def q(v):
    v = Fr(v)
    return f"(({v.numerator} / {v.denominator} : ℚ) : ℝ)"


HEAD = """import Solution.CapCell

open BGP212.Gram BGP212.V2d BGP212.V2e MeasureTheory

"""
BOXQ = """theorem ctl : boxVal (1 / 2 : ℚ) (2 / 3) 1 2 1 = ({V} : ℚ) := by decide +kernel
"""
BOXI = """theorem ctl : ∫ q in boxTri (1 / 2) (2 / 3) 1, q.1 ^ 2 * q.2 ^ 1 = {V} := by
  rw [box_monomial]
  have h := boxVal_cast (1 / 2 : ℚ) (2 / 3) 1 2 1
  have hv : boxVal (1 / 2 : ℚ) (2 / 3) 1 2 1 = {VQ} := by decide +kernel
  rw [hv] at h
  push_cast at h
  rw [← h]
  norm_num
"""
CERT = """theorem ctl : capPieceT3 = {V} := by
  rw [capPieceT3_value]
  all_goals norm_num
"""
BR = """theorem ctl : endpointAgg g3 L3 C3 1 0 (1 / 10) {U2} = C3 2 - (1 * g3 + 1 / 10) := by
  have hC : BGP212.Params.C 2 = 794 / 1250 := by decide +kernel
  simp only [endpointAgg, g3, L3, C3, hC, BGP212.Params.g, BGP212.Params.L]
  push_cast
  norm_num [min_def, max_def]
"""
EMPTY = """theorem ctl : L3 - ({K} : ℕ) * g3 < C3 (1 + 1) := by
  have hC : BGP212.Params.C 2 = 794 / 1250 := by decide +kernel
  simp only [g3, L3, C3, hC, BGP212.Params.g, BGP212.Params.L]
  push_cast
  norm_num
"""
files = {
    "ok_box_diag": BOXQ.replace("{V}", f"{v_diag.numerator} / {v_diag.denominator}"),
    "nc_box_rect": BOXQ.replace("{V}", f"{v_rect_wrong.numerator} / {v_rect_wrong.denominator}"),
    "ok_box_integral": BOXI.replace("{V}", q(v_diag)).replace("{VQ}", f"{v_diag.numerator} / {v_diag.denominator}"),
    "ok_cert": CERT.replace("{V}", q(V)),
    "nc_cert_capindex": CERT.replace("{V}", q(V_capindex)),
    "nc_cert_nojac": CERT.replace("{V}", q(V_nojac)),
    "ok_branch": BR.replace("{U2}", "(1 / 10)"),
    "nc_branch": BR.replace("{U2}", "(1 / 2)"),
    "ok_empty": EMPTY.replace("{K}", "7"),
    "nc_empty": EMPTY.replace("{K}", "6"),
}
for name, body in files.items():
    open(os.path.join(OUT, name + ".lean"), "w").write(HEAD + body)
print("wrote", len(files), "control files to", OUT)
print("diag cell value", v_diag, " certificate ≈", float(V), " 3-D analogue: grid", d3, "formula", float(V3))
