#!/usr/bin/env python3
"""Positive and negative controls for V2e-A (two-aggregate Dirichlet integration).

Writes Lean files into the given directory (default /tmp/v2e_ctl). Each `ok_*` file must be
accepted and each `nc_*` file rejected.

  ok_example / nc_example_*   the worked example ∫_{y ∈ ℝ³, y ≥ 0, Σy ≤ 1} y₀ y₂² 1[y₀ ≤ 1/2] dy.
                              Its value is recomputed here by an independent method: the direct
                              iterated integral dy₂ dy₁ dy₀ over the simplex, in exact rational
                              polynomial arithmetic, with no aggregate change of variables.
                              nc_example_nojac uses aggregate exponents |ι| + Σe (the −1 dropped);
                              nc_example_uncut claims the uncut value 1/360.
  ok_const / nc_const_nojac   two_group_const for I = Fin 1, J = Fin 2, a = (1), b = (0, 2), R = 1:
                              the value 1/360 of (10.1); the nc file uses the exponents without −1.
  ok_stratum / nc_union       the endpoint on V2b's piece (R, K) = ({0}, {1}) at Table 3 with
                              y = (1/10, 1/10, 1/20), x = y + g·1_{R∪K}: the stratum endpoint (cap
                              index |R| + 1 = 2, rough mass x₀) is 587/1250; the nc file takes the
                              cap index and mass from R ∪ K (the translated point's own rough set)
                              and claims the same value (its value is 461/1250, ok_union_value).
  ok_link                     stratumEndpoint_shift on the same piece: the endpoint equals
                              endpointAgg at the aggregates (u₁, u₂) = (1/10, 3/20).

Usage: python3 -I specs/checks/aggregate_v2e_controls.py [dir]
Check: for f in DIR/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
"""
import os
import sys
from fractions import Fraction as Fr
from math import comb, factorial as fact

OUT = sys.argv[1] if len(sys.argv) > 1 else "/tmp/v2e_ctl"
os.makedirs(OUT, exist_ok=True)


# ---- exact univariate polynomial arithmetic (coefficient lists) -------------------------------
def padd(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def pmul(p, q):
    out = [Fr(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return out


def ppow(p, n):
    out = [Fr(1)]
    for _ in range(n):
        out = pmul(out, p)
    return out


def pint(p, a, b):
    return sum(c * (b ** (i + 1) - a ** (i + 1)) / (i + 1) for i, c in enumerate(p))


# ---- independent value: ∫₀^{c} y₀ ∫₀^{1−y₀} ∫₀^{1−y₀−y₁} y₂² dy₂ dy₁ dy₀ --------------------
# inner: ∫₀^{T} y₂² = T³/3 with T = 1 − y₀ − y₁; middle: ∫₀^{1−y₀} (1 − y₀ − y₁)³/3 dy₁ =
# (1 − y₀)⁴/12 (substitute v = 1 − y₀ − y₁, a direct one-variable step); outer by expansion.
def example_direct(c, R=Fr(1)):
    one_minus = [R, Fr(-1)]                       # R − y₀
    integrand = pmul([Fr(0), Fr(1)], ppow(one_minus, 4))   # y₀ (R − y₀)⁴
    return pint(integrand, Fr(0), min(c, R)) / 12


# the same middle step checked symbolically: ∫₀^{M} (M − y)³ dy = M⁴/4 for M = 7/9
M = Fr(7, 9)
assert pint(ppow([M, Fr(-1)], 3), Fr(0), M) == M ** 4 / 4

v_example = example_direct(Fr(1, 2))
v_uncut = example_direct(Fr(1))
assert v_example == Fr(19, 7680) and v_uncut == Fr(1, 360)
assert v_uncut == Fr(fact(1) * fact(2), fact(6))   # (10.1): 1! 0! 2! / (3 + 3)!


# ---- the wrong-Jacobian variant: aggregate exponents |ι| + Σe instead of |ι| + Σe − 1 ----------
def tri_cut(R, c, al, be):
    integrand = pmul([Fr(0)] * al + [Fr(1)], ppow([R, Fr(-1)], be + 1))
    return pint(integrand, Fr(0), c) / (be + 1)


kI, kJ = 1 + 1, 2 + 2                     # no −1
cI, cJ = Fr(fact(1), fact(kI)), Fr(fact(0) * fact(2), fact(kJ))
v_nojac = cI * cJ * tri_cut(Fr(1), Fr(1, 2), kI, kJ)
assert v_nojac != v_example
# with the −1 the same recipe reproduces the direct value
assert Fr(1) * Fr(2, 6) * tri_cut(Fr(1), Fr(1, 2), 1, 3) == v_example
v_const_nojac = cI * cJ * Fr(fact(kI) * fact(kJ), fact(2 + kI + kJ))
assert v_const_nojac != v_uncut

# ---- the endpoint on a piece at Table 3 --------------------------------------------------------
G, L = Fr(41, 625), Fr(53, 50)
BNUM = [777, 794, 875, 917, 953, 983, 1016, 1042, 1063, 1081]


def C(m):
    return Fr(0) if m == 0 else 4 * Fr(BNUM[min(m, 10) - 1], 5000)


y = [Fr(1, 10), Fr(1, 10), Fr(1, 20)]
x = [y[0] + G, y[1] + G, y[2]]
assert x[2] <= G < x[0] and G < x[1]           # the translated point's own rough set is {0, 1}
S = sum(x)
U_stratum = min(L - S, max(G, C(2) - x[0]))
U_union = min(L - S, max(G, C(3) - (x[0] + x[1])))
u1, u2 = y[0], y[1] + y[2]
U_agg = min(L - (2 * G + u1 + u2), max(G, C(2) - (G + u1)))
assert U_stratum == U_agg == Fr(587, 1250) and U_union == Fr(461, 1250)


def q(v):
    v = Fr(v)
    return f"({v.numerator} / {v.denominator} : ℝ)"


HEAD = """import Solution.Aggregate

open BGP212.Gram BGP212.V2d BGP212.V2e MeasureTheory

"""
EX = """theorem ctl : exampleLHS (1 / 2) 1 = {V} := by
  rw [example_value]
  all_goals norm_num
"""
CONST = """theorem ctl : ∫ p in quad (Fin 1) (Fin 2) 1, (∏ i, p.1 i ^ (![1] : Fin 1 → ℕ) i) *
    (∏ j, p.2 j ^ (![0, 2] : Fin 2 → ℕ) j) = {V} := by
  rw [two_group_const 1 (by norm_num)]
  simp [Fin.sum_univ_two, Fin.prod_univ_two, Nat.factorial]
  all_goals norm_num
"""
END = """noncomputable def Ct : ℕ → ℝ := fun m => (BGP212.Params.C m : ℝ)

theorem C2 : Ct 2 = 794 / 1250 := by
  have : BGP212.Params.C 2 = 794 / 1250 := by decide +kernel
  simp only [Ct, this]; norm_num

theorem C3 : Ct 3 = 875 / 1250 := by
  have : BGP212.Params.C 3 = 875 / 1250 := by decide +kernel
  simp only [Ct, this]; norm_num

theorem ctl : stratumEndpoint (41 / 625) (53 / 50) Ct {SET}
    (![1 / 10 + 41 / 625, 1 / 10 + 41 / 625, 1 / 20] : Fin 3 → ℝ) = {V} := by
  simp only [stratumEndpoint, aggR, Fin.sum_univ_three, Finset.sum_singleton,
    Finset.sum_pair (show (0 : Fin 3) ≠ 1 by decide), Finset.card_singleton,
    Finset.card_pair (show (0 : Fin 3) ≠ 1 by decide), Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  norm_num [C2, C3, min_def, max_def]
"""
LINK = """noncomputable def Ct : ℕ → ℝ := fun m => (BGP212.Params.C m : ℝ)

theorem ctl : stratumEndpoint (41 / 625) (53 / 50) Ct {0}
    ((![1 / 10, 1 / 10, 1 / 20] : Fin 3 → ℝ) + shiftV (41 / 625) ({0} ∪ {1})) =
      endpointAgg (41 / 625) (53 / 50) Ct 1 1 (1 / 10) (3 / 20) := by
  rw [stratumEndpoint_shift _ _ _ _ _ (by decide)]
  have h1 : aggR {0} (![1 / 10, 1 / 10, 1 / 20] : Fin 3 → ℝ) = 1 / 10 := by
    simp [aggR]
  have h2 : aggS {0} (![1 / 10, 1 / 10, 1 / 20] : Fin 3 → ℝ) = 3 / 20 := by
    rw [aggS, show ({0} : Finset (Fin 3))ᶜ = {1, 2} by decide,
      Finset.sum_pair (show (1 : Fin 3) ≠ 2 by decide)]
    simp; norm_num
  rw [h1, h2]; rfl
"""
files = {
    "ok_example": EX.replace("{V}", q(v_example)),
    "nc_example_nojac": EX.replace("{V}", q(v_nojac)),
    "nc_example_uncut": EX.replace("{V}", q(v_uncut)),
    "ok_const": CONST.replace("{V}", q(v_uncut)),
    "nc_const_nojac": CONST.replace("{V}", q(v_const_nojac)),
    "ok_stratum": END.replace("{SET}", "{0}").replace("{V}", q(U_stratum)),
    "nc_union": END.replace("{SET}", "{0, 1}").replace("{V}", q(U_stratum)),
    "ok_union_value": END.replace("{SET}", "{0, 1}").replace("{V}", q(U_union)),
    "ok_link": LINK,
}
for name, body in files.items():
    open(os.path.join(OUT, name + ".lean"), "w").write(HEAD + body)
print("wrote", len(files), "control files to", OUT)
print("example (direct) =", v_example, " no-Jacobian variant =", v_nojac, " uncut =", v_uncut)
print("endpoint: stratum =", U_stratum, " union =", U_union)
