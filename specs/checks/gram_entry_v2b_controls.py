#!/usr/bin/env python3
"""Positive and negative controls for V2b (the Gram entry as a Lebesgue integral).

Writes Lean files into the given directory (default /tmp/v2b_ctl). Each `ok_*` file must be
accepted and each `nc_*` file rejected:

  ok_N1 / nc_N1        ∫_{T̃₁} (L − x) x² = L·C(1)³/3 − C(1)⁴/4, an independent closed form
                       (T̃₁ = [0, C(1)]); the nc file claims the uncapped value L⁴/12.
  ok_N2 / nc_N2        the 2-dimensional entry equals V2a's exact polygon-clipping value; the nc file
                       uses the two-level caps of Lemma 9.1's proof (31/50, 17/25) in place of
                       Table 3's, which changes the value.
  ok_entry / nc_entry  the 45-dimensional entry equals gramEntryQ's value; the nc file claims the
                       value over the uncapped simplex {Σ x ≤ L} (relative difference 7·10⁻¹³).

Usage: python3 -I specs/checks/gram_entry_v2b_controls.py [dir]
Check: for f in DIR/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done
"""
import os
import sys
from fractions import Fraction as Fr
from math import factorial as fact

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gram_entry_v2b_emit as E  # noqa: E402

OUT = sys.argv[1] if len(sys.argv) > 1 else "/tmp/v2b_ctl"
os.makedirs(OUT, exist_ok=True)

HEAD = "import Solution.GramEntry\n\nopen BGP212.Gram MeasureTheory\n\n"
SUPP = "supportT {N} (41 / 625) (53 / 50) (fun m => ({C} m : ℝ))"


def q(x):
    x = Fr(x)
    return f"({x.numerator} / {x.denominator} : ℚ)"


def two_cap(m):
    if m == 0:
        return Fr(0)
    return Fr(31, 50) if m <= 2 else Fr(17, 25)


L, G = E.L, E.G
c1 = E.C(1)
v1 = L * c1 ** 3 / 3 - c1 ** 4 / 4
assert v1 == E.gram_formula(1, G, L, E.C, 2, 1)
v1_uncapped = L ** 4 / 12

v2 = E.gram_formula(2, G, L, E.C, 2, 1)
assert 2 * v2 == Fr(9366843779443, 610351562500000)   # V2a's polygon-clipping value
v2_two = E.gram_formula(2, G, L, two_cap, 2, 1)
assert v2_two != v2

entry = 45 * E.gram_formula(45, G, L, E.C, 2, 1)
entry_uncapped = 45 * L ** 48 * fact(2) * fact(1) / Fr(fact(48))

N1 = f"""theorem ctl : ∫ x in {SUPP.format(N=1, C='BGP212.Params.C')},
    ((53 / 50 : ℝ) - ∑ i, x i) ^ 1 * x 0 ^ 2 = (({{V}} : ℚ) : ℝ) := by
  have hc := gramFormula_ratCast 1 (41 / 625 : ℚ) (53 / 50) BGP212.Params.C 2 1
  rw [integral_supportT 1 _ _ _ (by norm_num) 0 2 1]
  have hq : gramFormula 1 (41 / 625 : ℚ) (53 / 50) BGP212.Params.C 2 1 = {{V}} := by decide +kernel
  rw [hq] at hc
  push_cast at hc
  rw [← hc]
  all_goals norm_num
"""

N2 = """def twoCap (m : ℕ) : ℚ := if m = 0 then 0 else if m ≤ 2 then 31 / 50 else 17 / 25

theorem ctl : gramFormula 2 (41 / 625 : ℚ) (53 / 50) {CAP} 2 1 = {V} := by decide +kernel
"""

ENTRY = f"""theorem ctl : ∫ x in {SUPP.format(N=45, C='BGP212.Params.C')},
    ((53 / 50 : ℝ) - ∑ i, x i) * ∑ i, x i ^ 2 = (({{V}} : ℚ) : ℝ) := by
  rw [gram_entry_integral, gramEntryQ_eq]
  all_goals norm_num
"""

files = {
    "ok_N1": N1.replace("{V}", q(v1)),
    "nc_N1": N1.replace("{V}", q(v1_uncapped)),
    "ok_N2": N2.replace("{CAP}", "BGP212.Params.C").replace("{V}", q(v2)),
    "nc_N2": N2.replace("{CAP}", "twoCap").replace("{V}", q(v2)),
    "ok_entry": ENTRY.replace("{V}", q(entry)),
    "nc_entry": ENTRY.replace("{V}", q(entry_uncapped)),
}
for name, body in files.items():
    open(os.path.join(OUT, name + ".lean"), "w").write(HEAD + body)
print("wrote", len(files), "control files to", OUT)
print("uncapped/capped − 1 =", float(entry_uncapped / entry - 1))
