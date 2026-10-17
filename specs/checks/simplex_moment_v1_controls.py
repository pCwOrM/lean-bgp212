"""V1 positive and negative controls (outside the trusted base).

Usage, from the repository root (after `lake build Solution.SimplexMoment`):
  python3 -I specs/checks/simplex_moment_v1_controls.py OUTDIR
  for f in OUTDIR/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done

Each file evaluates one concrete integral through the kernel-checked identity (10.1) or the
Beta moment and then asks `norm_num` to confirm a value. `ok_*` files carry the true value and
are accepted; `nc_*` files carry a value from a plausible wrong formula and are rejected."""
import os, sys

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
HDR = ("import Solution.SimplexMoment\nopen BGP212.Var MeasureTheory\n")
TRI = ("example : ∫ z in simplex 2 ((1 : ℚ) : ℝ), ∏ i, z i ^ ({VEC} : Fin 2 → ℕ) i = {VAL} := by\n"
       "  rw [simplex_integral_rat 2 1 (by norm_num)]\n"
       "  norm_num [simplexMoment, Nat.factorial]\n")
BETA = ("example : ∫ x in (0 : ℝ)..1, x ^ 2 * (1 - x) ^ 3 = {VAL} := by\n"
        "  rw [beta_integral]\n"
        "  norm_num [betaR, Nat.factorial]\n")
VOL = ("example : ∫ _ in simplex 3 (2 : ℝ), (1 : ℝ) = {VAL} := by\n"
       "  rw [simplex_volume 3 2 (by norm_num)]\n"
       "  norm_num [Nat.factorial]\n")
cases = {
    "ok_triangle_area": ("area of the unit triangle: 1/2", TRI.replace("{VEC}", "![0, 0]").replace("{VAL}", "1 / 2")),
    "nc_triangle_area": ("area 1 (the formula without the dimension term m)", TRI.replace("{VEC}", "![0, 0]").replace("{VAL}", "1")),
    "ok_z1z2": ("∫ z₁ z₂ over the unit triangle: 1/24", TRI.replace("{VEC}", "![1, 1]").replace("{VAL}", "1 / 24")),
    "nc_z1z2": ("1/12 (the factorial of Σe in place of (m + Σe)!)", TRI.replace("{VEC}", "![1, 1]").replace("{VAL}", "1 / 12")),
    "ok_beta": ("∫₀¹ x²(1 − x)³ dx = 1/60", BETA.replace("{VAL}", "1 / 60")),
    "nc_beta": ("1/72 (a wrong value)", BETA.replace("{VAL}", "1 / 72")),
    "ok_volume": ("volume of the simplex of radius 2 in ℝ³: 4/3", VOL.replace("{VAL}", "4 / 3")),
    "nc_volume": ("8 (the cube [0, 2]³)", VOL.replace("{VAL}", "8")),
}
for name, (what, body) in cases.items():
    open(os.path.join(out, name + ".lean"), "w").write(f"{HDR}-- control: {what}\n{body}")
