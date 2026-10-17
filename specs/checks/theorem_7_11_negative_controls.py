"""A4 negative controls (outside the trusted base).

Usage, from the repository root (after `lake build BGP212.Theorem711`):
  python3 -I specs/checks/theorem_7_11_negative_controls.py OUTDIR
  for f in OUTDIR/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done

Each `ok_*.lean` file is a true statement and is accepted; each `nc_*.lean` file moves one
parameter across a wall the A4 proofs depend on and is rejected (`decide` fails)."""
import os, sys

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
HDR = "import BGP212.Theorem711\nopen BGP212.Params BGP212.Packing BGP212.T711\n"
cases = {
    "ok_scalar": ("(I)–(III) at Table 3",
                  "example : Prop78Scalar 1 A3 δ ξ1 ξ2 ξ3 εa := by unfold Prop78Scalar; decide +kernel"),
    "nc_scalar_wall": ("δ raised by 1/10000 crosses the dominant Type II wall (slack 499999/5000000000)",
                       "example : Prop78Scalar 1 A3 (δ + 1 / 10000) ξ1 ξ2 ξ3 εa := by unfold Prop78Scalar; decide +kernel"),
    "ok_IIc_bottom": ("Lemma 5.6 permissible at γ = ξ₂ − ϵ, δ* = δ",
                      "example : PermIIc 0 ω11 (ξ2 - εa) δ := by unfold PermIIc; decide +kernel"),
    "nc_IIc_below": ("γ = 2/5 − 1/1000, below the IIc range: 48ω + 16δ − 4γ < −1 fails",
                     "example : PermIIc 0 ω11 (2 / 5 - 1 / 1000) δ := by unfold PermIIc; decide +kernel"),
    "ok_III_A4": ("Lemma 5.7 permissible at γ = ξ₃ + ϵ with A4's width",
                  "example : PermIII 0 ω11 (ξ3 + εa) (dIII ω11 ξ3 εa) := by unfold PermIII; decide +kernel"),
    "nc_III_printed": ("the printed Type III width at γ = ξ₃ + ϵ",
                       "example : PermIII 0 ω11 (ξ3 + εa) (dIIIprinted ω11 ξ3 εa) := by unfold PermIII; decide +kernel"),
    "ok_floor": ("⌊1/δ⌋ = 60", "example : floorInv δ = 60 := by decide +kernel"),
    "nc_floor": ("⌊1/δ⌋ = 61", "example : floorInv δ = 61 := by decide +kernel"),
    "ok_vacuity": ("14 coordinates of size δ exceed every cap: B 14 < 14δ",
                   "example : B 14 < 14 * δ := by decide +kernel"),
    "nc_vacuity": ("the reverse, which would make m = 14 non-vacuous",
                   "example : 14 * δ ≤ B 14 := by decide +kernel"),
}
for name, (what, body) in cases.items():
    open(os.path.join(out, name + ".lean"), "w").write(f"{HDR}-- control: {what}\n{body}\n")
