"""V0 negative controls (outside the trusted base).

Usage, from the repository root (after `lake build BGP212.Variational`):
  python3 -I specs/checks/variational_v0_negative_controls.py OUTDIR
  for f in OUTDIR/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done

Each `ok_*.lean` file is a true count and is accepted; each `nc_*.lean` file changes one
constraint of the printed index set (or the target count) and is rejected (`decide` fails).
The counts use the explicit partition enumeration `partsLE`, equal to `Nat.Partition` counts
by the kernel-checked `p_eq_enumeration`."""
import os, sys

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
HDR = "import BGP212.Variational\nopen BGP212.Var\n"
S = "∑ j ∈ Finset.range 11, (partsLE j j).length * (22 - 2 * j)"
cases = {
    "ok_846": ("the printed index set: 846", f"example : {S} = 846 := by decide +kernel"),
    "nc_845": ("a dimension of 845", f"example : {S} = 845 := by decide +kernel"),
    "ok_p10": ("p(10) = 42", "example : (partsLE 10 10).length = 42 := by decide +kernel"),
    "nc_p10": ("p(10) = 41", "example : (partsLE 10 10).length = 41 := by decide +kernel"),
    "ok_all_parts": ("all parts allowed (odd too): 3506",
                     "example : ∑ d ∈ Finset.range 22, (partsLE d d).length = 3506 := by decide +kernel"),
    "nc_all_parts": ("all parts allowed counted as 846",
                     "example : ∑ d ∈ Finset.range 22, (partsLE d d).length = 846 := by decide +kernel"),
    "ok_degree_22": ("degree bound 22: 1041",
                     "example : ∑ j ∈ Finset.range 12, (partsLE j j).length * (23 - 2 * j) = 1041 := by decide +kernel"),
    "nc_degree_22": ("degree bound 22 counted as 846",
                     "example : ∑ j ∈ Finset.range 12, (partsLE j j).length * (23 - 2 * j) = 846 := by decide +kernel"),
}
for name, (what, body) in cases.items():
    open(os.path.join(out, name + ".lean"), "w").write(f"{HDR}-- control: {what}\n{body}\n")
