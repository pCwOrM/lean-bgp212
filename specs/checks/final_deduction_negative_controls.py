"""B3 negative controls (outside the trusted base).

Usage, from the repository root (after `lake build BGP212.Gap`):
  python3 -I specs/checks/final_deduction_negative_controls.py OUTDIR
  for f in OUTDIR/*.lean; do lake env lean "$f" >/dev/null 2>&1 && echo "$f accepted" || echo "$f rejected"; done

Each `ok_*.lean` file is a true statement and is accepted; each `nc_*.lean` file moves one
quantity the B3 proofs depend on and is rejected (`decide` fails)."""
import os, sys

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
HDR = "import BGP212.Gap\nopen BGP212 BGP212.WTrick BGP212.Gap\n"
cases = {
    "ok_diameter": ("H₄₅ has diameter at most 212",
                    "example : ∀ a ∈ H45Z, ∀ b ∈ H45Z, b - a ≤ 212 := by decide"),
    "nc_diameter": ("diameter at most 211",
                    "example : ∀ a ∈ H45Z, ∀ b ∈ H45Z, b - a ≤ 211 := by decide"),
    "ok_card": ("H₄₅ has 45 elements", "example : H45Z.card = 45 := by decide"),
    "nc_card": ("44 elements", "example : H45Z.card = 44 := by decide"),
    "ok_even": ("every element of H₄₅ is even", "example : ∀ a ∈ H45Z, (2 : ℤ) ∣ a := by decide"),
    "nc_odd": ("some element of H₄₅ is odd", "example : ∃ a ∈ H45Z, ¬ (2 : ℤ) ∣ a := by decide"),
    "ok_103": ("103 divides the difference 206 − 0 of H₄₅",
               "example : (0 : ℤ) ∈ H45Z ∧ (206 : ℤ) ∈ H45Z ∧ (103 : ℤ) ∣ 206 - 0 := by decide"),
    "nc_103": ("no difference of H₄₅ is divisible by 103 (would lower the W-trick bound below 103)",
               "example : ∀ a ∈ H45Z, ∀ c ∈ H45Z, a ≠ c → ¬ (103 : ℤ) ∣ a - c := by decide"),
    "ok_residue": ("B2's residue 74549147 is coprime to W23 on H₄₅",
                   "example : ∀ h ∈ H45, Nat.gcd (74549147 + h) W23 = 1 := by decide"),
    "nc_residue": ("the residue 74549148",
                   "example : ∀ h ∈ H45, Nat.gcd (74549148 + h) W23 = 1 := by decide"),
}
for name, (what, body) in cases.items():
    open(os.path.join(out, name + ".lean"), "w").write(f"{HDR}-- control: {what}\n{body}\n")
