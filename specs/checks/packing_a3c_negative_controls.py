"""A3c negative controls for the certificate checker (outside the trusted base).

Usage, from the repository root (after `lake build Solution.PackingCertC`):
  python3 -I specs/checks/packing_a3c_negative_controls.py OUTDIR
  for f in OUTDIR/*.lean; do lake env lean "$f" && echo "$f ACCEPTED" || echo "$f REJECTED"; done

Writes one Lean file per control, each asking the kernel to run `rowC` on a tree for the
(D, 3, 3) root. `ok.lean` is the unmodified certificate and is accepted; every `nc*.lean`
file carries one corruption and is rejected (`decide` fails)."""
import json, copy, os, sys
from fractions import Fraction as F

out = sys.argv[1]
os.makedirs(out, exist_ok=True)
src = open("specs/checks/packing_a3c_emit.py").read()
g = {"F": F}
exec(src[src.index("def lam"):src.index("def cut")], g)   # the emitter's own term printer
term = g["term"]
C = json.load(open("specs/certificates/packing_a3c.json"))
row = next(p for p in C["proved"] if (p["m"], p["m_prime"]) == (3, 3))
m, mp = row["m"], row["m_prime"]

def first_leaf(t):
    while "split" in t: t = t["left"]
    return t

def write(name, t, what):
    open(os.path.join(out, name + ".lean"), "w").write(
        f"import Solution.PackingCertC\nopen BGP212.PackingCert\n-- control: {what}\n"
        f"example : rowC ({m}, {mp}, {term(t)}) = true := by decide +kernel\n")

write("ok", copy.deepcopy(row["tree"]), "unmodified (D, 3, 3) certificate: accepted")

t = copy.deepcopy(row["tree"]); L = first_leaf(t)
j, l = L["certs"][1][0]; L["certs"][1][0] = [j, str(F(l) * F(101, 100))]
write("nc1_multiplier", t, "one Farkas multiplier scaled by 101/100: rejected")

t = copy.deepcopy(row["tree"]); a = first_leaf(t)["leaf"]
a[a.index(0)] = 2
write("nc2_assignment", t, "one coordinate moved from bin 0 to bin 2: rejected")

t = copy.deepcopy(row["tree"]); x = t
while "split" in x["left"]: x = x["left"]
x["left"] = {"empty": x["left"]["certs"][0]}
write("nc3_forged_empty", t, "a feasible leaf claimed as an empty cell: rejected")

t = copy.deepcopy(row["tree"]); t["left"], t["right"] = t["right"], t["left"]
write("nc4_swapped_sides", t, "the two sides of the root cut swapped: rejected")

t = copy.deepcopy(row["tree"]); t["rhs"] = str(F(t["rhs"]) + F(1, 1000))
write("nc5_shifted_cut", t, "root cut threshold shifted by 1/1000: rejected")
