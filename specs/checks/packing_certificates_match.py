"""Check that Solution/Packing.lean's certTable and BGP212/Packing.lean's settledRoots /
openRoots equal the exploratory ledger in specs/certificates/packing_a3a.json.
Run from the repository root: python3 -I specs/checks/packing_certificates_match.py"""
import json, re
L = json.load(open("specs/certificates/packing_a3a.json"))
sol = open("Solution/Packing.lean").read()
dat = open("BGP212/Packing.lean").read()
def roots(name):
    body = dat[dat.index(f"def {name}"):]
    body = body[body.index("[") : body.index("]") + 1]
    return [(c, int(m), int(mp)) for c, m, mp in re.findall(r"\(\.(\w), (\d+), (\d+)\)", body)]
table = sol[sol.index("def certTable"):]
table = table[table.index("[") : table.index(" ]") + 2]
rows = re.findall(r"\(\.(\w), (\d+), (\d+), \[([\d, ]*)\], \[([\d, ]*)\]\)", table)
lean_certs = {(c, int(m), int(mp)): ([int(x) for x in a.split(",") if x.strip()],
                                     [int(x) for x in b.split(",") if x.strip()]) for c, m, mp, a, b in rows}
json_certs = {}
for x in L["certificates"]:
    if x["cond"] == "D":
        continue
    b = x["bins"]
    json_certs[(x["cond"], x["m"], x["m_prime"])] = (b.get("A1", b.get(x["cond"])), b.get("A2", []) if x["cond"] == "A" else [])
assert roots("settledRoots") == [tuple(r) for r in L["settled"]], "settledRoots differ"
assert roots("openRoots") == [tuple(r) for r in L["open"]], "openRoots differ"
assert lean_certs == json_certs, "certificate table differs"
print(f"match: {len(roots('settledRoots'))} settled, {len(roots('openRoots'))} open, {len(lean_certs)} certificates")
