"""Generate the A3c certificate trees for the 43 condition (D) roots of Lemma 7.10.

Exploratory tooling, outside the trusted base: SciPy (HiGHS LP and MILP) proposes cuts,
assignments and dual supports; every multiplier is then re-solved in exact rational
arithmetic and every tree is re-checked exactly here before it is written. The Lean kernel
re-checks everything again (`rowC`, Solution/PackingCertC.lean); nothing below is trusted.

Usage, from the repository root:
  python3 -I specs/checks/packing_a3c_generate.py specs/certificates/packing_a3c.json [--jobs J]

Method (lazy point generation with load-hyperplane cuts):
* A cell is the A3b base cell (both sides sorted, last coordinate >= δ, side sums <= B₁,ₘ,
  the full (γ, ω₀) box of Proposition 7.8 (D)) plus the cuts on the path to it. The
  coordinates are v = sorted side 1 ++ sorted side 2 ++ [γ, ω₀]; the constraint order matches
  `baseCell` in Solution/PackingCert.lean.
* At a cell, a MILP finds an assignment of the coordinates to the four bins that fits every
  sample point collected so far. An LP maximises each bin's load minus capacity over the
  whole cell. If no bin can overflow, the leaf is certified with exact Farkas multipliers
  (LP dual support, re-solved exactly). Otherwise the LP maximiser joins the sample points.
* When the sample points admit no common assignment, the cell is cut along the load
  hyperplane `load_k(a)(v) = cap_k(γ, ω₀)` of an assignment `a` that failed on bin k. The
  cut vector is integral (0/1 on the coordinates, small integers on (γ, ω₀)), and the side
  on which bin k fits is exactly where `a` stays a candidate.
* A cell with no point gets an exact Farkas infeasibility certificate (`empty`).
"""
import json, sys
from fractions import Fraction as F
from multiprocessing import Pool
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds, linprog

sys.setrecursionlimit(100000)

# Table 3 parameters (BGP212/Params.lean) and Proposition 7.8 (D).
A1 = F(257, 1000); d = F(41, 2500); e = F(1, 10**10)
Bt = [777, 794, 875, 917, 953, 983, 1016, 1042, 1063, 1081]
def B(m): return F(Bt[m - 1], 5000) if m <= 10 else F(1081, 5000)
w = (A1 + A1) / 2 - F(1, 4)
GLO, GHI = F(2, 5) - e, F(1, 3) + 8 * w + F(7, 3) * d + 3 * e
# cap_k(γ, ω₀) = CK[k] − EXTRA[k]·[γ, ω₀]   (cdD in Solution/PackingCert.lean)
EXTRA = [[F(-1), F(8)], [F(1), F(2)], [F(0), F(-4)], [F(0), F(-8)]]
CK = [-2 * d - e, F(1, 2) - e, d - e, F(0)]
OPEN = [(1, 3), (1, 4), (2, 2), (2, 3), (2, 4), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7),
        (4, 4), (4, 5), (4, 6), (4, 7), (4, 8), (5, 5), (5, 6), (5, 7), (5, 8), (5, 9),
        (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (7, 7), (7, 8), (7, 9), (7, 10), (7, 11),
        (8, 8), (8, 9), (8, 10), (8, 11), (9, 9), (9, 10), (9, 11), (10, 10), (10, 11),
        (10, 12), (11, 11), (11, 12), (12, 12)]
MAXDEPTH = 80

def side_cons(m, Bm):
    cs = []
    for i in range(m - 1):
        v = [F(0)] * m; v[i] = F(-1); v[i + 1] = F(1); cs.append((v, F(0)))
    v = [F(0)] * m; v[m - 1] = F(-1); cs.append((v, -d))
    cs.append(([F(1)] * m, Bm))
    return cs

def base_cell(m, mp):
    cs = [(v + [F(0)] * (mp + 2), b) for v, b in side_cons(m, B(m))]
    cs += [([F(0)] * m + v + [F(0)] * 2, b) for v, b in side_cons(mp, B(mp))]
    z = [F(0)] * (m + mp)
    cs += [(z + [F(-1), F(0)], -GLO), (z + [F(1), F(0)], GHI),
           (z + [F(0), F(-1)], F(0)), (z + [F(0), F(1)], w)]
    return cs

def target(a, k):
    return [F(1) if x == k else F(0) for x in a] + EXTRA[k]

def neg(c): return ([-x for x in c[0]], -c[1])

def lp_max(cell, c):
    A = np.array([[float(x) for x in a] for a, _ in cell])
    b = np.array([float(x) for _, x in cell])
    return linprog(-np.array([float(x) for x in c]), A_ub=A, b_ub=b,
                   bounds=[(None, None)] * len(c), method="highs")

def exact_solve(rows, rhs):
    """Solve Σ_j lam_j rows[j] = rhs exactly; None if inconsistent."""
    n, m = len(rhs), len(rows)
    M = [[rows[j][i] for j in range(m)] + [rhs[i]] for i in range(n)]
    piv = []; r = 0
    for col in range(m):
        p = next((i for i in range(r, n) if M[i][col] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]; pv = M[r][col]; M[r] = [x / pv for x in M[r]]
        for i in range(n):
            if i != r and M[i][col] != 0:
                f = M[i][col]; M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(col); r += 1
    if any(M[i][m] != 0 for i in range(r, n)): return None
    lam = [F(0)] * m
    for i, col in enumerate(piv): lam[col] = M[i][m]
    return lam

def farkas(cell, c, rhs):
    """Exact sparse multipliers λ ≥ 0 with Σλ a = c and Σλ b ≤ rhs, or None."""
    for j, (a, b) in enumerate(cell):
        if a == c and b <= rhs: return [(j, F(1))]
    r = lp_max(cell, c)
    if r.status != 0: return None
    mu = -r.ineqlin.marginals
    for tol in (1e-11, 1e-9, 1e-7):
        supp = [j for j, x in enumerate(mu) if x > tol]
        lam = exact_solve([cell[j][0] for j in supp], c)
        if lam is None or any(l < 0 for l in lam): continue
        if sum(l * cell[j][1] for l, j in zip(lam, supp)) <= rhs:
            return [(j, l) for l, j in zip(lam, supp) if l != 0]
    return None

def infeasible(cell):
    """Exact λ ≥ 0 with Σλ a = 0 and Σλ b < 0, or None."""
    N = len(cell[0][0])
    A = np.array([[float(x) for x in a] for a, _ in cell]); b = np.array([float(x) for _, x in cell])
    r = linprog(np.zeros(len(cell)), A_eq=np.vstack([A.T, b.reshape(1, -1)]),
                b_eq=np.concatenate([np.zeros(N), [-1.0]]), bounds=[(0, None)] * len(cell),
                method="highs")
    if r.status != 0: return None
    supp = [j for j, x in enumerate(r.x) if x > 1e-11]
    lam = exact_solve([cell[j][0] + [cell[j][1]] for j in supp], [F(0)] * N + [F(-1)])
    if lam is None or any(l < 0 for l in lam): return None
    return [(j, l) for l, j in zip(lam, supp) if l != 0]

def feasible_point(cell):
    r = lp_max(cell, [F(0)] * len(cell[0][0]))
    return None if r.status != 0 else r.x

def in_cell(cell, p, tol=1e-12):
    return all(sum(float(a[i]) * p[i] for i in range(len(p))) <= float(b) + tol for a, b in cell)

def milp_points(pts, n):
    K = 4; nv = n * K; A = []; lo = []; hi = []
    for i in range(n):
        row = [0] * nv
        for k in range(K): row[i * K + k] = 1
        A.append(row); lo.append(1); hi.append(1)
    for p in pts:
        for k in range(K):
            row = [0] * nv
            for i in range(n): row[i * K + k] = p[i]
            cap = float(CK[k]) - float(EXTRA[k][0]) * p[n] - float(EXTRA[k][1]) * p[n + 1]
            A.append(row); lo.append(-np.inf); hi.append(cap - 1e-9)
    r = milp(np.zeros(nv), constraints=LinearConstraint(np.array(A), lo, hi),
             integrality=np.ones(nv), bounds=Bounds(0, 1))
    if r.status != 0: return None
    return [int(np.argmax([r.x[i * K + k] for k in range(K)])) for i in range(n)]

def overflows(cell, a, k):
    return -lp_max(cell, target(a, k)).fun > float(CK[k]) + 1e-7

def solve_cell(cell, pts, n, depth):
    if feasible_point(cell) is None:
        cert = infeasible(cell)
        return None if cert is None else ("empty", cert)
    pts = [p for p in pts if in_cell(cell, p)] or [feasible_point(cell)]
    cands = []
    for _ in range(60):
        a = milp_points(pts, n)
        if a is None: break
        viol = None; certs = []
        for k in range(4):
            c = target(a, k); r = lp_max(cell, c)
            if -r.fun > float(CK[k]) + 1e-7: viol = (r.x, k); break
            fk = farkas(cell, c, CK[k])
            if fk is None: viol = (r.x, k); break
            certs.append(fk)
        if viol is None: return ("leaf", a, certs)
        cands.append((a, viol[1])); pts.append(viol[0])
    if depth == 0: return None
    def fresh(a, k):
        c = (target(a, k), CK[k]); return c not in cell and neg(c) not in cell
    pick = next(((a, k) for a, k in reversed(cands) if fresh(a, k)), None)
    if pick is None:
        for p in reversed(pts):
            a = milp_points([p], n)
            if a is None: continue
            k = next((k for k in range(4) if fresh(a, k) and overflows(cell, a, k)), None)
            if k is not None: pick = (a, k); break
    if pick is None: return None
    a, k = pick; cut = (target(a, k), CK[k])
    L = solve_cell(cell + [cut], pts, n, depth - 1)
    if L is None: return None
    R = solve_cell(cell + [neg(cut)], pts, n, depth - 1)
    if R is None: return None
    return ("split", cut[0], cut[1], L, R)

# ---- exact re-check (mirrors checkTree2 in Solution/PackingCertC.lean) ----
def comb(cell, lam, N):
    vec = [F(0)] * N; rhs = F(0)
    for j, l in lam:
        assert 0 <= j < len(cell) and l >= 0
        vec = [x + l * y for x, y in zip(vec, cell[j][0])]; rhs += l * cell[j][1]
    return vec, rhs

def check(t, cell, n):
    N = n + 2
    if t[0] == "empty":
        vec, rhs = comb(cell, t[1], N); return vec == [F(0)] * N and rhs < 0
    if t[0] == "leaf":
        a, certs = t[1], t[2]
        if len(a) != n or len(certs) != 4 or any(not 0 <= x < 4 for x in a): return False
        for k in range(4):
            vec, rhs = comb(cell, certs[k], N)
            if vec != target(a, k) or rhs > CK[k]: return False
        return True
    _, av, b, L, R = t
    assert all(x.denominator == 1 for x in av) and len(av) == N
    return check(L, cell + [(av, b)], n) and check(R, cell + [neg((av, b))], n)

def count(t, kind):
    if t[0] == "split": return count(t[3], kind) + count(t[4], kind)
    return 1 if t[0] == kind else 0

def ser(t):
    if t[0] == "empty": return {"empty": [[j, str(l)] for j, l in t[1]]}
    if t[0] == "leaf":
        return {"leaf": t[1], "certs": [[[j, str(l)] for j, l in c] for c in t[2]]}
    return {"split": [int(x) for x in t[1]], "rhs": str(t[2]), "left": ser(t[3]), "right": ser(t[4])}

def work(r):
    m, mp = r
    t = solve_cell(base_cell(m, mp), [], m + mp, MAXDEPTH)
    if t is None or not check(t, base_cell(m, mp), m + mp): return r, None
    return r, t

if __name__ == "__main__":
    out = sys.argv[1]
    jobs = int(sys.argv[sys.argv.index("--jobs") + 1]) if "--jobs" in sys.argv else 1
    with Pool(jobs) as pool:
        res = dict(pool.map(work, OPEN, chunksize=1))
    proved, still = [], []
    for r in OPEN:
        t = res[r]
        if t is None: still.append(["D", *r]); print(r, "OPEN", flush=True); continue
        print(r, "leaves", count(t, "leaf"), "empty", count(t, "empty"), flush=True)
        proved.append({"cond": "D", "m": r[0], "m_prime": r[1], "tree": ser(t)})
    json.dump({"proved": proved, "open": still}, open(out, "w"))
    print("proved", len(proved), "open", len(still))
