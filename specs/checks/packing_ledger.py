"""A3a ledger generator (exploratory; the Lean checker re-derives every settled root).
Semantics match Solution/Packing.lean: a root (c, m, m') is settled when some nonempty
set S of bins satisfies  B_m + B_m' <= sum_{S} cap - (|S| - 1) * s(m, m'),
s(m, m') = max(B_m - (m-1) delta, B_m' - (m'-1) delta), and every bin capacity is >= 0.
Condition A needs both of its partitions. Condition D must hold for every (gamma, omega0)
in its box; for a fixed S the bound is affine, so the four corners decide it."""
from fractions import Fraction as F
from itertools import combinations
import json, sys
A1=F(257,1000); d=F(41,2500); e=F(1,10**10); x1=F(19,50); x2=F(2,5); x3=F(2,5)
Bt=[777,794,875,917,953,983,1016,1042,1063,1081]
def B(m): return F(0) if m==0 else (F(Bt[m-1],5000) if m<=10 else F(1081,5000))
w=A1-F(1,4)
caps={
 "A1":[x1-2*e, F(1,6)-4*w-2*e],
 "A2":[F(1,2)-2*w-2*e, F(1,14)-F(68,14)*w-2*e],
 "B": [F(2,5)+F(24,5)*w+F(7,5)*d-2*e, F(1,14)-F(24,7)*w-2*e],
 "C": [F(1,3)+F(24,3)*w+F(7,3)*d-4*e, F(1,10)-F(34,5)*w-F(7,5)*d-4*e, 2*w+d-4*e],
 "E": [1-6*w-F(3,2)*x3-2*e, F(5,2)*w+F(3,8)*x3-2*e],
}
def capsD(g,o): return [g-2*d-8*o-e, F(1,2)-g-2*o-e, 4*o+d-e, 8*o]
gbox=[x2-e, F(1,3)+8*w+F(7,3)*d+3*e]; obox=[F(0), w]
corners=[(g,o) for g in gbox for o in obox]
def smax(m,mp): return max(B(m)-(m-1)*d, B(mp)-(mp-1)*d)
def find(cl, T, s):
    if any(c<0 for c in cl): return None
    for k in range(1,len(cl)+1):
        for S in combinations(range(len(cl)),k):
            if T <= sum(cl[i] for i in S)-(k-1)*s: return list(S)
    return None
def findD(T,s):
    for k in range(1,5):
        for S in combinations(range(4),k):
            if all(min(capsD(*c))>=0 for c in corners) and all(T <= sum(capsD(*c)[i] for i in S)-(k-1)*s for c in corners):
                return list(S)
    return None
settled=[]; open_=[]; certs=[]
for c in "ABCDE":
  for m in range(1,14):
    for mp in range(m,14):
      T=B(m)+B(mp); s=smax(m,mp)
      if c=="A":
          S1=find(caps["A1"],T,s); S2=find(caps["A2"],T,s); ok=S1 is not None and S2 is not None; cert={"A1":S1,"A2":S2}
      elif c=="D":
          S=findD(T,s); ok=S is not None; cert={"D":S}
      else:
          S=find(caps[c],T,s); ok=S is not None; cert={c:S}
      (settled if ok else open_).append((c,m,mp))
      if ok: certs.append({"cond":c,"m":m,"m_prime":mp,"bins":cert,"total_bound":str(T),"s":str(s)})
print(len(settled),len(open_),len(settled)+len(open_))
from collections import Counter
print("settled by condition", dict(Counter(r[0] for r in settled)))
print("D settled:", [r for r in settled if r[0]=="D"], [x for x in certs if x["cond"]=="D"])
json.dump({"settled":settled,"open":open_,"certificates":certs}, open(sys.argv[1],"w"), indent=1)
