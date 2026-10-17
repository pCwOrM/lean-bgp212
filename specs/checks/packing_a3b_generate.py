"""A3b certificate generator (exploratory; OUTSIDE the trusted base).

Usage, from the repository root:
  python3 -I specs/checks/packing_a3b_generate.py specs/certificates/packing_a3a.json OUT.json
Reads A3a's open roots, writes subdivision trees with exact sparse Farkas certificates, and
re-checks every tree in exact Fractions with the same rules as the Lean checker `rowB`.
Candidate partitions come from scipy.optimize.milp (HiGHS); the solver only proposes, and
nothing it returns is trusted: Python re-verifies exactly, and the Lean kernel re-verifies
again from the emitted data.
"""
"""A3b exploration: for each open root, find ONE assignment of sorted coordinates to bins valid
at every vertex of the sorted cell (and every (gamma, omega0) corner for D). MILP finds a
candidate; exact Fraction arithmetic then re-verifies it at every vertex."""
import json, sys, numpy as np
from fractions import Fraction as F
from scipy.optimize import milp, LinearConstraint, Bounds
A1=F(257,1000); d=F(41,2500); e=F(1,10**10); x1=F(19,50); x2=F(2,5); x3=F(2,5)
Bt=[777,794,875,917,953,983,1016,1042,1063,1081]
def B(m): return F(0) if m==0 else (F(Bt[m-1],5000) if m<=10 else F(1081,5000))
w=A1-F(1,4)
capsC={"A1":[x1-2*e, F(1,6)-4*w-2*e],"A2":[F(1,2)-2*w-2*e, F(1,14)-F(68,14)*w-2*e],
 "C":[F(1,3)+F(24,3)*w+F(7,3)*d-4*e, F(1,10)-F(34,5)*w-F(7,5)*d-4*e, 2*w+d-4*e],
 "E":[1-6*w-F(3,2)*x3-2*e, F(5,2)*w+F(3,8)*x3-2*e]}
def capsD(g,o): return [g-2*d-8*o-e, F(1,2)-g-2*o-e, 4*o+d-e, 8*o]
corners=[(g,o) for g in [x2-e, F(1,3)+8*w+F(7,3)*d+3*e] for o in [F(0),w]]
def side_vertices(m,Bm):
    R=Bm-m*d; vs=[[d]*m]
    for j in range(1,m+1): vs.append([d+R/j]*j+[d]*(m-j))
    return vs
def vertices(m,mp):
    return [a+b for a in side_vertices(m,B(m)) for b in side_vertices(mp,B(mp))]
def solve(capsets, m, mp):
    """capsets: list of cap lists (one per (gamma,omega0) corner, or one for constant caps)."""
    n=m+mp; k=len(capsets[0]); V=vertices(m,mp)
    nv=n*k; A=[]; lo=[]; hi=[]
    for i in range(n):   # each coordinate in exactly one bin
        row=[0]*nv
        for b in range(k): row[i*k+b]=1
        A.append(row); lo.append(1); hi.append(1)
    for caps in capsets:
        for v in V:
            for b in range(k):
                row=[0]*nv
                for i in range(n): row[i*k+b]=float(v[i])
                A.append(row); lo.append(-np.inf); hi.append(float(caps[b])-1e-12)
    res=milp(c=np.zeros(nv), constraints=LinearConstraint(np.array(A),lo,hi), integrality=np.ones(nv), bounds=Bounds(0,1))
    if res.status!=0: return None
    assign=[int(np.argmax([res.x[i*k+b] for b in range(k)])) for i in range(n)]
    # exact re-verification at every vertex and corner
    for caps in capsets:
        for v in V:
            for b in range(k):
                if sum(v[i] for i in range(n) if assign[i]==b) > caps[b]: return "INEXACT"
    return assign

import json, sys
from fractions import Fraction as F
gl,gh=x2-e, F(1,3)+8*w+F(7,3)*d+3*e
CAP={  # condition part -> (extraT_k list, c_k list); caps are constant for A1, A2, C, E
 "A1":([[]]*2, capsC["A1"]), "A2":([[]]*2, capsC["A2"]), "C":([[]]*3, capsC["C"]), "E":([[]]*2, capsC["E"]),
 "D":([[F(-1),F(8)],[F(1),F(2)],[F(0),F(-4)],[F(0),F(-8)]], [-2*d-e, F(1,2)-e, d-e, F(0)]),
}
def side_cons(m,Bm):
    cs=[]
    for i in range(m-1):
        v=[F(0)]*m; v[i]=F(-1); v[i+1]=F(1); cs.append((v,F(0)))
    v=[F(0)]*m; v[m-1]=F(-1); cs.append((v,-d))
    cs.append(([F(1)]*m,B(m)))
    return cs
def base_cell(m,mp,extra):
    N=m+mp+extra; cs=[]
    for v,b in side_cons(m,B(m)): cs.append((v+[F(0)]*(mp+extra),b))
    for v,b in side_cons(mp,B(mp)): cs.append(([F(0)]*m+v+[F(0)]*extra,b))
    if extra==2:
        z=[F(0)]*(m+mp)
        cs+= [(z+[F(-1),F(0)],-gl),(z+[F(1),F(0)],gh),(z+[F(0),F(-1)],F(0)),(z+[F(0),F(1)],w)]
    return cs
def prefix_cert(cmask, off, m):
    """Farkas multipliers on a sorted side block for target sum_{i in mask} y_i."""
    C=[0]*(m+1)
    for i in range(m): C[i+1]=C[i]+cmask[i]
    mu=max([F(0)]+[F(C[i],i) for i in range(1,m+1)])
    lam=[]
    for j in range(1,m+1):           # z_j constraint index: adjacency j-1 (j<m) or lower (j=m)
        l=j*mu-C[j]
        if l: lam.append((off+j-1,l))
    if mu: lam.append((off+m,mu))
    return lam
def leaf_cert(assign,part,m,mp,cell,box_idx):
    extraT,cks=CAP[part]; K=len(cks); certs=[]
    for k in range(K):
        mask=[1 if a==k else 0 for a in assign]
        lam=prefix_cert(mask[:m],0,m)+prefix_cert(mask[m:],m+1,mp)
        if extraT[k]:   # box part: pick the active bound constraint for each extra coordinate
            for t,(lo_i,hi_i) in zip(extraT[k],box_idx):
                if t>0: lam.append((hi_i,t))
                elif t<0: lam.append((lo_i,-t))
        certs.append(lam)
    return certs
def check_farkas(cell,lam,target,rhs):
    N=len(target); comb=[F(0)]*N; r=F(0)
    for j,l in lam:
        if l<0 or j>=len(cell): return False
        a,b=cell[j]; comb=[comb[i]+l*a[i] for i in range(N)]; r+=l*b
    return comb==target and r<=rhs
def check_tree(t,cell,part,m,mp):
    extraT,cks=CAP[part]
    if t[0]=="split":
        _,a,b,l,r=t
        return check_tree(l,cell+[(a,b)],part,m,mp) and check_tree(r,cell+[([-x for x in a],-b)],part,m,mp)
    _,assign,certs=t
    if len(assign)!=m+mp or any(not(0<=x<len(cks)) for x in assign) or len(certs)!=len(cks): return False
    for k in range(len(cks)):
        tgt=[F(1) if a==k else F(0) for a in assign]+list(extraT[k])
        if not check_farkas(cell,certs[k],tgt,cks[k]): return False
    return True
# ---- build trees ----
def build_const(part,m,mp):
    caps=CAP[part][1]; a=solve([caps],m,mp)
    if not isinstance(a,list): return None
    cell=base_cell(m,mp,0)
    return ("leaf",a,leaf_cert(a,part,m,mp,cell,[]))
def build_D(m,mp,depth):
    n=m+mp
    def rec(cell,g0,g1,o0,o1,gidx,oidx,dep):
        cs=[capsD(g,o) for g in (g0,g1) for o in (o0,o1)]
        a=solve(cs,m,mp)
        if isinstance(a,list):
            return ("leaf",a,leaf_cert(a,"D",m,mp,cell,[gidx,oidx]))
        if dep==0: return None
        z=[F(0)]*n
        if (g1-g0)/(gh-gl) >= (o1-o0)/w:
            t=(g0+g1)/2; av=z+[F(1),F(0)]
            L_=rec(cell+[(av,t)],g0,t,o0,o1,(gidx[0],len(cell)),oidx,dep-1)
            if L_ is None: return None
            R_=rec(cell+[([-x for x in av],-t)],t,g1,o0,o1,(len(cell),gidx[1]),oidx,dep-1)
        else:
            t=(o0+o1)/2; av=z+[F(0),F(1)]
            L_=rec(cell+[(av,t)],g0,g1,o0,t,gidx,(oidx[0],len(cell)),dep-1)
            if L_ is None: return None
            R_=rec(cell+[([-x for x in av],-t)],g0,g1,t,o1,gidx,(len(cell),oidx[1]),dep-1)
        if L_ is None or R_ is None: return None
        return ("split",av,t,L_,R_)
    base=m+mp+2
    return rec(base_cell(m,mp,2),gl,gh,F(0),w,(base,base+1),(base+2,base+3),depth)
def leaves(t): return 1 if t[0]=="leaf" else leaves(t[3])+leaves(t[4])
L=json.load(open(sys.argv[1])); proved=[]; still=[]
for idx,(c,m,mp) in enumerate(L["open"]):
    print("root",idx,c,m,mp,flush=True)
    if c=="A":
        t1=build_const("A1",m,mp); t2=build_const("A2",m,mp); trees=[("A1",t1),("A2",t2)]
    elif c=="D":
        trees=[("D",build_D(m,mp,8))]
    else:
        trees=[(c,build_const(c,m,mp))]
    if all(t is not None for _,t in trees):
        n=m+mp; ex=2 if c=="D" else 0
        assert all(check_tree(t,base_cell(m,mp,ex),p,m,mp) for p,t in trees), (c,m,mp)
        proved.append((c,m,mp,trees))
    else: still.append((c,m,mp))
def ser(t):
    if t[0]=="leaf": return {"leaf":t[1],"certs":[[[j,str(l)] for j,l in c] for c in t[2]]}
    return {"split":[str(x) for x in t[1]],"rhs":str(t[2]),"left":ser(t[3]),"right":ser(t[4])}
out={"proved":[{"cond":c,"m":m,"m_prime":mp,"trees":{p:ser(t) for p,t in trees}} for c,m,mp,trees in proved],
     "open":still}
json.dump(out,open(sys.argv[2],"w"))
from collections import Counter
print("proved", len(proved), dict(Counter(p[0] for p in proved)), "open", len(still))
print("D leaves", sum(leaves(t) for c,m,mp,tr in proved if c=="D" for _,t in tr))
