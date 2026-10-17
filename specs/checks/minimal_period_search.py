"""B2 investigation: least positive period of the multi-shift accepted set."""
from math import gcd, prod
import random
def pf(n):
    out,p=[],2
    while p*p<=n:
        if n%p==0:
            out.append(p)
            while n%p==0: n//=p
        p+=1
    if n>1: out.append(n)
    return out
def R(m,N): return prod(p for p in pf(N) if m%p)
def nu(p,H): return len({(-h)%p for h in H})
def acc(m,N,a,H,n): return (n-a)%m==0 and all(gcd(n+h,N)==1 for h in H)
def least_period(m,N,a,H):
    T=m*R(m,N); S=[acc(m,N,a,H,n) for n in range(3*T+5)]
    for t in range(1,T+1):
        if all(S[n]==S[n+t] for n in range(2*T)): return t
rng=random.Random(7); stats={"nonempty_H_nonempty_set":[0,0],"empty_H":[0,0],"empty_set":[0,0]}
examples={}
for _ in range(4000):
    m,N=rng.randint(1,12),rng.randint(1,40); a=rng.randint(-10,10)
    H=rng.sample(range(-6,7),rng.randint(0,4)); T=m*R(m,N)
    t=least_period(m,N,a,H); nonempty=any(acc(m,N,a,H,n) for n in range(T))
    key="empty_H" if not H else ("nonempty_H_nonempty_set" if nonempty else "empty_set")
    stats[key][0]+=1
    if t==T: stats[key][1]+=1
    elif key not in examples: examples[key]=(m,N,a,H,T,t)
print("case: [cases, cases with least period = Tmin]"); print(stats); print("first examples with least period < Tmin:", examples)
