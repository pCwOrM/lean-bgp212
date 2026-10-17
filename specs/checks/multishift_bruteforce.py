"""B0 brute-force checks: multi-shift GDT count, nonemptiness criterion, H45 readings."""
from math import gcd, prod
import random

def primefactors(n):
    out, p = [], 2
    while p * p <= n:
        if n % p == 0:
            out.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out

def nu(p, H):
    return len({(-h) % p for h in H})

def admissible(m, N, a, H):
    return all((a + h) % p for p in primefactors(gcd(m, N)) for h in H)

def R(m, N):
    return prod(p for p in primefactors(N) if m % p)

def accepted(m, N, a, H, n):
    return (n - a) % m == 0 and all(gcd(n + h, N) == 1 for h in H)

def check_random(trials=3000, seed=1):
    rng = random.Random(seed)
    bad = 0
    for _ in range(trials):
        m, N = rng.randint(1, 30), rng.randint(1, 60)
        a = rng.randint(-40, 40)
        H = rng.sample(range(0, 20), rng.randint(1, 4))
        T = m * R(m, N)
        b = rng.randint(0, 50)
        count = sum(accepted(m, N, a, H, n) for n in range(b, b + T))
        local = prod(p - nu(p, H) for p in primefactors(N) if m % p)
        expected = local if admissible(m, N, a, H) else 0
        nonempty_pred = admissible(m, N, a, H) and all(nu(p, H) < p for p in primefactors(N) if m % p)
        if count != expected or (count > 0) != nonempty_pred:
            bad += 1
    return bad

H45 = [0, 2, 12, 14, 24, 26, 30, 36, 44, 50, 54, 56, 60, 66, 72, 74, 80, 84, 92, 96, 102,
       110, 114, 116, 122, 126, 134, 140, 144, 150, 156, 162, 164, 170, 176, 180, 182, 186,
       192, 194, 200, 204, 206, 210, 212]

if __name__ == "__main__":
    print("random mismatches:", check_random())
    print("free classes p - nu_p(H45):",
          {p: p - nu(p, H45) for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]})
    W = prod([2, 3, 5, 7, 11, 13, 17, 19, 23])
    sols30 = [b for b in range(30) if all(gcd(b + h, 30) == 1 for h in H45)]
    print("b mod 30:", sols30)
    b = 74549147
    print("W =", W, "b =", b, "valid:", all(gcd(b + h, W) == 1 for h in H45), "b mod 30 =", b % 30)
