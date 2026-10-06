"""Exact check, on a small cyclic randomizer space, of the facts the v5 potential uses.

Positions Z_n, attempt limit L <= n, landing probability p, u = 1/n, I = u (1 - p) / p.
status: 0 unqueried, 1 queried non-landing, 2 queried landing.  t = (1 - p, 1, 0).
arrive(x) = u * sum_{j < L} prod_{1 <= i <= j} t(x - i): probability that the walk tries x.
Checked for random configurations:
  (D) sum over landed of arrive <= 1;
  (N) S := sum over landed of arrive <= A := u #queried + I #landed;
  (M) for an unqueried y and every landed rho: p arrive_L(rho) + (1 - p) arrive_N(rho) = arrive(rho),
      and arrive(y) does not depend on the status of y;
  (R) hence E[A' - S'] + p arrive(y) = (A - S) + (2 - p) u.
"""
import random
from fractions import Fraction as Fr

def arrive(st, n, L, p, x):
    t = (1 - p, Fr(1), Fr(0))
    tot = Fr(0); prod = Fr(1)
    for j in range(L):
        tot += prod
        prod *= t[st[(x - j - 1) % n]]
    return tot / n

def check(n, L, p, st):
    u = Fr(1, n); I = u * (1 - p) / p
    landed = [x for x in range(n) if st[x] == 2]
    S = sum(arrive(st, n, L, p, x) for x in landed)
    A = u * sum(1 for x in range(n) if st[x]) + I * len(landed)
    assert S <= 1, 'D'
    assert S <= A, ('N', st, L)
    for y in range(n):
        if st[y]: continue
        sL = list(st); sL[y] = 2; sN = list(st); sN[y] = 1
        M = arrive(st, n, L, p, y)
        assert arrive(sL, n, L, p, y) == M == arrive(sN, n, L, p, y)
        for r in landed:
            assert p * arrive(sL, n, L, p, r) + (1 - p) * arrive(sN, n, L, p, r) == arrive(st, n, L, p, r), 'M'
    return True

random.seed(1)
for trial in range(3000):
    n = random.choice([5, 8, 11, 16])
    L = random.choice([1, 2, n // 2, n - 1, n])
    p = Fr(1, random.choice([2, 3, 8, 64]))
    dens = random.random()
    st = [random.choice([0, 1, 1, 2]) if random.random() < dens else 0 for _ in range(n)]
    check(n, max(L, 1), p, st)
print('ok')
