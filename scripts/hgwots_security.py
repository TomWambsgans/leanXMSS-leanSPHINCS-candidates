#!/usr/bin/env python3
"""Exact reuse security of HG-WOTS ("Hogwots"), as modelled by J. Nick (x.com/n1ckler/status/2103500295003066614).

Key: k groups of s hash chains (distances 0..w-1 to the chain end). Each group's chain endpoints are hashed
into the start of a group chain (distances 0..w2-1); pk = hash of the k group-chain endpoints.
Codeword (uniform): a j-subset of hidden groups; each revealed group gets chain distances with sum dg;
the hidden groups get group-chain distances with total sum dh.
Signature: the s chain nodes of each revealed group and one group-chain node per hidden group,
i.e. (k-j)*s + j nodes of n bytes.

A forward-hashing adversary who saw r signatures can produce a target codeword iff
  (a) the target hides every group hidden in all r signatures,
  (b) every revealed target chain distance is <= the largest distance exposed on that chain,
  (c) every always-hidden group's target group-chain distance is <= the largest one exposed there.
cover(r) = P(uniform target derivable from r uniform signatures), computed exactly: given the hidden sets,
(b) factorizes over groups and (c) depends only on how many groups are always hidden; the hidden-set
patterns are summed with a dynamic program over signatures.

Security with a b-bit digest mapped onto codewords: the signer grinds g >= gmin = max(0, 128 - log2 nu) bits
to hit a valid codeword, and a forger's success per hash query after r uses is 2^-g * cover(r). So
security(r) = g + cov(r), with cov(r) = -log2 cover(r). This script prints log2 nu, gmin and cov(r).
"""

import argparse
import math
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product


@lru_cache(maxsize=None)
def count_bounded(bounds, total):
    """#tuples x with 0 <= x_c <= bounds[c] and sum x = total (bounds: sorted tuple)."""
    if total < 0 or any(b < 0 for b in bounds):
        return 0
    poly = [1]
    for b in bounds:
        new = [0] * min(len(poly) + b, total + 1)
        for i, c in enumerate(poly):
            if c:
                for d in range(min(b, total - i) + 1):
                    new[i + d] += c
        poly = new
    return poly[total] if total < len(poly) else 0


def n_tuples(m, W, D):
    return count_bounded((W - 1,) * m, D) if m > 0 else int(D == 0)


def multisets(m, W, lo, hi):
    """Nondecreasing m-tuples over [0, W-1] with lo <= sum <= hi, as [(value, multiplicity)]."""
    def rec(start, left, acc, total):
        if left == 0:
            if total >= lo:
                yield acc
            return
        for v in range(start, W):
            if total + v * left > hi:
                break
            for mu in range(1, left + 1):
                if total + v * mu > hi:
                    break
                yield from rec(v + 1, left - mu, acc + [(v, mu)], total + v * mu)
    yield from rec(0, m, [], 0)


def _perms(groups):
    n = math.factorial(sum(mu for _, mu in groups))
    for _, mu in groups:
        n //= math.factorial(mu)
    return n


def _ie(groups, width, W, total, power):
    """sum over S of (-1)^|S| count(coords in S bounded by value-1, the rest by W-1)^power."""
    acc = 0
    for sig in product(*[range(mu + 1) for _, mu in groups]):
        mult, bounds = 1, []
        for (v, mu), sg in zip(groups, sig):
            mult *= math.comb(mu, sg)
            bounds += [v - 1] * sg
        bounds = tuple(sorted(bounds + [W - 1] * (width - sum(sig))))
        acc += (-1) ** sum(sig) * mult * count_bounded(bounds, total) ** power
    return acc


@lru_cache(maxsize=None)
def p_rev(s, w, dg, m):
    """P(v <= max(v_1..v_m)) for i.i.d. uniform v's in {[0,w-1]^s, sum dg}."""
    if m == 0:
        return Fraction(0)
    num = sum(_perms(g) * _ie(g, s, w, dg, m) for g in multisets(s, w, dg, dg))
    return Fraction(num, n_tuples(s, w, dg) ** (m + 1))


@lru_cache(maxsize=None)
def q_hidden(j, w2, dh, a, r):
    """P(target <= max of r past vectors on a fixed set of a coordinates), vectors uniform in {[0,w2-1]^j, sum dh}."""
    if a == 0:
        return Fraction(1)
    num = 0
    for g in multisets(a, w2, max(0, dh - (j - a) * (w2 - 1)), dh):
        rest = dh - sum(v * mu for v, mu in g)
        compl = n_tuples(j - a, w2, rest)
        if compl:
            num += _perms(g) * compl * _ie(g, j, w2, dh, r)
    return Fraction(num, n_tuples(j, w2, dh) ** (r + 1))


def compositions(total, caps):
    if not caps:
        if total == 0:
            yield ()
        return
    for x in range(min(total, caps[0]) + 1):
        for rest in compositions(total - x, caps[1:]):
            yield (x,) + rest


def reveal_histograms(k, j, r):
    """Distribution of n = (n_0..n_r), n_m = #groups revealed by exactly m of r signatures."""
    dist = {(k,) + (0,) * r: 1.0}
    denom = math.comb(k, j)
    for step in range(r):
        new = {}
        for n, p in dist.items():
            for x in compositions(j, n[: step + 1]):  # hidden groups taken from classes 0..step
                ways = math.prod(math.comb(n[m], x[m]) for m in range(step + 1))
                nn = [0] * (r + 1)
                for m in range(step + 1):
                    nn[m] += x[m]
                    nn[m + 1] += n[m] - x[m]
                nn = tuple(nn)
                new[nn] = new.get(nn, 0.0) + p * ways / denom
        dist = new
    return dist


def cover(k, s, j, w, w2, dg, dh, r, q_max_multisets=60000):
    """cover(r). Returns (value, exact): exact is False if some non-negligible always-hidden term was
    bounded by 1 because it was too expensive (the value is then an upper bound)."""
    prev = [float(p_rev(s, w, dg, m)) for m in range(r + 1)]
    by_a = {}
    for n, p in reveal_histograms(k, j, r).items():
        a = n[0]
        if a > j:
            continue
        poly = [1.0]  # ways for the target to hide j - a more groups among groups revealed >= 1 times
        for m in range(1, r + 1):
            term = [math.comb(n[m], y) * prev[m] ** (n[m] - y) for y in range(n[m] + 1)]
            new = [0.0] * (len(poly) + len(term) - 1)
            for i, c in enumerate(poly):
                for y, t in enumerate(term):
                    new[i + y] += c * t
            poly = new
        if j - a < len(poly):
            by_a[a] = by_a.get(a, 0.0) + p * poly[j - a] / math.comb(k, j)
    total, exact = 0.0, True
    for a in sorted(by_a, key=lambda a: -by_a[a]):
        if a == 0:
            total += by_a[a]
        elif by_a[a] < 2.0**-40 * total:
            total += by_a[a]  # negligible: bound q by 1
        elif math.comb(w2 + a - 1, a) > q_max_multisets:
            total += by_a[a]
            exact = False
        else:
            total += by_a[a] * float(q_hidden(j, w2, dh, a, r))
    return total, exact


def log2_codewords(k, s, j, w, w2, dg, dh):
    return math.log2(math.comb(k, j)) + (k - j) * math.log2(n_tuples(s, w, dg)) + math.log2(n_tuples(j, w2, dh))


def _brute(k, s, j, w, w2, dg, dh, r):
    V = [v for v in product(range(w), repeat=s) if sum(v) == dg]
    U = [u for u in product(range(w2), repeat=j) if sum(u) == dh]
    C = [(frozenset(H), dict(zip([g for g in range(k) if g not in H], vs)), dict(zip(H, u)))
         for H in combinations(range(k), j) for vs in product(V, repeat=k - j) for u in U]

    def derivable(past, T):
        A = frozenset(range(k)).intersection(*[P[0] for P in past])
        if not A <= T[0]:
            return False
        for g, v in T[1].items():
            seen = [P[1][g] for P in past if g in P[1]]
            if not seen or any(v[c] > max(x[c] for x in seen) for c in range(s)):
                return False
        return all(T[2][g] <= max(P[2][g] for P in past) for g in A)
    hits = sum(derivable(p, T) for p in product(C, repeat=r) for T in C)
    return hits / len(C) ** (r + 1)


def selftest():
    ok = True
    for params, rs in [((3, 2, 1, 3, 3, 2, 1), (1, 2, 3)), ((1, 3, 0, 3, 3, 3, 0), (1, 2, 3)),
                       ((3, 1, 2, 4, 4, 2, 3), (1, 2, 3)), ((4, 2, 2, 3, 3, 2, 2), (1, 2)), ((4, 2, 1, 3, 4, 3, 2), (1, 2))]:
        for r in rs:
            b, (c, _) = _brute(*params, r), cover(*params, r)
            good = abs(b - c) < 1e-12
            ok &= good
            print(f"{'ok  ' if good else 'FAIL'} {params} r={r}: brute force {b:.10f}, exact {c:.10f}")
    return ok


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0], epilog=__doc__.split("\n\n", 1)[1],
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    for name, default in (("k", 26), ("s", 4), ("j", 16), ("w", 16), ("w2", 4)):
        ap.add_argument(f"--{name}", type=int, default=default)
    ap.add_argument("--dg", type=int, help="revealed-group distance sum (default: s(w-1)/2)")
    ap.add_argument("--dh", type=int, help="hidden group-chain distance sum (default: j(w2-1)/2)")
    ap.add_argument("--r", type=int, nargs="+", default=[2, 3, 4, 5, 6], help="numbers of uses")
    ap.add_argument("--n", type=int, default=16, help="node size in bytes (default 16)")
    ap.add_argument("--selftest", action="store_true", help="compare with brute-force enumeration")
    a = ap.parse_args()
    if a.selftest:
        raise SystemExit(0 if selftest() else 1)
    dg = a.dg if a.dg is not None else a.s * (a.w - 1) // 2
    dh = a.dh if a.dh is not None else a.j * (a.w2 - 1) // 2
    p = (a.k, a.s, a.j, a.w, a.w2, dg, dh)
    L = log2_codewords(*p)
    nodes = (a.k - a.j) * a.s + a.j
    print(f"HG-WOTS k={a.k} s={a.s} j={a.j} w={a.w} w2={a.w2} dg={dg} dh={dh}: {nodes} nodes = {nodes * a.n} B, "
          f"log2 nu = {L:.1f}, gmin = {max(0.0, 128 - L):.1f} bits")
    for r in a.r:
        c, exact = cover(*p, r)
        print(f"  r={r}: cov = -log2 cover = {-math.log2(c):6.1f} bits{'' if exact else '  (lower bound)'}")


if __name__ == "__main__":
    main()
