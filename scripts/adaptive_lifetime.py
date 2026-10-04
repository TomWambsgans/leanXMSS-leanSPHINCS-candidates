#!/usr/bin/env python3
"""Lifetimes of the pruned leanSphincs candidate that stay at 127 bits against adaptive forgers.

The older estimate (`fors_security.py`, `scheme.py` before this script) bounded the *average* FORS
success rate of a fresh digest by 2^-127 per hash call. That is not enough. A forger first collects
its signatures and then decides how to spend its hash calls: on the FORS search when the realised
openings make it better than 2^-127 per call, and on the WOTS preimage search (2 / 2^128 per call)
otherwise. Its rate is then E[max(X, 1)] * 2^-127, where X is the realised FORS rate in units of
2^-127, and any positive E[(X - 1)^+] breaks the q / 2^127 bound for large q.

This script computes the largest number N of signatures for which the following argument, the one
formalised in `formal/sphincs`, proves q / 2^127. Each hash call is charged at most 2^-127: a hidden
chain guess plus a target hit (2 x 2^-128) for chain inputs, a target hit for tree and encoding
inputs, and for message-digest inputs the *forecast* that the digest ends up covered by FORS
openings, conditioned on everything revealed so far. That forecast must be at most 2^-127 in every
reachable state, except on bad events whose total probability fits in the slack left by key
generation, K * 2^-127 with K = 258 * 2^b + 2 * (26 - b) honest hash calls.

  * Occupancy. A signing call lands on a given kept leaf with probability at most i_occ * 2^-b,
    whatever the adversary pre-queried: a pre-queried randomiser is selected with the same
    probability as any other, so only an excess of cached digests of the signed message at that
    leaf over its fair share 2^-b helps, and that excess is at most a 1/16 fraction except with
    negligible probability. The bad events are "some leaf receives m0 signatures" and, for two
    levels mu, "n leaves each receive mu signatures", bounded by exponential moments of adaptive
    hit counts.
  * Forecast. Outside those events, the forecast of a fresh digest is at most a union bound over
    which current or future signatures cover which of its 24 FORS trees. Future signatures cover a
    block J of trees at the digest's leaf with probability at most i_cov * 2^(-b-10|J|); i_cov = 3.07
    counts the fresh choice, cached digests the adversary may steer the signer onto (at most a
    (1 + 1/16) multiple of their fair number), and digests it may still query. Summed over leaves
    with a chord bound below the first level, the exact worst load for the at most n - 1 leaves
    of each level (a leaf at load m may still receive m0 - 1 - m signatures), and
    s (N - s)^r <= N^(r+1) r^r / (r+1)^(r+1), the forecast must stay below 2^-127.

The bounds are deliberately the ones a proof can check; the true safe lifetimes are larger. The
`--estimate` option prints a heuristic, unproved reference: the N at which E[(X - 1)^+] reaches
2^-13.5, the excess the leanVM proof absorbs with its refined WOTS analysis, from a simulation in
which X only depends on per-leaf signature counts.
"""

import argparse
import itertools
import math
import random
from functools import lru_cache

LOG2E = 1 / math.log(2)
I_OCC = 1.07
I_COV = 3.07
KEEP = 24  # FORS trees
WIDTH = 1024  # FORS leaves per tree


@lru_cache(None)
def stirling(n, k):
    if n == k:
        return 1
    if k == 0 or k > n:
        return 0
    return k * stirling(n - 1, k) + stirling(n - 1, k - 1)


def log2_comb(n, k):
    return (math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)) * LOG2E


def keygen_calls(b):
    return 258 * 2**b + 2 * (26 - b)


def slack_log2(b):
    """log2 of the absolute slack K 2^-127 minus the seed term q 2^-256 < 2^-129, less a 2^-8 share
    reserved for the two cache-concentration events."""
    return math.log2(keygen_calls(b) * 2.0**-127 - 2.0**-129) + math.log2(1 - 2.0**-8)


def set_tail(b, N, leaves, mu, rate):
    """log2 of C(2^b, leaves) exp((c - 1) leaves rate N) / c^(leaves mu) at the optimal c >= 1, and c."""
    mean = leaves * rate * N
    c = max(1.0, mu / (rate * N))
    exponent = (c - 1) * mean * LOG2E - leaves * mu * math.log2(c)
    return log2_comb(2**b, leaves) + min(0.0, exponent), c


def leaf_forecasts(b, N, m0):
    """Per-leaf forecast numerators: G[m] for a leaf at load m that may still receive m0 - 1 - m
    signatures, and slope[mu] bounding (G[m] - G[0]) / m for every 1 <= m < mu (with N - s
    remaining signatures paid by s (N - s)^r <= N^(r+1) r^r / (r+1)^(r+1))."""
    y = I_COV * 2.0**-b
    coef = [[math.comb(KEEP, k) * stirling(k, r) * y**r for r in range(KEEP + 1)] for k in range(KEEP + 1)]
    G = [sum(coef[k][r] * N**r * m ** (KEEP - k) for k in range(KEEP + 1) for r in range(min(k, m0 - 1 - m) + 1))
         for m in range(m0)]
    slope = {}
    for mu in range(2, m0 + 1):
        total = 0.0
        for k in range(KEEP):
            for r in range(min(k, m0 - 1) + 1):
                if coef[k][r]:
                    peak = r**r / (r + 1) ** (r + 1) if r else 1.0
                    total += coef[k][r] * N ** (r + 1) * peak * min(mu - 1, m0 - 1 - r) ** (KEEP - 1 - k)
        slope[mu] = total
    return G, slope


def forecast_log2(b, G, slope, m0, levels):
    """log2 of the certified forecast bound for a fresh digest: a chord below the first level,
    then at most n - 1 leaves per level at their worst load."""
    bounds = [mu for mu, _ in levels] + [m0]
    total = 2**b * G[0] + slope[bounds[0]]
    for j, (mu, n) in enumerate(levels):
        total += (n - 1) * max(G[mu:bounds[j + 1]])
    return math.log2(total / float(WIDTH) ** KEEP) - 26


def fewest_leaves(b, N, mu, rate, budget):
    lo, hi = 2, 2**b
    if set_tail(b, N, hi, mu, rate)[0] > budget:
        return None
    while lo < hi:
        mid = (lo + hi) // 2
        if set_tail(b, N, mid, mu, rate)[0] <= budget:
            hi = mid
        else:
            lo = mid + 1
    return lo


def certify(b, N, depth=2):
    """Best (forecast, m0, levels, tails) proving N signatures at subtree height b, or None. Each
    level (mu, n) is the bad event that n leaves each receive mu signatures."""
    rate = I_OCC * 2.0**-b
    budget = slack_log2(b)
    best = None
    for m0 in range(16, 72):
        top, _ = set_tail(b, N, 1, m0, rate)
        if top > budget:
            continue
        share = math.log2(2.0**budget - 2.0**top) - math.log2(depth)
        counts = {mu: fewest_leaves(b, N, mu, rate, share) for mu in range(8, m0)}
        G, slope = leaf_forecasts(b, N, m0)
        for combo in itertools.combinations(range(8, m0), depth):
            if any(counts[mu] is None for mu in combo):
                continue
            levels = [(mu, counts[mu]) for mu in combo]
            phi = forecast_log2(b, G, slope, m0, levels)
            if best is None or phi < best[0]:
                best = (phi, m0, levels, top, [set_tail(b, N, n, mu, rate) for mu, n in levels])
    if best is None or best[0] > -127:
        return None
    return best


def max_signatures(b, precision=1000):
    lo, hi = 1, 2 ** (b + 4)
    while certify(b, hi) is not None:
        hi *= 2
    while hi - lo > max(1, lo // precision):
        mid = (lo + hi) // 2
        if certify(b, mid) is None:
            hi = mid
        else:
            lo = mid
    return lo


def simulated_excess(b, N, samples, seed=1):
    """E[(X - 1)^+] with X = 2^101 * sum over leaves of (1 - (1 - 1/1024)^m)^24 for Poisson loads."""
    rng = random.Random(seed)
    lam = N / 2**b
    scale = 2.0**101
    deterministic, random_terms = 0.0, []
    for m in range(int(lam + 40 * math.sqrt(lam) + 80)):
        mass = 2**b * math.exp(-lam + m * math.log(lam) - math.lgamma(m + 1))
        value = scale * (1 - (1 - 1 / WIDTH) ** m) ** KEEP
        if value < 1e-3 and mass * value < 1e-6:
            deterministic += mass * value
        elif mass > 1e-15:
            random_terms.append((mass, value))

    def poisson(mu):
        if mu > 50:
            return max(0, round(rng.gauss(mu, math.sqrt(mu))))
        limit, k, prod = math.exp(-mu), 0, 1.0
        while True:
            prod *= rng.random()
            if prod <= limit:
                return k
            k += 1

    total = 0.0
    for _ in range(samples):
        x = deterministic + sum(poisson(mu) * v for mu, v in random_terms)
        total += max(0.0, x - 1)
    return total / samples


def estimate(b, upper, samples):
    target = 2.0**-13.5
    lo, hi = 1, upper
    for _ in range(14):
        mid = (lo + hi) // 2
        if simulated_excess(b, mid, samples) <= target:
            lo = mid
        else:
            hi = mid
    return lo


REQUESTED = {26: 1200000000, 20: 23700000, 14: 460000, 13: 240000, 12: 125000, 10: 33}


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--b", type=int, nargs="+", default=list(REQUESTED), help="log2 kept leaves")
    ap.add_argument("--estimate", action="store_true", help="also print the unproved leanVM-style estimate")
    ap.add_argument("--samples", type=int, default=6000)
    x = ap.parse_args()
    print(f"i_occ = {I_OCC}, i_cov = {I_COV}; slack K 2^-127 with K = 258 2^b + 2 (26 - b)")
    for b in x.b:
        n = max_signatures(b)
        phi, m0, levels, top, tails = certify(b, n)
        levels_text = ", ".join(f"{count} leaves >= {mu} (2^{tail[0]:.1f})" for (mu, count), tail in zip(levels, tails))
        line = (f"b={b:2d}: provable lifetime {n:,} (2^{math.log2(n):.2f}); forecast 2^{phi:.2f}; "
                f"no leaf >= {m0} (2^{top:.1f}), {levels_text}; slack 2^{slack_log2(b):.1f}")
        if b in REQUESTED:
            line += f"; previously {REQUESTED[b]:,}"
        if x.estimate and b in REQUESTED and REQUESTED[b] > 1000:
            line += f"; unproved estimate ~{estimate(b, REQUESTED[b], x.samples):,}"
        print(line)


if __name__ == "__main__":
    main()
