#!/usr/bin/env python3
"""How well an adversary tells a pruned key from a full one (leanSPHINCS.tex, the privacy of a pruned key).

THE GAME. The challenger tosses a bit beta and runs a signer:

    beta = 0 (full key)    every signature's leaf index is uniform over the 2^h leaves;
    beta = 1 (pruned key)  a kept set S of 2^b of the 2^h leaves is drawn uniformly at random, and every
                           signature's index is uniform over S.

The adversary sees the N signatures and outputs a guess; its advantage is

    Adv(N) = | Pr[A = 1 | beta = 1] - Pr[A = 1 | beta = 0] |.

The best advantage over all adversaries, computationally unbounded ones included, is by definition the
statistical distance between the two transcript distributions, and that is what this script computes.

TWO MODELLING STEPS, both of them assumptions about the scheme, not about the game:

  - the kept set is pseudorandom (derived from the seed), and is treated here as uniformly random; a real
    adversary's advantage is this plus its advantage against that derivation;
  - given the indices, the rest of a signature carries nothing: the surrogate nodes of a pruned key are
    outputs of the seed's PRF where a full key has real hashes, and the chain values and paths are
    distributed alike. So the transcript reduces to the N indices.

WHY A REPEAT IS THE WHOLE STORY. S is a uniformly random subset, so conditioned on a collision pattern
with k distinct values, those values are a uniform k-tuple of distinct leaves under BOTH bits: the values
themselves carry no information. The observation is therefore the pattern alone, whose probability
depends only on k:

    P_M(k) = Stirling2(N, k) * M (M-1) ... (M-k+1) / M^N        (M = 2^b pruned, M = 2^h full)

    Adv(N) = 1/2 * sum_k | P_{2^b}(k) - P_{2^h}(k) |.

Both laws put their mass on k = N (no repeat yet), so the sum collapses to the difference of the
no-repeat probabilities, prod_{i<N} (1 - i/M); --check verifies that against the full Stirling sum.

WHY "ANSWER AT THE FIRST REPEAT" IS OPTIMAL, not merely natural. The best test is the likelihood ratio
R(k) = P_{2^b}(k) / P_{2^h}(k), which says "pruned" exactly when R(k) > 1. The Stirling factor cancels, so

    R(k+1) / R(k) = (2^b - k) / (2^h - k) < 1,

i.e. R decreases in k and the test is a threshold on k. The threshold sits between N-1 and N whenever
N is well below 2^b: R(N) = prod_{i<N} (1 - i/2^b) / (1 - i/2^h) < 1, while one repeat multiplies the
ratio by (2^h - N + 1) / (2^b - N + 1), about 2^(h-b), which carries R(N-1) far above 1. So the optimal
test is exactly "pruned iff some index repeats", and its advantage is the distance computed here.
--check prints both ratios; the argument needs N << 2^b, which every N plotted satisfies.
To first order Adv(N) = N^2 / 2^(b+1), so it reaches a threshold d after about sqrt(2d) * 2^(b/2)
signatures, and no N is private in the cryptographic sense: N = 2 already gives 2^-b.

WITH THE SEMI-TRUSTED STATE (same section). The signer keeps the set S of leaves it has already signed
and, when the grind lands on one of them again, accepts it only with some probability beta, otherwise
keeps grinding. Every attempt yields a uniform kept leaf, so with s = |S| already used,

    Pr[repeat] = s beta / ((2^b - s) + s beta),        a full key's rate being s / 2^h.

A CONSTANT beta = 2^(b-h) does not meet that rate. It is calibrated for an empty S, while rejection hands
the mass it removes back to the same 2^b candidates, so the repeat rate comes out too high by the
normaliser Z = 1 - s/2^b (1 - 2^(b-h)) -- the same factor as the grinding price, 2 at s = 2^(b-1).
Solving the equation instead gives the acceptance that is exact at every step,

    beta(s) = (2^b - s) / (2^h - s),

which is 2^(b-h) at s = 0 and half of it at s = 2^(b-1). The observation is the collision pattern, a
Markov chain on s, so matching Pr[repeat | s] at every step makes the two chains identical and the
advantage exactly zero rather than merely small. Grinding costs the same either way, acceptance being
dominated by the fresh leaves: 1/(1 - s/2^b) times the nominal 2^(h-b), twice the nominal at s = 2^(b-1),
which is the only reason to stop there. state_advantage() runs both chains; at b = 12, h = 24 and 2048
signatures the constant rule leaves 0.058 of advantage, beta(s) none.
"""

import argparse
import math
import os
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "formal", "sphincs", "scripts"))
import forest_certificates as fc

HEIGHTS = (22, 24, 26, 28)
PRUNED = (8, 10, 12, 13, 14, 20)


def no_repeat(n, M):
    """P(the n draws from a set of size M are all distinct)."""
    if n > M:
        return 0.0
    return math.exp(sum(math.log1p(-i / M) for i in range(n)))


def distance(n, b, h):
    """The best distinguisher's advantage after n signatures: the statistical distance between the
    index streams of a pruned key and of a full key."""
    return no_repeat(n, 2 ** h) - no_repeat(n, 2 ** b)


def distance_exact(n, b, h):
    """The same from the full sum over partitions, in exact arithmetic (small n only)."""
    s = [[0] * (n + 1) for _ in range(n + 1)]
    s[0][0] = 1
    for i in range(1, n + 1):
        for k in range(1, i + 1):
            s[i][k] = s[i - 1][k - 1] + k * s[i - 1][k]

    def probs(M):
        out, fall = [Fr(0)] * (n + 1), Fr(1)
        for k in range(n + 1):
            if k:
                fall *= Fr(M - k + 1, M)
            out[k] = Fr(s[n][k]) * fall / Fr(M ** (n - k))
        return out

    pb, ph = probs(2 ** b), probs(2 ** h)
    return float(sum(abs(x - y) for x, y in zip(pb, ph)) / 2)


def log_ratio(k, n, b, h):
    """log2 of the likelihood ratio P_{2^b}(k) / P_{2^h}(k) for k distinct indices in n signatures.

    The Stirling factor cancels, leaving the falling factorials: prod_{i<k} (2^b - i) / (2^h - i), times
    2^((h-b)n) from the two denominators. In logs, so that large n does not overflow.
    """
    r = (h - b) * n
    for i in range(k):
        r += math.log2(2 ** b - i) - math.log2(2 ** h - i)
    return r


def state_advantage(n, b, h, rule="exact"):
    """The best distinguisher's advantage after n signatures when the signer runs the rejection rule.

    Exact, by carrying the law of "s distinct leaves after j signatures" for the rule's signer and for a
    full key, and taking the distance between them: the collision pattern is the whole observation, and
    it is a Markov chain on s. rule="const" is the constant beta = 2^(b-h), rule="exact" is beta(s).
    """
    full, kept = {0: 1.0}, {0: 1.0}
    for _ in range(n):
        nf, nk = {}, {}
        for s_, pr in full.items():
            q = s_ / 2.0 ** h
            nf[s_] = nf.get(s_, 0.0) + pr * q
            nf[s_ + 1] = nf.get(s_ + 1, 0.0) + pr * (1 - q)
        for s_, pr in kept.items():
            beta = 2.0 ** (b - h) if rule == "const" else (2 ** b - s_) / (2 ** h - s_)
            q = s_ * beta / ((2 ** b - s_) + s_ * beta)
            nk[s_] = nk.get(s_, 0.0) + pr * q
            nk[s_ + 1] = nk.get(s_ + 1, 0.0) + pr * (1 - q)
        full, kept = nf, nk
    return sum(abs(kept.get(s_, 0.0) - full.get(s_, 0.0)) for s_ in set(full) | set(kept)) / 2


def signatures_until(b, h, d):
    """The largest N whose statistical distance to a full key is still at most d (binary search)."""
    lo, hi = 1, 2
    while distance(hi, b, h) <= d:
        lo, hi = hi, hi * 2
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if distance(mid, b, h) <= d:
            lo = mid
        else:
            hi = mid
    return lo


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--delta", type=float, default=0.1, help="advantage tolerated (default 0.1)")
    ap.add_argument("--h", type=int, nargs="+", choices=HEIGHTS, default=list(HEIGHTS))
    ap.add_argument("--check", action="store_true", help="check the first-order figures against the full sum")
    a = ap.parse_args()

    if a.check:
        print("advantage, the repeat term against the full partition sum:")
        for (n, b, h) in ((10, 12, 24), (29, 12, 24), (60, 14, 24), (120, 14, 26)):
            print("  N=%3d b=%2d h=%2d:  %.9f  %.9f" % (n, b, h, distance(n, b, h), distance_exact(n, b, h)))
        print()
        print("likelihood ratio at the threshold: log2 R(N) < 0 < log2 R(N-1), so the repeat test is optimal:")
        for (n, b, h) in ((10, 12, 24), (29, 12, 24), (75, 12, 24), (120, 14, 26)):
            print("  N=%3d b=%2d h=%2d:  log2 R(N) = %+.4f   log2 R(N-1) = %+.2f"
                  % (n, b, h, log_ratio(n, n, b, h), log_ratio(n - 1, n, b, h)))
        print()
        print("with the state, a constant beta = 2^(b-h) against the exact beta(s), at b = 12, h = 24:")
        for n in (500, 1024, 2048):
            print("  N=%5d:  constant %.4f   beta(s) %.2e"
                  % (n, state_advantage(n, 12, 24, "const"), state_advantage(n, 12, 24)))
        print()

    print("Signatures a pruned key can make while the best distinguisher's advantage against a full key")
    print("stays at most %g.\n" % a.delta)
    print("  %2s %3s  %9s  %12s  %7s   %10s  %10s"
          % ("h", "b", "private", "lifetime", "share", "budget", "const"))
    for h in a.h:
        for b in [x for x in PRUNED if x < h]:
            n = signatures_until(b, h, a.delta)
            life = fc.lifetime(h, "pruned", b)
            budget = 2 ** (b - 1)
            adv = "%.3f" % state_advantage(budget, b, h, "const") if budget <= 4096 else "-"
            print("  %2d %3d  %9d  %12.3g  %6.2f%%   %10d  %10s"
                  % (h, b, n, life, 100.0 * n / life, budget, adv))
        print()
    print("'private' is what a key makes with no state of its own; 'budget' is the 2^(b-1) of the rejection")
    print("rule, past which grinding costs more than twice the nominal 2^(h-b). 'const' is what a constant")
    print("beta = 2^(b-h) still leaves at that point ('-' where the chain is too long to run); the exact")
    print("beta(s) = (2^b - s)/(2^h - s) leaves nothing, at the same grinding cost: --check compares them.")
    print("A full key (b = h) is the standard scheme itself, so its advantage is zero by definition.")


if __name__ == "__main__":
    main()
