#!/usr/bin/env python3
"""Security level of an SLH-DSA parameter set as a function of the number of signatures.

Implements the generic-attack estimate of the SPHINCS+ submission (Appendix A), as computed by:
  - C. Fenner, slh-dsa-rls, pkg/slhdsa/param.go (a Go port of S. Fluhrer's gamma.c), which is
    reference [5] of NIST SP 800-230 ipd: Poisson approximation, `--method poisson`;
  - M. Kudinov, J. Nick, "Hash-based Signature Schemes for Bitcoin", ePrint 2025/2203,
    security.sage in github.com/BlockstreamResearch/SPHINCS-Parameters: exact binomial,
    `--method exact` (default).

After q signatures, the adversary looks for a message whose FORS instance (hypertree leaf) has
already signed r times and whose k FORS indices all point to leaves those r signatures revealed:

    P(q) = sum_{r >= 1} C(q, r) 2^(-h r) (1 - 2^(-h))^(q - r) * (1 - (1 - 2^(-a))^r)^k

The FORS bound is -log2 P(q). The security level combines it with the 2^(-8n) generic hash
attack in one of two ways:
  max: min(8n, -log2 P)          used by both tools above (and by NIST's parameter selection)
  sum: -log2(2^(-8n) + P)        used by the original SPHINCS+ parameter script

Only n, h, a and k enter the bound; d and w do not.

This is the *average* rate of a fresh digest. A forger that collects its signatures first and then
chooses between the FORS search and another 2^-127-per-query search gets E[max(X, 1)] instead, so
at 127 bits these limits are not safe; `adaptive_lifetime.py` computes the leanSphincs lifetimes
that are.
"""

import argparse
import math
import sys
from dataclasses import dataclass, replace

LN2 = math.log(2)


@dataclass(frozen=True)
class Params:
    name: str
    n: int  # hash output length in bytes; security is capped at 8n bits
    h: int  # total hypertree height: 2^h FORS instances
    a: int  # FORS tree height
    k: int  # number of FORS trees
    limit: float  # log2 of the specified signature limit


PRESETS = {
    "lean": Params("leanSPHINCS candidate", n=16, h=26, a=10, k=24, limit=30),
    "128-24": Params("SLH-DSA-*-128-24 (SP 800-230 ipd)", n=16, h=22, a=24, k=6, limit=24),
    "128s": Params("SLH-DSA-*-128s (FIPS 205)", n=16, h=63, a=12, k=14, limit=64),
    "128f": Params("SLH-DSA-*-128f (FIPS 205)", n=16, h=66, a=6, k=33, limit=64),
}


def log2_add(x, y):
    """log2(2^x + 2^y), without leaving the log domain."""
    big, little = max(x, y), min(x, y)
    if big == -math.inf or big > little + 64:
        return big
    return big + math.log2(1 + 2.0 ** (little - big))


def forgery_bits_exact(log2_q, h, a, k):
    """-log2 P(q) with the exact binomial distribution of hits per FORS instance."""
    q = 2.0**log2_q
    log_p, log_1mp = -h * LN2, math.log1p(-(2.0**-h))
    log_miss = math.log1p(-(2.0**-a))  # a signature misses a given leaf of a FORS tree
    total = -math.inf
    log_binom = 0.0  # log C(q, r), updated incrementally to avoid lgamma cancellation
    r = 1
    while r <= q:
        log_binom += math.log(q - r + 1) - math.log(r)
        log_hit = log_binom + r * log_p + (q - r) * log_1mp
        log_forge = k * math.log(-math.expm1(r * log_miss))
        term = (log_hit + log_forge) / LN2
        total = log2_add(total, term)
        if r > q * 2.0**-h and term < total - 60:
            break
        r += 1
    return -total


def forgery_bits_poisson(log2_q, h, a, k):
    """-log2 P(q) with hits per instance ~ Poisson(q / 2^h); port of Fenner/Fluhrer."""
    lam = 2.0 ** (log2_q - h)
    p_miss = 1.0 - 2.0**-a
    p_miss_g = 1.0  # probability that g signatures all miss a given leaf
    log_lam_g = 0.0  # log2(lam^g / g!)
    total = -math.inf
    g = 1
    while True:
        log_lam_g += (log2_q - h) - math.log2(g)
        p_miss_g *= p_miss
        if p_miss_g < 1e-5:
            # 1 - p_miss_g rounds badly here; use the second-order Taylor expansion of log2
            log_forge = -k * (p_miss_g + p_miss_g * p_miss_g / 2) / LN2
        else:
            log_forge = k * math.log2(1 - p_miss_g)
        total = log2_add(total, log_lam_g + log_forge)
        if g >= 10 and total > 20 + log_lam_g:
            break
        g += 1
    return lam / LN2 - total  # the e^(-lam) Poisson factor, applied once


METHODS = {"exact": forgery_bits_exact, "poisson": forgery_bits_poisson}


def security_bits(log2_q, p, method, combine):
    fors = METHODS[method](log2_q, p.h, p.a, p.k)
    cap = 8 * p.n
    if combine == "max":
        return min(cap, fors)
    return -log2_add(-cap, -fors)


def max_log2_sigs(level, p, method, combine):
    """Largest log2(q) keeping `level` bits of security, or None if even q = 1 falls short."""
    if combine == "sum" and level >= 8 * p.n:
        return None  # -log2(2^(-8n) + P) < 8n for every q; floating point only hides it
    if security_bits(0, p, method, combine) < level:
        return None
    lo = 0
    while security_bits(lo + 1, p, method, combine) >= level:
        lo += 1
    hi = lo + 1
    for _ in range(40):
        mid = (lo + hi) / 2
        if security_bits(mid, p, method, combine) >= level:
            lo = mid
        else:
            hi = mid
    return lo


def human(log2_q):
    q = 2.0**log2_q
    if q >= 1e15:
        return f"{q:.3g}"
    for div, unit in ((1e12, "T"), (1e9, "G"), (1e6, "M"), (1e3, "k")):
        if q >= div:
            return f"{q / div:.3g}{unit}"
    return f"{q:.3g}"


def report(p, sigs, levels, method):
    print(f"{p.name}: n={p.n} h={p.h} a={p.a} k={p.k}, specified limit 2^{p.limit:g}")
    print(f"method: {method}\n")

    print("signatures      FORS bound   security (max)   security (sum)")
    for m in sigs:
        fors = METHODS[method](m, p.h, p.a, p.k)
        sec_max = security_bits(m, p, method, "max")
        sec_sum = security_bits(m, p, method, "sum")
        mark = "  <- limit" if m == p.limit else ""
        print(f"2^{m:<6g} {human(m):>6}   {fors:9.2f}   {sec_max:14.2f}   {sec_sum:14.2f}{mark}")

    print("\nsecurity level   max signatures (max)   max signatures (sum)")
    for level in levels:
        cells = []
        for combine in ("max", "sum"):
            m = max_log2_sigs(level, p, method, combine)
            cells.append("never" if m is None else f"2^{m:.2f} = {human(m)}")
        print(f"{level:9g} bits   {cells[0]:>20}   {cells[1]:>20}")


def selftest():
    ok = True

    def check(label, got, want, tol):
        nonlocal ok
        good = abs(got - want) <= tol
        ok &= good
        print(f"{'ok  ' if good else 'FAIL'} {label}: got {got:.3f}, want {want} +- {tol}")

    # log2 signatures at 112 bits, published in the slh-dsa-rls README (2^24 code-signing table).
    for name, h, a, k, want in (
        ("rls128cs1 = SLH-DSA-128-24", 22, 24, 6, 27.25),
        ("rls128cs3", 22, 21, 7, 26.87),
        ("rls128cs9", 20, 26, 6, 27.31),
        ("rls128cs18", 22, 17, 9, 26.32),
    ):
        p = Params(name, n=16, h=h, a=a, k=k, limit=24)
        for method in METHODS:
            check(f"{name} sigs at 112 bits ({method})", max_log2_sigs(112, p, method, "max"), want, 0.011)

    # The two methods must agree wherever both are evaluated.
    for key, m in (("128-24", 24), ("128-24", 30), ("128s", 64), ("128f", 64)):
        p = PRESETS[key]
        exact = forgery_bits_exact(m, p.h, p.a, p.k)
        check(f"{key} at 2^{m}: exact vs poisson", exact, round(forgery_bits_poisson(m, p.h, p.a, p.k), 2), 0.01)
    return ok


def main():
    ap = argparse.ArgumentParser(
        description=__doc__.split("\n\n")[0],
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="examples:\n"
        "  %(prog)s                          # leanSPHINCS candidate (h=26, a=10, k=24)\n"
        "  %(prog)s --h 23                   # same set with one more level of tree height\n"
        "  %(prog)s --sigs 24 24.5 25 --levels 128 100\n"
        "  %(prog)s --preset 128s\n"
        "  %(prog)s --selftest",
    )
    ap.add_argument("--preset", choices=PRESETS, default="lean", help="starting parameter set (default: lean)")
    for field in ("n", "h", "a", "k"):
        ap.add_argument(f"--{field}", type=int, help=f"override {field}")
    ap.add_argument("--sigs", type=float, nargs="+", metavar="LOG2", help="log2 signature counts to tabulate")
    ap.add_argument("--levels", type=float, nargs="+", metavar="BITS", help="security levels to invert")
    ap.add_argument("--method", choices=METHODS, default="exact", help="hit distribution (default: exact)")
    ap.add_argument("--selftest", action="store_true", help="check against published slh-dsa-rls numbers")
    args = ap.parse_args()

    if args.selftest:
        sys.exit(0 if selftest() else 1)

    p = PRESETS[args.preset]
    overrides = {f: getattr(args, f) for f in ("n", "h", "a", "k") if getattr(args, f) is not None}
    if overrides:
        p = replace(p, name=p.name + " with " + ", ".join(f"{f}={v}" for f, v in overrides.items()), **overrides)

    L = p.limit
    sigs = args.sigs or [L - 4, L - 2, L - 1, L, L + 0.5, L + 1, L + 2, L + 3, L + 4, L + 6, L + 8]
    levels = args.levels or [lv for lv in (8 * p.n, 8 * p.n - 1, 120, 112, 96, 80, 64) if lv <= 8 * p.n]
    report(p, sigs, levels, args.method)


if __name__ == "__main__":
    main()
