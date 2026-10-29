#!/usr/bin/env python3
"""Generate FORS/Certificates/H*.lean: exact rational certificates for the FORS lifetimes.

A configuration is a total height H (20, 22, 24, 26, 28), a shape (pruned: one tree with a kept subtree
of height B; layered: the hypertree of SPLITS, nothing pruned, B = H), its FTS, FORS with `k` trees of
height `a`, and a signature limit N. FORS is 24 trees of height 10 except in the uniform keys of the
lifetimes 2^24 and 2^26, both at H = 24: 20 and 23 trees of height 9 (LAYERED; `scripts/scheme.py`).

Usage (from formal/sphincs):
    python3 scripts/fors_certificates.py check H SHAPE B N LX [K A]   # check one parameter set (exit 1 if it fails)
    python3 scripts/fors_certificates.py emit [ROOT]            # write FORS/Certificates/H*.lean (under ROOT)
    python3 scripts/fors_certificates.py emit-lifetimes [ROOT]  # and FORS/Lifetimes.lean
    python3 scripts/fors_certificates.py maxn H SHAPE B N0 [STEP LXLO LXHI [K A]]   # search the largest N above N0
    python3 scripts/fors_certificates.py scan H SHAPE B N LX... # the terms of the small route at several lx
    python3 scripts/fors_certificates.py sw H K A N [LX] [--cover F|J]  # three routes (small, SW, large) of a layered key
    python3 scripts/fors_certificates.py sw-emit H K A N [LX]   # and write FORS/Certificates/H<H>SW.lean
    python3 scripts/fors_certificates.py sw-scan H K A N LX0 LX1 [--cover F|J]   # SW slack per unit, entries 2^(1/16)
    python3 scripts/fors_certificates.py sw-maxn H K A N0 N1 [--cover F|J]       # the largest N of the three routes
(--cover J: P3's J-split option as a model, numbers only; LX defaults to the small route's largest on the 1/8 grid.)
SHAPE is `pruned` or `layered` (then B = H); K A default to 24 10. Then `lake build FORS.Lifetimes` (the kernel re-checks every
certificate). `maxn` is a search: its result counts only once `check` accepts it and it is in PARAMS or LAYERED.

For each parameter set (b, N, lx), with qh = floor(2^(128 + lx)):
  * a Poisson table at rate N/2^b + (2M - 1) qtop / (M denB 2^b), M = 2^(TOTAL - b), qtop the largest budget
    it serves (rate_of; checkPT, checkRate);
  * the small route at qh: a Chernoff option at baseline rho/2^128 (checkOptF), the near certificate
    (checkOptN) and the rational check checkSmallF (SmallBudget/Closing.lean);
  * the large route: a cover of every budget q' in [qh + 1, 2^127] at the survival-weighted baseline
    (checkCoverW, LargeBudget/Covers.lean).
Everything below mirrors the Lean checkers exactly (Fractions); floats only choose parameters.
The Lean file stores the scalars of each table, option and near certificate; the Lean functions poisOf,
buildOpt and buildOptN (Certificates/Build.lean) rebuild their lists as fill_poisT, fill_opt and make_optN
do here (in integers, from the numerators P1L, P2L of the moment tables), and a rebuilt
table, option or near certificate passes its checker by construction (checkPT_poisOf, checkOptF_build,
checkOptN_build): the kernel evaluates the construction and a few scalar conditions.
A layered configuration whose certificate is the full key's but for the keygen credit reuses it (`reuses`).
The moment tables P1tab, P2tab (CoverBound/MomentTable.lean) are the closed forms of the FORS moments
(CoverBound/MomentBounds.lean), computed here by the same integer recipe as the Lean kernel.
"""
from fractions import Fraction as Fr
import math, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

# ---------------- exact helpers (Base/SplitCert.lean) ----------------

def rdown(x, P): return Fr((x.numerator * 2 ** P) // x.denominator, 2 ** P)
def rup(x, P): return Fr(-((-x.numerator * 2 ** P) // x.denominator), 2 ** P)

def sqUp(P, s, x):
    for _ in range(s):
        x = rup(x * x, P)
    return x

def expUp(u, s, P): return sqUp(P, s, rup(1 / (1 - u / 2 ** s), P))

def expLow(u, J, P):
    j, t, acc = 0, Fr(1), Fr(0)
    for _ in range(J):
        t, acc = rdown(t * u / (j + 1), P), acc + t
        j += 1
    return acc + t

ELOW = Fr(27182818283, 10 ** 10)
TOTAL = 24          # tree height: the full key keeps all 2^TOTAL instances (set_config)
KQ = Fr(1, 2 ** TOTAL)
LAYERED_TOP = None  # the top layer's height of a layered key, None for a pruned key (set_config)
SHAPE = "pruned"
FA = 10             # a: the height of a FORS tree (set_config)
FK = 24             # k: the number of FORS trees (set_config)

# The layer split of a layered key, top layer first (crates/sphincs `layered_heights`).
SPLITS = {24: (10, 7, 7), 26: (10, 8, 8), 28: (10, 9, 9)}

def set_config(h, shape='pruned', b=None, k=24, a=10):
    """Select the height, the shape and the FORS shape (k, a) every function below works at."""
    global TOTAL, KQ, LAYERED_TOP, SHAPE, FK, FA, P1, P2
    assert shape in ('pruned', 'layered')
    TOTAL, KQ, SHAPE = h, Fr(1, 2 ** h), shape
    LAYERED_TOP = SPLITS[h][0] if shape == 'layered' else None
    FK, FA = k, a
    P1, P2 = moment_tables(a)

def num_layers():
    return len(SPLITS[TOTAL]) if SHAPE == 'layered' else 1

def kcredit(b):
    """Key generation, in hash calls: 32 + 64 * 3 + 2 per leaf of the kept subtree and 2 per surrogate
    (`keygenHashCost`); a layered key builds its top layer, with no surrogate."""
    if LAYERED_TOP is not None:
        return 226 * 2 ** LAYERED_TOP
    return 226 * 2 ** b + 2 * (TOTAL - b)
def betaWQ(qb): return Fr(2 * (2 ** 128 - qb) + 1, 2 ** 256)

# ---------------- the moment tables ----------------

# The moment tables are the closed forms of the FORS moments (CoverBound/MomentBounds.lean), with the
# numerators over 2^128 the Lean kernel computes (p1N, p2N; CoverBound/MomentTable.lean reads no literal).

def cdiv(x, y):
    """ceil(x / y) for y > 0 (cdiv on ℕ, cdivZ on ℤ)"""
    return -((-x) // y)

def p1N(a, n):
    """the numerator of the bound of Ψ1(n) over 2^128 (p1N)"""
    A = 2 ** a
    return cdiv(2 ** 128 * (A ** n - (A - 1) ** n), A ** n)

def z2N(a, n):
    """the exact numerator of Ψ2(n) over A^(n+1) (z2N)"""
    A = 2 ** a
    return A ** (n + 1) - 2 * A * (A - 1) ** n + (A - 1) ** n + (A - 1) * (A - 2) ** n

def p2N(a, n):
    """the numerator of the bound of Ψ2(n) over 2^128 (p2N, an `Int.toNat`)"""
    return max(0, cdiv(2 ** 128 * z2N(a, n), (2 ** a) ** (n + 1)))

def moment_tabs(a):
    """P1tab, P2tab for trees of height a, n <= 150 (CoverBound/MomentTable.lean)"""
    return ([Fr(p1N(a, n), 2 ** 128) for n in range(151)],
            [Fr(p2N(a, n), 2 ** 128) for n in range(151)])

_TABS = {}

def moment_tables(a):
    """moment_tabs(a), computed once per tree height"""
    if a not in _TABS:
        _TABS[a] = moment_tabs(a)
        assert all(len(x) == 151 for x in _TABS[a])
    return _TABS[a]

P1, P2 = moment_tables(FA)

def getD(lst, n): return lst[n] if 0 <= n < len(lst) else Fr(0)

# ---------------- the Poisson table (CoverBound/HTermCertificate.lean) ----------------

class PoisT:
    def __init__(self, m, P, J, pm):
        self.m, self.P, self.J, self.pm = m, P, J, pm
        self.mu = Fr(m, 2 ** 64)
        self.n1 = len(pm) - 2
        self.r = self.mu / (self.n1 + 2)
    def pb(self, n): return Fr(self.pm[n] if 0 <= n < len(self.pm) else 0, 2 ** self.P)

def scanMb(b): return 2 ** (TOTAL - b)
def lmaxB(b, q): return 65 * ((q + 64 * scanMb(b) - 1) // (64 * scanMb(b))) + 2 ** 15
def denB(b, q): return 2 ** 128 - (q + 2 ** 32 + (scanMb(b) - 1) * lmaxB(b, q))
def fair_ok(b, q): return q + 2 ** 32 + (scanMb(b) - 1) * lmaxB(b, q) + (2 * scanMb(b) - 1) <= 2 ** 128
def rate_of(b, N, qtop): return Fr(N, 2 ** b) + Fr((2 * scanMb(b) - 1) * qtop, scanMb(b) * denB(b, qtop) * 2 ** b)

def denHB(b, q): return 2 ** 128 - (q // 2 + (scanMb(b) - 1) * lmaxB(b, q))
def fairH_ok(b, q): return q // 2 + (scanMb(b) - 1) * lmaxB(b, q) + (2 * scanMb(b) - 1) <= 2 ** 128
def rateH_of(b, N, qtop): return Fr(N + 1, 2 ** b) + Fr((2 * scanMb(b) - 1) * qtop, scanMb(b) * denHB(b, qtop) * 2 ** b)
def checkRateH(b, N, qtop, t): return fairH_ok(b, qtop) and rateH_of(b, N, qtop) <= t.mu

def fill_poisT(m, P, J, n1):
    """the table of rate m / 2^64 from its scalars (poisOf, Certificates/Build.lean, is given pm[0])"""
    x = Fr(2 ** P) / expLow(Fr(m, 2 ** 64), J, P)
    pm = [-((-x.numerator) // x.denominator)]
    for n in range(n1 + 1):
        d = (n + 1) * 2 ** 64
        pm.append((pm[-1] * m + (d - 1)) // d)
    return PoisT(m, P, J, pm)

def make_poisT(b, N, qtop, n1=150, P=220, heavy=False):
    assert fairH_ok(b, qtop) if heavy else fair_ok(b, qtop)
    num = (rateH_of(b, N, qtop) if heavy else rate_of(b, N, qtop)) * 2 ** 64
    m = -((-num.numerator) // num.denominator)
    J = int(float(Fr(m, 2 ** 64)) + 14 * math.sqrt(float(Fr(m, 2 ** 64))) + 60)
    return fill_poisT(m, P, J, n1)

def checkPT(t):
    if not len(t.pm) >= 2: return False
    if not Fr(2 ** t.P) <= t.pm[0] * expLow(t.mu, t.J, t.P): return False
    for n in range(len(t.pm) - 1):
        if not t.pm[n] * t.m <= t.pm[n + 1] * ((n + 1) * 2 ** 64): return False
    return t.r < 1

def checkRate(b, N, qtop, t):
    return fair_ok(b, qtop) and rate_of(b, N, qtop) <= t.mu

def checkLeaf(tab, J):
    if not len(tab) >= 2: return False
    if not tab[0] >= 0: return False
    for n in range(len(tab) - 1):
        if not tab[n] <= tab[n + 1]: return False
    for n in range(len(tab) - 2):
        if not 2 * tab[n + 1] <= tab[n] + tab[n + 2]: return False
    return tab[-1] - tab[-2] <= J

def tailSum(t, tab, J):
    r = t.r
    return sum((t.pb(n) * tab[n] for n in range(t.n1 + 1)), Fr(0)) + \
        t.pb(t.n1 + 1) * (tab[t.n1] / (1 - r) + J / (1 - r) ** 2)

def convexify(xs):
    h = [xs[0]]
    for n in range(1, len(xs)):
        if n == 1: h.append(max(xs[1], h[0]))
        else: h.append(max(xs[n], 2 * h[-1] - h[-2]))
    return h

# ---------------- options (CoverBound/HTermOption.lean) ----------------

class OptF:
    pass

def gBound(o, n): return min(KQ * getD(P1, n) ** FK, KQ ** 2 * getD(P2, n) ** FK / (4 * o.c1))
def hBound(o, n): return min(o.eC - 1, o.th * KQ * getD(P1, n) ** FK + o.A2 * KQ ** 2 * getD(P2, n) ** FK)

def optB(b, t, o):
    return 2 ** b * o.Eg + sqUp(t.P, b, 1 + o.Ee) / (expLow(o.th * o.cthr, t.J, t.P) * ELOW * o.th)

def checkOptF(b, t, o):
    n1 = t.n1
    if not (0 < o.c1 and 0 < o.th and 0 <= o.cthr and o.th * o.c1 < 2 ** o.s): return False
    if not expUp(o.th * o.c1, o.s, t.P) <= o.eC: return False
    if not (o.eC - 1 - o.th * o.c1) / o.c1 ** 2 <= o.A2: return False
    if not (n1 <= 150 and len(o.gt) == n1 + 1 and len(o.ht) == n1 + 1): return False
    if not (checkLeaf(o.gt, o.Jg) and checkLeaf(o.ht, o.Jh)): return False
    for n in range(n1 + 1):
        if not gBound(o, n) <= o.gt[n]: return False
        if not hBound(o, n) <= o.ht[n]: return False
    if not KQ <= o.gt[n1] + o.Jg: return False
    if not o.eC - 1 <= o.ht[n1] + o.Jh: return False
    if not tailSum(t, o.gt, o.Jg) <= o.Eg: return False
    if not tailSum(t, o.ht, o.Jh) <= o.Ee: return False
    if not optB(b, t, o) <= o.B: return False
    return 0 <= o.Eg and 0 <= o.Ee

PG = 64

def fill_opt(b, t, c1, th, s, cthr):
    """the option from its scalars (buildOpt, Certificates/Build.lean)"""
    o = OptF()
    o.c1, o.th, o.s, o.cthr = c1, th, s, cthr
    n1 = t.n1
    o.eC = expUp(th * c1, s, t.P)
    o.A2 = rup((o.eC - 1 - th * c1) / c1 ** 2, 2 * 127 + PG)
    gs = [gBound(o, n) for n in range(n1 + 1)]
    hs = [hBound(o, n) for n in range(n1 + 1)]
    o.gt = convexify([rup(x, PG + 127) for x in gs])
    o.ht = convexify([rup(x, PG + 64) for x in hs])
    o.Jg = max(o.gt[-1] - o.gt[-2], KQ - o.gt[-1], Fr(0))
    o.Jh = max(o.ht[-1] - o.ht[-2], o.eC - 1 - o.ht[-1], Fr(0))
    o.Eg = rup(tailSum(t, o.gt, o.Jg), PG + 127 + 2 * b)
    o.Ee = rup(tailSum(t, o.ht, o.Jh), PG + 2 * b)
    o.B = rup(optB(b, t, o), PG + 127)
    return o

class FModel:
    """float model in units 2^-127"""
    def __init__(self, t):
        self.mu = float(t.mu)
        n1 = t.n1
        self.ps = [math.exp(-self.mu + n * math.log(self.mu) - math.lgamma(n + 1)) if n > 0 else math.exp(-self.mu)
                   for n in range(n1 + 1)]
        self.m1 = [2.0 ** (127 - TOTAL) * float(P1[n]) ** FK for n in range(n1 + 1)]
        self.m2 = [2.0 ** (2 * (127 - TOTAL)) * float(P2[n]) ** FK for n in range(n1 + 1)]
    def H(self, L, c1, th, c):
        A = (math.exp(th * c1) - 1 - th * c1) / c1 ** 2
        eh = sum(p * min(a, b2 / (4 * c1)) for p, a, b2 in zip(self.ps, self.m1, self.m2))
        ee = sum(p * min(math.exp(th * c1), 1 + th * a + A * b2) for p, a, b2 in zip(self.ps, self.m1, self.m2))
        v = L * math.log(ee) - th * c - 1 - math.log(th)
        return L * eh + math.exp(min(v, 700))
    def best(self, L, c):
        best = (1e300, None, None)
        for f in [0.3 + 0.05 * i for i in range(15)]:
            c1 = f * c
            for e in range(-32, 400, 2):
                th = 2.0 ** (e / 16)
                if th * c1 > 600: break
                v = self.H(L, c1, th, c)
                if v < best[0]: best = (v, c1, th)
        return best

def dyadic_down(x, bits):
    e = math.floor(math.log2(x)) - bits
    return Fr(math.floor(x / 2.0 ** e)) * Fr(2) ** e

def dyadic(x, bits=24):
    e = math.floor(math.log2(x)) - bits
    return Fr(round(x / 2.0 ** e)) * Fr(2) ** e

def make_opt(b, t, fm, cthr):
    """an option at the exact threshold cthr (absolute units)"""
    L = 2 ** b
    H, c1s, ths = fm.best(L, float(cthr * 2 ** 127))
    c1 = dyadic(c1s, 24) * Fr(1, 2 ** 127)
    th = dyadic(ths, 24) * 2 ** 127
    u = float(th * c1)
    s = max(0, math.ceil(math.log2(u + 1e-300)) + 12)
    return fill_opt(b, t, c1, th, s, cthr), H

# ---------------- the near certificate (CoverBound/NearOption.lean) ----------------

class OptN:
    pass

def nBound(n): return FK * KQ * getD(P1, n) ** (FK - 1)

def make_optN(b, t):
    """the near certificate of a table (buildOptN, Certificates/Build.lean)"""
    o = OptN()
    n1 = t.n1
    o.nt = convexify([rup(x, PG + 127) for x in [nBound(n) for n in range(n1 + 1)]])
    o.Jn = max(o.nt[-1] - o.nt[-2], FK * KQ - o.nt[-1], Fr(0))
    o.En = rup(tailSum(t, o.nt, o.Jn), PG + 127 + 2 * b)
    return o

def checkOptN(t, o):
    n1 = t.n1
    if not (n1 <= 150 and len(o.nt) == n1 + 1 and checkLeaf(o.nt, o.Jn)): return False
    for n in range(n1 + 1):
        if not nBound(n) <= o.nt[n]: return False
    if not FK * KQ <= o.nt[n1] + o.Jn: return False
    return tailSum(t, o.nt, o.Jn) <= o.En

# ---------------- the small route (SmallBudget/Closing.lean) ----------------

def checkSmallF(b, N, qh, rho, cthr, B, c):
    x = Fr(qh, 2 ** 128)
    rate = Fr(N, 2 ** b * 2 ** FA)
    conds = [Fr(3, 2) <= rho, rho <= 2, 1 + 4032 * (2 - rho) * x <= rho, 1 + 66 * x <= rho, 64 * x <= 1,
             qh <= 2 ** 127, N <= 2 ** 70, cthr <= rho / 2 ** 128, 0 <= B, 0 <= c, rate <= rho - 1 - x]
    if not all(conds): return False
    lhs = rho + 2 ** 128 * B + Fr((2 * scanMb(b) - 1) * qh, scanMb(b) * 2 ** 129) + (2 - rho + x + rate) * qh * c + Fr(1, 2 ** 60)
    return lhs <= 2

def small_lhs(b, N, qh, rho, B, c):
    x = Fr(qh, 2 ** 128)
    rate = Fr(N, 2 ** b * 2 ** FA)
    return rho + 2 ** 128 * B + Fr((2 * scanMb(b) - 1) * qh, scanMb(b) * 2 ** 129) + (2 - rho + x + rate) * qh * c + Fr(1, 2 ** 60)

def choose_rho(qh):
    x = Fr(qh, 2 ** 128)
    xf = float(x)
    r = max(1.5, 2 - 1 / (1 + 4032 * xf), 1 + 66 * xf)
    rho = Fr(math.ceil(r * 2 ** 40), 2 ** 40)
    while not (1 + 4032 * (2 - rho) * x <= rho and 1 + 66 * x <= rho and Fr(3, 2) <= rho):
        rho += Fr(1, 2 ** 40)
    return rho

# ---------------- the large route (LargeBudget/Covers.lean) ----------------

def entry_ok(b, N, o, qa, qb):
    if not (2 * qb <= 2 ** 128): return False
    if not (o.cthr <= betaWQ(qb)): return False
    lhs = qb * o.B + Fr(qb + kcredit(b) + N, 2 ** 200)
    rhs = Fr(qa, 2 ** 128) ** 2 + Fr(kcredit(b), 2 ** 127)
    return lhs <= rhs

GRID = 64

class Builder:
    def __init__(self, b, N, t, fm, maker=None):
        self.b, self.N, self.t, self.fm = b, N, t, fm
        self.maker = maker      # None: make_opt (the SW route's model mode passes another option maker)
        self.opts = {}
    def opt_for(self, key):
        if key not in self.opts:
            xg = Fr(2) ** Fr(key, GRID) if False else 2.0 ** (key / GRID)
            # the threshold betaWQ(qb) >= 2^-127 (1 - qb/2^128) > 2^-127 (1 - xg) for every qb <= xg 2^128
            cthr = dyadic_down((1 - xg) * (1 - 1e-9), 40) * Fr(1, 2 ** 127)
            o, _ = (self.maker or make_opt)(self.b, self.t, self.fm, cthr)
            self.opts[key] = o
        return self.opts[key]
    def key_of(self, qb):
        return math.ceil(math.log2(qb / 2.0 ** 128) * GRID)
    def ok(self, qa, qb):
        if 2 * qb > 2 ** 128: return None
        k = self.key_of(qb)
        return k if entry_ok(self.b, self.N, self.opt_for(k), qa, qb) else None
    def build(self, qstart, TOP=2 ** 127, maxint=400):
        qa = qstart
        out = []
        while True:
            if len(out) >= maxint: return None
            if self.ok(qa, qa) is None: return None
            k = self.ok(qa, TOP)
            if k is not None:
                out.append((qa, TOP, k))
                return out
            def qb_of(i): return min(TOP, int(qa * 2.0 ** (i / 256.0)))
            lo, i = 0, 1
            while qb_of(i) < TOP and self.ok(qa, qb_of(i)) is not None:
                lo = i
                i *= 2
            hi = i
            while hi - lo > 1:
                mid = (lo + hi) // 2
                if self.ok(qa, qb_of(mid)) is not None: lo = mid
                else: hi = mid
            qb = qb_of(lo)
            if lo == 0:
                a, z = qa, qb_of(1)
                while z - a > 1:
                    mm = (a + z) // 2
                    if self.ok(qa, mm) is not None: a = mm
                    else: z = mm
                qb = a
            k = self.ok(qa, qb)
            if k is None: return None
            out.append((qa, qb, k))
            qa = qb + 1

def chainF(b, N, qtop, opts, last, entries):
    for (qa, qb, j) in entries:
        if not (qa <= last): return False
        if not (j < len(opts) and entry_ok(b, N, opts[j], qa, qb)): return False
        last = qb + 1
    return qtop < last

def segments(b, qh):
    """budget ranges of the covers: each has its own table (rate fixed by its top)"""
    top = 2 ** 127 - 1 - kcredit(b)
    if b == TOTAL:
        return [2 ** 127]
    qlight = (64 * 2 ** 128 - 2 ** 60) // 257
    return [q for q in (2 ** 124, qlight) if q > qh]

# ---------------- one parameter set ----------------

def small_route(b, N, lx, verbose=True):
    """the small route at qh = floor(2^(128 + lx)): its table, rate, option and near certificate, None if
    checkSmallF fails"""
    qh = int(2 ** (128 + lx))
    t = make_poisT(b, N, qh)
    assert checkPT(t) and checkRate(b, N, qh, t)
    fm = FModel(t)
    rho = choose_rho(qh)
    cthr = rho / 2 ** 128
    o, _ = make_opt(b, t, fm, cthr)
    assert checkOptF(b, t, o)
    on = make_optN(b, t)
    assert checkOptN(t, on)
    c = (2 ** b * on.En) / 2
    lhs = small_lhs(b, N, qh, rho, o.B, c)
    ok_small = checkSmallF(b, N, qh, rho, o.cthr, o.B, c)
    if verbose:
        print('b %d N %d lx %s: rho %.6f 2^128B %.5f small lhs %.6f %s' % (b, N, lx, float(rho), float(2 ** 128 * o.B),
              float(lhs), 'OK' if ok_small else 'FAIL'), flush=True)
    if not ok_small:
        return None
    return dict(qh=qh, rho=rho, t=t, o=o, on=on)

def large_covers(b, N, qh, qstart, verbose=True):
    """the large route's covers of every budget from qstart (segments above qh), None if a cover fails"""
    covers = []
    heavy = []
    segs = [(qtop, False) for qtop in segments(b, qh)] + ([] if b == TOTAL else [(2 ** 127, True)])
    for qtop, hv in segs:
        tc = make_poisT(b, N, qtop, heavy=hv)
        assert checkPT(tc) and (checkRateH(b, N, qtop, tc) if hv else checkRate(b, N, qtop, tc))
        B = Builder(b, N, tc, FModel(tc))
        raw = B.build(qstart, TOP=qtop)
        if raw is None:
            if verbose: print('  large route FAIL in [2^%.3f, 2^%.3f]' % (math.log2(qstart), math.log2(qtop)), flush=True)
            return None
        keys = sorted(set(k for (_, _, k) in raw))
        idx = {k: i for i, k in enumerate(keys)}
        opts = [B.opts[k] for k in keys]
        entries = [(qa, qb, idx[k]) for (qa, qb, k) in raw]
        assert all(checkOptF(b, tc, oo) for oo in opts)
        assert chainF(b, N, qtop, opts, qstart, entries)
        if verbose: print('  cover up to 2^%.4f OK: %d entries, %d options' % (math.log2(qtop), len(entries), len(opts)), flush=True)
        (heavy if hv else covers).append(dict(qtop=qtop, qstart=qstart, t=tc, opts=opts, entries=entries))
        qstart = qtop + 1
    complete = 2 ** 127 <= qstart + kcredit(b)
    if verbose and not complete:
        print('  covers stop at 2^%.4f: the heavy range is not certified' % math.log2(qstart - 1), flush=True)
    return covers, heavy, complete

def certify(b, N, lx, verbose=True):
    s = small_route(b, N, lx, verbose)
    if s is None:
        return None
    r = large_covers(b, N, s['qh'], s['qh'] + 1, verbose)
    if r is None:
        return None
    covers, heavy, complete = r
    return dict(h=TOTAL, shape=SHAPE, d=num_layers(), K=kcredit(b), b=b, k=FK, a=FA, N=N, lx=lx, qh=s['qh'],
                rho=s['rho'], t=s['t'], o=s['o'], on=s['on'], covers=covers, heavy=heavy, complete=complete)

# ---------------- Lean output ----------------

def q(x):
    x = Fr(x)
    return str(x.numerator) if x.denominator == 1 else '%d / %d' % (x.numerator, x.denominator)

# The Lean file stores only the scalars of a table, an option and a near certificate: `poisOf`,
# `buildOpt` and `buildOptN` (Certificates/Build.lean) rebuild the lists, as fill_poisT, fill_opt and make_optN do here.

OPT_FIELDS = ('c1', 'th', 'cthr', 's', 'eC', 'A2', 'gt', 'Jg', 'ht', 'Jh', 'Eg', 'Ee', 'B')

def lean_opt(b, tab, t, o):
    again = fill_opt(b, t, o.c1, o.th, o.s, o.cthr)
    assert all(getattr(again, f) == getattr(o, f) for f in OPT_FIELDS), 'the scalars do not rebuild the option'
    return 'buildOpt %d %d %d %d %s\n    (%s) %s %d\n    (%s)' % (TOTAL, b, FK, FA, tab, q(o.c1), q(o.th), o.s, q(o.cthr))

def lean_optN(b, tab, t, on):
    again = make_optN(b, t)
    assert (again.nt, again.Jn, again.En) == (on.nt, on.Jn, on.En), 'the table does not rebuild the near certificate'
    return 'buildOptN %d %d %d %d %s' % (TOTAL, b, FK, FA, tab)

def lean_tab(t):
    again = fill_poisT(t.m, t.P, t.J, t.n1)
    assert (again.m, again.P, again.J, again.pm) == (t.m, t.P, t.J, t.pm), 'the scalars do not rebuild the table'
    return 'poisOf %d %d %d %d\n    %d' % (t.m, t.P, t.J, t.n1, t.pm[0])

def light(c):
    """FORS other than 24 trees of height 10"""
    return (c['k'], c['a']) != (24, 10)

def upper1(s): return s[:1].upper() + s[1:]

def tag_of(c):
    return 'h%d_%s' % (c['h'], ('Lk%d' % c['k'] if light(c) else 'L') if c['shape'] == 'layered' else 'b%d' % c['b'])

def describe(c):
    if c['shape'] == 'layered':
        return 'height %d, layered (%s)%s, %s signatures' % (c['h'], ' + '.join(map(str, SPLITS[c['h']])),
            ', %d FORS trees of height %d' % (c['k'], c['a']) if light(c) else '', format(c['N'], ','))
    if c['b'] == c['h']:
        return 'height %d, full key, %s signatures' % (c['h'], format(c['N'], ','))
    return 'height %d, kept subtree height %d, %s signatures' % (c['h'], c['b'], format(c['N'], ','))

HEADER = '''import FORS.Certificates.Build

/-! Certificates for the proved FORS lifetimes at total height %d (generated by
`scripts/fors_certificates.py`, checked by the kernel with `decide +kernel`, exact rational
arithmetic, no `native_decide`). For each configuration: a Poisson table, the small-route option at
baseline `ρ / 2^128`, the near certificate and `checkSmallF` at `qh ≈ 2^(128 + lx)`, and a cover of
every larger budget up to `2^127` at the survival-weighted baseline. The tables, the options and the
near certificates are rebuilt from their scalars (`poisOf`, `buildOpt`, `buildOptN`) and pass their
checkers by construction (`checkPT_poisOf`, `checkOptB_build`, `checkOptN_build`, `Build.lean`); a cover
is checked from its options and its table (`checkCoverW_of_pt`). The layered key reuses the full key's
certificate and checks again only its cover chains, where its keygen credit enters. -/

namespace FORS.Security.H0

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
-- one check at a time: with asynchronous elaboration the memory of the finished checks is kept
set_option Elab.async false
'''

def same_cover(a, b):
    """Two covers with the same budgets, table and options (their entries may differ)."""
    return (a['qtop'], a['qstart'], a['t'].pm, a['t'].m, a['t'].P, a['t'].J) == \
        (b['qtop'], b['qstart'], b['t'].pm, b['t'].m, b['t'].P, b['t'].J) and len(a['opts']) == len(b['opts']) and \
        all(getattr(x, f) == getattr(y, f) for x, y in zip(a['opts'], b['opts']) for f in OPT_FIELDS)

def reuses(c, f):
    """A layered configuration whose certificate is the full key's but for the keygen credit K, which enters
    only the cover chains (checkEntryF): the same table, small-route option, near certificate and covers."""
    return f is not None and (c['k'], c['a']) == (f['k'], f['a']) and \
        (c['b'], c['N'], c['qh'], c['rho']) == (f['b'], f['N'], f['qh'], f['rho']) and \
        (c['t'].m, c['t'].P, c['t'].J, c['t'].pm) == (f['t'].m, f['t'].P, f['t'].J, f['t'].pm) and \
        all(getattr(c['o'], x) == getattr(f['o'], x) for x in OPT_FIELDS) and \
        (c['on'].nt, c['on'].Jn, c['on'].En) == (f['on'].nt, f['on'].Jn, f['on'].En) and \
        len(c['covers']) == len(f['covers']) and len(c['heavy']) == len(f['heavy']) and \
        all(same_cover(a, b) for a, b in zip(c['covers'] + c['heavy'], f['covers'] + f['heavy']))

def cover_def(name, qtop, tab, opts, entries, base=None):
    ents = ',\n    '.join('(%d, %d, %d)' % e for e in entries)
    if base is not None:
        return 'def %s : CoverW := { %s with\n  entries := [\n    %s] }\n' % (name, base, ents)
    return 'def %s : CoverW where\n  qtop := %d\n  tab := %s\n  opts := [%s]\n  entries := [\n    %s]\n' % (
        name, qtop, tab, ', '.join(opts), ents)

def emit(certs, path):
    """The certificates of the configurations of one height. A layered configuration that `reuses` the full key's
    certificate gets only its cover chains (and the full key's names in Lifetimes.lean: c['base'], c['cover_names'])."""
    out = [HEADER % certs[0]['h']]
    full = None
    for c in certs:
        full = emit_one(out, c, full)
    out.append('end FORS.Security.H0\n')
    open(path, 'w').write('\n'.join(out))

def emit_one(out, c, full, middle=None):
    """Append the certificate of one configuration to out; return the full key's certificate seen so far.
    middle(out, c, tag), if given, appends more definitions after the small route (the SW route's cover); the
    large covers then start at c['large_start'] (default qh + 1)."""
    set_config(c['h'], c['shape'], c['b'], c['k'], c['a'])
    b, N, K, H, k, a = c['b'], c['N'], c['K'], c['h'], c['k'], c['a']
    tag = tag_of(c)
    base = full if c['shape'] == 'layered' and reuses(c, full) else None
    c['base'] = tag_of(base) if base else tag
    if base is None:
        out.append('/-- Poisson table of the small route, %s. -/' % describe(c))
        out.append('def tab_%s : PoisT := %s\n' % (tag, lean_tab(c['t'])))
        out.append('theorem tab_%s_ok : checkPT tab_%s = true := checkPT_poisOf (by decide +kernel)\n' % (tag, tag))
        out.append('theorem rate_%s_ok : checkRate %d %d %d %d tab_%s = true := by decide +kernel\n'
                   % (tag, H, b, N, c['qh'], tag))
        out.append('/-- The small-route option at baseline `ρ / 2^128`. -/')
        out.append('def small_%s : OptF := %s\n' % (tag, lean_opt(b, 'tab_' + tag, c['t'], c['o'])))
        out.append('theorem small_%s_ok : checkOptF %d %d %d %d tab_%s small_%s = true :=\n    checkOptF_build (by decide +kernel)\n'
                   % (tag, H, b, k, a, tag, tag))
        on = c['on']
        out.append('/-- The near certificate. -/')
        out.append('def near_%s : OptN := %s\n' % (tag, lean_optN(b, 'tab_' + tag, c['t'], on)))
        out.append('theorem near_%s_ok : checkOptN %d %d %d tab_%s near_%s = true :=\n    checkOptN_build (by decide +kernel)\n'
                   % (tag, H, k, a, tag, tag))
        out.append('/-- The plain rate `ρ`. -/')
        out.append('def rho_%s : ℚ := %s\n' % (tag, q(c['rho'])))
        out.append('theorem check_%s_ok : ForsPotential.checkSmallF %d %d %d %d %d rho_%s small_%s.cthr small_%s.B\n'
                   '    ((2 ^ %d * near_%s.En : ℚ) / 2) = true := by decide +kernel\n'
                   % (tag, H, b, a, N, c['qh'], tag, tag, tag, b, tag))
    else:
        out.append('/-! %s: the certificate of the %s (table, small-route option, near certificate, '
                   'cover tables and options), checked again only where the keygen credit `K = %d` enters: the '
                   'cover chains. -/\n' % (upper1(describe(c)), describe(base), K))
    if middle is not None:
        middle(out, c, tag)
    names = {'': [], 'h': []}
    for kind, lst, chk, of in (('', c['covers'], 'checkCoverW', 'checkCoverW_of_pt'),
                               ('h', c['heavy'], 'checkCoverH', 'checkCoverH_of_pt')):
        for ci, cv in enumerate(lst):
            own = 'cover%s_%s_%d' % (kind, tag, ci)
            if base is None:
                otag = tag
                out.append('/-- Poisson table of %scover %d (budgets up to %d). -/' % ('heavy ' if kind else '', ci, cv['qtop']))
                out.append('def tabc%s_%s_%d : PoisT := %s\n' % (kind, tag, ci, lean_tab(cv['t'])))
                out.append('theorem tabc%s_%s_%d_ok : checkPT tabc%s_%s_%d = true := checkPT_poisOf (by decide +kernel)\n'
                           % (kind, tag, ci, kind, tag, ci))
                for oi, o in enumerate(cv['opts']):
                    out.append('/-- Option %d of %scover %d. -/' % (oi, 'heavy ' if kind else '', ci))
                    name, tabn = 'large%s_%s_%d_%d' % (kind, tag, ci, oi), 'tabc%s_%s_%d' % (kind, tag, ci)
                    out.append('def %s : OptF := %s\n' % (name, lean_opt(b, tabn, cv['t'], o)))
                    out.append('/-- Its threshold and its bound. -/')
                    out.append('def %s_cB : ℚ × ℚ :=\n    (%s,\n     %s)\n' % (name, q(o.cthr), q(o.B)))
                    out.append('theorem %s_ok : checkOptB %d %d %d %d %s %s %s_cB = true :=\n    checkOptB_build (by decide +kernel)\n'
                               % (name, H, b, k, a, tabn, name, name))
                opts = ['large%s_%s_%d_%d' % (kind, tag, ci, oi) for oi in range(len(cv['opts']))]
                out.append('/-- %s %d: every budget from %d to %d. -/' % (
                    'Heavy cover (one heavy message, one spare slot)' if kind else 'Cover', ci, cv['qstart'], cv['qtop']))
                out.append(cover_def(own, cv['qtop'], 'tabc%s_%s_%d' % (kind, tag, ci), opts, cv['entries']))
                cname = own
            else:
                otag = c['base']
                bcv = (base['heavy'] if kind else base['covers'])[ci]
                cname = 'cover%s_%s_%d' % (kind, otag, ci)
                if cv['entries'] != bcv['entries']:
                    out.append('/-- %s %d with the entries of this keygen credit. -/' % ('Heavy cover' if kind else 'Cover', ci))
                    out.append(cover_def(own, None, None, None, cv['entries'], base=cname))
                    cname = own
            onames = ['large%s_%s_%d_%d' % (kind, otag, ci, oi) for oi in range(len(cv['opts']))]
            names[kind].append(cname)
            out.append('theorem %s_ok : %s %d %d %d %d %d %d %d %s = true :='
                       % (own, chk, H, b, k, a, K, N, cv['qstart'], cname))
            out.append('  %s [%s]\n    (%s)\n    tabc%s_%s_%d_ok\n    (by decide +kernel)\n' %
                       (of, ', '.join(n + '_cB' for n in onames),
                        ' <| '.join(['.cons %s_ok' % n for n in onames] + ['.nil']), kind, otag, ci))
    assert c['complete'], tag
    c['cover_names'] = names
    out.append('/-- The covers reach every budget below `2^127`. -/')
    out.append('theorem covers_%s_ok : ForsPotential.checkCoversH %d %d %d %d %d %d %d [%s] [%s] = true := by'
               % (tag, H, b, k, a, K, N, c.get('large_start', c['qh'] + 1), ', '.join(names['']), ', '.join(names['h'])))
    lems = ', '.join(['cover_%s_%d_ok' % (tag, ci) for ci in range(len(c['covers']))] +
                     ['coverh_%s_%d_ok' % (tag, ci) for ci in range(len(c['heavy']))])
    out.append('  simp only [ForsPotential.checkCoversH, ForsPotential.checkCoversHeavy, Bool.and_eq_true]')
    out.append('  exact ⟨%s, by decide +kernel⟩\n' % lems)
    if c['shape'] == 'pruned' and b == H:
        full = c
    return full

# Attack lifetimes of the FORS FTS in the cover model (one expected cover per 2^127 digest
# queries), by height and kept subtree height (`scripts/scheme.py` `fors_log2_lifetime(h, b, a, k)` at
# a = 10 and k = 24, rounded down). A layered key is attacked as the full key of the same height; with
# lighter FORS, by (h, k, a) in ATTACK_LIGHT.
ATTACK = {
    20: {20: 18798990, 14: 371851, 13: 193219, 12: 100380, 10: 27078, 8: 7303},
    22: {22: 75195938, 20: 20356598, 14: 401494, 13: 208531, 12: 108288, 10: 29187, 8: 7865},
    24: {24: 300783729, 20: 22020747, 14: 433126, 13: 224867, 12: 116724, 10: 31437, 8: 8465},
    26: {26: 1203134891, 20: 23797932, 14: 466871, 13: 242292, 12: 125721, 10: 33835, 8: 9104},
    28: {28: 4812539541, 20: 25695072, 14: 502859, 13: 260873, 12: 135314, 10: 36392, 8: 9786},
}


ATTACK_LIGHT = {(24, 20, 9): 30900666, (24, 23, 9): 82781654}

HEIGHTS = (20, 22, 24, 26, 28)

def pname(c):
    if c['shape'] == 'layered':
        return 'h%d_layered' % c['h'] + ('_k%d' % c['k'] if light(c) else '')
    return 'h%d_full' % c['h'] if c['b'] == c['h'] else 'h%d_pruned%d' % (c['h'], c['b'])

LIFETIMES_HEADER = '''%s

/-! **Proofs of the proved lifetimes** (generated by `scripts/fors_certificates.py`): one theorem per
configuration, `ForsPotential.det_bitsFH` applied to the configuration's certificates
(`Certificates/H*.lean`). `Main.lean` states each of them again, independently of this file, and
proves it with the theorem here. Small budgets use the linear potential, the one-coin cover
potential at baseline `ρ / 2^128` and the contact bound A4 of the FORS leaves; large budgets use the
one-coin covers at the survival-weighted baseline. -/

namespace FORS.Lifetimes

open Security ForsPotential
'''

def lean_params(c):
    """The configuration as a `Params` term (`Params.pruned`, `Params.layered`, Scheme.lean): the FORS
    shape (k, a) is part of it."""
    if c['shape'] == 'layered':
        return '.layered %d %d %d %d %d %d' % (c['h'], c['d'], SPLITS[c['h']][1], c['k'], c['a'], c['N'])
    return '.pruned %d %d %d %d %d' % (c['h'], c['b'], c['k'], c['a'], c['N'])

def emit_lifetimes(certs, path):
    heights = sorted({c['h'] for c in certs})
    out = [LIFETIMES_HEADER % '\n'.join('import FORS.Certificates.H%d' % h for h in heights)]
    for c in certs:
        b, N, H, K, k, a = c['b'], c['N'], c['h'], c['K'], c['k'], c['a']
        tag, name, P = tag_of(c), pname(c), lean_params(c)
        att = attack(H, c['shape'], b, k, a)
        out.append("/-- %s (%.1f%% of the cover attack's %.4g). -/" % (upper1(describe(c)), 100.0 * N / att, att))
        bt = c['base']
        names = ', '.join('H0.' + n for n in c['cover_names'][''])
        hnames = ', '.join('H0.' + n for n in c['cover_names']['h'])
        out.append('theorem %s_bits : SecurityBits (%s) 127 :=' % (name, P))
        # the explicit arguments of det_bitsFH (Certificates/Closing.lean): H b k a K N, then hH hb hk ha hK hN, then qh
        out.append('  @det_bitsFH (%s) (by decide) %d %d %d %d %d %d\n'
                   '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) %d\n'
                   '    H0.rho_%s H0.tab_%s H0.small_%s H0.near_%s H0.tab_%s_ok H0.rate_%s_ok H0.small_%s_ok\n'
                   '    H0.near_%s_ok H0.check_%s_ok [%s] [%s] H0.covers_%s_ok\n'
                   % (P, H, b, k, a, K, N, c['qh'], bt, bt, bt, bt, bt, bt, bt, bt, bt, names, hnames, tag))
    out.append('end FORS.Lifetimes\n')
    open(path, 'w').write('\n'.join(out))

# Parameter sets of pruned keys, by height: (b, N, lx), b = h being the full key. N is the largest limit that
# `maxn` certified on the grid of lx (step 1/8), rounded down to four significant digits.
PARAMS = {
    20: [
        (20, 17440000, -8.25),
        (14, 325200, -7.375),
        (13, 167400, -7.25),
        (12, 86200, -7.125),
        (10, 22790, -7.0),
        (8, 6029, -6.875),
    ],
    22: [
        (22, 71490000, -8.75),
        (20, 19030000, -8.375),
        (14, 354500, -7.375),
        (13, 182200, -7.25),
        (12, 93560, -7.25),
        (10, 24770, -7.0),
        (8, 6547, -6.875),
    ],
    24: [
        (24, 292300000, -9.125),
        (20, 20740000, -8.375),
        (14, 385300, -7.5),
        (13, 198000, -7.375),
        (12, 101700, -7.25),
        (10, 26860, -7.0),
        (8, 7099, -6.875),
    ],
    26: [
        (26, 1182000000, -9.375),
        (20, 22590000, -8.5),
        (14, 418900, -7.5),
        (13, 215200, -7.375),
        (12, 110500, -7.25),
        (10, 29130, -7.125),
        (8, 7677, -7.0),
    ],
    28: [
        (28, 4731000000, -11.25),
        (20, 24540000, -8.625),
        (14, 454500, -7.625),
        (13, 233300, -7.5),
        (12, 119800, -7.375),
        (10, 31600, -7.125),
        (8, 8313, -7.0),
    ],
}

# Parameter sets of layered keys, by height and FORS shape (h, k, a): (N, lx). The index is not ground (b = h);
# with 24 trees of height 10 the smaller keygen credit of the top layer alone does not move the largest N, which
# is the full key's. The uniform keys of the lifetimes 2^24 and 2^26 are at h = 24 with lighter FORS (19 trees of
# height 9 do not reach 2^24: the largest certified N is about 14.6 million).
LAYERED = {
    (24, 20, 9): (24410000, -7.5),
    (24, 23, 9): (71650000, -7.625),
    (24, 24, 10): (292300000, -9.125),
    (26, 24, 10): (1182000000, -9.375),
    (28, 24, 10): (4731000000, -11.25),
}

def lifetime(h, shape, b=None, k=24, a=10):
    """The proved signature limit of a configuration, None if it has no certificate here."""
    if shape == 'layered':
        return (LAYERED.get((h, k, a)) or (None,))[0]
    if (k, a) != (24, 10):
        return None
    return next((n for (bb, n, _) in PARAMS.get(h, []) if bb == b), None)

def attack(h, shape, b=None, k=24, a=10):
    """The cover attack's lifetime of a configuration, None if not computed."""
    if (k, a) != (24, 10):
        return ATTACK_LIGHT.get((h, k, a)) if shape == 'layered' else None
    return ATTACK.get(h, {}).get(h if shape == 'layered' else b)

# The uniform (layered) key of each lifetime 2^L: (h, k, a).
UNIFORM = {24: (24, 20, 9), 26: (24, 23, 9), 28: (24, 24, 10), 30: (26, 24, 10), 32: (28, 24, 10)}

def uniform_lifetime(L):
    """The proved signature limit of the uniform key of the lifetime 2^L, None if not certified here."""
    return lifetime(*UNIFORM[L][:1], 'layered', None, *UNIFORM[L][1:])

def uniform_attack(L):
    """The cover attack's lifetime of the uniform key of the lifetime 2^L."""
    return attack(*UNIFORM[L][:1], 'layered', None, *UNIFORM[L][1:])

def configs():
    """Every configuration with a parameter set: (h, shape, b, N, lx, k, a)."""
    out = []
    for h in HEIGHTS:
        for (b, N, lx) in PARAMS.get(h, []):
            out.append((h, 'pruned', b, N, lx, 24, 10))
        for (hh, k, a), v in sorted(LAYERED.items(), key=lambda e: (e[0][0], -e[0][1])):
            if hh == h and v is not None:
                out.append((h, 'layered', h, v[0], v[1], k, a))
    return out

def certify_config(h, shape, b, N, lx, verbose=True, k=24, a=10):
    set_config(h, shape, b, k, a)
    if shape == 'layered':
        assert b == h, 'a layered key keeps every index: B = H'
    return certify(b, N, lx, verbose)

# ---------------- the SW route (SWRoute/ClosingReal.lean, SWRoute/Closing.lean) ----------------
#
# Three routes (det_bitsF3, SWRoute/Closing.lean): the small route up to qh, a SW cover of every budget in
# [qh + 1, qtop] and the large route's covers from qtop + 1. A SW cover (CoverSW) is a Poisson table at qtop, cover
# options (OptF today), near options at a baseline (OptNB, scripts/fors_sw_near.py) and entries
# (qa, qb, rho, beta, delta, m, Pb, ic, in, itl): qb <= qtop, the tail certificate itl gives Pb at (qb, m)
# (checkTail, SWRoute/ForecastCert.lean), at x = qb / 2^128 the side conditions checkNumSW with the contact
# coefficient cU = N/2^(b+a) + m, the digest payment cthr(cover) + delta cthr(near) <= beta / 2^128 and
#   satUp(rho, qa / 2^128) + qb B_c + delta qb B_n + coin(qb) + x_b Pb + (qb + K + N) / 2^200 <= 2 qa / 2^128 + K / 2^127.
# Per entry: rho is the least dyadic (2^-SW_PR) passing the rho conditions of checkNumSW but E3 (all monotone in rho
# on [3/2, 2]) with m > 0; m is the E3 cap at rho (so E3 does not move rho; rework/F2/verdict.md, route3.mOf); beta the
# largest dyadic (2^-SW_PB) below its five bounds; delta the least dyadic (2^-SW_PD) above the arming bound; the chain
# is built with Pb from F2's float model (pi.py, excess form, 2^-10 cushion: TailPbadModel), then each entry gets a
# certified tail (SW_TAIL_CERT: scripts/fors_sw_forecast.py make_tailCert / checkTail, reusing a certificate of an
# earlier entry when its Pb is no larger) and is checked again with that Pb; the near option sits at a baseline b0n of SW_BN
# (units 2^-128), the cover option at the threshold floor(beta - delta b0n) on the grid 2^-SW_CKEY (units 2^-128),
# or at a lower threshold already in use.
# The option kinds are pluggable: SW_COVER (maker, checker, Lean emitter of the cover option; today OptF) and SW_NEAR.

SW_BN = [1000, 1200, 1400, 1500, 1600, 1700, 1800, 2000, 2200, 2500, 3000]
SW_CKEY = 8
SW_PR, SW_PB, SW_PD = 40, 48, 64

def satUpQ(rho, x): return rho * x - rho * (rho - 1) * x ** 2 / 2

def coinQ(q):
    x = Fr(q, 2 ** 128)
    return x ** 2 / 2 ** 30 + x / 2 ** 100 + Fr(1, 2 ** 180)

def cUQ(b, a, N, m): return Fr(N, 2 ** b * 2 ** a) + m

def rho_baseSW(rho, x):
    """the conditions of checkNumSW on rho but E3 (monotone in rho on [3/2, 2])"""
    return (0 <= x and x <= Fr(1, 8) and Fr(3, 2) <= rho and rho <= 2 and
            Fr(1, 2) <= (rho - 1) * (1 - rho * x) and
            4032 * (2 - rho) * x / (1 - x) <= rho - 1 and
            2 - rho <= (1 - x) ** 65)

def rho_condsSW(rho, x, cU):
    """the conditions of checkNumSW on rho (with x, cU): each is monotone in rho on [3/2, 2]"""
    return (rho_baseSW(rho, x) and
            1 + (3 - rho) * x / (1 - x) + cU / (1 - x) ** 3 <= rho and
            0 <= cU)

F2_COIN_A, F2_COIN_B, F2_CUSHION = Fr(1, 2 ** 31), Fr(1, 2 ** 118), Fr(1, 2 ** 30)

def mOfSW(b, N, x, rho):
    """the per-entry cap m (route3.mOf): the E3 cap at rho less N/2^(b+a), the coin 2^-31 x + 2^-118 and 2^-30,
    down to 2^-40; 0 if not positive"""
    v = (rho - 1 - (3 - rho) * x / (1 - x)) * (1 - x) ** 3 - Fr(N, 2 ** (b + FA)) - F2_COIN_A * x - F2_COIN_B - F2_CUSHION
    return rdown(v, 40) if v > 0 else Fr(0)


def betaMaxSW(rho, x):
    return min(rho / (1 + (rho - 1) * x / (1 - x)), 2 * (1 - x), 3 * (1 - x) ** 2, 66 * (1 - x) ** 65, 67 * (1 - x) ** 66)

def deltaSW(rho, x): return (1 - rho * x + rho * (rho - 1) * x ** 2 / 2) * (2 - rho) * x / (1 - x)

def checkNumSW(rho, beta, delta, x, cU):
    """checkNumSW (SWRoute/ClosingReal.lean)"""
    return (rho_condsSW(rho, x, cU) and 0 <= beta and beta <= rho / (1 + (rho - 1) * x / (1 - x)) and
            beta <= 2 * (1 - x) and beta <= 3 * (1 - x) ** 2 and beta <= 66 * (1 - x) ** 65 and
            beta <= 67 * (1 - x) ** 66 and deltaSW(rho, x) <= delta)

def swMain_sides(K, N, qa, qb, rho, delta, BC, BN, Pb):
    """the two sides of swMainQ"""
    xa = Fr(qa, 2 ** 128)
    lhs = satUpQ(rho, xa) + qb * BC + delta * (qb * BN) + coinQ(qb) + Fr(qb, 2 ** 128) * Pb + Fr(qb + K + N, 2 ** 200)
    return lhs, 2 * xa + Fr(K, 2 ** 127)

def swMainQ(K, N, qa, qb, rho, delta, BC, BN, Pb):
    """swMainQ (SWRoute/ClosingReal.lean)"""
    lhs, rhs = swMain_sides(K, N, qa, qb, rho, delta, BC, BN, Pb)
    return lhs <= rhs

def choose_rhoSW(x, cU, P=None, okr=None):
    """the least rho = n / 2^P passing the rho conditions of checkNumSW (or okr, monotone), None if rho = 2 fails"""
    P = P or SW_PR
    def ok(n): return okr(Fr(n, 2 ** P)) if okr else rho_condsSW(Fr(n, 2 ** P), x, cU)
    lo, hi = 3 * 2 ** (P - 1) - 1, 2 ** (P + 1)       # lo fails (rho < 3/2)
    if not ok(hi): return None
    xf, cf = float(x), float(cU)
    if 0 < xf < 0.125:
        y = xf / (1 - xf)
        disc = (1 + xf) ** 2 - 6 * xf
        g = max(2 - 1 / (1 + 4032 * y), ((1 + xf) - math.sqrt(max(disc, 0))) / (2 * xf),
                2 - (1 - xf) ** 65, (1 + 3 * y + cf / (1 - xf) ** 3) / (1 + y))
        n0 = min(hi, max(lo + 1, math.ceil(g * 2 ** P)))
        for d in (2 ** 12, 2 ** 24):         # bracket the float guess
            if ok(n0) and not ok(max(lo, n0 - d)):
                lo, hi = max(lo, n0 - d), n0
                break
            if not ok(n0) and ok(min(hi, n0 + d)):
                lo, hi = n0, min(hi, n0 + d)
                break
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if ok(mid): hi = mid
        else: lo = mid
    return Fr(hi, 2 ** P)

def paramsSW(b, N, qb):
    """(rho, beta, delta, m) of an entry ending at qb, None if the side conditions fail"""
    x = Fr(qb, 2 ** 128)
    if not x <= Fr(1, 8): return None
    # E3 does not constrain rho, m takes its slack (m > 0 is monotone in rho)
    rho = choose_rhoSW(x, Fr(N, 2 ** (b + FA)), okr=lambda r: rho_baseSW(r, x) and mOfSW(b, N, x, r) > 0)
    if rho is None: return None
    m = mOfSW(b, N, x, rho)
    cU = cUQ(b, FA, N, m)
    beta = rdown(betaMaxSW(rho, x), SW_PB)
    delta = rup(deltaSW(rho, x), SW_PD)
    if not checkNumSW(rho, beta, delta, x, cU): return None
    return rho, beta, delta, m

F2_DIR = os.environ.get('F2_DIR', '/tmp/claude-0/-root-leanXMSS-leanSPHINCS-candidates/'
                        'a131ab4a-9415-4c48-ae68-08b3d654c282/scratchpad/rework/F2')

class TailPbadModel:
    """The tail term of an entry: Pb >= Pbad(m, qb, N) in the excess form (1 - m) Pbad, from F2's float bound
    (pi.py, FORS 19x9 at b = 24 only) times 1 + 2^-10, up to a dyadic with 60 bits (route3.PbFr, FORM=exc).
    MODEL: the certified tail (WP-F, scripts/fors_sw_forecast.py; TailOK in SWRoute/Closing.lean) replaces it."""
    def __init__(self):
        sys.path.insert(0, F2_DIR)
        import pi
        self.pi, self.cache = pi, {}
    def pb(self, b, N, m, qb):
        assert (TOTAL, b, FK, FA) == (24, 24, 19, 9), 'pi.py models FORS 19x9 at b = 24 only'
        key = (m, qb, N)
        if key not in self.cache:
            p = self.pi.Pbad(float(m), float(qb), N) * (1 - float(m)) * (1 + 2 ** -10)
            e = math.floor(math.log2(p)) - 60
            self.cache[key] = Fr(math.ceil(p * 2.0 ** -e), 1) * Fr(2) ** e
        return self.cache[key]
    def check(self, b, N, m, qb, Pb):
        """the tail bound of an entry: here, Pb at least the model's"""
        return self.pb(b, N, m, qb) <= Pb

class TailCertWPF:
    """The certified tail of an entry (WP-F): a TailCert (n0, theta_D, s, P, J) whose exact tail
    max(0, 1 - m) tailQ at (qb, m) is at most Pb (checkTail; scripts/fors_sw_forecast.py, SWRoute/ForecastCert.lean)."""
    def __init__(self):
        sys.modules.setdefault('fors_certificates', sys.modules[__name__])
        import fors_sw_forecast
        self.SF = fors_sw_forecast
    def pb_of(self, b, t, qb, m, c):
        """the Pb of the certificate c at (qb, m), rounded up to 40 significant bits as make_tailCert does; None if its
        side conditions fail there"""
        SF = self.SF
        if not (1 <= c.n0 and len(c.th) == c.n0 and 1 <= t.n1): return None
        for D in range(c.n0):
            th = SF.getD(c.th, D)
            if th < 0 or not all(th * SF.phiQ(FA, t.mu, j) < 2 ** c.s for j in range(FK)): return None
            if SF.vQ(b, FK, FA, t.mu, qb, m, c, D) < 0: return None
        tail = max(Fr(0), 1 - m) * SF.tailQ(b, FK, FA, t, qb, m, c)
        return rup(tail, 40 - math.floor(math.log2(float(tail))))
    def certify(self, b, t, qb, m, pool, Pmax):
        """(index in pool, Pb): a certificate of the pool whose Pb at (qb, m) is at most Pmax, else a new one"""
        for i, c in enumerate(pool):
            Pb = self.pb_of(b, t, qb, m, c)
            if Pb is not None and Pb <= Pmax and self.check(b, t, qb, m, c, Pb): return i, Pb
        c, Pb = self.SF.make_tailCert(b, FK, FA, t, qb, m)
        if Pb > Pmax:
            c, Pb = self.repair(b, t, qb, m, c, Pb)
        pool.append(c)
        return len(pool) - 1, Pb
    def repair(self, b, t, qb, m, c, Pb):
        """make_tailCert's golden-section search can return theta_D = 0 where a positive theta_D is far better
        (seen at D = 0); scan theta_D on a log grid and keep each improvement that passes vQ >= 0"""
        SF = self.SF
        F = SF._F(b, FK, FA, t.mu, qb)
        th = list(c.th)
        for D in range(c.n0):
            best = (F.logterm(D, float(th[D]), float(m)), th[D])
            for i in range(241):
                x = 10.0 ** (-3 + i / 24)
                v = F.logterm(D, x, float(m))
                if v < best[0]:
                    cand = rdown(Fr(x), 20)
                    old, th[D] = th[D], cand
                    ok = SF.vQ(b, FK, FA, t.mu, qb, m, SF.TailCert(c.n0, th, c.s, c.P, c.J), D) >= 0
                    th[D] = old
                    if ok: best = (v, cand)
            th[D] = best[1]
        c2 = SF.TailCert(c.n0, th, c.s, c.P, c.J)
        Pb2 = self.pb_of(b, t, qb, m, c2)
        if Pb2 is not None and Pb2 < Pb and self.check(b, t, qb, m, c2, Pb2): return c2, Pb2
        return c, Pb
    def check(self, b, t, qb, m, c, Pb): return self.SF.checkTail(b, FK, FA, t, qb, m, c, Pb)
    def lean(self, name, c): return 'def %s : SWRoute.TailCert := %s\n' % (name, self.SF.lean_tailCert(c))

SW_TAIL_SEARCH = TailPbadModel    # Pb while the chain is built
SW_TAIL_CERT = TailCertWPF        # the certified tails of the entries

# -- the option kinds (swap SW_COVER / SW_NEAR to change the options of the SW route) --

class CoverOptF:
    """The SW route's cover option: today's Chernoff option OptF (make_opt, checkOptF, buildOpt)."""
    name, lean_type, emittable = 'F', 'OptF', True
    def __init__(self):
        self.fms = {}
    def make(self, b, t, cthr):
        if id(t) not in self.fms: self.fms[id(t)] = (t, FModel(t))
        o, _ = make_opt(b, t, self.fms[id(t)][1], cthr)
        return o
    def check(self, b, t, o): return checkOptF(b, t, o)
    def large_maker(self): return None          # the large route: make_opt
    def lean(self, name, b, tab, t, o):
        return 'def %s : OptF := %s\n' % (name, lean_opt(b, tab, t, o))

P3_DIR = os.environ.get('FC_P3_DIR', '/tmp/claude-0/-root-leanXMSS-leanSPHINCS-candidates/'
                        'a131ab4a-9415-4c48-ae68-08b3d654c282/scratchpad/rework/P3')

class CoverOptJModel:
    """MODEL ONLY: P3's J-split option (fc_p3.make_optJ, P3_DIR; the kill test's settings NX = 11..15, per-n A2),
    for the numbers; it has no Lean form here (the Lean OptJ is on branch fors-split-j)."""
    name, lean_type, emittable = 'J', 'OptJ', False
    def __init__(self):
        sys.modules.setdefault('fcbase', sys.modules[__name__])
        sys.path.insert(0, P3_DIR)
        import fc_p3
        fc_p3.NX = (11, 12, 13, 14, 15); fc_p3.PERN_A2 = True
        self.P3 = fc_p3
    def make(self, b, t, cthr):
        o, _ = self.P3.make_optJ(b, t, None, cthr)
        return o
    def check(self, b, t, o): return self.P3.checkOptJ(b, t, o)
    def large_maker(self): return self.P3.make_optJ
    def lean(self, *args): raise NotImplementedError('the J option is a model here')

class NearOptNB:
    """The SW route's near option at a baseline: OptNB (scripts/fors_sw_near.py, CoverBound/NearOptionB.lean)."""
    def __init__(self):
        sys.modules.setdefault('fors_certificates', sys.modules[__name__])
        import fors_sw_near
        self.SN = fors_sw_near
    def make(self, b, t, cthr):
        o, _ = self.SN.make_optNB(TOTAL, b, FK, FA, t, cthr)
        return o
    def check(self, b, t, o): return self.SN.check_optNB(TOTAL, b, FK, FA, t, o)
    def lean(self, name, b, tab, t, o):
        again = self.SN.fill_optNB(TOTAL, b, FK, FA, t, o.c1, o.th, o.s, o.cthr)
        assert all(getattr(again, f) == getattr(o, f) for f in self.SN.OptNB.FIELDS), 'the scalars do not rebuild'
        return self.SN.lean_optNB(o, name, tab, TOTAL, b, FK, FA) + '\n'

SW_COVER_KINDS = {'F': CoverOptF, 'J': CoverOptJModel}
SW_COVER = 'F'        # the kind of the cover option (the one place to swap it)
SW_NEAR = NearOptNB

# -- the exact checker (SWRoute/Closing.lean) --

class CoverSW:
    def __init__(self, qtop, tab, opts, nopts, tails, entries):
        self.qtop, self.tab, self.opts, self.nopts, self.tails, self.entries = qtop, tab, opts, nopts, tails, entries

def checkEntrySW(b, k, a, K, N, qtop, t, opts, nopts, tails, e, tail):
    """checkEntrySW (SWRoute/Closing.lean); tail.check is checkTail"""
    qa, qb, rho, beta, delta, m, Pb, ic, inr, itl = e
    if not (0 <= ic < len(opts) and 0 <= inr < len(nopts) and 0 <= itl < len(tails)): return False
    o, n, tc = opts[ic], nopts[inr], tails[itl]
    return (qa <= qb and qb <= qtop and tail.check(b, t, qb, m, tc, Pb) and
            checkNumSW(rho, beta, delta, Fr(qb, 2 ** 128), cUQ(b, a, N, m)) and
            0 <= delta and 0 <= o.cthr and 0 <= n.cthr and o.cthr + delta * n.cthr <= beta / 2 ** 128 and
            0 <= o.B and 0 <= n.B and 0 <= Pb and swMainQ(K, N, qa, qb, rho, delta, o.B, n.B, Pb))

def chainSW(b, k, a, K, N, qtop, t, opts, nopts, tails, last, entries, tail):
    """chainSW (SWRoute/Closing.lean)"""
    for e in entries:
        if not (e[0] <= last and checkEntrySW(b, k, a, K, N, qtop, t, opts, nopts, tails, e, tail)): return False
        last = e[1] + 1
    return qtop < last

def checkCoverSW(H, b, k, a, K, N, qstart, c, cover, near, tail):
    """checkCoverSW (SWRoute/Closing.lean), with the checkers of the option kinds and of the tails"""
    assert (H, k, a) == (TOTAL, FK, FA)
    return (H == b and 31 <= b + a and (H + k * a + 255) // 256 == 1 and
            checkRate(b, N, c.qtop, c.tab) and checkPT(c.tab) and
            all(cover.check(b, c.tab, o) for o in c.opts) and all(near.check(b, c.tab, n) for n in c.nopts) and
            chainSW(b, k, a, K, N, c.qtop, c.tab, c.opts, c.nopts, c.tails, qstart, c.entries, tail))

# -- the builder --

class SWBuilder:
    def __init__(self, b, N, t, cover, near, bn=None, ckey=None, margin=0, tail=None):
        self.b, self.N, self.t, self.cover, self.near = b, N, t, cover, near
        self.tail = tail if tail is not None else SW_TAIL_SEARCH()
        self.K = kcredit(b)
        self.bn, self.ckey, self.margin = list(bn or SW_BN), ckey or SW_CKEY, Fr(margin)
        self.cov, self.nopt, self.prm = {}, {}, {}
        self.used_c, self.used_n = [], []
    def params(self, qb):
        if qb not in self.prm:
            p = paramsSW(self.b, self.N, qb)
            self.prm[qb] = None if p is None else p + (self.tail.pb(self.b, self.N, p[3], qb),)
        return self.prm[qb]
    def cover_opt(self, key):
        if key not in self.cov: self.cov[key] = self.cover.make(self.b, self.t, Fr(key, 2 ** self.ckey * 2 ** 128))
        return self.cov[key]
    def near_opt(self, c):
        if c not in self.nopt: self.nopt[c] = self.near.make(self.b, self.t, Fr(c, 2 ** 128))
        return self.nopt[c]
    def slack(self, qa, qb, rho, delta, o, n, Pb):
        """(rhs - lhs) / x_a of the main inequality: the slack per budget unit (target 2)"""
        lhs, rhs = swMain_sides(self.K, self.N, qa, qb, rho, delta, o.B, n.B, Pb)
        return (rhs - lhs) / Fr(qa, 2 ** 128)
    def choice(self, qa, qb, reuse=True):
        """the best passing (new options, -slack, key, b0n, rho, beta, delta, m, Pb) for [qa, qb], None if none"""
        p = self.params(qb)
        if p is None: return None
        rho, beta, delta, m, Pb = p
        best = None
        for c in self.bn:
            n = self.near_opt(c)
            kmax = math.floor((beta / 2 ** 128 - delta * n.cthr) * 2 ** 128 * 2 ** self.ckey)
            if kmax <= 0: continue
            keys = [kmax] + (sorted([k for k in self.used_c if k < kmax], reverse=True)[:3] if reuse else [])
            for key in keys:
                o = self.cover_opt(key)
                if not o.cthr + delta * n.cthr <= beta / 2 ** 128: continue
                sl = self.slack(qa, qb, rho, delta, o, n, Pb)
                if sl < self.margin: continue
                cand = ((key not in self.used_c) + (c not in self.used_n), -sl, key, c, rho, beta, delta, m, Pb)
                if best is None or cand[:2] < best[:2]: best = cand
        return best
    def build(self, qstart, qtop, maxent=2000):
        """entries from qstart to qtop, each as wide as it passes (raw: (qa, qb, rho, beta, delta, key, b0n, slack,
        m, Pb))"""
        qa, out = qstart, []
        while True:
            if len(out) >= maxent or self.choice(qa, qa) is None: return None, qa
            if self.choice(qa, qtop) is not None:
                qb = qtop
            else:
                def qb_of(i): return min(qtop, int(qa * 2.0 ** (i / 1024.0)))
                lo, i = 0, 1
                while qb_of(i) < qtop and self.choice(qa, qb_of(i)) is not None:
                    lo, i = i, i * 2
                hi = i
                while hi - lo > 1:
                    mid = (lo + hi) // 2
                    if self.choice(qa, qb_of(mid)) is not None: lo = mid
                    else: hi = mid
                qb = qb_of(lo)
                if lo == 0:
                    a_, z = qa, qb_of(1)
                    while z - a_ > 1:
                        mm = (a_ + z) // 2
                        if self.choice(qa, mm) is not None: a_ = mm
                        else: z = mm
                    qb = a_
            ch = self.choice(qa, qb)
            _, msl, key, c, rho, beta, delta, m, Pb = ch
            if key not in self.used_c: self.used_c.append(key)
            if c not in self.used_n: self.used_n.append(c)
            out.append((qa, qb, rho, beta, delta, key, c, -msl, m, Pb))
            if qb >= qtop: return out, None
            qa = qb + 1
    def cover_of(self, qtop, raw, tcert, verbose=False):
        """the CoverSW of a built chain: options in first-use order; each entry's search Pb replaced by a certified
        tail (tcert), reused across entries where it is no larger; None if an entry fails with its certified Pb"""
        ck = {k: i for i, k in enumerate(self.used_c)}
        nk = {c: i for i, c in enumerate(self.used_n)}
        pool, entries = [], []
        for (qa, qb, rho, beta, delta, key, c, _, m, Pb0) in raw:
            itl, Pb = tcert.certify(self.b, self.t, qb, m, pool, Pb0)
            if verbose: print('    tail at 2^%.4f: cert %d, Pb 2^%.2f (search 2^%.2f)' % (
                math.log2(qb), itl, math.log2(Pb), math.log2(Pb0)), flush=True)
            if Pb > Pb0 and self.slack(qa, qb, rho, delta, self.cover_opt(key), self.near_opt(c), Pb) < 0: return None
            entries.append((qa, qb, rho, beta, delta, m, Pb, ck[key], nk[c], itl))
        return CoverSW(qtop, self.t, [self.cover_opt(k) for k in self.used_c], [self.near_opt(c) for c in self.used_n],
                       pool, entries)

def large_startSW(b, N, maker=None, lo=-9.0, hi=-2.0, step=1 / 64, refine=6):
    """the least budget (lx grid, then bisection) from which the large route's light cover reaches 2^127"""
    tc = make_poisT(b, N, 2 ** 127)
    B = Builder(b, N, tc, FModel(tc), maker)
    def single(lx):
        q = int(2 ** (128 + lx))
        try:
            return B.ok(q, q) is not None
        except Exception:          # the float search found no option at this threshold
            return False
    lx, prev = lo, None
    while lx <= hi and not single(lx):
        prev, lx = lx, lx + step
    if lx > hi: return None
    if prev is not None:
        a_, z = prev, lx
        for _ in range(refine):
            m = (a_ + z) / 2
            if single(m): z = m
            else: a_ = m
        lx = z
    while lx <= hi:
        q = int(2 ** (128 + lx))
        if B.build(q, TOP=2 ** 127) is not None: return q
        lx += step / 8
    return None

def sw_small_lx(b, N, lo=-12.0, hi=-6.0, step=0.125):
    """the largest lx of the grid at which the small route passes"""
    best, lx = None, lo
    while lx <= hi + 1e-9:
        if small_route(b, N, lx, verbose=False) is not None: best = lx
        elif best is not None: break
        lx += step
    return best

def certify_sw(b, N, lx=None, cover='F', large=None, verbose=True, emit_large=True, tails=True, **kw):
    """the small route at lx (default: the largest on the 1/8 grid), the SW cover from qh + 1 and the large route
    from the SW cover's top + 1; None if a part fails. tails=False: the search's model tails only (no SW cover)."""
    ck = SW_COVER_KINDS[cover](); nk = SW_NEAR()
    lk = SW_COVER_KINDS[large or cover]() if (large or cover) != cover else ck
    if lx is None: lx = sw_small_lx(b, N)
    if lx is None:
        if verbose: print('N %d: the small route fails everywhere' % N, flush=True)
        return None
    s = small_route(b, N, lx, verbose)
    if s is None: return None
    qL = large_startSW(b, N, lk.large_maker())
    if qL is None:
        if verbose: print('  large route: no start found', flush=True)
        return None
    qtop = qL - 1
    if verbose: print('  large route (%s) from 2^%.4f; SW cover of [2^%.4f, 2^%.4f]' % (
        lk.name, math.log2(qL), math.log2(s['qh'] + 1), math.log2(qtop)), flush=True)
    t = make_poisT(b, N, qtop)
    assert checkPT(t) and checkRate(b, N, qtop, t)
    SB = SWBuilder(b, N, t, ck, nk, **kw)
    raw, stuck = SB.build(s['qh'] + 1, qtop)
    if raw is None:
        if verbose: print('  SW cover FAIL at 2^%.4f' % math.log2(stuck), flush=True)
        return None
    K = kcredit(b)
    if not tails:
        return dict(N=N, lx=lx, qh=s['qh'], sw=None, sw_raw=raw, large_start=qL)
    tk = SW_TAIL_CERT()
    sw = SB.cover_of(qtop, raw, tk, verbose)
    if sw is None:
        if verbose: print('  SW cover FAIL with the certified tails', flush=True)
        return None
    assert checkCoverSW(TOTAL, b, FK, FA, K, N, s['qh'] + 1, sw, ck, nk, tk), 'checkCoverSW fails'
    if verbose:
        print('  SW cover OK: %d entries, %d cover options (%s), %d near options, %d tail certificates' % (
            len(sw.entries), len(sw.opts), ck.name, len(sw.nopts), len(sw.tails)), flush=True)
    c = dict(h=TOTAL, shape=SHAPE, d=num_layers(), K=K, b=b, k=FK, a=FA, N=N, lx=lx, qh=s['qh'], rho=s['rho'],
             t=s['t'], o=s['o'], on=s['on'], sw=sw, sw_raw=raw, sw_kinds=(ck, nk, tk), large_start=qL,
             covers=[], heavy=[], complete=None)      # None: the large route only as found by large_startSW
    if emit_large and lk.name == 'F':
        r = large_covers(b, N, s['qh'], qL, verbose)
        assert r is not None, 'the large route fails from its start'
        c['covers'], c['heavy'], c['complete'] = r
    return c

def sw_report(c):
    """the entries of a SW cover, with the slack per budget unit of each at its width"""
    for (qa, qb, rho, beta, delta, key, bn, sl, m, Pb) in c['sw_raw']:
        print('  [2^%8.4f, 2^%8.4f] rho %.6f beta %.5f delta %.3e b0c %.4f b0n %d slack/unit %+.5f%s' % (
            math.log2(qa), math.log2(qb), float(rho), float(beta), float(delta), key / 2 ** SW_CKEY, bn, float(sl),
            '' if m is None else '  m %.4f Pb 2^%.2f' % (float(m), math.log2(Pb))))

def sw_scan(b, N, lx0, lx1, cover='F', step=1 / 16, **kw):
    """the K model's view: entries of fixed width 2^step from lx0 to lx1 at the SW table of qtop = 2^lx1, the best
    choice of each (fresh options allowed); returns the worst slack per unit and where"""
    ck = SW_COVER_KINDS[cover](); nk = SW_NEAR()
    qtop = int(2 ** (128 + lx1))
    t = make_poisT(b, N, qtop)
    SB = SWBuilder(b, N, t, ck, nk, margin=-1, **kw)
    worst, lx = None, lx0
    while lx < lx1 - 1e-12:
        qa, qb = int(2 ** (128 + lx)), min(qtop, int(2 ** (128 + lx + step)))
        ch = SB.choice(qa, qb, reuse=False)
        sl = None if ch is None else float(-ch[1])
        print('  lx %7.4f: slack/unit %s%s' % (lx, 'side conditions fail' if ch is None else '%+.5f' % sl,
              '' if ch is None else '  (b0c %.4f, b0n %d)' % (ch[2] / 2 ** SB.ckey, ch[3])), flush=True)
        if sl is None: return None, lx
        if worst is None or sl < worst[0]: worst = (sl, lx)
        lx += step
    return worst

SW_HEADER = '''import FORS.Certificates.Build
import FORS.SWRoute.Closing

/-! The certificate of %s (generated by
`scripts/fors_certificates.py sw-emit`, checked by the kernel with `decide +kernel`, exact rational
arithmetic, no `native_decide`), for three routes (`ForsPotential.det_bitsF3`):
  * the small route at `qh = %d`;
  * a SW cover of every budget from `qh + 1` to `%d` (`SWRoute.checkCoverSW`: a Poisson
    table, %d cover option(s), %d near option(s) at a baseline, %d tail certificate(s) and %d entries);
  * the large route's covers from the SW cover's top `+ 1`. -/

namespace FORS.Security.H0

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
-- one check at a time: with asynchronous elaboration the memory of the finished checks is kept
set_option Elab.async false
'''

def sw_block(out, c, tag):
    """the SW cover of a configuration and its check"""
    sw, (ck, nk, tk) = c['sw'], c['sw_kinds']
    assert ck.emittable, 'the %s cover option has no Lean form here' % ck.name
    b, N, K, H, k, a = c['b'], c['N'], c['K'], c['h'], c['k'], c['a']
    tab = 'tabsw_%s' % tag
    out.append('/-- Poisson table of the SW cover (budgets up to %d). -/' % sw.qtop)
    out.append('def %s : PoisT := %s\n' % (tab, lean_tab(sw.tab)))
    for i, o in enumerate(sw.opts):
        out.append('/-- Cover option %d of the SW cover (threshold %.6f / 2^128). -/' % (i, float(o.cthr * 2 ** 128)))
        out.append(ck.lean('swc_%s_%d' % (tag, i), b, tab, sw.tab, o))
    for i, n in enumerate(sw.nopts):
        out.append('/-- Near option %d of the SW cover (baseline %.6f / 2^128). -/' % (i, float(n.cthr * 2 ** 128)))
        out.append(nk.lean('swn_%s_%d' % (tag, i), b, tab, sw.tab, n))
    for i, tc in enumerate(sw.tails):
        out.append('/-- Tail certificate %d of the SW cover. -/' % i)
        out.append(tk.lean('swt_%s_%d' % (tag, i), tc))
    ents = ',\n    '.join(lean_entrySW(e) for e in sw.entries)
    out.append('/-- The SW cover: every budget from %d to %d. -/' % (c['qh'] + 1, sw.qtop))
    out.append('def sw_%s : SWRoute.CoverSW where\n  qtop := %d\n  tab := %s\n  opts := [%s]\n'
               '  nopts := [%s]\n  tails := [%s]\n  entries := [\n    %s]\n' % (
                   tag, sw.qtop, tab, ', '.join('swc_%s_%d' % (tag, i) for i in range(len(sw.opts))),
                   ', '.join('swn_%s_%d' % (tag, i) for i in range(len(sw.nopts))),
                   ', '.join('swt_%s_%d' % (tag, i) for i in range(len(sw.tails))), ents))
    out.append('theorem sw_%s_ok : SWRoute.checkCoverSW %d %d %d %d %d %d %d sw_%s = true := by decide +kernel\n'
               % (tag, H, b, k, a, K, N, c['qh'] + 1, tag))

def lean_entrySW(e):
    """an entry as a Lean tuple (qa, qb, ρ, β, δ, m, Pb, ic, in, itl)"""
    return '(%d, %d, %s, %s, %s, %s, %s, %d, %d, %d)' % (e[0], e[1], q(e[2]), q(e[3]), q(e[4]), q(e[5]), q(e[6]),
                                                      e[7], e[8], e[9])

def emit_sw(c, path):
    sw = c['sw']
    assert c['complete'], 'the large route is not complete'
    out = [SW_HEADER % (describe(c), c['qh'], sw.qtop, len(sw.opts), len(sw.nopts), len(sw.tails), len(sw.entries))]
    emit_one(out, c, None, middle=sw_block)
    out.append('end FORS.Security.H0\n')
    open(path, 'w').write('\n'.join(out))

def sw_args(argv):
    """H K A N [LX] and --cover F|J, --large F|J, --ckey n, --bn a,b,..., --margin m"""
    pos, kw, i = [], {}, 0
    while i < len(argv):
        if argv[i].startswith('--'):
            kw[argv[i][2:]] = argv[i + 1]; i += 2
        else:
            pos.append(argv[i]); i += 1
    h, k, a, N = int(pos[0]), int(pos[1]), int(pos[2]), int(float(pos[3]))
    lx = float(pos[4]) if len(pos) > 4 else None
    opts = dict(cover=kw.get('cover', SW_COVER), large=kw.get('large'))
    if 'ckey' in kw: opts['ckey'] = int(kw['ckey'])
    if 'bn' in kw: opts['bn'] = [int(v) for v in kw['bn'].split(',')]
    if 'margin' in kw: opts['margin'] = Fr(kw['margin'])
    set_config(h, 'layered', h, k, a)
    return h, N, lx, opts

if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else None
    if cmd == 'check':
        h, shape, b, N, lx = int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(float(sys.argv[5])), float(sys.argv[6])
        k, a = (int(sys.argv[7]), int(sys.argv[8])) if len(sys.argv) > 8 else (24, 10)
        c = certify_config(h, shape, b, N, lx, k=k, a=a)
        if c is None or not c['complete']:
            sys.exit('NOT certified')
    elif cmd == 'maxn':
        # maxn H SHAPE B N0 [STEP LXLO LXHI]: the largest N (to 1 part in 20000) that both routes certify at some
        # split lx of the grid LXLO, LXLO + STEP, ..., LXHI, starting from a certified N0
        h, shape, b, best = int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(float(sys.argv[5]))
        step, lx_lo, lx_hi = [float(a) for a in sys.argv[6:9]] if len(sys.argv) > 8 else (0.125, -11.5, -6.0)
        k, a = (int(sys.argv[9]), int(sys.argv[10])) if len(sys.argv) > 10 else (24, 10)
        def feasible(N, lx):
            try:
                c = certify_config(h, shape, b, N, lx, verbose=False, k=k, a=a)
            except Exception:       # the float search found no option
                return False
            return c is not None and c['complete']
        best_lx, lx, n0 = None, lx_lo, best
        while lx <= lx_hi + 1e-9:
            lo = best + max(1, best // 20000)
            if feasible(lo, lx):
                hi = lo + lo // 50
                while feasible(hi, lx):
                    lo, hi = hi, hi + hi // 50
                while hi - lo > max(1, lo // 20000):
                    mid = (lo + hi) // 2
                    if feasible(mid, lx): lo = mid
                    else: hi = mid
                best, best_lx = lo, lx
                print('lx %.5f -> N %d' % (lx, lo), flush=True)
            lx += step
        if best_lx is None:
            sys.exit('H %d %s b %d: nothing above N0 = %d was certified on this grid (N0 itself was not checked)'
                     % (h, shape, b, n0))
        print('H %d %s b %d max N ~ %d (lx %s)' % (h, shape, b, best, best_lx))
    elif cmd == 'scan':
        # small-route left-hand sides only, for several lx
        h, shape, b, N = int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(float(sys.argv[5]))
        set_config(h, shape, b)
        for lx in [float(a) for a in sys.argv[6:]]:
            qh = int(2 ** (128 + lx))
            t = make_poisT(b, N, qh)
            fm = FModel(t)
            on = make_optN(b, t)
            c = (2 ** b * on.En) / 2
            rho = choose_rho(qh)
            o, _ = make_opt(b, t, fm, rho / 2 ** 128)
            x = Fr(qh, 2 ** 128)
            rate = Fr(N, 2 ** b * 2 ** FA)
            near = (2 - rho + x + rate) * qh * c
            print('lx %s: rho %.6f 2^128B %.5f coin %.5f near %.5f lhs %.6f rate ok %s' % (
                lx, float(rho), float(2 ** 128 * o.B), float(Fr((2 * scanMb(b) - 1) * qh, scanMb(b) * 2 ** 129)),
                float(near), float(small_lhs(b, N, qh, rho, o.B, c)), rate <= rho - 1 - x), flush=True)
    elif cmd in ('emit', 'emit-lifetimes'):
        certs = []
        for (h, shape, b, N, lx, k, a) in configs():
            c = certify_config(h, shape, b, N, lx, k=k, a=a)
            assert c is not None and c['complete'], (h, shape, b, N, lx, k, a)
            certs.append(c)
        root = sys.argv[2] if len(sys.argv) > 2 else ROOT     # another root: a regression copy
        os.makedirs(os.path.join(root, 'FORS', 'Certificates'), exist_ok=True)
        for h in sorted({c['h'] for c in certs}):
            emit([c for c in certs if c['h'] == h], os.path.join(root, 'FORS', 'Certificates', 'H%d.lean' % h))
        # Lifetimes.lean only with emit-lifetimes
        if cmd == 'emit-lifetimes':
            emit_lifetimes(certs, os.path.join(root, 'FORS', 'Lifetimes.lean'))
        print('written')
    elif cmd in ('sw', 'sw-emit'):
        # sw H K A N [LX] [--cover F|J] [--large F|J] [--ckey n] [--bn ...]: the three routes of a layered key
        import time
        t0 = time.time()
        h, N, lx, opts = sw_args(sys.argv[2:])
        c = certify_sw(h, N, lx, emit_large=True, **opts)
        if c is None:
            sys.exit('NOT certified')
        sw_report(c)
        sl = min(e[-1] for e in c['sw_raw'])
        print('N %d: small route to qh = 2^%.4f (lx %s), SW cover to 2^%.4f: %d entries, %d + %d options, '
              'least slack/unit %+.6f; large route covers emitted: %s  (%.0fs)' % (
                  N, math.log2(c['qh']), c['lx'], math.log2(c['sw'].qtop), len(c['sw'].entries), len(c['sw'].opts),
                  len(c['sw'].nopts), float(sl), c['complete'], time.time() - t0), flush=True)
        if cmd == 'sw-emit':
            path = os.path.join(ROOT, 'FORS', 'Certificates', 'H%dSW.lean' % h)
            emit_sw(c, path)
            print('written %s (%d bytes)' % (path, os.path.getsize(path)))
    elif cmd == 'sw-scan':
        # sw-scan H K A N LX0 LX1 [--cover F|J]: fixed-width entries 2^(1/16), the worst slack per unit
        h, k, a, N, lx0, lx1 = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(float(sys.argv[5])), \
            float(sys.argv[6]), float(sys.argv[7])
        _, _, _, opts = sw_args(sys.argv[2:6] + sys.argv[8:])
        opts.pop('large', None)
        print('worst slack/unit, lx:', sw_scan(h, N, lx0, lx1, **opts))
    elif cmd == 'sw-maxn':
        # sw-maxn H K A N0 N1 [--cover F|J] [--tails 1]: the largest N in [N0, N1) the three routes certify (N0 must
        # pass); the search's model tails unless --tails 1 (certified tails, slower)
        h, k, a, lo, hi = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(float(sys.argv[5])), int(float(sys.argv[6]))
        argv = sys.argv[7:]
        tails = '--tails' in argv and argv[argv.index('--tails') + 1] == '1'
        if '--tails' in argv: del argv[argv.index('--tails'):argv.index('--tails') + 2]
        _, _, _, opts = sw_args(sys.argv[2:6] + argv)
        def feas(N):
            try:
                c = certify_sw(h, N, None, verbose=False, emit_large=False, tails=tails, **opts)
            except Exception as e:
                print('  N %d: %r' % (N, e), flush=True)
                return False
            return c is not None
        assert feas(lo), 'N0 is not certified'
        while hi - lo > max(1, lo // 4000):
            mid = (lo + hi) // 2
            r = feas(mid)
            print('  N %d: %s' % (mid, r), flush=True)
            if r: lo = mid
            else: hi = mid
        print('max N in [%d, %d) (2^%.5f)' % (lo, hi, math.log2(lo)), flush=True)
    else:
        sys.exit(__doc__)
