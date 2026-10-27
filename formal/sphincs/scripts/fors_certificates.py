#!/usr/bin/env python3
"""Generate LeanFors/Certificates/H*.lean: exact rational certificates for the vanilla (FORS) lifetimes.

A configuration is a total height H (22, 24, 26, 28), a shape (pruned: one tree with a kept subtree
of height B; layered: the hypertree of SPLITS, nothing pruned, B = H) and a signature limit N. Its
FTS is FORS with `k` trees of height `a = 10` (`scripts/scheme.py` `fors(h, shape, b)`, FORS_K).

Usage (from formal/sphincs):
    python3 scripts/fors_certificates.py check H SHAPE B N LX   # check one parameter set (exit status 1 if it fails)
    python3 scripts/fors_certificates.py emit                   # write LeanFors/Certificates/H*.lean
    python3 scripts/fors_certificates.py emit-lifetimes         # and LeanFors/Lifetimes.lean (P3's file)
    python3 scripts/fors_certificates.py maxn H SHAPE B N0 [STEP LXLO LXHI]   # search the largest N above N0
    python3 scripts/fors_certificates.py scan H SHAPE B N LX... # the terms of the small route at several lx
SHAPE is `pruned` or `layered` (then B = H). Then `lake build LeanFors.Lifetimes` (the kernel re-checks every
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
FA = 10             # a: the height of a FORS tree, the same in every configuration
FK = 25             # k: the number of FORS trees of the configuration (set_config)

# The FORS shape of each configuration (`scripts/scheme.py` `fors(h, shape, b)`, fe57807): the
# smallest k that reaches the cover attack's lifetime ATTACK at a = 10.
FORS_K = {(h, shape, b): (25 if (shape == 'layered' or b == h or (h, b) == (22, 20)) else 26)
          for h in (22, 24, 26, 28) for shape in ('pruned', 'layered')
          for b in (h, 20, 14, 13, 12, 10, 8)}

# The layer split of a layered key, top layer first (crates/sphincs `layered_heights`).
SPLITS = {22: (10, 6, 6), 24: (12, 6, 6), 26: (12, 7, 7), 28: (12, 8, 8)}

def set_config(h, shape='pruned', b=None):
    """Select the height, the shape and the FORS shape every function below works at."""
    global TOTAL, KQ, LAYERED_TOP, SHAPE, FK
    assert shape in ('pruned', 'layered')
    TOTAL, KQ, SHAPE = h, Fr(1, 2 ** h), shape
    LAYERED_TOP = SPLITS[h][0] if shape == 'layered' else None
    if b is not None:
        FK = FORS_K[(h, shape, b)]

def num_layers():
    return len(SPLITS[TOTAL]) if SHAPE == 'layered' else 1

def kcredit(b):
    """Key generation, in hash calls: 32 + 64 * 3 + 2 per leaf of the kept subtree and 2 per surrogate
    (kCreditF); a layered key builds its top layer, with no surrogate."""
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

P1, P2 = moment_tabs(FA)
assert len(P1) == 151 and len(P2) == 151

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
    def __init__(self, b, N, t, fm):
        self.b, self.N, self.t, self.fm = b, N, t, fm
        self.opts = {}
    def opt_for(self, key):
        if key not in self.opts:
            xg = Fr(2) ** Fr(key, GRID) if False else 2.0 ** (key / GRID)
            # the threshold betaWQ(qb) >= 2^-127 (1 - qb/2^128) > 2^-127 (1 - xg) for every qb <= xg 2^128
            cthr = dyadic_down((1 - xg) * (1 - 1e-9), 40) * Fr(1, 2 ** 127)
            o, _ = make_opt(self.b, self.t, self.fm, cthr)
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

def certify(b, N, lx, verbose=True):
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
    covers = []
    heavy = []
    qstart = qh + 1
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
    return dict(h=TOTAL, shape=SHAPE, d=num_layers(), K=kcredit(b), b=b, k=FK, a=FA, N=N, lx=lx, qh=qh,
                rho=rho, t=t, o=o, on=on, covers=covers, heavy=heavy, complete=complete)

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

def tag_of(c):
    return 'h%d_%s' % (c['h'], 'L' if c['shape'] == 'layered' else 'b%d' % c['b'])

def describe(c):
    if c['shape'] == 'layered':
        return 'height %d, layered (%s), %s signatures' % (c['h'], ' + '.join(map(str, SPLITS[c['h']])), format(c['N'], ','))
    if c['b'] == c['h']:
        return 'height %d, full key, %s signatures' % (c['h'], format(c['N'], ','))
    return 'height %d, kept subtree height %d, %s signatures' % (c['h'], c['b'], format(c['N'], ','))

HEADER = '''import LeanFors.Certificates.Build

/-! Certificates for the proved vanilla (FORS) lifetimes at total height %d (generated by
`scripts/fors_certificates.py`, checked by the kernel with `decide +kernel`, exact rational
arithmetic, no `native_decide`). For each configuration: a Poisson table, the small-route option at
baseline `ρ / 2^128`, the near certificate and `checkSmallF` at `qh ≈ 2^(128 + lx)`, and a cover of
every larger budget up to `2^127` at the survival-weighted baseline. The tables, the options and the
near certificates are rebuilt from their scalars (`poisOf`, `buildOpt`, `buildOptN`) and pass their
checkers by construction (`checkPT_poisOf`, `checkOptB_build`, `checkOptN_build`, `Build.lean`); a cover
is checked from its options and its table (`checkCoverW_of_pt`). The layered key reuses the full key's
certificate and checks again only its cover chains, where its keygen credit enters. -/

namespace LeanFors.Security.H0

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
    return f is not None and (c['b'], c['N'], c['qh'], c['rho']) == (f['b'], f['N'], f['qh'], f['rho']) and \
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
        set_config(c['h'], c['shape'], c['b'])
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
            out.append('theorem check_%s_ok : ForestPotential.checkSmallF %d %d %d %d %d rho_%s small_%s.cthr small_%s.B\n'
                       '    ((2 ^ %d * near_%s.En : ℚ) / 2) = true := by decide +kernel\n'
                       % (tag, H, b, a, N, c['qh'], tag, tag, tag, b, tag))
        else:
            out.append('/-! %s: the certificate of the %s (table, small-route option, near certificate, '
                       'cover tables and options), checked again only where the keygen credit `K = %d` enters: the '
                       'cover chains. -/\n' % (describe(c).capitalize(), describe(base), K))
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
        out.append('theorem covers_%s_ok : ForestPotential.checkCoversH %d %d %d %d %d %d %d [%s] [%s] = true := by'
                   % (tag, H, b, k, a, K, N, c['qh'] + 1, ', '.join(names['']), ', '.join(names['h'])))
        lems = ', '.join(['cover_%s_%d_ok' % (tag, ci) for ci in range(len(c['covers']))] +
                         ['coverh_%s_%d_ok' % (tag, ci) for ci in range(len(c['heavy']))])
        out.append('  simp only [ForestPotential.checkCoversH, ForestPotential.checkCoversHeavy, Bool.and_eq_true]')
        out.append('  exact ⟨%s, by decide +kernel⟩\n' % lems)
        if c['shape'] == 'pruned' and b == H:
            full = c
    out.append('end LeanFors.Security.H0\n')
    open(path, 'w').write('\n'.join(out))

# Attack lifetimes of the vanilla (FORS) FTS in the cover model (one expected cover per 2^127 digest
# queries), by height and kept subtree height (`scripts/scheme.py` `fors_log2_lifetime(h, b, a, k)` at
# the configuration's (k, a)). A layered key is attacked as the full key of the same height. These are
# the lifetimes FORS_K was chosen to reach.
ATTACK = {
    22: {22: 90609779, 20: 24410410, 14: 553479, 13: 286324, 12: 148101, 10: 39612, 8: 10595},
    24: {24: 362439088, 20: 30865956, 14: 592375, 13: 306357, 12: 158418, 10: 42348, 8: 11320},
    26: {26: 1449756325, 20: 33076204, 14: 633642, 13: 327609, 12: 169363, 10: 45251, 8: 12090},
    28: {28: 5799025272, 20: 35422057, 14: 677421, 13: 350154, 12: 180972, 10: 48329, 8: 12906},
}

HEIGHTS = (22, 24, 26, 28)

def pname(c):
    if c['shape'] == 'layered':
        return 'h%d_layered' % c['h']
    return 'h%d_full' % c['h'] if c['b'] == c['h'] else 'h%d_pruned%d' % (c['h'], c['b'])

LIFETIMES_HEADER = '''%s

/-! **Proofs of the proved lifetimes** (generated by `scripts/fors_certificates.py`): one theorem per
configuration, `ForestPotential.det_bitsFH` applied to the configuration's certificates
(`Certificates/H*.lean`). `Main.lean` states each of them again, independently of this file, and
proves it with the theorem here. Small budgets use the linear potential, the one-coin cover
potential at baseline `ρ / 2^128` and the contact bound A4 of the FORS leaves; large budgets use the
one-coin covers at the survival-weighted baseline. -/

namespace LeanFors.Lifetimes

open Security ForestPotential
'''

def lean_params(c):
    """The configuration as a `Params` term (`Params.pruned`, `Params.layered`, Scheme.lean): the FORS
    shape (k, a) is part of it."""
    if c['shape'] == 'layered':
        return '.layered %d %d %d %d %d %d' % (c['h'], c['d'], SPLITS[c['h']][1], c['k'], c['a'], c['N'])
    return '.pruned %d %d %d %d %d' % (c['h'], c['b'], c['k'], c['a'], c['N'])

def emit_lifetimes(certs, path):
    heights = sorted({c['h'] for c in certs})
    out = [LIFETIMES_HEADER % '\n'.join('import LeanFors.Certificates.H%d' % h for h in heights)]
    for c in certs:
        b, N, H, K, k, a = c['b'], c['N'], c['h'], c['K'], c['k'], c['a']
        tag, name, P = tag_of(c), pname(c), lean_params(c)
        att = ATTACK[H][H if c['shape'] == 'layered' else b]
        out.append("/-- %s (%.1f%% of the cover attack's %.4g). -/" % (describe(c).capitalize(), 100.0 * N / att, att))
        bt = c['base']
        names = ', '.join('H0.' + n for n in c['cover_names'][''])
        hnames = ', '.join('H0.' + n for n in c['cover_names']['h'])
        out.append('theorem %s_bits : SecurityBits (%s) 127 :=' % (name, P))
        # the explicit arguments of det_bitsFH: H b k a K N, then hH hb hk ha hK hN, then qh (P8's file)
        out.append('  @det_bitsFH (%s) (by decide) %d %d %d %d %d %d\n'
                   '    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) %d\n'
                   '    H0.rho_%s H0.tab_%s H0.small_%s H0.near_%s H0.tab_%s_ok H0.rate_%s_ok H0.small_%s_ok\n'
                   '    H0.near_%s_ok H0.check_%s_ok [%s] [%s] H0.covers_%s_ok\n'
                   % (P, H, b, k, a, K, N, c['qh'], bt, bt, bt, bt, bt, bt, bt, bt, bt, names, hnames, tag))
    out.append('end LeanFors.Lifetimes\n')
    open(path, 'w').write('\n'.join(out))

# Parameter sets of pruned keys, by height: (b, N, lx), b = h being the full key. N is the largest limit that
# `maxn` certified on the grid of lx (step 1/8), rounded down to four significant digits.
PARAMS = {
    22: [
        (22, 81860000, -9.375),
        (20, 21760000, -9.0),
        (14, 405300, -8.0),
        (13, 208500, -7.875),
        (12, 107200, -7.75),
        (10, 28410, -7.5),
        (8, 7514, -7.25),
    ],
    24: [
        (24, 336700000, -10.0),
        (20, 23830000, -9.125),
        (14, 441500, -8.125),
        (13, 226800, -8.0),
        (12, 116600, -7.75),
        (10, 30810, -7.625),
        (8, 8154, -7.375),
    ],
    26: [
        (26, 1381000000, -10.5),
        (20, 26030000, -9.25),
        (14, 480100, -8.25),
        (13, 246900, -8.0),
        (12, 126900, -7.875),
        (10, 33480, -7.625),
        (8, 8830, -7.375),
    ],
    28: [
        (28, 5634000000, -10.875),
        (20, 28350000, -9.375),
        (14, 522000, -8.25),
        (13, 267900, -8.125),
        (12, 137400, -8.0),
        (10, 36190, -7.75),
        (8, 9541, -7.5),
    ],
}

# Parameter sets of layered keys, by height: (N, lx). The index is not ground (b = h); the smaller keygen credit
# of the top layer alone does not move the largest N, which is the full key's.
LAYERED = {
    22: (81860000, -9.375),
    24: (336700000, -10.0),
    26: (1381000000, -10.5),
    28: (5634000000, -10.875),
}

def lifetime(h, shape, b=None):
    """The proved signature limit of a configuration, None if it has no certificate here."""
    if shape == 'layered':
        return LAYERED[h][0] if h in LAYERED else None
    return next((n for (bb, n, _) in PARAMS.get(h, []) if bb == b), None)

def attack(h, shape, b=None):
    """The cover attack's lifetime of a configuration, None if not computed."""
    return ATTACK.get(h, {}).get(h if shape == 'layered' else b)

def configs():
    """Every configuration with a parameter set: (h, shape, b, N, lx)."""
    out = []
    for h in HEIGHTS:
        for (b, N, lx) in PARAMS.get(h, []):
            out.append((h, 'pruned', b, N, lx))
        if h in LAYERED:
            N, lx = LAYERED[h]
            out.append((h, 'layered', h, N, lx))
    return out

def certify_config(h, shape, b, N, lx, verbose=True):
    set_config(h, shape, b)
    if shape == 'layered':
        assert b == h, 'a layered key keeps every index: B = H'
    return certify(b, N, lx, verbose)

if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else None
    if cmd == 'check':
        h, shape, b, N, lx = int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(float(sys.argv[5])), float(sys.argv[6])
        c = certify_config(h, shape, b, N, lx)
        if c is None or not c['complete']:
            sys.exit('NOT certified')
    elif cmd == 'maxn':
        # maxn H SHAPE B N0 [STEP LXLO LXHI]: the largest N (to 1 part in 20000) that both routes certify at some
        # split lx of the grid LXLO, LXLO + STEP, ..., LXHI, starting from a certified N0
        h, shape, b, best = int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(float(sys.argv[5]))
        step, lx_lo, lx_hi = [float(a) for a in sys.argv[6:9]] if len(sys.argv) > 8 else (0.125, -11.5, -6.0)
        def feasible(N, lx):
            try:
                c = certify_config(h, shape, b, N, lx, verbose=False)
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
        for (h, shape, b, N, lx) in configs():
            c = certify_config(h, shape, b, N, lx)
            assert c is not None and c['complete'], (h, shape, b, N, lx)
            certs.append(c)
        os.makedirs(os.path.join(ROOT, 'LeanFors', 'Certificates'), exist_ok=True)
        for h in sorted({c['h'] for c in certs}):
            emit([c for c in certs if c['h'] == h], os.path.join(ROOT, 'LeanFors', 'Certificates', 'H%d.lean' % h))
        # Lifetimes.lean is not this package's file: write it only when asked for
        if cmd == 'emit-lifetimes':
            emit_lifetimes(certs, os.path.join(ROOT, 'LeanFors', 'Lifetimes.lean'))
        print('written')
    else:
        sys.exit(__doc__)
