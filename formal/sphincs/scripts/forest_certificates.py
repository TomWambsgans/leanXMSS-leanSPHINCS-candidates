#!/usr/bin/env python3
"""Generate LeanForest/LifetimeCertificates.lean: exact rational certificates for the forest lifetimes.

Usage (from formal/sphincs):
    python3 scripts/forest_certificates.py tables        # print the moment tables (H0PTab.lean, H0NTab.lean)
    python3 scripts/forest_certificates.py check B N LX  # check one parameter set
    python3 scripts/forest_certificates.py emit          # write LeanForest/LifetimeCertificates.lean
then  lake build LeanForest.LifetimeCertificates  (the kernel re-checks every certificate).

For each parameter set (b, N, lx), with qh = floor(2^(128 + lx)):
  * a Poisson table at rate N/2^b + 2^127/((2^127 - 2^32) 2^b) (checkPT, checkRate);
  * the small route at qh: a Chernoff option at baseline rho/2^128 (checkOptF), the near certificate
    (checkOptN) and the rational check checkSmallF (BridgeDetCloseF.lean);
  * the large route: a cover of every budget q' in [qh + 1, 2^127] at the survival-weighted baseline
    (checkCoverW, BridgeDetW.lean).
Everything below mirrors the Lean checkers exactly (Fractions); floats only choose parameters.
The moment tables P1tab, P2tab (H0PTab.lean) and PHtab (H0NTab.lean) are read from the Lean sources.
"""

from fractions import Fraction as Fr
from math import comb
import itertools, math, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

# ---------------- exact helpers (H0SplitCert.lean) ----------------

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
KQ = Fr(1, 2 ** 26)

def kcredit(b): return 258 * 2 ** b + 2 * (26 - b)
def betaWQ(qb): return Fr(2 * (2 ** 128 - qb) + 1, 2 ** 256)

# ---------------- the moment tables ----------------

def parse_table(path, name):
    src = open(path).read()
    i = src.index('def %s : List ℚ := [' % name)
    j = src.index(']', i)
    body = src[src.index('[', i) + 1:j]
    out = []
    for item in body.split(','):
        item = item.strip()
        if not item:
            continue
        if '/' in item:
            a, b = item.split('/')
            out.append(Fr(int(a.strip()), int(b.strip())))
        else:
            out.append(Fr(int(item)))
    return out

P1 = parse_table(os.path.join(ROOT, 'LeanForest', 'H0PTab.lean'), 'P1tab')
P2 = parse_table(os.path.join(ROOT, 'LeanForest', 'H0PTab.lean'), 'P2tab')
PH = parse_table(os.path.join(ROOT, 'LeanForest', 'H0NTab.lean'), 'PHtab')
assert len(P1) == 151 and len(P2) == 151 and len(PH) == 151

def getD(lst, n): return lst[n] if 0 <= n < len(lst) else Fr(0)

# ---------------- the Poisson table (H0ForestCert.lean) ----------------

class PoisT:
    def __init__(self, m, P, J, pm):
        self.m, self.P, self.J, self.pm = m, P, J, pm
        self.mu = Fr(m, 2 ** 64)
        self.n1 = len(pm) - 2
        self.r = self.mu / (self.n1 + 2)
    def pb(self, n): return Fr(self.pm[n] if 0 <= n < len(self.pm) else 0, 2 ** self.P)

def scanMb(b): return 2 ** (26 - b)
def lmaxB(b, q): return 65 * ((q + 64 * scanMb(b) - 1) // (64 * scanMb(b))) + 2 ** 15
def denB(b, q): return 2 ** 128 - (q + 2 ** 32 + (scanMb(b) - 1) * lmaxB(b, q))
def fair_ok(b, q): return q + 2 ** 32 + (scanMb(b) - 1) * lmaxB(b, q) + (2 * scanMb(b) - 1) <= 2 ** 128
def rate_of(b, N, qtop): return Fr(N, 2 ** b) + Fr((2 * scanMb(b) - 1) * qtop, scanMb(b) * denB(b, qtop) * 2 ** b)

def denHB(b, q): return 2 ** 128 - (q // 2 + (scanMb(b) - 1) * lmaxB(b, q))
def fairH_ok(b, q): return q // 2 + (scanMb(b) - 1) * lmaxB(b, q) + (2 * scanMb(b) - 1) <= 2 ** 128
def rateH_of(b, N, qtop): return Fr(N + 1, 2 ** b) + Fr((2 * scanMb(b) - 1) * qtop, scanMb(b) * denHB(b, qtop) * 2 ** b)
def checkRateH(b, N, qtop, t): return fairH_ok(b, qtop) and rateH_of(b, N, qtop) <= t.mu

def make_poisT(b, N, qtop, n1=150, P=220, heavy=False):
    assert fairH_ok(b, qtop) if heavy else fair_ok(b, qtop)
    num = (rateH_of(b, N, qtop) if heavy else rate_of(b, N, qtop)) * 2 ** 64
    m = -((-num.numerator) // num.denominator)
    mu = Fr(m, 2 ** 64)
    J = int(float(mu) + 14 * math.sqrt(float(mu)) + 60)
    el = expLow(mu, J, P)
    x = Fr(2 ** P) / el
    pm = [-((-x.numerator) // x.denominator)]
    for n in range(n1 + 1):
        v = Fr(pm[-1] * m, (n + 1) * 2 ** 64)
        pm.append(-((-v.numerator) // v.denominator))
    return PoisT(m, P, J, pm)

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

# ---------------- options (H0ForestOpt.lean) ----------------

class OptF:
    pass

def gBound(o, n): return min(KQ * getD(P1, n) ** 8, KQ ** 2 * getD(P2, n) ** 8 / (4 * o.c1))
def hBound(o, n): return min(o.eC - 1, o.th * KQ * getD(P1, n) ** 8 + o.A2 * KQ ** 2 * getD(P2, n) ** 8)

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
    o = OptF()
    o.c1, o.th, o.s, o.cthr = c1, th, s, cthr
    n1 = t.n1
    o.eC = expUp(th * c1, s, t.P)
    o.A2 = rup((o.eC - 1 - th * c1) / c1 ** 2, 2 * 127 + PG)
    gs = [gBound(o, n) for n in range(n1 + 1)]
    hs = [hBound(o, n) for n in range(n1 + 1)]
    o.gt = convexify([rup(x, PG + 127) for x in convexify(gs)])
    o.ht = convexify([rup(x, PG + 64) for x in convexify(hs)])
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
        self.m1 = [2.0 ** 101 * float(P1[n]) ** 8 for n in range(n1 + 1)]
        self.m2 = [2.0 ** 202 * float(P2[n]) ** 8 for n in range(n1 + 1)]
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

# ---------------- the near certificate (H0NearOpt.lean) ----------------

class OptN:
    pass

def nBound(n): return 16 * KQ * getD(PH, n) * getD(P1, n) ** 7

def make_optN(b, t):
    o = OptN()
    n1 = t.n1
    o.nt = convexify([rup(x, PG + 127) for x in convexify([nBound(n) for n in range(n1 + 1)])])
    o.Jn = max(o.nt[-1] - o.nt[-2], 16 * KQ - o.nt[-1], Fr(0))
    o.En = rup(tailSum(t, o.nt, o.Jn), PG + 127 + 2 * b)
    return o

def checkOptN(t, o):
    n1 = t.n1
    if not (n1 <= 150 and len(o.nt) == n1 + 1 and checkLeaf(o.nt, o.Jn)): return False
    for n in range(n1 + 1):
        if not nBound(n) <= o.nt[n]: return False
    if not 16 * KQ <= o.nt[n1] + o.Jn: return False
    return tailSum(t, o.nt, o.Jn) <= o.En

# ---------------- the small route (BridgeDetCloseF.lean) ----------------

def checkSmallF(b, N, qh, rho, cthr, B, c):
    x = Fr(qh, 2 ** 128)
    rate = Fr(N * 134, 2 ** b * 2 ** 15)
    conds = [Fr(3, 2) <= rho, rho <= 2, 1 + 4032 * (2 - rho) * x <= rho, 1 + 66 * x <= rho, 64 * x <= 1,
             qh <= 2 ** 127, N <= 2 ** 70, cthr <= rho / 2 ** 128, 0 <= B, 0 <= c, rate <= rho - 1 - x]
    if not all(conds): return False
    lhs = rho + 2 ** 128 * B + Fr((2 * scanMb(b) - 1) * qh, scanMb(b) * 2 ** 129) + (2 - rho + x + rate) * qh * c + Fr(1, 2 ** 60)
    return lhs <= 2

def small_lhs(b, N, qh, rho, B, c):
    x = Fr(qh, 2 ** 128)
    rate = Fr(N * 134, 2 ** b * 2 ** 15)
    return rho + 2 ** 128 * B + Fr((2 * scanMb(b) - 1) * qh, scanMb(b) * 2 ** 129) + (2 - rho + x + rate) * qh * c + Fr(1, 2 ** 60)

def choose_rho(qh):
    x = Fr(qh, 2 ** 128)
    xf = float(x)
    r = max(1.5, 2 - 1 / (1 + 4032 * xf), 1 + 66 * xf)
    rho = Fr(math.ceil(r * 2 ** 40), 2 ** 40)
    while not (1 + 4032 * (2 - rho) * x <= rho and 1 + 66 * x <= rho and Fr(3, 2) <= rho):
        rho += Fr(1, 2 ** 40)
    return rho

# ---------------- the large route (BridgeDetW.lean) ----------------

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
    if b == 26:
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
    segs = [(qtop, False) for qtop in segments(b, qh)] + ([] if b == 26 else [(2 ** 127, True)])
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
    return dict(b=b, N=N, lx=lx, qh=qh, rho=rho, t=t, o=o, on=on, covers=covers, heavy=heavy, complete=complete)

# ---------------- Lean output ----------------

def q(x):
    x = Fr(x)
    return str(x.numerator) if x.denominator == 1 else '%d / %d' % (x.numerator, x.denominator)

def qlist(xs, indent='    '):
    return '[' + (',\n' + indent).join(q(x) for x in xs) + ']'

def nlist(xs, per=8, indent='    '):
    rows = [', '.join(str(x) for x in xs[i:i + per]) for i in range(0, len(xs), per)]
    return '[' + (',\n' + indent).join(rows) + ']'

def lean_opt(o, indent='    '):
    return ('⟨%s, %s, %s, %d, %s, %s,\n%s%s,\n%s%s,\n%s%s,\n%s%s,\n%s%s, %s, %s⟩' %
            (q(o.c1), q(o.th), q(o.cthr), o.s, q(o.eC), q(o.A2),
             indent, qlist(o.gt, indent + '  '), indent, q(o.Jg), indent, qlist(o.ht, indent + '  '), indent, q(o.Jh),
             indent, q(o.Eg), q(o.Ee), q(o.B)))

def lean_tab(t):
    return '⟨%d, %d, %d,\n    %s⟩' % (t.m, t.P, t.J, nlist(t.pm, 6, '     '))

def emit(certs, path):
    out = []
    out.append('''import LeanForest.BridgeHeavyCert

/-! Certificates for the proved forest lifetimes (generated by `scripts/forest_certificates.py`,
checked by the kernel with `decide +kernel`, exact rational arithmetic, no `native_decide`). For each
parameter set: a Poisson table, the small-route option at baseline `ρ / 2^128`, the near
certificate and `checkSmallF` at `qh ≈ 2^(128 + lx)`, and a cover of every larger budget up to
`2^127` at the survival-weighted baseline. -/

namespace LeanForest.Security.H0

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
''')
    for c in certs:
        b, N = c['b'], c['N']
        tag = 'b%d' % b
        out.append('/-- Poisson table of the small route, subtree height %d, %d signatures. -/' % (b, N))
        out.append('def tab_%s : PoisT := %s\n' % (tag, lean_tab(c['t'])))
        out.append('theorem tab_%s_ok : checkPT tab_%s = true := by decide +kernel\n' % (tag, tag))
        out.append('theorem rate_%s_ok : checkRate %d %d %d tab_%s = true := by decide +kernel\n' % (tag, b, N, c['qh'], tag))
        out.append('/-- The small-route option at baseline `ρ / 2^128`. -/')
        out.append('def small_%s : OptF := %s\n' % (tag, lean_opt(c['o'])))
        out.append('theorem small_%s_ok : checkOptF %d tab_%s small_%s = true := by decide +kernel\n' % (tag, b, tag, tag))
        on = c['on']
        out.append('/-- The near certificate. -/')
        out.append('def near_%s : OptN := ⟨%s,\n    %s, %s⟩\n' % (tag, qlist(on.nt, '      '), q(on.Jn), q(on.En)))
        out.append('theorem near_%s_ok : checkOptN tab_%s near_%s = true := by decide +kernel\n' % (tag, tag, tag))
        out.append('/-- The plain rate `ρ`. -/')
        out.append('def rho_%s : ℚ := %s\n' % (tag, q(c['rho'])))
        out.append('theorem check_%s_ok : ForsPotential.checkSmallF %d %d %d rho_%s small_%s.cthr small_%s.B\n'
                   '    ((2 ^ %d * near_%s.En : ℚ) / 2) = true := by decide +kernel\n' % (tag, b, N, c['qh'], tag, tag, tag, b, tag))
        for kind, lst, chk in (('', c['covers'], 'checkCoverW'), ('h', c['heavy'], 'checkCoverH')):
            for ci, cv in enumerate(lst):
                out.append('/-- Poisson table of %scover %d (budgets up to %d). -/' % ('heavy ' if kind else '', ci, cv['qtop']))
                out.append('def tabc%s_%s_%d : PoisT := %s\n' % (kind, tag, ci, lean_tab(cv['t'])))
                for k, o in enumerate(cv['opts']):
                    out.append('/-- Option %d of %scover %d. -/' % (k, 'heavy ' if kind else '', ci))
                    out.append('def large%s_%s_%d_%d : OptF := %s\n' % (kind, tag, ci, k, lean_opt(o)))
                opts = ', '.join('large%s_%s_%d_%d' % (kind, tag, ci, k) for k in range(len(cv['opts'])))
                ents = ',\n    '.join('(%d, %d, %d)' % e for e in cv['entries'])
                out.append('/-- %s %d: every budget from %d to %d. -/' % ('Heavy cover (one heavy message, one spare slot)' if kind else 'Cover', ci, cv['qstart'], cv['qtop']))
                out.append('def cover%s_%s_%d : CoverW where\n  qtop := %d\n  tab := tabc%s_%s_%d\n  opts := [%s]\n  entries := [\n    %s]\n' %
                           (kind, tag, ci, cv['qtop'], kind, tag, ci, opts, ents))
                out.append('theorem cover%s_%s_%d_ok : %s %d %d %d cover%s_%s_%d = true := by decide +kernel\n' %
                           (kind, tag, ci, chk, b, N, cv['qstart'], kind, tag, ci))
        if c['complete']:
            names = ', '.join('cover_%s_%d' % (tag, ci) for ci in range(len(c['covers'])))
            hnames = ', '.join('coverh_%s_%d' % (tag, ci) for ci in range(len(c['heavy'])))
            out.append('/-- The covers reach every budget below `2^127`. -/')
            out.append('theorem covers_%s_ok : ForsPotential.checkCoversH %d %d %d [%s] [%s] = true := by' % (tag, b, N, c['qh'] + 1, names, hnames))
            lems = ', '.join(['cover_%s_%d_ok' % (tag, ci) for ci in range(len(c['covers']))] +
                             ['coverh_%s_%d_ok' % (tag, ci) for ci in range(len(c['heavy']))])
            out.append('  simp only [ForsPotential.checkCoversH, ForsPotential.checkCoversHeavy, %s, Bool.true_and]' % lems)
            out.append('  decide +kernel\n')
    out.append('end LeanForest.Security.H0\n')
    open(path, 'w').write('\n'.join(out))

# Best known attack lifetimes (forest, with the WOTS+C unit-neighbour route; FOREST.md).
ATTACK = {26: 1.352e9, 20: 2.654e7, 14: 4.98e5, 13: 2.57e5, 12: 1.32e5, 10: 3.47e4, 8: 9.23e3}
# Proved lifetimes of the FORS variant (LeanSphincs.Lifetimes.requestedSecurity).
FORS = {26: 1156000000, 20: 22380000, 14: 412500, 13: 211900, 12: 108700, 10: 28600, 8: 7530}

def pname(b): return 'full' if b == 26 else 'pruned%d' % b

def emit_lifetimes(certs, path):
    out = ['''import LeanForest.LifetimeCertificates

/-! **Proved lifetimes of the forest variant** for the deterministic signer (seed-derived
randomizers): 127 classical bits against any adversary. Small budgets use the linear potential, the
one-coin cover potential at baseline `ρ / 2^128` and the contact bound A4 of the forest; large
budgets use the one-coin covers at the survival-weighted baseline. Every lifetime is at least the
proved lifetime of the FORS variant (`LeanSphincs.Lifetimes.requestedSecurity`). -/

open OracleComp OracleSpec ENNReal

namespace LeanForest.Lifetimes

open Security ForsPotential
''']
    for c in certs:
        b, N = c['b'], c['N']
        tag = 'b%d' % b
        name = pname(b)
        out.append('/-- Subtree height %d, %d signatures (%.1f%% of the best known attack\'s %.4g; the FORS variant: %d). -/'
                   % (b, N, 100.0 * N / ATTACK[b], ATTACK[b], FORS[b]))
        out.append('abbrev %s : Params := ⟨%d, %d, by decide⟩\n' % (name, b, N))
        out.append('/-- **127 bits for the deterministic signer** at subtree height %d and %d signatures. -/' % (b, N))
        if not c['complete']:
            out.append('-- The covers of this height stop below 2^127: no theorem yet.\n')
            continue
        names = ', '.join('H0.cover_%s_%d' % (tag, ci) for ci in range(len(c['covers'])))
        hnames = ', '.join('H0.coverh_%s_%d' % (tag, ci) for ci in range(len(c['heavy'])))
        out.append('theorem %s_bits : @Det.HasClassicalSecurityBitsDet %s 127 :=' % (name, name))
        out.append('  @det_bitsFH %s (by decide) %d %d rfl rfl %d H0.rho_%s H0.tab_%s H0.small_%s H0.near_%s H0.tab_%s_ok\n'
                   '    H0.rate_%s_ok H0.small_%s_ok H0.near_%s_ok H0.check_%s_ok [%s] [%s] H0.covers_%s_ok\n'
                   % (name, b, N, c['qh'], tag, tag, tag, tag, tag, tag, tag, tag, tag, names, hnames, tag))
    order = [26, 20, 14, 13, 12, 10, 8]
    have = {c['b'] for c in certs if c['complete']}
    if all(b in have for b in order):
        out.append('/-- **The forest lifetimes**: 127 bits at every subtree height. -/')
        out.append('theorem requestedSecurity :\n    ' + ' ∧\n    '.join(
            '@Det.HasClassicalSecurityBitsDet %s 127' % pname(b) for b in order) + ' :=')
        out.append('  ⟨' + ', '.join('%s_bits' % pname(b) for b in order) + '⟩\n')
    out.append('end LeanForest.Lifetimes\n')
    open(path, 'w').write('\n'.join(out))

# Parameter sets: (b, N, lx).
PARAMS = [
    (26, 1268000000, -10.0),
    (20, 23700000, -9.0),
    (14, 438800, -8.0),
    (13, 226100, -7.75),
    (12, 115800, -7.75),
    (10, 30650, -7.5),
    (8, 8110, -7.25),
]

if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'emit'
    if cmd == 'check':
        b, N, lx = int(sys.argv[2]), int(float(sys.argv[3])), float(sys.argv[4])
        certify(b, N, lx)
    elif cmd == 'emit1':
        b, N, lx = int(sys.argv[2]), int(float(sys.argv[3])), float(sys.argv[4])
        c = certify(b, N, lx)
        assert c is not None
        emit([c], os.path.join(ROOT, 'LeanForest', 'LifetimeCertificates.lean'))
        emit_lifetimes([c], os.path.join(ROOT, 'LeanForest', 'Lifetimes.lean'))
        print('written')
    elif cmd == 'maxn':
        # largest N (3 significant digits) with a certificate at one of the given lx
        b, lo, hi = int(sys.argv[2]), int(float(sys.argv[3])), int(float(sys.argv[4]))
        lxs = [float(a) for a in sys.argv[5:]]
        def feasible(N):
            for lx in lxs:
                if certify(b, N, lx, verbose=False) is not None:
                    return lx
            return None
        assert feasible(lo) is not None
        while hi - lo > max(1, lo // 1000):
            mid = (lo + hi) // 2
            r = feasible(mid)
            print('N %d -> %s' % (mid, r), flush=True)
            if r is not None: lo = mid
            else: hi = mid
        print('b %d max N ~ %d (lx %s)' % (b, lo, feasible(lo)))
    elif cmd == 'scan':
        # small-route left-hand sides only, for several lx
        b, N = int(sys.argv[2]), int(float(sys.argv[3]))
        t = make_poisT(b, N)
        fm = FModel(t)
        on = make_optN(b, t)
        c = (2 ** b * on.En) / 2
        for lx in [float(a) for a in sys.argv[4:]]:
            qh = int(2 ** (128 + lx))
            rho = choose_rho(qh)
            o, _ = make_opt(b, t, fm, rho / 2 ** 128)
            x = Fr(qh, 2 ** 128)
            rate = Fr(N * 134, 2 ** b * 2 ** 15)
            near = (2 - rho + x + rate) * qh * c
            print('lx %s: rho %.6f 2^128B %.5f coin %.5f near %.5f lhs %.6f rate ok %s' % (
                lx, float(rho), float(2 ** 128 * o.B), float(Fr((2 * scanMb(b) - 1) * qh, scanMb(b) * 2 ** 129)), float(near),
                float(small_lhs(b, N, qh, rho, o.B, c)), rate <= rho - 1 - x), flush=True)
    elif cmd == 'emit':
        certs = []
        for (b, N, lx) in PARAMS:
            c = certify(b, N, lx)
            assert c is not None, (b, N, lx)
            certs.append(c)
        emit(certs, os.path.join(ROOT, 'LeanForest', 'LifetimeCertificates.lean'))
        emit_lifetimes(certs, os.path.join(ROOT, 'LeanForest', 'Lifetimes.lean'))
        print('written')
