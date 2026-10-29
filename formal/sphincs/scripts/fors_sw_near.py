#!/usr/bin/env python3
"""The near H-term option at a baseline (OptNB, CoverBound/NearOptionB.lean) for the SW route.

The near price of a digest is sum_l y_l, y_l = kappa yN(marks at index l) (priceNear_decomp), and the
SW route reserves the near H-term at a baseline b0 >= cthr: E[(sum_l y_l - b0)^+] over iid Poisson(mu)
view counts (hTermO, poisIID). The option splits it as the cover option does (Base/Split.lean),
    (sum_l y_l - c)^+ <= sum_l (y_l - c1)^+ + e^{-theta c} / (e theta) prod_l e^{theta min(y_l, c1)},
and bounds each per-index average with n views by the mean m1N(n) = nBound(n) >= E[y | n] and the
support y <= UN(n) = k 2^-H (min(n, A) / A)^(k-1), A = 2^a, through chords:
  * (y - c1)^+ <= y (1 - c1 / UN)^+                    on [0, UN]   ->  g(n) = m1N (1 - c1 / UN)^+;
  * e^{theta min(y, c1)} <= 1 + y (e^{theta z} - 1) / z, z = min(UN, c1)  ->  h(n) = min(eC - 1, m1N sl(n)),
    sl(n) = (eC - 1) / c1 if c1 <= UN(n), else (expUp(theta UN) - 1) / UN.
These are at least as tight as the "old split, mean+support (chord)" option of the K model (near.py with
m = 0, chord = True: its g = min(m1N, UN m1N / (4 c1)) and h = min(eH - 1, theta m1N + A2(n) UN m1N) are
the chords' upper bounds). Then B = 2^b Eg + sqUp(1 + Eh) / (expLow(theta cthr) e theta), as OptF.

API:
    make_optNB(H, b, k, a, t, cthr)  ->  (option, float estimate)   (float search of c1, theta; exact tables)
    fill_optNB(H, b, k, a, t, c1, th, s, cthr)                        (buildOptNB: the option from its scalars)
    check_optNB(H, b, k, a, t, o)                                     (checkOptNB, exactly)
    lean_optNB(o, name, tab)                                          (the Lean definition and its check)
Every exact function mirrors the Lean definition of the same name (Fractions); floats only choose c1, theta.

    python3 scripts/fors_sw_near.py        # 19x9 at N = 2^24: the certified 2^128 B at several baselines
"""
from fractions import Fraction as Fr
import math, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fors_certificates as fc

PG = 64

# ---------------- exact (CoverBound/NearOptionB.lean) ----------------

def kQ(H): return Fr(1, 2 ** H)

def p1tab(a, n):
    """(P1tab a).getD n 0"""
    return Fr(fc.p1N(a, n), 2 ** 128) if 0 <= n <= 150 else Fr(0)

def nBoundQ(H, k, a, n):
    """nBound H k a n (CoverBound/NearOption.lean)"""
    return k * kQ(H) * p1tab(a, n) ** (k - 1)

def UNQ(H, k, a, n):
    """the support bound of the near value at an index with n views: k 2^-H (min(n, A) / A)^(k-1)"""
    A = 2 ** a
    return k * kQ(H) * Fr(min(n, A), A) ** (k - 1)

def qdiv(x, y):
    """division in ℚ (x / 0 = 0)"""
    return Fr(0) if y == 0 else x / y

def gNB(H, k, a, o, n):
    u = UNQ(H, k, a, n)
    if u <= o.c1: return Fr(0)
    return nBoundQ(H, k, a, n) * (1 - qdiv(o.c1, u))

def slNB(H, k, a, P, o, n):
    u = UNQ(H, k, a, n)
    if o.c1 <= u: return qdiv(o.eC - 1, o.c1)
    return qdiv(fc.expUp(o.th * u, o.s, P) - 1, u)

def hNB(H, k, a, P, o, n):
    return min(o.eC - 1, nBoundQ(H, k, a, n) * slNB(H, k, a, P, o, n))

def leafJ(n1, tab, cap):
    return max(max(tab[n1] - tab[n1 - 1], cap - tab[n1]), Fr(0))

def boundNB(b, t, o):
    """2^b Eg + sqUp(1 + Ee) / (expLow(theta cthr) e theta)"""
    return 2 ** b * o.Eg + fc.sqUp(t.P, b, 1 + o.Ee) / (fc.expLow(o.th * o.cthr, t.J, t.P) * fc.ELOW * o.th)

class OptNB:
    FIELDS = ('c1', 'th', 'cthr', 's', 'eC', 'gt', 'Jg', 'ht', 'Jh', 'Eg', 'Ee', 'B')
    def __repr__(self):
        return 'OptNB(c1=%.4f, th*c1=%.4f, cthr=%.4f, s=%d, 2^128 B=%.6f)' % (
            float(self.c1 * 2 ** 128), float(self.th * self.c1), float(self.cthr * 2 ** 128), self.s,
            float(self.B * 2 ** 128))

def fill_optNB(H, b, k, a, t, c1, th, s, cthr):
    """the option from its scalars (buildOptNB)"""
    o = OptNB()
    o.c1, o.th, o.s, o.cthr = Fr(c1), Fr(th), s, Fr(cthr)
    n1 = t.n1
    o.eC = fc.expUp(o.th * o.c1, s, t.P)
    o.gt = fc.convexify([fc.rup(gNB(H, k, a, o, n), PG + 127) for n in range(n1 + 1)])
    o.ht = fc.convexify([fc.rup(hNB(H, k, a, t.P, o, n), PG + 64) for n in range(n1 + 1)])
    o.Jg = leafJ(n1, o.gt, k * kQ(H))
    o.Jh = leafJ(n1, o.ht, o.eC - 1)
    o.Eg = fc.rup(fc.tailSum(t, o.gt, o.Jg), PG + 127 + 2 * b)
    o.Ee = fc.rup(fc.tailSum(t, o.ht, o.Jh), PG + 2 * b)
    o.B = fc.rup(boundNB(b, t, o), PG + 127)
    return o

def check_optNB(H, b, k, a, t, o):
    """checkOptNB H b k a t o"""
    n1 = t.n1
    if not (0 < o.c1 and 0 < o.th and 0 <= o.cthr and o.th * o.c1 < 2 ** o.s): return False
    if not fc.expUp(o.th * o.c1, o.s, t.P) <= o.eC: return False
    if not (n1 <= 150 and len(o.gt) == n1 + 1 and len(o.ht) == n1 + 1): return False
    if not (fc.checkLeaf(o.gt, o.Jg) and fc.checkLeaf(o.ht, o.Jh)): return False
    for n in range(n1 + 1):
        if not gNB(H, k, a, o, n) <= o.gt[n]: return False
        if not hNB(H, k, a, t.P, o, n) <= o.ht[n]: return False
    if not k * kQ(H) <= o.gt[n1] + o.Jg: return False
    if not o.eC - 1 <= o.ht[n1] + o.Jh: return False
    if not fc.tailSum(t, o.gt, o.Jg) <= o.Eg: return False
    if not fc.tailSum(t, o.ht, o.Jh) <= o.Ee: return False
    if not boundNB(b, t, o) <= o.B: return False
    return 0 <= o.Eg and 0 <= o.Ee

# ---------------- float search (units 2^-128) ----------------

def _conv(v):
    h = [v[0]]
    for i in range(1, len(v)):
        h.append(max(v[1], h[0]) if i == 1 else max(v[i], 2 * h[-1] - h[-2]))
    return h

class NBModel:
    def __init__(self, H, k, a, t):
        mu = float(t.mu)
        self.n1 = t.n1
        self.ps = [math.exp(-mu + n * math.log(mu) - math.lgamma(n + 1)) if mu > 0 else float(n == 0)
                   for n in range(t.n1 + 1)]
        self.m1 = [float(nBoundQ(H, k, a, n) * 2 ** 128) for n in range(t.n1 + 1)]
        self.U = [float(UNQ(H, k, a, n) * 2 ** 128) for n in range(t.n1 + 1)]
        self.cap = k * 2.0 ** (128 - H)
    def B(self, L, c, c1, th):
        if c1 <= 0 or th <= 0 or th * c1 > 700: return 1e300
        eH = math.expm1(th * c1)
        g, h = [], []
        for m, u in zip(self.m1, self.U):
            g.append(0.0 if u <= c1 else m * (1 - c1 / u))
            sl = eH / c1 if c1 <= u else (math.expm1(th * u) / u if u > 0 else 0.0)
            h.append(min(eH, m * sl))
        g, h = _conv(g), _conv(h)
        Eg = sum(p * x for p, x in zip(self.ps, g))
        Eh = sum(p * x for p, x in zip(self.ps, h))
        lt = L * math.log1p(Eh) - th * c - 1 - math.log(th)
        return L * Eg + math.exp(min(lt, 700))
    def best(self, L, c):
        from scipy.optimize import minimize
        f = lambda z: self.B(L, c, math.exp(z[0]), math.exp(z[1]))
        best = None
        for fc1 in (0.4, 0.5, 0.6, 0.75, 0.9):
            for t0 in (4.0, 6.0, 8.0, 12.0, 16.0):
                r = minimize(f, [math.log(fc1 * c), math.log(t0 / c)], method='Nelder-Mead',
                             options=dict(maxiter=4000, xatol=1e-9, fatol=1e-14))
                if best is None or r.fun < best.fun: best = r
        return best.fun, math.exp(best.x[0]), math.exp(best.x[1])

_MODELS = {}

def make_optNB(H, b, k, a, t, cthr):
    """the option at the exact threshold cthr (absolute units), and the float estimate of B (units 2^-128)"""
    key = (H, k, a, t.m, t.P, t.J, t.n1)
    if key not in _MODELS: _MODELS[key] = NBModel(H, k, a, t)
    nm = _MODELS[key]
    val, c1s, ths = nm.best(2 ** b, float(Fr(cthr) * 2 ** 128))
    c1 = fc.dyadic(c1s, 24) * Fr(1, 2 ** 128)
    th = fc.dyadic(ths, 24) * 2 ** 128
    s = max(0, math.ceil(math.log2(float(th * c1) + 1e-300)) + 12)
    o = fill_optNB(H, b, k, a, t, c1, th, s, Fr(cthr))
    assert check_optNB(H, b, k, a, t, o)
    return o, val

# ---------------- Lean ----------------

def lean_optNB(o, name, tab, H=None, b=None, k=None, a=None):
    """`def name : OptNB := buildOptNB H b k a tab c1 θ s cthr` (the configuration defaults to fc's)"""
    H = fc.TOTAL if H is None else H
    b = fc.TOTAL if b is None else b
    k = fc.FK if k is None else k
    a = fc.FA if a is None else a
    return 'def %s : OptNB := buildOptNB %d %d %d %d %s\n    (%s) %s %d\n    (%s)' % (
        name, H, b, k, a, tab, fc.q(o.c1), fc.q(o.th), o.s, fc.q(o.cthr))

def lean_optNB_check(o, name, tab, t, H=None, b=None, k=None, a=None):
    """the theorem that the option passes checkOptNB, and the pair (cthr, B) it certifies"""
    H = fc.TOTAL if H is None else H
    b = fc.TOTAL if b is None else b
    k = fc.FK if k is None else k
    a = fc.FA if a is None else a
    return ('theorem %s_ok : checkOptNB %d %d %d %d %s %s = true := by decide +kernel\n\n'
            'theorem %s_cB : (%s.cthr, %s.B) = ((%s : ℚ), (%s : ℚ)) := by decide +kernel') % (
        name, H, b, k, a, tab, name, name, name, name, fc.q(o.cthr), fc.q(o.B))

if __name__ == '__main__':
    import time
    fc.set_config(24, 'layered', 24, 19, 9)
    t = fc.make_poisT(24, 2 ** 24, 2 ** 124)
    assert fc.checkPT(t) and fc.checkRate(24, 2 ** 24, 2 ** 124, t)
    print('mu = %.12f' % float(t.mu))
    for c in (1200, 1500, 1600, 1800, 2000, 2500):
        t0 = time.time()
        o, v = make_optNB(24, 24, 19, 9, t, Fr(c, 2 ** 128))
        print('b0 %4d: float %.4f  certified 2^128 B = %.6f  (c1 %.1f, theta c = %.3f, s %d)  %.1fs' % (
            c, v, float(o.B * 2 ** 128), float(o.c1 * 2 ** 128), float(o.th * o.cthr), o.s, time.time() - t0),
            flush=True)
