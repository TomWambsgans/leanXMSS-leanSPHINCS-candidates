#!/usr/bin/env python3
"""Generate LeanSphincs/LifetimeCertificates.lean: exact rational certificates for the proved lifetimes.

Usage (from formal/sphincs):  python3 scripts/lifetime_certificates.py
then  lake build LeanSphincs.LifetimeCertificates  (the kernel re-checks every certificate).

For each parameter set (b, N, lx), with qh = floor(2^(128 + lx)):
  * the large route: a split cover of every budget q' in [qh, 2^127] at the survival-weighted baseline
    (checkCoverSW, H0SplitCert.lean / BridgeDetW.lean): a Poisson table and Chernoff options;
  * the small route at qh: the threshold option at baseline rho/2^128 (checkThreshS), the near-cover
    certificate (checkNear, BridgeForsNear.lean) and the rational check checkSmallA (BridgeArmSmall.lean).
Everything below mirrors the Lean checkers exactly (Fractions); floats are only used to choose
parameters. Pure Python 3, no dependencies.
"""

from fractions import Fraction as Fr
import math

def kcredit(b): return 258 * 2 ** b + 2 * (26 - b)

def floordiv_fr(x, P):
    return (x.numerator * 2 ** P) // x.denominator

def rdown(x, P): return Fr(floordiv_fr(x, P), 2 ** P)
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

TWO266 = 2 ** 266
def yQ(n): return Fr(n ** 24, TWO266)
ELOW = Fr(27182818283, 10 ** 10)

def betaQ(qb):
    """Weighted large-route baseline `betaWQ` (BridgeSatWRoutes.lean)."""
    return Fr(2 * (2 ** 128 - qb) + 1, 2 ** 256)

class Table:
    def __init__(self, m, P, J, pm, T):
        self.m, self.P, self.J, self.pm, self.T = m, P, J, pm, T
        self.mu = Fr(m, 2 ** 64)
        self.n1 = len(pm) - 2
        self.rho = self.mu * (self.n1 + 2) ** 23 / Fr((self.n1 + 1) ** 24)
    def pb(self, n): return Fr(self.pm[n] if n < len(self.pm) else 0, 2 ** self.P)
    def to_json(self): return {'m': self.m, 'P': self.P, 'J': self.J, 'pm': self.pm, 'T': [self.T.numerator, self.T.denominator]}

def check_table(b, N, t):
    if not len(t.pm) >= 2: return False
    if not Fr(N, 2 ** b) + Fr(2 ** 127) / ((2 ** 127 - 2 ** 32) * 2 ** b) <= t.mu: return False
    if not Fr(2 ** t.P) <= t.pm[0] * expLow(t.mu, t.J, t.P): return False
    for n in range(len(t.pm) - 1):
        if not t.pm[n] * t.m <= t.pm[n + 1] * ((n + 1) * 2 ** 64): return False
    if not t.rho < 1: return False
    if not t.pb(t.n1 + 1) * (t.n1 + 1) ** 24 <= t.T * (1 - t.rho): return False
    return True

def make_table(b, N, P=100, J=None, n1=None, PT=64):
    num = (Fr(N, 2 ** b) + Fr(2 ** 127) / ((2 ** 127 - 2 ** 32) * 2 ** b)) * 2 ** 64
    m = -((-num.numerator) // num.denominator)
    mu = Fr(m, 2 ** 64)
    muf = float(mu)
    if J is None: J = int(muf + 14 * math.sqrt(muf) + 60)
    if n1 is None: n1 = int(muf + 16 * math.sqrt(muf) + 50)
    el = expLow(mu, J, P)
    x = Fr(2 ** P) / el
    pm = [-((-x.numerator) // x.denominator)]
    for n in range(n1 + 1):
        v = Fr(pm[-1] * m, (n + 1) * 2 ** 64)
        pm.append(-((-v.numerator) // v.denominator))
    t = Table(m, P, J, pm, Fr(0))
    T = rup(t.pb(n1 + 1) * (n1 + 1) ** 24 / (1 - t.rho), PT) if t.rho < 1 else None
    t.T = T
    return t

class Opt:
    def __init__(self, c1, th, s, cthr, eC=None, Eh=None, Ee=None, B=None):
        self.c1, self.th, self.s, self.cthr = c1, th, s, cthr
        self.eC, self.Eh, self.Ee, self.B = eC, Eh, Ee, B
    def tup(self): return (self.c1, self.th, self.s, self.cthr, self.eC, self.Eh, self.Ee, self.B)

def eVal(th, c1, eC, s, P, n):
    y = yQ(n)
    if y < c1:
        u = th * y
        if u * 2 ** 20 <= 1: return expUp(u, 0, P)
        return expUp(u, s, P)
    return eC

def opt_sums(b, t, o):
    sh = sum((t.pb(n) * max(yQ(n) - o.c1, Fr(0)) for n in range(t.n1 + 1)), Fr(0)) + yQ(1) * t.T
    se = sum((t.pb(n) * (eVal(o.th, o.c1, o.eC, o.s, t.P, n) - 1) for n in range(t.n1 + 1)), Fr(0)) + \
        (o.eC - 1) * t.T / (t.n1 + 1) ** 24
    return sh, se

def opt_B(b, t, o):
    return 2 ** b * o.Eh + sqUp(t.P, b, 1 + o.Ee) / (expLow(o.th * o.cthr, t.J, t.P) * ELOW * o.th)

def fill_opt(b, t, o, PR=64):
    """compute eC, Eh, Ee, B (rounded up) exactly as the Lean checker requires"""
    o.eC = expUp(o.th * o.c1, o.s, t.P)
    sh, se = opt_sums(b, t, o)
    o.Eh = rup(sh, PR + 266)  # Eh is ~2^-127 scale; keep relative precision
    o.Ee = rup(se, PR + 2 * b)
    o.B = rup(opt_B(b, t, o), PR + 127)
    return o

def check_opt(b, t, o):
    if not (o.th > 0 and o.c1 >= 0 and o.cthr >= 0 and o.th * o.c1 < 2 ** o.s): return False
    if not expUp(o.th * o.c1, o.s, t.P) <= o.eC: return False
    sh, se = opt_sums(b, t, o)
    if not sh <= o.Eh: return False
    if not se <= o.Ee: return False
    if not opt_B(b, t, o) <= o.B: return False
    return True

def entry_ok(b, N, o, qa, qb):
    if not (2 * qb <= 2 ** 128): return False
    if not (o.cthr <= betaQ(qb)): return False
    lhs = qb * o.B + Fr(qb + kcredit(b) + N, 2 ** 200)
    rhs = Fr(qa, 2 ** 128) ** 2 + Fr(kcredit(b), 2 ** 127)
    return lhs <= rhs

def check_cover(b, N, qstart, t, opts, entries, verbose=False):
    if not check_table(b, N, t):
        if verbose: print('table fails')
        return False
    for i, o in enumerate(opts):
        if not check_opt(b, t, o):
            if verbose: print('opt fails', i)
            return False
    last = qstart
    for (qa, qb, j) in entries:
        if not (qa <= last): return False
        if not (j < len(opts)): return False
        if not entry_ok(b, N, opts[j], qa, qb):
            if verbose: print('entry fails', qa, qb, j)
            return False
        last = qb + 1
    return 2 ** 127 < last

# ---------------- float search ----------------
LN2 = math.log(2)

class FLeaf:
    """float model in scaled units (y' = 2^127 yQ, beta' = 2^127 beta)"""
    def __init__(self, t):
        self.mu = float(t.mu)
        nmax = t.n1 + 1
        self.ps = [math.exp(-self.mu + n * math.log(self.mu) - math.lgamma(n + 1)) if n > 0 else math.exp(-self.mu)
                   for n in range(nmax)]
        self.ys = [math.exp(24 * math.log(n) - 139 * LN2) if n > 0 else 0.0 for n in range(nmax)]
    def Eh(self, c1): return sum(p * max(y - c1, 0.0) for p, y in zip(self.ps, self.ys))
    def logEe(self, c1, th):
        return math.log(sum(p * math.exp(th * min(y, c1)) for p, y in zip(self.ps, self.ys)))
    def H(self, L, c1, th, c):
        v = L * self.logEe(c1, th) - th * c - 1 - math.log(th)
        return L * self.Eh(c1) + math.exp(min(v, 700))
    def best(self, L, c, fs=(1.0, 0.95, 0.9, 0.85, 0.8, 0.75, 0.7, 0.65, 0.6, 0.55, 0.5, 0.45, 0.4)):
        best = (L * self.Eh(0.0), 0.0, 1e6)
        if c <= 0: return best
        for f in fs:
            c1 = f * c
            eh = L * self.Eh(c1)
            if eh >= best[0]: continue
            for e in range(-16, 200):
                th = 2.0 ** (e / 16)
                if th * c1 > 600: break
                v = self.H(L, c1, th, c)
                if v < best[0]: best = (v, c1, th)
        return best

def dyadic(x, bits=24):
    """a short dyadic rational near float x>0"""
    if x == 0: return Fr(0)
    e = math.floor(math.log2(x)) - bits
    return Fr(round(x / 2.0 ** e)) * Fr(2) ** e

def make_opt(b, t, fl, cthr_scaled, s=None):
    """option for threshold cthr (scaled units) using float optimisation; returns filled Opt (absolute units)"""
    L = 2 ** b
    H, c1s, ths = fl.best(L, cthr_scaled)
    cthr = dyadic(cthr_scaled, 40) * Fr(1, 2 ** 127) if cthr_scaled > 0 else Fr(0)
    c1 = dyadic(c1s, 24) * Fr(1, 2 ** 127) if c1s > 0 else Fr(0)
    th = dyadic(ths, 24) * 2 ** 127
    if s is None:
        u = float(th * c1)
        s = max(0, math.ceil(math.log2(u + 1e-300)) + 12) if u > 0 else 0
    o = Opt(c1, th, s, cthr)
    return fill_opt(b, t, o), H


# ---------------- large-route cover at the weighted baseline ----------------

GRID = 64  # grid points per octave of x for option thresholds

class Builder:
    def __init__(self, b, N, P=100, J=None, n1=None):
        self.b, self.N = b, N
        self.t = make_table(b, N, P=P, J=J, n1=n1)
        assert check_table(b, N, self.t)
        self.fl = FLeaf(self.t)
        self.opts = {}  # key -> Opt
    def opt_for(self, key):
        if key not in self.opts:
            if key is None:
                o = Opt(Fr(0), Fr(2 ** 40) * 2 ** 127, 0, Fr(0))
                self.opts[key] = fill_opt(self.b, self.t, o)
            else:
                xg = 2.0 ** (key / GRID)
                beta = 1 - xg
                o, _ = make_opt(self.b, self.t, self.fl, beta * (1 - 1e-12))
                self.opts[key] = o
        return self.opts[key]
    def key_of(self, qb):
        x = qb / 2.0 ** 128
        if 2 * qb > 2 ** 128: return None
        return math.ceil(math.log2(x) * GRID)
    def best_entry(self, qa, qb):
        """option keys usable at qb: the grid one, and the zero one"""
        for key in (self.key_of(qb), None):
            o = self.opt_for(key)
            if entry_ok(self.b, self.N, o, qa, qb):
                return key
        return False
    def build(self, qstart, maxint=500):
        TOP = 2 ** 127
        qa = qstart
        out = []
        while True:
            if len(out) >= maxint: return None
            if self.best_entry(qa, qa) is False: return None
            k = self.best_entry(qa, TOP)
            if k is not False:
                out.append((qa, TOP, k)); return out
            # geometric search on qb = qa * 2^(i/256)
            def qb_of(i): return min(TOP, int(qa * 2.0 ** (i / 256.0)))
            lo, i = 0, 1
            while qb_of(i) < TOP and self.best_entry(qa, qb_of(i)) is not False:
                lo = i; i *= 2
            hi = i
            while hi - lo > 1:
                mid = (lo + hi) // 2
                if self.best_entry(qa, qb_of(mid)) is not False: lo = mid
                else: hi = mid
            qb = qb_of(lo)
            if lo == 0:
                a, z = qa, qb_of(1)
                while z - a > 1:
                    mm = (a + z) // 2
                    if self.best_entry(qa, mm) is not False: a = mm
                    else: z = mm
                qb = a
            k = self.best_entry(qa, qb)
            if k is False: return None
            out.append((qa, qb, k))
            qa = qb + 1
    def finalize(self, raw):
        keys = []
        for (_, _, k) in raw:
            if k not in keys: keys.append(k)
        opts = [self.opts[k] for k in keys]
        entries = [(qa, qb, keys.index(k)) for (qa, qb, k) in raw]
        return opts, entries

def build_cover(b, N, qstart, P=100, J=None, n1=None):
    B = Builder(b, N, P=P, J=J, n1=n1)
    raw = B.build(qstart)
    if raw is None:
        return None
    opts, entries = B.finalize(raw)
    ok = check_cover(b, N, qstart, B.t, opts, entries)
    return (qstart, B.t, opts, entries) if ok else None


# ---------------- near-cover certificate (BridgeForsNear.checkNear) ----------------

def stir_row(n):
    row = [1]
    for k in range(n):
        new = [0] * (len(row) + 1)
        for j, s in enumerate(row):
            new[j] += j * s          # S(k+1, j) gets j S(k, j)
            new[j + 1] += s          # and S(k, j)
        row = new
    return row  # S(n, j), j = 0..n

S23 = stir_row(23)

def touch(n_row, mu):
    return sum(Fr(s) * mu ** j for j, s in enumerate(n_row))

def mu_once(b, N, qb):
    """Mirror of H0.muOnceQ5: the coin of a future digest pair is (2 - 2^-(26-b)) / (2^128 landing)."""
    return (Fr(N, 2 ** b) + (Fr(qb) * (2 - Fr(1, 2 ** (26 - b))) / 2 ** 128)
            * (1 + Fr(2 ** 27 - 2 ** b, 2 ** 128)) ** 24 / Fr(2) ** b)

def near_hq(b, mu):
    return 24 * Fr(2) ** b * touch(S23, mu) / Fr(2) ** 256

def certificate(b, N, qb, prec=260):
    """(m, c) with checkNear b N qb m c = true."""
    mu = mu_once(b, N, qb)
    m = math.ceil(mu * 2 ** 64)
    h = near_hq(b, Fr(m, 2 ** 64))
    c = Fr(math.ceil(h * 2 ** prec), 2 ** prec)
    return m, c


# ---------------- small route at qh (BridgeArmSmall.checkSmallA) ----------------

def rho_of(qh):
    """The linear-potential rate: max(3/2, 2 - 1/(1 + 4032 x), 1 + 66 x), rounded up to 2^-48."""
    x = Fr(qh, 2 ** 128)
    return rup(max(Fr(3, 2), 2 - 1 / (1 + 4032 * x), 1 + 66 * x), 48)

def check_smallA(b, N, qh, rho, cthr, B, c):
    """Mirror of checkSmallA (called with the halved near bound c = near / 2)."""
    x = Fr(qh, 2 ** 128); mr = Fr(N, 2 ** b * 2 ** 10)
    ok = (Fr(3, 2) <= rho <= 2 and 1 + 4032 * (2 - rho) * x <= rho and 1 + 66 * x <= rho and 64 * x <= 1
          and qh <= 2 ** 127 and N <= 2 ** 70 and cthr <= rho / 2 ** 128 and B >= 0 and c >= 0
          and mr <= rho - 1 - x)
    lhs = (rho + 2 ** 128 * B + Fr(qh) * (2 - Fr(1, 2 ** (26 - b))) / 2 ** 129 + (2 - rho + x + mr) * qh * c
           + Fr(1, 2 ** 60))
    return ok and lhs <= 2

# ---------------- parameter sets ----------------

# (b, N, lx): subtree height, proved signature limit, and qh = floor(2^(128 + lx)) where the
# small-budget route hands over to the large-budget route.
FINAL = [(8, 7530, -6.96875), (10, 28600, -7.15625), (12, 108700, -7.375), (13, 211900, -7.5),
         (14, 412500, -7.75), (20, 22380000, -8.78125), (26, 1156000000, -11.0)]

def certify(b, N, lx):
    qh = int(2.0 ** (128 + lx))
    cov = build_cover(b, N, qh)
    assert cov is not None, ('large route fails', b, N)
    _, t, opts, entries = cov
    fl = FLeaf(t)
    rho = rho_of(qh)
    o, _ = make_opt(b, t, fl, float(rho / 2) * (1 - 1e-9))
    assert check_opt(b, t, o)
    m, c = certificate(b, N, qh)
    assert check_smallA(b, N, qh, rho, o.cthr, o.B, c / 2), ('small route fails', b, N)
    return qh, t, opts, entries, rho, o, m, c

# ---------------- Lean output ----------------
def q(fr):
    n, d = fr
    if d == 1: return '%d' % n
    return '%d / %d' % (n, d)

def cover_lean(name, cj):
    """A `CoverS` definition from a JSON-like dict (table, options, entries)."""
    t = cj['table']
    lines = []
    lines.append('/-- Split-bound certificate for subtree height %d and %d signatures, budgets from %d. -/' % (cj['b'], cj['N'], cj['qstart']))
    lines.append('def %s : CoverS where' % name)
    lines.append('  tab := ⟨%d, %d, %d,' % (t['m'], t['P'], t['J']))
    pm = t['pm']
    chunks = [', '.join(str(x) for x in pm[i:i + 4]) for i in range(0, len(pm), 4)]
    lines.append('    [' + (',\n      ').join(chunks) + '],')
    lines.append('    %s⟩' % q(t['T']))
    lines.append('  opts := [')
    os_ = []
    for o in cj['opts']:
        c1, th, s, cthr, eC, Eh, Ee, B = o
        os_.append('    ⟨%s, %s, %d,\n      %s,\n      %s,\n      %s,\n      %s,\n      %s⟩' % (q(c1), q(th), s, q(cthr), q(eC), q(Eh), q(Ee), q(B)))
    lines.append(',\n'.join(os_) + ']')
    lines.append('  entries := [')
    lines.append(',\n'.join('    (%d, %d, %d)' % tuple(e) for e in cj['entries']) + ']')
    return '\n'.join(lines)


def fr(x): return [x.numerator, x.denominator]

def to_dict(b, N, qh, t, opts, entries):
    return {'b': b, 'N': N, 'qstart': qh, 'table': t.to_json(),
            'opts': [[fr(o.c1), fr(o.th), o.s, fr(o.cthr), fr(o.eC), fr(o.Eh), fr(o.Ee), fr(o.B)] for o in opts],
            'entries': entries}

HEADER = """import LeanSphincs.BridgeDetClose

/-! Certificates for the proved lifetimes (generated by `scripts/lifetime_certificates.py`, checked by
the kernel with `decide +kernel`, exact rational arithmetic, no `native_decide`). For each parameter
set: the split cover at the weighted baseline of every budget from `qh ≈ 2^(128 + lx)` to `2^127`,
and at `qh` the small-route threshold option, the near certificate and `checkSmallA`. -/

open ENNReal

namespace LeanSphincs.Security.H0

open Concrete Domination ForsPrice"""

def block(b, N, lx, qh, t, opts, entries, rho, o, m, c):
    name = 'cover_b%d' % b
    out = [cover_lean(name, to_dict(b, N, qh, t, opts, entries))]
    out.append("""set_option maxRecDepth 100000 in
theorem %s_ok : checkCoverSW %d %d %d %s = true := by decide +kernel

/-- **One-coin H-term bound at the weighted baseline** for subtree height %d and %d signatures,
budgets `q' ≥ 2^(128 %s)`. -/
theorem h0_bound_b%d [Params] (hb : subtreeHeight = %d) (hN : signatureLimit = %d) (q' : ℕ)
    (hq0 : %d ≤ q') (hq : 2 * q' ≤ 2 ^ 128) :
    (1 - HiddenDebt.budget 0 q') + (q' : ℝ≥0∞) * hOfOW q' +
        ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) : ℕ) : ℝ≥0∞) / 2 ^ 127 :=
  h0SW_bound_of_cover %d %d %d %s %s_ok hb hN q' hq0 hq""" % (name, b, N, qh, name, b, N, '%+g' % lx, b, b, N, qh,
                                                              b, N, qh, name, name))
    c1, th, s, cthr, eC, Eh, Ee, B = [o.c1, o.th, o.s, o.cthr, o.eC, o.Eh, o.Ee, o.B]
    Q = lambda x: q(fr(x))
    out.append("""/-- Small-route threshold option for subtree height %d: baseline `ρ / 2^128` at `qh = %d`. -/
def opt_b%d : OptS := ⟨%s, %s, %d,
  %s,
  %s,
  %s,
  %s,
  %s⟩

/-- `ρ` for subtree height %d. -/
def rho_b%d : ℚ := %s

/-- The near H-term bound for subtree height %d. -/
def near_b%d : ℚ := %s

set_option maxRecDepth 100000 in
theorem opt_b%d_ok : checkThreshS %d %d %s.tab opt_b%d = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem near_b%d_ok : checkNear %d %d %d %d near_b%d = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem small_b%d_ok : ForsPotential.checkSmallA %d %d %d rho_b%d opt_b%d.cthr opt_b%d.B (near_b%d / 2) = true := by
  decide +kernel""" % (b, qh, b, Q(c1), Q(th), s, Q(cthr), Q(eC), Q(Eh), Q(Ee), Q(B), b, b, Q(rho), b, b, Q(c),
                       b, b, N, name, b, b, b, N, qh, m, b, b, b, N, qh, b, b, b, b))
    return out

def main():
    import os
    here = os.path.dirname(os.path.abspath(__file__))
    target = os.path.join(here, '..', 'LeanSphincs', 'LifetimeCertificates.lean')
    parts = [HEADER]
    for b, N, lx in FINAL:
        qh, t, opts, entries, rho, o, m, c = certify(b, N, lx)
        parts += block(b, N, lx, qh, t, opts, entries, rho, o, m, c)
        print('b=%2d N=%d qh=2^%.3f: %d cover entries' % (b, N, 128 + lx, len(entries)), flush=True)
    parts.append('end LeanSphincs.Security.H0\n')
    open(target, 'w').write('\n\n'.join(parts))
    print('wrote', os.path.normpath(target))

if __name__ == '__main__':
    main()
