#!/usr/bin/env python3
"""The own-leaf near forecast of the SW route: the light cap, the cell counts and the contact coefficient.

A FORS leaf query at a cell c = (I, kappa, L) costs nu = 2^-128 times the chance that a cached or future pair
at I becomes near covered with c as its only missing leaf. With every index capped at n* disclosures (the
light event) this forecast splits into
  * the fresh part  G_fresh = q 2^-(b+a) (n*/A)^(k-1)                               (gFreshQ, A = 2^a),
  * the cached part sum_{p at c, m_p >= 1} rho^(m_p),  rho = (n* - D)/A, D = #disclosures at I,
    bounded by G_cached = m except on a bad event (a cell whose cached part exceeds m),
plus two failure terms, each an absolute probability x * (term) with x = q / 2^128:
  * light failure: 2^b E[(Pois(mu) - n*)^+] <= 2^b lightTail(t, n*)        (ForecastLight.lean, startLight_le),
  * cell counts:   sum_{D <= n*} cells (mu^D / D!) e^{-theta_D m} Gamma_D^q <= eps   (ForecastCert.lean),
    Gamma_D = 1 + 2^-(b+a) sum_{1 <= j < k} C(k-1, j) (D/A)^(k-1-j) (e^{theta_D rho_D^j} - 1),
    cells = 2^b k A (the pattern bound and the pair factor: ForecastCells.lean).
The contact coefficient of a FORS leaf query is cU = N / 2^(b+a) + G_fresh + G_cached.

API (every exact function mirrors the Lean definition of the same name; floats only choose theta_D, m):
    lightTail(t, nstar)                       (ForecastLight.lean)
    gFreshQ(b, k, a, q, nstar)                (ForecastCert.lean)
    excessUp(u, s, P), lamQ(...), cellTerm(...), cellSum(...), checkCellCert(b, k, a, mu, q, cc, eps)
    make_cellCert(b, k, a, mu, q, nstar, eps) ->  CellCert (float search of m and theta_D, then exact check)
    forecast_constants(b, k, a, N, t, q, nstar, eps)  ->  dict of the constants for one budget

    python3 scripts/fors_sw_forecast.py       # 19x9 at N = 2^24: the constants on x in [2^-10, 2^-5]
"""
from fractions import Fraction as Fr
import math, os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fors_certificates as fc


# ---------------- the light failure (ForecastLight.lean) ----------------

def lightTail(t, nstar):
    """lightTail t n*: the Poisson mean of (n - n*)^+ from a checked table (head up to n1, geometric tail)."""
    head = sum((t.pb(n) * max(n - nstar, 0) for n in range(t.n1 + 1)), Fr(0))
    return head + t.pb(t.n1 + 1) * (Fr(max(t.n1 - nstar, 0)) / (1 - t.r) + Fr(1) / (1 - t.r) ** 2)


# ---------------- closed forms (ForecastTail.lean) ----------------

def chooseQ(n, j):
    """chooseK n j: n! / (j! (n - j)!) (0 for j > n, as Nat subtraction truncates: n!/(j! 0!) is not 0;
    the Lean definition is only used with j <= n)."""
    return Fr(math.factorial(n), math.factorial(j) * math.factorial(max(n - j, 0)))


def touchardList(mu, r):
    """touchardGo mu r 0 [1]: T_0 .. T_r at mu (T_{n+1} = mu sum_{i<=n} C(n, i) T_i)."""
    L = [Fr(1)]
    for n in range(r):
        L.append(mu * sum((chooseQ(n, i) * L[i] for i in range(n + 1)), Fr(0)))
    return L


def touchard(mu, r):
    return touchardList(mu, r)[r]


def phiQ(a, mu, r):
    """phiK a mu r = T_r(mu) / 2^(a r): the per-pair weight at r missing trees."""
    return touchard(mu, r) / 2 ** (a * r)


def freshQ(b, k, a, mu, q, D):
    """freshK b k a mu q D = q 2^-(b+a) sum_{i<k} C(k-1, i) D^(k-1-i) T_i(mu) / 2^(a(k-1))."""
    T = touchardList(mu, k - 1)
    tot = sum((chooseQ(k - 1, i) * Fr(D) ** (k - 1 - i) * T[i] for i in range(k)), Fr(0))
    return Fr(q, 2 ** (b + a)) * (tot / 2 ** (a * (k - 1)))


COIN_SLACK = Fr(1, 2 ** 10)
FAIL_FLOOR = Fr(1, 2 ** 99)


# ---------------- the tail certificate (ForecastCert.lean) ----------------

def excessUp(u, s, P):
    """excessUp u s P >= e^u - 1 for 0 <= u < 2^s: u/(1-u) below 1/2, expUp(u) - 1 above."""
    if u < Fr(1, 2):
        return u / (1 - u)
    return fc.expUp(u, s, P) - 1


class TailCert:
    """TailCert: the cap n0, theta_D for D < n0, and the precision of the exponential bounds."""
    def __init__(self, n0, th, s=40, P=64, J=600):
        self.n0, self.th, self.s, self.P, self.J = n0, th, s, P, J


def getD(lst, n):
    return lst[n] if 0 <= n < len(lst) else Fr(0)


def lam1Q(b, k, a, mu, D, th, s, P):
    """lam1Q: 2^-(b+a) sum_{1<=j<k} C(k-1, j) (D/2^a)^(k-1-j) excessUp(th phi(j)) >= Gamma_D - 1."""
    tot = Fr(0)
    for j in range(k):
        if 1 <= j:
            tot += chooseQ(k - 1, j) * Fr(D, 2 ** a) ** (k - 1 - j) * excessUp(th * phiQ(a, mu, j), s, P)
    return tot / 2 ** (b + a)


def vQ(b, k, a, mu, q, m, c, D):
    """the Chernoff exponent of D: theta_D (m - fresh_D - 2^-10) - q lam1Q_D (checked >= 0)."""
    th = getD(c.th, D)
    return th * (m - freshQ(b, k, a, mu, q, D) - COIN_SLACK) - q * lam1Q(b, k, a, mu, D, th, c.s, c.P)


def termQ(b, k, a, mu, q, m, c, D):
    """k 2^a 2^b (mu^D / D!) / expLow(v_D)."""
    return Fr(k * 2 ** a * 2 ** b) * (mu ** D / math.factorial(D)) / fc.expLow(vQ(b, k, a, mu, q, m, c, D), c.J, c.P)


def tailQ(b, k, a, t, q, m, c):
    """2^b lightTail(t, n0 - 1) + sum_{D<n0} termQ + 2^-99 (the tail sum, before the excess factor)."""
    return 2 ** b * lightTail(t, c.n0 - 1) + \
        sum((termQ(b, k, a, t.mu, q, m, c, D) for D in range(c.n0)), Fr(0)) + FAIL_FLOOR


def checkTail(b, k, a, t, q, m, c, Pb):
    """checkTail: the side conditions and max(0, 1 - m) tailQ <= Pb (mirrors the Lean Bool, exactly)."""
    if not (1 <= c.n0 and len(c.th) == c.n0 and 1 <= t.n1): return False
    for D in range(c.n0):
        th = getD(c.th, D)
        if th < 0: return False
        if not all(th * phiQ(a, t.mu, j) < 2 ** c.s for j in range(k)): return False
        if vQ(b, k, a, t.mu, q, m, c, D) < 0: return False
    return max(Fr(0), 1 - m) * tailQ(b, k, a, t, q, m, c) <= Pb


# ---------------- the float search ----------------

class _F:
    """float tables for one (b, k, a, mu, q)."""
    def __init__(self, b, k, a, mu, q):
        self.b, self.k, self.a, self.mu, self.q = b, k, a, float(mu), q
        T = [float(v) for v in touchardList(Fr(mu), k - 1)]
        self.phi = [T[r] / 2 ** (a * r) for r in range(k)]
        A = 2 ** a
        self.fresh = [q / 2 ** (b + a) * sum(math.comb(k - 1, i) * D ** (k - 1 - i) * T[i] for i in range(k)) / A ** (k - 1)
                      for D in range(200)]

    def lam(self, D, th):
        A = 2 ** self.a
        tot = 0.0
        for j in range(1, self.k):
            u = th * self.phi[j]
            if u > 700: return math.inf
            tot += math.comb(self.k - 1, j) * (D / A) ** (self.k - 1 - j) * math.expm1(u)
        return self.q / 2 ** (self.b + self.a) * tot

    def logterm(self, D, th, m):
        cells = self.k * 2 ** self.a * 2 ** self.b
        return math.log(cells) + D * math.log(self.mu) - math.lgamma(D + 1) - \
            th * (m - self.fresh[D] - 2 ** -10) + self.lam(D, th)

    def best(self, D, m):
        """theta >= 0 minimizing the D-term (theta = 0 gives the term cells mu^D / D!)."""
        f = lambda lt: self.logterm(D, math.exp(lt), m)
        lo, hi = math.log(1e-3), math.log(1e7)
        g = (math.sqrt(5) - 1) / 2
        x1, x2 = hi - g * (hi - lo), lo + g * (hi - lo)
        f1, f2 = f(x1), f(x2)
        for _ in range(120):
            if f1 < f2:
                hi, x2, f2 = x2, x1, f1
                x1 = hi - g * (hi - lo); f1 = f(x1)
            else:
                lo, x1, f1 = x1, x2, f2
                x2 = lo + g * (hi - lo); f2 = f(x2)
        lt = (lo + hi) / 2
        v = f(lt)
        v0 = self.logterm(D, 0.0, m)
        return (math.exp(lt), v) if v < v0 else (0.0, v0)


def make_tailCert(b, k, a, t, q, m, nmax=40, s=40, P=64, J=600):
    """the certificate (n0, theta_D) minimizing the float tail, then the exact tail and Pb = its rounding up."""
    F = _F(b, k, a, t.mu, q)
    mf = float(m)
    best = None
    lt_cache = {}
    for n0 in range(1, nmax):
        light = 2 ** b * sum(math.exp(-F.mu + n * math.log(F.mu) - math.lgamma(n + 1)) * (n - n0 + 1)
                             for n in range(n0, n0 + 60))
        terms, ths = 0.0, []
        for D in range(n0):
            if D not in lt_cache: lt_cache[D] = F.best(D, mf)
            th, lv = lt_cache[D]
            terms += math.exp(lv) if lv < 700 else math.inf
            ths.append(th)
        tot = light + terms
        if best is None or tot < best[0]: best = (tot, n0, ths)
    _, n0, ths = best
    th = [fc.rdown(Fr(x), 20) for x in ths]
    c = TailCert(n0, th, s, P, J)
    # vQ >= 0 may fail after rounding for a D whose optimum is near theta = 0: use theta = 0 there
    for D in range(n0):
        if vQ(b, k, a, t.mu, q, m, c, D) < 0:
            c.th[D] = Fr(0)
    tail = max(Fr(0), 1 - m) * tailQ(b, k, a, t, q, m, c)
    e = math.floor(math.log2(float(tail))) - 40
    Pb = Fr(math.ceil(tail * 2 ** -e) if e < 0 else -(-tail.numerator // (tail.denominator * 2 ** e))) * Fr(2) ** e
    assert checkTail(b, k, a, t, q, m, c, Pb), "the exact check failed"
    return c, Pb


# ---------------- Lean emission ----------------

def lean_tailCert(c):
    """the Lean term of a TailCert (SWRoute/ForecastCert.lean)."""
    return '⟨%d, [%s], %d, %d, %d⟩' % (c.n0, ', '.join(fc.q(x) for x in c.th), c.s, c.P, c.J)


def lean_tail_test(b, k, a, t, q, m, c, Pb, H=24, N=2 ** 24, qtop=2 ** 124):
    """a kernel test file: the table, the rate and the tail check (decide +kernel)."""
    return '\n'.join([
        'import FORS.Certificates.Build',
        'import FORS.SWRoute.ForecastCert',
        'namespace FORS.Security.H0',
        'set_option maxRecDepth 1000000',
        'set_option maxHeartbeats 0',
        'def tabT : PoisT := %s' % fc.lean_tab(t),
        'theorem tabT_ok : checkPT tabT = true := checkPT_poisOf (by decide +kernel)',
        'theorem rateT_ok : checkRate %d %d %d %d tabT = true := by decide +kernel' % (H, b, N, qtop),
        'theorem tailT_ok : SWRoute.checkTail %d %d %d tabT %d (%s) %s (%s) = true := by decide +kernel'
        % (b, k, a, q, fc.q(m), lean_tailCert(c), fc.q(Pb)),
        'end FORS.Security.H0', ''])


# ---------------- the numbers ----------------

def main():
    H, k, a, N = 24, 19, 9, 2 ** 24
    fc.set_config(H, 'layered', k=k, a=a)
    b = H
    qtop = 2 ** 124
    t = fc.make_poisT(b, N, qtop)
    assert fc.checkPT(t) and fc.checkRate(b, N, qtop, t)
    print(f"19x9, h = b = {b}, N = 2^24, mu = {float(t.mu):.12f} (table at qtop = 2^124)")
    print(" lx_b      m        n0   log2 Pb (excess form)")
    rows = [(-12.9375, 0.4978), (-12.0, 0.4975), (-11.0, 0.6597), (-10.0, 0.7922), (-9.0, 0.8782),
            (-8.5, 0.9053), (-8.0, 0.9235), (-7.0, 0.937), (-6.5, 0.9332), (-6.0625, 0.9237), (-6.0, 0.9219)]
    for lx, mf in rows:
        q = int(2 ** (128 + lx))
        m = fc.rdown(Fr(mf), 40)
        c, Pb = make_tailCert(b, k, a, t, q, m)
        print(f" {lx:8.4f}  {mf:.4f}   {c.n0:3d}   {math.log2(float(Pb)):8.2f}")


if __name__ == '__main__':
    main()
