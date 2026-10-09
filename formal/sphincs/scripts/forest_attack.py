#!/usr/bin/env python3
"""Attack lifetimes of the forest (FOREST.md), floats and Monte Carlo; needs numpy and scipy.

Usage (from formal/sphincs):
    python3 scripts/forest_attack.py            # the table of scripts/forest_table.py
    python3 scripts/forest_attack.py lex        # the 246 codewords in lexicographic order, then the first 10

Cover model: the largest N with E[Y] <= 1, Y the cover rate of a digest query in units 2^-127 (Poisson
loads of the 2^b instances). Best known attack: the largest N with E[max(Y, r)] <= 1, where Y is the
cover rate of the realized key (random loads, leaves, WOTS keys and codewords) and r the rate of the
other searches in the same units: 1/2 for plain searches, RATE_WOTS for the WOTS+C unit-neighbour
route. RATE_WOTS is the value that reproduces the figures first computed for the lexicographic table
(100.0 / 99.4 / 95.7 / 95.3 / 94.4 / 92.5 / 91.8% of the cover lifetimes) to 0.3 points, 0.9 at b = 8.
The Monte Carlo noise is about 0.3% of N.
"""
import warnings; warnings.filterwarnings('ignore')
import itertools, math, os, sys
import numpy as np
from scipy.stats import binom, poisson
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import forest_table as ft

UMAX = 48; NMAX = 220; NMIN, NMX = 1, 125
BS = [26, 20, 14, 13, 12, 10, 8]
RATE_WOTS = 0.96875

def f_of_counts(cnt, U=UMAX):
    """cnt: array shape (W,)*D of multiplicities. f[u] = P(codeword <= max of u iid table entries)."""
    n = cnt.sum()
    K = cnt.astype(np.float64)/n
    D = cnt.ndim
    for ax in range(D): K = np.cumsum(K, axis=ax)
    DK = K.copy()
    for ax in range(D):
        sl_lo = [slice(None)]*D; sl_hi = [slice(None)]*D
        sl_lo[ax] = slice(0,-1); sl_hi[ax] = slice(1,None)
        DK[tuple(sl_lo)] -= DK[tuple(sl_hi)]
    K = K.ravel(); DK = DK.ravel()
    f = np.empty(U+1); p = np.ones_like(K)
    for u in range(U+1):
        f[u] = (p*DK).sum(); p *= K
    return np.clip(f, 0, 1)

def tree_P(f, a, s, c):
    """P[n] = prob one tree component is covered given n signatures on the instance."""
    U = len(f)-1
    i = np.arange(U+1)
    if c == 0: mu = f.copy()
    else:
        B = binom.pmf(i[None,:], i[:,None], 2.0**-c)   # B[i,u]
        mu = B @ f
    ms = mu**s
    n = np.arange(NMAX+1)
    B2 = binom.pmf(i[None,:], n[:,None], 2.0**-a)
    P = B2 @ ms + binom.sf(U, n, 2.0**-a)       # beyond U: count as covered
    return np.minimum(P, 1)

def log2_forge(P, T, lam, b):
    n = np.arange(NMAX+1)
    return (b-26) + math.log2((poisson.pmf(n, lam) * P**T).sum() + poisson.sf(NMAX, lam) + 1e-300)

def lifetime(P, T, b, level=127):
    lo, hi = 1e-3, 150.0
    for _ in range(60):
        mid = (lo+hi)/2
        if log2_forge(P, T, mid, b) <= -level: lo = mid
        else: hi = mid
    return lo * 2**b


def tables(name):
    lex=sorted(w for w in itertools.product(range(5),repeat=6) if sum(w)==5)
    if name=='lex': return lex+lex[:10]
    if name=='rule': return ft.table()
def pools(name,S=40000,chunk=4000,seed=5):
    rng=np.random.default_rng(seed)
    TAB=np.array(tables(name),dtype=np.int8)
    cnt=np.zeros((5,)*6,dtype=np.int64)
    for w in TAB: cnt[tuple(w)]+=1
    K=cnt.astype(np.float64)
    for ax in range(6): K=np.cumsum(K,axis=ax)
    Kf=K.ravel()/256.0; pw=5**np.arange(5,-1,-1)
    res={}
    for n in range(NMIN,NMX+1):
        out=[]
        for _ in range(S//chunk):
            M=np.full((chunk,256,6),-1,dtype=np.int8)
            rows=np.repeat(np.arange(chunk),n)
            leaf=rng.integers(16,size=(chunk,n))
            for j in (0,1):
                g=(leaf*16+j*8+rng.integers(8,size=(chunk,n))).ravel()
                d=TAB[rng.integers(256,size=chunk*n)]
                np.maximum.at(M,(rows,g),d)
            opened=M[:,:,0]>=0
            idx=(np.where(opened[:,:,None],M,0).astype(np.int64)*pw).sum(axis=2)
            kv=np.where(opened,Kf[idx],0.0).reshape(chunk,16,2,8).mean(axis=3)
            out.append(kv.prod(axis=2).mean(axis=1))
        res[n]=np.concatenate(out)
    return res
def prepare(name,Q=20000,seed=9):
    pl=pools(name); rng=np.random.default_rng(seed)
    TAB=tables(name); cnt=np.zeros((5,)*6,dtype=np.int64)
    for w in TAB: cnt[tuple(w)]+=1
    P=tree_P(f_of_counts(cnt),4,2,3)
    ys={}
    for n,phi in pl.items():
        p=phi/phi.sum()
        ys[n]=2.0**101*np.prod(phi[rng.choice(len(phi),size=(Q,8),p=p)],axis=1)   # size-biased y given n
    return P,ys,{n:(phi.mean()/P[n]) for n,phi in pl.items()}
def crit(P,ys,b,N,rs,M=20000,y0=1e-3,seed=3):
    rng=np.random.default_rng(seed)
    L=2.0**b; n=np.arange(NMAX+1); pn=poisson.pmf(n,N/L); m1=2.0**101*P**8
    bulk=0.0; rates=[]; vals=[]
    for k in range(NMAX+1):
        mass=L*pn[k]*m1[k]
        if k not in ys: bulk+=mass; continue      # outside the pools: counted as bulk (tiny)
        y=ys[k]; w=mass/len(y); big=y>=y0
        bulk+=w*(~big).sum(); rates.append(w/y[big]); vals.append(y[big])
    rates=np.concatenate(rates); vals=np.concatenate(vals); R=rates.sum()
    k=rng.poisson(R,size=M); tot=k.sum()
    draws=rng.choice(len(vals),size=tot,p=rates/R)
    Y=np.full(M,bulk); np.add.at(Y,np.repeat(np.arange(M),k),vals[draws])
    return {r:np.maximum(Y,r).mean() for r in rs}, Y.mean(), bulk
def life(P,ys,b,r,N0):
    lo,hi=N0*0.6,N0*1.03
    for _ in range(20):
        mid=(lo+hi)/2
        if crit(P,ys,b,mid,(r,))[0][r]<=1: lo=mid
        else: hi=mid
    return lo
if __name__=='__main__':
    name=sys.argv[1] if len(sys.argv)>1 else 'rule'
    P,ys,chk=prepare(name)
    print('pool mean / exact:',' '.join('%d:%.3f'%(n,chk[n]) for n in (10,20,40,80,120)))
    cov=[lifetime(P,8,b) for b in BS]
    print('cover model     ',' '.join('%.5e'%x for x in cov))
    for label,r in (('plain searches ',0.5),('with WOTS route',RATE_WOTS)):
        Ls=[life(P,ys,b,r,cov[i]) for i,b in enumerate(BS)]
        print(label,' ',' '.join('%.3e'%x for x in Ls),' | % of cover:',' '.join('%.1f'%(100*x/c) for x,c in zip(Ls,cov)),flush=True)
