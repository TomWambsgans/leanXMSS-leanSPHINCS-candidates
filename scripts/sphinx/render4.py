"""The sphinx of the website (site/sphinx.png and the stone data `D` in site/index.html). Needs numpy and scipy.

    python3 render4.py 1900          # writes sphinx.png (alpha = darkness) and stones.json in the current directory
    python3 render4.py 1000 head     # a close-up of the head, to work on the model

model4.py is the 3D model (a signed distance function, ray-marched); model3d.py holds its primitives. sphinx.png is
used as a CSS mask; stones.json (image size, outline, and for each stone of the path tree: parent, depth, polygon)
is the object `D` of the last script of site/index.html."""
import sys, json, math, numpy as np
from scipy.spatial import ConvexHull
import model4 as M, png
Wp = int(sys.argv[1]) if len(sys.argv) > 1 else 900
mode = sys.argv[2] if len(sys.argv) > 2 else 'full'
CAMS = {'full': dict(eye=(107, -76, 1.3), at=(35.5, 0, 9.3), fov=26.0, t0=45.0),
        'head': dict(eye=(98, -52, 12), at=(56.5, 0, 17.5), fov=13.0, t0=30.0)}
CAM = CAMS[mode]; Hp = int(Wp * (0.52 if mode == 'full' else 0.7))
hit, P, N, t, eye, dirs = M.march(Wp, Hp, **CAM)
N = np.nan_to_num(N)
x, y, z = P[..., 0], P[..., 1], P[..., 2]
foot = t * (2 * math.tan(math.radians(CAM['fov']) / 2) / Hp)
hash3 = M.hash3
mat, k, bx, by, zw, xw, yw, Hc, Lc = M.blocks(P)
def joint(v, size, na, lw=1.2):
    r = v - np.floor(v / size) * size
    d = np.minimum(r, size - r)
    s = np.sqrt(np.clip(1 - na * na, 0, 1))
    return np.where(s > 0.5, np.clip(lw - d / (foot * np.maximum(s, 1e-3)), 0, 1), 0)
jz = joint(zw, Hc, N[..., 2]); jv = np.maximum(joint(xw, Lc, N[..., 0]), joint(yw, Lc, N[..., 1]))
there = hash3(bx + 5, by - 3, k + 11)
face = (mat == 2) & (x > 58.6)
joints = np.choose(mat, [np.maximum(0.45 * jz, 0.5 * jv * (there > 0.35)),          # bedrock: beds, a few fissures
                         np.maximum(0.62 * jz, 0.62 * jv * np.where(there > 0.08, 1, 0.3)),   # masonry
                         np.maximum(0.34 * jz, 0.30 * jv * (there > 0.25)),                   # head
                         np.maximum(0.62 * jz, 0.62 * jv)])                                   # podium
joints = joints * np.where(face, 0.45, 1.0)
# light, shadow, occlusion
Lg = np.array([0.72, -0.42, 0.55]); Lg /= np.linalg.norm(Lg)
lam = np.clip(N @ Lg, 0, 1)
sh = np.ones_like(t); sh[hit] = M.shadow(P[hit] + N[hit] * 0.06, Lg)
ao = np.zeros_like(t); ao[hit] = np.clip(M.sdf(P[hit] + N[hit] * 1.4) / 1.4, 0, 1) * 0.6 + np.clip(M.sdf(P[hit] + N[hit] * 0.35) / 0.35, 0, 1) * 0.4
lit = lam * (0.25 + 0.75 * sh)
tone = hash3(bx, by, k)
lam_fine = 0.5 + 0.5 * np.sin(13.0 * zw + 1.5 * np.sin(0.3 * x + 0.2 * y))                    # fine bedding of the rock
dark = 0.05 + 0.40 * (1 - lit) ** 1.25 + 0.28 * (1 - ao) + np.where((mat == 1) | (mat == 3), 0.10, 0.05) * (tone - 0.5)
dark = dark + np.where((mat == 1) | (mat == 3), 0.0, 0.07) * (lam_fine > 0.8)
stain = np.clip(0.5 + 0.5 * np.sin(0.23 * x + 1.3 * np.sin(0.31 * z + 0.2 * y)) * np.sin(0.45 * z + 0.9 * np.sin(0.17 * x)), 0, 1)
dark = np.clip(dark + 0.09 * stain ** 2, 0, 1) * hit
dark = np.maximum(dark, joints * hit)
# cracks
crack = np.zeros_like(t)
for c0, zlo, zhi in ((12.5, 3, 12.6), (27.0, 4, 12.6), (36.5, 2, 12), (46.0, 4, 13), (54.4, 14.5, 23)):
    cx = x - c0 - 0.7 * np.sin(0.9 * z + c0) - 0.35 * np.sin(2.3 * z + 0.7 * y)
    s = np.sqrt(np.clip(1 - N[..., 0] ** 2, 0, 1))
    crack = np.maximum(crack, np.where((z > zlo) & (z < zhi) & (s > 0.4), np.clip(1.4 - np.abs(cx) / (foot * s + 1e-9), 0, 1), 0))
dark = np.maximum(dark, crack * 0.7 * hit)
# outline: depth discontinuities
td = np.where(hit, t, 500.0)
g = np.maximum(np.abs(td - np.roll(td, 1, 1)), np.abs(td - np.roll(td, 1, 0)))
cosv = np.clip(np.abs((N * dirs).sum(-1)), 0.04, 1)
edge = np.clip(g / (foot / cosv * 5 + foot * 6) - 0.6, 0, 1)
edge[0, :] = 0; edge[:, 0] = 0
dark = np.maximum(dark, edge * 0.75)
# the podium rises from the page's horizontal line: everything below the row of a point low on its near corner is cut
def project(pt):
    e = np.array(CAM['eye'], float); f = np.array(CAM['at'], float) - e; f /= np.linalg.norm(f)
    rgt = np.cross(f, (0, 0, 1)); rgt /= np.linalg.norm(rgt); up = np.cross(rgt, f)
    v = np.array(pt, float) - e; dep = v @ f; tn = math.tan(math.radians(CAM['fov']) / 2)
    return ((v @ rgt) / dep / (tn * Wp / Hp) + 1) / 2 * Wp, (1 - (v @ up) / dep / tn) / 2 * Hp
cut = int(project((81.0, -20.0, -3.5))[1]) if mode == 'full' else Hp
assert cut < Hp - 2, (cut, Hp)
dark[cut:] = 0; hit = hit & (np.arange(Hp)[:, None] < cut)
ys, xs = np.nonzero(dark > 0.03)
x0, x1, y0, y1 = max(xs.min() - 6, 0), min(xs.max() + 7, Wp), max(ys.min() - 6, 0), min(ys.max() + 1, Hp)
ramp = np.clip(np.minimum(np.arange(Wp) - x0, x1 - 1 - np.arange(Wp)) / (0.07 * (x1 - x0)), 0, 1) ** 1.5      # the podium fades out along the line
dark = dark * ramp[None, :]
alpha = (np.clip(dark, 0, 1) * 255).astype(np.uint8)[y0:y1, x0:x1]
png.save('sphinx.png', np.dstack([np.zeros_like(alpha), alpha]))
png.save('sphinx_preview.png', 255 - alpha)
print('image', alpha.shape)
if mode != 'full': sys.exit()

lab = np.where(hit, (mat.astype(np.int64) << 44) | ((k & 0xfff) << 30) | ((bx & 0x7fff) << 15) | (by & 0x7fff), -1)
ids, inv, cnt = np.unique(lab, return_inverse=True, return_counts=True)
inv = inv.reshape(lab.shape)
minarea = max(10, (Wp / 900) ** 2 * 9)
order = np.argsort(inv, axis=None); flat = inv.ravel()[order]
starts = np.searchsorted(flat, np.arange(len(ids))); ends = np.searchsorted(flat, np.arange(len(ids)), 'right')
adj = {}
def add_pairs(a, b):
    m = (a != b); pa, pb = a[m], b[m]
    key = np.minimum(pa, pb) * len(ids) + np.maximum(pa, pb)
    u, c = np.unique(key, return_counts=True)
    for kk, cc in zip(u, c):
        if cc >= max(3, Wp / 450):
            i, j = divmod(int(kk), len(ids)); adj.setdefault(i, set()).add(j); adj.setdefault(j, set()).add(i)
add_pairs(inv[:, 1:].ravel(), inv[:, :-1].ravel()); add_pairs(inv[1:].ravel(), inv[:-1].ravel())
good = [i for i in range(len(ids)) if ids[i] >= 0 and cnt[i] >= minarea]
gset = set(good)
def pix(i):
    o = order[starts[i]:ends[i]]; return o // Wp, o % Wp
zc = {}; xc = {}
for i in good:
    yy, xx = pix(i); zc[i] = float(z[yy, xx].mean()); xc[i] = float(x[yy, xx].mean())
root = max((i for i in good if xc[i] > 50), key=lambda i: zc[i])
dist = {root: 0}; q = [root]
while q:
    nq = []
    for a in q:
        for b in adj.get(a, ()):
            if b in gset and b not in dist: dist[b] = dist[a] + 1; nq.append(b)
    q = nq
rng = np.random.default_rng(11)
rowmax = {i: int(pix(i)[0].max()) for i in good}
leaves = [i for i in good if i in dist and ((ids[i] >> 44) & 3) == 3 and rowmax[i] >= cut - 2]
rng.shuffle(leaves); leaves = leaves[:70]
parent = {}
def climb(a):
    while a != root and a not in parent:
        ups = [b for b in adj[a] if b in dist and dist[b] == dist[a] - 1]
        ups.sort(key=lambda b: -zc[b]); b = ups[int(rng.integers(0, min(2, len(ups))))]
        parent[a] = b; a = b
for l in leaves: climb(l)
nodes = [root] + [a for a in parent]
index = {a: n for n, a in enumerate(nodes)}
def polygon(i):
    yy, xx = pix(i)
    pts = np.concatenate([np.stack([xx + dx, yy + dy], 1) for dx in (0, 1) for dy in (0, 1)]).astype(float)
    hull = list(map(tuple, pts[ConvexHull(pts).vertices]))
    def area(a, b, c): return abs((b[0]-a[0])*(c[1]-a[1]) - (c[0]-a[0])*(b[1]-a[1])) / 2
    while len(hull) > 6:
        j = min(range(len(hull)), key=lambda j: area(hull[j-1], hull[j], hull[(j+1) % len(hull)]))
        hull.pop(j)
    return [int(round(v)) for pt in hull for v in (pt[0] - x0, pt[1] - y0)]
colsum = alpha.astype(float).sum(axis=0)
# the outline seen from above: for 40 vertical strips, how far down (0..1) the first drawn row is
has = alpha > 14
first = np.where(has.any(axis=0), has.argmax(axis=0), alpha.shape[0]) / alpha.shape[0]
tops = [round(float(first[int(i * len(first) / 40):int((i + 1) * len(first) / 40)].min()), 3) for i in range(40)]
out = {'w': int(x1 - x0), 'h': int(y1 - y0), 'top': tops, 'cx': round(float((colsum * np.arange(len(colsum))).sum() / colsum.sum() / len(colsum)), 4), 'leaves': [index[l] for l in leaves],
       'stones': [[index[parent[a]] if a != root else -1, dist[a]] + polygon(a) for a in nodes]}
json.dump(out, open('stones.json', 'w'), separators=(',', ':'))
print('stones seen', len(good), 'in the tree', len(nodes), 'leaves', len(leaves), 'max depth', max(dist[l] for l in leaves), 'json bytes', len(json.dumps(out, separators=(',', ':'))))
