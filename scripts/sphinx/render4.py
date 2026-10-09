"""The sphinx of the website (site/sphinx.png and the stone data `D` in site/index.html). Needs numpy and scipy.

    python3 render4.py 1900          # writes sphinx.png (alpha = darkness) and stones.json in the current directory
    python3 render4.py 1000 head     # a close-up of the head, to work on the model

model4.py is the 3D model (a signed distance function, ray-marched); model3d.py holds its primitives. sphinx.png is
used as a CSS mask (sphinx_preview.png is the same picture, black on white, to look at). stones.json holds the image
size (w, h), the outline seen from above (top), the direction of the light on the image, the stones and the routes;
it is the object `D` of the last script of site/index.html: paste it after `var D = `, and when the image changes
raise the `?v=` number of the three `sphinx.png` references of that page. A stone is [dx, dy, x0, y0, x1, y1, ...]: its outline, and
(dx, dy), how its face moves when it is pushed in. A route is the list of its stones, from the line to the head.
    python3 render4.py 1900 full check   # also prints the quality of the stones and of the routes"""
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
rowmax = {i: int(pix(i)[0].max()) for i in good}
leaves = [i for i in good if i in dist and ((ids[i] >> 44) & 3) == 3 and rowmax[i] >= cut - 45]     # the two courses at the line
from scipy import ndimage

def region(i):
    """the largest connected piece of stone i: its mask, the offset of the mask, and its share of the stone"""
    yy, xx = pix(i)
    oy, ox = yy.min() - 1, xx.min() - 1
    m = np.zeros((yy.max() - oy + 2, xx.max() - ox + 2), bool); m[yy - oy, xx - ox] = True
    lab_, n = ndimage.label(m)
    if n > 1:
        sizes = ndimage.sum(m, lab_, range(1, n + 1)); m = lab_ == (1 + int(np.argmax(sizes)))
    return m, ox, oy, m.sum() / len(yy)

def outline(m):
    """the outer boundary of a mask, along the pixel edges, as a closed list of corners (x, y)"""
    nxt = {}
    H_, W_ = m.shape
    for y_ in range(H_):
        for x_ in range(W_):
            if not m[y_, x_]: continue
            if not m[y_ - 1, x_]: nxt.setdefault((x_, y_), []).append((x_ + 1, y_))          # top edge, going right
            if not m[y_, x_ + 1]: nxt.setdefault((x_ + 1, y_), []).append((x_ + 1, y_ + 1))  # right edge, going down
            if not m[y_ + 1, x_]: nxt.setdefault((x_ + 1, y_ + 1), []).append((x_, y_ + 1))  # bottom edge, going left
            if not m[y_, x_ - 1]: nxt.setdefault((x_, y_ + 1), []).append((x_, y_))          # left edge, going up
    start = min(nxt, key=lambda c: (c[1], c[0])); pts = [start]; cur = start; prev = (start[0] - 1, start[1])
    while True:
        outs = nxt[cur]
        if len(outs) > 1:                                    # two pieces touch by a corner: turn right, stay on this one
            dx_, dy_ = cur[0] - prev[0], cur[1] - prev[1]
            outs = sorted(outs, key=lambda o: ((o[0] - cur[0]) * dy_ - (o[1] - cur[1]) * dx_))
        prev, cur = cur, outs[0]
        if cur == start: break
        pts.append(cur)
    return pts

def simplify(pts, eps):
    """Ramer-Douglas-Peucker on a closed outline"""
    pts = np.array(pts, float)
    a = int(np.argmax(((pts - pts.mean(0)) ** 2).sum(1))); pts = np.roll(pts, -a, axis=0)
    b = int(np.argmax(((pts - pts[0]) ** 2).sum(1)))
    def rdp(seg):
        if len(seg) < 3: return seg[:1]
        p0, p1 = seg[0], seg[-1]; d = p1 - p0; n = np.hypot(*d) + 1e-9
        dist_ = np.abs((seg[:, 0] - p0[0]) * d[1] - (seg[:, 1] - p0[1]) * d[0]) / n
        k = int(np.argmax(dist_))
        if dist_[k] <= eps: return seg[:1]
        return np.vstack([rdp(seg[:k + 1]), rdp(seg[k:])])
    return np.vstack([rdp(pts[:b + 1]), rdp(np.vstack([pts[b:], pts[:1]]))])

shape_cache = {}
def shape(i):
    """polygon of stone i (image coordinates, x0 y0 x1 y1 ...) and whether it is fit to be moved: one piece, not a
    sliver seen edge-on, compact enough"""
    if i not in shape_cache:
        m, ox, oy, share = region(i)
        pg = simplify(outline(m), 1.2) + np.array([ox - x0, oy - y0])
        area = float(m.sum()); ys_, xs_ = np.nonzero(m)
        pts = np.stack([xs_, ys_], 1).astype(float)
        # the smaller side: the extent across the main axis
        c = pts - pts.mean(0); ev, evec = np.linalg.eigh(c.T @ c / len(c))
        thick = float(np.ptp(c @ evec[:, 0])) + 1
        solid = area / ConvexHull(np.vstack([pts, pts + 1])).volume
        ok = share > 0.9 and area >= 150 and thick >= 9.0 and solid >= 0.72 and len(pg) >= 3
        shape_cache[i] = ([round(float(v), 1) for q in pg for v in q], ok, thick)
    return shape_cache[i]

def polygon(i): return shape(i)[0]

def push(i, poly):
    """how the face of stone i moves on the image when the stone is pushed into the wall: a short vector along
    the projection of the inward normal, 40% of the stone's smaller side"""
    yy, xx = pix(i)
    pc = P[yy, xx].mean(axis=0); nc = N[yy, xx].mean(axis=0); nc = nc / (np.linalg.norm(nc) + 1e-9)
    a = np.array(project(pc)); b = np.array(project(pc - 1.0 * nc))
    d = b - a
    L = float(np.clip(0.4 * shape(i)[2], 3.5, 18.0))
    n = np.linalg.norm(d)
    d = d / n * L if n > 0.3 else np.array([0.5 * L, -0.5 * L])
    return [round(float(d[0]), 1), round(float(d[1]), 1)]

# One route per starting stone, each its own: a cheapest path to the top of the head with random costs, where a
# stone already used by other routes costs more and going down costs much more. A route keeps only the stones fit
# to be moved and steps over the others (the terraces seen edge-on, slivers).
import heapq
used = {}
def route(leaf, seed):
    r = np.random.default_rng(seed)
    cost = {leaf: 0.0}; prev = {}; heap = [(0.0, leaf)]; done = set()
    while heap:
        c, a = heapq.heappop(heap)
        if a in done: continue
        done.add(a)
        if a == root: break
        for b in adj.get(a, ()):
            if b not in dist or b in done: continue
            w = 1.0 + 1.5 * r.random() + 0.9 * used.get(b, 0) + 4.0 * max(0.0, zc[a] - zc[b]) + (0.0 if shape(b)[1] else 3.0)
            if c + w < cost.get(b, 1e18): cost[b] = c + w; prev[b] = a; heapq.heappush(heap, (c + w, b))
    path = [root]
    while path[-1] != leaf: path.append(prev[path[-1]])
    return path[::-1]
def longest_gap(full):
    """the longest run of stones a route steps over"""
    run = best = 0
    for a in full:
        run = 0 if shape(a)[1] else run + 1; best = max(best, run)
    return best
routes = []
wide = x1 - x0
for n_, l in enumerate(sorted(leaves, key=lambda i: pix(i)[1].mean())):
    cx_ = (pix(l)[1].mean() - x0) / wide
    if not (0.10 < cx_ < 0.90 and shape(l)[1]): continue           # a route starts on a whole stone, clear of the faded ends
    found = 0
    for attempt in range(14):                                       # up to two routes from a stone; a route may step
        full = route(l, 100 + n_ + 1000 * attempt)                  # over three stones in a row, not more
        kept = [a for a in full if shape(a)[1]]
        if longest_gap(full) > 3 or len(kept) < 18: continue
        if any(len(set(kept) & set(o)) > 0.5 * min(len(kept), len(o)) for o in routes): continue    # too close to another
        routes.append(kept); found += 1
        for a in kept: used[a] = used.get(a, 0) + 1
        if found == 2: break
moved = sorted({a for rt in routes for a in rt})
mindex = {a: n for n, a in enumerate(moved)}

if len(sys.argv) > 3 and sys.argv[3] == 'check':        # how well each stone of the tree is described by its polygon
    def parea(pg):
        xs_, ys_ = pg[0::2], pg[1::2]; n = len(xs_)
        return abs(sum(xs_[i] * ys_[(i + 1) % n] - xs_[(i + 1) % n] * ys_[i] for i in range(n))) / 2
    rows = []
    for a in moved:
        pg = polygon(a); d2 = push(a, pg); xs_, ys_ = pg[0::2], pg[1::2]
        rows.append((cnt[a] / parea(pg), mindex[a], int(cnt[a]), int(max(xs_) - min(xs_)), int(max(ys_) - min(ys_)), d2, int((ids[a] >> 44) & 3), used[a], len(pg) // 2))
    rows.sort()
    print('fill ratio (stone pixels / polygon area), worst first: ratio, index, pixels, w, h, push, material, depth')
    for r in rows[:25]: print('  %.2f' % r[0], r[1:])
    print('ratio < 0.8:', sum(1 for r in rows if r[0] < 0.8), ' < 0.9:', sum(1 for r in rows if r[0] < 0.9), ' of', len(rows))
    print('smallest stones:', sorted((r[2], r[1], r[3], r[4]) for r in rows)[:12])
    print('thinnest:', sorted((round(shape(a)[2], 1), mindex[a]) for a in moved)[:12])
    print('stones', len(moved), 'routes', len(routes), 'lengths', sorted(len(rt) for rt in routes), 'corners per stone: mean %.1f max %d' % (np.mean([r[8] for r in rows]), max(r[8] for r in rows)))
    ov = [len(set(a_) & set(b_)) / min(len(a_), len(b_)) for i_, a_ in enumerate(routes) for b_ in routes[i_ + 1:]]
    print('share of a route in common with another: mean %.2f, max %.2f; most used stone is on %d routes' % (np.mean(ov), max(ov), max(used.values())))
colsum = alpha.astype(float).sum(axis=0)
# the outline seen from above: for 40 vertical strips, how far down (0..1) the first drawn row is
has = alpha > 14
first = np.where(has.any(axis=0), has.argmax(axis=0), alpha.shape[0]) / alpha.shape[0]
tops = [round(float(first[int(i * len(first) / 40):int((i + 1) * len(first) / 40)].min()), 3) for i in range(40)]
_c = np.array((40.0, -8.0, 8.0)); _l = np.array(project(_c - 3 * Lg)) - np.array(project(_c)); _l = _l / np.linalg.norm(_l)   # the light, on the image
out = {'w': int(x1 - x0), 'h': int(y1 - y0), 'light': [round(float(_l[0]), 3), round(float(_l[1]), 3)], 'top': tops, 'cx': round(float((colsum * np.arange(len(colsum))).sum() / colsum.sum() / len(colsum)), 4), 'routes': [[mindex[a] for a in rt] for rt in routes],
       'stones': [(lambda pg: push(a, pg) + pg)(polygon(a)) for a in moved]}
json.dump(out, open('stones.json', 'w'), separators=(',', ':'))
print('stones seen', len(good), 'moved', len(moved), 'routes', len(routes), 'json bytes', len(json.dumps(out, separators=(',', ':'))))
