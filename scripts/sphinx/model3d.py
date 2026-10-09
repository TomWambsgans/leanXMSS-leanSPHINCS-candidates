"""A 3D model of the Great Sphinx as a signed distance function, ray-marched with numpy (metres; x forward,
y lateral, z up, ground z = 0)."""
import numpy as np

def smin(a, b, k):
    h = np.clip(0.5 + 0.5 * (b - a) / k, 0, 1)
    return b + (a - b) * h - k * h * (1 - h)

def smax(a, b, k): return -smin(-a, -b, k)

def ell(p, c, r):
    q = (p - np.array(c)) / np.array(r)
    k0 = np.linalg.norm(q, axis=-1)
    k1 = np.linalg.norm(q / np.array(r), axis=-1) + 1e-9
    return k0 * (k0 - 1) / k1

def box(p, c, h, r=0.0):
    q = np.abs(p - np.array(c)) - (np.array(h) - r)
    return np.linalg.norm(np.maximum(q, 0), axis=-1) + np.minimum(q.max(axis=-1), 0) - r

def cap(p, a, b, r):
    a = np.array(a, float); b = np.array(b, float); ab = b - a
    t = np.clip(((p - a) @ ab) / (ab @ ab), 0, 1)
    return np.linalg.norm(p - a - t[..., None] * ab, axis=-1) - r

def smooth_sdf(p):
    m = p.copy(); m[..., 1] = np.abs(m[..., 1])          # mirror symmetry
    d = box(p, (23, 0, 6.0), (25, 8.8, 6.6), 4.6)                      # body
    d = smin(d, ell(p, (40, 0, 6.5), (11, 8.8, 6.8)), 2.5)             # shoulders
    d = smin(d, ell(m, (7.5, 8.2, 4.8), (10, 4.8, 6.6)), 1.8)           # haunches
    d = smin(d, box(m, (17.5, 12.4, 1.3), (7.5, 2.0, 1.5), 1.1), 0.9)   # rear paws
    d = smin(d, ell(p, (49.5, 0, 7.6), (6.5, 7.6, 7.8)), 2.5)          # chest
    d = smin(d, box(m, (59.0, 5.9, 2.3), (11.5, 3.2, 2.7), 1.9), 1.6)    # front legs
    d = smin(d, cap(p, (52.5, 0, 10.5), (55.4, 0, 15.5), 3.2), 2.0)    # neck
    # head and headdress, modelled around (56.6, 0, 12) and enlarged
    HS = 1.2
    q = (p - np.array((56.6, 0, 12.0))) / HS + np.array((56.6, 0, 12.0))
    qm = q.copy(); qm[..., 1] = np.abs(qm[..., 1])
    head = ell(q, (56.4, 0, 17.6), (3.4, 2.9, 3.9))                               # skull
    head = smin(head, box(q, (58.0, 0, 16.2), (1.5, 2.25, 2.7), 1.2), 0.5)         # a broad, square face
    head = smin(head, ell(qm, (59.0, 1.55, 16.55), (0.8, 0.9, 0.8)), 0.5)          # cheekbones
    head = smin(head, ell(q, (58.85, 0, 13.95), (1.25, 1.85, 0.95)), 0.6)          # jaw and chin (the beard is lost)
    head = smin(head, ell(qm, (59.2, 1.25, 18.3), (0.45, 1.15, 0.24)), 0.35)        # brows
    head = smax(head, -ell(qm, (59.9, 1.25, 17.66), (0.5, 0.82, 0.42)), 0.22)      # eye sockets
    head = smin(head, ell(qm, (59.42, 1.25, 17.62), (0.34, 0.62, 0.28)), 0.12)     # lidded eyes
    head = smin(head, ell(q, (59.7, 0, 17.25), (0.35, 0.45, 0.85)), 0.3)           # what is left of the nose bridge
    head = smax(head, -ell(q, (60.1, 0, 16.45), (0.55, 0.78, 0.78)), 0.2)          # the nose, broken off
    head = smin(head, ell(q, (59.6, 0, 15.36), (0.42, 1.2, 0.26)), 0.2)           # lips
    head = smin(head, ell(q, (59.54, 0, 14.95), (0.4, 1.0, 0.27)), 0.2)
    head = smax(head, -ell(q, (59.95, 0, 15.16), (0.32, 1.15, 0.075)), 0.06)
    head = smin(head, ell(qm, (57.0, 3.0, 17.35), (0.6, 0.42, 1.05)), 0.2)         # ears
    head = smax(head, -ell(qm, (57.25, 3.4, 17.3), (0.3, 0.3, 0.6)), 0.15)
    # headdress: a pleated cloth, wider at the shoulders than at the crown, behind the face
    z = q[..., 2]
    w = 6.9 + (3.6 - 6.9) * np.clip((z - 11.5) / 9.0, 0, 1)
    front = q[..., 0] - (57.75 - 0.75 * np.clip(qm[..., 1] - 2.7, 0, None))        # the wings sweep back from the temples
    cloth = np.maximum(np.maximum(np.maximum(qm[..., 1] - w, front), 52.3 - q[..., 0]), 11.0 - z) / 1.25
    cloth = smax(cloth, ell(q, (55.4, 0, 14.4), (4.9, 8.6, 7.6)), 0.6)             # rounded crown
    cloth = cloth + 0.07 * np.sin(11.0 * z + 0.6 * qm[..., 1])                     # pleats
    cloth = smax(cloth, -ell(q, (59.6, 0, 16.2), (2.3, 3.0, 4.4)), 0.3)            # opening for the face
    cloth = smin(cloth, box(qm, (56.9, 3.7, 12.4), (1.1, 1.25, 3.3), 0.5), 0.5)    # lappets on the chest
    band = smax(ell(q, (56.9, 0, 19.3), (2.72, 3.0, 0.4)), 55.6 - q[..., 0], 0.3)  # the band on the forehead
    head = smin(head, band, 0.12)
    head = smin(head, cloth, 0.3)
    head = smin(head, box(q, (58.3, 0, 20.9), (0.45, 0.4, 0.75), 0.25), 0.3)       # the stump of the uraeus
    # weathering of the head: pitted cheeks, a worn crown
    head = head + 0.05 * np.sin(2.9 * q[..., 0] + 1.3) * np.sin(3.7 * q[..., 1]) * np.sin(3.1 * z + 0.7)
    d = smin(d, head * HS, 0.6)
    # an archaeological vestige: chips broken off, and fallen blocks on the ground
    for c, r in (((57.9, -5.3, 8.8), 1.5), ((55.6, -4.5, 22.4), 1.1), ((70.6, -8.7, 4.6), 1.6), ((-1.2, -6.0, 9.2), 2.1),
                 ((22.0, -8.2, 11.6), 1.9), ((40.5, -9.0, 9.4), 1.7), ((66.0, 3.0, 4.9), 1.3), ((50.5, -6.6, 12.6), 1.2)):
        d = smax(d, -(np.linalg.norm(p - np.array(c), axis=-1) - r), 0.25)
    for c, h, a in (((44.0, -15.5, 0.45), (1.1, 0.7, 0.5), 0.5), ((47.2, -14.2, 0.35), (0.8, 0.6, 0.4), -0.3),
                    ((30.0, -15.0, 0.4), (1.0, 0.6, 0.45), 1.1), ((74.5, -11.0, 0.4), (0.9, 0.7, 0.45), 0.2),
                    ((6.0, -17.0, 0.5), (1.2, 0.8, 0.55), -0.6), ((9.2, -18.2, 0.3), (0.6, 0.5, 0.35), 0.9),
                    ((77.0, 1.5, 0.4), (0.9, 0.6, 0.45), 0.7)):
        ca, sa = np.cos(a), np.sin(a)
        v = p - np.array(c)
        v = np.stack([v[..., 0] * ca + v[..., 1] * sa, -v[..., 0] * sa + v[..., 1] * ca, v[..., 2]], -1)
        d = np.minimum(d, box(v, (0, 0, 0), h, 0.12))
    return np.maximum(d, -p[..., 2])                                               # cut at the ground

def hash3(a, b, c):
    h = (a * 73856093) ^ (b * 19349663) ^ (c * 83492791)
    h = (h ^ (h >> 13)) * 1274126177
    return ((h ^ (h >> 16)) & 0xffff) / 65535.0

def blocks(p):
    """The stones: a staggered grid of blocks in space, finer above the shoulders, slightly warped."""
    x, y, z = p[..., 0], p[..., 1], p[..., 2]
    fine = z > 13.3
    Hc = np.where(fine, 0.62, 1.0); Lc = np.where(fine, 1.3, 2.3)
    zw = z + 0.10 * np.sin(0.55 * x + 0.8 * y) + 0.06 * np.sin(1.7 * x - 1.1 * y)
    k = np.floor(zw / Hc).astype(np.int64)
    off = (k % 2) * Lc / 2 + hash3(k, 0, 7) * Lc * 0.5
    xw = x + off + 0.16 * np.sin(1.3 * z + 0.6 * y); yw = y + off * 0.7 + 0.16 * np.sin(1.1 * z + 0.7 * x)
    bx = np.floor(xw / Lc).astype(np.int64); by = np.floor(yw / Lc).astype(np.int64)
    return fine, k, bx, by, zw, xw, yw, Hc, Lc

def sdf(p):
    """The weathered surface: uneven and missing stones, and eroded layers on the body."""
    d = smooth_sdf(p)
    x, z = p[..., 0], p[..., 2]
    fine, k, bx, by = blocks(p)[:4]
    face = fine & (x > 58.3)
    uneven = 0.09 * hash3(bx + 3, by + 9, k + 1)
    gone = np.where(hash3(bx - 7, by + 2, k + 5) < np.where(fine, 0.05, 0.085), np.where(fine, 0.22, 0.42), 0.0)
    layers = 0.26 * np.clip(np.sin(3.3 * z + 0.6 * np.sin(0.21 * x) + 0.4 * np.sin(0.5 * p[..., 1])), 0, 1) ** 2
    layers = layers * np.clip((z - 4.6) / 1.2, 0, 1) * np.clip((13.0 - z) / 1.0, 0, 1) * np.clip((51.0 - x) / 3, 0, 1)
    return d + np.where(face, 0.25 * uneven, uneven + gone) + layers

def camera(Wp, Hp, eye=(108, -66, 25), at=(35.5, 0, 9.4), fov=23.5):
    eye = np.array(eye, float); at = np.array(at, float)
    f = at - eye; f /= np.linalg.norm(f)
    r = np.cross(f, (0, 0, 1)); r /= np.linalg.norm(r)
    u = np.cross(r, f)
    t = np.tan(np.radians(fov) / 2)
    xs = (np.arange(Wp) + 0.5) / Wp * 2 - 1; ys = 1 - (np.arange(Hp) + 0.5) / Hp * 2
    X, Y = np.meshgrid(xs * t * Wp / Hp, ys * t)
    dirs = f + X[..., None] * r + Y[..., None] * u
    return eye, dirs / np.linalg.norm(dirs, axis=-1, keepdims=True)

def march(Wp, Hp, steps=230, t0=60.0, **kw):
    eye, dirs = camera(Wp, Hp, **kw)
    t = np.full((Hp, Wp), t0); hit = np.zeros((Hp, Wp), bool); alive = np.ones((Hp, Wp), bool)
    for _ in range(steps):
        idx = np.nonzero(alive)
        if len(idx[0]) == 0: break
        p = eye + t[idx][:, None] * dirs[idx]
        d = sdf(p)
        t[idx] += d * 0.55
        h = d < 0.015
        hit[idx[0][h], idx[1][h]] = True
        done = h | (t[idx] > 190)
        alive[idx[0][done], idx[1][done]] = False
    P = eye + t[..., None] * dirs
    e = 0.02; N = np.zeros_like(P)
    pts = P[hit]
    for a in range(3):
        o = np.zeros(3); o[a] = e
        N[hit, a] = sdf(pts + o) - sdf(pts - o)
    N[hit] /= np.linalg.norm(N[hit], axis=-1, keepdims=True) + 1e-12
    return hit, P, N, t, eye, dirs
