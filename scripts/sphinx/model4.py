"""The Great Sphinx as it stands today, as a signed distance function (metres; x forward, y lateral, z up).
Bedrock body with eroded beds, small restoration masonry on the paws and the lower body, the head with its
headdress, the stele between the paws. Ray-marched with numpy."""
import numpy as np
from model3d import smin, smax, ell, box, cap, hash3, camera

HS = 1.06                                   # the head, slightly enlarged
HC = np.array((56.4, 0.0, 12.0))

def core(p):
    m = p.copy(); m[..., 1] = np.abs(m[..., 1])
    d = box(p, (22, 0, 5.6), (24, 7.6, 6.0), 4.2)                       # trunk
    d = smin(d, ell(p, (39, 0, 6.6), (11, 8.6, 6.3)), 2.5)              # shoulders
    d = smin(d, ell(m, (7.5, 7.8, 4.6), (9.5, 4.6, 6.2)), 1.8)          # haunches
    d = smin(d, ell(p, (49.8, 0, 6.6), (7.2, 8.2, 8.0)), 2.5)           # chest
    d = smin(d, cap(p, (52.8, 0, 11.0), (55.2, 0, 15.4), 3.1), 1.8)     # neck, worn
    d = smin(d, ell(m, (47.0, 7.0, 3.2), (5.0, 3.0, 3.9)), 1.2)         # elbows
    paw = box(m, (59.5, 6.3, 1.9), (12.5, 2.9, 1.95), 0.75)             # long, flat-topped paws
    for yo in (-1.0, 1.0):                                              # toes
        paw = smax(paw, -box(m, (71.4, 6.3 + yo, 2.6), (1.7, 0.14, 2.2)), 0.12)
    d = smin(d, paw, 0.5)
    d = smin(d, box(m, (15.0, 12.3, 1.25), (8.0, 2.0, 1.3), 0.6), 0.6)  # rear paws
    # head
    q = (p - HC) / HS + HC
    qm = q.copy(); qm[..., 1] = np.abs(qm[..., 1])
    z = q[..., 2]
    head = ell(q, (56.4, 0, 17.6), (3.4, 2.9, 3.9))
    head = smin(head, box(q, (58.0, 0, 16.2), (1.5, 2.25, 2.7), 1.2), 0.5)
    head = smin(head, ell(qm, (59.0, 1.55, 16.55), (0.8, 0.9, 0.8)), 0.5)
    head = smin(head, ell(q, (58.85, 0, 13.95), (1.25, 1.85, 0.95)), 0.6)
    head = smin(head, ell(qm, (59.2, 1.25, 18.3), (0.45, 1.15, 0.24)), 0.35)
    head = smax(head, -ell(qm, (59.9, 1.25, 17.66), (0.5, 0.82, 0.42)), 0.22)
    head = smin(head, ell(qm, (59.42, 1.25, 17.62), (0.34, 0.62, 0.28)), 0.12)
    head = smin(head, ell(q, (59.7, 0, 17.25), (0.35, 0.45, 0.85)), 0.3)
    head = smax(head, -ell(q, (60.1, 0, 16.45), (0.55, 0.78, 0.78)), 0.2)
    head = smin(head, ell(q, (59.6, 0, 15.36), (0.42, 1.2, 0.26)), 0.2)
    head = smin(head, ell(q, (59.54, 0, 14.95), (0.4, 1.0, 0.27)), 0.2)
    head = smax(head, -ell(q, (59.95, 0, 15.16), (0.32, 1.15, 0.075)), 0.06)
    head = smin(head, ell(qm, (57.0, 3.0, 17.35), (0.6, 0.42, 1.05)), 0.2)
    head = smax(head, -ell(qm, (57.25, 3.4, 17.3), (0.3, 0.3, 0.6)), 0.15)
    # headdress: flat triangular wings behind the ears, finely pleated; the lappets are lost
    w = 6.3 + (3.5 - 6.3) * np.clip((z - 12.6) / 8.0, 0, 1)
    front = q[..., 0] - (57.7 - 0.8 * np.clip(qm[..., 1] - 2.7, 0, None))
    cloth = np.maximum(np.maximum(np.maximum(qm[..., 1] - w, front), 52.8 - q[..., 0]), 12.6 - z) / 1.25
    cloth = smax(cloth, ell(q, (55.4, 0, 14.4), (4.9, 8.6, 7.4)), 0.6)
    cloth = smax(cloth, z - 21.45, 0.5)                                            # the flat crown
    cloth = cloth + 0.035 * np.sin(17.0 * z + 5.0 * qm[..., 1])
    cloth = smax(cloth, -ell(q, (59.6, 0, 16.2), (2.3, 3.0, 4.4)), 0.3)
    band = smax(ell(q, (56.9, 0, 19.3), (2.72, 3.0, 0.4)), 55.6 - q[..., 0], 0.3)
    head = smin(head, band, 0.12)
    head = smin(head, cloth, 0.3)
    head = smin(head, box(q, (58.3, 0, 20.9), (0.4, 0.38, 0.6), 0.22), 0.3)
    d = smin(d, head * HS, 0.5)
    # the stele and the altar between the paws, a small masonry chapel by the flank
    d = np.minimum(d, box(p, (56.9, 0, 1.9), (0.4, 1.15, 1.9), 0.12))
    d = np.minimum(d, box(p, (61.5, 0, 0.5), (0.9, 0.9, 0.5), 0.1))
    d = np.minimum(d, box(p, (34.0, -11.4, 1.4), (2.4, 1.7, 1.4), 0.15))
    # breaks
    for c, r in (((71.0, -9.1, 3.9), 1.2), ((-1.2, -6.0, 9.2), 2.1), ((22.0, -7.2, 11.0), 1.9), ((40.5, -8.4, 10.6), 1.6),
                 ((54.6, -6.0, 15.2), 1.3), ((54.9, -4.4, 22.3), 0.9), ((49.0, -7.0, 11.6), 1.3)):
        d = smax(d, -(np.linalg.norm(p - np.array(c), axis=-1) - r), 0.25)
    # the podium that carries it: two tiers of large blocks, with broken corners
    pod = box(p, (35.5, 0, -1.0), (41.5, 16.8, 1.0), 0.12)                 # the sphinx stands on the upper tier
    pod = np.minimum(pod, box(p, (36.0, 0, -16.05), (45.0, 20.0, 15.0), 0.12))   # a step of one course, then the wall
    for c, r in (((77.0, -16.8, 0.2), 2.2), ((81.0, -20.0, -0.8), 2.4), ((30.0, -17.4, 0.3), 1.4), ((8.0, -20.4, -0.9), 1.8),
                 ((56.0, -20.4, -1.2), 1.3), ((78.0, 6.0, 0.4), 1.6), ((-6.5, -16.8, 0.0), 2.0)):
        pod = smax(pod, -(np.linalg.norm(p - np.array(c), axis=-1) - r), 0.2)
    d = np.minimum(d, pod)
    # fallen blocks, on the tiers
    for c, h, a in (((44.0, -18.4, -0.6), (1.1, 0.7, 0.5), 0.5), ((47.2, -18.2, -0.7), (0.8, 0.6, 0.4), -0.3),
                    ((22.0, -18.5, -0.65), (1.0, 0.6, 0.45), 1.1), ((79.3, -12.5, -0.65), (0.9, 0.7, 0.45), 0.2),
                    ((70.0, -18.4, -0.6), (1.2, 0.8, 0.5), -0.6), ((62.0, -14.6, 0.4), (0.8, 0.6, 0.42), 0.8)):
        ca, sa = np.cos(a), np.sin(a); v = p - np.array(c)
        v = np.stack([v[..., 0] * ca + v[..., 1] * sa, -v[..., 0] * sa + v[..., 1] * ca, v[..., 2]], -1)
        d = np.minimum(d, box(v, (0, 0, 0), h, 0.12))
    return d

BRICK = (0.66, 1.75); BED = (1.2, 3.6); HEAD = (0.62, 1.4); BASE = (1.05, 2.9)

def blocks(p):
    """material (0 bedrock beds, 1 masonry, 2 head, 3 podium), course, block indices, and the warped coordinates"""
    x, y, z = p[..., 0], p[..., 1], p[..., 2]
    ay = np.abs(y)
    paw = (x > 46.3) & (ay > 3.2) & (ay < 9.6) & (z < 4.4)
    rpaw = (x > 6.5) & (x < 23.5) & (ay > 10.0) & (z < 3.0)
    hx = np.floor((x + 1.3 * np.sin(0.4 * y)) / 3.4).astype(np.int64)
    hcl = 3.3 + 2.3 * hash3(hx, 1, 2) + np.where(x < 17, 2.6, 0) + np.where((x > 40) & (x < 47), 1.6, 0) - np.where(x > 52, 1.2, 0)
    hcl = np.floor(hcl / BRICK[0]) * BRICK[0]
    clad = z < hcl
    head = (z > 13.4) & (x > 50.5)
    mat = np.where(z < 0.04, 3, np.where(head, 2, np.where(paw | rpaw | clad, 1, 0)))
    Hc = np.choose(mat, [BED[0], BRICK[0], HEAD[0], BASE[0]]); Lc = np.choose(mat, [BED[1], BRICK[1], HEAD[1], BASE[1]])
    wob = np.where(mat == 0, 1.0, 0.25)
    zw = z + wob * (0.22 * np.sin(0.33 * x + 0.5 * y) + 0.12 * np.sin(0.9 * x - 0.7 * y + 1.0))
    zw = zw + np.where(mat == 0, 0.42 * np.sin(1.9 * z + 0.6) + 0.22 * np.sin(4.3 * z + 2.0), 0.0)    # beds of unequal thickness
    k = np.floor(zw / Hc).astype(np.int64)
    off = (k % 2) * Lc / 2 + hash3(k, mat, 7) * Lc * 0.5
    xw = x + off + wob * 0.5 * np.sin(1.1 * z + 0.4 * y); yw = y + off * 0.7 + wob * 0.5 * np.sin(0.9 * z + 0.5 * x)
    bx = np.floor(xw / Lc).astype(np.int64); by = np.floor(yw / Lc).astype(np.int64)
    return mat, k, bx, by, zw, xw, yw, Hc, Lc

def sdf(p):
    d = core(p)
    mat, k, bx, by, zw, xw, yw, Hc, Lc = blocks(p)
    fz = zw - k * Hc; db = np.minimum(fz, Hc - fz)
    x, y, z = p[..., 0], p[..., 1], p[..., 2]
    # bedrock: grooves between beds, softer beds eaten further back, pitted faces
    bed = (0.14 + 0.3 * hash3(k, 2, 9)) * np.exp(-(db / (0.1 + 0.16 * hash3(k, 8, 1))) ** 2) + 0.5 * hash3(k, 5, 3) ** 2
    bed = bed + 0.09 * np.sin(0.8 * x + 1.7 * np.sin(0.5 * y)) * np.sin(2.1 * z + 0.3 * x) + 0.10 * np.sin(0.37 * x + 2.0 * np.sin(0.21 * y + 0.3 * z))
    bed = bed + 0.07 * np.sin(5.0 * zw + 0.4 * x)
    # masonry: a casing in front of the bedrock, uneven, a few bricks fallen
    brick = -0.3 + 0.04 * hash3(bx + 3, by + 9, k + 1) + np.where(hash3(bx - 7, by + 2, k + 5) < 0.03, 0.28, 0.0)
    # head: fine beds, pitting
    hd = 0.06 * np.exp(-(db / 0.07) ** 2) + 0.045 * np.sin(2.9 * x + 1.3) * np.sin(3.7 * y) * np.sin(3.1 * z + 0.7)
    face = (mat == 2) & (x > HC[0] + (58.3 - HC[0]) * HS)
    hd = np.where(face, 0.4 * hd, hd)
    base = 0.07 * hash3(bx + 3, by + 9, k + 1) + np.where(hash3(bx - 7, by + 2, k + 5) < 0.045, 0.4, 0.0)
    return d + np.choose(mat, [bed, brick, hd, base])

def march(Wp, Hp, steps=260, t0=45.0, **kw):
    eye, dirs = camera(Wp, Hp, **kw)
    t = np.full((Hp, Wp), t0); hit = np.zeros((Hp, Wp), bool); alive = np.ones((Hp, Wp), bool)
    for _ in range(steps):
        idx = np.nonzero(alive)
        if len(idx[0]) == 0: break
        d = sdf(eye + t[idx][:, None] * dirs[idx])
        t[idx] += d * 0.5
        h = d < 0.012
        hit[idx[0][h], idx[1][h]] = True
        done = h | (t[idx] > 230)
        alive[idx[0][done], idx[1][done]] = False
    P = eye + t[..., None] * dirs
    N = np.zeros_like(P); pts = P[hit]
    for a in range(3):
        o = np.zeros(3); o[a] = 0.025
        N[hit, a] = sdf(pts + o) - sdf(pts - o)
    N[hit] /= np.linalg.norm(N[hit], axis=-1, keepdims=True) + 1e-12
    return hit, P, N, t, eye, dirs

def shadow(pts, L, steps=48):
    """soft shadow towards the light"""
    t = np.full(len(pts), 0.25); res = np.ones(len(pts))
    for _ in range(steps):
        d = sdf(pts + t[:, None] * L)
        res = np.minimum(res, np.clip(10 * d / t, 0, 1))
        t += np.clip(d, 0.12, 2.5)
    return res
