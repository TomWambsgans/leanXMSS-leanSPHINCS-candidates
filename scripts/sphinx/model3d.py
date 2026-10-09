"""Primitives of the sphinx model (model4.py): signed distances, smooth unions, a hash of block indices, the camera."""
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

def hash3(a, b, c):
    h = (a * 73856093) ^ (b * 19349663) ^ (c * 83492791)
    h = (h ^ (h >> 13)) * 1274126177
    return ((h ^ (h >> 16)) & 0xffff) / 65535.0

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
