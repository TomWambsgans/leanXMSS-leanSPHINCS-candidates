import zlib, struct, numpy as np
def save(path, a):
    """a: uint8 array (H, W) gray, (H, W, 2) gray+alpha, or (H, W, 4) rgba"""
    a = np.ascontiguousarray(a, dtype=np.uint8)
    if a.ndim == 2: a = a[..., None]
    ct = {1: 0, 2: 4, 3: 2, 4: 6}[a.shape[2]]
    raw = b''.join(b'\x00' + a[y].tobytes() for y in range(a.shape[0]))
    def chunk(t, d): return struct.pack('>I', len(d)) + t + d + struct.pack('>I', zlib.crc32(t + d) & 0xffffffff)
    open(path, 'wb').write(b'\x89PNG\r\n\x1a\n' + chunk(b'IHDR', struct.pack('>IIBBBBB', a.shape[1], a.shape[0], 8, ct, 0, 0, 0)) +
                           chunk(b'IDAT', zlib.compress(raw, 9)) + chunk(b'IEND', b''))
