#!/usr/bin/env python3
"""AND gates and AND-depth of BLAKE2s compressions as a Boolean circuit (XOR and rotations are free).

In secret-sharing MPC, AND gates cost traffic and AND-depth costs rounds (one round per layer of AND
gates, all independent hashes in parallel). 32-bit additions use ripple-carry adders (fewest AND gates) or
Sklansky parallel-prefix adders (lower depth). A three-operand addition is a carry-save layer followed by
one adder. Every input is treated as secret, so the counts are upper bounds.
"""

SIGMA = [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
         [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
         [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
         [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
         [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
         [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
         [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
         [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
         [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
         [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]]


class Circuit:
    """Tracks the AND-depth of every bit (a word is a list of 32 depths, least significant bit first)."""

    def __init__(self, adder):
        self.ands = 0
        self.adder = {"ripple": self.ripple, "sklansky": self.sklansky}[adder]

    def AND(self, x, y):
        self.ands += 1
        return max(x, y) + 1

    def maj(self, x, y, z):  # x ^ ((x ^ y) & (x ^ z))
        return self.AND(max(x, y), max(x, z))

    def ripple(self, x, y, first_carry=True):
        s, c = [], None
        for i in range(32):
            s.append(max(x[i], y[i]) if c is None else max(x[i], y[i], c))
            if i == 31 or (i == 0 and not first_carry):  # no carry out of bit 0 if y[0] is the constant 0
                continue
            c = self.AND(x[i], y[i]) if c is None else self.maj(x[i], y[i], c)
        return s

    def sklansky(self, x, y, first_carry=True):
        g = [self.AND(x[i], y[i]) for i in range(31)]
        p = [max(x[i], y[i]) for i in range(31)]
        d = 1
        while d < 31:
            for i in range(31):
                if (i // d) % 2 == 1:
                    j = (i // d) * d - 1
                    g[i] = max(g[i], self.AND(p[i], g[j]))  # g ^ (p & g')
                    p[i] = self.AND(p[i], p[j])
            d *= 2
        return [max(x[0], y[0])] + [max(x[i], y[i], g[i - 1]) for i in range(1, 32)]

    def add3(self, x, y, z):
        s = [max(x[i], y[i], z[i]) for i in range(32)]
        carries = [0] + [self.maj(x[i], y[i], z[i]) for i in range(31)]  # carries[0] is the constant 0
        return self.adder(s, carries, first_carry=self.adder != self.ripple)

    def compress(self, m):
        """m: 16 message words. Returns the 8 output words (h ^ v[0:8] ^ v[8:16])."""
        v = [[0] * 32 for _ in range(16)]
        xor_rot = lambda x, y, r: [max(p, q) for p, q in zip(x, y)][r:] + [max(p, q) for p, q in zip(x, y)][:r]

        def g(r, i, a, b, c, d):
            v[a] = self.add3(v[a], v[b], m[SIGMA[r][2 * i]]); v[d] = xor_rot(v[d], v[a], 16)
            v[c] = self.adder(v[c], v[d]);                    v[b] = xor_rot(v[b], v[c], 12)
            v[a] = self.add3(v[a], v[b], m[SIGMA[r][2 * i + 1]]); v[d] = xor_rot(v[d], v[a], 8)
            v[c] = self.adder(v[c], v[d]);                    v[b] = xor_rot(v[b], v[c], 7)

        for r in range(10):
            g(r, 0, 0, 4, 8, 12); g(r, 1, 1, 5, 9, 13); g(r, 2, 2, 6, 10, 14); g(r, 3, 3, 7, 11, 15)
            g(r, 4, 0, 5, 10, 15); g(r, 5, 1, 6, 11, 12); g(r, 6, 2, 7, 8, 13); g(r, 7, 3, 4, 9, 14)
        return [[max(p, q) for p, q in zip(v[i], v[i + 8])] for i in range(8)]


def chain(steps, adder="ripple"):
    """AND gates per compression and AND-depth of `steps` chained hashes Th(P, tw, x): the 16-byte x sits at
    bytes 32..47 of the block and the output is truncated to 16 bytes."""
    c = Circuit(adder)
    x = [[0] * 32 for _ in range(4)]
    for _ in range(steps):
        m = [[0] * 32 for _ in range(16)]
        m[8:12] = x
        x = c.compress(m)[:4]
    return c.ands // max(steps, 1), max(max(w) for w in x)


if __name__ == "__main__":
    for adder in ("ripple", "sklansky"):
        ands, _ = chain(1, adder)
        depths = [chain(s, adder)[1] for s in (1, 2, 3)]
        print(f"{adder}: {ands} AND gates per compression; AND-depth of 1, 2, 3 chained hashes: {depths}")
