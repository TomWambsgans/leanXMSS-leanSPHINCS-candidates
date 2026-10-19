#!/usr/bin/env python3
"""AND gates and AND-depth of Keccak-f[1600] as a Boolean circuit (XOR, NOT and rotations are free).

In secret-sharing MPC, AND gates cost traffic and AND-depth costs rounds (one round per layer of AND
gates, all independent hashes in parallel). Chi, a ^ (~b & c), is the only non-linear step: one AND per
state bit and per round, every round one AND layer. An AND costs only if both inputs are secret, so a
hash whose input is partly public folds part of its first round, and a truncated output skips the chi of
the lanes it drops in the last round. The same model as crates/mpc/src/keccak_circuit.rs.
"""

ROUNDS = 24
RHO = [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44]
PI = [10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1]


def permutation(secret, out_lanes=range(25)):
    """secret[lane][bit]: whether that state bit is secret. Returns the secret-secret AND gates of one
    Keccak-f whose outputs are the lanes `out_lanes` (theta makes every earlier gate live)."""
    a = [list(lane) for lane in secret]
    ands = 0
    for r in range(ROUNDS):
        c = [[any(a[x + 5 * y][i] for y in range(5)) for i in range(64)] for x in range(5)]
        d = [[c[(x + 4) % 5][i] or c[(x + 1) % 5][(i - 1) % 64] for i in range(64)] for x in range(5)]
        a = [[a[l][i] or d[l % 5][i] for i in range(64)] for l in range(25)]
        carried = a[1]
        for i in range(24):
            nxt = a[PI[i]]
            a[PI[i]] = [carried[(j - RHO[i]) % 64] for j in range(64)]
            carried = nxt
        live = range(25) if r < ROUNDS - 1 else out_lanes
        new = [lane[:] for lane in a]
        for l in range(25):
            x, y = l % 5, l // 5
            b, cc = a[(x + 1) % 5 + 5 * y], a[(x + 2) % 5 + 5 * y]
            for i in range(64):
                if b[i] and cc[i] and l in live:
                    ands += 1
                new[l][i] = a[l][i] or b[i] or cc[i]
        a = new
    return ands


def th(steps=1):
    """AND gates per hash and AND-depth of `steps` chained hashes Th(P, tw, x) = Keccak-256(P | tw | x)[:16]:
    P and tw public (bytes 0..31), the 16-byte x secret (bytes 32..47), the output truncated to 16 bytes."""
    secret = [[32 <= (8 * l + i // 8) < 48 for i in range(64)] for l in range(25)]
    return permutation(secret, out_lanes=[0, 1]), ROUNDS * steps


if __name__ == "__main__":
    print(f"all-secret permutation: {permutation([[True] * 64 for _ in range(25)])} AND gates, AND-depth {ROUNDS}")
    ands, _ = th()
    print(f"Th on a secret 16-byte value: {ands} AND gates; AND-depth of 1, 2, 3 chained hashes: "
          f"{[th(s)[1] for s in (1, 2, 3)]}")
