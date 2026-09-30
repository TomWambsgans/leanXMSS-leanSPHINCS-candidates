# leansphincs-candidate

**leanSPHINCS** is a stateless hash-based signature scheme (NIST category 1, n = 16 bytes). It keeps the
shape of SLH-DSA-SHA2-128-24: one XMSS tree over one-time keys, with FORS signing the message. It uses
h = 26, a = 10, k = 24 and WOTS+C (w = 4, 64 chains, digit sum S = 120), and it:

- signs 2^30 messages per key at 128-bit security, with 5,684-byte signatures;
- verifies every signature with the same cost: 366 hash calls (392 SHA-256 compressions);
- lets weak signers prune the tree: about 1M compressions of keygen for a 2^16-signature key, which then
  signs in about 200K.

- [`leansphincs.tex`](leansphincs.tex): the specification. Build it with
  `mkdir -p .build && pdflatex -output-directory=.build leansphincs.tex`, run twice.
- [`scripts/scheme.py`](scripts/scheme.py): sizes, costs and lifetime of the scheme (every number in the
  document), plus `--sweep` to explore other h, a and k.
- [`scripts/fors_security.py`](scripts/fors_security.py): security level against the number of signatures;
  `--selftest` checks it against published numbers.
