# leanSphincs candidate

A SPHINCS+ variant with the shape of SLH-DSA-128-24 (one Merkle tree over WOTS+C keys, FORS signing the
message), for 2^30 signatures per key at NIST level 1: 127 bits of classical security in the random-oracle
model (proof in Lean 4 to come):

- public key 32 bytes, signature 5,684 bytes;
- verification in 391 compressions, the same for every signature;
- key generation 18.4G compressions, or 1.12M for a pruned key signing 2^16 messages;
- signing in about 421K compressions with a 1 MiB cache, or about 140K for a pruned key.

Costs count 64-byte compression-function calls, as for BLAKE2s.

- [`leansphincs.tex`](leansphincs.tex): the specification. Build it with
  `mkdir -p .build && pdflatex -output-directory=.build leansphincs.tex`, run twice.
- [`scripts/scheme.py`](scripts/scheme.py): sizes, costs and lifetime (the numbers in the specification).
- [`scripts/fors_security.py`](scripts/fors_security.py): security level against the number of signatures.
