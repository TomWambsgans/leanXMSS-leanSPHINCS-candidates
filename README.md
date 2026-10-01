# leanSphincs candidate

A SPHINCS+ variant with the shape of SLH-DSA-128-24 (one Merkle tree over WOTS+C keys, FORS signing the
message), for 2^30 signatures per key at NIST level 1: 127 bits of classical security in the random-oracle
model (proof in Lean 4 to come):

- public key 32 bytes, signature 5,684 bytes;
- verification in 391 compressions, the same for every signature;
- key generation 18.4G compressions, or 1.12M for a pruned key signing 2^16 messages;
- signing in about 421K compressions with a 1 MiB cache, or about 142K for a pruned key with a 16 KiB cache.
- threshold signing, e.g. 3-of-4 with malicious security against 1 operator and a DKG: MPC for the XMSS
  at key generation and for each FORS instance in advance; online signing needs no MPC, only grinding the
  randomizer onto a precomputed instance. Shares can be refreshed without changing the public key. The
  verifier is unchanged.

Costs count 64-byte compression-function calls, as for BLAKE2s.

- [`leansphincs.tex`](leansphincs.tex): a short informal note describing the scheme. CI publishes the
  [latest PDF](https://github.com/TomWambsgans/leansphincs-candidate/releases/download/doc-latest/leansphincs.pdf)
  on every push to `main`; build it locally with `latexmk leansphincs.tex` (output in `.build/`).
- [`scripts/scheme.py`](scripts/scheme.py): sizes, costs and lifetime (the numbers in the note).
- [`scripts/fors_security.py`](scripts/fors_security.py): security level against the number of signatures.
- [`scripts/blake2s_circuit.py`](scripts/blake2s_circuit.py): AND gates and AND-depth (MPC rounds) of BLAKE2s.
