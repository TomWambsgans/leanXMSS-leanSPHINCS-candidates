# scripts

Helper scripts for evaluating SLH-DSA parameter sets. They use only the Python 3 standard
library.

| Script | What it computes |
|---|---|
| [`fors_security.py`](fors_security.py) | Security level against the number of signatures produced with one key (the FORS forgery bound), and the number of signatures each security level allows. Presets: SLH-DSA-*-128-24, 128s, 128f. |
| [`hgwots_security.py`](hgwots_security.py) | Exact reuse security of HG-WOTS: −log2 of the chance a forger can produce a new signature after r uses, per the model in Jonas Nick's tweet. Includes a brute-force self-test. |
| [`param_table.py`](param_table.py) | For d = 1 parameter sets over a range of h and a (k chosen as the smallest that keeps full security for 2^24 signatures): signature size, signature limit, keygen cost, signing cost with a keygen-time cache, the same two costs when pruned to 2^16 signatures, and verification cost. Counted in SHA-256 compressions. |

```sh
python3 scripts/fors_security.py                   # SLH-DSA-*-128-24 around its 2^24 limit
python3 scripts/fors_security.py --h 23            # override any of n, h, a, k
python3 scripts/fors_security.py --sigs 24 25 --levels 128 112
python3 scripts/fors_security.py --preset 128s     # FIPS 205 baseline
python3 scripts/fors_security.py --selftest        # check against published slh-dsa-rls numbers
python3 scripts/param_table.py                     # h = 18..26, 16 KiB cache, sig <= 5 KiB, pruned to 2^16
python3 scripts/param_table.py --all --h 22 --a 12 --cache-kib 64
```
