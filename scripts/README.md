# scripts

Helper scripts for evaluating SLH-DSA parameter sets. They use only the Python 3 standard
library.

| Script | What it computes |
|---|---|
| [`fors_security.py`](fors_security.py) | Security level against the number of signatures produced with one key (the FORS forgery bound), and the number of signatures each security level allows. Presets: SLH-DSA-*-128-24, 128s, 128f. |

```sh
python3 scripts/fors_security.py                   # SLH-DSA-*-128-24 around its 2^24 limit
python3 scripts/fors_security.py --h 23            # override any of n, h, a, k
python3 scripts/fors_security.py --sigs 24 25 --levels 128 112
python3 scripts/fors_security.py --preset 128s     # FIPS 205 baseline
python3 scripts/fors_security.py --selftest        # check against published slh-dsa-rls numbers
```
