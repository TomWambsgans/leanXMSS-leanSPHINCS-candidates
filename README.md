# leansphincs-candidate

**SLH-DSA-SHA2-128-24** and **SLH-DSA-SHAKE-128-24** are the NIST category 1 parameter sets of
[NIST SP 800-230 ipd](https://csrc.nist.gov/pubs/sp/800/230/ipd), *Additional SLH-DSA Parameter
Sets for Limited-Signature Use Cases* (Dang, Moody). They run the FIPS 205 SLH-DSA algorithms
unchanged, with new parameters and a limit of **2^24 signatures per key**. The document is an
initial public draft from April 2026, so the parameters may still change.

## Parameters (SP 800-230, Table 1)

| n | h | d | h′ | a | k | lg_w | m | pk | sk¹ | sig |
|---|---|---|---|---|---|---|---|---|---|---|
| 16 | 22 | 1 | 22 | 24 | 6 | 2 | 21 | 32 | 64 | 3,856 |

¹ The secret key size is not in the table; it is 4n, as in FIPS 205.

- The SHA2 variant uses SHA-256 for every function (FIPS 205 §11.2.1). The SHAKE variant uses
  SHAKE256 (FIPS 205 §11.1).
- Compared with SLH-DSA-128s: w = 4 instead of 16, a single XMSS tree (d = 1) instead of 7
  layers, and 6 FORS trees of height 24 instead of 14 of height 12.

## Requirements (SP 800-230, §3)

- A signing key must never produce more than 2^24 signatures; the security of these sets depends
  entirely on that.
- Each key's environment has to be evaluated before use: the number of devices sharing the key,
  signing speed, signing frequency and key lifetime. If the limit cannot be guaranteed, these
  sets must not be used.
- These sets are not approved for general-purpose use. They target sign-once, verify-many cases
  such as software, firmware and certificates.
- Caching part or all of the hypertree to speed up signing is allowed and does not affect
  security.

## Implementation notes (derived from FIPS 205)

- WOTS+ uses len1 = 64, len2 = 4 and len = 68, with 2-bit digits. The checksum shift is 0 and
  the checksum takes 1 byte.
- Signature layout: R (16) ‖ FORS (6·25·16 = 2,400) ‖ WOTS+ (68·16 = 1,088) ‖ auth path
  (22·16 = 352), for 3,856 bytes.
- The 21-byte digest splits into md (18 bytes, 144 bits used), idx_tree (0 bytes) and idx_leaf
  (3 bytes, reduced mod 2^22).
- Because d = 1, idx_tree and the layer and tree addresses are always 0, and the hypertree loops
  over layers 1…d−1 never run.
- The largest FORS tree index is 6·2^24 − 1, which is below 2^32, so it still fits in ADRS.

## Cost vs SLH-DSA-128s (hash calls, derived)

| | 128-24 | 128s |
|---|---|---|
| Signature bytes | 3,856 | 7,856 |
| Verify (upper bound) | 379 | 3,929 |
| Key generation | 1.1·10^9 | 2.9·10^5 |
| Sign | 1.5·10^9, or 3.0·10^8 with the whole tree cached (128 MiB) | 2.2·10^6 |

[`scripts/`](scripts/) computes security level against the number of signatures.

## References

- FIPS 205: https://doi.org/10.6028/NIST.FIPS.205
- SP 800-230 ipd: https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-230.ipd.pdf
- slh-dsa-rls, the parameter search tool the draft cites: https://github.com/chrisfenner/slh-dsa-rls
