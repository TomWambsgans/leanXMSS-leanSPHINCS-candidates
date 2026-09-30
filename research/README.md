# Design-space study: few-time schemes, tree shape and grinding (n = 16, 128-bit)

Date: 2026-09-30. Question: what's the best stateless hash-based signature for leansphincs under these
constraints?

- 128-bit security for at least 2^24 signatures per key.
- Keygen of about 1B SHA-256 compressions.
- Signing of at most 10M compressions, using a 16 KiB cache built at keygen.
- Signatures of at most 5 KiB.
- A pruned 2^16-signature mode with much faster keygen and signing.
- Verification cost reported, because it matters for zk.

The study also asks whether FORS should be replaced (PORS+FP, HG-WOTS) and how grinding can buy lifetime.

## TL;DR

1. **Within the current d = 1 architecture: WOTS+C + PORS+FP instead of WOTS+ (w = 4) + FORS.** Design B:
   - 3,700 B instead of 4,576 B (−19%), for 2^24.3 signatures.
   - Keygen (1.1B), signing (1.4M), verification (465) and the pruned mode (3.4M / 375K) stay the same.
   - Cost: both are verifier changes, so this is no longer SLH-DSA-compatible.
2. **A two-layer tree (d = 2) removes the 1B keygen entirely.** Design C:
   - 3,560 B, keygen 4.3M, signing 5.2M, pruned 219K / 1.1M.
   - Verification rises to about 670 compressions (+50%).
3. **Grinding buys lifetime only in tall trees.** Each doubling of lifetime costs about 11 bits of grinding at d = 1, but about 3 bits at d ≥ 3. Design E (d = 3):
   - 2^25.5 without grinding, 2^30.4 with a 16-bit digest condition (+0.46M signing), 3.7 KB.
   - Verification is about 900.
4. **HG-WOTS (drop FORS) gives the smallest signatures, 3.2 KB (design F), but isn't ready.**
   - It needs 4 layers plus a 16-bit digest condition just to reach 2^24.
   - Verification is about 1,200, and its security model is unproven.
   - It does survive a second use much better than WOTS+C: 82 bits at 896 B, against about 16 bits for WOTS+C at 3 uses.
5. **In pruned mode, verifier-enforced grinding multiplies with the pruning grinding.**
   - This affects PORS+FP forced pruning, FORS+C and digest conditions.
   - Keep such budgets at 2^4–2^8, or make the grinding level a per-key parameter.

## Model

- **Costs** are SHA-256 compressions in the FIPS 205 SHA2 layout with a precomputed PK.seed midstate:
  - PRF, F and H cost 1; T_l costs ⌈(22 + 16l + 9)/64⌉.
  - A grinding attempt (PRF_msg + H_msg) costs 7; the verifier's H_msg costs 4.
- **Cache:** the 16 KiB cache stores the one top-tree level that fits (1,024 nodes). Each signature rebuilds the 2^(h′−10) top leaves under its cached node, plus every lower layer in full. The pruned mode keeps 2^(h−P) real bottom instances, where P = log2(lifetime) − 16, split evenly over the layers.
- **Security** uses the generic-attack estimate of SPHINCS+ and Kudinov–Nick: the sum over r of Pois(q/2^h, r) × P_forge(r) × 2^−g must be at most 2^−128, with g = digest-condition bits. P_forge(r) per scheme:
  - FORS: (1 − (1 − 2^−a)^r)^k.
  - FORS+C: the same with k − 1 trees, times 2^−a.
  - PORS+FP: C(min(rk, t), k)/C(t, k), which conservatively ignores the forced-pruning filter.
  - HG-WOTS: the exact cover(r) below.
- **One-time signatures in the tree layers:**
  - WOTS+ with w = 4 (1,088 B, worst-case verify 222).
  - WOTS+ with w = 16 (560 B, 535).
  - WOTS+C with w = 16, l = 32, S = 240 (516 B including the counter, deterministic verify 250, about 66 grinding attempts per layer).
- **Validation:** the model reproduces SLH-DSA-128s (7,856 B), the d = 1 figures from `scripts/param_table.py`, and the Kudinov–Nick sizes. For the last, the paper's printed sizes are 16 B larger; see the Kudinov–Nick section.

## Results

Reproduce with `python3 research/design_model.py` (stdlib only, under a second):

| | Design | Size | Lifetime | Keygen | Sign | Verify | Pruned keygen | Pruned sign |
|---|---|---|---|---|---|---|---|---|
| A | d=1 h=22, WOTS+ w=4, FORS a=12 k=15 (current) | 4,576 | 2^24.66 | 1.22B | 1.38M | 448 | 3.03M | 191K |
| **B** | d=1 h=21, WOTS+C, PORS+FP a=13 k=14 (FP 2^4) | **3,700** | 2^24.32 | 1.1B | 1.41M | 465 | 3.44M | 375K |
| **C** | d=2 h=26, WOTS+C, PORS+FP a=15 k=9 (FP 2^4) | **3,560** | 2^24.58 | **4.28M** | 5.17M | 669 | 219K | 1.13M |
| D | d=2 h=26, WOTS+ w=16, FORS a=13 k=11 (standard parts) | 4,016 | 2^25.10 | 4.69M | 4.96M | 1,258 | 200K | 475K |
| E | d=3 h=33, WOTS+C, PORS+FP a=10 k=12 (FP 2^14) | 3,692 | 2^25.45 | 1.07M | 2.25M | 898 | 121K | 50.9M |
| F | d=4 h=44, WOTS+C, HG-WOTS 896 B, no FORS | 3,164 | 2^19.97 | 1.07M | 5.84M | 1,179 | – | – |

Notes on the table:
- **Design F** reaches 2^25.4 with g = 16: signing 6.3M, pruned signing 302M.
- **Design E** has the same problem in pruned mode because of its 2^14 forced-pruning budget. With a 2^8 budget it is 3,820 B and pruned signing is 1.31M. With 2^4 it is 3,932 B and pruned signing is 346K.

Lifetime with a verifier-enforced g-bit digest condition (log2 signatures at 128 bits):

| | g = 0 | g = 8 | g = 16 | g = 24 | Grinding bits per doubling |
|---|---|---|---|---|---|
| A (d=1) | 24.66 | 25.43 | 26.13 | 26.79 | 10.9 |
| B (d=1) | 24.32 | 25.05 | 25.74 | 26.40 | 11.2 |
| C (d=2) | 24.58 | 26.37 | 27.80 | 29.01 | 5.0 |
| E (d=3) | 25.45 | 28.26 | 30.43 | 32.15 | 3.2 |
| F (d=4, HG) | 19.97 | 22.69 | 25.36 | 28.01 | 3.0 |

Why: near the limit, forgery probability grows like λ^D, where λ is the average number of signatures per few-time instance.
- **Single tree (d = 1):** λ ≈ 6 and D ≈ number of FORS trees.
- **Tall trees:** λ ≪ 1, and D is the small number of reuses a forgery needs.

### HG-WOTS reuse security (`scripts/hgwots_security.py`)

The exact calculator follows the model in the tweet. It matches brute-force enumeration on 14 small cases and Monte Carlo on larger ones. Security after r uses = encoding grinding + cov(r):

| Signature | Best parameters found (k, s, j, w, w2) | Encoding grinding | r=2 | r=3 | r=4 | r=5 | r=6 |
|---|---|---|---|---|---|---|---|
| 640 B | 22, 3, 13, 16, 4 | 18.2 | 58.4 (+18.2) | 38.2 | 28.3 | 22.3 | 18.3 |
| 768 B | 26, 3, 15, 8, 4 | 17.1 | 59.3 (+17.1) | 40.0 | 29.6 | 23.2 | 18.8 |
| 896 B | 26, 4, 16, 16, 4 | 0 | 82.1 | 53.5 | 40.6 | 32.7 | 27.3 |
| 1,024 B | 28, 4, 16, 16, 4 | 0 | 93.0 | 59.5 | 44.7 | 35.7 | 29.5 |

- **Tweet's claim roughly confirmed:** about 76–80 bits at 2 uses for about 770–900 B.
- **Baseline:** SHRINCS-style WOTS+C (l = 32, w = 16, 516 B) gives about 16 bits at 3 uses and 11 at 4 uses (Monte Carlo). At 2 uses the exact value isn't computed; 10^7 samples only show it is at least about 22 bits.
- **The catch:** security falls to about 50 bits at 3 uses. So HG-WOTS needs about 2^44 bottom leaves for 2^24 signatures even with a 16-bit digest condition, and that tall tree costs 3–4 WOTS+C layers of 516 B each.

### Kudinov–Nick model (ePrint 2025/2203): points to know

These come from a full port that reproduces all 30 rows of their tables and 55/55 repo regression checks.

- **Accounting:** the tables use an older non-FIPS "uncached" accounting (a Merkle node costs 2 compressions) and a 32-byte R. Every printed size is therefore 16 B larger than FIPS 205 would give.
- **Hidden margins:** security is reported as max(2^−128, forgery), which hides the margins. Under the original SPHINCS+ sum rule, the k = 8, a = 16 rows are 127.1 bits.
- **PORS+FP verification** is undercounted by k − 1 node hashes, which is 7–10 hashes.
- **Message hash** is priced at 2 + 2 compressions, which flatters grinding-heavy variants by about 1.75x against FIPS 205.
- **Signing** rebuilds the top tree on every signature; there is no cache.

## Recommendation

- **Keep d = 1 and cheap verification:** move to design B (WOTS+C + PORS+FP). It is a clear win, 876 B smaller at equal cost. The remaining question is whether the verifier may deviate from FIPS 205.
- **Keygen matters more than verification:** design C (d = 2) gets keygen and the cache down to a few million compressions and a few KiB, and its pruned mode is cheap.
- **Lifetime well beyond 2^24:** design E (d = 3) with a digest condition is the efficient way; 2^30 costs about 0.5M extra signing. For a usable pruned mode, keep the forced-pruning budget at about 2^4.
- **HG-WOTS:** worth watching, but not a candidate until it has a proof and better security at 3+ uses.

## Caveats

- **Generic-attack estimates only.** No QROM loss is included; Kudinov–Nick estimate about 10 bits.
- **HG-WOTS model:** it is the tweet's forward-hashing model, not a proof.
- **PORS+FP:** the security formula ignores the forced-pruning filter, which is conservative. H_msg must output about 260 bits (k distinct indices plus the leaf index).
- **Verification counts:** WOTS+ uses the worst case. WOTS+C and PORS+FP are deterministic because their signatures are padded.
- **Standards:** WOTS+C, PORS+FP, FORS+C and digest conditions all change the verifier, so none of this is FIPS 205.
