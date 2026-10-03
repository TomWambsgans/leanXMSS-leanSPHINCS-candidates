# Working plan (temporary; delete before the final commit)

Target: `HasClassicalSecurityBits 127` (forge ≤ q/2^127 for every q ≥ 1) for each (b, N):
(26, 1.2e9), (20, 2.37e7), (14, 4.6e5), (13, 2.4e5), (12, 1.25e5), (10, 33000); plus correctness and
completeness. Units: 1 unit = 2^-128 per query; x = q/2^128; the target is 2x.

## Facts established numerically (scratchpad scripts ana/*.py)

- FORS coverage per digest query F(D) = 2^102 Σ_idx Π_κ |R_{idx,κ}|/1024 (units), D = signer landing digests.
  E F = Σ_r P(r) c(r)^24 · 2^128 · 2^-26 · 2^b, c(r) = 1-(1-2^-10)^r, r ~ Bin(N, 2^-b):
  b=26: 1.9118 (sd 0.045), b=20: 1.857, b=14: 1.520, b=13: 1.678, b=12: 1.802, b=10: 1.264.
  P(F > 2): 3% (b=26), 14% (b=20), 10-23% (pruned). E(F-2)^+ (MC): 0.0015, 0.025, 0.11, 0.19, 0.29, 0.20.
  Second-moment bound on E(F-2)^+ for b=26: Var/(4(2-EF)) = 0.0058; bulk/tail split 0.0053.
- leanVM's count price (r/1024)^24 overestimates c(r)^24 by 1.5-2x: must use the exact coverage.
- leanVM's signer overhead 1537/1024 is a bookkeeping artifact: landing digests are iid uniform;
  presample the signer's randomizers and their digests (D) and condition on D.
- Best adaptive attack (attack.py: grind digests, switch to aimed FORS guesses at a completable
  near certificate, 2 units/query) reaches at most 0.955 (b=26), 0.939 (b=20), 0.875 (b=14),
  0.922 (b=13), 0.945 (b=12), 0.79 (b=10) of 2x. No attack beats the claim.

## Route design

Large q (crude): every non-digest query has a deterministic cap of 2 units (S: output hits an honest
label at a non-honest input; G: input equals an undisclosed honest input; per-coordinate G exact via
1-G/N). Split each digest candidate's coverage hazard into min(cov,2) + (cov-2)^+:
P ≤ 1-(1-y)e^{-y-2z} + q·E(F-2)^+/N ≤ 2x - 1.5x² + x·E(F-2)^+. Closes for x ≥ E(F-2)^+/1.5.

Small q (refined), max over query-class allocation, per D:
Ψ(F,x) = max over x_d+x_p+x_e+x_g+x_o ≤ x of
  F x_d + 1.5 x_p (two-edge) + x_e (equal encoding) + x_o (structural) + x_g·min(1, ν x_d)·(≤2)
  + 126 x_p x_e (contact × marker, b1 = 63 per chain) + x_g²/2 (two guesses) + ...
with ν = completable near-certificate rate (missing leaf's sibling disclosed) ≈ 23·F.
E_D Ψ/x ≈ 1.912 (b=26) up to x ≈ 0.015; 1.865 (b=20) up to 0.015.

Middle (pruned keys): potential/MDP over states {no near cert, completable near cert exists}
with per-class hazard caps and saturation, averaged over D. Margin ~5%.

## Lean plan

1. Port scheme: one layer h=26, WOTS+C 64x4 T=120, plain FORS 24x10, two digest calls, our tags,
   pruning via `class Params` (subtreeHeight, signatureLimit). Draft: scratchpad new/Scheme.lean.
2. Decouple Base from RandomizedStatement so scheme edits don't rebuild generic tooling.
3. Port reduction layers (Adversary/Deterministic/Seeded/Scheme), canonical graph, witnesses.
4. New FORS analysis (exact coverage, presampled D), new combination (max-style), closers per instance.

Build: `taskpolicy -c background nice -n 19 lake build` from formal/sphincs (lake has no -j).
