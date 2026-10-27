# P1 status (CoverBound and FORS certificates), WIP

## Builds (checked on h2)
- `LeanFors.CoverBound.Moments`: real averages plus one FORS tree: `coverR t X` (`t ∈ X`), `missR`, `coverR_eq`
  (`1 - Π_{x∈X} [x ≠ t]`), `leavesR = 2^forsHeight`, `avgR_missR`, `avgR_missR_mul`, `avgNR_add/const/avgR`.
- `FirstMoment`: `Ψ1R n := avgNR (avg_t coverR t ·) n 0`, `Ψ1R_eq : Ψ1R n = 1 - (1 - 1/A)^n`.
- `SecondMoment`: `Ψ2R n`, `Ψ2R_eq : Ψ2R n = 1 - 2(1-1/A)^n + ((1-1/A)^n + (A-1)(1-2/A)^n)/A`.
- `PerIndex` (FORS rewrite) and `NearMoment` (FORS) built against a scratch stub of `ForestPotential.excess`
  (their real import `LeanFors.CoverPotential.Basic` does not build yet: Classification/ScanSigner upstream).
- Deleted (forest codeword machinery): CodewordMax, CodewordSums, CodewordTables, Grid, GridTensor.
  **`LeanFors.lean` (not P1's) must drop these 5 imports.** UniformMark was never in LeanFors.

## Not done yet
- `MomentBounds`, `MomentTable`: still the forest's (codeword) content. Plan: kernel-computed numerators over 2^128,
  `p1N a n := cdiv (2^128 * ((2^a)^n - (2^a-1)^n)) ((2^a)^n)` (ℕ) and
  `p2N a n := (cdivZ (2^128 * z2) ((2^a)^(n+1))).toNat`, `z2 = A^(n+1) - 2A(A-1)^n + (A-1)^n + (A-1)(A-2)^n` (ℤ);
  `P1L a := (List.range 151).map (p1N a)`, `P1tab a := (P1L a).map (· / 2^128)`, same for P2;
  `Ψ1R_le_tab (n ≤ 150) : Ψ1R n ≤ (P1tab forsHeight).getD n 0`, same for Ψ2. No literal tables.
  (Build.lean defines `cdivZ`; move it to MomentBounds when Build is ported.)
- `HTermCertificate`: generic; only its import of MomentBounds needs checking. `HTerm`: should build unchanged.
- `HTermOption`: k and a added (below); exponents 8 → k; `κE_toReal` unchanged.
- `NearMomentTable`: no FORS half-cover moment; reduce to nothing (or delete; then LeanFors.lean drops it)
  and make `NearOption` import `MomentTable`.
- `NearOption`: `nBound H k a n := k * κQ H * (P1tab a).getD n 0 ^ (k - 1)`, cap `k * κQ H`, per `avgN_yN`, `yN_le`.
- `scripts/fors_certificates.py` (not started): copy of forest_certificates.py with P1/P2 from the closed forms
  (exact Fractions), `gBound = min(KQ P1^k, KQ^2 P2^k/(4 c1))`, `nBound = k KQ P1^(k-1)`, the 28 configurations
  (h ∈ 22..28 × full, b ∈ 20,14,13,12,10,8, layered), k from scheme.py `fors(h, shape, b)`, a = 10; LIT (reveal
  rate) must be the FORS one from P2's RevealRate; maxn search, N rounded down to 4 significant digits.
- `Certificates/{Build,H22..H28}.lean`: port after the script (Build's zipTab uses `P1L a`, `^ k`).

## API settled (agreed with lead and P2)
- `checkOptF H b k a t o`, `gBound H k a o n`, `hBound H k a o n`,
  `hTermO_le_optF (hH : totalHeight = H) (hb : subtreeHeight = b) (hk : forsTrees = k) (ha : forsHeight = a) t o ht ho ...`
  (rest as in the forest). `PoisT`, `checkPT`, `checkRate`, `OptF`, `OptN` unchanged.
- `checkOptN H k a t o`, `hNearOf q`, `hNearOf_le H b k a N qtop hH hb hk ha hN t o hr ht ho q hq`.
- PerIndex: `CoverF (t : FLeaf) (Xs : Multiset FLeaf) : Prop := t ∈ Xs`;
  `φF Xs := freshAvg univ fun t : FLeaf => if CoverF t Xs then 1 else 0`; `yM Ms := ∏ κ, φF (Ms.map (· κ))`;
  `mem_marks_map`, `coverAll_iff`, `price_decomp`, `avgN_φF`, `avgN_yM : … = ofReal (Ψ1R n) ^ forsTrees`, `card_ftree`.
- NearMoment: `nearFactor κ κ' Xs := freshAvg univ fun t : FLeaf => if κ' = κ ∨ CoverF t Xs then 1 else 0`
  (P2 relies on this exact body), `nearFactor_self`, `nearFactor_of_ne`,
  `yN Ms := ∑ κ, ∏ κ', nearFactor κ κ' (Ms.map (· κ'))` — **no min**, so P2's `priceNear_decomp` is an equality;
  `avgN_yN n : avgN yN n 0 = ∑ _κ : FTree, ofReal (Ψ1R n) ^ (forsTrees - 1)`, `yN_le : yN Ms ≤ forsTrees`.

## Build practice
Build only own targets with the scratchpad `lbh.sh`; to test PerIndex/NearMoment before Basic builds, use a scratch
copy with `ForestPotential.excess` stubbed (never commit it).
