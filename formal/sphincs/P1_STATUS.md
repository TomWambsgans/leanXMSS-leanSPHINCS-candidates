# P1 status (CoverBound and FORS certificates)

## Builds (checked on h1, `/root/fors-p1`)
- `Moments`, `FirstMoment`, `SecondMoment`, `IndexFactor`, `MarkAverage`: unchanged, green.
  `coverR t X` (`t ∈ X`), `Ψ1R_eq : Ψ1R n = 1 - (1 - 1/A)^n`,
  `Ψ2R_eq : Ψ2R n = 1 - 2(1-1/A)^n + ((1-1/A)^n + (A-1)(1-2/A)^n)/A`, `A = leavesR = 2^forsHeight`.
- `MomentBounds` (rewritten): `cdiv`, `le_cdiv`, `div_le_cdiv_div`, `cdivZ`, `le_cdivZ`,
  `le_cdivZ_div`, `div_le_cdivZ_div` (moved here from `Certificates/Build.lean`),
  `getD_map_range`, `list_sum_range`; the closed forms as exact fractions
  (`Ψ1R_frac`, `Ψ2R_frac`) and their numerators over `2^128`:
  `p1N a n = cdiv (2^128 ((2^a)^n - (2^a-1)^n)) ((2^a)^n)` in `ℕ`,
  `z2N a n = A^(n+1) - 2A(A-1)^n + (A-1)^n + (A-1)(A-2)^n` and
  `p2N a n = (cdivZ (2^128 z2N) (A^(n+1))).toNat` in `ℤ`; `P1Q a n`, `P2Q a n`,
  `Ψ1R_le n`, `Ψ2R_le n` (no `n ≤ 150` needed). No codeword machinery, no `rup`.
- `MomentTable` (rewritten): `P1L a`, `P2L a` (`(List.range 151).map (p1N a)`, computed by the
  kernel, **no literal table**), `P1tab a`, `P2tab a`, `P1L_eq a`, `P2L_eq a`, `length_P1L a`,
  `length_P2L a`, `getD_P1tab`, `getD_P2tab`, `Ψ1R_le_tab`, `Ψ2R_le_tab`.
- `HTermCertificate`: unchanged except one added import (`LeanFors.Base.SplitCert`, which used to
  come through the old `MomentBounds`).
- `HTermOption`: `gBound H k a o n`, `hBound H k a o n`, `checkOptF H b k a t o`,
  `avgN_gS_le`/`avgN_hS_le`/`hTermO_le_optF` take `(hk : forsTrees = k) (ha : forsHeight = a)`
  after `hH hb` and `subst` them. Exponents `8 → forsTrees`, tables `P1tab a`, `P2tab a`.
- `NearMomentTable`: emptied (FORS has no half-cover moment). **It can be deleted together with its
  import in `LeanFors.lean` (the lead's file); nothing imports it any more.**
- `PerIndex`, `NearMoment`: unchanged (already FORS), green against a **scratch stub** of
  `CoverPotential/Basic` (`ForestPotential.excess`), since the real one does not build yet.

- `Certificates/Build.lean` (ported): `checkOptB H b k a`, `checkCoverW_of`/`checkCoverH_of`(`_pt`)
  with `{H b k a K N qstart}`, `gZ H k a n1 c1`, `hZ H k a n1 θ A2 E`, `nZ H k a n1`,
  `buildOpt H b k a t c1 θ s cthr`, `buildOptN H b k a t`, `checkOptF_build`, `checkOptB_build`,
  `checkOptN_build`, `tab_pow`. The shifts are multiplications, not subtractions: the numerators are
  `cdivZ (x^k * 2^191) (2^(H + 128 k))` (and `2^(2H + 128 k)`, `2^(H + 128 (k-1))`), so no
  `191 ≤ H + 128 k` side condition is needed. `cdivZ` and its bounds moved to `MomentBounds`;
  `length_P1L`/`length_P2L` moved to `MomentTable`; `PHL` is gone.
  Green against scratch copies of `LargeBudget/Covers`, `Certificates/Closing` and `NearOption`
  holding exactly the checker definitions of the real files.
- `NearOption`: its arithmetic half (`nBound`, `OptN`, `checkOptN`, `checkOptN_parts`,
  `SepGood.one`, `avgN_near_le`) is green as a scratch module. The half that needs
  `SmallBudget/Contact/NearWitness` and `LargeBudget/Covers` (`hTermO_near_le`, `hNearOf`,
  `hNearOf_le`) has never been elaborated: those two imports do not build yet.

## Not verified against the real tree yet
- `NearOption`: blocked by its import of `LargeBudget/Covers` (→ `LargeBudget/Route` →
  `WeightedPotential`, and `CoverPotential/StartValue`, 7 errors, not mine). Its arithmetic half
  (`nBound`, `OptN`, `checkOptN`, `checkOptN_parts`, `SepGood.one`, `avgN_near_le`) is green as a
  scratch module; the rest (`hTermO_near_le`, `hNearOf`, `hNearOf_le`) is the forest's text with
  `k a` threaded and has only been read.
- `Certificates/{Build, H22, H24, H26, H28}` and `Lifetimes.lean`: green against scratch copies of
  `LargeBudget/Covers`, `Certificates/Closing` (including `ForestPotential.checkSmallF`, copied from
  5983874) and `NearOption` that hold exactly the checker definitions of the real files. Kernel
  times with `decide +kernel`: H22 83 s, H24 105 s, H26 116 s, H28 116 s (the forest's are 30–50 s;
  the entries are raised to the power `k = 25` or `26` instead of 8).

## The proved lifetimes (`maxn`, then rounded down to four significant digits)

| h | full | b=20 | b=14 | b=13 | b=12 | b=10 | b=8 | layered |
|---|------|------|------|------|------|------|-----|---------|
| 22 | 86,910,000 | 23,050,000 | 499,600 | 256,100 | 131,200 | 34,420 | 9,041 | 86,910,000 |
| 24 | 354,200,000 | 29,540,000 | 537,700 | 275,500 | 141,100 | 37,030 | 9,710 | 354,200,000 |
| 26 | 1,426,000,000 | 31,810,000 | 579,400 | 296,700 | 151,900 | 39,850 | 10,430 | 1,426,000,000 |
| 28 | 5,707,000,000 | 34,270,000 | 622,600 | 319,000 | 163,300 | 42,750 | 11,190 | 5,707,000,000 |

as a share of the FORS cover attack: 95.9 / 94.4 / 90.3 / 89.4 / 88.6 / 86.9 / 85.3 % at h = 22,
rising to 98.4 / 96.7 / 91.9 / 91.1 / 90.2 / 88.5 / 86.7 % at h = 28. The splits `lx` are in
`PARAMS`/`LAYERED`. Every one of the 32 passes `check`.

## Interfaces this package assumes from others
- `checkSmallF (H b a N qh : ℕ) (ρ cthr B c : ℚ)` — confirmed (5983874).
- `checkCoverW (H b k a K N qstart)`, `checkCoverH` likewise, `checkCoversH (H b k a K N)` —
  the `k a` go right after `b`.
- `det_bitsFH … H b k a K N … hH hb hk ha hK hN qh …`.

## Build practice
`scratchpad/fb.sh h1 /root/fors-p1 12 <targets>`; `scratchpad/sb.sh` is the same with the scratch
`CoverPotential/{Basic,FairCoin}` stubs overlaid (never committed) for `PerIndex`, `NearMoment`,
`HTerm*`.
