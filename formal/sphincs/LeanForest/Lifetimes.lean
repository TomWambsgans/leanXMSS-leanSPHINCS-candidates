import LeanForest.Certificates.H22
import LeanForest.Certificates.H24
import LeanForest.Certificates.H26
import LeanForest.Certificates.H28

/-! **Proved lifetimes of the forest scheme** for the deterministic signer (seed-derived randomizers):
127 classical bits against any adversary, at every height, shape and kept subtree height. Small
budgets use the linear potential, the one-coin cover potential at baseline `ρ / 2^128` and the
contact bound A4 of the forest; large budgets use the one-coin covers at the survival-weighted
baseline. The proof does not depend on the hash function: `VerificationCost.lean` counts the
compressions of each. -/

open OracleComp OracleSpec ENNReal

namespace LeanForest.Lifetimes

open Security ForestPotential

/-- Height 22, full key, 81,860,000 signatures (91.0% of the cover attack's 8.998e+07). -/
abbrev h22_full : Params := ⟨22, 1, 6, 22, 81860000, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 22, full key, 81,860,000 signatures. -/
theorem h22_full_bits : @Det.HasClassicalSecurityBitsDet h22_full 127 :=
  @det_bitsFH h22_full (by decide) 22 22 947912704 81860000 (by decide) (by decide) (by decide) (by decide) 512487451133699472151040029945233408
    H0.rho_h22_b22 H0.tab_h22_b22 H0.small_h22_b22 H0.near_h22_b22 H0.tab_h22_b22_ok H0.rate_h22_b22_ok H0.small_h22_b22_ok
    H0.near_h22_b22_ok H0.check_h22_b22_ok [H0.cover_h22_b22_0] [] H0.covers_h22_b22_ok

/-- Height 22, kept subtree height 20, 21,760,000 signatures (89.2% of the cover attack's 2.438e+07). -/
abbrev h22_pruned20 : Params := ⟨22, 1, 6, 20, 21760000, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 22, kept subtree height 20, 21,760,000 signatures. -/
theorem h22_pruned20_bits : @Det.HasClassicalSecurityBitsDet h22_pruned20 127 :=
  @det_bitsFH h22_pruned20 (by decide) 22 20 236978180 21760000 (by decide) (by decide) (by decide) (by decide) 664613997892457936451903530140172288
    H0.rho_h22_b20 H0.tab_h22_b20 H0.small_h22_b20 H0.near_h22_b20 H0.tab_h22_b20_ok H0.rate_h22_b20_ok H0.small_h22_b20_ok
    H0.near_h22_b20_ok H0.check_h22_b20_ok [H0.cover_h22_b20_0, H0.cover_h22_b20_1] [H0.coverh_h22_b20_0] H0.covers_h22_b20_ok

/-- Height 22, kept subtree height 14, 405,300 signatures (84.3% of the cover attack's 4.807e+05). -/
abbrev h22_pruned14 : Params := ⟨22, 1, 6, 14, 405300, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 22, kept subtree height 14, 405,300 signatures. -/
theorem h22_pruned14_bits : @Det.HasClassicalSecurityBitsDet h22_pruned14 127 :=
  @det_bitsFH h22_pruned14 (by decide) 22 14 3702800 405300 (by decide) (by decide) (by decide) (by decide) 1329227995784915872903807060280344576
    H0.rho_h22_b14 H0.tab_h22_b14 H0.small_h22_b14 H0.near_h22_b14 H0.tab_h22_b14_ok H0.rate_h22_b14_ok H0.small_h22_b14_ok
    H0.near_h22_b14_ok H0.check_h22_b14_ok [H0.cover_h22_b14_0, H0.cover_h22_b14_1] [H0.coverh_h22_b14_0] H0.covers_h22_b14_ok

/-- Height 22, kept subtree height 13, 208,500 signatures (83.6% of the cover attack's 2.495e+05). -/
abbrev h22_pruned13 : Params := ⟨22, 1, 6, 13, 208500, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 22, kept subtree height 13, 208,500 signatures. -/
theorem h22_pruned13_bits : @Det.HasClassicalSecurityBitsDet h22_pruned13 127 :=
  @det_bitsFH h22_pruned13 (by decide) 22 13 1851410 208500 (by decide) (by decide) (by decide) (by decide) 1449533407878593313898110627080044544
    H0.rho_h22_b13 H0.tab_h22_b13 H0.small_h22_b13 H0.near_h22_b13 H0.tab_h22_b13_ok H0.rate_h22_b13_ok H0.small_h22_b13_ok
    H0.near_h22_b13_ok H0.check_h22_b13_ok [H0.cover_h22_b13_0, H0.cover_h22_b13_1] [H0.coverh_h22_b13_0] H0.covers_h22_b13_ok

/-- Height 22, kept subtree height 12, 107,200 signatures (82.8% of the cover attack's 1.295e+05). -/
abbrev h22_pruned12 : Params := ⟨22, 1, 6, 12, 107200, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 22, kept subtree height 12, 107,200 signatures. -/
theorem h22_pruned12_bits : @Det.HasClassicalSecurityBitsDet h22_pruned12 127 :=
  @det_bitsFH h22_pruned12 (by decide) 22 12 925716 107200 (by decide) (by decide) (by decide) (by decide) 1580727390048228830862881339350188032
    H0.rho_h22_b12 H0.tab_h22_b12 H0.small_h22_b12 H0.near_h22_b12 H0.tab_h22_b12_ok H0.rate_h22_b12_ok H0.small_h22_b12_ok
    H0.near_h22_b12_ok H0.check_h22_b12_ok [H0.cover_h22_b12_0, H0.cover_h22_b12_1] [H0.coverh_h22_b12_0] H0.covers_h22_b12_ok

/-- Height 22, kept subtree height 10, 28,410 signatures (81.5% of the cover attack's 3.484e+04). -/
abbrev h22_pruned10 : Params := ⟨22, 1, 6, 10, 28410, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 22, kept subtree height 10, 28,410 signatures. -/
theorem h22_pruned10_bits : @Det.HasClassicalSecurityBitsDet h22_pruned10 127 :=
  @det_bitsFH h22_pruned10 (by decide) 22 10 231448 28410 (by decide) (by decide) (by decide) (by decide) 1879812259125035374945945504540786688
    H0.rho_h22_b10 H0.tab_h22_b10 H0.small_h22_b10 H0.near_h22_b10 H0.tab_h22_b10_ok H0.rate_h22_b10_ok H0.small_h22_b10_ok
    H0.near_h22_b10_ok H0.check_h22_b10_ok [H0.cover_h22_b10_0, H0.cover_h22_b10_1] [H0.coverh_h22_b10_0] H0.covers_h22_b10_ok

/-- Height 22, kept subtree height 8, 7,514 signatures (80.2% of the cover attack's 9364). -/
abbrev h22_pruned8 : Params := ⟨22, 1, 6, 8, 7514, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 22, kept subtree height 8, 7,514 signatures. -/
theorem h22_pruned8_bits : @Det.HasClassicalSecurityBitsDet h22_pruned8 127 :=
  @det_bitsFH h22_pruned8 (by decide) 22 8 57884 7514 (by decide) (by decide) (by decide) (by decide) 2235486113420830575288774845660135424
    H0.rho_h22_b8 H0.tab_h22_b8 H0.small_h22_b8 H0.near_h22_b8 H0.tab_h22_b8_ok H0.rate_h22_b8_ok H0.small_h22_b8_ok
    H0.near_h22_b8_ok H0.check_h22_b8_ok [H0.cover_h22_b8_0, H0.cover_h22_b8_1] [H0.coverh_h22_b8_0] H0.covers_h22_b8_ok

/-- Height 22, layered (10 + 6 + 6), 81,860,000 signatures (91.0% of the cover attack's 8.998e+07). -/
abbrev h22_layered : Params := ⟨22, 3, 6, 22, 81860000, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 22, layered (10 + 6 + 6), 81,860,000 signatures. -/
theorem h22_layered_bits : @Det.HasClassicalSecurityBitsDet h22_layered 127 :=
  @det_bitsFH h22_layered (by decide) 22 22 231424 81860000 (by decide) (by decide) (by decide) (by decide) 512487451133699472151040029945233408
    H0.rho_h22_b22 H0.tab_h22_b22 H0.small_h22_b22 H0.near_h22_b22 H0.tab_h22_b22_ok H0.rate_h22_b22_ok H0.small_h22_b22_ok
    H0.near_h22_b22_ok H0.check_h22_b22_ok [H0.cover_h22_b22_0] [] H0.covers_h22_L_ok

/-- Height 24, full key, 336,700,000 signatures (93.5% of the cover attack's 3.599e+08). -/
abbrev h24_full : Params := ⟨24, 1, 6, 24, 336700000, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 24, full key, 336,700,000 signatures. -/
theorem h24_full_bits : @Det.HasClassicalSecurityBitsDet h24_full 127 :=
  @det_bitsFH h24_full (by decide) 24 24 3791650816 336700000 (by decide) (by decide) (by decide) (by decide) 332306998946228968225951765070086144
    H0.rho_h24_b24 H0.tab_h24_b24 H0.small_h24_b24 H0.near_h24_b24 H0.tab_h24_b24_ok H0.rate_h24_b24_ok H0.small_h24_b24_ok
    H0.near_h24_b24_ok H0.check_h24_b24_ok [H0.cover_h24_b24_0] [] H0.covers_h24_b24_ok

/-- Height 24, kept subtree height 20, 23,830,000 signatures (90.3% of the cover attack's 2.639e+07). -/
abbrev h24_pruned20 : Params := ⟨24, 1, 6, 20, 23830000, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 24, kept subtree height 20, 23,830,000 signatures. -/
theorem h24_pruned20_bits : @Det.HasClassicalSecurityBitsDet h24_pruned20 127 :=
  @det_bitsFH h24_pruned20 (by decide) 24 20 236978184 23830000 (by decide) (by decide) (by decide) (by decide) 609453723237804761606486446491828224
    H0.rho_h24_b20 H0.tab_h24_b20 H0.small_h24_b20 H0.near_h24_b20 H0.tab_h24_b20_ok H0.rate_h24_b20_ok H0.small_h24_b20_ok
    H0.near_h24_b20_ok H0.check_h24_b20_ok [H0.cover_h24_b20_0, H0.cover_h24_b20_1] [H0.coverh_h24_b20_0] H0.covers_h24_b20_ok

/-- Height 24, kept subtree height 14, 441,500 signatures (85.2% of the cover attack's 5.18e+05). -/
abbrev h24_pruned14 : Params := ⟨24, 1, 6, 14, 441500, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 24, kept subtree height 14, 441,500 signatures. -/
theorem h24_pruned14_bits : @Det.HasClassicalSecurityBitsDet h24_pruned14 127 :=
  @det_bitsFH h24_pruned14 (by decide) 24 14 3702804 441500 (by decide) (by decide) (by decide) (by decide) 1218907446475609523212972892983656448
    H0.rho_h24_b14 H0.tab_h24_b14 H0.small_h24_b14 H0.near_h24_b14 H0.tab_h24_b14_ok H0.rate_h24_b14_ok H0.small_h24_b14_ok
    H0.near_h24_b14_ok H0.check_h24_b14_ok [H0.cover_h24_b14_0, H0.cover_h24_b14_1] [H0.coverh_h24_b14_0] H0.covers_h24_b14_ok

/-- Height 24, kept subtree height 13, 226,800 signatures (84.4% of the cover attack's 2.687e+05). -/
abbrev h24_pruned13 : Params := ⟨24, 1, 6, 13, 226800, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 24, kept subtree height 13, 226,800 signatures. -/
theorem h24_pruned13_bits : @Det.HasClassicalSecurityBitsDet h24_pruned13 127 :=
  @det_bitsFH h24_pruned13 (by decide) 24 13 1851414 226800 (by decide) (by decide) (by decide) (by decide) 1329227995784915872903807060280344576
    H0.rho_h24_b13 H0.tab_h24_b13 H0.small_h24_b13 H0.near_h24_b13 H0.tab_h24_b13_ok H0.rate_h24_b13_ok H0.small_h24_b13_ok
    H0.near_h24_b13_ok H0.check_h24_b13_ok [H0.cover_h24_b13_0, H0.cover_h24_b13_1] [H0.coverh_h24_b13_0] H0.covers_h24_b13_ok

/-- Height 24, kept subtree height 12, 116,600 signatures (83.7% of the cover attack's 1.394e+05). -/
abbrev h24_pruned12 : Params := ⟨24, 1, 6, 12, 116600, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 24, kept subtree height 12, 116,600 signatures. -/
theorem h24_pruned12_bits : @Det.HasClassicalSecurityBitsDet h24_pruned12 127 :=
  @det_bitsFH h24_pruned12 (by decide) 24 12 925720 116600 (by decide) (by decide) (by decide) (by decide) 1580727390048228830862881339350188032
    H0.rho_h24_b12 H0.tab_h24_b12 H0.small_h24_b12 H0.near_h24_b12 H0.tab_h24_b12_ok H0.rate_h24_b12_ok H0.small_h24_b12_ok
    H0.near_h24_b12_ok H0.check_h24_b12_ok [H0.cover_h24_b12_0, H0.cover_h24_b12_1] [H0.coverh_h24_b12_0] H0.covers_h24_b12_ok

/-- Height 24, kept subtree height 10, 30,810 signatures (82.3% of the cover attack's 3.746e+04). -/
abbrev h24_pruned10 : Params := ⟨24, 1, 6, 10, 30810, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 24, kept subtree height 10, 30,810 signatures. -/
theorem h24_pruned10_bits : @Det.HasClassicalSecurityBitsDet h24_pruned10 127 :=
  @det_bitsFH h24_pruned10 (by decide) 24 10 231452 30810 (by decide) (by decide) (by decide) (by decide) 1723795442083364420290692123923054592
    H0.rho_h24_b10 H0.tab_h24_b10 H0.small_h24_b10 H0.near_h24_b10 H0.tab_h24_b10_ok H0.rate_h24_b10_ok H0.small_h24_b10_ok
    H0.near_h24_b10_ok H0.check_h24_b10_ok [H0.cover_h24_b10_0, H0.cover_h24_b10_1] [H0.coverh_h24_b10_0] H0.covers_h24_b10_ok

/-- Height 24, kept subtree height 8, 8,154 signatures (81.1% of the cover attack's 1.005e+04). -/
abbrev h24_pruned8 : Params := ⟨24, 1, 6, 8, 8154, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 24, kept subtree height 8, 8,154 signatures. -/
theorem h24_pruned8_bits : @Det.HasClassicalSecurityBitsDet h24_pruned8 127 :=
  @det_bitsFH h24_pruned8 (by decide) 24 8 57888 8154 (by decide) (by decide) (by decide) (by decide) 2049949804534797888604160119780933632
    H0.rho_h24_b8 H0.tab_h24_b8 H0.small_h24_b8 H0.near_h24_b8 H0.tab_h24_b8_ok H0.rate_h24_b8_ok H0.small_h24_b8_ok
    H0.near_h24_b8_ok H0.check_h24_b8_ok [H0.cover_h24_b8_0, H0.cover_h24_b8_1] [H0.coverh_h24_b8_0] H0.covers_h24_b8_ok

/-- Height 24, layered (12 + 6 + 6), 336,700,000 signatures (93.5% of the cover attack's 3.599e+08). -/
abbrev h24_layered : Params := ⟨24, 3, 6, 24, 336700000, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 24, layered (12 + 6 + 6), 336,700,000 signatures. -/
theorem h24_layered_bits : @Det.HasClassicalSecurityBitsDet h24_layered 127 :=
  @det_bitsFH h24_layered (by decide) 24 24 925696 336700000 (by decide) (by decide) (by decide) (by decide) 332306998946228968225951765070086144
    H0.rho_h24_b24 H0.tab_h24_b24 H0.small_h24_b24 H0.near_h24_b24 H0.tab_h24_b24_ok H0.rate_h24_b24_ok H0.small_h24_b24_ok
    H0.near_h24_b24_ok H0.check_h24_b24_ok [H0.cover_h24_b24_0] [] H0.covers_h24_L_ok

/-- Height 26, full key, 1,381,000,000 signatures (95.9% of the cover attack's 1.44e+09). -/
abbrev h26_full : Params := ⟨26, 1, 6, 26, 1381000000, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 26, full key, 1,381,000,000 signatures. -/
theorem h26_full_bits : @Det.HasClassicalSecurityBitsDet h26_full 127 :=
  @det_bitsFH h26_full (by decide) 26 26 15166603264 1381000000 (by decide) (by decide) (by decide) (by decide) 234976532390629421868243188067598336
    H0.rho_h26_b26 H0.tab_h26_b26 H0.small_h26_b26 H0.near_h26_b26 H0.tab_h26_b26_ok H0.rate_h26_b26_ok H0.small_h26_b26_ok
    H0.near_h26_b26_ok H0.check_h26_b26_ok [H0.cover_h26_b26_0] [] H0.covers_h26_b26_ok

/-- Height 26, kept subtree height 20, 26,030,000 signatures (91.3% of the cover attack's 2.851e+07). -/
abbrev h26_pruned20 : Params := ⟨26, 1, 6, 20, 26030000, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 26, kept subtree height 20, 26,030,000 signatures. -/
theorem h26_pruned20_bits : @Det.HasClassicalSecurityBitsDet h26_pruned20 127 :=
  @det_bitsFH h26_pruned20 (by decide) 26 20 236978188 26030000 (by decide) (by decide) (by decide) (by decide) 558871528355207643822193711415033856
    H0.rho_h26_b20 H0.tab_h26_b20 H0.small_h26_b20 H0.near_h26_b20 H0.tab_h26_b20_ok H0.rate_h26_b20_ok H0.small_h26_b20_ok
    H0.near_h26_b20_ok H0.check_h26_b20_ok [H0.cover_h26_b20_0, H0.cover_h26_b20_1] [H0.coverh_h26_b20_0] H0.covers_h26_b20_ok

/-- Height 26, kept subtree height 14, 480,100 signatures (86.1% of the cover attack's 5.575e+05). -/
abbrev h26_pruned14 : Params := ⟨26, 1, 6, 14, 480100, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 26, kept subtree height 14, 480,100 signatures. -/
theorem h26_pruned14_bits : @Det.HasClassicalSecurityBitsDet h26_pruned14 127 :=
  @det_bitsFH h26_pruned14 (by decide) 26 14 3702808 480100 (by decide) (by decide) (by decide) (by decide) 1117743056710415287644387422830067712
    H0.rho_h26_b14 H0.tab_h26_b14 H0.small_h26_b14 H0.near_h26_b14 H0.tab_h26_b14_ok H0.rate_h26_b14_ok H0.small_h26_b14_ok
    H0.near_h26_b14_ok H0.check_h26_b14_ok [H0.cover_h26_b14_0, H0.cover_h26_b14_1] [H0.coverh_h26_b14_0] H0.covers_h26_b14_ok

/-- Height 26, kept subtree height 13, 246,900 signatures (85.4% of the cover attack's 2.89e+05). -/
abbrev h26_pruned13 : Params := ⟨26, 1, 6, 13, 246900, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 26, kept subtree height 13, 246,900 signatures. -/
theorem h26_pruned13_bits : @Det.HasClassicalSecurityBitsDet h26_pruned13 127 :=
  @det_bitsFH h26_pruned13 (by decide) 26 13 1851418 246900 (by decide) (by decide) (by decide) (by decide) 1329227995784915872903807060280344576
    H0.rho_h26_b13 H0.tab_h26_b13 H0.small_h26_b13 H0.near_h26_b13 H0.tab_h26_b13_ok H0.rate_h26_b13_ok H0.small_h26_b13_ok
    H0.near_h26_b13_ok H0.check_h26_b13_ok [H0.cover_h26_b13_0, H0.cover_h26_b13_1] [H0.coverh_h26_b13_0] H0.covers_h26_b13_ok

/-- Height 26, kept subtree height 12, 126,900 signatures (84.7% of the cover attack's 1.498e+05). -/
abbrev h26_pruned12 : Params := ⟨26, 1, 6, 12, 126900, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 26, kept subtree height 12, 126,900 signatures. -/
theorem h26_pruned12_bits : @Det.HasClassicalSecurityBitsDet h26_pruned12 127 :=
  @det_bitsFH h26_pruned12 (by decide) 26 12 925724 126900 (by decide) (by decide) (by decide) (by decide) 1449533407878593313898110627080044544
    H0.rho_h26_b12 H0.tab_h26_b12 H0.small_h26_b12 H0.near_h26_b12 H0.tab_h26_b12_ok H0.rate_h26_b12_ok H0.small_h26_b12_ok
    H0.near_h26_b12_ok H0.check_h26_b12_ok [H0.cover_h26_b12_0, H0.cover_h26_b12_1] [H0.coverh_h26_b12_0] H0.covers_h26_b12_ok

/-- Height 26, kept subtree height 10, 33,480 signatures (83.2% of the cover attack's 4.022e+04). -/
abbrev h26_pruned10 : Params := ⟨26, 1, 6, 10, 33480, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 26, kept subtree height 10, 33,480 signatures. -/
theorem h26_pruned10_bits : @Det.HasClassicalSecurityBitsDet h26_pruned10 127 :=
  @det_bitsFH h26_pruned10 (by decide) 26 10 231456 33480 (by decide) (by decide) (by decide) (by decide) 1723795442083364420290692123923054592
    H0.rho_h26_b10 H0.tab_h26_b10 H0.small_h26_b10 H0.near_h26_b10 H0.tab_h26_b10_ok H0.rate_h26_b10_ok H0.small_h26_b10_ok
    H0.near_h26_b10_ok H0.check_h26_b10_ok [H0.cover_h26_b10_0, H0.cover_h26_b10_1] [H0.coverh_h26_b10_0] H0.covers_h26_b10_ok

/-- Height 26, kept subtree height 8, 8,830 signatures (81.9% of the cover attack's 1.078e+04). -/
abbrev h26_pruned8 : Params := ⟨26, 1, 6, 8, 8830, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 26, kept subtree height 8, 8,830 signatures. -/
theorem h26_pruned8_bits : @Det.HasClassicalSecurityBitsDet h26_pruned8 127 :=
  @det_bitsFH h26_pruned8 (by decide) 26 8 57892 8830 (by decide) (by decide) (by decide) (by decide) 2049949804534797888604160119780933632
    H0.rho_h26_b8 H0.tab_h26_b8 H0.small_h26_b8 H0.near_h26_b8 H0.tab_h26_b8_ok H0.rate_h26_b8_ok H0.small_h26_b8_ok
    H0.near_h26_b8_ok H0.check_h26_b8_ok [H0.cover_h26_b8_0, H0.cover_h26_b8_1] [H0.coverh_h26_b8_0] H0.covers_h26_b8_ok

/-- Height 26, layered (12 + 7 + 7), 1,381,000,000 signatures (95.9% of the cover attack's 1.44e+09). -/
abbrev h26_layered : Params := ⟨26, 3, 7, 26, 1381000000, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 26, layered (12 + 7 + 7), 1,381,000,000 signatures. -/
theorem h26_layered_bits : @Det.HasClassicalSecurityBitsDet h26_layered 127 :=
  @det_bitsFH h26_layered (by decide) 26 26 925696 1381000000 (by decide) (by decide) (by decide) (by decide) 234976532390629421868243188067598336
    H0.rho_h26_b26 H0.tab_h26_b26 H0.small_h26_b26 H0.near_h26_b26 H0.tab_h26_b26_ok H0.rate_h26_b26_ok H0.small_h26_b26_ok
    H0.near_h26_b26_ok H0.check_h26_b26_ok [H0.cover_h26_b26_0] [] H0.covers_h26_L_ok

/-- Height 28, full key, 5,634,000,000 signatures (97.8% of the cover attack's 5.759e+09). -/
abbrev h28_full : Params := ⟨28, 1, 6, 28, 5634000000, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 28, full key, 5,634,000,000 signatures. -/
theorem h28_full_bits : @Det.HasClassicalSecurityBitsDet h28_full 127 :=
  @det_bitsFH h28_full (by decide) 28 28 60666413056 5634000000 (by decide) (by decide) (by decide) (by decide) 181191675984824164237263828385005568
    H0.rho_h28_b28 H0.tab_h28_b28 H0.small_h28_b28 H0.near_h28_b28 H0.tab_h28_b28_ok H0.rate_h28_b28_ok H0.small_h28_b28_ok
    H0.near_h28_b28_ok H0.check_h28_b28_ok [H0.cover_h28_b28_0] [] H0.covers_h28_b28_ok

/-- Height 28, kept subtree height 20, 28,350,000 signatures (92.1% of the cover attack's 3.077e+07). -/
abbrev h28_pruned20 : Params := ⟨28, 1, 6, 20, 28350000, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 28, kept subtree height 20, 28,350,000 signatures. -/
theorem h28_pruned20_bits : @Det.HasClassicalSecurityBitsDet h28_pruned20 127 :=
  @det_bitsFH h28_pruned20 (by decide) 28 20 236978192 28350000 (by decide) (by decide) (by decide) (by decide) 512487451133699472151040029945233408
    H0.rho_h28_b20 H0.tab_h28_b20 H0.small_h28_b20 H0.near_h28_b20 H0.tab_h28_b20_ok H0.rate_h28_b20_ok H0.small_h28_b20_ok
    H0.near_h28_b20_ok H0.check_h28_b20_ok [H0.cover_h28_b20_0, H0.cover_h28_b20_1] [H0.coverh_h28_b20_0] H0.covers_h28_b20_ok

/-- Height 28, kept subtree height 14, 522,000 signatures (87.1% of the cover attack's 5.993e+05). -/
abbrev h28_pruned14 : Params := ⟨28, 1, 6, 14, 522000, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 28, kept subtree height 14, 522,000 signatures. -/
theorem h28_pruned14_bits : @Det.HasClassicalSecurityBitsDet h28_pruned14 127 :=
  @det_bitsFH h28_pruned14 (by decide) 28 14 3702812 522000 (by decide) (by decide) (by decide) (by decide) 1117743056710415287644387422830067712
    H0.rho_h28_b14 H0.tab_h28_b14 H0.small_h28_b14 H0.near_h28_b14 H0.tab_h28_b14_ok H0.rate_h28_b14_ok H0.small_h28_b14_ok
    H0.near_h28_b14_ok H0.check_h28_b14_ok [H0.cover_h28_b14_0, H0.cover_h28_b14_1] [H0.coverh_h28_b14_0] H0.covers_h28_b14_ok

/-- Height 28, kept subtree height 13, 267,900 signatures (86.3% of the cover attack's 3.105e+05). -/
abbrev h28_pruned13 : Params := ⟨28, 1, 6, 13, 267900, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 28, kept subtree height 13, 267,900 signatures. -/
theorem h28_pruned13_bits : @Det.HasClassicalSecurityBitsDet h28_pruned13 127 :=
  @det_bitsFH h28_pruned13 (by decide) 28 13 1851422 267900 (by decide) (by decide) (by decide) (by decide) 1218907446475609523212972892983656448
    H0.rho_h28_b13 H0.tab_h28_b13 H0.small_h28_b13 H0.near_h28_b13 H0.tab_h28_b13_ok H0.rate_h28_b13_ok H0.small_h28_b13_ok
    H0.near_h28_b13_ok H0.check_h28_b13_ok [H0.cover_h28_b13_0, H0.cover_h28_b13_1] [H0.coverh_h28_b13_0] H0.covers_h28_b13_ok

/-- Height 28, kept subtree height 12, 137,400 signatures (85.4% of the cover attack's 1.609e+05). -/
abbrev h28_pruned12 : Params := ⟨28, 1, 6, 12, 137400, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 28, kept subtree height 12, 137,400 signatures. -/
theorem h28_pruned12_bits : @Det.HasClassicalSecurityBitsDet h28_pruned12 127 :=
  @det_bitsFH h28_pruned12 (by decide) 28 12 925728 137400 (by decide) (by decide) (by decide) (by decide) 1329227995784915872903807060280344576
    H0.rho_h28_b12 H0.tab_h28_b12 H0.small_h28_b12 H0.near_h28_b12 H0.tab_h28_b12_ok H0.rate_h28_b12_ok H0.small_h28_b12_ok
    H0.near_h28_b12_ok H0.check_h28_b12_ok [H0.cover_h28_b12_0, H0.cover_h28_b12_1] [H0.coverh_h28_b12_0] H0.covers_h28_b12_ok

/-- Height 28, kept subtree height 10, 36,190 signatures (83.9% of the cover attack's 4.314e+04). -/
abbrev h28_pruned10 : Params := ⟨28, 1, 6, 10, 36190, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 28, kept subtree height 10, 36,190 signatures. -/
theorem h28_pruned10_bits : @Det.HasClassicalSecurityBitsDet h28_pruned10 127 :=
  @det_bitsFH h28_pruned10 (by decide) 28 10 231460 36190 (by decide) (by decide) (by decide) (by decide) 1580727390048228830862881339350188032
    H0.rho_h28_b10 H0.tab_h28_b10 H0.small_h28_b10 H0.near_h28_b10 H0.tab_h28_b10_ok H0.rate_h28_b10_ok H0.small_h28_b10_ok
    H0.near_h28_b10_ok H0.check_h28_b10_ok [H0.cover_h28_b10_0, H0.cover_h28_b10_1] [H0.coverh_h28_b10_0] H0.covers_h28_b10_ok

/-- Height 28, kept subtree height 8, 9,541 signatures (82.6% of the cover attack's 1.156e+04). -/
abbrev h28_pruned8 : Params := ⟨28, 1, 6, 8, 9541, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 28, kept subtree height 8, 9,541 signatures. -/
theorem h28_pruned8_bits : @Det.HasClassicalSecurityBitsDet h28_pruned8 127 :=
  @det_bitsFH h28_pruned8 (by decide) 28 8 57896 9541 (by decide) (by decide) (by decide) (by decide) 1879812259125035374945945504540786688
    H0.rho_h28_b8 H0.tab_h28_b8 H0.small_h28_b8 H0.near_h28_b8 H0.tab_h28_b8_ok H0.rate_h28_b8_ok H0.small_h28_b8_ok
    H0.near_h28_b8_ok H0.check_h28_b8_ok [H0.cover_h28_b8_0, H0.cover_h28_b8_1] [H0.coverh_h28_b8_0] H0.covers_h28_b8_ok

/-- Height 28, layered (12 + 8 + 8), 5,634,000,000 signatures (97.8% of the cover attack's 5.759e+09). -/
abbrev h28_layered : Params := ⟨28, 3, 8, 28, 5634000000, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- **127 bits for the deterministic signer**, height 28, layered (12 + 8 + 8), 5,634,000,000 signatures. -/
theorem h28_layered_bits : @Det.HasClassicalSecurityBitsDet h28_layered 127 :=
  @det_bitsFH h28_layered (by decide) 28 28 925696 5634000000 (by decide) (by decide) (by decide) (by decide) 181191675984824164237263828385005568
    H0.rho_h28_b28 H0.tab_h28_b28 H0.small_h28_b28 H0.near_h28_b28 H0.tab_h28_b28_ok H0.rate_h28_b28_ok H0.small_h28_b28_ok
    H0.near_h28_b28_ok H0.check_h28_b28_ok [H0.cover_h28_b28_0] [] H0.covers_h28_L_ok

/-- **The forest lifetimes**: 127 bits at every configuration. -/
theorem requestedSecurity :
    @Det.HasClassicalSecurityBitsDet h22_full 127 ∧
    @Det.HasClassicalSecurityBitsDet h22_pruned20 127 ∧
    @Det.HasClassicalSecurityBitsDet h22_pruned14 127 ∧
    @Det.HasClassicalSecurityBitsDet h22_pruned13 127 ∧
    @Det.HasClassicalSecurityBitsDet h22_pruned12 127 ∧
    @Det.HasClassicalSecurityBitsDet h22_pruned10 127 ∧
    @Det.HasClassicalSecurityBitsDet h22_pruned8 127 ∧
    @Det.HasClassicalSecurityBitsDet h22_layered 127 ∧
    @Det.HasClassicalSecurityBitsDet h24_full 127 ∧
    @Det.HasClassicalSecurityBitsDet h24_pruned20 127 ∧
    @Det.HasClassicalSecurityBitsDet h24_pruned14 127 ∧
    @Det.HasClassicalSecurityBitsDet h24_pruned13 127 ∧
    @Det.HasClassicalSecurityBitsDet h24_pruned12 127 ∧
    @Det.HasClassicalSecurityBitsDet h24_pruned10 127 ∧
    @Det.HasClassicalSecurityBitsDet h24_pruned8 127 ∧
    @Det.HasClassicalSecurityBitsDet h24_layered 127 ∧
    @Det.HasClassicalSecurityBitsDet h26_full 127 ∧
    @Det.HasClassicalSecurityBitsDet h26_pruned20 127 ∧
    @Det.HasClassicalSecurityBitsDet h26_pruned14 127 ∧
    @Det.HasClassicalSecurityBitsDet h26_pruned13 127 ∧
    @Det.HasClassicalSecurityBitsDet h26_pruned12 127 ∧
    @Det.HasClassicalSecurityBitsDet h26_pruned10 127 ∧
    @Det.HasClassicalSecurityBitsDet h26_pruned8 127 ∧
    @Det.HasClassicalSecurityBitsDet h26_layered 127 ∧
    @Det.HasClassicalSecurityBitsDet h28_full 127 ∧
    @Det.HasClassicalSecurityBitsDet h28_pruned20 127 ∧
    @Det.HasClassicalSecurityBitsDet h28_pruned14 127 ∧
    @Det.HasClassicalSecurityBitsDet h28_pruned13 127 ∧
    @Det.HasClassicalSecurityBitsDet h28_pruned12 127 ∧
    @Det.HasClassicalSecurityBitsDet h28_pruned10 127 ∧
    @Det.HasClassicalSecurityBitsDet h28_pruned8 127 ∧
    @Det.HasClassicalSecurityBitsDet h28_layered 127 :=
  ⟨h22_full_bits, h22_pruned20_bits, h22_pruned14_bits, h22_pruned13_bits, h22_pruned12_bits, h22_pruned10_bits, h22_pruned8_bits, h22_layered_bits, h24_full_bits, h24_pruned20_bits, h24_pruned14_bits, h24_pruned13_bits, h24_pruned12_bits, h24_pruned10_bits, h24_pruned8_bits, h24_layered_bits, h26_full_bits, h26_pruned20_bits, h26_pruned14_bits, h26_pruned13_bits, h26_pruned12_bits, h26_pruned10_bits, h26_pruned8_bits, h26_layered_bits, h28_full_bits, h28_pruned20_bits, h28_pruned14_bits, h28_pruned13_bits, h28_pruned12_bits, h28_pruned10_bits, h28_pruned8_bits, h28_layered_bits⟩

end LeanForest.Lifetimes
