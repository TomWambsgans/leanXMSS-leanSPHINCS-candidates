import LeanForest.LifetimeCertificates

/-! **Proved lifetimes of the forest variant** for the deterministic signer (seed-derived
randomizers): 127 classical bits against any adversary. Small budgets use the linear potential, the
one-coin cover potential at baseline `ρ / 2^128` and the contact bound A4 of the forest; large
budgets use the one-coin covers at the survival-weighted baseline. -/

open OracleComp OracleSpec ENNReal

namespace LeanForest.Lifetimes

open Security ForsPotential

/-- Subtree height 24, 336700000 signatures (93.5% of the cover attack's 3.599e+08). -/
abbrev full : Params := ⟨24, 336700000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 24 and 336700000 signatures. -/
theorem full_bits : @Det.HasClassicalSecurityBitsDet full 127 :=
  @det_bitsFH full (by decide) 24 336700000 rfl rfl 332306998946228968225951765070086144 H0.rho_b24 H0.tab_b24 H0.small_b24 H0.near_b24 H0.tab_b24_ok
    H0.rate_b24_ok H0.small_b24_ok H0.near_b24_ok H0.check_b24_ok [H0.cover_b24_0] [] H0.covers_b24_ok

/-- Subtree height 20, 23830000 signatures (90.3% of the cover attack's 2.639e+07). -/
abbrev pruned20 : Params := ⟨20, 23830000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 20 and 23830000 signatures. -/
theorem pruned20_bits : @Det.HasClassicalSecurityBitsDet pruned20 127 :=
  @det_bitsFH pruned20 (by decide) 20 23830000 rfl rfl 609453723237804761606486446491828224 H0.rho_b20 H0.tab_b20 H0.small_b20 H0.near_b20 H0.tab_b20_ok
    H0.rate_b20_ok H0.small_b20_ok H0.near_b20_ok H0.check_b20_ok [H0.cover_b20_0, H0.cover_b20_1] [H0.coverh_b20_0] H0.covers_b20_ok

/-- Subtree height 14, 441500 signatures (85.2% of the cover attack's 5.18e+05). -/
abbrev pruned14 : Params := ⟨14, 441500, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 14 and 441500 signatures. -/
theorem pruned14_bits : @Det.HasClassicalSecurityBitsDet pruned14 127 :=
  @det_bitsFH pruned14 (by decide) 14 441500 rfl rfl 1218907446475609523212972892983656448 H0.rho_b14 H0.tab_b14 H0.small_b14 H0.near_b14 H0.tab_b14_ok
    H0.rate_b14_ok H0.small_b14_ok H0.near_b14_ok H0.check_b14_ok [H0.cover_b14_0, H0.cover_b14_1] [H0.coverh_b14_0] H0.covers_b14_ok

/-- Subtree height 13, 226800 signatures (84.4% of the cover attack's 2.687e+05). -/
abbrev pruned13 : Params := ⟨13, 226800, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 13 and 226800 signatures. -/
theorem pruned13_bits : @Det.HasClassicalSecurityBitsDet pruned13 127 :=
  @det_bitsFH pruned13 (by decide) 13 226800 rfl rfl 1329227995784915872903807060280344576 H0.rho_b13 H0.tab_b13 H0.small_b13 H0.near_b13 H0.tab_b13_ok
    H0.rate_b13_ok H0.small_b13_ok H0.near_b13_ok H0.check_b13_ok [H0.cover_b13_0, H0.cover_b13_1] [H0.coverh_b13_0] H0.covers_b13_ok

/-- Subtree height 12, 116600 signatures (83.7% of the cover attack's 1.394e+05). -/
abbrev pruned12 : Params := ⟨12, 116600, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 12 and 116600 signatures. -/
theorem pruned12_bits : @Det.HasClassicalSecurityBitsDet pruned12 127 :=
  @det_bitsFH pruned12 (by decide) 12 116600 rfl rfl 1580727390048228830862881339350188032 H0.rho_b12 H0.tab_b12 H0.small_b12 H0.near_b12 H0.tab_b12_ok
    H0.rate_b12_ok H0.small_b12_ok H0.near_b12_ok H0.check_b12_ok [H0.cover_b12_0, H0.cover_b12_1] [H0.coverh_b12_0] H0.covers_b12_ok

/-- Subtree height 10, 30810 signatures (82.3% of the cover attack's 3.746e+04). -/
abbrev pruned10 : Params := ⟨10, 30810, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 10 and 30810 signatures. -/
theorem pruned10_bits : @Det.HasClassicalSecurityBitsDet pruned10 127 :=
  @det_bitsFH pruned10 (by decide) 10 30810 rfl rfl 1723795442083364420290692123923054592 H0.rho_b10 H0.tab_b10 H0.small_b10 H0.near_b10 H0.tab_b10_ok
    H0.rate_b10_ok H0.small_b10_ok H0.near_b10_ok H0.check_b10_ok [H0.cover_b10_0, H0.cover_b10_1] [H0.coverh_b10_0] H0.covers_b10_ok

/-- Subtree height 8, 8154 signatures (81.1% of the cover attack's 1.005e+04). -/
abbrev pruned8 : Params := ⟨8, 8154, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 8 and 8154 signatures. -/
theorem pruned8_bits : @Det.HasClassicalSecurityBitsDet pruned8 127 :=
  @det_bitsFH pruned8 (by decide) 8 8154 rfl rfl 2049949804534797888604160119780933632 H0.rho_b8 H0.tab_b8 H0.small_b8 H0.near_b8 H0.tab_b8_ok
    H0.rate_b8_ok H0.small_b8_ok H0.near_b8_ok H0.check_b8_ok [H0.cover_b8_0, H0.cover_b8_1] [H0.coverh_b8_0] H0.covers_b8_ok

/-- **The forest lifetimes**: 127 bits at every subtree height. -/
theorem requestedSecurity :
    @Det.HasClassicalSecurityBitsDet full 127 ∧
    @Det.HasClassicalSecurityBitsDet pruned20 127 ∧
    @Det.HasClassicalSecurityBitsDet pruned14 127 ∧
    @Det.HasClassicalSecurityBitsDet pruned13 127 ∧
    @Det.HasClassicalSecurityBitsDet pruned12 127 ∧
    @Det.HasClassicalSecurityBitsDet pruned10 127 ∧
    @Det.HasClassicalSecurityBitsDet pruned8 127 :=
  ⟨full_bits, pruned20_bits, pruned14_bits, pruned13_bits, pruned12_bits, pruned10_bits, pruned8_bits⟩

end LeanForest.Lifetimes
