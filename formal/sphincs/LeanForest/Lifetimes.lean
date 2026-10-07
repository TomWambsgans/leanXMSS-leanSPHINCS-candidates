import LeanForest.LifetimeCertificates

/-! **Proved lifetimes of the forest variant** for the deterministic signer (seed-derived
randomizers): 127 classical bits against any adversary. Small budgets use the linear potential, the
one-coin cover potential at baseline `ρ / 2^128` and the contact bound A4 of the forest; large
budgets use the one-coin covers at the survival-weighted baseline. Every lifetime is at least the
proved lifetime of the FORS variant (`LeanSphincs.Lifetimes.requestedSecurity`). -/

open OracleComp OracleSpec ENNReal

namespace LeanForest.Lifetimes

open Security ForsPotential

/-- Subtree height 26, 1400000000 signatures (96.2% of the cover attack's 1.455e+09; the FORS variant: 1156000000). -/
abbrev full : Params := ⟨26, 1400000000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 26 and 1400000000 signatures. -/
theorem full_bits : @Det.HasClassicalSecurityBitsDet full 127 :=
  @det_bitsFH full (by decide) 26 1400000000 rfl rfl 248051843446051213170987463415431168 H0.rho_b26 H0.tab_b26 H0.small_b26 H0.near_b26 H0.tab_b26_ok
    H0.rate_b26_ok H0.small_b26_ok H0.near_b26_ok H0.check_b26_ok [H0.cover_b26_0] [] H0.covers_b26_ok

/-- Subtree height 20, 26340000 signatures (91.4% of the cover attack's 2.881e+07; the FORS variant: 22380000). -/
abbrev pruned20 : Params := ⟨20, 26340000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 20 and 26340000 signatures. -/
theorem pruned20_bits : @Det.HasClassicalSecurityBitsDet pruned20 127 :=
  @det_bitsFH pruned20 (by decide) 20 26340000 rfl rfl 558871528355207643822193711415033856 H0.rho_b20 H0.tab_b20 H0.small_b20 H0.near_b20 H0.tab_b20_ok
    H0.rate_b20_ok H0.small_b20_ok H0.near_b20_ok H0.check_b20_ok [H0.cover_b20_0, H0.cover_b20_1] [H0.coverh_b20_0] H0.covers_b20_ok

/-- Subtree height 14, 486400 signatures (86.4% of the cover attack's 5.63e+05; the FORS variant: 412500). -/
abbrev pruned14 : Params := ⟨14, 486400, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 14 and 486400 signatures. -/
theorem pruned14_bits : @Det.HasClassicalSecurityBitsDet pruned14 127 :=
  @det_bitsFH pruned14 (by decide) 14 486400 rfl rfl 1179940068462340716375613534384422912 H0.rho_b14 H0.tab_b14 H0.small_b14 H0.near_b14 H0.tab_b14_ok
    H0.rate_b14_ok H0.small_b14_ok H0.near_b14_ok H0.check_b14_ok [H0.cover_b14_0, H0.cover_b14_1] [H0.coverh_b14_0] H0.covers_b14_ok

/-- Subtree height 13, 249800 signatures (85.6% of the cover attack's 2.919e+05; the FORS variant: 211900). -/
abbrev pruned13 : Params := ⟨13, 249800, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 13 and 249800 signatures. -/
theorem pruned13_bits : @Det.HasClassicalSecurityBitsDet pruned13 127 :=
  @det_bitsFH pruned13 (by decide) 13 249800 rfl rfl 1314909569352122321482228451418046464 H0.rho_b13 H0.tab_b13 H0.small_b13 H0.near_b13 H0.tab_b13_ok
    H0.rate_b13_ok H0.small_b13_ok H0.near_b13_ok H0.check_b13_ok [H0.cover_b13_0, H0.cover_b13_1] [H0.coverh_b13_0] H0.covers_b13_ok

/-- Subtree height 12, 128300 signatures (84.8% of the cover attack's 1.513e+05; the FORS variant: 108700). -/
abbrev pruned12 : Params := ⟨12, 128300, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 12 and 128300 signatures. -/
theorem pruned12_bits : @Det.HasClassicalSecurityBitsDet pruned12 127 :=
  @det_bitsFH pruned12 (by decide) 12 128300 rfl rfl 1465317791798479402835792044283133952 H0.rho_b12 H0.tab_b12 H0.small_b12 H0.near_b12 H0.tab_b12_ok
    H0.rate_b12_ok H0.small_b12_ok H0.near_b12_ok H0.check_b12_ok [H0.cover_b12_0, H0.cover_b12_1] [H0.coverh_b12_0] H0.covers_b12_ok

/-- Subtree height 10, 33850 signatures (83.4% of the cover attack's 4.06e+04; the FORS variant: 28600). -/
abbrev pruned10 : Params := ⟨10, 33850, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 10 and 33850 signatures. -/
theorem pruned10_bits : @Det.HasClassicalSecurityBitsDet pruned10 127 :=
  @det_bitsFH pruned10 (by decide) 10 33850 rfl rfl 1742566343746827758207774509045383168 H0.rho_b10 H0.tab_b10 H0.small_b10 H0.near_b10 H0.tab_b10_ok
    H0.rate_b10_ok H0.small_b10_ok H0.near_b10_ok H0.check_b10_ok [H0.cover_b10_0, H0.cover_b10_1] [H0.coverh_b10_0] H0.covers_b10_ok

/-- Subtree height 8, 8930 signatures (82.0% of the cover attack's 1.089e+04; the FORS variant: 7530). -/
abbrev pruned8 : Params := ⟨8, 8930, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 8 and 8930 signatures. -/
theorem pruned8_bits : @Det.HasClassicalSecurityBitsDet pruned8 127 :=
  @det_bitsFH pruned8 (by decide) 8 8930 rfl rfl 2027867772287336761555281578532274176 H0.rho_b8 H0.tab_b8 H0.small_b8 H0.near_b8 H0.tab_b8_ok
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
