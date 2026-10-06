import LeanForest.LifetimeCertificates

/-! **Proved lifetimes of the forest variant** for the deterministic signer (seed-derived
randomizers): 127 classical bits against any adversary. Small budgets use the linear potential, the
one-coin cover potential at baseline `ρ / 2^128` and the contact bound A4 of the forest; large
budgets use the one-coin covers at the survival-weighted baseline. Every lifetime is at least the
proved lifetime of the FORS variant (`LeanSphincs.Lifetimes.requestedSecurity`). -/

open OracleComp OracleSpec ENNReal

namespace LeanForest.Lifetimes

open Security ForsPotential

/-- Subtree height 26, 1268000000 signatures (93.8% of the best known attack's 1.352e+09; the FORS variant: 1156000000). -/
abbrev full : Params := ⟨26, 1268000000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 26 and 1268000000 signatures. -/
theorem full_bits : @Det.HasClassicalSecurityBitsDet full 127 :=
  @det_bitsF full (by decide) 26 1268000000 rfl rfl 332306998946228968225951765070086144 H0.rho_b26 H0.tab_b26 H0.small_b26 H0.near_b26 H0.tab_b26_ok
    H0.rate_b26_ok H0.small_b26_ok H0.near_b26_ok H0.check_b26_ok H0.cover_b26 H0.cover_b26_ok

/-- Subtree height 20, 23700000 signatures (89.3% of the best known attack's 2.654e+07; the FORS variant: 22380000). -/
abbrev pruned20 : Params := ⟨20, 23700000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 20 and 23700000 signatures. -/
theorem pruned20_bits : @Det.HasClassicalSecurityBitsDet pruned20 127 :=
  @det_bitsF pruned20 (by decide) 20 23700000 rfl rfl 664613997892457936451903530140172288 H0.rho_b20 H0.tab_b20 H0.small_b20 H0.near_b20 H0.tab_b20_ok
    H0.rate_b20_ok H0.small_b20_ok H0.near_b20_ok H0.check_b20_ok H0.cover_b20 H0.cover_b20_ok

/-- Subtree height 14, 438800 signatures (88.1% of the best known attack's 4.98e+05; the FORS variant: 412500). -/
abbrev pruned14 : Params := ⟨14, 438800, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 14 and 438800 signatures. -/
theorem pruned14_bits : @Det.HasClassicalSecurityBitsDet pruned14 127 :=
  @det_bitsF pruned14 (by decide) 14 438800 rfl rfl 1329227995784915872903807060280344576 H0.rho_b14 H0.tab_b14 H0.small_b14 H0.near_b14 H0.tab_b14_ok
    H0.rate_b14_ok H0.small_b14_ok H0.near_b14_ok H0.check_b14_ok H0.cover_b14 H0.cover_b14_ok

/-- Subtree height 13, 226100 signatures (88.0% of the best known attack's 2.57e+05; the FORS variant: 211900). -/
abbrev pruned13 : Params := ⟨13, 226100, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 13 and 226100 signatures. -/
theorem pruned13_bits : @Det.HasClassicalSecurityBitsDet pruned13 127 :=
  @det_bitsF pruned13 (by decide) 13 226100 rfl rfl 1580727390048228830862881339350188032 H0.rho_b13 H0.tab_b13 H0.small_b13 H0.near_b13 H0.tab_b13_ok
    H0.rate_b13_ok H0.small_b13_ok H0.near_b13_ok H0.check_b13_ok H0.cover_b13 H0.cover_b13_ok

/-- Subtree height 12, 115800 signatures (87.7% of the best known attack's 1.32e+05; the FORS variant: 108700). -/
abbrev pruned12 : Params := ⟨12, 115800, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 12 and 115800 signatures. -/
theorem pruned12_bits : @Det.HasClassicalSecurityBitsDet pruned12 127 :=
  @det_bitsF pruned12 (by decide) 12 115800 rfl rfl 1580727390048228830862881339350188032 H0.rho_b12 H0.tab_b12 H0.small_b12 H0.near_b12 H0.tab_b12_ok
    H0.rate_b12_ok H0.small_b12_ok H0.near_b12_ok H0.check_b12_ok H0.cover_b12 H0.cover_b12_ok

/-- Subtree height 10, 30650 signatures (88.3% of the best known attack's 3.47e+04; the FORS variant: 28600). -/
abbrev pruned10 : Params := ⟨10, 30650, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 10 and 30650 signatures. -/
theorem pruned10_bits : @Det.HasClassicalSecurityBitsDet pruned10 127 :=
  @det_bitsF pruned10 (by decide) 10 30650 rfl rfl 1879812259125035374945945504540786688 H0.rho_b10 H0.tab_b10 H0.small_b10 H0.near_b10 H0.tab_b10_ok
    H0.rate_b10_ok H0.small_b10_ok H0.near_b10_ok H0.check_b10_ok H0.cover_b10 H0.cover_b10_ok

/-- Subtree height 8, 8110 signatures (87.9% of the best known attack's 9230; the FORS variant: 7530). -/
abbrev pruned8 : Params := ⟨8, 8110, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 8 and 8110 signatures. -/
theorem pruned8_bits : @Det.HasClassicalSecurityBitsDet pruned8 127 :=
  @det_bitsF pruned8 (by decide) 8 8110 rfl rfl 2235486113420830575288774845660135424 H0.rho_b8 H0.tab_b8 H0.small_b8 H0.near_b8 H0.tab_b8_ok
    H0.rate_b8_ok H0.small_b8_ok H0.near_b8_ok H0.check_b8_ok H0.cover_b8 H0.cover_b8_ok

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
