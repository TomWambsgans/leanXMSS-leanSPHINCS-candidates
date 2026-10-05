import LeanSphincs.LifetimeCertificates

/-! Proved lifetimes for the deterministic signer (seed-derived randomizers): 127 classical bits
against any adversary. Small budgets use the linear potential (which also pays the signature part of
the contact-before-reveal term and the shortfall of FORS leaf queries at near-covered leaves), the
cover potential at baseline `ρ / 2^128` and the FORS contact bounds; large budgets use the one-coin
split certificates at the survival-weighted baseline. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Lifetimes

open Security ForsPotential

/-- Subtree height 8, 7530 signatures (83.0% of the attack's 9074). -/
abbrev pruned8 : Params := ⟨8, 7530, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 8 and 7530 signatures. -/
theorem pruned8_bits : @Det.HasClassicalSecurityBitsDet pruned8 127 :=
  @det_bits pruned8 (by decide) 8 7530 rfl rfl 2716668597607663370492372386760884224 H0.rho_b8 H0.cover_b8.tab H0.opt_b8 H0.opt_b8_ok
    542594263012276011485 H0.near_b8 H0.near_b8_ok H0.small_b8_ok
    (fun q' h1 h2 => @H0.h0_bound_b8 pruned8 rfl rfl q' h1 h2)

/-- Subtree height 10, 28600 signatures (84.6% of the attack's 33809). -/
abbrev pruned10 : Params := ⟨10, 28600, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 10 and 28600 signatures. -/
theorem pruned10_bits : @Det.HasClassicalSecurityBitsDet pruned10 127 :=
  @det_bits pruned10 (by decide) 10 28600 rfl rfl 2385577546783380400171387171683434496 H0.rho_b10 H0.cover_b10.tab H0.opt_b10 H0.opt_b10_ok
    515211924554235764060 H0.near_b10 H0.near_b10_ok H0.small_b10_ok
    (fun q' h1 h2 => @H0.h0_bound_b10 pruned10 rfl rfl q' h1 h2)

/-- Subtree height 12, 108700 signatures (86.5% of the attack's 125715). -/
abbrev pruned12 : Params := ⟨12, 108700, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 12 and 108700 signatures. -/
theorem pruned12_bits : @Det.HasClassicalSecurityBitsDet pruned12 127 :=
  @det_bits pruned12 (by decide) 12 108700 rfl rfl 2049949804534797888604160119780933632 H0.rho_b12 H0.cover_b12.tab H0.opt_b12 H0.opt_b12_ok
    489541306790466650023 H0.near_b12 H0.near_b12_ok H0.small_b12_ok
    (fun q' h1 h2 => @H0.h0_bound_b12 pruned12 rfl rfl q' h1 h2)

/-- Subtree height 13, 211900 signatures (87.5% of the attack's 242291). -/
abbrev pruned13 : Params := ⟨13, 211900, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 13 and 211900 signatures. -/
theorem pruned13_bits : @Det.HasClassicalSecurityBitsDet pruned13 127 :=
  @det_bits pruned13 (by decide) 13 211900 rfl rfl 1879812259125035374945945504540786688 H0.rho_b13 H0.cover_b13.tab H0.opt_b13 H0.opt_b13_ok
    477156393028559309702 H0.near_b13 H0.near_b13_ok H0.small_b13_ok
    (fun q' h1 h2 => @H0.h0_bound_b13 pruned13 rfl rfl q' h1 h2)

/-- Subtree height 14, 412500 signatures (88.4% of the attack's 466871). -/
abbrev pruned14 : Params := ⟨14, 412500, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 14 and 412500 signatures. -/
theorem pruned14_bits : @Det.HasClassicalSecurityBitsDet pruned14 127 :=
  @det_bits pruned14 (by decide) 14 412500 rfl rfl 1580727390048228830862881339350188032 H0.rho_b14 H0.cover_b14.tab H0.opt_b14 H0.opt_b14_ok
    464433716827179997059 H0.near_b14 H0.near_b14_ok H0.small_b14_ok
    (fun q' h1 h2 => @H0.h0_bound_b14 pruned14 rfl rfl q' h1 h2)

/-- Subtree height 20, 22380000 signatures (94.0% of the attack's 23797911). -/
abbrev pruned20 : Params := ⟨20, 22380000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 20 and 22380000 signatures. -/
theorem pruned20_bits : @Det.HasClassicalSecurityBitsDet pruned20 127 :=
  @det_bits pruned20 (by decide) 20 22380000 rfl rfl 773427830839001786045950191225274368 H0.rho_b20 H0.cover_b20.tab H0.opt_b20 H0.opt_b20_ok
    393713123714106451269 H0.near_b20 H0.near_b20_ok H0.small_b20_ok
    (fun q' h1 h2 => @H0.h0_bound_b20 pruned20 rfl rfl q' h1 h2)

/-- Subtree height 26, 1156000000 signatures (96.1% of the attack's 1203133390). -/
abbrev full : Params := ⟨26, 1156000000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 26 and 1156000000 signatures. -/
theorem full_bits : @Det.HasClassicalSecurityBitsDet full 127 :=
  @det_bits full (by decide) 26 1156000000 rfl rfl 166153499473114484112975882535043072 H0.rho_b26 H0.cover_b26.tab H0.opt_b26 H0.opt_b26_ok
    317758860427398283297 H0.near_b26 H0.near_b26_ok H0.small_b26_ok
    (fun q' h1 h2 => @H0.h0_bound_b26 full rfl rfl q' h1 h2)

/-- **The deterministic-signer lifetimes**: 127 bits at every subtree height. -/
theorem requestedSecurity :
    @Det.HasClassicalSecurityBitsDet full 127 ∧ @Det.HasClassicalSecurityBitsDet pruned20 127 ∧
    @Det.HasClassicalSecurityBitsDet pruned14 127 ∧ @Det.HasClassicalSecurityBitsDet pruned13 127 ∧
    @Det.HasClassicalSecurityBitsDet pruned12 127 ∧ @Det.HasClassicalSecurityBitsDet pruned10 127 ∧
    @Det.HasClassicalSecurityBitsDet pruned8 127 :=
  ⟨full_bits, pruned20_bits, pruned14_bits, pruned13_bits, pruned12_bits, pruned10_bits, pruned8_bits⟩

end LeanSphincs.Lifetimes
