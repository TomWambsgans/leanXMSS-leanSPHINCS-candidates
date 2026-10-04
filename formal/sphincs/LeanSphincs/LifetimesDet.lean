import LeanSphincs.H0DetCheckFW

/-! Proved lifetimes for the deterministic signer (seed-derived randomizers): 127 classical bits
against any adversary. Small budgets use the linear potential (which also pays the signature part of
the contact-before-reveal term at FORS leaf queries), the cover potential at baseline `ρ / 2^128` and
the FORS contact bounds; large budgets use the one-coin split certificates at the survival-weighted
baseline. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.LifetimesDet

open Security ForsPotential


/-- Subtree height 8, 7340 signatures (80.9% of the attack's 9074). -/
abbrev det8 : Params := ⟨8, 7340, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 8 and 7340 signatures. -/
theorem det8_bits : @Det.HasClassicalSecurityBitsDet det8 127 :=
  @det_bitsFW det8 (by decide) 8 7340 rfl rfl 1218907446475609523212972892983656448 H0.rhoFW_b8 H0.coverFW_b8.tab H0.optFW_b8 H0.optFW_b8_ok
    528902999279981919639 H0.nearFW_b8 H0.nearFW_b8_ok H0.smallFW_b8_ok
    (fun q' h1 h2 => @H0.h0FW_bound_b8 det8 rfl rfl q' h1 h2)

/-- Subtree height 10, 27800 signatures (82.2% of the attack's 33809). -/
abbrev det10 : Params := ⟨10, 27800, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 10 and 27800 signatures. -/
theorem det10_bits : @Det.HasClassicalSecurityBitsDet det10 127 :=
  @det_bitsFW det10 (by decide) 10 27800 rfl rfl 939906129562517687472972752270393344 H0.rhoFW_b10 H0.coverFW_b10.tab H0.optFW_b10 H0.optFW_b10_ok
    500800328459634976823 H0.nearFW_b10 H0.nearFW_b10_ok H0.smallFW_b10_ok
    (fun q' h1 h2 => @H0.h0FW_bound_b10 det10 rfl rfl q' h1 h2)

/-- Subtree height 12, 105800 signatures (84.2% of the attack's 125715). -/
abbrev det12 : Params := ⟨12, 105800, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 12 and 105800 signatures. -/
theorem det12_bits : @Det.HasClassicalSecurityBitsDet det12 127 :=
  @det_bitsFW det12 (by decide) 12 105800 rfl rfl 790363695024114415431440669675094016 H0.rhoFW_b12 H0.coverFW_b12.tab H0.optFW_b12 H0.optFW_b12_ok
    476480851060527450016 H0.nearFW_b12 H0.nearFW_b12_ok H0.smallFW_b12_ok
    (fun q' h1 h2 => @H0.h0FW_bound_b12 det12 rfl rfl q' h1 h2)

/-- Subtree height 13, 206000 signatures (85.0% of the attack's 242291). -/
abbrev det13 : Params := ⟨13, 206000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 13 and 206000 signatures. -/
theorem det13_bits : @Det.HasClassicalSecurityBitsDet det13 127 :=
  @det_bitsFW det13 (by decide) 13 206000 rfl rfl 664613997892457936451903530140172288 H0.rhoFW_b13 H0.coverFW_b13.tab H0.optFW_b13 H0.optFW_b13_ok
    463870766025814343745 H0.nearFW_b13 H0.nearFW_b13_ok H0.smallFW_b13_ok
    (fun q' h1 h2 => @H0.h0FW_bound_b13 det13 rfl rfl q' h1 h2)

/-- Subtree height 14, 402000 signatures (86.1% of the attack's 466871). -/
abbrev det14 : Params := ⟨14, 402000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 14 and 402000 signatures. -/
theorem det14_bits : @Det.HasClassicalSecurityBitsDet det14 127 :=
  @det_bitsFW det14 (by decide) 14 402000 rfl rfl 609453723237804761606486446491828224 H0.rhoFW_b14 H0.coverFW_b14.tab H0.optFW_b14 H0.optFW_b14_ok
    452611764570866167153 H0.nearFW_b14 H0.nearFW_b14_ok H0.smallFW_b14_ok
    (fun q' h1 h2 => @H0.h0FW_bound_b14 det14 rfl rfl q' h1 h2)

/-- Subtree height 20, 22000000 signatures (92.4% of the attack's 23797911). -/
abbrev det20 : Params := ⟨20, 22000000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 20 and 22000000 signatures. -/
theorem det20_bits : @Det.HasClassicalSecurityBitsDet det20 127 :=
  @det_bitsFW det20 (by decide) 20 22000000 rfl rfl 279435764177603821911096855707516928 H0.rhoFW_b20 H0.coverFW_b20.tab H0.optFW_b20 H0.optFW_b20_ok
    387028092991610363445 H0.nearFW_b20 H0.nearFW_b20_ok H0.smallFW_b20_ok
    (fun q' h1 h2 => @H0.h0FW_bound_b20 det20 rfl rfl q' h1 h2)

/-- Subtree height 26, 1156000000 signatures (96.1% of the attack's 1203133390). -/
abbrev det26 : Params := ⟨26, 1156000000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 26 and 1156000000 signatures. -/
theorem det26_bits : @Det.HasClassicalSecurityBitsDet det26 127 :=
  @det_bitsFW det26 (by decide) 26 1156000000 rfl rfl 166153499473114484112975882535043072 H0.rhoFW_b26 H0.coverFW_b26.tab H0.optFW_b26 H0.optFW_b26_ok
    317758860427398283297 H0.nearFW_b26 H0.nearFW_b26_ok H0.smallFW_b26_ok
    (fun q' h1 h2 => @H0.h0FW_bound_b26 det26 rfl rfl q' h1 h2)

/-- **The deterministic-signer lifetimes**: 127 bits at every subtree height. -/
theorem requestedSecurityDet :
    @Det.HasClassicalSecurityBitsDet det26 127 ∧ @Det.HasClassicalSecurityBitsDet det20 127 ∧
    @Det.HasClassicalSecurityBitsDet det14 127 ∧ @Det.HasClassicalSecurityBitsDet det13 127 ∧
    @Det.HasClassicalSecurityBitsDet det12 127 ∧ @Det.HasClassicalSecurityBitsDet det10 127 ∧
    @Det.HasClassicalSecurityBitsDet det8 127 :=
  ⟨det26_bits, det20_bits, det14_bits, det13_bits, det12_bits, det10_bits, det8_bits⟩

end LeanSphincs.LifetimesDet
