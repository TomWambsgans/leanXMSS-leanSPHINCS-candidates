import LeanSphincs.H0DetCheck

/-! Proved lifetimes for the deterministic signer (seed-derived randomizers): 127 classical bits
against any adversary, at signature limits within 20% of the best known attack's (exact multinomial
model). Small budgets use the linear potential, the cover potential at baseline `ρ / 2^128` and the
FORS contact bounds; large budgets use the one-coin split certificates. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.LifetimesDet

open Security ForsPotential


/-- Subtree height 8, 7290 signatures (80.3% of the attack's 9074). -/
abbrev det8 : Params := ⟨8, 7290, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 8 and 7290 signatures. -/
theorem det8_bits : @Det.HasClassicalSecurityBitsDet det8 127 :=
  @det_bits det8 (by decide) 8 7290 rfl rfl 1003011803699947616358273242277871616 H0.rhoD_b8 H0.coverD_b8.tab H0.optD_b8 H0.optD_b8_ok
    525300073560412189732 H0.nearD_b8 H0.nearD_b8_ok H0.smallD_b8_ok
    (fun q' h1 h2 => @H0.h0D_bound_b8 det8 rfl rfl q' h1 h2)

/-- Subtree height 10, 27700 signatures (81.9% of the attack's 33809). -/
abbrev det10 : Params := ⟨10, 27700, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 10 and 27700 signatures. -/
theorem det10_bits : @Det.HasClassicalSecurityBitsDet det10 127 :=
  @det_bits det10 (by decide) 10 27700 rfl rfl 861897721041682210145346061961527296 H0.rhoD_b10 H0.coverD_b10.tab H0.optD_b10 H0.optD_b10_ok
    498998884457001784726 H0.nearD_b10 H0.nearD_b10_ok H0.smallD_b10_ok
    (fun q' h1 h2 => @H0.h0D_bound_b10 det10 rfl rfl q' h1 h2)

/-- Subtree height 12, 105000 signatures (83.5% of the attack's 125715). -/
abbrev det12 : Params := ⟨12, 105000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 12 and 105000 signatures. -/
theorem det12_bits : @Det.HasClassicalSecurityBitsDet det12 127 :=
  @det_bits det12 (by decide) 12 105000 rfl rfl 709236448006383222531678056019394560 H0.rhoD_b12 H0.coverD_b12.tab H0.optD_b12 H0.optD_b12_ok
    472877970280173413986 H0.nearD_b12 H0.nearD_b12_ok H0.smallD_b12_ok
    (fun q' h1 h2 => @H0.h0D_bound_b12 det12 rfl rfl q' h1 h2)

/-- Subtree height 13, 205000 signatures (84.6% of the attack's 242291). -/
abbrev det13 : Params := ⟨13, 205000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 13 and 205000 signatures. -/
theorem det13_bits : @Det.HasClassicalSecurityBitsDet det13 127 :=
  @det_bits det13 (by decide) 13 205000 rfl rfl 636436544780012666811850899752747008 H0.rhoD_b13 H0.coverD_b13.tab H0.optD_b13 H0.optD_b13_ok
    461618966024951372567 H0.nearD_b13 H0.nearD_b13_ok H0.smallD_b13_ok
    (fun q' h1 h2 => @H0.h0D_bound_b13 det13 rfl rfl q' h1 h2)

/-- Subtree height 14, 401000 signatures (85.9% of the attack's 466871). -/
abbrev det14 : Params := ⟨14, 401000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 14 and 401000 signatures. -/
theorem det14_bits : @Det.HasClassicalSecurityBitsDet det14 127 :=
  @det_bits det14 (by decide) 14 401000 rfl rfl 571109221290155043851993097059696640 H0.rhoD_b14 H0.coverD_b14.tab H0.optD_b14 H0.optD_b14_ok
    451485864536710917740 H0.nearD_b14 H0.nearD_b14_ok H0.smallD_b14_ok
    (fun q' h1 h2 => @H0.h0D_bound_b14 det14 rfl rfl q' h1 h2)

/-- Subtree height 20, 21450000 signatures (90.1% of the attack's 23797911). -/
abbrev det20 : Params := ⟨20, 21450000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 20 and 21450000 signatures. -/
theorem det20_bits : @Det.HasClassicalSecurityBitsDet det20 127 :=
  @det_bits det20 (by decide) 20 21450000 rfl rfl 98795461878014301928930083709386752 H0.rhoD_b20 H0.coverD_b20.tab H0.optD_b20 H0.optD_b20_ok
    377352390657832289009 H0.nearD_b20 H0.nearD_b20_ok H0.smallD_b20_ok
    (fun q' h1 h2 => @H0.h0D_bound_b20 det20 rfl rfl q' h1 h2)

/-- Subtree height 26, 1084000000 signatures (90.1% of the attack's 1203133390). -/
abbrev det26 : Params := ⟨26, 1084000000, by decide⟩

/-- **127 bits for the deterministic signer** at subtree height 26 and 1084000000 signatures. -/
theorem det26_bits : @Det.HasClassicalSecurityBitsDet det26 127 :=
  @det_bits det26 (by decide) 26 1084000000 rfl rfl 649037107316853453566312041152512 H0.rhoD_b26 H0.coverD_b26.tab H0.optD_b26 H0.optD_b26_ok
    297967651127296524290 H0.nearD_b26 H0.nearD_b26_ok H0.smallD_b26_ok
    (fun q' h1 h2 => @H0.h0D_bound_b26 det26 rfl rfl q' h1 h2)

/-- **The deterministic-signer lifetimes**: 127 bits at every subtree height. -/
theorem requestedSecurityDet :
    @Det.HasClassicalSecurityBitsDet det26 127 ∧ @Det.HasClassicalSecurityBitsDet det20 127 ∧
    @Det.HasClassicalSecurityBitsDet det14 127 ∧ @Det.HasClassicalSecurityBitsDet det13 127 ∧
    @Det.HasClassicalSecurityBitsDet det12 127 ∧ @Det.HasClassicalSecurityBitsDet det10 127 ∧
    @Det.HasClassicalSecurityBitsDet det8 127 :=
  ⟨det26_bits, det20_bits, det14_bits, det13_bits, det12_bits, det10_bits, det8_bits⟩

end LeanSphincs.LifetimesDet
