import LeanSphincs.BridgeForsAssembly
import LeanSphincs.H0Lifetimes
import LeanSphincs.BridgeTargeting

/-! The six requested lifetimes from the stage-1 argument: saturation of fixed and hidden targets,
the FORS potential through any adaptive adversary, and the certified excess-forecast bound. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Lifetimes

open Security ForsPotential HiddenBridge

/-- The targeting facts at every prepared sample of a parameter set. -/
def TargetingAll [Params] : Prop :=
  ∀ parameterOutput fixed highs remaining prepared,
    prepared ∈ support (preparation parameterOutput fixed highs remaining) →
    TargetingFor parameterOutput fixed highs remaining prepared

theorem full_of_targeting (h : @TargetingAll full) : @HasClassicalSecurityBits full 127 :=
  @stage1_close full (by decide) (by decide) h _ (fun q' hq => @H0.h0_fair full q' hq)
    (fun q' hq => @H0.h0_bound_full full rfl rfl q' hq)

theorem pruned20_of_targeting (h : @TargetingAll pruned20) : @HasClassicalSecurityBits pruned20 127 :=
  @stage1_close pruned20 (by decide) (by decide) h _ (fun q' hq => @H0.h0_fair pruned20 q' hq)
    (fun q' hq => @H0.h0_bound_pruned20 pruned20 rfl rfl q' hq)

theorem pruned14_of_targeting (h : @TargetingAll pruned14) : @HasClassicalSecurityBits pruned14 127 :=
  @stage1_close pruned14 (by decide) (by decide) h _ (fun q' hq => @H0.h0_fair pruned14 q' hq)
    (fun q' hq => @H0.h0_bound_pruned14 pruned14 rfl rfl q' hq)

theorem pruned13_of_targeting (h : @TargetingAll pruned13) : @HasClassicalSecurityBits pruned13 127 :=
  @stage1_close pruned13 (by decide) (by decide) h _ (fun q' hq => @H0.h0_fair pruned13 q' hq)
    (fun q' hq => @H0.h0_bound_pruned13 pruned13 rfl rfl q' hq)

theorem pruned12_of_targeting (h : @TargetingAll pruned12) : @HasClassicalSecurityBits pruned12 127 :=
  @stage1_close pruned12 (by decide) (by decide) h _ (fun q' hq => @H0.h0_fair pruned12 q' hq)
    (fun q' hq => @H0.h0_bound_pruned12 pruned12 rfl rfl q' hq)

theorem pruned10_of_targeting (h : @TargetingAll pruned10) : @HasClassicalSecurityBits pruned10 127 :=
  @stage1_close pruned10 (by decide) (by decide) h _ (fun q' hq => @H0.h0_fair pruned10 q' hq)
    (fun q' hq => @H0.h0_bound_pruned10 pruned10 rfl rfl q' hq)

theorem pruned8_of_targeting (h : @TargetingAll pruned8) : @HasClassicalSecurityBits pruned8 127 :=
  @stage1_close pruned8 (by decide) (by decide) h _ (fun q' hq => @H0.h0_fair pruned8 q' hq)
    (fun q' hq => @H0.h0_bound_pruned8 pruned8 rfl rfl q' hq)

/-- Every prepared sample has a targeting, at every pruning height `b ≥ 1`. -/
theorem targetingAll [Params] (hb : 0 < subtreeHeight) : TargetingAll := by
  intro parameterOutput fixed highs remaining prepared hprepared
  obtain ⟨tg, htrunc, hcompat, hmsg, hhit⟩ :=
    exists_targeting hb parameterOutput fixed highs remaining prepared hprepared
  exact ⟨tg, hcompat, uniformTruncation_of_trunc tg htrunc, hmsg, hhit⟩

/-- **The requested 127-bit lifetime claims.** -/
theorem requestedSecurity : RequestedSecurity :=
  ⟨full_of_targeting (@targetingAll full (by decide)),
    pruned20_of_targeting (@targetingAll pruned20 (by decide)),
    pruned13_of_targeting (@targetingAll pruned13 (by decide)),
    pruned14_of_targeting (@targetingAll pruned14 (by decide)),
    pruned12_of_targeting (@targetingAll pruned12 (by decide)),
    pruned10_of_targeting (@targetingAll pruned10 (by decide)),
    pruned8_of_targeting (@targetingAll pruned8 (by decide))⟩

end LeanSphincs.Lifetimes
