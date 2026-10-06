import LeanSphincs.BridgeForsAssembly
import LeanSphincs.BridgeNoRepeat

/-! The one-coin excess forecast of a new pair at the start of the run (`startExcessO`), which is
the start value of the future-pair term of the one-coin FORS potential. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

section TotalO

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- The one-coin excess forecast of a new pair at the start of the run. -/
noncomputable def startExcessO (wbar b0 : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtualOnce Finset.univ wbar (excess b0) signatureLimit I 0) k []

/-- Without cached digest blocks the excess forecast is that of the future pairs alone. -/
theorem hValueO_clean (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (s : State)
    (hclean : ∀ m ρ, s.cache (blk parameter data m ρ 0) = none) (P : List Pair) (L : QueryLog SigningSpec)
    (d : Multiset View) (n k : ℕ) :
    hValueO parameter data wbar b0 s P L d n k =
      creations Finset.univ landing (fun I => virtualOnce Finset.univ wbar (excess b0) n I d) k [] :=
  fut_clean s L _ hclean _ n k d

theorem hValueO_start (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (s : State)
    (hclean : ∀ m ρ, s.cache (blk parameter data m ρ 0) = none) (k : ℕ) :
    hValueO parameter data wbar b0 s [] [] 0 signatureLimit k = startExcessO wbar b0 k :=
  hValueO_clean parameter data wbar b0 s hclean [] [] 0 signatureLimit k

end TotalO

end LeanSphincs.Security.ForsPotential
