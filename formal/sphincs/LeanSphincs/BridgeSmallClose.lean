import LeanSphincs.BridgeSmallSample
import LeanSphincs.BridgeRoutes
import LeanSphincs.BridgeDet

/-! The coefficient `smallFail q` of the expected failing share of the prepared searches in the
small-budget bound for the deterministic signer. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
open HiddenBridge PotentialA Completeness SeedModel Graph Assembly Reduce Internalize

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- The coefficient of the failing share. -/
noncomputable def smallFail (q : ℕ) : ℝ≥0∞ :=
  (((q - keygenCost : ℕ) : ℝ≥0∞) + signatureLimit) +
    (((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) * (((q - keygenCost : ℕ) : ℝ≥0∞) + signatureLimit)

end LeanSphincs.Security.ForsPotential
