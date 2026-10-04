import LeanSphincs.BridgeSmallSample
import LeanSphincs.BridgeRoutes
import LeanSphincs.BridgeDet

/-! The small-budget route for the deterministic signer: the seed-free win of the memoizing
adversary averaged over the samples, preparations and exposures. -/

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

/-- The sample-independent part of the small-budget bound. -/
noncomputable def smallMain (ρ : ℝ) (q : ℕ) (B c : ℚ) : ℝ≥0∞ :=
  ENNReal.ofReal (ρ * (q - keygenCost : ℕ) / 2 ^ 128) + ((q - keygenCost : ℕ) : ℝ≥0∞) * ENNReal.ofReal (B : ℝ) +
    (((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) *
      (signatureLimit * matchRate +
        (q - keygenCost : ℕ) * (((2 ^ 128 - ((q - keygenCost) + 2 ^ 32) : ℕ) : ℝ≥0∞))⁻¹) +
    (((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) * ((q - keygenCost : ℕ) * ENNReal.ofReal (c : ℝ))

/-- The coefficient of the failing share. -/
noncomputable def smallFail (q : ℕ) : ℝ≥0∞ :=
  (((q - keygenCost : ℕ) : ℝ≥0∞) + signatureLimit) +
    (((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) * (((q - keygenCost : ℕ) : ℝ≥0∞) + signatureLimit)

set_option maxRecDepth 100000 in
/-- **Small budgets, seed-free win.** The near term enters at half the certified near H-term `c`. -/
theorem small_seedFree_bound (hb : 0 < subtreeHeight) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (hq : q < 2 ^ 256) (hq2 : 2 * (q - keygenCost) ≤ 2 ^ 128)
    (ρ : ℝ) (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (b N : ℕ) (hbb : subtreeHeight = b) (hNN : signatureLimit = N)
    (t : H0.PoisTable) (o : H0.OptS) (hthr : H0.checkThreshS b N t o = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128)
    (qb m : ℕ) (c : ℚ) (hnear : H0.checkNear b N qb m c = true) (hqb : q - keygenCost ≤ qb) :
    Pr[Win | seedFreeExperiment (internalize adversary) q] ≤
      smallMain ρ q o.B (c / 2) + smallFail q * expectedFail := by
  refine le_trans (seedFree_le_exposeP adversary q) ?_
  set A := smallMain ρ q o.B (c / 2) with hA
  set C := smallFail q with hC
  have hsample : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) →
      ∀ known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
        (knownOf (truncateHash parameterOutput) fixed)),
      Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining)))) known prepared.2] ≤
        A + C * failMass (failSet prepared.1) := by
    intro parameterOutput fixed highs remaining prepared hprepared known hk
    refine le_trans (sample_boundS hb adversary hnr q hq hq2 parameterOutput fixed highs remaining prepared
      hprepared known hk ρ hN b N hbb hNN t o hthr hcthr qb m c hnear hqb) (le_of_eq ?_)
    rw [hA, hC]
    unfold smallMain smallFail
    ring
  simp only [probEvent_bind_eq_tsum]
  refine le_trans (tsum_bound_le _ _ A C (fun parameterOutput => ∑' fixed, Pr[= fixed | ($ᵗ HiddenGraph.Table :
    ProbComp HiddenGraph.Table)] *
    ∑' highs, Pr[= highs | ($ᵗ CoordinateHighs : ProbComp CoordinateHighs)] *
    ∑' remaining, Pr[= remaining | ($ᵗ RemainingOutputs : ProbComp RemainingOutputs)] *
    ∑' prepared, Pr[= prepared | preparation parameterOutput fixed highs remaining] *
      failMass (failSet prepared.1)) fun parameterOutput _ => ?_) le_rfl
  refine tsum_bound_le _ _ A C _ fun fixed _ => ?_
  refine tsum_bound_le _ _ A C _ fun highs _ => ?_
  refine tsum_bound_le _ _ A C _ fun remaining _ => ?_
  refine tsum_bound_le _ _ A C _ fun prepared hprepared => ?_
  refine le_trans (tsum_bound_le _ _ A C (fun _ => failMass (failSet prepared.1))
    fun known hk => hsample parameterOutput fixed highs remaining prepared hprepared known hk) ?_
  refine add_le_add le_rfl (mul_le_mul_right ?_ _)
  rw [ENNReal.tsum_mul_right]
  exact mul_le_of_le_one_left' tsum_probOutput_le_one

/-- **Small budgets, deterministic signer.** -/
theorem det_small (hb : 0 < subtreeHeight) (adversary : Adversary) (q : ℕ)
    (hbound : Det.HasHashQueryBoundDet adversary q) (hq : q < 2 ^ 256) (hq2 : 2 * (q - keygenCost) ≤ 2 ^ 128)
    (ρ : ℝ) (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (b N : ℕ) (hbb : subtreeHeight = b) (hNN : signatureLimit = N)
    (t : H0.PoisTable) (o : H0.OptS) (hthr : H0.checkThreshS b N t o = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128)
    (qb m : ℕ) (c : ℚ) (hnear : H0.checkNear b N qb m c = true) (hqb : q - keygenCost ≤ qb) :
    Det.forgeAdvantageDet adversary ≤
      smallMain ρ q o.B (c / 2) + smallFail q * (2 : ℝ≥0∞)⁻¹ ^ 201 + 2 * ((q : ℝ≥0∞) / 2 ^ 256) := by
  refine le_trans (Det.forgeAdvantageDet_le_seedFree adversary q hbound) (add_le_add ?_ le_rfl)
  refine le_trans (small_seedFree_bound hb (Memo.memoAdv adversary) (Memo.memoAdv_noRepeat adversary) q hq hq2 ρ hN
    b N hbb hNN t o hthr hcthr qb m c hnear hqb) ?_
  exact add_le_add le_rfl (mul_le_mul_left' expectedFail_le _)

end LeanSphincs.Security.ForsPotential
