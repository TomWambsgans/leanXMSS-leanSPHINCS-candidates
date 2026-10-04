import LeanSphincs.BridgeRoutes
import LeanSphincs.BridgeForsAssemblyOnce
import LeanSphincs.BridgeDet
import LeanSphincs.StageOne
import LeanSphincs.H0BoundOnce

/-! The large-budget route for the deterministic signer: the one-coin stage-1 chain started from the
seed-free win of the memoizing adversary, closed by the split certificates above a starting budget. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

set_option maxRecDepth 100000 in
/-- **One-coin stage 1 from the seed-free win.** -/
theorem stage1_seedFree_boundO (hb : 0 < subtreeHeight) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (hq : q < 2 ^ 256)
    (htarget : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) →
      ∃ tg : Targeting HashInput HashOutput Coordinate,
        Compatible tg (sampleModel parameterOutput highs) ∧ UniformTruncation (R := HashOutput) tg ∧
        (∀ x, IsMsgInput x → tg.kind x = .none ∧ tg.digest x) ∧
        ∀ table, tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table →
          ∀ s : State, Prepared prepared.2 s → Agrees s.known table →
            (CorrectGuess table s ∨ CacheMatch.Bad (TargetAssignment.targets (truncateHash parameterOutput)
              (compTable parameterOutput fixed highs remaining table prepared.1)) s.cache) →
            Hit tg prepared.2 table s)
    (hclean : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) → ∀ x, IsMsgInput x → prepared.2 x = none)
    (wbar : ℝ≥0∞) (hfair : Fair wbar (q - keygenCost + digestAttemptLimit))
    (htotal : 2 * ((q - keygenCost : ℕ) : ℝ) + 2 ≤ spaceReal) :
    Pr[Win | seedFreeExperiment (internalize adversary) q] ≤
      ((1 - budget 0 (q - keygenCost)) + (q - keygenCost : ℕ) * startExcessO wbar (baseline (q - keygenCost))
        (q - keygenCost)) +
      ((q - keygenCost : ℕ) + signatureLimit) * expectedFail := by
  refine le_trans (HiddenBridge.seedFree_le_prep adversary q) ?_
  set A := (1 - budget 0 (q - keygenCost)) + (q - keygenCost : ℕ) * startExcessO wbar (baseline (q - keygenCost))
    (q - keygenCost) with hA
  set C : ℝ≥0∞ := ((q - keygenCost : ℕ) + signatureLimit) with hC
  -- one sample
  have hsample : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) →
      Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining))))
          (knownOf (truncateHash parameterOutput) fixed) prepared.2] ≤ A + C * failMass (failSet prepared.1) := by
    intro parameterOutput fixed highs remaining prepared hprepared
    obtain ⟨tg, hcompat, htrunc, hmsg, hhit⟩ := htarget parameterOutput fixed highs remaining prepared hprepared
    refine le_trans (sample_boundO hb adversary hnr q hq parameterOutput fixed highs remaining prepared hprepared tg hhit
      hcompat htrunc hmsg (hclean _ _ _ _ _ hprepared) (failSet prepared.1)
      (fun m ρ digest budget s1 hprep out hout hnone => finishRest_fail parameterOutput fixed highs remaining prepared
        hprepared tg m ρ digest budget s1 hprep out hout hnone) wbar htotal hfair) (le_of_eq ?_)
    rw [hValueO_start, hA, hC]
    push_cast
    ring
  -- average
  simp only [probEvent_bind_eq_tsum]
  refine le_trans (tsum_bound_le _ _ A C (fun parameterOutput => ∑' fixed, Pr[= fixed | ($ᵗ HiddenGraph.Table : ProbComp HiddenGraph.Table)] *
    ∑' highs, Pr[= highs | ($ᵗ CoordinateHighs : ProbComp CoordinateHighs)] *
    ∑' remaining, Pr[= remaining | ($ᵗ RemainingOutputs : ProbComp RemainingOutputs)] *
    ∑' prepared, Pr[= prepared | preparation parameterOutput fixed highs remaining] *
      failMass (failSet prepared.1)) fun parameterOutput _ => ?_) le_rfl
  refine tsum_bound_le _ _ A C _ fun fixed _ => ?_
  refine tsum_bound_le _ _ A C _ fun highs _ => ?_
  refine tsum_bound_le _ _ A C _ fun remaining _ => ?_
  exact tsum_bound_le _ _ A C _ fun prepared hprepared =>
    hsample parameterOutput fixed highs remaining prepared hprepared

set_option maxRecDepth 100000 in
/-- **Large budgets, deterministic signer.** If the one-coin stage-1 inequality holds at the
adversary's budget after key generation, the deterministic signer's advantage is at most
`q / 2^127`. -/
theorem det_large (hb : 0 < subtreeHeight) (hN : signatureLimit ≤ 2 ^ 70) (adversary : Adversary) (q : ℕ)
    (hbound : Det.HasHashQueryBoundDet adversary q) (hq : q < 2 ^ 127) (hK : keygenCost ≤ q)
    (hH0 : (1 - budget 0 (q - keygenCost)) + ((q - keygenCost : ℕ) : ℝ≥0∞) * H0.hOfO (q - keygenCost) +
        ((q - keygenCost + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q - keygenCost + keygenCost : ℕ) : ℝ≥0∞) / 2 ^ 127) :
    Det.forgeAdvantageDet adversary ≤ q / 2 ^ 127 := by
  set q' := q - keygenCost with hq'
  have hsum : q' + keygenCost = q := by omega
  have hq'le : 2 * q' ≤ 2 ^ 128 := by omega
  have htotal : 2 * ((q' : ℕ) : ℝ) + 2 ≤ spaceReal := by
    unfold spaceReal
    have : (2 * q' + 2 : ℕ) ≤ 2 ^ 128 := by omega
    exact_mod_cast this
  have hmain := stage1_seedFree_boundO hb (Memo.memoAdv adversary) (Memo.memoAdv_noRepeat adversary) q
    (by omega) (fun _ _ _ _ _ hprep => Lifetimes.targetingAll hb _ _ _ _ _ hprep)
    (fun _ _ _ _ _ hprep => prepared_clean _ _ _ _ _ hprep) (H0.wbarOf q') (H0.fair_of q' hq'le) htotal
  refine le_trans (Det.forgeAdvantageDet_le_seedFree adversary q hbound) ?_
  have hE := expectedFail_le
  -- the negligible terms fit in the slack
  have hslack : ((q' : ℝ≥0∞) + signatureLimit) * expectedFail + 2 * ((q : ℝ≥0∞) / 2 ^ 256) ≤
      ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 := by
    have h256 : 2 * ((q : ℝ≥0∞) / 2 ^ 256) ≤ (((q' + keygenCost : ℕ) : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ 201 := by
      rw [div_two_pow, hsum, mul_left_comm]
      refine mul_le_mul' le_rfl ?_
      rw [show (256 : ℕ) = 55 + 201 by norm_num, pow_add, ← mul_assoc]
      calc 2 * (2 : ℝ≥0∞)⁻¹ ^ 55 * (2 : ℝ≥0∞)⁻¹ ^ 201 ≤ 1 * (2 : ℝ≥0∞)⁻¹ ^ 201 := by
            refine mul_le_mul' ?_ le_rfl
            rw [show (55 : ℕ) = 1 + 54 by norm_num, pow_add, pow_one, ← mul_assoc,
              ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
            exact pow_le_one₀ (by norm_num) (by norm_num)
        _ = _ := one_mul _
    have hnat : ((q' : ℝ≥0∞) + signatureLimit) + ((q' + keygenCost : ℕ) : ℝ≥0∞) ≤
        2 * ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) := by
      have h : (q' + signatureLimit) + (q' + keygenCost) ≤ 2 * (q' + keygenCost + signatureLimit) := by omega
      have h' : (((q' + signatureLimit) + (q' + keygenCost) : ℕ) : ℝ≥0∞) ≤
          ((2 * (q' + keygenCost + signatureLimit) : ℕ) : ℝ≥0∞) := by exact_mod_cast h
      push_cast at h' ⊢
      exact h'
    calc _ ≤ ((q' : ℝ≥0∞) + signatureLimit) * (2 : ℝ≥0∞)⁻¹ ^ 201 +
          (((q' + keygenCost : ℕ) : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ 201 := add_le_add (mul_le_mul' le_rfl hE) h256
      _ = (((q' : ℝ≥0∞) + signatureLimit) + ((q' + keygenCost : ℕ) : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ 201 := by
          ring
      _ ≤ (2 * ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ 201 :=
          mul_le_mul' hnat le_rfl
      _ = _ := by rw [mul_comm (2 : ℝ≥0∞), mul_assoc, two_mul_inv_pow_succ]
  calc _ ≤ (((1 - budget 0 q') + (q' : ℝ≥0∞) * startExcessO (H0.wbarOf q') (baseline q') q') +
          ((q' : ℕ) + signatureLimit) * expectedFail) + 2 * ((q : ℝ≥0∞) / 2 ^ 256) := add_le_add hmain le_rfl
    _ = ((1 - budget 0 q') + (q' : ℝ≥0∞) * H0.hOfO q') +
          (((q' : ℝ≥0∞) + signatureLimit) * expectedFail + 2 * ((q : ℝ≥0∞) / 2 ^ 256)) := by
        rw [show startExcessO (H0.wbarOf q') (baseline q') q' = H0.hOfO q' from rfl]
        push_cast
        ring
    _ ≤ ((1 - budget 0 q') + (q' : ℝ≥0∞) * H0.hOfO q') +
          ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 := add_le_add le_rfl hslack
    _ ≤ ((q' + keygenCost : ℕ) : ℝ≥0∞) / 2 ^ 127 := hH0
    _ = (q : ℝ≥0∞) / 2 ^ 127 := by rw [hsum]

end LeanSphincs.Security.ForsPotential
