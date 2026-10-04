import LeanSphincs.BridgeContactSample

/-! The A4 bounds at the fair share `wbarOf y` of the budget `y = q - keygenCost`: A4a costs
`x (N 2^-b 2^-10 + y / (2^128 - y - 2^32))`, and A4b costs `x (y (c + φ) + N φ)` for every rational
`c` certified by `checkNear` for a range containing `y`. Certificates for the parameter sets of the
small-budget plan are checked by the kernel. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-- The near forecast at the fair share is the near H-term. -/
theorem startNear_wbarOf (q : ℕ) : startNear (H0.wbarOf q) q = H0.hNearOf q := rfl

/-- The fair share is fair for the signer's attempts. -/
theorem fair_wbarOf (y : ℕ) (hy : 2 * y ≤ 2 ^ 128) : Fair (H0.wbarOf y) (y + digestAttemptLimit) :=
  H0.fair_of y hy

theorem wbarOf_mul_landing (y : ℕ) : H0.wbarOf y * landing = (((2 ^ 128 - (y + 2 ^ 32) : ℕ) : ℝ≥0∞))⁻¹ := by
  have hland0 : landing ≠ 0 := by
    unfold landing
    exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)
  have hlandT : landing ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top landing_le_one
  unfold H0.wbarOf
  rw [ENNReal.mul_inv (Or.inr hlandT) (Or.inr hland0), mul_assoc, ENNReal.inv_mul_cancel hland0 hlandT, mul_one]

/-- **The start of the near potential** at the fair share, for every budget of a checked range. -/
theorem potNear_start_le_of_check (b N qb m : ℕ) (c : ℚ) (hb : subtreeHeight = b) (hN : signatureLimit = N)
    (hc : H0.checkNear b N qb m c = true) (y : ℕ) (hy : y ≤ qb) (φ : ℝ≥0∞) :
    (y : ℝ≥0∞) * (startNear (H0.wbarOf y) y + φ) + signatureLimit * φ ≤
      y * (ENNReal.ofReal (c : ℝ) + φ) + signatureLimit * φ := by
  rw [startNear_wbarOf]
  gcongr
  exact H0.hNearOf_le_of_check b N qb m c hb hN hc y hy

section Game

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- **Theorem (a) at the fair share.** -/
theorem a4a_bound_fair (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (hq : 2 * (q - keygenCost) ≤ 2 ^ 128)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) (hmsg : ∀ x, IsMsgInput x → tg.kind x = .none)
    (K : HiddenReveal.Knowledge Coordinate) (known : Knowledge Coordinate) :
    Pr[A4aRun (truncateHash parameterOutput) K | interp tg prepared.2 (sampleModel parameterOutput highs)
        (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
          (internalize adversary)) q (DebtState.start prepared.2 known)] ≤
      (((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) *
        (signatureLimit * matchRate +
          (q - keygenCost : ℕ) * (((2 ^ 128 - ((q - keygenCost) + 2 ^ 32) : ℕ) : ℝ≥0∞))⁻¹) := by
  have h := a4a_bound_game adversary hnr q parameterOutput fixed highs remaining prepared hprepared tg hmsg K
    (H0.wbarOf (q - keygenCost)) (fair_wbarOf _ hq) known
  rwa [wbarOf_mul_landing] at h

/-- **Theorem (b) at the fair share, with a certified near H-term.** -/
theorem a4b_bound_check (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (b N qb m : ℕ) (c : ℚ) (hb : subtreeHeight = b) (hN : signatureLimit = N)
    (hc : H0.checkNear b N qb m c = true) (hq : q - keygenCost ≤ qb)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) (hmsg : ∀ x, IsMsgInput x → tg.kind x = .none)
    (K : HiddenReveal.Knowledge Coordinate) (known : Knowledge Coordinate) :
    Pr[A4bRun (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining) K |
        interp tg prepared.2 (sampleModel parameterOutput highs)
          (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
            (internalize adversary)) q (DebtState.start prepared.2 known)] ≤
      (((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) *
        ((q - keygenCost : ℕ) * (ENNReal.ofReal (c : ℝ) + failMass (failSet prepared.1)) +
          signatureLimit * failMass (failSet prepared.1)) := by
  have hqb : 2 * qb ≤ 2 ^ 128 := by
    simp only [H0.checkNear, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1.1.2
  have h := a4b_bound_game adversary hnr q parameterOutput fixed highs remaining prepared hprepared tg hmsg K
    (H0.wbarOf (q - keygenCost)) (fair_wbarOf _ (by omega)) known
  refine le_trans h (mul_le_mul_left' ?_ _)
  exact potNear_start_le_of_check b N qb m c hb hN hc _ hq _

end Game

end LeanSphincs.Security.ForsPotential

namespace LeanSphincs.Security.H0

/-! ### Certificates for the small-budget plan (`plan6.py`, crude mode)

`checkNear b N qb m c`: budgets up to `qb = ⌈x_h 2^128⌉`, rate bound `m / 2^64`, and near H-term at
most `c`, for `(b, N, x_h) = (8, 7190, 2^-9)`, `(10, 27310, 2^-9.25)`, `(12, 103911, 2^-9.5)`,
`(13, 202538, 2^-9.75)`, `(14, 394650, 2^-10)`, `(20, 21455303, 2^-11.75)`, `(26, 1084699946, 2^-19)`. -/

theorem near_cert_b8 : checkNear 8 7190 664613997892457936451903530140172288 518094242145606043653
    (117857123088141077648221455191770359152697 /
      1852673427797059126777135760139006525652319754650249024631321344126610074238976) = true := by
  decide +kernel

theorem near_cert_b10 : checkNear 10 27310 558871528355207643822193711415033856 491973252929037291118
    (184256235868783046423722435757856773018245 /
      1852673427797059126777135760139006525652319754650249024631321344126610074238976) = true := by
  decide +kernel

theorem near_cert_b12 : checkNear 12 103911 469953064781258843736486376135196672 467973547108074448089
    (299306040423913095880824089956133325289869 /
      1852673427797059126777135760139006525652319754650249024631321344126610074238976) = true := by
  decide +kernel

theorem near_cert_b13 : checkNear 13 202538 395181847512057207715720334837547008 456075033282317392559
    (377391752629082831536271784041981868497639 /
      1852673427797059126777135760139006525652319754650249024631321344126610074238976) = true := by
  decide +kernel

theorem near_cert_b14 : checkNear 14 394650 332306998946228968225951765070086144 444336399336027980802
    (237011151584729607487198639962475346008797 /
      926336713898529563388567880069503262826159877325124512315660672063305037119488) = true := by
  decide +kernel

theorem near_cert_b20 : checkNear 20 21455303 98795461878014301928930083709386752 377445682020425827057
    (1726043362193298997612964900623095533854843 /
      1852673427797059126777135760139006525652319754650249024631321344126610074238976) = true := by
  decide +kernel

theorem near_cert_b26 : checkNear 26 1084699946 649037107316853453566312041152512 298160050818750349314
    (503122560686820503488806759720071899290761 /
      463168356949264781694283940034751631413079938662562256157830336031652518559744) = true := by
  decide +kernel

end LeanSphincs.Security.H0
