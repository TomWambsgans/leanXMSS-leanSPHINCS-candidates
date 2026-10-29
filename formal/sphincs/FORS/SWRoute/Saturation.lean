import FORS.SWRoute.Steps
import FORS.SWRoute.NumericFacts

/-! **The S-part of the SW route.** Over any interpreted run from a state satisfying the route's
invariant, the budget at the route's exponent times the weight, the digest payments `β · WF`, the
contact payments `cU · WC` and the final weight times the pending credit are at most the final
weight, the initial weight times the pending credit, the arming costs `δ · WA` and the kills `WK`.
From the start state (weight one, exponent `ρ`, no pending credit):

  `budgetE ρ 0 q' + β/2^128 · WF + cU/2^128 · WC ≤ E[w_end] + δ · WA + WK`. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost PotentialA GraphView ForsPotential

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

section Run

variable (K : Ctx) (root : Digest) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (ρ β δ cU : ℝ)

/-- The expected final weight times the pending credit. -/
noncomputable def endWP {α : Type} (comp : OracleComp CostSpec α) (budget : ℕ) (s : St) : ℝ≥0∞ :=
  ∑' out, Pr[= out | interp K.tg K.initial model comp budget s] * (weightA K root out.2 * pendA K out.2)

theorem costStep_mass (input : CostSpec.Domain) (s : St) :
    ∑' r, Pr[= r | costStep model input s] = 1 :=
  tsum_probOutput_eq_one' probFailure_eq_zero

theorem tsum_add_const_left {γ : Type} (μ : ProbComp γ) (hμ : ∑' x, Pr[= x | μ] = 1) (a : ℝ≥0∞)
    (F : γ → ℝ≥0∞) : ∑' x, Pr[= x | μ] * (a + F x) = a + ∑' x, Pr[= x | μ] * F x := by
  simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hμ, one_mul]

/-- **The S-part over any interpreted run.** -/
theorem sPart_run {total : ℕ} (hN : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (hH : StepHyp K model)
    {α : Type} (comp : OracleComp CostSpec α) :
    ∀ (remaining : ℕ) (s : St) (probes : ℕ) (flag : Bool), InvS K s probes → probes + remaining ≤ total →
      budgetE (expo K ρ flag s) probes remaining * weightA K root s +
          (ENNReal.ofReal (β / 2 ^ 128) * WF model K root comp remaining s +
            ENNReal.ofReal (cU / 2 ^ 128) * WC model K root comp remaining s) +
          endWP K root model comp remaining s ≤
        endW model K root comp remaining s +
          (weightA K root s * pendA K s + ENNReal.ofReal δ * WA model K root comp remaining s flag +
            WK model K root comp remaining s) := by
  have htot : (total : ℝ) < spaceReal := hN.total_lt_space
  have hρ0 : ∀ flag s, 0 ≤ expo K ρ flag s := by
    intro flag s
    unfold expo
    have := hN.low
    split_ifs <;> linarith
  -- the end of a run
  have hend : ∀ (remaining : ℕ) (s : St) (probes : ℕ) (flag : Bool), probes + remaining ≤ total →
      budgetE (expo K ρ flag s) probes remaining * weightA K root s + 0 + weightA K root s * pendA K s ≤
        weightA K root s + (weightA K root s * pendA K s + 0 + 0) := by
    intro remaining s probes flag hsum
    have hb : budgetE (expo K ρ flag s) probes remaining ≤ 1 := by
      refine budgetE_le_one (hρ0 flag s) probes remaining ?_
      have : ((probes + remaining : ℕ) : ℝ) ≤ total := by exact_mod_cast hsum
      push_cast at this
      linarith
    rw [add_zero, add_zero, add_zero]
    exact add_le_add (mul_le_of_le_one_left' hb) le_rfl
  induction comp using OracleComp.inductionOn with
  | pure value =>
      intro remaining s probes flag _ hsum
      simp only [WF, WC, WK, WA, acct_pure, acctA_pure, endW, endWP, interp_pure, tsum_probOutput_pure_mul,
        mul_zero, add_zero]
      have := hend remaining s probes flag hsum
      simpa using this
  | query_bind input next ih =>
      intro remaining s probes flag hinv hsum
      by_cases hcost : sourceCost input ≤ remaining
      swap
      · simp only [WF, WC, WK, WA, endW, endWP]
        rw [acct_query_bind, acct_query_bind, acct_query_bind, acctA_query_bind, interp_query_bind,
          if_neg hcost, if_neg hcost, if_neg hcost, if_neg hcost, if_neg hcost, tsum_probOutput_pure_mul,
          tsum_probOutput_pure_mul]
        simp only [mul_zero, add_zero]
        have := hend remaining s probes flag hsum
        simpa using this
      obtain ⟨probes', hsum', hinv', hstep⟩ :=
        sStep K root model ρ β δ cU hN hH input s flag probes remaining hinv hcost hsum
      set step := costStep model input s with hstepdef
      have hmass : ∑' r, Pr[= r | step] = 1 := costStep_mass model input s
      set R := remaining - sourceCost input with hR
      set fl' := nextFlag K root flag s input with hfl'
      have hWF : WF model K root (liftM (CostSpec.query input) >>= next) remaining s =
          payF K root s input + ∑' r, Pr[= r | step] * WF model K root (next r.1) R r.2 := by
        simp only [WF]
        rw [acct_query_bind, if_pos hcost, tsum_add_const_left step hmass]
      have hWC : WC model K root (liftM (CostSpec.query input) >>= next) remaining s =
          payC K root s input + ∑' r, Pr[= r | step] * WC model K root (next r.1) R r.2 := by
        simp only [WC]
        rw [acct_query_bind, if_pos hcost, tsum_add_const_left step hmass]
      have hWA : WA model K root (liftM (CostSpec.query input) >>= next) remaining s flag =
          payA K root flag s input + ∑' r, Pr[= r | step] * WA model K root (next r.1) R r.2 fl' := by
        simp only [WA]
        rw [acctA_query_bind, if_pos hcost, tsum_add_const_left step hmass]
      have hWK : WK model K root (liftM (CostSpec.query input) >>= next) remaining s =
          ∑' r, Pr[= r | step] * payK K root s input r.2 +
            ∑' r, Pr[= r | step] * WK model K root (next r.1) R r.2 := by
        simp only [WK]
        rw [acct_query_bind, if_pos hcost, ← ENNReal.tsum_add]
        simp only [mul_add]
        rfl
      have hEW : endW model K root (liftM (CostSpec.query input) >>= next) remaining s =
          ∑' r, Pr[= r | step] * endW model K root (next r.1) R r.2 := by
        simp only [endW]
        rw [interp_query_bind, if_pos hcost, tsum_probOutput_bind_mul]
        simp only [tsum_probOutput_map_mul]
        rfl
      have hEWP : endWP K root model (liftM (CostSpec.query input) >>= next) remaining s =
          ∑' r, Pr[= r | step] * endWP K root model (next r.1) R r.2 := by
        simp only [endWP]
        rw [interp_query_bind, if_pos hcost, tsum_probOutput_bind_mul]
        simp only [tsum_probOutput_map_mul]
        rfl
      rw [hWF, hWC, hWA, hWK, hEW, hEWP]
      have hrest : ∀ r ∈ support step,
          budgetE (expo K ρ fl' r.2) probes' R * weightA K root r.2 +
              (ENNReal.ofReal (β / 2 ^ 128) * WF model K root (next r.1) R r.2 +
                ENNReal.ofReal (cU / 2 ^ 128) * WC model K root (next r.1) R r.2) +
              endWP K root model (next r.1) R r.2 ≤
            endW model K root (next r.1) R r.2 + weightA K root r.2 * pendA K r.2 +
              (ENNReal.ofReal δ * WA model K root (next r.1) R r.2 fl' + WK model K root (next r.1) R r.2) := by
        intro r hr
        have h := ih r.1 R r.2 probes' fl' (hinv' r hr) hsum'
        refine h.trans (le_of_eq ?_)
        ring
      have hfin : ∑' r, Pr[= r | step] * (weightA K root r.2 * pendA K r.2) ≠ ⊤ := by
        refine ne_top_of_le_ne_top (b := ∑' r, Pr[= r | step] * (1 * (ν / 2 * (probes' : ℝ≥0∞)))) ?_ ?_
        · rw [ENNReal.tsum_mul_right, hmass, one_mul, one_mul]
          exact ENNReal.mul_ne_top (ENNReal.div_ne_top ν_ne_top (by norm_num)) (ENNReal.natCast_ne_top _)
        · refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support step
          · refine mul_le_mul_right (mul_le_mul' (weightA_le_one K root r.2) ?_) _
            refine (pendA_le K r.2).trans (mul_le_mul_right ?_ _)
            exact_mod_cast (hinv' r hr).ua
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      have hc := combineS step (budgetE (expo K ρ flag s) probes remaining * weightA K root s)
        (ENNReal.ofReal (β / 2 ^ 128) * payF K root s input + ENNReal.ofReal (cU / 2 ^ 128) * payC K root s input)
        (weightA K root s * pendA K s + ENNReal.ofReal δ * payA K root flag s input +
          ∑' r, Pr[= r | step] * payK K root s input r.2)
        (fun r => weightA K root r.2 * pendA K r.2)
        (fun r => budgetE (expo K ρ fl' r.2) probes' R * weightA K root r.2)
        (fun r => ENNReal.ofReal (β / 2 ^ 128) * WF model K root (next r.1) R r.2 +
          ENNReal.ofReal (cU / 2 ^ 128) * WC model K root (next r.1) R r.2)
        (fun r => endWP K root model (next r.1) R r.2)
        (fun r => endW model K root (next r.1) R r.2)
        (fun r => ENNReal.ofReal δ * WA model K root (next r.1) R r.2 fl' + WK model K root (next r.1) R r.2)
        hstep hrest hfin
      have e2 : ∀ (a b : ℝ≥0∞) (F G : _ → ℝ≥0∞), ∑' r, Pr[= r | step] * (a * F r + b * G r) =
          a * ∑' r, Pr[= r | step] * F r + b * ∑' r, Pr[= r | step] * G r := by
        intro a b F G
        simp only [mul_add, ENNReal.tsum_add, mul_left_comm _ a, mul_left_comm _ b, ENNReal.tsum_mul_left]
      have e3 : ∀ (a : ℝ≥0∞) (F G : _ → ℝ≥0∞), ∑' r, Pr[= r | step] * (a * F r + G r) =
          a * ∑' r, Pr[= r | step] * F r + ∑' r, Pr[= r | step] * G r := by
        intro a F G
        simp only [mul_add, ENNReal.tsum_add, mul_left_comm _ a, ENNReal.tsum_mul_left]
      rw [e2, e3] at hc
      refine le_trans (le_of_eq ?_) (hc.trans (le_of_eq ?_))
      · ring
      · ring

end Run

end FORS.Security.SWRoute
