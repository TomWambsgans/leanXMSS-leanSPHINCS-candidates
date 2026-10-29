import FORS.SWRoute.WeightCoverA
import FORS.SmallBudget.Contact.Signing

/-! **The arming account and the weighted generic signing step.** The SW route's near flag is a
sticky ghost bit, switched on at a step whose input arms (`Arms`, the route's `ArmsAt`: a FORS leaf
query at a near-missing cell). The arming account pays the weight before the step at every step
that switches the flag on (`acctArm`, the route's `WA`). A computation whose ordinary queries avoid
every arming input (a signing call, which asks no FORS leaf query) neither pays nor moves the flag
(`acctArm_bind_avoid`). The weighted signing step of the generic one-coin potential
(`sign_expectGA`) is `sign_expectG_level` with the final weight. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.LoopWalk ForsPotential

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### The arming account -/

section Arm

variable {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate) (wt : State → ℝ≥0∞)
  (Arms : State → CostSpec.Domain → Prop)

/-- The payment of a step: the weight before it, if it switches the flag on. -/
noncomputable def payArm (flag : Bool) (s : State) (input : CostSpec.Domain) : ℝ≥0∞ :=
  if flag = false ∧ Arms s input then wt s else 0

/-- The flag after a step. -/
noncomputable def flagNext (flag : Bool) (s : State) (input : CostSpec.Domain) : Bool :=
  flag || decide (Arms s input)

/-- **The arming account** (`WA`): the expected sum of the weights at the steps that switch the
flag on. -/
noncomputable def acctArm {α : Type} (comp : OracleComp CostSpec α) : ℕ → State → Bool → ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => ℕ → State → Bool → ℝ≥0∞) (fun _ _ _ _ => 0)
    (fun input _ next budget state flag =>
      if sourceCost input ≤ budget then
        ∑' result, Pr[= result | costStep model input state] *
          (payArm wt Arms flag state input +
            next result.1 (budget - sourceCost input) result.2 (flagNext Arms flag state input))
      else 0) comp

theorem acctArm_pure {α : Type} (value : α) (budget : ℕ) (state : State) (flag : Bool) :
    acctArm model wt Arms (pure value : OracleComp CostSpec α) budget state flag = 0 := rfl

theorem acctArm_query_bind {α : Type} (input : CostSpec.Domain)
    (next : CostSpec.Range input → OracleComp CostSpec α) (budget : ℕ) (state : State) (flag : Bool) :
    acctArm model wt Arms (liftM (CostSpec.query input) >>= next) budget state flag =
      if sourceCost input ≤ budget then
        ∑' result, Pr[= result | costStep model input state] *
          (payArm wt Arms flag state input +
            acctArm model wt Arms (next result.1) (budget - sourceCost input) result.2
              (flagNext Arms flag state input))
      else 0 := rfl

theorem payArm_true (s : State) (input : CostSpec.Domain) : payArm wt Arms true s input = 0 := by
  simp [payArm]

theorem flagNext_true (s : State) (input : CostSpec.Domain) : flagNext Arms true s input = true := by
  simp [flagNext]

variable (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)

/-- **A computation avoiding the arming inputs** pays nothing and keeps the flag: the account of a
sequential run is the account of the continuation after it. -/
theorem acctArm_bind_avoid (Q : HashInput → Prop)
    (hQ : ∀ s input, Arms s input → ∃ x, input = .inl (.inr (.inl x)) ∧ Q x) {α β : Type}
    (first : OracleComp CostSpec α) (hav : Avoids Q first) (next : α → OracleComp CostSpec β) :
    ∀ budget (state : State) (flag : Bool),
      acctArm model wt Arms (first >>= next) budget state flag =
        ∑' o1, Pr[= o1 | interp tg initial model first budget state] *
          o1.1.1.elim 0 (fun value => acctArm model wt Arms (next value) (budget - traceCost o1.1.2.2.1) o1.2 flag) := by
  induction first using OracleComp.inductionOn with
  | pure value =>
      intro budget state flag
      rw [pure_bind, interp_pure, tsum_probOutput_pure_mul]
      simp only [Option.elim, traceCost, List.map_nil, List.sum_nil, Nat.sub_zero]
  | query_bind input rest ih =>
      intro budget state flag
      obtain ⟨hin, hrest⟩ := (avoids_query_bind Q input rest).1 hav
      have hno : ∀ s, ¬Arms s input := by
        intro s hs
        obtain ⟨x, rfl, hx⟩ := hQ s _ hs
        exact hin x rfl hx
      have hpay : ∀ s, payArm wt Arms flag s input = 0 := fun s => by simp [payArm, hno s]
      have hflag : ∀ s, flagNext Arms flag s input = flag := fun s => by simp [flagNext, hno s]
      rw [bind_assoc, acctArm_query_bind, interp_query_bind]
      split_ifs with hcost
      · rw [tsum_probOutput_bind_mul]
        refine tsum_congr fun r => ?_
        rw [tsum_probOutput_map_mul, hpay, zero_add, hflag, ih r.1 (hrest r.1) (budget - sourceCost input) r.2 flag]
        congr 1
        refine tsum_congr fun o => ?_
        congr 1
        cases o.1.1 with
        | none => rfl
        | some v =>
            simp only [Option.elim, traceCost_append, recorded_cost, Nat.sub_sub]
      · rw [tsum_probOutput_pure_mul]
        simp

end Arm

/-! ### The weighted signing step of the generic potential -/

section SignG

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate) {wt : State → ℝ≥0∞} (hW : WtSpec model wt IsMsgInput)
  (hcalls : digestCalls = 1)
  (parameter : PublicParameter) (data : PublicData) {W : View → Multiset View → ℝ≥0∞} (wbar b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight))) (m : Message)
include hW hcalls

/-- **The signing step in expectation, weighted**, for the generic potential on a message signed for
the first time. -/
theorem sign_expectGA (hWp : WitnessProps W) (gate : State → Prop)
    (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hb0 : b0 ≠ ⊤) (budget K : ℕ) (s : State) (P : List Pair) (Ms : List Message)
    (L : QueryLog SigningSpec) (hm : MsgLive L m) (d : Multiset View) (hP : PInv parameter data s P)
    (hM : MInv parameter data s Ms) :
    ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (wt out.2 * canonL parameter data W wbar b0 Fail m s P Ms L d gate K out) ≤
      wt s * potG parameter data W wbar b0 Fail gate s P Ms L d K := by
  unfold canonL
  by_cases hcase : gate s ∨ signatureLimit ≤ L.length
  · simp only [if_pos hcase, mul_zero, tsum_zero]
    exact bot_le
  simp only [if_neg hcase]
  have hcase' : ¬gate s ∧ L.length < signatureLimit := by push Not at hcase; exact hcase
  have hlen := hcase'.2
  unfold potG
  rw [if_neg (by rintro (h | h); exact hcase'.1 h; omega)]
  set n := signatureLimit - (L.length + 1) with hn
  have hn1 : signatureLimit - L.length = n + 1 := by omega
  rw [hn1]
  have hparse' : ∀ ρ call, model.parse (GraphView.pblk parameter data m ρ call) = none :=
    fun ρ call => hparse (m, ρ) call
  have hkind' : ∀ ρ call, tg.kind (GraphView.pblk parameter data m ρ call) = .none :=
    fun ρ call => hkind (m, ρ) call
  have hinv : PairInv parameter data m s := fun ρ =>
    ⟨fun h call => hP.first (m, ρ) h call,
      fun u0 h hl call => Option.ne_none_iff_isSome.1 (hP.all (m, ρ) ⟨u0, h, hl⟩ call)⟩
  have hconst := fun c => interp_wt_const tg initial hW (signCostSource parameter data m) budget s c
  have hFN : ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (wt out.2 * freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out) ≤
      wt s * failMass Fail :=
    fresh_expectA tg initial model hW hcalls parameter data m hparse' hkind' s hinv _ budget
  have hT : ∀ q ∈ P, ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (wt out.2 * (if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
        creations Finset.univ landing (fun J => upperO parameter data wbar m s n d (W (pview parameter data s q))
          (restMsgs m L Ms) (· = q) out J) K []) else 0)) ≤
      wt s * candG parameter data W wbar Fail s Ms L d (n + 1) K q := by
    intro q _
    unfold candG
    split_ifs
    · exact hconst 1
    · unfold candValueG
      rw [termO_eq_cons hm hM]
      exact term_expectA tg initial model hW hcalls hparse' hkind' hinv (hWp _) _ _ budget K
    · exact hconst 0
  have hH : ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (wt out.2 * creations Finset.univ landing (fun J => upperO parameter data wbar m s n d (excessW W b0)
        (restMsgs m L Ms) (fun _ => False) out J) K []) ≤
      wt s * hValueG parameter data W wbar b0 s Ms L d (n + 1) K := by
    unfold hValueG
    rw [termO_eq_cons hm hM]
    exact term_expectA tg initial model hW hcalls hparse' hkind' hinv (excessW_props hWp hb0) _ _ budget K
  have hLS : ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (wt out.2 * (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1
        else creations Finset.univ landing (fun J => upperO parameter data wbar m s n d
          (W (pview parameter data s q)) (restMsgs m L Ms) (· = q) out J) K [])
        else 0).sum) ≤
      wt s * (P.map (candG parameter data W wbar Fail s Ms L d (n + 1) K)).sum := by
    simp only [← mul_assoc]
    rw [tsum_list_sum, ← List.sum_map_mul_left]
    exact List.sum_le_sum fun q hq => by simpa only [mul_assoc] using hT q hq
  have hHC : ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (wt out.2 * ((K : ℝ≥0∞) * (creations Finset.univ landing
        (fun J => upperO parameter data wbar m s n d (excessW W b0) (restMsgs m L Ms) (fun _ => False) out J) K [] +
          failMass Fail))) ≤
      wt s * ((K : ℝ≥0∞) * (hValueG parameter data W wbar b0 s Ms L d (n + 1) K + failMass Fail)) := by
    have hpt : ∀ out : Run HashInput Coordinate (Option Signature) × State,
        Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (wt out.2 * ((K : ℝ≥0∞) * (creations Finset.univ landing
            (fun J => upperO parameter data wbar m s n d (excessW W b0) (restMsgs m L Ms) (fun _ => False) out J) K [] +
              failMass Fail))) =
        (K : ℝ≥0∞) * (Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (wt out.2 * creations Finset.univ landing
            (fun J => upperO parameter data wbar m s n d (excessW W b0) (restMsgs m L Ms) (fun _ => False) out J) K [])) +
        (K : ℝ≥0∞) * (Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (wt out.2 * failMass Fail)) := by
      intro out
      ring
    simp only [hpt, ENNReal.tsum_add, ENNReal.tsum_mul_left]
    calc _ ≤ (K : ℝ≥0∞) * (wt s * hValueG parameter data W wbar b0 s Ms L d (n + 1) K) +
          (K : ℝ≥0∞) * (wt s * failMass Fail) :=
          add_le_add (mul_le_mul' le_rfl hH) (mul_le_mul' le_rfl (hconst _))
      _ = _ := by ring
  have hsplit : ∀ out : Run HashInput Coordinate (Option Signature) × State,
      Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (wt out.2 * canonG parameter data W wbar b0 Fail m s P Ms L d n K out) =
      Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (wt out.2 * freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out) +
        Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (wt out.2 * (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1
            else creations Finset.univ landing (fun J => upperO parameter data wbar m s n d
              (W (pview parameter data s q)) (restMsgs m L Ms) (· = q) out J) K [])
            else 0).sum) +
        Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (wt out.2 * ((K : ℝ≥0∞) * (creations Finset.univ landing
            (fun J => upperO parameter data wbar m s n d (excessW W b0) (restMsgs m L Ms) (fun _ => False) out J) K [] +
              failMass Fail))) +
        Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (wt out.2 * ((n : ℝ≥0∞) * failMass Fail)) := by
    intro out
    unfold canonG
    ring
  simp only [hsplit, ENNReal.tsum_add]
  calc _ ≤ wt s * failMass Fail +
        wt s * (P.map (candG parameter data W wbar Fail s Ms L d (n + 1) K)).sum +
        wt s * ((K : ℝ≥0∞) * (hValueG parameter data W wbar b0 s Ms L d (n + 1) K + failMass Fail)) +
        wt s * ((n : ℝ≥0∞) * failMass Fail) :=
        add_le_add (add_le_add (add_le_add hFN hLS) hHC) (hconst _)
    _ = _ := by
        unfold coreG
        push_cast
        ring

end SignG

end FORS.Security.SWRoute
