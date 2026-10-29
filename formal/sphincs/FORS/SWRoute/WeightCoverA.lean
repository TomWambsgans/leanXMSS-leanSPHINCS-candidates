import FORS.SWRoute.WeightScanA

/-! **The weighted one-coin cover potential, for an abstract weight.** `LargeBudget/WeightedPotential`
with the survival weight replaced by a weight `wt` with `WtSpec … IsMsgInput` (the route's `weightA`)
and the weighted digest payments by the account `wcount … tg.digest` (the route's `WF`): the final
value of a run (a FORS cover of a cached landed unsigned digest) weighted by the final weight is paid by
the start potential times the start weight and the baseline per weighted digest query (`goodWA_advProg`). -/

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

/-! ### Signing a message for the first time, weighted -/

section SignScanW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate) {wt : State → ℝ≥0∞} (hW : WtSpec model wt IsMsgInput)
  (hcalls : digestCalls = 1)
  (parameter : PublicParameter) (data : PublicData) (m : Message)
include hW hcalls

/-- **One signing call, one term, weighted** (the weighted `sign_term`). Averaged over the uniform
start and the scan, the weighted upper value of a monotone function of the disclosures is at most the
initial weight times the group of the message applied to that function after one fresh slot. -/
theorem upper_expectA (hparse : ∀ ρ call, model.parse (GraphView.pblk parameter data m ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (GraphView.pblk parameter data m ρ call) = .none)
    {X : Multiset View → ℝ≥0∞} (hX : Monotone' X) (s : State)
    (hinv : PairInv parameter data m s) (d : Multiset View)
    (excl : Pair → Prop) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (wt out.2 *
          (X d + (freshNewWeight parameter data m s (fun v => X (d + {v}) - X d) out +
            outWeight parameter data m s 0 (fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d) out))) ≤
      wt s *
        grpM parameter data s excl m (fun e => freshAvg Finset.univ fun v => X (e + {v})) d := by
  refine le_trans ?_ (mul_le_mul' le_rfl (ForsPotential.walk_avg_le_grpM parameter data m hX s d excl))
  set gf : View → ℝ≥0∞ := fun v => X (d + {v}) - X d with hgf
  set gp : Randomness → View → ℝ≥0∞ := fun ρ v => if excl (m, ρ) then 0 else X (d + {v}) - X d with hgp
  set c := (Fintype.card Randomness : ℝ≥0∞)⁻¹ with hc
  have hscan : ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (wt out.2 *
          (freshNewWeight parameter data m s gf out + outWeight parameter data m s 0 gp out)) ≤
      wt s * (c * ∑ start, walk (nextRand (data.steps m)) landing (stOf parameter data m s)
        (poolValue parameter data m s gp) (freshAvg Finset.univ gf) 0 digestAttemptLimit start) := by
    unfold signCostSource
    rw [interp_liftProb_bind, tsum_probOutput_bind_mul]
    have hpr : ∀ ρ, Pr[= ρ | ($ᵗ Randomness : ProbComp Randomness)] = c := by
      intro ρ
      rw [probOutput_uniformSample]
    simp only [hpr]
    rw [ENNReal.tsum_mul_left, tsum_fintype]
    refine le_trans (mul_le_mul' le_rfl (Finset.sum_le_sum fun start _ =>
      loop_bound_combSA tg initial hW hcalls parameter data m hparse hkind s gf gp digestAttemptLimit
        (by unfold digestAttemptLimit; norm_num) budget s start (fun _ => Or.inl rfl) hinv
          (fun _ _ _ => rfl)))
      (le_of_eq ?_)
    rw [← Finset.mul_sum, mul_left_comm]
  rw [mul_add]
  refine le_trans (le_of_eq ?_) (add_le_add
    (interp_wt_const tg initial hW (signCostSource parameter data m) budget s (X d)) hscan)
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun out => by ring

/-- The fresh pair completed by a signing call weighs at most its fresh average, weighted. -/
theorem fresh_expectA (hparse : ∀ ρ call, model.parse (GraphView.pblk parameter data m ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (GraphView.pblk parameter data m ρ call) = .none) (s : State)
    (hinv : PairInv parameter data m s) (gf : View → ℝ≥0∞) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (wt out.2 * freshNewWeight parameter data m s gf out) ≤
      wt s * freshAvg Finset.univ gf := by
  unfold signCostSource
  rw [interp_liftProb_bind, tsum_probOutput_bind_mul]
  have hstart : ∀ start : Randomness, ∑' out, Pr[= out | interp tg initial model
      (signCostSourceLoop parameter data m (data.step m) digestAttemptLimit start) budget s] *
      (wt out.2 * freshNewWeight parameter data m s gf out) ≤
      wt s * freshAvg Finset.univ gf := by
    intro start
    have h := loop_bound_combSA tg initial hW hcalls parameter data m hparse hkind s gf (fun _ _ => 0)
      digestAttemptLimit (by unfold digestAttemptLimit; norm_num) budget s start (fun _ => Or.inl rfl)
      hinv (fun _ _ _ => rfl)
    refine le_trans (ENNReal.tsum_le_tsum fun out => mul_le_mul' le_rfl (mul_le_mul' le_rfl le_self_add))
      (le_trans h (mul_le_mul' le_rfl ?_))
    refine walk_le ForsPrice.landing_le_one _ (fun ρ => ?_) le_rfl bot_le _ start
    unfold poolValue
    cases pcache parameter data m s ρ <;> simp
  calc _ ≤ ∑' start, Pr[= start | ($ᵗ Randomness : ProbComp Randomness)] *
        (wt s * freshAvg Finset.univ gf) :=
        ENNReal.tsum_le_tsum fun start => mul_le_mul' le_rfl (hstart start)
    _ ≤ _ := by rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one

end SignScanW

section SignExpectW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate) {wt : State → ℝ≥0∞} (hW : WtSpec model wt IsMsgInput)
  (hcalls : digestCalls = 1)
  {parameter : PublicParameter} {data : PublicData} {w : ℝ≥0∞} {m : Message} {s : State} {n : ℕ}
  {d : Multiset View} {f : Multiset View → ℝ≥0∞}
include hW hcalls

/-- **A dominated term, weighted.** -/
theorem term_expectA (hparse : ∀ ρ call, model.parse (GraphView.pblk parameter data m ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (GraphView.pblk parameter data m ρ call) = .none)
    (hinv : PairInv parameter data m s)
    (hf : MonoFin f) (rest : List Message) (excl : Pair → Prop) (budget k : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (wt out.2 *
          creations Finset.univ landing (fun J => upperO parameter data w m s n d f rest excl out J) k []) ≤
      wt s * creations Finset.univ landing (fun J => grpAll parameter data s excl (m :: rest)
        (virtualOnce Finset.univ w f (n + 1) J) d) k [] := by
  simp only [← mul_assoc]
  rw [creations_tsum, ← creations_const_mul]
  refine creations_mono (fun J => ?_) k []
  simp only [mul_assoc]
  have hX : Monotone' (restBase parameter data w s n f rest excl J) :=
    grpAll_mono s excl (virtualOnce_mono hf.1 n J) rest
  refine le_trans (upper_expectA tg initial model hW hcalls parameter data m hparse hkind hX s hinv d excl budget)
    (mul_le_mul' le_rfl (le_of_eq ?_))
  simp only [grpAll]
  refine grp_congr _ _ (fun e => ?_) d
  unfold restBase
  symm
  rw [grpAll_congr s excl (virtualOnce_succ_nil J) rest e, grpAll_freshAvg]
  congr 1
  funext v
  exact grpAll_shift s excl _ {v} rest e

end SignExpectW

section SignPointW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate) {wt : State → ℝ≥0∞} (hW : WtSpec model wt IsMsgInput)
  (hcalls : digestCalls = 1)
  (parameter : PublicParameter) (data : PublicData) (w b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ) (m : Message)
include hW hcalls

/-- **The signing step in expectation, weighted**, for a message signed for the first time. -/
theorem sign_expectA (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (budget : ℕ) (s : State) (P : List Pair) (Ms : List Message)
    (L : QueryLog SigningSpec) (hm : MsgLive L m) (d : Multiset View)
    (hP : PInv parameter data s P) (hM : MInv parameter data s Ms) :
    ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (wt out.2 * (if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
          else canonO parameter data w b0 Fail m s P Ms L d (signatureLimit - (L.length + 1)) budget out)) ≤
      wt s * (if Realized tg initial s ∨ signatureLimit < L.length then 0
        else coreO parameter data w b0 Fail s P Ms L d (signatureLimit - L.length) budget) := by
  by_cases hcase : Realized tg initial s ∨ signatureLimit ≤ L.length
  · simp only [if_pos hcase, mul_zero, tsum_zero]
    exact bot_le
  simp only [if_neg hcase]
  have hcase' : ¬Realized tg initial s ∧ L.length < signatureLimit := by push Not at hcase; exact hcase
  have hlen := hcase'.2
  rw [if_neg (by rintro (h | h); exact hcase'.1 h; omega)]
  set n := signatureLimit - (L.length + 1) with hn
  have hn1 : signatureLimit - L.length = n + 1 := by omega
  rw [hn1]
  have hparse' : ∀ ρ call, model.parse (GraphView.pblk parameter data m ρ call) = none :=
    fun ρ call => hparse (m, ρ) call
  have hkind' : ∀ ρ call, tg.kind (GraphView.pblk parameter data m ρ call) = .none :=
    fun ρ call => hkind (m, ρ) call
  -- the pair invariant of the state, from `PInv.first` and `PInv.all` at `(m, ρ)`
  have hinv : PairInv parameter data m s := fun ρ =>
    ⟨fun h call => hP.first (m, ρ) h call,
      fun u0 h hl call => Option.ne_none_iff_isSome.1 (hP.all (m, ρ) ⟨u0, h, hl⟩ call)⟩
  have hconst := fun c => interp_wt_const tg initial hW
    (signCostSource parameter data m) budget s c
  have hFN : ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (wt out.2 * freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out) ≤
      wt s * failMass Fail :=
    fresh_expectA tg initial model hW hcalls parameter data m hparse' hkind' s hinv _ budget
  have hT : ∀ q ∈ P, ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (wt out.2 * (if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
        creations Finset.univ landing (fun J => upperO parameter data w m s n d (witnessFn (pview parameter data s q))
          (restMsgs m L Ms) (· = q) out J) budget []) else 0)) ≤
      wt s * candO parameter data w Fail s Ms L d (n + 1) budget q := by
    intro q _
    unfold candO
    split_ifs
    · exact hconst 1
    · unfold candValueO
      rw [termO_eq_cons hm hM]
      exact term_expectA tg initial model hW hcalls hparse' hkind' hinv (witness_props _) _ _ budget budget
    · exact hconst 0
  have hH : ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (wt out.2 * creations Finset.univ landing (fun J => upperO parameter data w m s n d (excess b0)
        (restMsgs m L Ms) (fun _ => False) out J) budget []) ≤
      wt s * hValueO parameter data w b0 s Ms L d (n + 1) budget := by
    unfold hValueO
    rw [termO_eq_cons hm hM]
    exact term_expectA tg initial model hW hcalls hparse' hkind' hinv (excess_props b0) _ _ budget budget
  have hLS : ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (wt out.2 * (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1
        else creations Finset.univ landing (fun J => upperO parameter data w m s n d
          (witnessFn (pview parameter data s q)) (restMsgs m L Ms) (· = q) out J) budget [])
        else 0).sum) ≤
      wt s * (P.map (candO parameter data w Fail s Ms L d (n + 1) budget)).sum := by
    simp only [← mul_assoc]
    rw [tsum_list_sum, ← List.sum_map_mul_left]
    exact List.sum_le_sum fun q hq => by simpa only [mul_assoc] using hT q hq
  have hHC : ∑' out, Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
      (wt out.2 * ((budget : ℝ≥0∞) * (creations Finset.univ landing
        (fun J => upperO parameter data w m s n d (excess b0) (restMsgs m L Ms) (fun _ => False) out J) budget [] +
          failMass Fail))) ≤
      wt s * ((budget : ℝ≥0∞) * (hValueO parameter data w b0 s Ms L d (n + 1) budget +
        failMass Fail)) := by
    have hpt : ∀ out : Run HashInput Coordinate (Option Signature) × State,
        Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (wt out.2 * ((budget : ℝ≥0∞) * (creations Finset.univ landing
            (fun J => upperO parameter data w m s n d (excess b0) (restMsgs m L Ms) (fun _ => False) out J) budget [] +
              failMass Fail))) =
        (budget : ℝ≥0∞) * (Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (wt out.2 * creations Finset.univ landing
            (fun J => upperO parameter data w m s n d (excess b0) (restMsgs m L Ms) (fun _ => False) out J) budget [])) +
        (budget : ℝ≥0∞) * (Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (wt out.2 * failMass Fail)) := by
      intro out
      ring
    simp only [hpt, ENNReal.tsum_add, ENNReal.tsum_mul_left]
    calc _ ≤ (budget : ℝ≥0∞) * (wt s * hValueO parameter data w b0 s Ms L d (n + 1) budget) +
          (budget : ℝ≥0∞) * (wt s * failMass Fail) :=
          add_le_add (mul_le_mul' le_rfl hH) (mul_le_mul' le_rfl (hconst _))
      _ = _ := by ring
  have hsplit : ∀ out : Run HashInput Coordinate (Option Signature) × State,
      Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
        (wt out.2 * canonO parameter data w b0 Fail m s P Ms L d n budget out) =
      Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (wt out.2 * freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out) +
        Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (wt out.2 * (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1
            else creations Finset.univ landing (fun J => upperO parameter data w m s n d
              (witnessFn (pview parameter data s q)) (restMsgs m L Ms) (· = q) out J) budget [])
            else 0).sum) +
        Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (wt out.2 * ((budget : ℝ≥0∞) * (creations Finset.univ landing
            (fun J => upperO parameter data w m s n d (excess b0) (restMsgs m L Ms) (fun _ => False) out J) budget [] +
              failMass Fail))) +
        Pr[= out | interp tg initial model (signCostSource parameter data m) budget s] *
          (wt out.2 * ((n : ℝ≥0∞) * failMass Fail)) := by
    intro out
    unfold canonO
    ring
  simp only [hsplit, ENNReal.tsum_add]
  calc _ ≤ wt s * failMass Fail +
        wt s * (P.map (candO parameter data w Fail s Ms L d (n + 1) budget)).sum +
        wt s * ((budget : ℝ≥0∞) * (hValueO parameter data w b0 s Ms L d (n + 1) budget +
          failMass Fail)) + wt s * ((n : ℝ≥0∞) * failMass Fail) :=
        add_le_add (add_le_add (add_le_add hFN hLS) hHC) (hconst _)
    _ = _ := by
        unfold coreO
        push_cast
        ring

end SignPointW

/-! ### Weighted paid programs -/

section GoodWA

variable (parameter : PublicParameter) (data : PublicData) (w b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot Lmax : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (wt : State → ℝ≥0∞)

/-- A program whose final value, weighted by the final survival weight, is paid by the weighted
potential and the weighted baseline payments. -/
def GoodWA (L : QueryLog SigningSpec) (prog : OracleComp CostSpec HiddenBridge.Outcome) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View) (R : List Coordinate),
    Prepared initial s → PInv parameter data s P → MInv parameter data s Ms → DInv R d →
      CountInv parameter data Qtot s budget →
      ∑' out, Pr[= out | interp tg initial model prog budget s] *
          (wt out.2 * finalValue parameter data tg initial R out) ≤
        wt s * potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
          b0 * wcount model wt tg.digest prog budget s

variable {wt} (hW : WtSpec model wt IsMsgInput) (hcalls : digestCalls = 1)
include hW hcalls

/-- The weighted final value is at most the initial weight in the mean. -/
theorem finalWA_le (prog : OracleComp CostSpec HiddenBridge.Outcome) (budget : ℕ) (s : State) (R : List Coordinate) :
    ∑' out, Pr[= out | interp tg initial model prog budget s] *
        (wt out.2 * finalValue parameter data tg initial R out) ≤ wt s := by
  refine le_trans (interp_wt_mul_le tg initial hW prog budget s _ 1 fun out _ => ?_) (mul_one _).le
  unfold finalValue
  cases out.1.1 with
  | none => exact zero_le_one
  | some outcome =>
      simp only [Option.elim]
      split_ifs
      · exact le_rfl
      · exact zero_le_one

theorem goodWA_draw (L : QueryLog SigningSpec) (draw : ℕ)
    (next : Fin (draw + 1) → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodWA parameter data w b0 Fail Qtot Lmax tg initial model wt L (next v)) :
    GoodWA parameter data w b0 Fail Qtot Lmax tg initial model wt L
      (liftM (CostSpec.query (.inl (.inl draw))) >>= next) := by
  intro budget s P Ms d R hprep hP hM hD hC
  have hw : wcount model wt tg.digest (liftM (CostSpec.query (.inl (.inl draw))) >>= next) budget s =
      ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
        wcount model wt tg.digest (next v) budget s := by
    rw [wcount_query_bind]
    refine (if_pos (Nat.zero_le budget)).trans ?_
    change ∑' r, Pr[= r | (fun v => (v, s)) <$> (liftM (unifSpec.query draw) : ProbComp _)] *
      (0 + wcount model wt tg.digest (next r.1) (budget - 0) r.2) = _
    rw [tsum_probOutput_map_mul]
    simp only [zero_add, Nat.sub_zero]
  rw [hw, interp_draw, tsum_probOutput_bind_mul]
  calc _ ≤ ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
        (wt s * potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
          b0 * wcount model wt tg.digest (next v) budget s) :=
        ENNReal.tsum_le_tsum fun v => mul_le_mul_right (h v budget s P Ms d R hprep hP hM hD hC) _
    _ ≤ _ := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
        refine add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) (le_of_eq ?_)
        simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

theorem finalValueWA_ordinary (R : List Coordinate) (x : HashInput)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome) (budget : ℕ) (hb : 1 ≤ budget) (s : State) :
    ∑' out, Pr[= out | interp tg initial model (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) budget s] *
        (wt out.2 * finalValue parameter data tg initial R out) =
      ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        ∑' out, Pr[= out | interp tg initial model (next r.1) (budget - 1) r.2] *
          (wt out.2 * finalValue parameter data tg initial R out) := by
  rw [interp_ordinary, if_pos hb, tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_map_mul]
  rfl

theorem wcountD_ordinary (x : HashInput) (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) :
    wcount model wt tg.digest (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) budget s =
      ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        (wpaysA wt tg.digest s (.inl (.inr (.inl x))) + wcount model wt tg.digest (next r.1) (budget - 1) r.2) := by
  rw [wcount_query_bind, costStep_ordinary]
  exact if_pos hb

/-- A new pair: one of its blocks is read fresh and the others are presampled, weighted. The blocks
are message-digest inputs, so the presample keeps both the weight and the weighted
payments. -/
theorem new_pair_boundWA {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot ≤ Cmax) (L : QueryLog SigningSpec)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodWA parameter data w b0 Fail Qtot Lmax tg initial model wt L (next v))
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View)
    (R : List Coordinate) (hprep : Prepared initial s) (hP : PInv parameter data s P)
    (hM : MInv parameter data s Ms) (hD : DInv R d)
    (hC : CountInv parameter data Qtot s budget) (p : Pair) (c : DigestCall)
    (_hkind : ∀ call, tg.kind (pblk parameter data p call) = .none)
    (hp0 : s.cache (pblk parameter data p firstCall) = none) :
    ∑' v, Pr[= v | ($ᵗ HashOutput : ProbComp HashOutput)] *
        ∑' out, Pr[= out | interp tg initial model (next v) (budget - 1)
          (s.store (pblk parameter data p c) v)] *
          (wt out.2 * finalValue parameter data tg initial R out) ≤
      wt s * potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
        b0 * (wt s +
          ∑' v, Pr[= v | ($ᵗ HashOutput : ProbComp HashOutput)] *
            wcount model wt tg.digest (next v) (budget - 1) (s.store (pblk parameter data p c) v)) := by
  set ℓ := (livePairs L P).length with hℓ
  have hfresh : ∀ call, s.cache (pblk parameter data p call) = none := hP.first p hp0
  have hdig : ∀ call, IsMsgInput (pblk parameter data p call) := fun call =>
    msgInput_digestInput parameter data.root p.1 p.2 call
  have hwall : ∀ u : DigestCall → HashOutput,
      wt (withPair parameter data s p u) ≤ wt s := fun u =>
    wt_storeAll_le hW (pblk parameter data p) u s (pblk_call_injective parameter data p) hdig hfresh
  have hpairE : ∀ F : (DigestCall → HashOutput) → ℝ≥0∞,
      pairE F = ((Fintype.card HashOutput : ℝ≥0∞) ^ digestCalls)⁻¹ * ∑ u, F u := by
    intro F
    unfold pairE
    rw [tsum_uniform_eq, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  have hpre : ∑' v, Pr[= v | ($ᵗ HashOutput : ProbComp HashOutput)] *
        ∑' out, Pr[= out | interp tg initial model (next v) (budget - 1)
          (s.store (pblk parameter data p c) v)] *
          (wt out.2 * finalValue parameter data tg initial R out) ≤
      pairE (fun u => ∑' out, Pr[= out | interp tg initial model (next (u c)) (budget - 1)
        (withPair parameter data s p u)] *
          (wt out.2 * finalValue parameter data tg initial R out)) := by
    rw [hpairE]
    exact le_of_eq (presample_one hcalls (pblk parameter data p) c s (fun v s' =>
      ∑' out, Pr[= out | interp tg initial model (next v) (budget - 1) s'] *
        (wt out.2 * finalValue parameter data tg initial R out)))
  have hcount : pairE (fun u => wcount model wt tg.digest (next (u c)) (budget - 1)
        (withPair parameter data s p u)) =
      ∑' v, Pr[= v | ($ᵗ HashOutput : ProbComp HashOutput)] *
        wcount model wt tg.digest (next v) (budget - 1) (s.store (pblk parameter data p c) v) := by
    rw [hpairE]
    exact (presample_one hcalls (pblk parameter data p) c s (fun v s' =>
      wcount model wt tg.digest (next v) (budget - 1) s')).symm
  by_cases hcap : 1 ≤ lam Lmax ℓ budget
  · -- more landed pairs than the cap: the cap term pays everything
    calc _ ≤ ∑' v, Pr[= v | ($ᵗ HashOutput : ProbComp HashOutput)] * wt s :=
          ENNReal.tsum_le_tsum fun v => mul_le_mul_right
            ((finalWA_le parameter data tg initial model hW hcalls (next v) (budget - 1) _ R).trans
              (hW.store_le s _ v (hdig c) (hfresh c))) _
      _ ≤ wt s := by
          rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one
      _ ≤ wt s * lam Lmax ℓ budget := le_mul_of_one_le_right' hcap
      _ ≤ _ := by
          unfold potO
          exact le_trans (mul_le_mul' le_rfl le_add_self) le_self_add
  have hlen : ℓ ≤ Lmax := by
    by_contra hlt
    exact hcap (one_le_lam (by omega) budget)
  have hrate : MsgLive L p.1 → Rate parameter data w s p.1 := fun hlive =>
    rate_of_fair hfair s p.1 (by have := hC p.1; omega) (le_trans (landedCount_le hP L hlive) hlen)
  have hC2 : ∀ a, CountInv parameter data Qtot (withPair parameter data s p a) (budget - 1) := by
    intro a mm
    have h1 := count_withPair (parameter := parameter) (data := data) mm s p a
    have h2 := hC mm
    omega
  have hone : ∀ u, ∑' out, Pr[= out | interp tg initial model (next (u c)) (budget - 1)
        (withPair parameter data s p u)] *
          (wt out.2 * finalValue parameter data tg initial R out) ≤
      wt s * potO parameter data w b0 Fail tg initial Lmax (withPair parameter data s p u)
          (addPair parameter P p u) (addMsg Ms p.1) L d (budget - 1) +
        b0 * wcount model wt tg.digest (next (u c)) (budget - 1) (withPair parameter data s p u) := fun u => by
    have := h (u c) (budget - 1) _ _ _ d R
      (fun x v hx => (extends_withPair hP hp0 u).1 x v (hprep x v hx)) (pinv_withPair hP hp0 u)
      (minv_withPair hM p u) hD (hC2 u)
    exact this.trans (add_le_add (mul_le_mul' (hwall u) le_rfl) le_rfl)
  refine le_trans (le_trans hpre (pairE_mono hone)) ?_
  rw [pairE_add, pairE_const_mul, pairE_const_mul, hcount, mul_add, ← add_assoc]
  refine add_le_add ?_ le_rfl
  calc wt s * pairE (fun u => potO parameter data w b0 Fail tg initial Lmax
          (withPair parameter data s p u) (addPair parameter P p u) (addMsg Ms p.1) L d (budget - 1))
      ≤ wt s * (potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
          b0 * (if Realized tg initial s then 0 else 1)) :=
        mul_le_mul_right (new_pair_core parameter data w b0 Fail Lmax tg initial hfair.le_one L budget hb s P Ms d
          hP hM p hp0 hrate) _
    _ ≤ _ := by
        rw [mul_add]
        refine add_le_add le_rfl ?_
        rw [mul_left_comm]
        refine mul_le_mul_right ?_ _
        split_ifs <;> simp

/-- **One ordinary query, weighted.** -/
theorem goodWA_ordinary (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot ≤ Cmax) (L : QueryLog SigningSpec) (x : HashInput)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodWA parameter data w b0 Fail Qtot Lmax tg initial model wt L (next v)) :
    GoodWA parameter data w b0 Fail Qtot Lmax tg initial model wt L
      (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) := by
  intro budget s P Ms d R hprep hP hM hD hC
  by_cases hb : 1 ≤ budget
  swap
  · rw [interp_ordinary, if_neg hb, tsum_probOutput_pure_mul, finalValue_abort, mul_zero]
    exact bot_le
  rw [finalValueWA_ordinary parameter data tg initial model hW hcalls R x next budget hb s,
    wcountD_ordinary tg model hW hcalls x next budget hb s]
  by_cases hnew : ∃ (p : Pair) (call : DigestCall), x = pblk parameter data p call ∧
      s.cache (pblk parameter data p firstCall) = none
  · obtain ⟨p, c, rfl, hp0⟩ := hnew
    have hfresh : ∀ call, s.cache (pblk parameter data p call) = none := hP.first p hp0
    rw [ordinaryStep, hparse p c]
    simp only
    rw [readOutside_fresh _ s (hfresh c), tsum_probOutput_map_mul, tsum_probOutput_map_mul]
    have hpay : wpaysA wt tg.digest s (.inl (.inr (.inl (pblk parameter data p c)))) = wt s := by
      change (if tg.digest (pblk parameter data p c) then wt s else 0) = _
      rw [if_pos (hdigest p c)]
    rw [hpay]
    have hsum : ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (wt s +
          wcount model wt tg.digest (next u) (budget - 1) (s.store (pblk parameter data p c) u)) =
        wt s + ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
          wcount model wt tg.digest (next u) (budget - 1) (s.store (pblk parameter data p c) u) := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' probFailure_eq_zero,
        one_mul]
    rw [hsum]
    exact new_pair_boundWA parameter data w b0 Fail Qtot Lmax tg initial model hW hcalls hfair hQ L next h budget hb
      s P Ms d R hprep hP hM hD hC p c (hkind p) hp0
  · have hmean : ∑' r, Pr[= r | ordinaryStep model x s.known s] * wt r.2 ≤ wt s := by
      have := hW.step (.inl (.inr (.inl x))) s
      rwa [costStep_ordinary] at this
    calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] *
          (wt r.2 * potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget +
            b0 * wcount model wt tg.digest (next r.1) (budget - 1) r.2) := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support (ordinaryStep model x s.known s)
          · refine mul_le_mul_right ?_ _
            have hext := ordinaryStep_extends model x s r hr
            have hblocks := same_blocks (parameter := parameter) (data := data) hext
              (ordinaryStep_cache_ne model x s r hr) hnew
            obtain ⟨hP', -⟩ := same_items parameter data hext (ordinaryStep_cache_ne model x s r hr) hnew hP
            have hcnt : CountInv parameter data Qtot r.2 (budget - 1) := by
              intro m
              have h1 : cachedCount parameter data m r.2 ≤ cachedCount parameter data m s + 1 := by
                rw [cachedCount_eq, cachedCount_eq]
                exact costStep_card_le model _ (.inl (.inr (.inl x))) s r (by rw [costStep_ordinary]; exact hr)
              have h2 := hC m
              omega
            have hland : ∀ q, LandedIn parameter data s q → ∀ call,
                r.2.cache (pblk parameter data q call) = s.cache (pblk parameter data q call) :=
              fun q hq call => landed_blocks hext hP hq call
            refine le_trans (h r.1 (budget - 1) r.2 P Ms d R
              (fun i o hi => hext.1 i o (hprep i o hi)) hP' (minv_blocks hblocks hM) hD hcnt) (add_le_add ?_ le_rfl)
            exact mul_le_mul_right
              (potO_grow w b0 Fail tg initial hfair.le_one Lmax hext hblocks hland
                (fun q hq => (hP.mem q).1 hq) Ms L d (Nat.sub_le _ _)) _
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ ≤ _ := by
          simp only [mul_add, ENNReal.tsum_add]
          refine add_le_add ?_ ?_
          · calc _ = (∑' r, Pr[= r | ordinaryStep model x s.known s] * wt r.2) *
                  potO parameter data w b0 Fail tg initial Lmax s P Ms L d budget := by
                  rw [← ENNReal.tsum_mul_right]
                  exact tsum_congr fun r => by ring
              _ ≤ _ := mul_le_mul_left hmean _
          · refine le_add_left (le_of_eq ?_)
            simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

/-- **Leaf, weighted.** -/
theorem goodWA_pure (hw : w ≤ 1) (L : QueryLog SigningSpec) (forgery : Forgery) (verified : Bool) :
    GoodWA parameter data w b0 Fail Qtot Lmax tg initial model wt L (pure (forgery, L, verified)) := by
  intro budget s P Ms d R hprep hP hM hD hC
  have h := goodO_pure parameter data w b0 Fail Qtot Lmax tg initial model hw L forgery verified budget s P Ms d R
    hprep hP hM hD hC
  have hflag : expectedFlagged tg initial model (pure (forgery, L, verified) : OracleComp CostSpec _) budget s = 0 := by
    unfold expectedFlagged
    rw [interp_pure, tsum_probOutput_pure_mul]
    simp [flaggedCount]
  rw [hflag, mul_zero, add_zero, interp_pure, tsum_probOutput_pure_mul] at h
  rw [wcount_pure, mul_zero, add_zero, interp_pure, tsum_probOutput_pure_mul]
  exact mul_le_mul_right h _

/-- Lifted hash computations are sequences of ordinary queries. -/
theorem goodWA_liftHash (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot ≤ Cmax) (L : QueryLog SigningSpec) {α : Type}
    (computation : OracleComp HashSpec α)
    (next : α → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ a, GoodWA parameter data w b0 Fail Qtot Lmax tg initial model wt L (next a)) :
    GoodWA parameter data w b0 Fail Qtot Lmax tg initial model wt L
      ((liftM computation : OracleComp CostSpec α) >>= next) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [liftM_pure, pure_bind] using h value
  | query_bind query rest ih =>
      rw [liftM_bind, bind_assoc]
      exact goodWA_ordinary parameter data w b0 Fail Qtot Lmax tg initial model hW hcalls hparse hkind hdigest hfair hQ L
        query _ ih

/-- **One signing call, weighted**, on a message that was never signed before. -/
theorem goodWA_sign (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hw : w ≤ 1) (m : Message) (L : QueryLog SigningSpec) (hm : MsgLive L m)
    (next : Option Signature → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ r, GoodWA parameter data w b0 Fail Qtot Lmax tg initial model wt (L ++ [⟨m, r⟩]) (next r)) :
    GoodWA parameter data w b0 Fail Qtot Lmax tg initial model wt L (signCostSource parameter data m >>= next) := by
  intro budget s P Ms d R hprep hP hM hD hC
  set sign := signCostSource parameter data m with hsign
  set ℓ := (livePairs L P).length with hℓ
  set cont : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    o1.1.1.elim 0 fun r => wcount model wt tg.digest (next r) (budget - traceCost o1.1.2.2.1) o1.2 with hcont
  set canonR : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
    else canonO parameter data w b0 Fail m s P Ms L d (signatureLimit - (L.length + 1)) budget o1 with hcanonR
  have hpoint : ∀ o1 ∈ support (interp tg initial model sign budget s),
      ∑' out, Pr[= out | interpThen tg initial model next budget o1] *
          (wt out.2 * finalValue parameter data tg initial R out) ≤
        wt o1.2 * (canonR o1 + lam Lmax ℓ budget) + b0 * cont o1 := by
    intro o1 ho1
    cases hres : o1.1.1 with
    | none =>
        rw [interpThen_none tg initial model next budget o1 hres, tsum_probOutput_pure_mul]
        have h0 : finalValue parameter data tg initial R ((none, o1.1.2.1, o1.1.2.2.1, o1.1.2.2.2), o1.2) = 0 := rfl
        rw [h0, mul_zero]
        exact bot_le
    | some r =>
        rw [interpThen_some tg initial model next budget o1 r hres, tsum_probOutput_map_mul]
        obtain ⟨hprep', hP', hM', hD', hC', _⟩ := sign_paramsS tg initial model Fail Qtot hparse (hfail m)
          budget s P Ms d R hprep hP hM hD hC o1 ho1 r hres
        have hIH := h r (budget - traceCost o1.1.2.2.1) o1.2 _ _ _ _ hprep' hP' hM' hD' hC'
        have hpot := sign_pointO tg initial model parameter data w b0 Fail Qtot m hparse (hfail m) hw
          budget s P Ms L d R hprep hP hM hD hC o1 ho1 r hres (Nat.sub_le budget (traceCost o1.1.2.2.1))
        have hlam : lam Lmax (livePairs (L ++ [⟨m, r⟩]) (newPairs parameter data m s o1.2 ++ P)).length
            (budget - traceCost o1.1.2.2.1) ≤ lam Lmax ℓ budget := by
          refine lam_mono ?_ (Nat.sub_le _ _)
          unfold livePairs
          rw [List.filter_append]
          have hnew : (newPairs parameter data m s o1.2).filter
              (fun q => decide (MsgLive (L ++ [⟨m, r⟩]) q.1)) = [] := by
            refine List.filter_eq_nil_iff.2 fun q hq => ?_
            obtain ⟨hqm, _, _⟩ := (mem_newPairs parameter data m s).1 hq
            simp only [decide_eq_true_eq, msgLive_append, not_and, not_not]
            exact fun _ => hqm
          rw [hnew, List.nil_append]
          refine (List.Sublist.length_le ?_)
          refine List.monotone_filter_right _ fun q hq => ?_
          simp only [decide_eq_true_eq, msgLive_append] at hq ⊢
          exact hq.1
        have heq : ∀ o2 : Run HashInput Coordinate HiddenBridge.Outcome × State,
            finalValue parameter data tg initial R
              ((o2.1.1, o1.1.2.1 ++ o2.1.2.1, o1.1.2.2.1 ++ o2.1.2.2.1, o1.1.2.2.2 ++ o2.1.2.2.2), o2.2) =
            finalValue parameter data tg initial (R ++ o1.1.2.1) o2 := by
          intro o2
          unfold finalValue
          simp only [List.append_assoc]
        simp only [heq]
        refine le_trans hIH (add_le_add (mul_le_mul' le_rfl ?_) ?_)
        · unfold potO
          exact add_le_add hpot hlam
        · simp only [hcont, hres, Option.elim, le_refl]
  have hflag : ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * cont o1 ≤
      wcount model wt tg.digest (sign >>= next) budget s := by
    rw [wcount_bind model wt tg.digest tg initial]
    exact le_add_self
  rw [interp_bind, tsum_probOutput_bind_mul]
  calc _ ≤ ∑' o1, Pr[= o1 | interp tg initial model sign budget s] *
        (wt o1.2 * (canonR o1 + lam Lmax ℓ budget) + b0 * cont o1) := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support (interp tg initial model sign budget s)
        · exact mul_le_mul_right (hpoint o1 ho1) _
        · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
    _ = ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * (wt o1.2 * canonR o1) +
          ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * (wt o1.2 * lam Lmax ℓ budget) +
          b0 * ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * cont o1 := by
        simp only [mul_add, ENNReal.tsum_add, mul_left_comm _ b0, ENNReal.tsum_mul_left]
    _ ≤ _ := by
        unfold potO
        rw [mul_add]
        exact add_le_add (add_le_add
          (sign_expectA tg initial model hW hcalls parameter data w b0 Fail m hparse hkind budget s P Ms L hm d hP hM)
          (interp_wt_const tg initial hW sign budget s _)) (mul_le_mul_right hflag _)

theorem goodWA_finish (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot ≤ Cmax) (L : QueryLog SigningSpec) (forgery : Forgery) :
    GoodWA parameter data w b0 Fail Qtot Lmax tg initial model wt L (finishGame parameter data L forgery) := by
  unfold finishGame
  exact goodWA_liftHash parameter data w b0 Fail Qtot Lmax tg initial model hW hcalls hparse hkind hdigest hfair hQ L _ _
    fun v => goodWA_pure parameter data w b0 Fail Qtot Lmax tg initial model hW hcalls hfair.le_one L forgery v

/-- **The weighted one-coin potential of the scan signer through any adversary that never repeats a
message.** -/
theorem goodWA_advProg (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    {Cmax : ℕ} (hfair : FairS w Cmax Lmax) (hQ : Qtot ≤ Cmax) :
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec),
      NoRepeat M (L.map Sigma.fst) →
        GoodWA parameter data w b0 Fail Qtot Lmax tg initial model wt L (advProg parameter data M L) := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L _
      rw [advProg_pure]
      exact goodWA_finish parameter data w b0 Fail Qtot Lmax tg initial model hW hcalls hparse hkind hdigest hfair hQ L
        forgery
  | query_bind input next ih =>
      intro L hnr
      rcases input with (draw | bytes) | message
      · rw [advProg_draw]
        exact goodWA_draw parameter data w b0 Fail Qtot Lmax tg initial model hW hcalls L draw _ fun v => ih v L (hnr v)
      · rw [advProg_hash]
        exact goodWA_ordinary parameter data w b0 Fail Qtot Lmax tg initial model hW hcalls hparse hkind hdigest hfair hQ
          L bytes _ fun v => ih v L (hnr v)
      · rw [advProg_sign]
        obtain ⟨hnot, hrest⟩ := (noRepeat_sign message next _).1 hnr
        have hm : MsgLive L message := by
          intro entry he heq
          exact hnot (heq ▸ List.mem_map_of_mem he)
        refine goodWA_sign parameter data w b0 Fail Qtot Lmax tg initial model hW hcalls hparse hkind hfail hfair.le_one
          message L hm _ fun r => ih r _ ?_
        rw [List.map_append]
        exact hrest r

end GoodWA

end FORS.Security.SWRoute
