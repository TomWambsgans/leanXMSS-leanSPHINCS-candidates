import LeanSphincs.BridgeSatWSigner
import LeanSphincs.BridgeForsGameOnce

/-! The one-coin FORS potential weighted by the survival weight. The final value of a run counts
a FORS cover with weight `w_end`; a new message/randomizer pair costs the baseline times the
current weight; ordinary queries and signing calls do not raise `w * pot` in expectation, since
the potential only depends on the views of the message-digest blocks, whose reads keep the
weight, and the weight is a supermartingale of the run. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### Signing a message for the first time, weighted -/

section SignExpectW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (m : Message) (s : State) (n : ℕ)
  (d : Multiset View) (f : Multiset View → ℝ≥0∞)

variable {parameter data wbar m s n d f}

/-- The weighted mass of a constant. -/
theorem interp_weight_constW {α : Type} (computation : OracleComp CostSpec α) (budget : ℕ) (c : ℝ≥0∞) :
    ∑' out, Pr[= out | interp tg initial model computation budget s] * (weight tg initial out.2 * c) ≤
      weight tg initial s * c := by
  calc _ = (∑' out, Pr[= out | interp tg initial model computation budget s] * weight tg initial out.2) * c := by
        rw [← ENNReal.tsum_mul_right]
        exact tsum_congr fun out => by ring
    _ ≤ _ := mul_le_mul_left (interp_weight_leW tg initial model computation budget s) _

theorem upper_expectW (hparse : ∀ ρ call, model.parse (blk parameter data m ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (blk parameter data m ρ call) = .none)
    {Cmax : ℕ} (hfair : Fair wbar Cmax) (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤)
    {P : List Pair} (hP : PInv parameter data s P) (excl : Pair → Prop) (attempts budget : ℕ)
    (hcount : cachedCount parameter data m s + attempts ≤ Cmax) (J : List View) :
    ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
        (weight tg initial out.2 * upperO parameter data wbar m s n d f excl out J) ≤
      weight tg initial s * (baseVO wbar n d f J + freshAvg Finset.univ (gainFO wbar n d f J) +
        wbar * ∑ ρ, poolValue parameter data m s (fun ρ v => if excl (m, ρ) then 0 else gainPO wbar n d f J v) ρ) := by
  have hprops := virtualOnce_props Finset.univ_nonempty hfair.le_one hf.1 hf.2.1 hf.2.2 n J
  have hnob1 : ∀ ρ, s.cache (blk parameter data m ρ 0) = none → s.cache (blk parameter data m ρ 1) = none :=
    fun ρ h => hP.first (m, ρ) h
  have hlandb1 : ∀ ρ u0, s.cache (blk parameter data m ρ 0) = some u0 → Landed parameter (blockIndex u0) →
      s.cache (blk parameter data m ρ 1) ≠ none := fun ρ u0 h0 hl => hP.second (m, ρ) ⟨u0, h0, hl⟩
  set B : ℝ≥0∞ := ∑ v : View, virtualOnce Finset.univ wbar f n J (d + {v}) with hB
  have hBfin : B ≠ ⊤ := ENNReal.sum_ne_top.2 fun v _ => hprops.2.2 _
  have hgp : ∀ ρ v, (fun ρ v => if excl (m, ρ) then 0 else gainPO wbar n d f J v) ρ v ≤ B := by
    intro ρ v
    simp only
    split_ifs
    · exact bot_le
    · exact le_trans tsub_le_self (Finset.single_le_sum (f := fun v => virtualOnce Finset.univ wbar f n J (d + {v}))
        (fun _ _ => bot_le) (Finset.mem_univ v))
  have hpool := loop_boundW tg initial model parameter data m hparse hkind s hnob1 (fun _ => 0)
    (fun ρ v => if excl (m, ρ) then 0 else gainPO wbar n d f J v) B hBfin (fun _ => bot_le) hgp wbar hfair.ne_top
    Cmax hfair.cmax hfair.share attempts budget s (related_self parameter data m s) hcount
  have hfresh := loop_bound_freshW tg initial model parameter data m hparse hkind s hnob1 hlandb1
    (gainFO wbar n d f J) attempts budget s (related_self parameter data m s)
  unfold upperO
  simp only [mul_add, ENNReal.tsum_add]
  refine add_le_add (add_le_add (interp_weight_constW tg initial model _ _ _) hfresh) (le_trans hpool ?_)
  simp [freshAvg]

/-- **A dominated term, weighted.** -/
theorem term_expectW (hparse : ∀ ρ call, model.parse (blk parameter data m ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (blk parameter data m ρ call) = .none)
    {Cmax : ℕ} (hfair : Fair wbar Cmax) (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤)
    {P : List Pair} (hP : PInv parameter data s P) (excl : Pair → Prop) (attempts budget k : ℕ)
    (hcount : cachedCount parameter data m s + attempts ≤ Cmax) (rest : List View) :
    ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
        (weight tg initial out.2 *
          creations Finset.univ landing (fun J => upperO parameter data wbar m s n d f excl out J) k rest) ≤
      weight tg initial s * creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar f (n + 1) J d) k
        (msgItems parameter data m s (others excl P) ++ rest) := by
  simp only [← mul_assoc]
  rw [creations_tsum, creations_prepend (virtualOnce_perm' wbar (n + 1) d), ← creations_const_mul]
  refine creations_mono_suffix k _ fun news => ?_
  simp only [mul_assoc]
  exact le_trans (upper_expectW tg initial model hparse hkind hfair hf hP excl attempts budget hcount _)
    (mul_le_mul_right (slot_combineO hfair.le_one hf hP excl (news ++ rest)) _)

end SignExpectW

section SignPointW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ) (m : Message)

/-- **The signing step in expectation, weighted**, for a message signed for the first time. -/
theorem sign_expectW (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    {Cmax : ℕ} (hfair : Fair wbar Cmax) (hb0 : b0 ≠ ⊤) (attempts budget : ℕ) (s : State) (P : List Pair)
    (L : QueryLog SigningSpec) (hm : ∀ entry ∈ L, entry.1 ≠ m) (d : Multiset View) (hP : PInv parameter data s P)
    (hcount : cachedCount parameter data m s + attempts ≤ Cmax) :
    ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
        (weight tg initial out.2 * (if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
          else canonO parameter data wbar b0 Fail m s P L d (signatureLimit - (L.length + 1)) budget out)) ≤
      weight tg initial s * potO parameter data wbar b0 Fail tg initial s P L d budget := by
  by_cases hcase : Realized tg initial s ∨ signatureLimit ≤ L.length
  · simp only [if_pos hcase, mul_zero, tsum_zero]
    exact bot_le
  simp only [if_neg hcase]
  have hcase' : ¬Realized tg initial s ∧ L.length < signatureLimit := by push Not at hcase; exact hcase
  have hlen := hcase'.2
  unfold potO
  rw [if_neg (by rintro (h | h); exact hcase'.1 h; omega)]
  set n := signatureLimit - (L.length + 1) with hn
  have hn1 : signatureLimit - L.length = n + 1 := by omega
  rw [hn1]
  have hparse' : ∀ ρ call, model.parse (blk parameter data m ρ call) = none := fun ρ call => hparse (m, ρ) call
  have hkind' : ∀ ρ call, tg.kind (blk parameter data m ρ call) = .none := fun ρ call => hkind (m, ρ) call
  have hnob1 : ∀ ρ, s.cache (blk parameter data m ρ 0) = none → s.cache (blk parameter data m ρ 1) = none :=
    fun ρ h => hP.first (m, ρ) h
  have hlandb1 : ∀ ρ u0, s.cache (blk parameter data m ρ 0) = some u0 → Landed parameter (blockIndex u0) →
      s.cache (blk parameter data m ρ 1) ≠ none := fun ρ u0 h0 hl => hP.second (m, ρ) ⟨u0, h0, hl⟩
  have hconst := fun c => interp_weight_constW tg initial model (s := s)
    (signCostSourceLoop parameter data m attempts) budget c
  have hFN := loop_bound_freshW tg initial model parameter data m hparse' hkind' s hnob1 hlandb1
    (fun v => if v.1 ∈ Fail then 1 else 0) attempts budget s (related_self parameter data m s)
  have hT : ∀ q ∈ P, ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
      (weight tg initial out.2 * (if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
        creations Finset.univ landing (fun J => upperO parameter data wbar m s n d (witnessFn (pview parameter data s q))
          (· = q) out J) budget (restItems parameter data m s L (P.erase q))) else 0)) ≤
      weight tg initial s * candO parameter data wbar Fail s P L d (n + 1) budget q := by
    intro q _
    unfold candO
    split_ifs
    · exact hconst 1
    · unfold candValueO
      rw [creations_perm (virtualOnce_perm' wbar (n + 1) d) budget _ _ (coinItems_perm parameter data m s L hm _)]
      have h := term_expectW tg initial model hparse' hkind' hfair (witness_props (pview parameter data s q)) hP
        (· = q) attempts budget budget hcount (restItems parameter data m s L (P.erase q)) (n := n) (d := d)
      rwa [← erase_eq_filter' hP.nodup q] at h
    · exact hconst 0
  have hH := term_expectW tg initial model (n := n) (d := d) hparse' hkind' hfair (excess_props b0 hb0) hP
    (fun _ => False) attempts budget budget hcount (restItems parameter data m s L P)
  rw [filter_false'] at hH
  have hHv : hValueO parameter data wbar b0 s P L d (n + 1) budget =
      creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar (excess b0) (n + 1) J d) budget
        (msgItems parameter data m s P ++ restItems parameter data m s L P) := by
    unfold hValueO
    exact creations_perm (virtualOnce_perm' wbar (n + 1) d) budget _ _ (coinItems_perm parameter data m s L hm _)
  have hφ : freshAvg Finset.univ (fun v : View => if v.1 ∈ Fail then (1 : ℝ≥0∞) else 0) = failMass Fail := rfl
  rw [hφ] at hFN
  -- the list of candidates
  have hLS : ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
      (weight tg initial out.2 * (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1
        else creations Finset.univ landing (fun J => upperO parameter data wbar m s n d
          (witnessFn (pview parameter data s q)) (· = q) out J) budget (restItems parameter data m s L (P.erase q)))
        else 0).sum) ≤
      weight tg initial s * (P.map (candO parameter data wbar Fail s P L d (n + 1) budget)).sum := by
    simp only [← mul_assoc]
    rw [tsum_list_sum, ← List.sum_map_mul_left]
    exact List.sum_le_sum fun q hq => by simpa only [mul_assoc] using hT q hq
  -- the excess forecast
  have hHC : ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
      (weight tg initial out.2 * ((budget : ℝ≥0∞) * (creations Finset.univ landing
        (fun J => upperO parameter data wbar m s n d (excess b0) (fun _ => False) out J) budget
          (restItems parameter data m s L P) + failMass Fail))) ≤
      weight tg initial s * ((budget : ℝ≥0∞) * (hValueO parameter data wbar b0 s P L d (n + 1) budget +
        failMass Fail)) := by
    have hpt : ∀ out : Run HashInput Coordinate (Option Signature) × State,
        Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
          (weight tg initial out.2 * ((budget : ℝ≥0∞) * (creations Finset.univ landing
            (fun J => upperO parameter data wbar m s n d (excess b0) (fun _ => False) out J) budget
              (restItems parameter data m s L P) + failMass Fail))) =
        (budget : ℝ≥0∞) * (Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
          (weight tg initial out.2 * creations Finset.univ landing
            (fun J => upperO parameter data wbar m s n d (excess b0) (fun _ => False) out J) budget
              (restItems parameter data m s L P))) +
        (budget : ℝ≥0∞) * (Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
          (weight tg initial out.2 * failMass Fail)) := by
      intro out
      ring
    simp only [hpt, ENNReal.tsum_add, ENNReal.tsum_mul_left]
    rw [hHv]
    calc _ ≤ (budget : ℝ≥0∞) * (weight tg initial s * creations Finset.univ landing
          (fun J => virtualOnce Finset.univ wbar (excess b0) (n + 1) J d) budget
            (msgItems parameter data m s P ++ restItems parameter data m s L P)) +
          (budget : ℝ≥0∞) * (weight tg initial s * failMass Fail) :=
          add_le_add (mul_le_mul_right hH _) (mul_le_mul_right (hconst _) _)
      _ = _ := by ring
  have hsplit : ∀ out : Run HashInput Coordinate (Option Signature) × State,
      Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
        (weight tg initial out.2 * canonO parameter data wbar b0 Fail m s P L d n budget out) =
      Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
          (weight tg initial out.2 * freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out) +
        Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
          (weight tg initial out.2 * (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1
            else creations Finset.univ landing (fun J => upperO parameter data wbar m s n d
              (witnessFn (pview parameter data s q)) (· = q) out J) budget (restItems parameter data m s L (P.erase q)))
            else 0).sum) +
        Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
          (weight tg initial out.2 * ((budget : ℝ≥0∞) * (creations Finset.univ landing
            (fun J => upperO parameter data wbar m s n d (excess b0) (fun _ => False) out J) budget
              (restItems parameter data m s L P) + failMass Fail))) +
        Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
          (weight tg initial out.2 * ((n : ℝ≥0∞) * failMass Fail)) := by
    intro out
    unfold canonO
    ring
  simp only [hsplit, ENNReal.tsum_add]
  calc _ ≤ weight tg initial s * failMass Fail +
        weight tg initial s * (P.map (candO parameter data wbar Fail s P L d (n + 1) budget)).sum +
        weight tg initial s * ((budget : ℝ≥0∞) * (hValueO parameter data wbar b0 s P L d (n + 1) budget +
          failMass Fail)) + weight tg initial s * ((n : ℝ≥0∞) * failMass Fail) :=
        add_le_add (add_le_add (add_le_add hFN hLS) hHC) (hconst _)
    _ = _ := by
        unfold coreO
        push_cast
        ring

end SignPointW

/-! ### Weighted paid programs -/

section GoodW

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A program whose final value, weighted by the final survival weight, is paid by the weighted
potential and the weighted baseline payments. -/
def GoodW (L : QueryLog SigningSpec) (prog : OracleComp CostSpec HiddenBridge.Outcome) : Prop :=
  ∀ budget (s : State) (P : List Pair) (d : Multiset View) (R : List Coordinate),
    Prepared initial s → PInv parameter data s P → DInv R d → CountInv parameter data Qtot s budget →
      ∑' out, Pr[= out | interp tg initial model prog budget s] *
          (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
        weight tg initial s * potO parameter data wbar b0 Fail tg initial s P L d budget +
          b0 * wflag tg initial model prog budget s

theorem goodW_draw (L : QueryLog SigningSpec) (draw : ℕ)
    (next : Fin (draw + 1) → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodW parameter data wbar b0 Fail Qtot tg initial model L (next v)) :
    GoodW parameter data wbar b0 Fail Qtot tg initial model L
      (liftM (CostSpec.query (.inl (.inl draw))) >>= next) := by
  intro budget s P d R hprep hP hD hC
  have hw : wflag tg initial model (liftM (CostSpec.query (.inl (.inl draw))) >>= next) budget s =
      ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
        wflag tg initial model (next v) budget s := by
    rw [wflag_query_bind]
    refine (if_pos (Nat.zero_le budget)).trans ?_
    change ∑' r, Pr[= r | (fun v => (v, s)) <$> (liftM (unifSpec.query draw) : ProbComp _)] *
      (0 + wflag tg initial model (next r.1) (budget - 0) r.2) = _
    rw [tsum_probOutput_map_mul]
    simp only [zero_add, Nat.sub_zero]
  rw [hw, interp_draw, tsum_probOutput_bind_mul]
  calc _ ≤ ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
        (weight tg initial s * potO parameter data wbar b0 Fail tg initial s P L d budget +
          b0 * wflag tg initial model (next v) budget s) :=
        ENNReal.tsum_le_tsum fun v => mul_le_mul_right (h v budget s P d R hprep hP hD hC) _
    _ ≤ _ := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
        refine add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) (le_of_eq ?_)
        simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

theorem finalValueW_ordinary (R : List Coordinate) (x : HashInput)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome) (budget : ℕ) (hb : 1 ≤ budget) (s : State) :
    ∑' out, Pr[= out | interp tg initial model (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) budget s] *
        (weight tg initial out.2 * finalValue parameter data tg initial R out) =
      ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        ∑' out, Pr[= out | interp tg initial model (next r.1) (budget - 1) r.2] *
          (weight tg initial out.2 * finalValue parameter data tg initial R out) := by
  rw [interp_ordinary, if_pos hb, tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_map_mul]
  rfl

theorem wflag_ordinary (x : HashInput) (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) :
    wflag tg initial model (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) budget s =
      ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        (wpays tg initial s (.inl (.inr (.inl x))) + wflag tg initial model (next r.1) (budget - 1) r.2) := by
  rw [wflag_query_bind, costStep_ordinary]
  exact if_pos hb

/-- The sibling of a new pair, presampled after the first read, weighted. -/
theorem new_pair_boundW (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (L : QueryLog SigningSpec)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodW parameter data wbar b0 Fail Qtot tg initial model L (next v))
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) (P : List Pair) (d : Multiset View) (R : List Coordinate)
    (hprep : Prepared initial s) (hP : PInv parameter data s P) (hD : DInv R d)
    (hC : CountInv parameter data Qtot s budget) (p : Pair)
    (hp0 : s.cache (pblk parameter data p 0) = none) (hp1 : s.cache (pblk parameter data p 1) = none)
    (call : Fin 2) :
    ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        ∑' out, Pr[= out | interp tg initial model (next u) (budget - 1)
          (s.store (pblk parameter data p call) u)] *
            (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
      weight tg initial s * potO parameter data wbar b0 Fail tg initial s P L d budget +
        b0 * (weight tg initial s +
          ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
            wflag tg initial model (next u) (budget - 1) (s.store (pblk parameter data p call) u)) := by
  set y := pblk parameter data p (if call = 0 then 1 else 0) with hy
  have hstate : ∀ u u', (s.store (pblk parameter data p call) u).store y u' =
      if call = 0 then withPair parameter data s p u u' else withPair parameter data s p u' u := by
    intro u u'
    fin_cases call
    · rfl
    · simp only [hy, Fin.mk_one, one_ne_zero, if_false, withPair]
      exact store_comm s _ _ (Ne.symm (pblk_ne_call parameter data p)) u u'
  have hsib : ∀ u, (s.store (pblk parameter data p call) u).cache y = none := by
    intro u
    have hne : y ≠ pblk parameter data p call := by
      fin_cases call
      · exact Ne.symm (pblk_ne_call parameter data p)
      · exact pblk_ne_call parameter data p
    rw [store_cache_ne s _ _ hne u]
    fin_cases call
    · exact hp1
    · exact hp0
  have hxfresh : s.cache (pblk parameter data p call) = none := by
    fin_cases call
    · exact hp0
    · exact hp1
  have hws : ∀ u u', weight tg initial ((s.store (pblk parameter data p call) u).store y u') =
      weight tg initial s := by
    intro u u'
    rw [weight_store_untargetedW tg initial _ y u' (hkind _ _),
      weight_store_untargetedW tg initial s _ u (hkind _ _)]
  have hone : ∀ u, ∑' out, Pr[= out | interp tg initial model (next u) (budget - 1)
        (s.store (pblk parameter data p call) u)] *
          (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
      ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (weight tg initial ((s.store (pblk parameter data p call) u).store y u') *
          potO parameter data wbar b0 Fail tg initial ((s.store (pblk parameter data p call) u).store y u')
            (addPair parameter P p (if call = 0 then u else u')) L d (budget - 1) +
        b0 * wflag tg initial model (next u) (budget - 1)
          ((s.store (pblk parameter data p call) u).store y u')) := by
    intro u
    refine le_trans (interp_presample_le tg initial model y (hkind _ _) (next u) (budget - 1) _ _
      (fun out s' hs' => ?_)) ?_
    · show weight tg initial out.2 * finalValue parameter data tg initial R out ≤
        weight tg initial s' * finalValue parameter data tg initial R (out.1, s')
      rw [weight_presampleW tg initial y (hkind _ _) out.2 s' hs']
      exact mul_le_mul_right (finalValue_presample tg initial parameter data y (hkind _ _) R out s' hs') _
    rw [presample_fresh y _ (hsib u), tsum_probOutput_map_mul]
    refine ENNReal.tsum_le_tsum fun u' => mul_le_mul_right ?_ _
    rw [hstate u u']
    have hprep2 : ∀ a b, Prepared initial (withPair parameter data s p a b) := by
      intro a b
      unfold withPair
      exact prepared_store initial _ (prepared_store initial s hprep _ a hp0) _ b
        (by rw [store_cache_ne s _ _ (Ne.symm (pblk_ne_call parameter data p))]; exact hp1)
    have hC2 : ∀ a b, CountInv parameter data Qtot (withPair parameter data s p a b) (budget - 1) := by
      intro a b m
      have h1 := count_withPair (parameter := parameter) (data := data) m s p a b
      have h2 := hC m
      omega
    split_ifs with hc
    · exact h u (budget - 1) _ _ d R (hprep2 u u') (pinv_withPair hP hp0 u u') hD (hC2 u u')
    · exact h u (budget - 1) _ _ d R (hprep2 u' u) (pinv_withPair hP hp0 u' u) hD (hC2 u' u)
  -- the potential part, unweighted
  have hcore : ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
      ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] *
        potO parameter data wbar b0 Fail tg initial ((s.store (pblk parameter data p call) u).store y u')
          (addPair parameter P p (if call = 0 then u else u')) L d (budget - 1) ≤
      potO parameter data wbar b0 Fail tg initial s P L d budget + b0 * (if Realized tg initial s then 0 else 1) := by
    by_cases hr : Realized tg initial s ∨ signatureLimit < L.length
    · refine le_of_eq_of_le (ENNReal.tsum_eq_zero.2 fun u => ?_) bot_le
      rw [ENNReal.tsum_eq_zero.2 fun u' => ?_, mul_zero]
      unfold potO
      rw [if_pos (hr.imp (realized_of_extends tg initial ((extends_store s _ u hxfresh).trans
        (extends_store _ y u' (hsib u)))) id), mul_zero]
    · have hreal : ¬Realized tg initial s := fun h' => hr (Or.inl h')
      rw [if_neg hreal, mul_one]
      have hpot : potO parameter data wbar b0 Fail tg initial s P L d budget =
          coreO parameter data wbar b0 Fail s P L d (signatureLimit - L.length) (budget - 1 + 1) := by
        unfold potO; rw [if_neg hr, Nat.sub_add_cancel hb]
      rw [hpot]
      refine le_trans ?_ (coreO_newPair wbar b0 Fail hw hb0 hP hp0 L d _ (budget - 1))
      unfold pairE
      have hle : ∀ u u', potO parameter data wbar b0 Fail tg initial ((s.store (pblk parameter data p call) u).store y u')
          (addPair parameter P p (if call = 0 then u else u')) L d (budget - 1) ≤
          if call = 0 then coreO parameter data wbar b0 Fail (withPair parameter data s p u u') (addPair parameter P p u)
            L d (signatureLimit - L.length) (budget - 1)
          else coreO parameter data wbar b0 Fail (withPair parameter data s p u' u) (addPair parameter P p u') L d
            (signatureLimit - L.length) (budget - 1) := by
        intro u u'
        rw [hstate u u']
        split_ifs
        · exact potO_le_coreO wbar b0 Fail tg initial _ _ L d _
        · exact potO_le_coreO wbar b0 Fail tg initial _ _ L d _
      refine le_trans (ENNReal.tsum_le_tsum fun u => mul_le_mul_right
        (ENNReal.tsum_le_tsum fun u' => mul_le_mul_right (hle u u') _) _) (le_of_eq ?_)
      split_ifs with hc
      · rfl
      · exact tsum_swap2 _ (fun a b => coreO parameter data wbar b0 Fail (withPair parameter data s p a b)
          (addPair parameter P p a) L d (signatureLimit - L.length) (budget - 1))
  -- the weighted payments
  have hu : ∀ u, ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] *
      wflag tg initial model (next u) (budget - 1) ((s.store (pblk parameter data p call) u).store y u') ≤
      wflag tg initial model (next u) (budget - 1) (s.store (pblk parameter data p call) u) := by
    intro u
    have h := wflag_presample_le tg initial model y (hkind _ _) (next u) (budget - 1)
      (s.store (pblk parameter data p call) u)
    rwa [presample_fresh y _ (hsib u), tsum_probOutput_map_mul] at h
  refine le_trans (ENNReal.tsum_le_tsum fun u => mul_le_mul_right (hone u) _) ?_
  simp only [hws, mul_add, ENNReal.tsum_add]
  rw [← add_assoc]
  refine add_le_add ?_ ?_
  · calc _ = weight tg initial s * ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
          ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] *
            potO parameter data wbar b0 Fail tg initial ((s.store (pblk parameter data p call) u).store y u')
              (addPair parameter P p (if call = 0 then u else u')) L d (budget - 1) := by
          simp only [mul_left_comm _ (weight tg initial s), ENNReal.tsum_mul_left]
      _ ≤ weight tg initial s * (potO parameter data wbar b0 Fail tg initial s P L d budget +
            b0 * (if Realized tg initial s then 0 else 1)) := mul_le_mul_right hcore _
      _ ≤ _ := by
          rw [mul_add]
          refine add_le_add le_rfl ?_
          rw [mul_left_comm]
          refine mul_le_mul_right ?_ _
          split_ifs
          · simp
          · simp
  · calc _ = b0 * ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
          ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] *
            wflag tg initial model (next u) (budget - 1) ((s.store (pblk parameter data p call) u).store y u') := by
          simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]
      _ ≤ _ := mul_le_mul_right (ENNReal.tsum_le_tsum fun u => mul_le_mul_right (hu u) _) _

/-- **One ordinary query, weighted.** -/
theorem goodW_ordinary (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (L : QueryLog SigningSpec) (x : HashInput)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodW parameter data wbar b0 Fail Qtot tg initial model L (next v)) :
    GoodW parameter data wbar b0 Fail Qtot tg initial model L
      (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) := by
  intro budget s P d R hprep hP hD hC
  by_cases hb : 1 ≤ budget
  swap
  · rw [interp_ordinary, if_neg hb, tsum_probOutput_pure_mul, finalValue_abort, mul_zero]
    exact bot_le
  rw [finalValueW_ordinary parameter data tg initial model R x next budget hb s,
    wflag_ordinary tg initial model x next budget hb s]
  by_cases hnew : ∃ p call, x = pblk parameter data p call ∧ s.cache (pblk parameter data p 0) = none
  · obtain ⟨p, call, rfl, hp0⟩ := hnew
    have hp1 := hP.first p hp0
    have hfresh : s.cache (pblk parameter data p call) = none := by
      fin_cases call
      · exact hp0
      · exact hp1
    rw [ordinaryStep, hparse p call]
    simp only
    rw [readOutside_fresh _ s hfresh, tsum_probOutput_map_mul, tsum_probOutput_map_mul]
    have hpay : wpays tg initial s (.inl (.inr (.inl (pblk parameter data p call)))) = weight tg initial s := by
      change (if tg.digest (pblk parameter data p call) then weight tg initial s else 0) = _
      rw [if_pos (hdigest p call)]
    rw [hpay]
    simp only
    have hsum : ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (weight tg initial s + wflag tg initial model (next u) (budget - 1) (s.store (pblk parameter data p call) u)) =
        weight tg initial s + ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
          wflag tg initial model (next u) (budget - 1) (s.store (pblk parameter data p call) u) := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' probFailure_eq_zero,
        one_mul]
    rw [hsum]
    exact new_pair_boundW parameter data wbar b0 Fail Qtot tg initial model hkind hw hb0 L next h budget hb s P d R
      hprep hP hD hC p hp0 hp1 call
  · have hmean : ∑' r, Pr[= r | ordinaryStep model x s.known s] * weight tg initial r.2 ≤ weight tg initial s := by
      have := meanWeight_costStep_leW tg initial model (.inl (.inr (.inl x))) s
      rwa [costStep_ordinary] at this
    calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] *
          (weight tg initial r.2 * potO parameter data wbar b0 Fail tg initial s P L d budget +
            b0 * wflag tg initial model (next r.1) (budget - 1) r.2) := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support (ordinaryStep model x s.known s)
          · refine mul_le_mul_right ?_ _
            have hext := ordinaryStep_extends model x s r hr
            obtain ⟨hP', hview⟩ := same_items parameter data hext
              (ordinaryStep_cache_ne model x s r hr) hnew hP
            have hcnt : CountInv parameter data Qtot r.2 (budget - 1) := by
              intro m
              have h1 : cachedCount parameter data m r.2 ≤ cachedCount parameter data m s + 1 := by
                rw [cachedCount_eq, cachedCount_eq]
                exact costStep_card_le model _ (.inl (.inr (.inl x))) s r (by rw [costStep_ordinary]; exact hr)
              have h2 := hC m
              omega
            refine le_trans (h r.1 (budget - 1) r.2 P d R
              (fun i o hi => hext.1 i o (hprep i o hi)) hP' hD hcnt) (add_le_add ?_ le_rfl)
            exact mul_le_mul_right (potO_grow wbar b0 Fail tg initial hw hb0 hext hview L d (Nat.sub_le _ _)) _
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ ≤ _ := by
          simp only [mul_add, ENNReal.tsum_add]
          refine add_le_add ?_ ?_
          · calc _ = (∑' r, Pr[= r | ordinaryStep model x s.known s] * weight tg initial r.2) *
                  potO parameter data wbar b0 Fail tg initial s P L d budget := by
                  rw [← ENNReal.tsum_mul_right]
                  exact tsum_congr fun r => by ring
              _ ≤ _ := mul_le_mul_left hmean _
          · refine le_add_left (le_of_eq ?_)
            simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

/-- **Leaf, weighted.** -/
theorem goodW_pure (hw : wbar ≤ 1) (L : QueryLog SigningSpec) (forgery : Forgery) (verified : Bool) :
    GoodW parameter data wbar b0 Fail Qtot tg initial model L (pure (forgery, L, verified)) := by
  intro budget s P d R hprep hP hD hC
  have h := goodO_pure parameter data wbar b0 Fail Qtot tg initial model hw L forgery verified budget s P d R
    hprep hP hD hC
  have hflag : expectedFlagged tg initial model (pure (forgery, L, verified) : OracleComp CostSpec _) budget s = 0 := by
    unfold expectedFlagged
    rw [interp_pure, tsum_probOutput_pure_mul]
    simp [flaggedCount]
  rw [hflag, mul_zero, add_zero, interp_pure, tsum_probOutput_pure_mul] at h
  rw [wflag_pure, mul_zero, add_zero, interp_pure, tsum_probOutput_pure_mul]
  exact mul_le_mul_right h _

/-- Lifted hash computations are sequences of ordinary queries. -/
theorem goodW_liftHash (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (L : QueryLog SigningSpec) {α : Type} (computation : OracleComp HashSpec α)
    (next : α → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ a, GoodW parameter data wbar b0 Fail Qtot tg initial model L (next a)) :
    GoodW parameter data wbar b0 Fail Qtot tg initial model L
      ((liftM computation : OracleComp CostSpec α) >>= next) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [liftM_pure, pure_bind] using h value
  | query_bind query rest ih =>
      rw [liftM_bind, bind_assoc]
      exact goodW_ordinary parameter data wbar b0 Fail Qtot tg initial model hparse hkind hdigest hw hb0 L query _ ih

/-- **One signing call, weighted**, on a message that was never signed before. -/
theorem goodW_sign (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    {Cmax : ℕ} (hfair : Fair wbar Cmax) (hb0 : b0 ≠ ⊤) (hQ : Qtot + digestAttemptLimit ≤ Cmax)
    (m : Message) (L : QueryLog SigningSpec) (hm : ∀ entry ∈ L, entry.1 ≠ m)
    (next : Option Signature → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ r, GoodW parameter data wbar b0 Fail Qtot tg initial model (L ++ [⟨m, r⟩]) (next r)) :
    GoodW parameter data wbar b0 Fail Qtot tg initial model L (signCostSource parameter data m >>= next) := by
  intro budget s P d R hprep hP hD hC
  have hcount : cachedCount parameter data m s + digestAttemptLimit ≤ Cmax := by
    have := hC m; omega
  unfold signCostSource
  set sign := signCostSourceLoop parameter data m digestAttemptLimit with hsign
  set cont : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    o1.1.1.elim 0 fun r => wflag tg initial model (next r) (budget - traceCost o1.1.2.2.1) o1.2 with hcont
  set canonR : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
    else canonO parameter data wbar b0 Fail m s P L d (signatureLimit - (L.length + 1)) budget o1 with hcanonR
  have hpoint : ∀ o1 ∈ support (interp tg initial model sign budget s),
      ∑' out, Pr[= out | interpThen tg initial model next budget o1] *
          (weight tg initial out.2 * finalValue parameter data tg initial R out) ≤
        weight tg initial o1.2 * canonR o1 + b0 * cont o1 := by
    intro o1 ho1
    cases hres : o1.1.1 with
    | none =>
        rw [interpThen_none tg initial model next budget o1 hres, tsum_probOutput_pure_mul]
        have h0 : finalValue parameter data tg initial R ((none, o1.1.2.1, o1.1.2.2.1, o1.1.2.2.2), o1.2) = 0 := rfl
        rw [h0, mul_zero]
        exact bot_le
    | some r =>
        rw [interpThen_some tg initial model next budget o1 r hres, tsum_probOutput_map_mul]
        obtain ⟨hprep', hP', hD', hC', _⟩ := sign_params tg initial model Fail Qtot hparse (hfail m)
          digestAttemptLimit budget s P d R hprep hP hD hC o1 ho1 r hres
        have hIH := h r (budget - traceCost o1.1.2.2.1) o1.2 _ _ _ hprep' hP' hD' hC'
        have hpot := sign_pointO tg initial model parameter data wbar b0 Fail Qtot m hparse (hfail m) hfair.le_one hb0
          digestAttemptLimit budget s P L d R hprep hP hD hC o1 ho1 r hres (Nat.sub_le budget (traceCost o1.1.2.2.1))
        have heq : ∀ o2 : Run HashInput Coordinate HiddenBridge.Outcome × State,
            finalValue parameter data tg initial R
              ((o2.1.1, o1.1.2.1 ++ o2.1.2.1, o1.1.2.2.1 ++ o2.1.2.2.1, o1.1.2.2.2 ++ o2.1.2.2.2), o2.2) =
            finalValue parameter data tg initial (R ++ o1.1.2.1) o2 := by
          intro o2
          unfold finalValue
          simp only [List.append_assoc]
        simp only [heq]
        refine le_trans hIH (add_le_add (mul_le_mul_right hpot _) ?_)
        simp only [hcont, hres, Option.elim, le_refl]
  have hflag : ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * cont o1 ≤
      wflag tg initial model (sign >>= next) budget s := by
    rw [wflag_bind]
    exact le_add_self
  rw [interp_bind, tsum_probOutput_bind_mul]
  calc _ ≤ ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * (weight tg initial o1.2 * canonR o1 + b0 * cont o1) := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support (interp tg initial model sign budget s)
        · exact mul_le_mul_right (hpoint o1 ho1) _
        · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
    _ = ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * (weight tg initial o1.2 * canonR o1) +
          b0 * ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * cont o1 := by
        simp only [mul_add, ENNReal.tsum_add, mul_left_comm _ b0, ENNReal.tsum_mul_left]
    _ ≤ _ := add_le_add (sign_expectW tg initial model parameter data wbar b0 Fail m hparse hkind hfair hb0
          digestAttemptLimit budget s P L hm d hP hcount) (mul_le_mul_right hflag _)

theorem goodW_finish (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (L : QueryLog SigningSpec) (forgery : Forgery) :
    GoodW parameter data wbar b0 Fail Qtot tg initial model L (finishGame parameter data L forgery) := by
  unfold finishGame
  exact goodW_liftHash parameter data wbar b0 Fail Qtot tg initial model hparse hkind hdigest hw hb0 L _ _
    fun v => goodW_pure parameter data wbar b0 Fail Qtot tg initial model hw L forgery v

/-- **The weighted one-coin potential through any adversary that never repeats a message.** -/
theorem goodW_advProg (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    {Cmax : ℕ} (hfair : Fair wbar Cmax) (hb0 : b0 ≠ ⊤) (hQ : Qtot + digestAttemptLimit ≤ Cmax) :
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec),
      NoRepeat M (L.map Sigma.fst) →
        GoodW parameter data wbar b0 Fail Qtot tg initial model L (advProg parameter data M L) := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L _
      rw [advProg_pure]
      exact goodW_finish parameter data wbar b0 Fail Qtot tg initial model hparse hkind hdigest hfair.le_one hb0 L
        forgery
  | query_bind input next ih =>
      intro L hnr
      rcases input with (draw | bytes) | message
      · rw [advProg_draw]
        exact goodW_draw parameter data wbar b0 Fail Qtot tg initial model L draw _ fun v => ih v L (hnr v)
      · rw [advProg_hash]
        exact goodW_ordinary parameter data wbar b0 Fail Qtot tg initial model hparse hkind hdigest hfair.le_one hb0
          L bytes _ fun v => ih v L (hnr v)
      · rw [advProg_sign]
        obtain ⟨hnot, hrest⟩ := (noRepeat_sign message next _).1 hnr
        have hm : ∀ entry ∈ L, entry.1 ≠ message := by
          intro entry he heq
          exact hnot (heq ▸ List.mem_map_of_mem he)
        refine goodW_sign parameter data wbar b0 Fail Qtot tg initial model hparse hkind hfail hfair hb0 hQ message L
          hm _ fun r => ih r _ ?_
        rw [List.map_append]
        exact hrest r

end GoodW

end LeanSphincs.Security.ForsPotential
