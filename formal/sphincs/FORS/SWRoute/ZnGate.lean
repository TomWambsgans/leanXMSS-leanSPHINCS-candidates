import FORS.SWRoute.ArmAccount
import FORS.SWRoute.SignBound

/-! **The gated near potential `Z_n` pays the arming account.** The near potential is the generic
one-coin potential with the near witness (`potG … witnessNear …`), gated by the route's sticky near
flag, plus the cap term on the landed pairs of unsigned messages. Weighted by an abstract weight
`wt`, it pays the arming account `acctArm` (the route's `WA`) and the baseline `b0` per weighted
digest query (`wcount … tg.digest`, the route's `WF`):

  `WA ≤ wt_start · Z_n(start) + b0 · WF`   (`goodN_advProg`).

At an arming step the flag goes on, so the gated potential drops to zero, while the potential before
the step is at least one: some unsigned cached landed pair has realized near witness at least one
(the release, `hrel`). Elsewhere the potential is the generic one-coin potential: a new pair costs the
baseline, other queries do not raise it, and a signing call does not raise it in the weighted mean
(`sign_expectGA`). The release is stated through an abstract run invariant `J` of the state, the
signing log and the reveals; it holds while the adversary has asked at most `N` signatures
(`SignBound`). -/

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

/-! ### The potential -/

section Defs

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Lmax : ℕ)

/-- **The gated near potential** with the cap term on the landed pairs of unsigned messages. -/
noncomputable def potNG (flag : Bool) (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (k : ℕ) : ℝ≥0∞ :=
  potG parameter data witnessNear wbar b0 Fail (fun _ => flag = true) s P Ms L d k +
    lam Lmax (livePairs L P).length k

theorem potNG_true (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (k : ℕ) :
    potNG parameter data wbar b0 Fail Lmax true s P Ms L d k = lam Lmax (livePairs L P).length k := by
  unfold potNG potG
  simp

/-- A new pair costs at most the baseline. -/
theorem new_pair_coreN (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (flag : Bool) (L : QueryLog SigningSpec)
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View)
    (hP : PInv parameter data s P) (hM : MInv parameter data s Ms) (p : Pair)
    (hp0 : s.cache (pblk parameter data p firstCall) = none)
    (hrate : MsgLive L p.1 → Rate parameter data wbar s p.1) :
    pairE (fun u => potNG parameter data wbar b0 Fail Lmax flag (withPair parameter data s p u)
        (addPair parameter P p u) (addMsg Ms p.1) L d (budget - 1)) ≤
      potNG parameter data wbar b0 Fail Lmax flag s P Ms L d budget + b0 := by
  set ℓ := (livePairs L P).length with hℓ
  have hlam : pairE (fun u => lam Lmax (livePairs L (addPair parameter P p u)).length (budget - 1)) ≤
      lam Lmax ℓ budget := by
    by_cases hlive : MsgLive L p.1
    · have hl : ∀ u : DigestCall → HashOutput,
          lam Lmax (livePairs L (addPair parameter P p u)).length (budget - 1) =
          if Landed parameter (blockIndex (u firstCall)) then lam Lmax (ℓ + 1) (budget - 1)
          else lam Lmax ℓ (budget - 1) := by
        intro u
        unfold addPair livePairs
        split_ifs with hl
        · rw [List.filter_cons, if_pos (by simpa using hlive), List.length_cons]
          rfl
        · rfl
      simp only [hl]
      have := lam_newPair parameter Lmax ℓ (budget - 1)
      rw [Nat.sub_add_cancel hb] at this
      exact le_of_eq this
    · have hl : ∀ u : DigestCall → HashOutput,
          lam Lmax (livePairs L (addPair parameter P p u)).length (budget - 1) =
            lam Lmax ℓ (budget - 1) := by
        intro u
        unfold addPair livePairs
        split_ifs with hl
        · rw [List.filter_cons, if_neg (by simpa using hlive)]
          rfl
        · rfl
      simp only [hl, pairE_const]
      exact lam_mono le_rfl (Nat.sub_le _ _)
  unfold potNG
  rw [pairE_add, add_right_comm]
  refine add_le_add ?_ hlam
  unfold potG
  by_cases hr : flag = true ∨ signatureLimit < L.length
  · simp only [if_pos hr, pairE_const]
    exact bot_le
  · simp only [if_neg hr]
    have hcore : coreG parameter data witnessNear wbar b0 Fail s P Ms L d (signatureLimit - L.length) budget =
        coreG parameter data witnessNear wbar b0 Fail s P Ms L d (signatureLimit - L.length) (budget - 1 + 1) := by
      rw [Nat.sub_add_cancel hb]
    rw [hcore]
    exact coreG_newPair wbar b0 Fail witnessNear_props hw hb0 hP hM hp0 L hrate d _ (budget - 1)

end Defs

/-! ### The arming account is at most the weight -/

section ArmLe

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  {model : HiddenRows.Model HashInput HashOutput A Coordinate} {wt : State → ℝ≥0∞} (hW : WtSpec model wt IsMsgInput)
  (Arms : State → CostSpec.Domain → Prop)

/-- Once the flag is on, nothing is paid. -/
theorem acctArm_true {α : Type} (comp : OracleComp CostSpec α) :
    ∀ budget (s : State), acctArm model wt Arms comp budget s true = 0 := by
  induction comp using OracleComp.inductionOn with
  | pure value => intro budget s; rfl
  | query_bind input next ih =>
      intro budget s
      rw [acctArm_query_bind]
      split_ifs
      · simp only [payArm_true, flagNext_true, zero_add, ih, mul_zero, tsum_zero]
      · rfl

include hW in
/-- The arming account pays at most once, so at most the weight. -/
theorem acctArm_le {α : Type} (comp : OracleComp CostSpec α) :
    ∀ budget (s : State) (flag : Bool), acctArm model wt Arms comp budget s flag ≤ wt s := by
  induction comp using OracleComp.inductionOn with
  | pure value => intro budget s flag; exact bot_le
  | query_bind input next ih =>
      intro budget s flag
      rw [acctArm_query_bind]
      split_ifs
      · by_cases harm : flag = false ∧ Arms s input
        · have hp : payArm wt Arms flag s input = wt s := if_pos harm
          have hf : flagNext Arms flag s input = true := by
            obtain ⟨rfl, ha⟩ := harm
            simp [flagNext, ha]
          simp only [hp, hf, acctArm_true, add_zero, ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' tsum_probOutput_le_one
        · have hp : payArm wt Arms flag s input = 0 := if_neg harm
          simp only [hp, zero_add]
          exact le_trans (ENNReal.tsum_le_tsum fun r => mul_le_mul_right (ih r.1 _ r.2 _) _) (hW.step input s)
      · exact bot_le

end ArmLe

/-! ### The paid programs -/

section GoodN

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot Lmax : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (wt : State → ℝ≥0∞) (Arms : State → CostSpec.Domain → Prop)
  (J : State → QueryLog SigningSpec → List Coordinate → Prop)

/-- A program whose arming account is paid by the weighted gated near potential and the weighted
baseline payments. -/
def GoodN (L : QueryLog SigningSpec) (prog : OracleComp CostSpec HiddenBridge.Outcome) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View) (R : List Coordinate) (flag : Bool),
    Prepared initial s → PInv parameter data s P → MInv parameter data s Ms → DInv R d →
      CountInv parameter data Qtot s budget → J s L R → L.length ≤ signatureLimit →
      acctArm model wt Arms prog budget s flag ≤
        wt s * potNG parameter data wbar b0 Fail Lmax flag s P Ms L d budget +
          b0 * wcount model wt tg.digest prog budget s

variable {wt} (hW : WtSpec model wt IsMsgInput) (hcalls : digestCalls = 1)
  (hArmsF : ∀ s input, Arms s input → ∃ x, input = .inl (.inr (.inl x)) ∧ HiddenBridge.IsFleafIn parameter x)
include hW hcalls hArmsF

theorem goodN_draw (L : QueryLog SigningSpec) (draw : ℕ)
    (next : Fin (draw + 1) → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodN parameter data wbar b0 Fail Qtot Lmax tg initial model wt Arms J L (next v)) :
    GoodN parameter data wbar b0 Fail Qtot Lmax tg initial model wt Arms J L
      (liftM (CostSpec.query (.inl (.inl draw))) >>= next) := by
  intro budget s P Ms d R flag hprep hP hM hD hC hJ hL
  have hno : ¬Arms s (.inl (.inl draw)) := fun ha => by
    obtain ⟨x, hx, -⟩ := hArmsF s _ ha
    cases hx
  have hw : wcount model wt tg.digest (liftM (CostSpec.query (.inl (.inl draw))) >>= next) budget s =
      ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
        wcount model wt tg.digest (next v) budget s := by
    rw [wcount_query_bind]
    refine (if_pos (Nat.zero_le budget)).trans ?_
    change ∑' r, Pr[= r | (fun v => (v, s)) <$> (liftM (unifSpec.query draw) : ProbComp _)] *
      (0 + wcount model wt tg.digest (next r.1) (budget - 0) r.2) = _
    rw [tsum_probOutput_map_mul]
    simp only [zero_add, Nat.sub_zero]
  have ha : acctArm model wt Arms (liftM (CostSpec.query (.inl (.inl draw))) >>= next) budget s flag =
      ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
        acctArm model wt Arms (next v) budget s flag := by
    rw [acctArm_query_bind]
    refine (if_pos (Nat.zero_le budget)).trans ?_
    have hp : payArm wt Arms flag s (.inl (.inl draw)) = 0 := by simp [payArm, hno]
    have hf : flagNext Arms flag s (.inl (.inl draw)) = flag := by simp [flagNext, hno]
    rw [hp, hf]
    change ∑' r, Pr[= r | (fun v => (v, s)) <$> (liftM (unifSpec.query draw) : ProbComp _)] *
      (0 + acctArm model wt Arms (next r.1) (budget - 0) r.2 flag) = _
    rw [tsum_probOutput_map_mul]
    simp only [zero_add, Nat.sub_zero]
  rw [hw, ha]
  calc _ ≤ ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
        (wt s * potNG parameter data wbar b0 Fail Lmax flag s P Ms L d budget +
          b0 * wcount model wt tg.digest (next v) budget s) :=
        ENNReal.tsum_le_tsum fun v => mul_le_mul_right (h v budget s P Ms d R flag hprep hP hM hD hC hJ hL) _
    _ ≤ _ := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
        refine add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) (le_of_eq ?_)
        simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

/-- **One ordinary query.** An arming query is paid by the release; any other query is a step of
the one-coin potential with a fixed gate. -/
theorem goodN_ordinary (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hrel : ∀ (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
      (R : List Coordinate) (n k : ℕ) (input : CostSpec.Domain), PInv parameter data s P → DInv R d → J s L R →
      Arms s input → 1 ≤ coreG parameter data witnessNear wbar b0 Fail s P Ms L d n k)
    (hJord : ∀ (s : State) (L : QueryLog SigningSpec) (R : List Coordinate) (x : HashInput) r,
      r ∈ support (ordinaryStep model x s.known s) → J s L R → J r.2 L R)
    (hJstore : ∀ (s : State) (L : QueryLog SigningSpec) (R : List Coordinate) (p : Pair) (u : DigestCall → HashOutput),
      (∀ call, s.cache (pblk parameter data p call) = none) → J s L R → J (withPair parameter data s p u) L R)
    {Cmax : ℕ} (hfair : FairS wbar Cmax Lmax) (hQ : Qtot ≤ Cmax) (hb0 : b0 ≠ ⊤) (L : QueryLog SigningSpec)
    (x : HashInput) (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodN parameter data wbar b0 Fail Qtot Lmax tg initial model wt Arms J L (next v)) :
    GoodN parameter data wbar b0 Fail Qtot Lmax tg initial model wt Arms J L
      (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) := by
  intro budget s P Ms d R flag hprep hP hM hD hC hJ hL
  set input : CostSpec.Domain := .inl (.inr (.inl x)) with hinput
  by_cases hb : 1 ≤ budget
  swap
  · rw [acctArm_query_bind, if_neg (by change ¬1 ≤ budget; exact hb)]
    exact bot_le
  have hacct : acctArm model wt Arms (liftM (CostSpec.query input) >>= next) budget s flag =
      ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        (payArm wt Arms flag s input + acctArm model wt Arms (next r.1) (budget - 1) r.2 (flagNext Arms flag s input)) := by
    rw [acctArm_query_bind, costStep_ordinary]
    exact if_pos hb
  rw [hacct, wcountD_ordinary tg model hW hcalls x next budget hb s]
  set ℓ := (livePairs L P).length with hℓ
  have hmean : ∑' r, Pr[= r | ordinaryStep model x s.known s] * wt r.2 ≤ wt s := by
    have := hW.step input s
    rwa [costStep_ordinary] at this
  -- the invariants after a query that touches no new pair
  have hstep : (¬∃ (p : Pair) (call : DigestCall), x = pblk parameter data p call ∧
      s.cache (pblk parameter data p firstCall) = none) → ∀ r ∈ support (ordinaryStep model x s.known s),
      Prepared initial r.2 ∧ PInv parameter data r.2 P ∧ MInv parameter data r.2 Ms ∧
        CountInv parameter data Qtot r.2 (budget - 1) ∧ J r.2 L R ∧
        (∀ k k', k ≤ k' → ∀ fl : Bool, potNG parameter data wbar b0 Fail Lmax fl r.2 P Ms L d k ≤
          potNG parameter data wbar b0 Fail Lmax fl s P Ms L d k') := by
    intro hnew r hr
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
    refine ⟨fun i o hi => hext.1 i o (hprep i o hi), hP', minv_blocks hblocks hM, hcnt, hJord s L R x r hr hJ,
      fun k k' hk fl => ?_⟩
    unfold potNG
    exact add_le_add (potG_grow wbar b0 Fail witnessNear_props (fun _ _ _ h => h) hfair.le_one hb0 hext hblocks hland
      (fun q hq => (hP.mem q).1 hq) Ms L d hk) (lam_mono le_rfl hk)
  by_cases harm : flag = false ∧ Arms s input
  · -- an arming query: the release pays the weight
    obtain ⟨hf0, ha⟩ := harm
    subst hf0
    obtain ⟨x', hx', hF⟩ := hArmsF s _ ha
    have hxx : x = x' := by simpa [hinput] using hx'
    subst hxx
    have hnew : ¬∃ (p : Pair) (call : DigestCall), x = pblk parameter data p call ∧
        s.cache (pblk parameter data p firstCall) = none := by
      rintro ⟨p, call, rfl, -⟩
      obtain ⟨f, hf⟩ := hF
      exact PotentialA.msg_ne_fleaf (msgInput_digestInput parameter data.root p.1 p.2 call) hf
    have hp : payArm wt Arms false s input = wt s := if_pos ⟨rfl, ha⟩
    have hfl : flagNext Arms false s input = true := by simp [flagNext, ha]
    rw [hp, hfl]
    have hone : 1 ≤ potG parameter data witnessNear wbar b0 Fail (fun _ => false = true) s P Ms L d budget := by
      unfold potG
      rw [if_neg (by simp only [Bool.false_eq_true, false_or, not_lt]; exact hL)]
      exact hrel s P Ms L d R _ _ input hP hD hJ ha
    calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] *
          (wt s + (wt r.2 * lam Lmax ℓ budget + b0 * wcount model wt tg.digest (next r.1) (budget - 1) r.2)) := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support (ordinaryStep model x s.known s)
          · obtain ⟨hprep', hP', hM', hC', hJ', -⟩ := hstep hnew r hr
            refine mul_le_mul_right (add_le_add le_rfl ?_) _
            refine le_trans (h r.1 (budget - 1) r.2 P Ms d R true hprep' hP' hM' hD hC' hJ' hL)
              (add_le_add (mul_le_mul' le_rfl ?_) le_rfl)
            rw [potNG_true]
            exact lam_mono le_rfl (Nat.sub_le _ _)
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ = ∑' r, Pr[= r | ordinaryStep model x s.known s] * wt s +
            ∑' r, Pr[= r | ordinaryStep model x s.known s] * (wt r.2 * lam Lmax ℓ budget) +
            ∑' r, Pr[= r | ordinaryStep model x s.known s] *
              (b0 * wcount model wt tg.digest (next r.1) (budget - 1) r.2) := by
          rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
          exact tsum_congr fun r => by ring
      _ ≤ wt s + wt s * lam Lmax ℓ budget + b0 * ∑' r, Pr[= r | ordinaryStep model x s.known s] *
            wcount model wt tg.digest (next r.1) (budget - 1) r.2 := by
          refine add_le_add (add_le_add ?_ ?_) (le_of_eq ?_)
          · rw [ENNReal.tsum_mul_right]
            exact mul_le_of_le_one_left' tsum_probOutput_le_one
          · calc _ = (∑' r, Pr[= r | ordinaryStep model x s.known s] * wt r.2) * lam Lmax ℓ budget := by
                  rw [← ENNReal.tsum_mul_right]
                  exact tsum_congr fun r => by ring
              _ ≤ _ := mul_le_mul' hmean le_rfl
          · simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]
      _ ≤ _ := by
          unfold potNG
          rw [mul_add]
          refine add_le_add (add_le_add (le_mul_of_one_le_right' hone) le_rfl) (mul_le_mul_right ?_ _)
          exact ENNReal.tsum_le_tsum fun r => mul_le_mul_right le_add_self _
  -- any other query: nothing paid, the flag stays
  have hp : payArm wt Arms flag s input = 0 := if_neg harm
  have hfl : flagNext Arms flag s input = flag := by
    cases flag
    · have hna : ¬Arms s input := fun ha => harm ⟨rfl, ha⟩
      simp [flagNext, hna]
    · simp [flagNext]
  rw [hp, hfl]
  simp only [zero_add]
  by_cases hnew : ∃ (p : Pair) (call : DigestCall), x = pblk parameter data p call ∧
      s.cache (pblk parameter data p firstCall) = none
  · obtain ⟨p, c, rfl, hp0⟩ := hnew
    have hfresh : ∀ call, s.cache (pblk parameter data p call) = none := hP.first p hp0
    have hdig : ∀ call, IsMsgInput (pblk parameter data p call) := fun call =>
      msgInput_digestInput parameter data.root p.1 p.2 call
    rw [ordinaryStep, hparse p c]
    simp only
    rw [readOutside_fresh _ s (hfresh c), tsum_probOutput_map_mul, tsum_probOutput_map_mul]
    have hpay : wpaysA wt tg.digest s (.inl (.inr (.inl (pblk parameter data p c)))) = wt s := by
      change (if tg.digest (pblk parameter data p c) then wt s else 0) = _
      rw [if_pos (hdigest p c)]
    rw [hpay]
    have hsum : ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (wt s + wcount model wt tg.digest (next u) (budget - 1) (s.store (pblk parameter data p c) u)) =
        wt s + ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
          wcount model wt tg.digest (next u) (budget - 1) (s.store (pblk parameter data p c) u) := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' probFailure_eq_zero,
        one_mul]
    rw [hsum]
    have hpairE : ∀ F : (DigestCall → HashOutput) → ℝ≥0∞,
        pairE F = ((Fintype.card HashOutput : ℝ≥0∞) ^ digestCalls)⁻¹ * ∑ u, F u := by
      intro F
      unfold pairE
      rw [tsum_uniform_eq, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    have hpre : ∑' v, Pr[= v | ($ᵗ HashOutput : ProbComp HashOutput)] *
          acctArm model wt Arms (next v) (budget - 1) (s.store (pblk parameter data p c) v) flag =
        pairE (fun u => acctArm model wt Arms (next (u c)) (budget - 1) (withPair parameter data s p u) flag) := by
      rw [hpairE]
      exact presample_one hcalls (pblk parameter data p) c s (fun v s' =>
        acctArm model wt Arms (next v) (budget - 1) s' flag)
    have hcount : pairE (fun u => wcount model wt tg.digest (next (u c)) (budget - 1)
          (withPair parameter data s p u)) =
        ∑' v, Pr[= v | ($ᵗ HashOutput : ProbComp HashOutput)] *
          wcount model wt tg.digest (next v) (budget - 1) (s.store (pblk parameter data p c) v) := by
      rw [hpairE]
      exact (presample_one hcalls (pblk parameter data p) c s (fun v s' =>
        wcount model wt tg.digest (next v) (budget - 1) s')).symm
    rw [hpre]
    by_cases hcap : 1 ≤ lam Lmax ℓ budget
    · -- more landed pairs than the cap: the cap term pays everything
      calc _ ≤ pairE (fun _ => wt s) := by
            refine pairE_mono fun u => (acctArm_le hW Arms _ _ _ _).trans ?_
            exact wt_storeAll_le hW (pblk parameter data p) u s (pblk_call_injective parameter data p) hdig hfresh
        _ = wt s := pairE_const _
        _ ≤ wt s * lam Lmax ℓ budget := le_mul_of_one_le_right' hcap
        _ ≤ _ := by
            unfold potNG
            exact le_trans (mul_le_mul' le_rfl le_add_self) le_self_add
    have hlen : ℓ ≤ Lmax := by
      by_contra hlt
      exact hcap (one_le_lam (by omega) budget)
    have hrate : MsgLive L p.1 → Rate parameter data wbar s p.1 := fun hlive =>
      rate_of_fair hfair s p.1 (by have := hC p.1; omega) (le_trans (landedCount_le hP L hlive) hlen)
    have hC2 : ∀ a, CountInv parameter data Qtot (withPair parameter data s p a) (budget - 1) := by
      intro a mm
      have h1 := count_withPair (parameter := parameter) (data := data) mm s p a
      have h2 := hC mm
      omega
    have hone : ∀ u, acctArm model wt Arms (next (u c)) (budget - 1) (withPair parameter data s p u) flag ≤
        wt s * potNG parameter data wbar b0 Fail Lmax flag (withPair parameter data s p u)
            (addPair parameter P p u) (addMsg Ms p.1) L d (budget - 1) +
          b0 * wcount model wt tg.digest (next (u c)) (budget - 1) (withPair parameter data s p u) := fun u => by
      have := h (u c) (budget - 1) _ _ _ d R flag
        (fun x v hx => (extends_withPair hP hp0 u).1 x v (hprep x v hx)) (pinv_withPair hP hp0 u)
        (minv_withPair hM p u) hD (hC2 u) (hJstore s L R p u hfresh hJ) hL
      exact this.trans (add_le_add (mul_le_mul' (wt_storeAll_le hW (pblk parameter data p) u s
        (pblk_call_injective parameter data p) hdig hfresh) le_rfl) le_rfl)
    refine le_trans (pairE_mono hone) ?_
    rw [pairE_add, pairE_const_mul, pairE_const_mul, hcount, mul_add, ← add_assoc]
    refine add_le_add ?_ le_rfl
    calc wt s * pairE (fun u => potNG parameter data wbar b0 Fail Lmax flag (withPair parameter data s p u)
            (addPair parameter P p u) (addMsg Ms p.1) L d (budget - 1))
        ≤ wt s * (potNG parameter data wbar b0 Fail Lmax flag s P Ms L d budget + b0) :=
          mul_le_mul_right (new_pair_coreN parameter data wbar b0 Fail Lmax hfair.le_one hb0 flag L budget hb s P Ms d
            hP hM p hp0 hrate) _
      _ = _ := by ring
  · calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] *
          (wt r.2 * potNG parameter data wbar b0 Fail Lmax flag s P Ms L d budget +
            b0 * wcount model wt tg.digest (next r.1) (budget - 1) r.2) := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support (ordinaryStep model x s.known s)
          · obtain ⟨hprep', hP', hM', hC', hJ', hgrow⟩ := hstep hnew r hr
            refine mul_le_mul_right ?_ _
            refine le_trans (h r.1 (budget - 1) r.2 P Ms d R flag hprep' hP' hM' hD hC' hJ' hL)
              (add_le_add ?_ le_rfl)
            exact mul_le_mul_right (hgrow _ _ (Nat.sub_le _ _) flag) _
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ ≤ _ := by
          simp only [mul_add, ENNReal.tsum_add]
          refine add_le_add ?_ ?_
          · calc _ = (∑' r, Pr[= r | ordinaryStep model x s.known s] * wt r.2) *
                  potNG parameter data wbar b0 Fail Lmax flag s P Ms L d budget := by
                  rw [← ENNReal.tsum_mul_right]
                  exact tsum_congr fun r => by ring
              _ ≤ _ := mul_le_mul' hmean le_rfl
          · refine le_add_left (le_of_eq ?_)
            simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

theorem goodN_pure (L : QueryLog SigningSpec) (forgery : Forgery) (verified : Bool) :
    GoodN parameter data wbar b0 Fail Qtot Lmax tg initial model wt Arms J L (pure (forgery, L, verified)) := by
  intro budget s P Ms d R flag _ _ _ _ _ _ _
  rw [acctArm_pure]
  exact bot_le

/-- **One signing call** on a message never signed before: it asks no FORS leaf query, so it pays
nothing and keeps the flag, and the gated potential does not grow in the weighted mean. -/
theorem goodN_sign (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hJsign : ∀ budget (s : State) (L : QueryLog SigningSpec) (R : List Coordinate) (m : Message)
      (o1 : Run HashInput Coordinate (Option Signature) × State) (r : Option Signature),
      o1 ∈ support (interp tg initial model (signCostSource parameter data m) budget s) → o1.1.1 = some r →
      J s L R → J o1.2 (L ++ [⟨m, r⟩]) (R ++ o1.1.2.1))
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (m : Message) (L : QueryLog SigningSpec) (hm : MsgLive L m)
    (hlt : L.length < signatureLimit)
    (next : Option Signature → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ r, GoodN parameter data wbar b0 Fail Qtot Lmax tg initial model wt Arms J (L ++ [⟨m, r⟩]) (next r)) :
    GoodN parameter data wbar b0 Fail Qtot Lmax tg initial model wt Arms J L
      (signCostSource parameter data m >>= next) := by
  intro budget s P Ms d R flag hprep hP hM hD hC hJ hL
  set sign := signCostSource parameter data m with hsign
  set ℓ := (livePairs L P).length with hℓ
  set gate : State → Prop := fun _ => flag = true with hgate
  set cont : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    o1.1.1.elim 0 fun r => wcount model wt tg.digest (next r) (budget - traceCost o1.1.2.2.1) o1.2 with hcont
  set canonR : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    canonL parameter data witnessNear wbar b0 Fail m s P Ms L d gate budget o1 with hcanonR
  rw [acctArm_bind_avoid model wt Arms tg initial (HiddenBridge.IsFleafIn parameter) hArmsF sign
    (avoids_source_fleaf parameter parameter data m) next budget s flag]
  have hpoint : ∀ o1 ∈ support (interp tg initial model sign budget s),
      o1.1.1.elim 0 (fun r => acctArm model wt Arms (next r) (budget - traceCost o1.1.2.2.1) o1.2 flag) ≤
        wt o1.2 * (canonR o1 + lam Lmax ℓ budget) + b0 * cont o1 := by
    intro o1 ho1
    cases hres : o1.1.1 with
    | none =>
        simp only [Option.elim]
        exact bot_le
    | some r =>
        simp only [Option.elim]
        obtain ⟨hprep', hP', hM', hD', hC', _⟩ := sign_paramsS tg initial model Fail Qtot hparse (hfail m)
          budget s P Ms d R hprep hP hM hD hC o1 ho1 r hres
        have hlen' : (L ++ [(⟨m, r⟩ : (_ : Message) × Option Signature)]).length ≤ signatureLimit := by
          simp only [List.length_append, List.length_singleton]
          omega
        have hIH := h r (budget - traceCost o1.1.2.2.1) o1.2 _ _ _ _ flag hprep' hP' hM' hD' hC'
          (hJsign budget s L R m o1 r ho1 hres hJ) hlen'
        have hpot := sign_pointG_level tg initial model parameter data wbar b0 Fail Qtot m witnessNear_props
          (gate := gate) (fun _ _ _ h => h) hparse (hfail m) hw hb0 budget s P Ms L d R hprep hP hM hD hC o1 ho1 r hres
          (Nat.sub_le budget (traceCost o1.1.2.2.1))
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
        refine le_trans hIH (add_le_add (mul_le_mul' le_rfl ?_) ?_)
        · unfold potNG
          exact add_le_add hpot hlam
        · simp only [hcont, hres, Option.elim, le_refl]
  have hflag : ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * cont o1 ≤
      wcount model wt tg.digest (sign >>= next) budget s := by
    rw [wcount_bind model wt tg.digest tg initial]
    exact le_add_self
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
        unfold potNG
        rw [mul_add]
        exact add_le_add (add_le_add
          (sign_expectGA tg initial model hW hcalls parameter data wbar b0 Fail m witnessNear_props gate hparse hkind
            hb0 budget budget s P Ms L hm d hP hM)
          (interp_wt_const tg initial hW sign budget s _)) (mul_le_mul_right hflag _)

variable (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
  (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
  (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
  (hrel : ∀ (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (R : List Coordinate) (n k : ℕ) (input : CostSpec.Domain), PInv parameter data s P → DInv R d → J s L R →
    Arms s input → 1 ≤ coreG parameter data witnessNear wbar b0 Fail s P Ms L d n k)
  (hJord : ∀ (s : State) (L : QueryLog SigningSpec) (R : List Coordinate) (x : HashInput) r,
    r ∈ support (ordinaryStep model x s.known s) → J s L R → J r.2 L R)
  (hJstore : ∀ (s : State) (L : QueryLog SigningSpec) (R : List Coordinate) (p : Pair) (u : DigestCall → HashOutput),
    (∀ call, s.cache (pblk parameter data p call) = none) → J s L R → J (withPair parameter data s p u) L R)
  {Cmax : ℕ} (hfair : FairS wbar Cmax Lmax) (hQ : Qtot ≤ Cmax) (hb0 : b0 ≠ ⊤)

include hparse hkind hdigest hrel hJord hJstore hfair hQ hb0 in
/-- Lifted hash computations are sequences of ordinary queries. -/
theorem goodN_liftHash (L : QueryLog SigningSpec) {α : Type} (computation : OracleComp HashSpec α)
    (next : α → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ a, GoodN parameter data wbar b0 Fail Qtot Lmax tg initial model wt Arms J L (next a)) :
    GoodN parameter data wbar b0 Fail Qtot Lmax tg initial model wt Arms J L
      ((liftM computation : OracleComp CostSpec α) >>= next) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [liftM_pure, pure_bind] using h value
  | query_bind query rest ih =>
      rw [liftM_bind, bind_assoc]
      exact goodN_ordinary parameter data wbar b0 Fail Qtot Lmax tg initial model Arms J hW hcalls hArmsF hparse hkind
        hdigest hrel hJord hJstore hfair hQ hb0 L query _ ih

include hparse hkind hdigest hrel hJord hJstore hfair hQ hb0 in
theorem goodN_finish (L : QueryLog SigningSpec) (forgery : Forgery) :
    GoodN parameter data wbar b0 Fail Qtot Lmax tg initial model wt Arms J L (finishGame parameter data L forgery) := by
  unfold finishGame
  exact goodN_liftHash parameter data wbar b0 Fail Qtot Lmax tg initial model Arms J hW hcalls hArmsF hparse hkind
    hdigest hrel hJord hJstore hfair hQ hb0 L _ _
    fun v => goodN_pure parameter data wbar b0 Fail Qtot Lmax tg initial model Arms J hW hcalls hArmsF L forgery v

include hparse hkind hdigest hrel hJord hJstore hfair hQ hb0 in
/-- **The gated near potential pays the arming account through any adversary that never repeats a
message and asks at most `N` signatures.** -/
theorem goodN_advProg
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hJsign : ∀ budget (s : State) (L : QueryLog SigningSpec) (R : List Coordinate) (m : Message)
      (o1 : Run HashInput Coordinate (Option Signature) × State) (r : Option Signature),
      o1 ∈ support (interp tg initial model (signCostSource parameter data m) budget s) → o1.1.1 = some r →
      J s L R → J o1.2 (L ++ [⟨m, r⟩]) (R ++ o1.1.2.1)) :
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec),
      NoRepeat M (L.map Sigma.fst) → SignBound M (signatureLimit - L.length) →
        GoodN parameter data wbar b0 Fail Qtot Lmax tg initial model wt Arms J L (advProg parameter data M L) := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L _ _
      rw [advProg_pure]
      exact goodN_finish parameter data wbar b0 Fail Qtot Lmax tg initial model Arms J hW hcalls hArmsF hparse hkind
        hdigest hrel hJord hJstore hfair hQ hb0 L forgery
  | query_bind input next ih =>
      intro L hnr hsb
      rcases input with (draw | bytes) | message
      · rw [advProg_draw]
        exact goodN_draw parameter data wbar b0 Fail Qtot Lmax tg initial model Arms J hW hcalls hArmsF L draw _
          fun v => ih v L (hnr v) (hsb v)
      · rw [advProg_hash]
        exact goodN_ordinary parameter data wbar b0 Fail Qtot Lmax tg initial model Arms J hW hcalls hArmsF hparse hkind
          hdigest hrel hJord hJstore hfair hQ hb0 L bytes _ fun v => ih v L (hnr v) (hsb v)
      · rw [advProg_sign]
        obtain ⟨hnot, hrest⟩ := (noRepeat_sign message next _).1 hnr
        obtain ⟨hpos, hsrest⟩ := (signBound_sign message next _).1 hsb
        have hm : MsgLive L message := by
          intro entry he heq
          exact hnot (heq ▸ List.mem_map_of_mem he)
        refine goodN_sign parameter data wbar b0 Fail Qtot Lmax tg initial model Arms J hW hcalls hArmsF hparse hkind
          hfail hJsign hfair.le_one hb0 message L hm (by omega) _ fun r => ih r _ ?_ ?_
        · rw [List.map_append]
          exact hrest r
        · have hlen : signatureLimit - (L ++ [(⟨message, r⟩ : (_ : Message) × Option Signature)]).length =
              signatureLimit - L.length - 1 := by
            simp only [List.length_append, List.length_singleton]
            omega
          rw [hlen]
          exact hsrest r

end GoodN

end FORS.Security.SWRoute
