import FORS.SWRoute.ZnGate
import FORS.SWRoute.State

/-! **The P-part of the SW route.** The route's weighted potentials pay, over the interpreted run of
the rest of the game from the start state,

  `E[weightA_end · cover] + δ · WA + WK
     ≤ q' · startExcessO(wbar, b0c) + δ · q' · startExcessG witnessNear (wbar, b0n)
       + (A4' bound) + (b0c + δ · b0n) · WF + (failing indices and cap terms)`.

The cover potential `Z_c` pays the weighted cover (`goodWA_advProg`), the gated near potential `Z_n`
pays the arming account `WA` (`goodN_advProg`), and the contact potential `A4'` pays the kill
account `WK` (its bound is the hypothesis `hA4` here; see `notes/CORE-P.md`). This file connects the
route's accounts (`SWRoute/State.lean`) with the generic ones and adds the three parts. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.LoopWalk ForsPotential PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### The route's accounts as the generic ones -/

section Bridge

variable {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate) (K : Ctx) (root : Digest)

theorem payF_eq (s : PotentialA.St) (input : CostSpec.Domain) :
    payF K root s input = wpaysA (weightA K root) K.tg.digest s input := by
  rcases input with (draw | (bytes | coordinate)) | amount <;> rfl

/-- `WF` is the generic weighted digest account. -/
theorem WF_eq_wcount {α : Type} (comp : OracleComp CostSpec α) :
    ∀ budget (s : PotentialA.St), WF model K root comp budget s = wcount model (weightA K root) K.tg.digest comp budget s := by
  induction comp using OracleComp.inductionOn with
  | pure value => intro budget s; rfl
  | query_bind input next ih =>
      intro budget s
      change acct model (fun s input _ => payF K root s input) (liftM (CostSpec.query input) >>= next) budget s = _
      rw [acct_query_bind, wcount_query_bind]
      split_ifs
      · refine tsum_congr fun r => ?_
        rw [payF_eq]
        exact congrArg _ (congrArg _ (ih r.1 _ r.2))
      · rfl

/-- `WA` is the generic arming account with the route's trigger. -/
theorem WA_eq_acctArm {α : Type} (comp : OracleComp CostSpec α) :
    ∀ budget (s : PotentialA.St) (flag : Bool),
      WA model K root comp budget s flag = acctArm model (weightA K root) (ArmsAt K root) comp budget s flag := by
  induction comp using OracleComp.inductionOn with
  | pure value => intro budget s flag; rfl
  | query_bind input next ih =>
      intro budget s flag
      change acctA model K root (liftM (CostSpec.query input) >>= next) budget s flag = _
      rw [acctA_query_bind, acctArm_query_bind]
      split_ifs
      · refine tsum_congr fun r => ?_
        exact congrArg _ (congrArg _ (ih r.1 _ r.2 _))
      · rfl

/-- The route's arming trigger is a FORS leaf query. -/
theorem armsAt_fleaf (s : PotentialA.St) (input : CostSpec.Domain) (h : ArmsAt K root s input) :
    ∃ x, input = .inl (.inr (.inl x)) ∧ HiddenBridge.IsFleafIn K.p x := by
  obtain ⟨f, rfl, -⟩ := h
  exact ⟨_, rfl, f, rfl⟩

end Bridge

/-! ### The near potential at the start -/

theorem potNG_start_le (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞)
    (Fail : Finset (Fin (2 ^ subtreeHeight))) (Lmax : ℕ) (s : State) (k : ℕ) :
    potNG parameter data wbar b0 Fail Lmax false s [] [] [] 0 k ≤
      (k * (startExcessG witnessNear wbar b0 k + failMass Fail) + signatureLimit * failMass Fail) +
        lam Lmax 0 k := by
  unfold potNG potG
  refine add_le_add ?_ (le_of_eq rfl)
  rw [if_neg (by simp)]
  unfold coreG
  simp only [List.map_nil, List.sum_nil, zero_add, List.length_nil, Nat.sub_zero]
  rfl

/-! ### The three parts together -/

section Sum

variable (K : Ctx) (data : PublicData) {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (wbar b0c b0n : ℝ≥0∞) (δ : ℝ) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Lmax : ℕ)

/-- **The P-part from the contact part.** With the cover potential at baseline `b0c` and the gated
near potential at baseline `b0n` (both weighted by `weightA`), the weighted cover, `δ` times the
arming account and the kill account are paid by the start values, the bound `B4` of the kill
account (the contact potential A4'), the baselines per weighted digest query, and the failing
indices and cap terms. The near potential's release is stated through a run invariant `J`. -/
theorem ppart_of_A4 (hcalls : digestCalls = 1) (hW : WtSpec model (weightA K data.root) IsMsgInput)
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none)
    (hkind : ∀ p call, K.tg.kind (pblk K.p data p call) = .none)
    (hdigest : ∀ p call, K.tg.digest (pblk K.p data p call))
    (hclean : ∀ p call, K.initial (pblk K.p data p call) = none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared K.initial s1 →
      ∀ out ∈ support (interp K.tg K.initial model (finishRest K.p data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (total : ℕ) (hfair : FairS wbar (total + digestAttemptLimit) Lmax) (hb0n : b0n ≠ ⊤)
    (J : State → QueryLog SigningSpec → List Coordinate → Prop)
    (hrel : ∀ (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
      (R : List Coordinate) (n k : ℕ) (input : CostSpec.Domain), PInv K.p data s P → DInv R d → J s L R →
      ArmsAt K data.root s input → 1 ≤ coreG K.p data witnessNear wbar b0n Fail s P Ms L d n k)
    (hJord : ∀ (s : State) (L : QueryLog SigningSpec) (R : List Coordinate) (x : HashInput) r,
      r ∈ support (ordinaryStep model x s.known s) → J s L R → J r.2 L R)
    (hJstore : ∀ (s : State) (L : QueryLog SigningSpec) (R : List Coordinate) (p : Pair) (u : DigestCall → HashOutput),
      (∀ call, s.cache (pblk K.p data p call) = none) → J s L R → J (withPair K.p data s p u) L R)
    (hJsign : ∀ budget (s : State) (L : QueryLog SigningSpec) (R : List Coordinate) (m : Message)
      (o1 : Run HashInput Coordinate (Option Signature) × State) (r : Option Signature),
      o1 ∈ support (interp K.tg K.initial model (signCostSource K.p data m) budget s) → o1.1.1 = some r →
      J s L R → J o1.2 (L ++ [⟨m, r⟩]) (R ++ o1.1.2.1))
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M [])
    (hsb : SignBound M signatureLimit) (known : HiddenReveal.Knowledge Coordinate)
    (hw1 : weightA K data.root (DebtState.start K.initial known) = 1)
    (hJ0 : J (DebtState.start K.initial known) [] [])
    (B4 : ℝ≥0∞)
    (hA4 : WK model K data.root (advProg K.p data M []) total (DebtState.start K.initial known) ≤ B4) :
    ∑' out, Pr[= out | interp K.tg K.initial model (advProg K.p data M []) total (DebtState.start K.initial known)] *
        (weightA K data.root out.2 * finalValue K.p data K.tg K.initial [] out) +
      ENNReal.ofReal δ * WA model K data.root (advProg K.p data M []) total (DebtState.start K.initial known) false +
      WK model K data.root (advProg K.p data M []) total (DebtState.start K.initial known) ≤
    (total * startExcessO wbar b0c total + ENNReal.ofReal δ * (total * startExcessG witnessNear wbar b0n total)) +
      B4 + (b0c + ENNReal.ofReal δ * b0n) *
        WF model K data.root (advProg K.p data M []) total (DebtState.start K.initial known) +
      (1 + ENNReal.ofReal δ) * ((total * failMass Fail + signatureLimit * failMass Fail) + lam Lmax 0 total) := by
  set start := DebtState.start K.initial known with hstart
  set prog := advProg K.p data M [] with hprog
  set wF := WF model K data.root prog total start with hwF
  have hwF' : wF = wcount model (weightA K data.root) K.tg.digest prog total start :=
    WF_eq_wcount model K data.root prog total start
  -- the cover part
  have hcov := goodWA_advProg K.p data wbar b0c Fail total Lmax K.tg K.initial model hW hcalls hparse hkind hdigest
    hfail hfair (Nat.le_add_right _ _) M [] hnr total start [] [] 0 [] (start_prepared K.initial known)
    (start_pinv K.p data K.initial hclean known) (start_minv K.p data K.initial hclean known)
    (fun _ _ _ _ h => by cases h) (start_count K.p data K.initial hclean known total)
  rw [hw1, one_mul, ← hwF'] at hcov
  -- the near part
  have hnear := goodN_advProg K.p data wbar b0n Fail total Lmax K.tg K.initial model (ArmsAt K data.root) J hW hcalls
    (armsAt_fleaf K data.root) hparse hkind hdigest hrel hJord hJstore hfair (Nat.le_add_right _ _) hb0n hfail hJsign
    M [] hnr (by simpa using hsb) total start [] [] 0 [] false (start_prepared K.initial known)
    (start_pinv K.p data K.initial hclean known) (start_minv K.p data K.initial hclean known)
    (fun _ _ _ _ h => by cases h) (start_count K.p data K.initial hclean known total) hJ0 (by simp)
  rw [hw1, one_mul, ← hwF', ← WA_eq_acctArm] at hnear
  have hpO := potO_start_le K.p data wbar b0c Fail K.tg K.initial Lmax start total
  have hpN := potNG_start_le K.p data wbar b0n Fail Lmax start total
  set F : ℝ≥0∞ := (total * failMass Fail + signatureLimit * failMass Fail) + lam Lmax 0 total with hF
  have hO : potO K.p data wbar b0c Fail K.tg K.initial Lmax start [] [] [] 0 total ≤
      total * startExcessO wbar b0c total + F := by
    refine hpO.trans (le_of_eq ?_)
    rw [hF]
    ring
  have hN : potNG K.p data wbar b0n Fail Lmax false start [] [] [] 0 total ≤
      total * startExcessG witnessNear wbar b0n total + F := by
    refine hpN.trans (le_of_eq ?_)
    rw [hF]
    ring
  calc _ ≤ (total * startExcessO wbar b0c total + F + b0c * wF) +
        ENNReal.ofReal δ * (total * startExcessG witnessNear wbar b0n total + F + b0n * wF) + B4 := by
        refine add_le_add (add_le_add (hcov.trans (add_le_add hO le_rfl)) (mul_le_mul' le_rfl
          (hnear.trans (add_le_add hN le_rfl)))) hA4
    _ = _ := by ring

end Sum

end FORS.Security.SWRoute
