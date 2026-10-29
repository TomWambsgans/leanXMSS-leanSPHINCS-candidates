import FORS.SWRoute.ContactPot
import FORS.SWRoute.Release
import FORS.SWRoute.StepsBase

/-! **The contact potential A4' pays the kill account.** The potential of a state is the sum, over
its decided FORS contacts, of the contact's coefficient (the reveal rate of the remaining
signatures, the cached-pair share `cinv` per live landed pair at the cell plus the creation rate of
the remaining budget, and the capped own-cell near forecast), plus the coin forecast of the future
contacts, the coin cap and the landed-pair cap. Weighted by `weightA`, it pays the kill account `WK`,
`cU` per weighted FORS leaf query whose contact would survive (`WC`), and `ν` times the excess
account `XS m` (`goodK_advProg`). -/

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

/-! ### Accounts: sequencing -/

section AcctBind

variable {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (pay : PotentialA.St → CostSpec.Domain → PotentialA.St → ℝ≥0∞)

/-- A flag-free account of a sequential run splits at the end of the first computation. -/
theorem acct_bind {α β : Type} (first : OracleComp CostSpec α) (next : α → OracleComp CostSpec β) :
    ∀ budget (s : PotentialA.St),
      acct model pay (first >>= next) budget s =
        acct model pay first budget s +
          ∑' o1, Pr[= o1 | interp tg initial model first budget s] *
            o1.1.1.elim 0 (fun value => acct model pay (next value) (budget - traceCost o1.1.2.2.1) o1.2) := by
  induction first using OracleComp.inductionOn with
  | pure value =>
      intro budget s
      rw [pure_bind, acct_pure, interp_pure, tsum_probOutput_pure_mul, zero_add]
      simp only [Option.elim, traceCost, List.map_nil, List.sum_nil, Nat.sub_zero]
  | query_bind input rest ih =>
      intro budget s
      rw [bind_assoc, acct_query_bind, acct_query_bind, interp_query_bind]
      split_ifs with hcost
      · rw [tsum_probOutput_bind_mul, ← ENNReal.tsum_add]
        refine tsum_congr fun r => ?_
        rw [tsum_probOutput_map_mul, ih r.1 (budget - sourceCost input) r.2]
        simp only [traceCost_append, recorded_cost, Nat.sub_sub]
        ring
      · rw [tsum_probOutput_pure_mul]
        simp

end AcctBind

/-! ### The potential -/

section Defs

variable (K : Ctx) (data : PublicData) (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Lmax T : ℕ)

/-- **The coefficient of a contact at a cell.** -/
noncomputable def coefK (c : Cell) (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (k : ℕ) : ℝ≥0∞ :=
  sigRiskF L + cinv * (ncell K.p data c s P L + k * revRate) + min 1 (PiC K data wbar Fail c s P Ms L d k)

/-- The coin forecast of the future contacts: one coefficient's coin part `cinv (T + j revRate)` per
remaining unit of budget. -/
noncomputable def coinPotK (k : ℕ) : ℝ≥0∞ :=
  ν * cinv * (k * T + ((Nat.choose k 2 : ℕ) : ℝ≥0∞) * revRate)

/-- **The contact potential A4'.** -/
noncomputable def psiK (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (k : ℕ) : ℝ≥0∞ :=
  (∑ f : FIn, if FCk K s f then coefK K data wbar Fail (CellOf f) s P Ms L d k else 0) +
    coinPotK T k + capC K.p data T k s P L + lam Lmax (livePairs L P).length k

/-- One unit of budget releases one contact's coin part. -/
theorem coinPotK_succ (k : ℕ) : coinPotK T (k + 1) = coinPotK T k + ν * cinv * (T + k * revRate) := by
  unfold coinPotK
  rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
  push_cast
  ring

/-- The invariants of the induction. -/
structure InvK (Qtot : ℕ) (budget : ℕ) (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (R : List Coordinate) : Prop where
  prep : Prepared K.initial s
  pinv : PInv K.p data s P
  minv : MInv K.p data s Ms
  dinv : DInv R d
  count : CountInv K.p data Qtot s budget
  jinv : JInv K.p data s L R
  len : L.length ≤ signatureLimit

variable {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate) (cU m : ℝ≥0∞) (Qtot : ℕ)

/-- **An adversary program whose kill account is paid** by the weighted contact potential, `cU` per
weighted surviving FORS leaf query and `ν` times the excess account. -/
def GoodK (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View) (R : List Coordinate),
    InvK K data Qtot budget s P Ms L d R →
      WK model K data.root (advProg K.p data M L) budget s ≤
        weightA K data.root s * psiK K data wbar Fail Lmax T s P Ms L d budget +
          cU * WC model K data.root (advProg K.p data M L) budget s +
          ν * XS K data.root data wbar Fail model m M L budget s P Ms d

/-- A draw moves nothing. -/
theorem goodK_draw (L : QueryLog SigningSpec) (draw : ℕ)
    (next : Fin (draw + 1) → OracleComp (OracleWorld + SigningSpec) Forgery)
    (h : ∀ v, GoodK K data wbar Fail Lmax T model cU m Qtot (next v) L) :
    GoodK K data wbar Fail Lmax T model cU m Qtot
      (liftM ((OracleWorld + SigningSpec).query (.inl (.inl draw))) >>= next) L := by
  intro budget s P Ms d R hI
  rw [advProg_draw, XS_draw]
  have hacc : ∀ (pay : PotentialA.St → CostSpec.Domain → PotentialA.St → ℝ≥0∞),
      pay s (.inl (.inl draw)) s = 0 →
      acct model pay (liftM (CostSpec.query (.inl (.inl draw))) >>= fun v => advProg K.p data (next v) L) budget s =
        ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
          acct model pay (advProg K.p data (next v) L) budget s := by
    intro pay hpay
    rw [acct_query_bind]
    refine (if_pos (Nat.zero_le budget)).trans ?_
    change ∑' r, Pr[= r | (fun v => (v, s)) <$> (liftM (unifSpec.query draw) : ProbComp _)] *
      (pay s (.inl (.inl draw)) r.2 + acct model pay (advProg K.p data (next r.1) L) (budget - 0) r.2) = _
    rw [tsum_probOutput_map_mul]
    simp only [hpay, zero_add, Nat.sub_zero]
  have hK : WK model K data.root (liftM (CostSpec.query (.inl (.inl draw))) >>= fun v =>
      advProg K.p data (next v) L) budget s =
      ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
        WK model K data.root (advProg K.p data (next v) L) budget s :=
    hacc _ (by simp [payK])
  have hC : WC model K data.root (liftM (CostSpec.query (.inl (.inl draw))) >>= fun v =>
      advProg K.p data (next v) L) budget s =
      ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
        WC model K data.root (advProg K.p data (next v) L) budget s :=
    hacc _ (by simp [payC])
  rw [hK, hC]
  calc _ ≤ ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
        (weightA K data.root s * psiK K data wbar Fail Lmax T s P Ms L d budget +
          cU * WC model K data.root (advProg K.p data (next v) L) budget s +
          ν * XS K data.root data wbar Fail model m (next v) L budget s P Ms d) :=
        ENNReal.tsum_le_tsum fun v => mul_le_mul_right (h v budget s P Ms d R hI) _
    _ ≤ _ := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
        refine add_le_add (add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) (le_of_eq ?_)) (le_of_eq ?_)
        · simp only [mul_left_comm _ cU, ENNReal.tsum_mul_left]
        · simp only [mul_left_comm _ ν, ENNReal.tsum_mul_left]

/-- **The contact potential through any adversary program**, from its three step obligations: a
hash query (adversary or verifier: the FORS leaf queries, new pairs and other queries), a signing call
on a fresh message while fewer than `N` signatures were asked, and the end of the game. -/
theorem goodK_advProg
    (hhash : ∀ (L : QueryLog SigningSpec) (x : HashInput) (next : HashOutput → OracleComp (OracleWorld + SigningSpec) Forgery),
      (∀ v, GoodK K data wbar Fail Lmax T model cU m Qtot (next v) L) →
        GoodK K data wbar Fail Lmax T model cU m Qtot (liftM ((OracleWorld + SigningSpec).query (.inl (.inr x))) >>= next) L)
    (hsign : ∀ (L : QueryLog SigningSpec) (msg : Message)
      (next : Option Signature → OracleComp (OracleWorld + SigningSpec) Forgery),
      MsgLive L msg → L.length < signatureLimit →
      (∀ r, GoodK K data wbar Fail Lmax T model cU m Qtot (next r) (L ++ [⟨msg, r⟩])) →
        GoodK K data wbar Fail Lmax T model cU m Qtot (liftM ((OracleWorld + SigningSpec).query (.inr msg)) >>= next) L)
    (hpure : ∀ (L : QueryLog SigningSpec) (forgery : Forgery), GoodK K data wbar Fail Lmax T model cU m Qtot (pure forgery) L) :
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec),
      NoRepeat M (L.map Sigma.fst) → SignBound M (signatureLimit - L.length) →
        GoodK K data wbar Fail Lmax T model cU m Qtot M L := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery => intro L _ _; exact hpure L forgery
  | query_bind input next ih =>
      intro L hnr hsb
      rcases input with (draw | bytes) | message
      · exact goodK_draw K data wbar Fail Lmax T model cU m Qtot L draw _ fun v => ih v L (hnr v) (hsb v)
      · exact hhash L bytes _ fun v => ih v L (hnr v) (hsb v)
      · obtain ⟨hnot, hrest⟩ := (noRepeat_sign message next _).1 hnr
        obtain ⟨hpos, hsrest⟩ := (signBound_sign message next _).1 hsb
        have hm : MsgLive L message := by
          intro entry he heq
          exact hnot (heq ▸ List.mem_map_of_mem he)
        refine hsign L message next hm (by omega) fun r => ih r _ ?_ ?_
        · rw [List.map_append]
          exact hrest r
        · have hlen : signatureLimit - (L ++ [(⟨message, r⟩ : (_ : Message) × Option Signature)]).length =
              signatureLimit - L.length - 1 := by
            simp only [List.length_append, List.length_singleton]
            omega
          rw [hlen]
          exact hsrest r

/-- No FORS contact is decided at the start of the run. -/
theorem not_fck_start (known : HiddenReveal.Knowledge Coordinate) (f : FIn) :
    ¬FCk K (DebtState.start K.initial known) f := by
  rintro ⟨u, ⟨hc, hi⟩, -⟩
  change K.initial (f.input K.p) = some u at hc
  rw [hi] at hc
  cases hc

/-- **The kill account from the start**, given the step obligations of `goodK_advProg`. -/
theorem wk_start_le
    (hhash : ∀ (L : QueryLog SigningSpec) (x : HashInput) (next : HashOutput → OracleComp (OracleWorld + SigningSpec) Forgery),
      (∀ v, GoodK K data wbar Fail Lmax T model cU m Qtot (next v) L) →
        GoodK K data wbar Fail Lmax T model cU m Qtot (liftM ((OracleWorld + SigningSpec).query (.inl (.inr x))) >>= next) L)
    (hsign : ∀ (L : QueryLog SigningSpec) (msg : Message)
      (next : Option Signature → OracleComp (OracleWorld + SigningSpec) Forgery),
      MsgLive L msg → L.length < signatureLimit →
      (∀ r, GoodK K data wbar Fail Lmax T model cU m Qtot (next r) (L ++ [⟨msg, r⟩])) →
        GoodK K data wbar Fail Lmax T model cU m Qtot (liftM ((OracleWorld + SigningSpec).query (.inr msg)) >>= next) L)
    (hpure : ∀ (L : QueryLog SigningSpec) (forgery : Forgery), GoodK K data wbar Fail Lmax T model cU m Qtot (pure forgery) L)
    (hclean : ∀ p call, K.initial (pblk K.p data p call) = none)
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M []) (hsb : SignBound M signatureLimit)
    (known : HiddenReveal.Knowledge Coordinate) (hknown : ∀ i κ l, known (Coordinate.fors i κ l 0) = none) :
    WK model K data.root (advProg K.p data M []) Qtot (DebtState.start K.initial known) ≤
      (coinPotK T Qtot + capC K.p data T Qtot (DebtState.start K.initial known) [] [] + lam Lmax 0 Qtot) +
        cU * WC model K data.root (advProg K.p data M []) Qtot (DebtState.start K.initial known) +
        ν * XS K data.root data wbar Fail model m M [] Qtot (DebtState.start K.initial known) [] [] 0 := by
  have hI : InvK K data Qtot Qtot (DebtState.start K.initial known) [] [] [] 0 [] :=
    ⟨start_prepared K.initial known, start_pinv K.p data K.initial hclean known,
      start_minv K.p data K.initial hclean known, (fun _ _ _ _ h => by cases h),
      start_count K.p data K.initial hclean known Qtot, jInv_start K.p data K.initial known hknown, by simp⟩
  have h := goodK_advProg K data wbar Fail Lmax T model cU m Qtot hhash hsign hpure M [] hnr (by simpa using hsb)
    Qtot _ [] [] 0 [] hI
  refine h.trans (add_le_add (add_le_add ?_ le_rfl) le_rfl)
  have hpsi : psiK K data wbar Fail Lmax T (DebtState.start K.initial known) [] [] [] 0 Qtot =
      coinPotK T Qtot + capC K.p data T Qtot (DebtState.start K.initial known) [] [] + lam Lmax 0 Qtot := by
    unfold psiK
    rw [Finset.sum_eq_zero fun f _ => if_neg (not_fck_start K known f), zero_add]
    rfl
  rw [hpsi]
  exact mul_le_of_le_one_left' (weightA_le_one K data.root _)

end Defs

end FORS.Security.SWRoute
