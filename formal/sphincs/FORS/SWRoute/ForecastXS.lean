import FORS.SWRoute.ForecastStep
import FORS.SWRoute.ContactGood

/-! **The excess account is paid by the tail potential: `xs_bound`** (WP-F-B, the WP-F contract of
`notes/CORE-P.md`).

The induction over the adversary program (as `XS` is defined) carries the invariant `InvX`
(`InvK` of the contact potential and `KnownInvB`: every FORS leaf secret of a disclosed view is
known) and the bound

  `XS … M L budget s P Ms d ≤ budget · (1 - m)⁺ · (psi … s P Ms L d budget + lam Lmax ℓ budget)`

(`ℓ` the cached landed pairs of unsigned messages). At an ordinary query the excess payment is at
most `(1 - m)⁺ psi` (`hexc`, WP-F-A's `excPay_le_psi`) and `psi + lam` is a supermartingale
(`psi_newPair` with `lam_newPair`, `psi_grow`, `psi_sign`); once the landed-pair cap is at least one
the crude bound `XS ≤ budget (1 - m)⁺` pays (`XS_le_budget`). At the start `psi + lam ≤ tailSum`, so
`ν XS ≤ x (1 - m)⁺ tailSum ≤ x Pb`. -/

open OracleComp OracleSpec ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.LoopWalk ForsPotential PotentialA
open FORS.Security FORS.Security.H0 FORS.Security.H0Avg FORS.Base.H0

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-! ### The invariant -/

section Inv

variable (K : Ctx) (data : PublicData) (Qtot : ℕ)

/-- Every FORS leaf secret of a disclosed view is known. -/
def KnownInvB (s : State) (d : Multiset View) : Prop :=
  ∀ v ∈ d, ∀ (κ' : FTree) (i : Index), localIdx i = v.1 → s.known (Coordinate.fors i κ' (v.2 κ') 0) ≠ none

/-- **The invariant of the induction.** -/
structure InvX (budget : ℕ) (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (R : List Coordinate) : Prop where
  inv : InvK K data Qtot budget s P Ms L d R
  known : KnownInvB s d

variable {K data Qtot}

theorem knownInvB_extends {s s' : State} (hext : Extends s s') {d : Multiset View} (h : KnownInvB s d) :
    KnownInvB s' d := by
  intro v hv κ' i hi
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 (h v hv κ' i hi)
  rw [hext.2.1 _ _ hw]
  exact Option.some_ne_none _

theorem localIdx_injective (hH : totalHeight = subtreeHeight) : Function.Injective localIdx := by
  intro i j h
  have hi : i.val < 2 ^ subtreeHeight := hH ▸ i.isLt
  have hj : j.val < 2 ^ subtreeHeight := hH ▸ j.isLt
  have h' := congrArg Fin.val h
  simp only [localIdx, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h'
  exact Fin.ext h'

theorem budget_le_of_count {s : State} {budget : ℕ} (hC : CountInv K.p data Qtot s budget) : budget ≤ Qtot :=
  le_trans (Nat.le_add_left _ _) (hC default)

variable {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0)

include hout in
/-- The invariant after an ordinary query that touches no new pair. -/
theorem invX_ordinary {budget : ℕ} {s : State} {P : List Pair} {Ms : List Message} {L : QueryLog SigningSpec}
    {d : Multiset View} {R : List Coordinate} (hI : InvX K data Qtot budget s P Ms L d R) (hb : 1 ≤ budget)
    (x : HashInput) (hnew : ¬∃ (p : Pair) (call : DigestCall), x = pblk K.p data p call ∧
      s.cache (pblk K.p data p firstCall) = none)
    (r : HashOutput × State) (hr : r ∈ support (ordinaryStep model x s.known s)) :
    InvX K data Qtot (budget - 1) r.2 P Ms L d R := by
  obtain ⟨⟨hprep, hP, hM, hD, hC, hJ, hL⟩, hK⟩ := hI
  have hext := ordinaryStep_extends model x s r hr
  have hblocks := same_blocks (parameter := K.p) (data := data) hext (ordinaryStep_cache_ne model x s r hr) hnew
  obtain ⟨hP', -⟩ := same_items K.p data hext (ordinaryStep_cache_ne model x s r hr) hnew hP
  have hcnt : CountInv K.p data Qtot r.2 (budget - 1) := by
    intro m
    have h1 : cachedCount K.p data m r.2 ≤ cachedCount K.p data m s + 1 := by
      rw [cachedCount_eq, cachedCount_eq]
      exact costStep_card_le model _ (.inl (.inr (.inl x))) s r (by rw [costStep_ordinary]; exact hr)
    have h2 := hC m
    omega
  exact ⟨⟨fun i o hi => hext.1 i o (hprep i o hi), hP', minv_blocks hblocks hM, hD, hcnt,
    jInv_ordinary K.p data model hout s L R x r hr hJ, hL⟩, knownInvB_extends hext hK⟩

include hout in
/-- The invariant after a new pair. -/
theorem invX_withPair {budget : ℕ} {s : State} {P : List Pair} {Ms : List Message} {L : QueryLog SigningSpec}
    {d : Multiset View} {R : List Coordinate} (hI : InvX K data Qtot budget s P Ms L d R) (hb : 1 ≤ budget)
    (p : Pair) (hp0 : s.cache (pblk K.p data p firstCall) = none) (u : DigestCall → HashOutput) :
    InvX K data Qtot (budget - 1) (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1) L d R := by
  obtain ⟨⟨hprep, hP, hM, hD, hC, hJ, hL⟩, hK⟩ := hI
  have hext := extends_withPair hP hp0 u
  have hfresh : ∀ call, s.cache (pblk K.p data p call) = none := hP.first p hp0
  have hcnt : CountInv K.p data Qtot (withPair K.p data s p u) (budget - 1) := by
    intro mm
    have h1 := count_withPair (parameter := K.p) (data := data) mm s p u
    have h2 := hC mm
    omega
  exact ⟨⟨fun x v hx => hext.1 x v (hprep x v hx), pinv_withPair hP hp0 u, minv_withPair hM p u, hD, hcnt,
    jInv_withPair K.p data model hout s L R p u hfresh hJ, hL⟩, knownInvB_extends hext hK⟩

include hout in
/-- The invariant after a signing call, when no index fails. -/
theorem invX_sign (hH : totalHeight = subtreeHeight)
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none) (m : Message)
    (hfail : ∀ ρ digest budget (s1 : State), Prepared K.initial s1 →
      ∀ out ∈ support (interp K.tg K.initial model (finishRest K.p data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ (∅ : Finset (Fin (2 ^ subtreeHeight))))
    {budget : ℕ} {s : State} {P : List Pair} {Ms : List Message} {L : QueryLog SigningSpec}
    {d : Multiset View} {R : List Coordinate} (hI : InvX K data Qtot budget s P Ms L d R)
    (hlt : L.length < signatureLimit)
    (o1 : Run HashInput Coordinate (Option Signature) × State)
    (ho1 : o1 ∈ support (interp K.tg K.initial model (signCostSource K.p data m) budget s))
    (r : Option Signature) (hr : o1.1.1 = some r) :
    InvX K data Qtot (budget - traceCost o1.1.2.2.1) o1.2 (newPairs K.p data m s o1.2 ++ P) (addMsg Ms m)
      (L ++ [⟨m, r⟩]) (discAfter K.p data m s d o1) (R ++ o1.1.2.1) := by
  obtain ⟨⟨hprep, hP, hM, hD, hC, hJ, hL⟩, hK⟩ := hI
  obtain ⟨hprep', hP', hM', hD', hC', -⟩ := sign_paramsS K.tg K.initial model ∅ Qtot hparse hfail budget s P Ms d R
    hprep hP hM hD hC o1 ho1 r hr
  have hJ' := jInv_sign K.p data K.tg K.initial model hout hparse budget s L R m o1 r ho1 hr hJ
  have hext := interp_extends K.tg K.initial model _ budget s o1 ho1
  have hlen : (L ++ [(⟨m, r⟩ : (_ : Message) × Option Signature)]).length ≤ signatureLimit := by
    simp only [List.length_append, List.length_singleton]; omega
  refine ⟨⟨hprep', hP', hM', hD', hC', hJ', hlen⟩, ?_⟩
  -- the disclosed views of the signed pair have every FORS secret known
  have hsigned : ∀ (sig : Signature) (u : DigestCall → HashOutput), r = some sig →
      pcache K.p data m o1.2 sig.randomness = some u → KnownInvB o1.2 {viewOf u} := by
    intro sig u hsig hu v hv κ' i hi
    rw [Multiset.mem_singleton] at hv
    subst hv
    obtain ⟨u', hu', hall⟩ := hJ'.2 ⟨m, r⟩ (List.mem_append_right _ (List.mem_singleton_self _)) sig hsig
    rw [hu] at hu'
    cases hu'
    have hi' : i = digestIndex (truncateMessageDigest u) :=
      localIdx_injective hH (hi.trans (localDigestView_fst (truncateMessageDigest u)))
    subst hi'
    exact hall κ'
  have hpost := source_post K.tg K.initial model K.p data m (fun ρ call => hparse (m, ρ) call) ∅ hfail
    budget s hprep o1 ho1 r hr
  have hshape := sign_shape K.p data ∅ m hpost o1 rfl hr
  intro v hv
  unfold discAfter at hv
  rcases Multiset.mem_add.1 hv with hv | hv
  · rcases Multiset.mem_add.1 hv with hv | hv
    · exact knownInvB_extends hext hK v hv
    · rcases hshape with ⟨hnew, _⟩ | ⟨ρ, u, hnew, _, h0, _, _, _, hfl, hsig⟩ | ⟨_, _, _, hnew, _⟩
      · unfold newPairs at hv; rw [hnew] at hv; simp at hv
      · have hlist : newPairs K.p data m s o1.2 = [(m, ρ)] := by
          unfold newPairs; rw [hnew, Finset.toList_singleton]; rfl
        rw [hlist] at hv
        have hpv : pview K.p data o1.2 (m, ρ) = viewOf u := pview_of_pcache (q := (m, ρ)) h0
        simp only [List.map_cons, List.map_nil, Multiset.mem_coe, List.mem_singleton] at hv
        rw [hv, hpv]
        rcases r with _ | sig
        · exact absurd (hfl rfl) (Finset.notMem_empty _)
        · have hρ := hsig sig rfl
          refine hsigned sig u rfl ?_ _ (Multiset.mem_singleton_self _)
          rw [hρ]; exact h0
      · unfold newPairs at hv; rw [hnew] at hv; simp at hv
  · rcases hshape with ⟨_, hpool⟩ | ⟨_, _, _, hpool, _⟩ | ⟨ρ, u, sig, _, hpool, hsig, hρ, _, h0⟩
    · rw [hpool] at hv; simp at hv
    · rw [hpool] at hv; simp at hv
    · rw [hpool] at hv
      refine hsigned sig u hsig ?_ v hv
      rw [hρ]; exact h0

end Inv

/-! ### The crude bound -/

theorem one_sub_ofReal_le (m : ℝ) : 1 - ENNReal.ofReal m ≤ ENNReal.ofReal (1 - m) := by
  rcases le_total 0 m with hm | hm
  · rw [ENNReal.ofReal_sub 1 hm, ENNReal.ofReal_one]
  · rw [ENNReal.ofReal_of_nonpos hm, tsub_zero, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)

theorem excPay_le_c (K : Ctx) (root : Digest) (data : PublicData) (wbar : ℝ≥0∞)
    (Fail : Finset (Fin (2 ^ subtreeHeight))) (m : ℝ) (s : State) (P : List Pair) (Ms : List Message)
    (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ) (x : HashInput) :
    excPay K root data wbar Fail (ENNReal.ofReal m) s P Ms L d k x ≤ ENNReal.ofReal (1 - m) := by
  unfold excPay
  split_ifs
  · calc weightA K root s * (min 1 _ - ENNReal.ofReal m) ≤ 1 * (1 - ENNReal.ofReal m) :=
          mul_le_mul' (weightA_le_one K root s) (tsub_le_tsub_right (min_le_left _ _) _)
      _ = 1 - ENNReal.ofReal m := one_mul _
      _ ≤ _ := one_sub_ofReal_le m
  · exact zero_le

theorem natCast_pred_add_one {budget : ℕ} (hb : 1 ≤ budget) :
    (budget : ℝ≥0∞) = ((budget - 1 : ℕ) : ℝ≥0∞) + 1 := by
  rw [← Nat.cast_one (R := ℝ≥0∞), ← Nat.cast_add, Nat.sub_add_cancel hb]

section Crude

variable (K : Ctx) (data : PublicData) (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate) (m : ℝ)

/-- One ordinary query in the crude bound. -/
theorem hash_crude (x : HashInput) (budget : ℕ) (s : State) (P : List Pair) (Ms : List Message)
    (L : QueryLog SigningSpec) (d : Multiset View) (Cont : HashOutput × State → ℝ≥0∞)
    (hcont : ∀ r, Cont r ≤ ((budget - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 - m)) :
    (if 1 ≤ budget then ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        (excPay K data.root data wbar Fail (ENNReal.ofReal m) s P Ms L d budget x + Cont r) else 0) ≤
      budget * ENNReal.ofReal (1 - m) := by
  split_ifs with hb
  · calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] *
          (ENNReal.ofReal (1 - m) + ((budget - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 - m)) :=
          ENNReal.tsum_le_tsum fun r => mul_le_mul_right (add_le_add (excPay_le_c K data.root data wbar Fail m
            s P Ms L d budget x) (hcont r)) _
      _ ≤ ENNReal.ofReal (1 - m) + ((budget - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 - m) := by
          rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one
      _ = _ := by rw [natCast_pred_add_one hb]; ring
  · exact zero_le

theorem xsHash_le_budget {β : Type} (comp : OracleComp HashSpec β) :
    ∀ (L : QueryLog SigningSpec) (d : Multiset View) (budget : ℕ) (s : State) (P : List Pair) (Ms : List Message),
      xsHash K data.root data wbar Fail model (ENNReal.ofReal m) comp L d budget s P Ms ≤
        budget * ENNReal.ofReal (1 - m) := by
  induction comp using OracleComp.inductionOn with
  | pure v => intro L d budget s P Ms; exact zero_le
  | query_bind x rest ih =>
      intro L d budget s P Ms
      exact hash_crude K data wbar Fail model m x budget s P Ms L d
        (fun r => xsHash K data.root data wbar Fail model (ENNReal.ofReal m) (rest r.1) L d (budget - 1) r.2
          (ghostP K data s r.2 x P) (ghostMs K data s x Ms))
        fun r => ih r.1 L d (budget - 1) r.2 _ _

/-- **The crude bound**: at most `(1 - m)⁺` per unit of budget. -/
theorem XS_le_budget (M : OracleComp (OracleWorld + SigningSpec) Forgery) :
    ∀ (L : QueryLog SigningSpec) (budget : ℕ) (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View),
      XS K data.root data wbar Fail model (ENNReal.ofReal m) M L budget s P Ms d ≤
        budget * ENNReal.ofReal (1 - m) := by
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L budget s P Ms d
      exact xsHash_le_budget K data wbar Fail model m _ L d budget s P Ms
  | query_bind input next ih =>
      intro L budget s P Ms d
      rcases input with (draw | x) | msg
      · refine (le_of_eq (XS_draw K data.root data wbar Fail model _ draw next L budget s P Ms d)).trans ?_
        calc _ ≤ ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
              ((budget : ℝ≥0∞) * ENNReal.ofReal (1 - m)) :=
              ENNReal.tsum_le_tsum fun v => mul_le_mul_right (ih v L budget s P Ms d) _
          _ ≤ _ := by rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one
      · refine (le_of_eq (XS_hash K data.root data wbar Fail model _ x next L budget s P Ms d)).trans ?_
        exact hash_crude K data wbar Fail model m x budget s P Ms L d
          (fun r => XS K data.root data wbar Fail model (ENNReal.ofReal m) (next r.1) L (budget - 1) r.2
            (ghostP K data s r.2 x P) (ghostMs K data s x Ms) d)
          fun r => ih r.1 L (budget - 1) r.2 _ _ d
      · refine (le_of_eq (XS_sign K data.root data wbar Fail model _ msg next L budget s P Ms d)).trans ?_
        calc _ ≤ ∑' o1, Pr[= o1 | interp K.tg K.initial model (signCostSource K.p data msg) budget s] *
              ((budget : ℝ≥0∞) * ENNReal.ofReal (1 - m)) := by
              refine ENNReal.tsum_le_tsum fun o1 => mul_le_mul_right ?_ _
              cases o1.1.1 with
              | none => exact zero_le
              | some r =>
                  refine (ih r _ _ _ _ _ _).trans (mul_le_mul_left ?_ _)
                  exact_mod_cast Nat.sub_le _ _
          _ ≤ _ := by rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one

end Crude

/-! ### The ghosts of an ordinary query -/

section Ghosts

variable (K : Ctx) (data : PublicData)

theorem ghostP_other {s s' : State} {x : HashInput}
    (hnew : ¬∃ (p : Pair) (call : DigestCall), x = pblk K.p data p call ∧ s.cache (pblk K.p data p firstCall) = none)
    (P : List Pair) : ghostP K data s s' x P = P := by
  unfold ghostP; rw [dif_neg hnew]

theorem ghostMs_other {s : State} {x : HashInput}
    (hnew : ¬∃ (p : Pair) (call : DigestCall), x = pblk K.p data p call ∧ s.cache (pblk K.p data p firstCall) = none)
    (Ms : List Message) : ghostMs K data s x Ms = Ms := by
  unfold ghostMs; rw [dif_neg hnew]

theorem ghostP_new {s : State} {p : Pair} (c : DigestCall) (hp0 : s.cache (pblk K.p data p firstCall) = none)
    (P : List Pair) (u : DigestCall → HashOutput) :
    ghostP K data s (withPair K.p data s p u) (pblk K.p data p c) P = addPair K.p P p u := by
  have hh : ∃ (p' : Pair) (call : DigestCall), pblk K.p data p c = pblk K.p data p' call ∧
      s.cache (pblk K.p data p' firstCall) = none := ⟨p, c, rfl, hp0⟩
  unfold ghostP
  rw [dif_pos hh]
  have hc : Classical.choose hh = p :=
    ((pblk_injective K.p data (Classical.choose_spec hh).choose_spec.1).1).symm
  rw [hc]
  have hl : LandedIn K.p data (withPair K.p data s p u) p ↔ Landed K.p (blockIndex (u firstCall)) := by
    constructor
    · rintro ⟨u0, h, hl⟩
      rw [withPair_self] at h
      cases h
      exact hl
    · intro hl
      exact ⟨u firstCall, withPair_self s p u firstCall, hl⟩
  unfold addPair
  by_cases hL : Landed K.p (blockIndex (u firstCall))
  · rw [if_pos (hl.2 hL), if_pos hL]
  · rw [if_neg (fun h => hL (hl.1 h)), if_neg hL]

theorem ghostMs_new {s : State} {p : Pair} (c : DigestCall) (hp0 : s.cache (pblk K.p data p firstCall) = none)
    (Ms : List Message) : ghostMs K data s (pblk K.p data p c) Ms = addMsg Ms p.1 := by
  have hh : ∃ (p' : Pair) (call : DigestCall), pblk K.p data p c = pblk K.p data p' call ∧
      s.cache (pblk K.p data p' firstCall) = none := ⟨p, c, rfl, hp0⟩
  unfold ghostMs
  rw [dif_pos hh]
  have hc : Classical.choose hh = p :=
    ((pblk_injective K.p data (Classical.choose_spec hh).choose_spec.1).1).symm
  rw [hc]

end Ghosts

/-! ### The potential of the induction -/

section Main

variable (K : Ctx) (data : PublicData) (wbar : ℝ≥0∞) (tp : TailPar) (Lmax : ℕ)

/-- `psi` plus the landed-pair cap. -/
noncomputable def psiX (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (k : ℕ) : ℝ≥0∞ :=
  psi K.p data wbar tp s P Ms L d k + lam Lmax (livePairs L P).length k

/-- The cap through a new pair. -/
theorem lam_addPair (L : QueryLog SigningSpec) (P : List Pair) (p : Pair) (budget : ℕ) (hb : 1 ≤ budget) :
    pairE (fun u => lam Lmax (livePairs L (addPair K.p P p u)).length (budget - 1)) ≤
      lam Lmax (livePairs L P).length budget := by
  classical
  set ℓ := (livePairs L P).length with hℓ
  by_cases hlive : MsgLive L p.1
  · have hl : ∀ u : DigestCall → HashOutput,
        lam Lmax (livePairs L (addPair K.p P p u)).length (budget - 1) =
        if Landed K.p (blockIndex (u firstCall)) then lam Lmax (ℓ + 1) (budget - 1)
        else lam Lmax ℓ (budget - 1) := by
      intro u
      unfold addPair livePairs
      split_ifs with hl
      · rw [List.filter_cons, if_pos (by simpa using hlive), List.length_cons]
        rfl
      · rfl
    simp only [hl]
    have := lam_newPair K.p Lmax ℓ (budget - 1)
    rw [Nat.sub_add_cancel hb] at this
    exact le_of_eq this
  · have hl : ∀ u : DigestCall → HashOutput,
        lam Lmax (livePairs L (addPair K.p P p u)).length (budget - 1) = lam Lmax ℓ (budget - 1) := by
      intro u
      unfold addPair livePairs
      split_ifs with hl
      · rw [List.filter_cons, if_neg (by simpa using hlive)]
        rfl
      · rfl
    simp only [hl, pairE_const]
    exact lam_mono le_rfl (Nat.sub_le _ _)

variable (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ)
  {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- **One ordinary query** (adversary or verifier), for a continuation bounded by the potential of
the next state and by the crude bound. -/
theorem xs_step (hcalls : digestCalls = 1) (hparse : ∀ p call, model.parse (pblk K.p data p call) = none)
    (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0)
    {Cmax : ℕ} (hfair : FairS wbar Cmax Lmax) (hQ : Qtot ≤ Cmax) (hθ : ∀ D, 0 ≤ tp.θ D)
    (x : HashInput) {budget : ℕ} {s : State} {P : List Pair} {Ms : List Message} {L : QueryLog SigningSpec}
    {d : Multiset View} {R : List Coordinate} (hI : InvX K data Qtot budget s P Ms L d R)
    (hexc : 1 ≤ budget → excPay K data.root data wbar Fail (ENNReal.ofReal tp.m) s P Ms L d budget x ≤
      ENNReal.ofReal (1 - tp.m) * psi K.p data wbar tp s P Ms L d budget)
    (Cont : HashOutput → State → List Pair → List Message → ℝ≥0∞)
    (hcont : ∀ v s' P' Ms', InvX K data Qtot (budget - 1) s' P' Ms' L d R →
      Cont v s' P' Ms' ≤ ((budget - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 - tp.m) *
        psiX K data wbar tp Lmax s' P' Ms' L d (budget - 1))
    (hcrude : ∀ v s' P' Ms', Cont v s' P' Ms' ≤ ((budget - 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 - tp.m)) :
    (if 1 ≤ budget then ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        (excPay K data.root data wbar Fail (ENNReal.ofReal tp.m) s P Ms L d budget x +
          Cont r.1 r.2 (ghostP K data s r.2 x P) (ghostMs K data s x Ms)) else 0) ≤
      budget * ENNReal.ofReal (1 - tp.m) * psiX K data wbar tp Lmax s P Ms L d budget := by
  split_ifs with hb
  swap
  · exact zero_le
  set c := ENNReal.ofReal (1 - tp.m) with hc
  set ℓ := (livePairs L P).length with hℓ
  set E := excPay K data.root data wbar Fail (ENNReal.ofReal tp.m) s P Ms L d budget x with hE
  have hEle : E ≤ c * psiX K data wbar tp Lmax s P Ms L d budget :=
    (hexc hb).trans (mul_le_mul_right le_self_add _)
  have hsplit : ∀ (F : HashOutput × State → ℝ≥0∞),
      ∑' r, Pr[= r | ordinaryStep model x s.known s] * (E + F r) ≤
        E + ∑' r, Pr[= r | ordinaryStep model x s.known s] * F r := by
    intro F
    simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    exact add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl
  have hfinish : ∀ Y : ℝ≥0∞, Y ≤ ((budget - 1 : ℕ) : ℝ≥0∞) * c * psiX K data wbar tp Lmax s P Ms L d budget →
      E + Y ≤ budget * c * psiX K data wbar tp Lmax s P Ms L d budget := by
    intro Y hY
    calc E + Y ≤ c * psiX K data wbar tp Lmax s P Ms L d budget +
          ((budget - 1 : ℕ) : ℝ≥0∞) * c * psiX K data wbar tp Lmax s P Ms L d budget := add_le_add hEle hY
      _ = _ := by rw [natCast_pred_add_one hb]; ring
  by_cases hcap : 1 ≤ lam Lmax ℓ budget
  · -- the cap pays everything
    refine (hsplit _).trans (hfinish _ ?_)
    calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] * (((budget - 1 : ℕ) : ℝ≥0∞) * c) :=
          ENNReal.tsum_le_tsum fun r => mul_le_mul_right (hcrude _ _ _ _) _
      _ ≤ ((budget - 1 : ℕ) : ℝ≥0∞) * c := by
          rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one
      _ ≤ _ := by
          refine le_mul_of_one_le_right' (le_trans hcap ?_)
          unfold psiX
          exact le_add_self
  have hlen : ℓ ≤ Lmax := by
    by_contra hlt
    exact hcap (one_le_lam (by omega) budget)
  obtain ⟨⟨hprep, hP, hM, hD, hC, hJ, hL⟩, hK⟩ := hI
  by_cases hnew : ∃ (p : Pair) (call : DigestCall), x = pblk K.p data p call ∧
      s.cache (pblk K.p data p firstCall) = none
  · -- a new pair
    obtain ⟨p, c', rfl, hp0⟩ := hnew
    have hfresh : ∀ call, s.cache (pblk K.p data p call) = none := hP.first p hp0
    have hrate : MsgLive L p.1 → Rate K.p data wbar s p.1 := fun hlive =>
      rate_of_fair hfair s p.1 (by have := hC p.1; omega) (le_trans (landedCount_le hP L hlive) hlen)
    refine (hsplit _).trans (hfinish _ ?_)
    rw [ordinaryStep, hparse p c']
    simp only
    rw [readOutside_fresh _ s (hfresh c'), tsum_probOutput_map_mul]
    have hpairE : ∀ F : (DigestCall → HashOutput) → ℝ≥0∞,
        pairE F = ((Fintype.card HashOutput : ℝ≥0∞) ^ digestCalls)⁻¹ * ∑ u, F u := by
      intro F
      unfold pairE
      rw [tsum_uniform_eq, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    have hpre : ∑' v, Pr[= v | ($ᵗ HashOutput : ProbComp HashOutput)] *
          Cont v (s.store (pblk K.p data p c') v)
            (ghostP K data s (s.store (pblk K.p data p c') v) (pblk K.p data p c') P)
            (ghostMs K data s (pblk K.p data p c') Ms) =
        pairE (fun u => Cont (u c') (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1)) := by
      rw [hpairE]
      refine (presample_one hcalls (pblk K.p data p) c' s (fun v s' =>
        Cont v s' (ghostP K data s s' (pblk K.p data p c') P) (ghostMs K data s (pblk K.p data p c') Ms))).trans ?_
      refine congrArg (fun t => ((Fintype.card HashOutput : ℝ≥0∞) ^ digestCalls)⁻¹ * t) ?_
      refine Finset.sum_congr rfl fun u _ => ?_
      change Cont (u c') (withPair K.p data s p u) (ghostP K data s (withPair K.p data s p u) (pblk K.p data p c') P)
        (ghostMs K data s (pblk K.p data p c') Ms) = _
      rw [ghostP_new K data c' hp0 P u, ghostMs_new K data c' hp0 Ms]
    refine (le_of_eq hpre).trans ?_
    have hI' : ∀ u, InvX K data Qtot (budget - 1) (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1) L d R :=
      fun u => invX_withPair model hout ⟨⟨hprep, hP, hM, hD, hC, hJ, hL⟩, hK⟩ hb p hp0 u
    calc pairE (fun u => Cont (u c') (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1))
        ≤ pairE (fun u => ((budget - 1 : ℕ) : ℝ≥0∞) * c *
            psiX K data wbar tp Lmax (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1) L d (budget - 1)) :=
          pairE_mono fun u => hcont _ _ _ _ (hI' u)
      _ = ((budget - 1 : ℕ) : ℝ≥0∞) * c * pairE (fun u =>
            psiX K data wbar tp Lmax (withPair K.p data s p u) (addPair K.p P p u) (addMsg Ms p.1) L d (budget - 1)) :=
          pairE_const_mul _ _
      _ ≤ _ := by
          refine mul_le_mul_right ?_ _
          unfold psiX
          rw [pairE_add]
          refine add_le_add ?_ (lam_addPair K Lmax L P p budget hb)
          have h := psi_newPair K.p data wbar tp hfair.le_one hθ hP hM p hp0 L hrate d (budget - 1)
          rwa [Nat.sub_add_cancel hb] at h
  · -- any other query
    refine (hsplit _).trans (hfinish _ ?_)
    simp only [ghostP_other K data hnew, ghostMs_other K data hnew]
    calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] *
          (((budget - 1 : ℕ) : ℝ≥0∞) * c * psiX K data wbar tp Lmax s P Ms L d budget) := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support (ordinaryStep model x s.known s)
          · refine mul_le_mul_right ((hcont _ _ _ _ (invX_ordinary model hout ⟨⟨hprep, hP, hM, hD, hC, hJ, hL⟩, hK⟩
              hb x hnew r hr)).trans (mul_le_mul_right ?_ _)) _
            have hext := ordinaryStep_extends model x s r hr
            have hblocks := same_blocks (parameter := K.p) (data := data) hext
              (ordinaryStep_cache_ne model x s r hr) hnew
            unfold psiX
            exact add_le_add (psi_grow hfair.le_one hθ hblocks (fun q hq call => landed_blocks hext hP hq call)
              (fun q hq => (hP.mem q).1 hq) Ms L d (Nat.sub_le _ _)) (lam_mono le_rfl (Nat.sub_le _ _))
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ ≤ _ := by rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one

/-- **A program whose excess account is paid** by `budget (1 - m)⁺ (psi + lam)`. -/
def GoodX (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (d : Multiset View) (R : List Coordinate),
    InvX K data Qtot budget s P Ms L d R →
      XS K data.root data wbar Fail model (ENNReal.ofReal tp.m) M L budget s P Ms d ≤
        budget * ENNReal.ofReal (1 - tp.m) * psiX K data wbar tp Lmax s P Ms L d budget

variable (hcalls : digestCalls = 1) (hH : totalHeight = subtreeHeight)
  (hparse : ∀ p call, model.parse (pblk K.p data p call) = none)
  (hkind : ∀ p call, K.tg.kind (pblk K.p data p call) = .none)
  (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0)
  {Cmax : ℕ} (hfair : FairS wbar Cmax Lmax) (hQ : Qtot ≤ Cmax) (hθ : ∀ D, 0 ≤ tp.θ D)
  (hexc : ∀ budget (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (R : List Coordinate) (x : HashInput), InvX K data Qtot budget s P Ms L d R → 1 ≤ budget →
      excPay K data.root data wbar Fail (ENNReal.ofReal tp.m) s P Ms L d budget x ≤
        ENNReal.ofReal (1 - tp.m) * psi K.p data wbar tp s P Ms L d budget)

include hcalls hparse hout hfair hQ hθ hexc in
/-- The verification of the forgery: a sequence of ordinary queries. -/
theorem xsHash_good {β : Type} (comp : OracleComp HashSpec β) :
    ∀ (L : QueryLog SigningSpec) (d : Multiset View) (budget : ℕ) (s : State) (P : List Pair) (Ms : List Message)
      (R : List Coordinate), InvX K data Qtot budget s P Ms L d R →
      xsHash K data.root data wbar Fail model (ENNReal.ofReal tp.m) comp L d budget s P Ms ≤
        budget * ENNReal.ofReal (1 - tp.m) * psiX K data wbar tp Lmax s P Ms L d budget := by
  induction comp using OracleComp.inductionOn with
  | pure v => intro L d budget s P Ms R _; exact zero_le
  | query_bind x rest ih =>
      intro L d budget s P Ms R hI
      exact xs_step K data wbar tp Lmax Fail Qtot model hcalls hparse hout hfair hQ hθ x hI
        (hexc budget s P Ms L d R x hI) (fun v s' P' Ms' => xsHash K data.root data wbar Fail model
          (ENNReal.ofReal tp.m) (rest v) L d (budget - 1) s' P' Ms')
        (fun v s' P' Ms' hI' => ih v L d (budget - 1) s' P' Ms' R hI')
        (fun v s' P' Ms' => xsHash_le_budget K data wbar Fail model tp.m (rest v) L d (budget - 1) s' P' Ms')

include hcalls hparse hout hfair hQ hθ hexc in
theorem goodX_pure (L : QueryLog SigningSpec) (forgery : Forgery) :
    GoodX K data wbar tp Lmax Fail Qtot model (pure forgery) L := by
  intro budget s P Ms d R hI
  exact xsHash_good K data wbar tp Lmax Fail Qtot model hcalls hparse hout hfair hQ hθ hexc _ L d budget s P Ms R hI

include hcalls hparse hout hfair hQ hθ hexc in
theorem goodX_hash (L : QueryLog SigningSpec) (x : HashInput)
    (next : HashOutput → OracleComp (OracleWorld + SigningSpec) Forgery)
    (h : ∀ v, GoodX K data wbar tp Lmax Fail Qtot model (next v) L) :
    GoodX K data wbar tp Lmax Fail Qtot model (liftM ((OracleWorld + SigningSpec).query (.inl (.inr x))) >>= next) L := by
  intro budget s P Ms d R hI
  rw [XS_hash]
  exact xs_step K data wbar tp Lmax Fail Qtot model hcalls hparse hout hfair hQ hθ x hI
    (hexc budget s P Ms L d R x hI) (fun v s' P' Ms' => XS K data.root data wbar Fail model
      (ENNReal.ofReal tp.m) (next v) L (budget - 1) s' P' Ms' d)
    (fun v s' P' Ms' hI' => h v (budget - 1) s' P' Ms' d R hI')
    (fun v s' P' Ms' => XS_le_budget K data wbar Fail model tp.m (next v) L (budget - 1) s' P' Ms' d)

theorem goodX_draw (L : QueryLog SigningSpec) (draw : ℕ)
    (next : Fin (draw + 1) → OracleComp (OracleWorld + SigningSpec) Forgery)
    (h : ∀ v, GoodX K data wbar tp Lmax Fail Qtot model (next v) L) :
    GoodX K data wbar tp Lmax Fail Qtot model (liftM ((OracleWorld + SigningSpec).query (.inl (.inl draw))) >>= next) L := by
  intro budget s P Ms d R hI
  rw [XS_draw]
  calc _ ≤ ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
        (budget * ENNReal.ofReal (1 - tp.m) * psiX K data wbar tp Lmax s P Ms L d budget) :=
        ENNReal.tsum_le_tsum fun v => mul_le_mul_right (h v budget s P Ms d R hI) _
    _ ≤ _ := by rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one

include hH hparse hkind hout hθ hfair in
/-- **One signing call** on a fresh message while fewer than `N` signatures were asked. -/
theorem goodX_sign
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared K.initial s1 →
      ∀ out ∈ support (interp K.tg K.initial model (finishRest K.p data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ (∅ : Finset (Fin (2 ^ subtreeHeight))))
    (L : QueryLog SigningSpec) (msg : Message)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) Forgery) (hm : MsgLive L msg)
    (hlt : L.length < signatureLimit)
    (h : ∀ r, GoodX K data wbar tp Lmax Fail Qtot model (next r) (L ++ [⟨msg, r⟩])) :
    GoodX K data wbar tp Lmax Fail Qtot model (liftM ((OracleWorld + SigningSpec).query (.inr msg)) >>= next) L := by
  classical
  intro budget s P Ms d R hI
  rw [XS_sign]
  set c := ENNReal.ofReal (1 - tp.m) with hc
  set sign := signCostSource K.p data msg with hsign
  set post : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    o1.1.1.elim 0 (fun r => psi K.p data wbar tp o1.2 (newPairs K.p data msg s o1.2 ++ P) (addMsg Ms msg)
      (L ++ [⟨msg, r⟩]) (discAfter K.p data msg s d o1) (budget - traceCost o1.1.2.2.1)) with hpost
  set ℓ := (livePairs L P).length with hℓ
  have hpoint : ∀ o1 ∈ support (interp K.tg K.initial model sign budget s),
      o1.1.1.elim 0 (fun r => XS K data.root data wbar Fail model (ENNReal.ofReal tp.m) (next r) (L ++ [⟨msg, r⟩])
        (budget - traceCost o1.1.2.2.1) o1.2 (newPairs K.p data msg s o1.2 ++ P) (addMsg Ms msg)
        (discAfter K.p data msg s d o1)) ≤
        budget * c * (post o1 + lam Lmax ℓ budget) := by
    intro o1 ho1
    cases hres : o1.1.1 with
    | none => simp only [Option.elim]; exact zero_le
    | some r =>
        have hpr : post o1 = psi K.p data wbar tp o1.2 (newPairs K.p data msg s o1.2 ++ P) (addMsg Ms msg)
            (L ++ [⟨msg, r⟩]) (discAfter K.p data msg s d o1) (budget - traceCost o1.1.2.2.1) := by
          simp only [hpost, hres, Option.elim]
        simp only [Option.elim]
        rw [hpr]
        have hI' := invX_sign model hout hH hparse msg (hfail msg) hI hlt o1 ho1 r hres
        refine (h r _ _ _ _ _ _ hI').trans ?_
        have hlam : lam Lmax (livePairs (L ++ [⟨msg, r⟩]) (newPairs K.p data msg s o1.2 ++ P)).length
            (budget - traceCost o1.1.2.2.1) ≤ lam Lmax ℓ budget := by
          refine lam_mono ?_ (Nat.sub_le _ _)
          unfold livePairs
          rw [List.filter_append]
          have hnew : (newPairs K.p data msg s o1.2).filter
              (fun q => decide (MsgLive (L ++ [⟨msg, r⟩]) q.1)) = [] := by
            refine List.filter_eq_nil_iff.2 fun q hq => ?_
            obtain ⟨hqm, _, _⟩ := (mem_newPairs K.p data msg s).1 hq
            simp only [decide_eq_true_eq, msgLive_append, not_and, not_not]
            exact fun _ => hqm
          rw [hnew, List.nil_append]
          refine (List.Sublist.length_le ?_)
          refine List.monotone_filter_right _ fun q hq => ?_
          simp only [decide_eq_true_eq, msgLive_append] at hq ⊢
          exact hq.1
        unfold psiX
        exact mul_le_mul' (mul_le_mul' (by exact_mod_cast Nat.sub_le _ _) le_rfl) (add_le_add le_rfl hlam)
  have hE := psi_sign K.tg K.initial model K.p data wbar tp Qtot msg hparse hkind (hfail msg) hfair.le_one hθ budget s
    P Ms L d R hI.inv.prep hI.inv.pinv hI.inv.minv hI.inv.dinv hI.inv.count hm hlt
  calc _ ≤ ∑' o1, Pr[= o1 | interp K.tg K.initial model sign budget s] *
        (budget * c * (post o1 + lam Lmax ℓ budget)) := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support (interp K.tg K.initial model sign budget s)
        · exact mul_le_mul_right (hpoint o1 ho1) _
        · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
    _ = budget * c * (∑' o1, Pr[= o1 | interp K.tg K.initial model sign budget s] * post o1 +
          (∑' o1, Pr[= o1 | interp K.tg K.initial model sign budget s]) * lam Lmax ℓ budget) := by
        rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
        exact tsum_congr fun o1 => by ring
    _ ≤ _ := by
        unfold psiX
        refine mul_le_mul_right (add_le_add hE (mul_le_of_le_one_left' tsum_probOutput_le_one)) _

include hcalls hH hparse hkind hout hfair hQ hθ hexc in
/-- **The excess account through any adversary program** that never repeats a message and asks at
most `N` signatures. -/
theorem goodX_advProg
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared K.initial s1 →
      ∀ out ∈ support (interp K.tg K.initial model (finishRest K.p data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ (∅ : Finset (Fin (2 ^ subtreeHeight)))) :
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec),
      NoRepeat M (L.map Sigma.fst) → SignBound M (signatureLimit - L.length) →
        GoodX K data wbar tp Lmax Fail Qtot model M L := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L _ _
      exact goodX_pure K data wbar tp Lmax Fail Qtot model hcalls hparse hout hfair hQ hθ hexc L forgery
  | query_bind input next ih =>
      intro L hnr hsb
      rcases input with (draw | bytes) | message
      · exact goodX_draw K data wbar tp Lmax Fail Qtot model L draw _ fun v => ih v L (hnr v) (hsb v)
      · exact goodX_hash K data wbar tp Lmax Fail Qtot model hcalls hparse hout hfair hQ hθ hexc L bytes _
          fun v => ih v L (hnr v) (hsb v)
      · obtain ⟨hnot, hrest⟩ := (noRepeat_sign message next _).1 hnr
        obtain ⟨hpos, hsrest⟩ := (signBound_sign message next _).1 hsb
        have hm : MsgLive L message := by
          intro entry he heq
          exact hnot (heq ▸ List.mem_map_of_mem he)
        refine goodX_sign K data wbar tp Lmax Fail Qtot model hH hparse hkind hout hfair hθ hfail L message next hm
          (by omega) fun r => ih r _ ?_ ?_
        · rw [List.map_append]
          exact hrest r
        · have hlen : signatureLimit - (L ++ [(⟨message, r⟩ : (_ : Message) × Option Signature)]).length =
              signatureLimit - L.length - 1 := by
            simp only [List.length_append, List.length_singleton]
            omega
          rw [hlen]
          exact hsrest r

end Main

/-! ### The bound -/

/-- **The start value of the induction's potential** with the cap at most `2^-101`. -/
theorem psiX_start_le (K : Ctx) (data : PublicData) (wbar : ℝ≥0∞) (hw1 : wbar ≤ 1) (tp : TailPar) (Lmax : ℕ)
    (s : State) (hlam0 : lam Lmax 0 tp.q ≤ (2 : ℝ≥0∞)⁻¹ ^ 101)
    (hrate : (signatureLimit : ℝ) / 2 ^ subtreeHeight + (tp.q : ℝ) * (landing * wbar).toReal / 2 ^ subtreeHeight
      ≤ tp.μ) :
    psiX K data wbar tp Lmax s [] [] [] 0 tp.q ≤ tailSum subtreeHeight forsTrees forsHeight tp.n0 tp.μ tp.θ tp.m tp.q := by
  unfold psiX psi tailSum
  have hlen : (livePairs ([] : QueryLog SigningSpec) ([] : List Pair)).length = 0 := rfl
  rw [hlen, add_assoc]
  refine add_le_add (add_le_add (psiL_start_le K.p data wbar hw1 tp s hrate)
    (psiC_start_le K.p data wbar hw1 tp s hrate)) ?_
  calc psiP K.p data tp s [] [] tp.q + lam Lmax 0 tp.q ≤ (2 : ℝ≥0∞)⁻¹ ^ 101 + (2 : ℝ≥0∞)⁻¹ ^ 101 :=
        add_le_add (psiP_start_le' K.p data tp s) hlam0
    _ = (2 : ℝ≥0∞)⁻¹ ^ 100 := by
        rw [← two_mul, show (101 : ℕ) = 1 + 100 from rfl, pow_add, pow_one, ← mul_assoc,
          ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ ENNReal.ofReal (1 / 2 ^ 99) := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat, ← ENNReal.inv_pow]
        exact ENNReal.inv_le_inv.2 (pow_le_pow_right₀ one_le_two (by norm_num))

/-- **`xs_bound`** (the WP-F contract of `notes/CORE-P.md`): the excess account of an adversary that
never repeats a message and asks at most `N` signatures is at most `x Pb`, `x = q' / 2^128`, under the
tail predicate `ForecastTail m q' Pb`. The hypothesis `hexc` is WP-F-A's `excPay_le_psi`. -/
theorem xs_bound (K : Ctx) (data : PublicData) {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)
    (wbar : ℝ≥0∞) (m Pb : ℝ) (q' : ℕ) (hFT : ForecastTail m q' Pb) (hwbar : wbar = wbarOf q')
    (hH : totalHeight = subtreeHeight) (hcalls : digestCalls = 1)
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none)
    (hkind : ∀ p call, K.tg.kind (pblk K.p data p call) = .none)
    (hclean : ∀ p call, K.initial (pblk K.p data p call) = none)
    (hfail : ∀ msg ρ digest budget (s1 : State), Prepared K.initial s1 →
      ∀ out ∈ support (interp K.tg K.initial model (finishRest K.p data msg ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ (∅ : Finset (Fin (2 ^ subtreeHeight))))
    (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0)
    {Cmax Lmax : ℕ} (hfair : FairS wbar Cmax Lmax) (hQ : q' ≤ Cmax) (hlam0 : lam Lmax 0 q' ≤ (2 : ℝ≥0∞)⁻¹ ^ 101)
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M []) (hsb : SignBound M signatureLimit)
    (known : HiddenReveal.Knowledge Coordinate) (hknown : ∀ i κ l, known (Coordinate.fors i κ l 0) = none)
    (hexc : ∀ (tp : TailPar) (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
      (d : Multiset View) (k : ℕ) (x : HashInput),
      totalHeight = subtreeHeight → wbar ≤ 1 → PInv K.p data s P → MInv K.p data s Ms →
      L.length ≤ signatureLimit → k ≤ tp.q → (∀ D, 0 ≤ tp.θ D) → 1 ≤ tp.n0 →
      (signatureLimit : ℝ) / 2 ^ subtreeHeight + (tp.q : ℝ) * (landing * wbar).toReal / 2 ^ subtreeHeight ≤ tp.μ →
      CoinCond subtreeHeight forsTrees forsHeight capFloor tp.q (tp.μ : ℝ) tp.n0 →
      KnownInvB s d →
      excPay K data.root data wbar ∅ (ENNReal.ofReal tp.m) s P Ms L d k x ≤
        ENNReal.ofReal (1 - tp.m) * psi K.p data wbar tp s P Ms L d k) :
    ν * XS K data.root data wbar ∅ model (ENNReal.ofReal m) M [] q' (DebtState.start K.initial known) [] [] 0 ≤
      ENNReal.ofReal ((q' : ℝ) / 2 ^ 128 * Pb) := by
  obtain ⟨n0, μ, θ, hn0, hrate, hθ, hcoin, htail⟩ := hFT
  set tp : TailPar := ⟨n0, μ, θ, m, q'⟩ with htp
  subst hwbar
  set start := DebtState.start K.initial known with hstart
  have hI : InvX K data q' q' start [] [] [] 0 [] :=
    ⟨⟨start_prepared K.initial known, start_pinv K.p data K.initial hclean known,
      start_minv K.p data K.initial hclean known, (fun _ _ _ _ h => by cases h),
      start_count K.p data K.initial hclean known q', jInv_start K.p data K.initial known hknown, by simp⟩,
      fun v hv => by simp at hv⟩
  have hexc' : ∀ budget (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
      (R : List Coordinate) (x : HashInput), InvX K data q' budget s P Ms L d R → 1 ≤ budget →
        excPay K data.root data (wbarOf q') ∅ (ENNReal.ofReal tp.m) s P Ms L d budget x ≤
          ENNReal.ofReal (1 - tp.m) * psi K.p data (wbarOf q') tp s P Ms L d budget :=
    fun budget s P Ms L d R x hI' _ => hexc tp s P Ms L d budget x hH hfair.le_one hI'.inv.pinv hI'.inv.minv
      hI'.inv.len (budget_le_of_count hI'.inv.count) hθ hn0 hrate hcoin hI'.known
  have hgood := goodX_advProg K data (wbarOf q') tp Lmax ∅ q' model hcalls hH hparse hkind hout hfair hQ hθ hexc'
    hfail M [] hnr (by simpa using hsb) q' start [] [] 0 [] hI
  have hpot := psiX_start_le K data (wbarOf q') hfair.le_one tp Lmax start hlam0 hrate
  have hx : ν * (q' : ℝ≥0∞) = ENNReal.ofReal ((q' : ℝ) / 2 ^ 128) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat, ENNReal.div_eq_inv_mul]
    rfl
  calc ν * XS K data.root data (wbarOf q') ∅ model (ENNReal.ofReal m) M [] q' start [] [] 0
      ≤ ν * ((q' : ℝ≥0∞) * ENNReal.ofReal (1 - m) *
          tailSum subtreeHeight forsTrees forsHeight n0 μ θ m q') :=
        mul_le_mul_right (hgood.trans (mul_le_mul_right hpot _)) _
    _ = ν * (q' : ℝ≥0∞) * (ENNReal.ofReal (1 - m) * tailSum subtreeHeight forsTrees forsHeight n0 μ θ m q') := by
        ring
    _ ≤ ENNReal.ofReal ((q' : ℝ) / 2 ^ 128) * ENNReal.ofReal Pb := by
        rw [hx]; exact mul_le_mul_right htail _
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

end FORS.Security.SWRoute
