import FORS.SWRoute.ContactGood
import FORS.SWRoute.StepsStore

/-! **The contact potential A4': the hash-query steps.** The step obligations `hhash` (one ordinary
query of the adversary) and `hpure` (the verifier's hash queries) of `goodK_advProg`, from one
ordinary-query step lemma with an abstract continuation (`goodKC_ordinary`):

* a FORS leaf query makes a new contact with chance `ν`; if it would survive, its coefficient is
  paid by `cU` (the reveal rate of the remaining signatures and the share `m` of the near forecast),
  the excess account (the rest of the near forecast) and the coin forecast (the cell count below the
  cap `T` and the creation rate of the remaining budget); a contact that would not survive kills;
* a new pair raises the cell counts by `revRate` in the mean, the own-cell forecasts by nothing (one
  coin at baseline zero), the coin and landed-pair caps by nothing in the mean; a new pair that makes a
  near cell at a contact (a kill, booked in `WK`) makes the contact's own-cell forecast at least one
  (`release_ownW`), so the capped forecast pays the kill;
* any other query neither kills nor raises the potential.

Shared helpers: `release_ownW`, `step_kill_le` (a step pays its kill and the weight after it from the
weight before it) and `wk_le_weightA` (the kill account is at most the weight). -/

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

/-! ### The release of the own-cell forecast -/

section ReleaseOwn

variable (K : Ctx) (data : PublicData) (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- **A near cell at a FORS leaf query whose secret is unknown makes its own-cell forecast at least
one**: the near pair is cached, landed and unsigned (a signed pair has every secret known), and its
realized own-cell witness is one (its other secrets are known, hence disclosed). -/
theorem release_ownW (hw : wbar ≤ 1) {s : State} {P : List Pair} {Ms : List Message} {L : QueryLog SigningSpec}
    {d : Multiset View} {R : List Coordinate} (k : ℕ) (f : FIn)
    (hP : PInv K.p data s P) (hD : DInv R d) (hJ : JInv K.p data s L R) (hL : L.length ≤ signatureLimit)
    (hnl : NearLeaf K data.root s f.index f.κ f.leaf) (hmiss : s.known f.inC = none) :
    1 ≤ PiC K data wbar Fail (CellOf f) s P Ms L d k := by
  obtain ⟨message, randomness, digest, hcd, hland, hidx, hleaf, hother⟩ := hnl
  set q : Pair := (message, randomness) with hq
  have hpb : HiddenBridge.cachedDigest s.cache K.p data.root message randomness =
      (pcache K.p data q.1 s q.2).map truncateMessageDigest := rfl
  rw [hpb] at hcd
  cases h0 : pcache K.p data q.1 s q.2 with
  | none =>
      rw [h0] at hcd
      cases hcd
  | some u =>
      rw [h0] at hcd
      have hdig : truncateMessageDigest u = digest := by simpa using hcd
      subst hdig
      have hlanded : LandedIn K.p data s q :=
        ⟨u firstCall, cached_of_pcache K.p data (p := q) h0 firstCall,
          by rwa [Concrete.digestIndex_truncate] at hland⟩
      have hqP := (hP.mem q).2 hlanded
      have hv : pview K.p data s q = Lifetime.localDigestView (truncateMessageDigest u) :=
        pview_of_pcache (q := q) h0
      have hun : Unsigned L q := by
        intro entry he sig hsig ⟨h1, h2⟩
        obtain ⟨u', hpc', hall⟩ := hJ.2 entry he sig hsig
        rw [h1, h2] at hpc'
        have huu : u' = u := Option.some_inj.1 (hpc'.symm.trans h0)
        subst huu
        apply hall f.κ
        rw [hidx, hleaf]
        exact hmiss
      have hown : 1 ≤ ownW (CellOf f) (pview K.p data s q) d := by
        rw [hv]
        have hsub : NearSub (Lifetime.localDigestView (truncateMessageDigest u)) f.κ d := by
          intro κ' hκ'
          have hk := hother κ' hκ'
          rw [← hidx] at hk
          obtain ⟨v, hvd, hv1, hv2⟩ := hD _ _ _ _ (hJ.1 _ _ _ hk)
          exact ⟨v, hvd, by rw [localDigestView_fst]; exact hv1, by rw [localDigestView_snd]; exact hv2⟩
        unfold ownW
        rw [if_pos ⟨by rw [localDigestView_fst, hidx], by rw [localDigestView_snd, hleaf], hsub⟩]
      unfold PiC potG
      rw [if_neg (by simp only [false_or, not_lt]; exact hL)]
      unfold coreG
      refine le_trans ?_ (le_trans (List.le_sum_of_mem (List.mem_map_of_mem hqP)) (le_self_add.trans le_self_add))
      unfold candG
      rw [if_pos hun]
      split_ifs
      · exact le_rfl
      · exact hown.trans (base_le_candValueG wbar (ownW_props _) hw s Ms L d _ _ q)

end ReleaseOwn

/-! ### A step pays its kill from the weight -/

section Kill

variable (K : Ctx) (root : Digest)

theorem weightB_le_of_extends {s s' : State} (h : Extends s s') (hknown : s'.known = s.known) :
    weightB K s' ≤ weightB K s := by
  by_cases hb : BadW K s
  · rw [weightB_eq, if_pos (badW_mono h hb)]
    exact bot_le
  · rw [weightB_eq K s, if_neg hb]
    exact (weightB_le_weight K s').trans (weight_le_of_extendsW K.tg K.initial h hknown)

/-- Pointwise: without a completed contact before, the kill payment and the weight after are at most
the weight before once `weightB` does not grow. -/
theorem payK_add_le {s s' : State} (input : CostSpec.Domain) (hn : ¬NearContact K root s)
    (hle : weightB K s' ≤ weightB K s) :
    payK K root s input s' + weightA K root s' ≤ weightA K root s := by
  unfold payK
  by_cases hk : NearContact K root s'
  · rw [weightA_eq_weightB K root s', if_pos hk, add_zero]
    split_ifs
    · exact le_rfl
    · exact bot_le
  · rw [if_neg (fun h => hk h.2.1), zero_add, weightA_eq_weightB K root s', if_neg hk,
      weightA_eq_weightB K root s, if_neg hn]
    exact hle

/-- A completed contact moves back to a state with the same contacts, the same cached pairs and no
fewer known FORS secrets. -/
theorem nearContact_transfer {s s' : State} (hf : ∀ f, FCk K s' f → FCk K s f)
    (hc : ∀ m ρ, HiddenBridge.cachedDigest s'.cache K.p root m ρ = HiddenBridge.cachedDigest s.cache K.p root m ρ)
    (hk : ∀ i κ l, s'.known (Coordinate.fors i κ l 0) ≠ none → s.known (Coordinate.fors i κ l 0) ≠ none)
    (h : NearContact K root s') : NearContact K root s := by
  obtain ⟨f, hfc, hkn | ⟨mm, ρ, dg, hcd, hl, hi, hlf, hoth⟩⟩ := h
  · exact ⟨f, hf f hfc, Or.inl (hk f.index f.κ f.leaf hkn)⟩
  · refine ⟨f, hf f hfc, Or.inr ⟨mm, ρ, dg, by rw [← hc]; exact hcd, hl, hi, hlf, fun κ' hκ' => ?_⟩⟩
    exact hk _ _ _ (hoth κ' hκ')

variable {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- An ordinary query either keeps the known coordinates and grows the state, or exposes the output
coordinate of a row (the canonical branch). -/
theorem ordinaryStep_known_or_expose (x : HashInput) (s : State) :
    (∀ r ∈ support (ordinaryStep model x s.known s), r.2.known = s.known ∧ Extends s r.2) ∨
      ∃ a, ∀ r ∈ support (ordinaryStep model x s.known s), ∃ val, r.2 = s.expose (model.outgoing a) val := by
  have hread : ∀ s1 : State, s1.known = s.known → (∀ r ∈ support (readOutside x s1), r.2.known = s.known) := by
    intro s1 hs1 r hr
    rw [readOutside_known x s1 r hr, hs1]
  cases hp : model.parse x with
  | none =>
      left
      intro r hr
      have hr' := hr
      simp only [ordinaryStep, hp] at hr'
      exact ⟨hread s rfl r hr', ordinaryStep_extends model x s r hr⟩
  | some q =>
      cases hk : s.known (model.incoming q.1) with
      | none =>
          left
          intro r hr
          have hr' := hr
          simp only [ordinaryStep, hp, hk] at hr'
          exact ⟨hread (s.record (model.incoming q.1, q.2)) rfl r hr', ordinaryStep_extends model x s r hr⟩
      | some canonical =>
          by_cases heq : q.2 = canonical
          · right
            refine ⟨q.1, fun r hr => ?_⟩
            simp only [ordinaryStep, hp, hk, if_pos heq, support_map] at hr
            obtain ⟨res, hres, rfl⟩ := hr
            exact ⟨res.1, sampleCoordinate_expose _ s res hres⟩
          · left
            intro r hr
            have hr' := hr
            simp only [ordinaryStep, hp, hk, if_neg heq] at hr'
            exact ⟨hread s rfl r hr', ordinaryStep_extends model x s r hr⟩

variable (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0)
include hout

/-- **One step pays its kill and the weight after it from the weight before it.** A kill (a contact
becoming completed at a step other than a FORS leaf query) loses the weight it pays; an exposure keeps
`weightB` in the mean and decides a kill independently of the value. -/
theorem step_kill_le (input : CostSpec.Domain) (s : State) :
    ∑' r, Pr[= r | costStep model input s] * (payK K root s input r.2 + weightA K root r.2) ≤ weightA K root s := by
  by_cases hn : NearContact K root s
  · have hp : ∀ r : CostSpec.Range input × State, payK K root s input r.2 = 0 := fun r => by
      unfold payK
      rw [if_neg (fun h => h.2.2 hn)]
    simp only [hp, zero_add]
    exact weightA_step_le K root model input s
  by_cases hF : IsFLQ K input
  · have hp : ∀ r : CostSpec.Range input × State, payK K root s input r.2 = 0 := fun r => by
      unfold payK
      rw [if_neg (fun h => h.1 hF)]
    simp only [hp, zero_add]
    exact weightA_step_le K root model input s
  have hpt : ∀ s' : State, weightB K s' ≤ weightB K s →
      payK K root s input s' + weightA K root s' ≤ weightA K root s :=
    fun s' hle => payK_add_le K root input hn hle
  rcases input with (draw | (x | c)) | amount
  · change ∑' r, Pr[= r | (fun v => (v, s)) <$> (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
      (payK K root s (.inl (.inl draw)) r.2 + weightA K root r.2) ≤ _
    rw [tsum_probOutput_map_mul]
    calc _ ≤ ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] * weightA K root s :=
          ENNReal.tsum_le_tsum fun v => mul_le_mul_right (hpt s le_rfl) _
      _ ≤ _ := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' tsum_probOutput_le_one
  · rw [costStep_ordinary]
    have hmean : ∑' r, Pr[= r | ordinaryStep model x s.known s] * weightA K root r.2 ≤ weightA K root s := by
      have := weightA_step_le K root model (.inl (.inr (.inl x))) s
      rwa [costStep_ordinary] at this
    rcases ordinaryStep_known_or_expose model x s with hk | ⟨a, ha⟩
    · calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] * weightA K root s := by
            refine ENNReal.tsum_le_tsum fun r => ?_
            by_cases hr : r ∈ support (ordinaryStep model x s.known s)
            · obtain ⟨hk1, hext⟩ := hk r hr
              exact mul_le_mul_right (hpt r.2 (weightB_le_of_extends K hext hk1)) _
            · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        _ ≤ _ := by
            rw [ENNReal.tsum_mul_right]
            exact mul_le_of_le_one_left' tsum_probOutput_le_one
    · calc _ = ∑' r, Pr[= r | ordinaryStep model x s.known s] * weightA K root r.2 := by
            refine tsum_congr fun r => ?_
            by_cases hr : r ∈ support (ordinaryStep model x s.known s)
            · obtain ⟨val, hval⟩ := ha r hr
              have hp0 : payK K root s (.inl (.inr (.inl x))) r.2 = 0 := by
                unfold payK
                rw [if_neg]
                rintro ⟨-, hk', -⟩
                rw [hval] at hk'
                refine hn (nearContact_transfer K root (s := s) (s' := s.expose (model.outgoing a) val)
                  (fun f h => h) (fun _ _ => rfl) (fun i κ l h => ?_) hk')
                rwa [known_expose_ne s val (Ne.symm (hout a i κ l))] at h
              rw [hp0, zero_add]
            · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
        _ ≤ _ := hmean
  · change ∑' r, Pr[= r | sampleCoordinate c s] * (payK K root s (.inl (.inr (.inr c))) r.2 + weightA K root r.2) ≤ _
    cases hc : s.known c with
    | some v =>
        rw [sampleCoordinate_known c s v hc, tsum_probOutput_pure_mul]
        exact hpt s le_rfl
    | none =>
        rw [sampleCoordinate_unknown c s hc, tsum_probOutput_map_mul]
        by_cases hk0 : NearContact K root (s.expose c default)
        · have hall : ∀ v, NearContact K root (s.expose c v) := fun v =>
            (nearContact_expose_iff K root s c v default).2 hk0
          have heq : ∀ v, payK K root s (.inl (.inr (.inr c))) (s.expose c v) + weightA K root (s.expose c v) =
              weightA K root s := by
            intro v
            unfold payK
            rw [if_pos ⟨hF, hall v, hn⟩, weightA_of_badP K root (Or.inr (Or.inr (Or.inr (hall v)))), add_zero]
          simp only [heq, ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' tsum_probOutput_le_one
        · have hnone : ∀ v, ¬NearContact K root (s.expose c v) := fun v h =>
            hk0 ((nearContact_expose_iff K root s c v default).1 h)
          have heq : ∀ v, payK K root s (.inl (.inr (.inr c))) (s.expose c v) + weightA K root (s.expose c v) =
              weightB K (s.expose c v) := by
            intro v
            unfold payK
            rw [if_neg (fun h => hnone v h.2.1), zero_add, weightA_eq_weightB, if_neg (hnone v)]
          simp only [heq]
          rw [weightB_expose_mean K s c hc, weightA_eq_weightB K root s, if_neg hn]
  · change ∑' r, Pr[= r | (pure ((), s) : ProbComp (Unit × State))] *
      (payK K root s (.inr amount) r.2 + weightA K root r.2) ≤ _
    rw [tsum_probOutput_pure_mul]
    exact hpt s le_rfl

/-- **The kill account is at most the weight.** -/
theorem wk_le_weightA {α : Type} (comp : OracleComp CostSpec α) :
    ∀ budget (s : State), WK model K root comp budget s ≤ weightA K root s := by
  induction comp using OracleComp.inductionOn with
  | pure value => intro budget s; exact bot_le
  | query_bind input next ih =>
      intro budget s
      change acct model (payK K root) (liftM (CostSpec.query input) >>= next) budget s ≤ _
      rw [acct_query_bind]
      split_ifs
      · refine le_trans (ENNReal.tsum_le_tsum fun r => mul_le_mul_right (add_le_add le_rfl (ih r.1 _ r.2)) _) ?_
        exact step_kill_le K root model hout input s
      · exact bot_le

end Kill

/-! ### Facts of one step -/

section Facts

variable (K : Ctx) (data : PublicData)

theorem tsum_le_of_support {β : Type} (μ : ProbComp β) (F G : β → ℝ≥0∞) (h : ∀ r ∈ support μ, F r ≤ G r) :
    ∑' r, Pr[= r | μ] * F r ≤ ∑' r, Pr[= r | μ] * G r :=
  ENNReal.tsum_le_tsum fun r => by
    by_cases hr : r ∈ support μ
    · exact mul_le_mul_right (h r hr) _
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]

theorem pairE_finset_sum {γ : Type} (S : Finset γ) (F : (DigestCall → HashOutput) → γ → ℝ≥0∞) :
    pairE (fun a => ∑ c ∈ S, F a c) = ∑ c ∈ S, pairE fun a => F a c := by
  unfold pairE
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]

theorem fck_congr {s s' : State} {f : FIn} (h : s'.cache (f.input K.p) = s.cache (f.input K.p)) :
    FCk K s' f ↔ FCk K s f := by
  unfold FCk Ctx.Fr
  rw [h]

theorem pblk_ne_fleaf (p : Pair) (call : DigestCall) (f : FIn) : pblk K.p data p call ≠ f.input K.p :=
  msg_ne_fleaf (msgInput_digestInput K.p data.root p.1 p.2 call)

theorem fck_withPair (s : State) (p : Pair) (U : DigestCall → HashOutput) (f : FIn) :
    FCk K (withPair K.p data s p U) f ↔ FCk K s f :=
  fck_congr K (withPair_other s p U _ fun call => (pblk_ne_fleaf K data p call f).symm)

theorem not_isFLQ_pblk (p : Pair) (call : DigestCall) : ¬IsFLQ K (.inl (.inr (.inl (pblk K.p data p call)))) := by
  rintro ⟨f, hf⟩
  simp only [Sum.inl.injEq, Sum.inr.injEq] at hf
  exact pblk_ne_fleaf K data p call f hf

theorem payC_fleaf (s : State) (f : FIn) :
    payC K data.root s (.inl (.inr (.inl (f.input K.p)))) =
      if SurvivesAt K data.root s f then weightA K data.root s else 0 := by
  unfold payC
  by_cases hs : SurvivesAt K data.root s f
  · rw [if_pos ⟨f, rfl, hs⟩, if_pos hs]
  · rw [if_neg hs, if_neg]
    rintro ⟨g, hg, hs'⟩
    simp only [Sum.inl.injEq, Sum.inr.injEq] at hg
    exact hs (fleaf_inj hg ▸ hs')

theorem payC_not (s : State) (x : HashInput) (hx : ∀ f : FIn, x ≠ f.input K.p) :
    payC K data.root s (.inl (.inr (.inl x))) = 0 := by
  unfold payC
  rw [if_neg]
  rintro ⟨g, hg, -⟩
  simp only [Sum.inl.injEq, Sum.inr.injEq] at hg
  exact hx g hg

variable (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

theorem excPay_fleaf (m : ℝ≥0∞) {s : State} (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (k : ℕ) (f : FIn) (hs : SurvivesAt K data.root s f) :
    excPay K data.root data wbar Fail m s P Ms L d k (f.input K.p) =
      weightA K data.root s * (min 1 (PiC K data wbar Fail (CellOf f) s P Ms L d k) - m) := by
  have hex : ∃ g : FIn, f.input K.p = g.input K.p ∧ SurvivesAt K data.root s g := ⟨f, rfl, hs⟩
  unfold excPay
  rw [dif_pos hex]
  have hch : Classical.choose hex = f := (fleaf_inj (Classical.choose_spec hex).1).symm
  rw [hch]

theorem excPay_not (m : ℝ≥0∞) (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (k : ℕ) (x : HashInput) (hx : ∀ f : FIn, x ≠ f.input K.p) :
    excPay K data.root data wbar Fail m s P Ms L d k x = 0 := by
  unfold excPay
  rw [dif_neg]
  rintro ⟨g, hg, -⟩
  exact hx g hg

theorem ncell_congr {s s' : State} {P : List Pair} (hv : ∀ q ∈ P, pview K.p data s' q = pview K.p data s q)
    (c : Cell) (L : QueryLog SigningSpec) : ncell K.p data c s' P L = ncell K.p data c s P L := by
  unfold ncell
  congr 1
  refine List.filter_congr fun q hq => ?_
  rw [hv q (List.mem_filter.1 hq).1]

theorem coefK_le {c : Cell} {s s' : State} {P P' : List Pair} {Ms Ms' : List Message} {L : QueryLog SigningSpec}
    {d : Multiset View} {k k' : ℕ} (hn : ncell K.p data c s' P' L ≤ ncell K.p data c s P L) (hk : k' ≤ k)
    (hpi : PiC K data wbar Fail c s' P' Ms' L d k' ≤ PiC K data wbar Fail c s P Ms L d k) :
    coefK K data wbar Fail c s' P' Ms' L d k' ≤ coefK K data wbar Fail c s P Ms L d k := by
  unfold coefK
  gcongr

theorem ghostP_withPair {s : State} {p : Pair} {c : DigestCall} (hp0 : s.cache (pblk K.p data p firstCall) = none)
    (P : List Pair) (U : DigestCall → HashOutput) :
    ghostP K data s (withPair K.p data s p U) (pblk K.p data p c) P = addPair K.p P p U := by
  have hex : ∃ (p' : Pair) (call : DigestCall), pblk K.p data p c = pblk K.p data p' call ∧
      s.cache (pblk K.p data p' firstCall) = none := ⟨p, c, rfl, hp0⟩
  unfold ghostP
  rw [dif_pos hex]
  have hch : Classical.choose hex = p := by
    obtain ⟨call, heq, -⟩ := Classical.choose_spec hex
    exact ((pblk_injective K.p data heq).1).symm
  rw [hch]
  have hl : LandedIn K.p data (withPair K.p data s p U) p ↔ Landed K.p (blockIndex (U firstCall)) := by
    constructor
    · rintro ⟨u0, hu0, hl⟩
      rw [withPair_self] at hu0
      cases hu0
      exact hl
    · intro hl
      exact ⟨U firstCall, withPair_self s p U firstCall, hl⟩
  unfold addPair
  by_cases h : Landed K.p (blockIndex (U firstCall))
  · rw [if_pos (hl.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hl.1 h')), if_neg h]

theorem ghostMs_new {s : State} {p : Pair} {c : DigestCall} (hp0 : s.cache (pblk K.p data p firstCall) = none)
    (Ms : List Message) : ghostMs K data s (pblk K.p data p c) Ms = addMsg Ms p.1 := by
  have hex : ∃ (p' : Pair) (call : DigestCall), pblk K.p data p c = pblk K.p data p' call ∧
      s.cache (pblk K.p data p' firstCall) = none := ⟨p, c, rfl, hp0⟩
  unfold ghostMs
  rw [dif_pos hex]
  have hch : Classical.choose hex = p := by
    obtain ⟨call, heq, -⟩ := Classical.choose_spec hex
    exact ((pblk_injective K.p data heq).1).symm
  rw [hch]

end Facts

/-! ### The potential under a new pair -/

section NewPair

variable (K : Ctx) (data : PublicData) (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Lmax T : ℕ)

theorem piC_newPair (hw : wbar ≤ 1) {s : State} {P : List Pair} {Ms : List Message}
    (hP : PInv K.p data s P) (hM : MInv K.p data s Ms) {p : Pair}
    (hp0 : s.cache (pblk K.p data p firstCall) = none) (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ)
    (hrate : MsgLive L p.1 → Rate K.p data wbar s p.1) (c : Cell) :
    pairE (fun U => PiC K data wbar Fail c (withPair K.p data s p U) (addPair K.p P p U) (addMsg Ms p.1) L d k) ≤
      PiC K data wbar Fail c s P Ms L d (k + 1) := by
  unfold PiC potG
  simp only [false_or]
  by_cases hr : signatureLimit < L.length
  · simp only [if_pos hr, pairE_const, le_refl]
  · simp only [if_neg hr]
    have := coreG_newPair wbar 0 Fail (ownW_props c) hw ENNReal.zero_ne_top hP hM hp0 L hrate d
      (signatureLimit - L.length) k
    rwa [add_zero] at this

theorem coefK_newPair (hw : wbar ≤ 1) {s : State} {P : List Pair} {Ms : List Message}
    (hP : PInv K.p data s P) (hM : MInv K.p data s Ms) {p : Pair}
    (hp0 : s.cache (pblk K.p data p firstCall) = none) (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ)
    (hrate : MsgLive L p.1 → Rate K.p data wbar s p.1) (c : Cell) :
    pairE (fun U => coefK K data wbar Fail c (withPair K.p data s p U) (addPair K.p P p U) (addMsg Ms p.1) L d k) ≤
      coefK K data wbar Fail c s P Ms L d (k + 1) := by
  have h1 := ncell_newPair K.p data hP hp0 L c
  have h2 : pairE (fun U => min 1 (PiC K data wbar Fail c (withPair K.p data s p U) (addPair K.p P p U)
      (addMsg Ms p.1) L d k)) ≤ min 1 (PiC K data wbar Fail c s P Ms L d (k + 1)) :=
    le_trans (pairE_min_leF _) (min_le_min le_rfl (piC_newPair K data wbar Fail hw hP hM hp0 L d k hrate c))
  calc pairE (fun U => coefK K data wbar Fail c (withPair K.p data s p U) (addPair K.p P p U) (addMsg Ms p.1) L d k)
      = sigRiskF L + cinv * (pairE (fun U => (ncell K.p data c (withPair K.p data s p U) (addPair K.p P p U) L : ℝ≥0∞)) +
          k * revRate) + pairE (fun U => min 1 (PiC K data wbar Fail c (withPair K.p data s p U) (addPair K.p P p U)
            (addMsg Ms p.1) L d k)) := by
        unfold coefK
        rw [pairE_add, pairE_add, pairE_const, pairE_const_mul, pairE_add, pairE_const]
    _ ≤ sigRiskF L + cinv * ((ncell K.p data c s P L + revRate) + k * revRate) +
          min 1 (PiC K data wbar Fail c s P Ms L d (k + 1)) := by
        gcongr
    _ = coefK K data wbar Fail c s P Ms L d (k + 1) := by
        unfold coefK
        push_cast
        ring

theorem lam_newPairK {P : List Pair} (p : Pair) (L : QueryLog SigningSpec) (k : ℕ) :
    pairE (fun U => lam Lmax (livePairs L (addPair K.p P p U)).length k) ≤ lam Lmax (livePairs L P).length (k + 1) := by
  set ℓ := (livePairs L P).length with hℓ
  by_cases hlive : MsgLive L p.1
  · have hl : ∀ u : DigestCall → HashOutput,
        lam Lmax (livePairs L (addPair K.p P p u)).length k =
          if Landed K.p (blockIndex (u firstCall)) then lam Lmax (ℓ + 1) k else lam Lmax ℓ k := by
      intro u
      unfold addPair livePairs
      split_ifs with hl
      · rw [List.filter_cons, if_pos (by simpa using hlive), List.length_cons]
        rfl
      · rfl
    simp only [hl]
    exact le_of_eq (lam_newPair K.p Lmax ℓ k)
  · have hl : ∀ u : DigestCall → HashOutput, lam Lmax (livePairs L (addPair K.p P p u)).length k = lam Lmax ℓ k := by
      intro u
      unfold addPair livePairs
      split_ifs with hl
      · rw [List.filter_cons, if_neg (by simpa using hlive)]
        rfl
      · rfl
    simp only [hl, pairE_const]
    exact lam_mono le_rfl (Nat.le_succ k)

/-- **The contact potential under a new pair** does not grow in the mean (one unit of budget pays the
new pair's share of the cell counts). -/
theorem psiK_newPair (hw : wbar ≤ 1) {s : State} {P : List Pair} {Ms : List Message}
    (hP : PInv K.p data s P) (hM : MInv K.p data s Ms) {p : Pair}
    (hp0 : s.cache (pblk K.p data p firstCall) = none) (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ)
    (hrate : MsgLive L p.1 → Rate K.p data wbar s p.1) :
    pairE (fun U => psiK K data wbar Fail Lmax T (withPair K.p data s p U) (addPair K.p P p U) (addMsg Ms p.1) L d k) ≤
      psiK K data wbar Fail Lmax T s P Ms L d (k + 1) := by
  unfold psiK
  rw [pairE_add, pairE_add, pairE_add, pairE_const]
  refine add_le_add (add_le_add (add_le_add ?_ ?_) (capC_newPair K.p data T hP hp0 L k))
    (lam_newPairK K Lmax p L k)
  · simp only [fck_withPair K data s p]
    rw [pairE_finset_sum]
    refine Finset.sum_le_sum fun g _ => ?_
    by_cases hg : FCk K s g
    · simp only [if_pos hg]
      exact coefK_newPair K data wbar Fail hw hP hM hp0 L d k hrate (CellOf g)
    · simp only [if_neg hg, pairE_const, le_refl]
  · rw [coinPotK_succ]
    exact le_self_add

end NewPair

/-! ### A new contact at a FORS leaf query has chance at most `ν` -/

section Prob

variable (K : Ctx) {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)

theorem tsum_sample_zero (c : Coordinate) (s : State) (F : Digest × State → ℝ≥0∞)
    (hF : ∀ v, F (v, s.expose c v) = 0) : ∑' res, Pr[= res | sampleCoordinate c s] * F res = 0 := by
  refine ENNReal.tsum_eq_zero.2 fun res => ?_
  by_cases hres : res ∈ support (sampleCoordinate c s)
  · have h2 := sampleCoordinate_expose c s res hres
    have hres' : F res = 0 := by
      have : res = (res.1, s.expose c res.1) := Prod.ext rfl h2
      rw [this]
      exact hF _
    rw [hres', mul_zero]
  · rw [probOutput_eq_zero_of_not_mem_support hres, zero_mul]

/-- **A FORS leaf query decides a new contact with chance at most `ν`**: only a fresh answer can, and
its truncation is uniform. -/
theorem prob_newContact (s : State) (f : FIn) :
    ∑' r, Pr[= r | ordinaryStep model (f.input K.p) s.known s] *
      (if FCk K r.2 f ∧ ¬FCk K s f then (1 : ℝ≥0∞) else 0) ≤ ν := by
  have hread : ∀ s0 : State, s0.cache = s.cache →
      ∑' r, Pr[= r | readOutside (f.input K.p) s0] * (if FCk K r.2 f ∧ ¬FCk K s f then (1 : ℝ≥0∞) else 0) ≤ ν := by
    intro s0 hs0
    cases hc : s0.cache (f.input K.p) with
    | some u =>
        rw [readOutside_cached _ s0 u hc, tsum_probOutput_pure_mul, if_neg]
        · exact zero_le
        · rintro ⟨h1, h2⟩
          exact h2 ((fck_congr K (s := s) (s' := s0) (by rw [hs0])).1 h1)
    | none =>
        rw [readOutside_fresh _ s0 hc, tsum_probOutput_map_mul]
        have hmean := mean_trunc (fun t : Digest => if t = K.F f.outC then (1 : ℝ≥0∞) else 0)
        rw [meanD_ite_eq (K.F f.outC) (fun t => t = K.F f.outC) (fun t => Iff.rfl), mul_one] at hmean
        refine le_trans (ENNReal.tsum_le_tsum fun u => mul_le_mul_right ?_ _) (le_of_eq hmean)
        by_cases h : FCk K (s0.store (f.input K.p) u) f ∧ ¬FCk K s f
        · rw [if_pos h]
          obtain ⟨w, ⟨hw, -⟩, ht⟩ := h.1
          have hself : (s0.store (f.input K.p) u).cache (f.input K.p) = some u := by
            simp [DebtState.store]
          rw [hself] at hw
          cases hw
          simp only [ht, if_true, le_refl]
        · rw [if_neg h]
          exact zero_le
  unfold ordinaryStep
  split
  · exact hread s rfl
  · split
    · exact hread _ (by rfl)
    · split
      · rw [tsum_probOutput_map_mul]
        refine le_trans (le_of_eq (tsum_sample_zero _ s _ fun v => ?_)) zero_le
        show (if FCk K (s.expose _ v) f ∧ ¬FCk K s f then (1 : ℝ≥0∞) else 0) = 0
        rw [if_neg]
        rintro ⟨h1, h3⟩
        exact h3 h1
      · exact hread s rfl

end Prob

/-! ### One ordinary query -/

section Step

variable (K : Ctx) (data : PublicData) (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Lmax T : ℕ)
  {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate) (cU m : ℝ≥0∞) (Qtot : ℕ)

/-- **A cost program paid by the contact potential**, with an abstract excess functional `X` (the
excess account of the rest of the game, read from the ghost state). -/
def GoodKC {α : Type} (L : QueryLog SigningSpec) (d : Multiset View) (prog : OracleComp CostSpec α)
    (X : ℕ → State → List Pair → List Message → ℝ≥0∞) : Prop :=
  ∀ budget (s : State) (P : List Pair) (Ms : List Message) (R : List Coordinate),
    InvK K data Qtot budget s P Ms L d R →
      WK model K data.root prog budget s ≤
        weightA K data.root s * psiK K data wbar Fail Lmax T s P Ms L d budget +
          cU * WC model K data.root prog budget s + ν * X budget s P Ms

/-- The excess functional of one ordinary query followed by a continuation (the hash case of `XS`
and of `xsHash`). -/
noncomputable def xsStep (L : QueryLog SigningSpec) (d : Multiset View) (x : HashInput)
    (Xn : HashOutput → ℕ → State → List Pair → List Message → ℝ≥0∞) :
    ℕ → State → List Pair → List Message → ℝ≥0∞ := fun budget s P Ms =>
  if 1 ≤ budget then
    ∑' r, Pr[= r | ordinaryStep model x s.known s] *
      (excPay K data.root data wbar Fail m s P Ms L d budget x +
        Xn r.1 (budget - 1) r.2 (ghostP K data s r.2 x P) (ghostMs K data s x Ms))
  else 0

/-- Chaining one step with the rest: the rest's bound at every outcome and the step's bound on the
kill payment and the weighted potential after it. -/
theorem combine_step {β : Type} (μ : ProbComp β) (hμ : ∑' r, Pr[= r | μ] = 1)
    (pk wa wk wc xn : β → ℝ≥0∞) (a pc pe c n : ℝ≥0∞)
    (hih : ∀ r ∈ support μ, wk r ≤ wa r + c * wc r + n * xn r)
    (hcore : ∑' r, Pr[= r | μ] * (pk r + wa r) ≤ a + c * pc + n * pe) :
    ∑' r, Pr[= r | μ] * (pk r + wk r) ≤
      a + c * ∑' r, Pr[= r | μ] * (pc + wc r) + n * ∑' r, Pr[= r | μ] * (pe + xn r) := by
  have hsplit : ∀ (k : ℝ≥0∞) (F : β → ℝ≥0∞), ∑' r, Pr[= r | μ] * (k + F r) = k + ∑' r, Pr[= r | μ] * F r := by
    intro k F
    simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hμ, one_mul]
  calc ∑' r, Pr[= r | μ] * (pk r + wk r) ≤ ∑' r, Pr[= r | μ] * ((pk r + wa r) + c * wc r + n * xn r) :=
        tsum_le_of_support μ _ _ fun r hr => by
          calc pk r + wk r ≤ pk r + (wa r + c * wc r + n * xn r) := add_le_add le_rfl (hih r hr)
            _ = _ := by ring
    _ = ∑' r, Pr[= r | μ] * (pk r + wa r) + c * ∑' r, Pr[= r | μ] * wc r + n * ∑' r, Pr[= r | μ] * xn r := by
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
        exact tsum_congr fun r => by ring
    _ ≤ (a + c * pc + n * pe) + c * ∑' r, Pr[= r | μ] * wc r + n * ∑' r, Pr[= r | μ] * xn r := by gcongr
    _ = a + c * (pc + ∑' r, Pr[= r | μ] * wc r) + n * (pe + ∑' r, Pr[= r | μ] * xn r) := by ring
    _ = _ := by rw [hsplit, hsplit]

variable (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0)
include hout

/-- **The step without a new pair.** No kill; at a FORS leaf query a new contact (chance `ν`) that
would survive costs its coefficient, paid by `cU`, the excess account and one unit of the coin
forecast. -/
theorem core_notNew (hcalls : digestCalls = 1) (hw : wbar ≤ 1)
    (hcU : ν * ((signatureLimit : ℝ≥0∞) * revRate + m) ≤ cU)
    {b : ℕ} {s : State} {P : List Pair} {Ms : List Message} {L : QueryLog SigningSpec} {d : Multiset View}
    (hP : PInv K.p data s P) (hcells : ∀ c, ncell K.p data c s P L < T) (x : HashInput)
    (hnew : ¬∃ (p : Pair) (call : DigestCall), x = pblk K.p data p call ∧ s.cache (pblk K.p data p firstCall) = none) :
    ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        (payK K data.root s (.inl (.inr (.inl x))) r.2 +
          weightA K data.root r.2 * psiK K data wbar Fail Lmax T r.2 P Ms L d b) ≤
      weightA K data.root s * psiK K data wbar Fail Lmax T s P Ms L d (b + 1) +
        cU * payC K data.root s (.inl (.inr (.inl x))) +
        ν * excPay K data.root data wbar Fail m s P Ms L d (b + 1) x := by
  have hfacts : ∀ r ∈ support (ordinaryStep model x s.known s),
      Extends s r.2 ∧ (∀ c, ncell K.p data c r.2 P L = ncell K.p data c s P L) ∧
      (∀ c, PiC K data wbar Fail c r.2 P Ms L d b ≤ PiC K data wbar Fail c s P Ms L d (b + 1)) ∧
      (∀ g : FIn, x ≠ g.input K.p → (FCk K r.2 g ↔ FCk K s g)) ∧
      (r.2.known = s.known ∨ r.2.cache = s.cache) ∧
      (∀ i κ l, r.2.known (Coordinate.fors i κ l 0) ≠ none → s.known (Coordinate.fors i κ l 0) ≠ none) ∧
      (∀ mm ρ, HiddenBridge.cachedDigest r.2.cache K.p data.root mm ρ =
        HiddenBridge.cachedDigest s.cache K.p data.root mm ρ) := by
    intro r hr
    have hext := ordinaryStep_extends model x s r hr
    have hother := ordinaryStep_cache_ne model x s r hr
    have hblocks := same_blocks (parameter := K.p) (data := data) hext hother hnew
    obtain ⟨-, hpv⟩ := same_items K.p data hext hother hnew hP
    have hland : ∀ q, LandedIn K.p data s q → ∀ call,
        r.2.cache (pblk K.p data q call) = s.cache (pblk K.p data q call) :=
      fun q hq call => landed_blocks hext hP hq call
    refine ⟨hext, fun c => ncell_congr K data hpv c L, fun c => ?_, fun g hg => fck_congr K (hother _ (Ne.symm hg)),
      ?_, ?_, ?_⟩
    · exact potG_grow wbar 0 Fail (ownW_props c) (fun _ _ _ h => h) hw ENNReal.zero_ne_top hext hblocks hland
        (fun q hq => (hP.mem q).1 hq) Ms L d (Nat.le_succ b)
    · rcases ordinaryStep_shape x s r hr with ⟨_, h1 | ⟨_, h1⟩⟩ | ⟨a, v, _, _, ⟨_, h1⟩ | ⟨_, h1⟩⟩ |
          ⟨a, v, val, _, h1⟩
      · exact Or.inl (by rw [h1])
      · exact Or.inl (by rw [h1]; try rfl)
      · exact Or.inl (by rw [h1]; try rfl)
      · exact Or.inl (by rw [h1]; try rfl)
      · exact Or.inr (by rw [h1]; try rfl)
    · intro i κ l hk
      rcases known_ordinary model x s r hr _ hk with h' | ⟨a, ha⟩
      · exact h'
      · exact absurd ha.symm (hout a i κ l)
    · intro mm ρ
      have hcall : ∀ call : DigestCall,
          r.2.cache (pblk K.p data (mm, ρ) call) = s.cache (pblk K.p data (mm, ρ) call) := by
        intro call
        have hc : call = firstCall := Fin.ext (show call.val = 0 by have := call.isLt; omega)
        rw [hc]
        exact hblocks (mm, ρ)
      have hpc : pcache K.p data mm r.2 ρ = pcache K.p data mm s ρ := pcache_congr K.p data (p := (mm, ρ)) hcall
      change (pcache K.p data mm r.2 ρ).map truncateMessageDigest = (pcache K.p data mm s ρ).map truncateMessageDigest
      rw [hpc]
  set S0 : ℝ≥0∞ := ∑ g : FIn, if FCk K s g then coefK K data wbar Fail (CellOf g) s P Ms L d (b + 1) else 0 with hS0
  set ψ' : ℝ≥0∞ := S0 + coinPotK T b + capC K.p data T (b + 1) s P L + lam Lmax (livePairs L P).length (b + 1)
    with hψ'
  have hψeq : psiK K data wbar Fail Lmax T s P Ms L d (b + 1) = ψ' + ν * cinv * (T + b * revRate) := by
    rw [hψ', hS0]
    unfold psiK
    rw [coinPotK_succ]
    ring
  have hpsi_r : ∀ r ∈ support (ordinaryStep model x s.known s),
      psiK K data wbar Fail Lmax T r.2 P Ms L d b ≤ ψ' +
        ∑ g : FIn, if FCk K r.2 g ∧ ¬FCk K s g then coefK K data wbar Fail (CellOf g) r.2 P Ms L d b else 0 := by
    intro r hr
    obtain ⟨hext, hnc, hpi, -, -, -, -⟩ := hfacts r hr
    have hsum : (∑ g : FIn, if FCk K r.2 g then coefK K data wbar Fail (CellOf g) r.2 P Ms L d b else 0) ≤
        S0 + ∑ g : FIn, if FCk K r.2 g ∧ ¬FCk K s g then coefK K data wbar Fail (CellOf g) r.2 P Ms L d b else 0 := by
      rw [hS0, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun g _ => ?_
      have hle : coefK K data wbar Fail (CellOf g) r.2 P Ms L d b ≤
          coefK K data wbar Fail (CellOf g) s P Ms L d (b + 1) :=
        coefK_le K data wbar Fail (le_of_eq (hnc _)) (Nat.le_succ b) (hpi _)
      by_cases h1 : FCk K s g
      · rw [if_pos (fck_mono hext h1), if_pos h1, if_neg (fun h => h.2 h1), add_zero]
        exact hle
      · by_cases h2 : FCk K r.2 g
        · rw [if_pos h2, if_neg h1, if_pos ⟨h2, h1⟩, zero_add]
        · rw [if_neg h2, if_neg h1, if_neg (fun h => h2 h.1), add_zero]
    have hcap : capC K.p data T b r.2 P L ≤ capC K.p data T (b + 1) s P L :=
      capC_mono K.p data T (Nat.le_succ b) fun c => le_of_eq (hnc c)
    have hlam : lam Lmax (livePairs L P).length b ≤ lam Lmax (livePairs L P).length (b + 1) :=
      lam_mono le_rfl (Nat.le_succ b)
    unfold psiK
    calc _ ≤ (S0 + ∑ g : FIn, if FCk K r.2 g ∧ ¬FCk K s g then
            coefK K data wbar Fail (CellOf g) r.2 P Ms L d b else 0) + coinPotK T b +
          capC K.p data T (b + 1) s P L + lam Lmax (livePairs L P).length (b + 1) :=
          add_le_add (add_le_add (add_le_add hsum le_rfl) hcap) hlam
      _ = _ := by rw [hψ']; ring
  have hmean : ∀ y : HashInput,
      ∑' r, Pr[= r | ordinaryStep model y s.known s] * weightA K data.root r.2 ≤ weightA K data.root s := by
    intro y
    have := weightA_step_le K data.root model (.inl (.inr (.inl y))) s
    rwa [costStep_ordinary] at this
  have hψle : ψ' ≤ psiK K data wbar Fail Lmax T s P Ms L d (b + 1) := by
    rw [hψeq]
    exact le_self_add
  by_cases hF : ∃ f : FIn, x = f.input K.p
  · obtain ⟨f, rfl⟩ := hF
    have hp0 : ∀ r : HashOutput × State, payK K data.root s (.inl (.inr (.inl (f.input K.p)))) r.2 = 0 := by
      intro r
      unfold payK
      rw [if_neg]
      rintro ⟨h, -⟩
      exact h ⟨f, rfl⟩
    set mi : ℝ≥0∞ := min 1 (PiC K data wbar Fail (CellOf f) s P Ms L d (b + 1)) with hmi
    set Cf : ℝ≥0∞ := sigRiskF L + cinv * ((T : ℝ≥0∞) + b * revRate) + mi with hCf
    set D : ℝ≥0∞ := if SurvivesAt K data.root s f then weightA K data.root s * Cf else 0 with hD
    have hpt : ∀ r ∈ support (ordinaryStep model (f.input K.p) s.known s),
        payK K data.root s (.inl (.inr (.inl (f.input K.p)))) r.2 +
            weightA K data.root r.2 * psiK K data wbar Fail Lmax T r.2 P Ms L d b ≤
          weightA K data.root r.2 * ψ' + D * (if FCk K r.2 f ∧ ¬FCk K s f then 1 else 0) := by
      intro r hr
      obtain ⟨hext, hnc, hpi, hfc, hkc, -, -⟩ := hfacts r hr
      rw [hp0, zero_add]
      have hnew_sum : (∑ g : FIn, if FCk K r.2 g ∧ ¬FCk K s g then
            coefK K data wbar Fail (CellOf g) r.2 P Ms L d b else 0) =
          if FCk K r.2 f ∧ ¬FCk K s f then coefK K data wbar Fail (CellOf f) r.2 P Ms L d b else 0 :=
        Finset.sum_eq_single f
          (fun g _ hgf => if_neg fun h => h.2 ((hfc g fun he => hgf (fleaf_inj he).symm).1 h.1))
          (fun h => absurd (Finset.mem_univ f) h)
      have h1 := hpsi_r r hr
      rw [hnew_sum] at h1
      refine le_trans (mul_le_mul_right h1 _) ?_
      rw [mul_add]
      refine add_le_add le_rfl ?_
      by_cases hnw : FCk K r.2 f ∧ ¬FCk K s f
      · rw [if_pos hnw, if_pos hnw, mul_one]
        have hkn : r.2.known = s.known := by
          rcases hkc with h | h
          · exact h
          · exact absurd ((fck_congr K (by rw [h])).1 hnw.1) hnw.2
        by_cases hs : SurvivesAt K data.root s f
        · rw [hD, if_pos hs]
          refine mul_le_mul' (weightA_le_of_extends hext hkn) ?_
          rw [hCf, hmi]
          unfold coefK
          refine add_le_add (add_le_add le_rfl (mul_le_mul_right (add_le_add ?_ le_rfl) _))
            (min_le_min le_rfl (hpi _))
          exact_mod_cast ((hnc (CellOf f)).trans_lt (hcells (CellOf f))).le
        · have hbad : BadP K data.root r.2 := by
            by_cases h1 : s.known f.inC = none
            · by_cases h2 : NearLeaf K data.root s f.index f.κ f.leaf
              · exact Or.inr (Or.inr (Or.inr ⟨f, hnw.1, Or.inr (nearLeaf_mono hext h2)⟩))
              · by_cases h3 : FContact K s
                · obtain ⟨g, hg⟩ := h3
                  have hgf : f ≠ g := fun h => hnw.2 (h ▸ hg)
                  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ⟨f, g, hgf, hnw.1, fck_mono hext hg⟩))))
                · have h4 : WContact K s := by
                    by_contra h4
                    exact hs ⟨h1, h2, h3, h4⟩
                  exact Or.inr (Or.inr (Or.inl (Or.inr (Or.inr ⟨wContact_mono hext h4, ⟨f, hnw.1⟩⟩))))
            · exact Or.inr (Or.inr (Or.inr ⟨f, hnw.1, Or.inl (by rw [hkn]; exact h1)⟩))
          rw [weightA_of_badP K data.root hbad, zero_mul]
          exact zero_le
      · rw [if_neg hnw, if_neg hnw, mul_zero, mul_zero]
    have hprob := prob_newContact K model s f
    calc _ ≤ ∑' r, Pr[= r | ordinaryStep model (f.input K.p) s.known s] *
            (weightA K data.root r.2 * ψ' + D * (if FCk K r.2 f ∧ ¬FCk K s f then 1 else 0)) :=
          tsum_le_of_support _ _ _ hpt
      _ = (∑' r, Pr[= r | ordinaryStep model (f.input K.p) s.known s] * weightA K data.root r.2) * ψ' +
            D * ∑' r, Pr[= r | ordinaryStep model (f.input K.p) s.known s] *
              (if FCk K r.2 f ∧ ¬FCk K s f then (1 : ℝ≥0∞) else 0) := by
          rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
          exact tsum_congr fun r => by ring
      _ ≤ weightA K data.root s * ψ' + D * ν :=
          add_le_add (mul_le_mul' (hmean _) le_rfl) (mul_le_mul_right hprob _)
      _ ≤ _ := by
          rw [hψeq, payC_fleaf K data s f]
          by_cases hs : SurvivesAt K data.root s f
          · rw [if_pos hs, excPay_fleaf K data wbar Fail m P Ms L d (b + 1) f hs, hD, if_pos hs, hCf, ← hmi]
            have hsig : sigRiskF L ≤ (signatureLimit : ℝ≥0∞) * revRate := by
              unfold sigRiskF
              gcongr
              exact_mod_cast Nat.sub_le _ _
            have hkey : ν * sigRiskF L + ν * mi ≤ cU + ν * (mi - m) :=
              calc ν * sigRiskF L + ν * mi ≤ ν * ((signatureLimit : ℝ≥0∞) * revRate) + ν * (m + (mi - m)) := by
                    gcongr
                    exact le_add_tsub
                _ = ν * ((signatureLimit : ℝ≥0∞) * revRate + m) + ν * (mi - m) := by ring
                _ ≤ cU + ν * (mi - m) := add_le_add hcU le_rfl
            calc weightA K data.root s * ψ' + weightA K data.root s * (sigRiskF L + cinv * (T + b * revRate) + mi) * ν
                = weightA K data.root s * (ψ' + ν * cinv * (T + b * revRate)) +
                    weightA K data.root s * (ν * sigRiskF L + ν * mi) := by ring
              _ ≤ weightA K data.root s * (ψ' + ν * cinv * (T + b * revRate)) +
                    weightA K data.root s * (cU + ν * (mi - m)) := by gcongr
              _ = _ := by ring
          · rw [if_neg hs, hD, if_neg hs, zero_mul, add_zero]
            exact le_trans (mul_le_mul_right le_self_add _) (le_trans le_self_add le_self_add)
  · push Not at hF
    have hpt : ∀ r ∈ support (ordinaryStep model x s.known s),
        payK K data.root s (.inl (.inr (.inl x))) r.2 +
            weightA K data.root r.2 * psiK K data wbar Fail Lmax T r.2 P Ms L d b ≤
          weightA K data.root r.2 * ψ' := by
      intro r hr
      obtain ⟨-, -, -, hfc, -, hkn, hcd⟩ := hfacts r hr
      have hp0 : payK K data.root s (.inl (.inr (.inl x))) r.2 = 0 := by
        unfold payK
        rw [if_neg]
        rintro ⟨-, hk, hn⟩
        exact hn (nearContact_transfer K data.root (s := s) (s' := r.2) (fun g h => (hfc g (hF g)).1 h) hcd hkn hk)
      have hz : (∑ g : FIn, if FCk K r.2 g ∧ ¬FCk K s g then
          coefK K data wbar Fail (CellOf g) r.2 P Ms L d b else 0) = 0 :=
        Finset.sum_eq_zero fun g _ => if_neg fun h => h.2 ((hfc g (hF g)).1 h.1)
      have h1 := hpsi_r r hr
      rw [hz, add_zero] at h1
      rw [hp0, zero_add]
      exact mul_le_mul_right h1 _
    calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] * (weightA K data.root r.2 * ψ') :=
          tsum_le_of_support _ _ _ hpt
      _ = (∑' r, Pr[= r | ordinaryStep model x s.known s] * weightA K data.root r.2) * ψ' := by
          rw [← ENNReal.tsum_mul_right]
          exact tsum_congr fun r => by ring
      _ ≤ weightA K data.root s * psiK K data wbar Fail Lmax T s P Ms L d (b + 1) :=
          mul_le_mul' (hmean x) hψle
      _ ≤ _ := le_trans le_self_add le_self_add

/-- **The step of a new pair.** A kill (a near cell at a contact) makes the contact's own-cell
forecast at least one, so the potential after the step pays it. -/
theorem core_newPair (hw : wbar ≤ 1) {b : ℕ} {s : State} {P : List Pair} {Ms : List Message}
    {L : QueryLog SigningSpec} {d : Multiset View} {R : List Coordinate} (hP : PInv K.p data s P) (hD : DInv R d)
    (hJ : JInv K.p data s L R) (hL : L.length ≤ signatureLimit) {p : Pair} (c : DigestCall)
    (hp0 : s.cache (pblk K.p data p firstCall) = none) (U : DigestCall → HashOutput) :
    payK K data.root s (.inl (.inr (.inl (pblk K.p data p c)))) (withPair K.p data s p U) +
        weightA K data.root (withPair K.p data s p U) *
          psiK K data wbar Fail Lmax T (withPair K.p data s p U) (addPair K.p P p U) (addMsg Ms p.1) L d b ≤
      weightA K data.root s *
        psiK K data wbar Fail Lmax T (withPair K.p data s p U) (addPair K.p P p U) (addMsg Ms p.1) L d b := by
  have hfresh : ∀ call, s.cache (pblk K.p data p call) = none := hP.first p hp0
  have hext : Extends s (withPair K.p data s p U) := extends_withPair hP hp0 U
  have hkn : (withPair K.p data s p U).known = s.known := (withPair_known s p U).1
  have hfck : ∀ g, FCk K (withPair K.p data s p U) g ↔ FCk K s g := fun g => fck_withPair K data s p U g
  by_cases hn : NearContact K data.root s
  · have h0' : weightA K data.root (withPair K.p data s p U) = 0 :=
      weightA_of_badP K data.root (badP_mono hext (Or.inr (Or.inr (Or.inr hn))))
    have hp : payK K data.root s (.inl (.inr (.inl (pblk K.p data p c)))) (withPair K.p data s p U) = 0 := by
      unfold payK
      rw [if_neg (fun h => h.2.2 hn)]
    rw [hp, h0', zero_mul, zero_add]
    exact zero_le
  by_cases hk : NearContact K data.root (withPair K.p data s p U)
  · have hp : payK K data.root s (.inl (.inr (.inl (pblk K.p data p c)))) (withPair K.p data s p U) =
        weightA K data.root s := by
      unfold payK
      rw [if_pos ⟨not_isFLQ_pblk K data p c, hk, hn⟩]
    rw [hp, weightA_of_badP K data.root (Or.inr (Or.inr (Or.inr hk))), zero_mul, add_zero]
    refine le_mul_of_one_le_right' ?_
    obtain ⟨g, hg, hkg | hnl⟩ := hk
    · exact absurd ⟨g, (hfck g).1 hg, Or.inl (by rwa [hkn] at hkg)⟩ hn
    · have hmiss : (withPair K.p data s p U).known g.inC = none := by
        by_contra hne
        exact hn ⟨g, (hfck g).1 hg, Or.inl (by rwa [hkn] at hne)⟩
      have h1 := release_ownW K data wbar Fail hw (Ms := addMsg Ms p.1) b g (pinv_withPair hP hp0 U) hD
        (jInv_withPair K.p data model hout s L R p U hfresh hJ) hL hnl hmiss
      calc (1 : ℝ≥0∞) ≤ min 1 (PiC K data wbar Fail (CellOf g) (withPair K.p data s p U) (addPair K.p P p U)
            (addMsg Ms p.1) L d b) := le_min le_rfl h1
        _ ≤ coefK K data wbar Fail (CellOf g) (withPair K.p data s p U) (addPair K.p P p U) (addMsg Ms p.1) L d b :=
            le_add_self
        _ ≤ ∑ g' : FIn, if FCk K (withPair K.p data s p U) g' then
              coefK K data wbar Fail (CellOf g') (withPair K.p data s p U) (addPair K.p P p U) (addMsg Ms p.1) L d b
              else 0 := by
            have hsingle := Finset.single_le_sum (f := fun g' => if FCk K (withPair K.p data s p U) g' then
              coefK K data wbar Fail (CellOf g') (withPair K.p data s p U) (addPair K.p P p U) (addMsg Ms p.1) L d b
              else 0) (fun _ _ => zero_le) (Finset.mem_univ g)
            simp only [if_pos hg] at hsingle
            exact hsingle
        _ ≤ _ := by
            unfold psiK
            exact le_self_add.trans (le_self_add.trans le_self_add)
  · have hp : payK K data.root s (.inl (.inr (.inl (pblk K.p data p c)))) (withPair K.p data s p U) = 0 := by
      unfold payK
      rw [if_neg (fun h => hk h.2.1)]
    rw [hp, zero_add]
    exact mul_le_mul' (weightA_le_of_extends hext hkn) le_rfl

omit hout in
/-- The invariants after a new pair. -/
theorem invK_withPair (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0) {b : ℕ} {s : State}
    {P : List Pair} {Ms : List Message} {L : QueryLog SigningSpec} {d : Multiset View} {R : List Coordinate}
    (hI : InvK K data Qtot (b + 1) s P Ms L d R) {p : Pair} (hp0 : s.cache (pblk K.p data p firstCall) = none)
    (U : DigestCall → HashOutput) :
    InvK K data Qtot b (withPair K.p data s p U) (addPair K.p P p U) (addMsg Ms p.1) L d R := by
  have hfresh : ∀ call, s.cache (pblk K.p data p call) = none := hI.pinv.first p hp0
  refine ⟨fun i o hi => (extends_withPair hI.pinv hp0 U).1 i o (hI.prep i o hi), pinv_withPair hI.pinv hp0 U,
    minv_withPair hI.minv p U, hI.dinv, fun mm => ?_, jInv_withPair K.p data model hout s L R p U hfresh hI.jinv,
    hI.len⟩
  have h1 := count_withPair (parameter := K.p) (data := data) mm s p U
  have h2 := hI.count mm
  omega

omit hout in
/-- The invariants after an ordinary query without a new pair. -/
theorem invK_ordinary (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0) {b : ℕ} {s : State}
    {P : List Pair} {Ms : List Message} {L : QueryLog SigningSpec} {d : Multiset View} {R : List Coordinate}
    (hI : InvK K data Qtot (b + 1) s P Ms L d R) (x : HashInput)
    (hnew : ¬∃ (p : Pair) (call : DigestCall), x = pblk K.p data p call ∧ s.cache (pblk K.p data p firstCall) = none)
    (r : HashOutput × State) (hr : r ∈ support (ordinaryStep model x s.known s)) :
    InvK K data Qtot b r.2 P Ms L d R := by
  have hext := ordinaryStep_extends model x s r hr
  have hother := ordinaryStep_cache_ne model x s r hr
  have hblocks := same_blocks (parameter := K.p) (data := data) hext hother hnew
  obtain ⟨hP', -⟩ := same_items K.p data hext hother hnew hI.pinv
  refine ⟨fun i o hi => hext.1 i o (hI.prep i o hi), hP', minv_blocks hblocks hI.minv, hI.dinv, fun mm => ?_,
    jInv_ordinary K.p data model hout s L R x r hr hI.jinv, hI.len⟩
  have h1 : cachedCount K.p data mm r.2 ≤ cachedCount K.p data mm s + 1 := by
    rw [cachedCount_eq, cachedCount_eq]
    exact costStep_card_le model _ (.inl (.inr (.inl x))) s r (by rw [costStep_ordinary]; exact hr)
  have h2 := hI.count mm
  omega

omit hout in
/-- **One ordinary query**, followed by any continuation paid by the contact potential. -/
theorem goodKC_ordinary (hcalls : digestCalls = 1)
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none)
    (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0)
    {Cmax : ℕ} (hfair : FairS wbar Cmax Lmax) (hQ : Qtot ≤ Cmax)
    (hcU : ν * ((signatureLimit : ℝ≥0∞) * revRate + m) ≤ cU)
    {α : Type} (L : QueryLog SigningSpec) (d : Multiset View) (x : HashInput)
    (next : HashOutput → OracleComp CostSpec α)
    (Xn : HashOutput → ℕ → State → List Pair → List Message → ℝ≥0∞)
    (h : ∀ v, GoodKC K data wbar Fail Lmax T model cU Qtot L d (next v) (Xn v)) :
    GoodKC K data wbar Fail Lmax T model cU Qtot L d (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next)
      (xsStep K data wbar Fail model m L d x Xn) := by
  intro budget s P Ms R hI
  have hw : wbar ≤ 1 := hfair.le_one
  by_cases hb : 1 ≤ budget
  swap
  · change acct model (payK K data.root) (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) budget s ≤ _
    rw [acct_query_bind, if_neg (by change ¬1 ≤ budget; exact hb)]
    exact zero_le
  obtain ⟨b, rfl⟩ : ∃ b, budget = b + 1 := ⟨budget - 1, by omega⟩
  by_cases hcap : 1 ≤ psiK K data wbar Fail Lmax T s P Ms L d (b + 1)
  · refine le_trans (wk_le_weightA K data.root model hout _ (b + 1) s) ?_
    exact le_trans (le_mul_of_one_le_right' hcap) (le_trans le_self_add le_self_add)
  have hcells : ∀ c, ncell K.p data c s P L < T := by
    intro c
    by_contra hc
    push Not at hc
    refine hcap (le_trans (one_le_capC K.p data T (k := b + 1) c hc) ?_)
    unfold psiK
    exact le_add_self.trans le_self_add
  have hlen : (livePairs L P).length < Lmax := by
    by_contra hl
    push Not at hl
    refine hcap (le_trans (one_le_lam hl (b + 1)) ?_)
    unfold psiK
    exact le_add_self
  have hK : WK model K data.root (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) (b + 1) s =
      ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        (payK K data.root s (.inl (.inr (.inl x))) r.2 + WK model K data.root (next r.1) (b + 1 - 1) r.2) := by
    change acct model (payK K data.root) (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) (b + 1) s = _
    rw [acct_query_bind, costStep_ordinary]
    exact if_pos (Nat.le_add_left 1 b)
  have hC : WC model K data.root (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) (b + 1) s =
      ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        (payC K data.root s (.inl (.inr (.inl x))) + WC model K data.root (next r.1) (b + 1 - 1) r.2) := by
    change acct model (fun s i _ => payC K data.root s i) (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next)
      (b + 1) s = _
    rw [acct_query_bind, costStep_ordinary]
    exact if_pos (Nat.le_add_left 1 b)
  have hX : xsStep K data wbar Fail model m L d x Xn (b + 1) s P Ms =
      ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        (excPay K data.root data wbar Fail m s P Ms L d (b + 1) x +
          Xn r.1 (b + 1 - 1) r.2 (ghostP K data s r.2 x P) (ghostMs K data s x Ms)) :=
    if_pos (Nat.le_add_left 1 b)
  rw [hK, hC, hX, Nat.add_sub_cancel]
  by_cases hnew : ∃ (p : Pair) (call : DigestCall), x = pblk K.p data p call ∧
      s.cache (pblk K.p data p firstCall) = none
  · obtain ⟨p, c, rfl, hp0⟩ := hnew
    have hfresh : ∀ call, s.cache (pblk K.p data p call) = none := hI.pinv.first p hp0
    have hord : ordinaryStep model (pblk K.p data p c) s.known s =
        (fun u => (u, s.store (pblk K.p data p c) u)) <$> ($ᵗ HashOutput : ProbComp HashOutput) := by
      rw [ordinaryStep, hparse p c]
      exact readOutside_fresh _ s (hfresh c)
    have hpairE : ∀ F : (DigestCall → HashOutput) → ℝ≥0∞,
        pairE F = ((Fintype.card HashOutput : ℝ≥0∞) ^ digestCalls)⁻¹ * ∑ u, F u := by
      intro F
      unfold pairE
      rw [tsum_uniform_eq, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    have hconv : ∀ G : HashOutput × State → ℝ≥0∞,
        ∑' r, Pr[= r | ordinaryStep model (pblk K.p data p c) s.known s] * G r =
          pairE (fun U => G (U c, withPair K.p data s p U)) := by
      intro G
      rw [hord, tsum_probOutput_map_mul, hpairE]
      exact presample_one hcalls (pblk K.p data p) c s (fun v s' => G (v, s'))
    rw [hconv, hconv, hconv]
    dsimp only
    have hnf : ∀ g : FIn, pblk K.p data p c ≠ g.input K.p := fun g => pblk_ne_fleaf K data p c g
    simp only [payC_not K data s _ hnf, excPay_not K data wbar Fail m s P Ms L d (b + 1) _ hnf,
      ghostP_withPair K data hp0 P, ghostMs_new K data hp0 Ms]
    have hrate : MsgLive L p.1 → Rate K.p data wbar s p.1 := fun hlive =>
      rate_of_fair hfair s p.1 (by have := hI.count p.1; omega) (le_trans (landedCount_le hI.pinv L hlive) hlen.le)
    unfold pairE
    refine combine_step ($ᵗ (DigestCall → HashOutput)) (tsum_probOutput_eq_one' probFailure_eq_zero)
      (fun U => payK K data.root s (.inl (.inr (.inl (pblk K.p data p c)))) (withPair K.p data s p U))
      (fun U => weightA K data.root (withPair K.p data s p U) *
        psiK K data wbar Fail Lmax T (withPair K.p data s p U) (addPair K.p P p U) (addMsg Ms p.1) L d b)
      (fun U => WK model K data.root (next (U c)) b (withPair K.p data s p U))
      (fun U => WC model K data.root (next (U c)) b (withPair K.p data s p U))
      (fun U => Xn (U c) b (withPair K.p data s p U) (addPair K.p P p U) (addMsg Ms p.1)) _ 0 0 cU ν
      (fun U _ => h (U c) b _ _ _ R (invK_withPair K data model Qtot hout hI hp0 U)) ?_
    calc _ ≤ ∑' U, Pr[= U | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
          (weightA K data.root s *
            psiK K data wbar Fail Lmax T (withPair K.p data s p U) (addPair K.p P p U) (addMsg Ms p.1) L d b) :=
          ENNReal.tsum_le_tsum fun U => mul_le_mul_right
            (core_newPair K data wbar Fail Lmax T model hout hw hI.pinv hI.dinv hI.jinv hI.len c hp0 U) _
      _ = weightA K data.root s * pairE (fun U =>
            psiK K data wbar Fail Lmax T (withPair K.p data s p U) (addPair K.p P p U) (addMsg Ms p.1) L d b) := by
          unfold pairE
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun U => by ring
      _ ≤ weightA K data.root s * psiK K data wbar Fail Lmax T s P Ms L d (b + 1) :=
          mul_le_mul_right (psiK_newPair K data wbar Fail Lmax T hw hI.pinv hI.minv hp0 L d b hrate) _
      _ = _ := by simp
  · have hgP : ∀ s' : State, ghostP K data s s' x P = P := fun s' => by
      unfold ghostP
      exact dif_neg hnew
    have hgM : ghostMs K data s x Ms = Ms := by
      unfold ghostMs
      exact dif_neg hnew
    simp only [hgP, hgM]
    refine combine_step (ordinaryStep model x s.known s) (by simp)
      (fun r => payK K data.root s (.inl (.inr (.inl x))) r.2)
      (fun r => weightA K data.root r.2 * psiK K data wbar Fail Lmax T r.2 P Ms L d b)
      (fun r => WK model K data.root (next r.1) b r.2) (fun r => WC model K data.root (next r.1) b r.2)
      (fun r => Xn r.1 b r.2 P Ms) _ _ _ cU ν
      (fun r hr => h r.1 b r.2 P Ms R (invK_ordinary K data model Qtot hout hI x hnew r hr)) ?_
    exact core_notNew K data wbar Fail Lmax T model cU m hout hcalls hw hcU hI.pinv hcells x hnew

omit hout in
/-- **The verifier's hash queries.** -/
theorem goodKC_liftHash (hcalls : digestCalls = 1)
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none)
    (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0)
    {Cmax : ℕ} (hfair : FairS wbar Cmax Lmax) (hQ : Qtot ≤ Cmax)
    (hcU : ν * ((signatureLimit : ℝ≥0∞) * revRate + m) ≤ cU)
    (L : QueryLog SigningSpec) (d : Multiset View) {β γ : Type} (comp : OracleComp HashSpec β) (g : β → γ) :
    GoodKC K data wbar Fail Lmax T model cU Qtot L d
      ((liftM comp : OracleComp CostSpec β) >>= fun v => pure (g v))
      (fun budget s P Ms => xsHash K data.root data wbar Fail model m comp L d budget s P Ms) := by
  induction comp using OracleComp.inductionOn with
  | pure value =>
      intro budget s P Ms R hI
      rw [liftM_pure, pure_bind]
      change acct model (payK K data.root) (pure (g value) : OracleComp CostSpec γ) budget s ≤ _
      rw [acct_pure]
      exact zero_le
  | query_bind q rest ih =>
      rw [liftM_bind, bind_assoc]
      exact goodKC_ordinary K data wbar Fail Lmax T model cU m Qtot hcalls hparse hout hfair hQ hcU L d q _
        (fun v budget s P Ms => xsHash K data.root data wbar Fail model m (rest v) L d budget s P Ms) ih

end Step

/-! ### The obligations `hhash` and `hpure` of `goodK_advProg` -/

section Obligations

variable (K : Ctx) (data : PublicData) (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Lmax T : ℕ)
  {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate) (cU m : ℝ≥0∞) (Qtot : ℕ)

/-- **O1 (`hhash` of `goodK_advProg`): one ordinary query of the adversary.** -/
theorem goodK_hash (hcalls : digestCalls = 1)
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none)
    (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0)
    {Cmax : ℕ} (hfair : FairS wbar Cmax Lmax) (hQ : Qtot ≤ Cmax)
    (hcU : ν * ((signatureLimit : ℝ≥0∞) * revRate + m) ≤ cU)
    (L : QueryLog SigningSpec) (x : HashInput) (next : HashOutput → OracleComp (OracleWorld + SigningSpec) Forgery)
    (h : ∀ v, GoodK K data wbar Fail Lmax T model cU m Qtot (next v) L) :
    GoodK K data wbar Fail Lmax T model cU m Qtot
      (liftM ((OracleWorld + SigningSpec).query (.inl (.inr x))) >>= next) L := by
  intro budget s P Ms d R hI
  rw [advProg_hash, XS_hash]
  exact goodKC_ordinary K data wbar Fail Lmax T model cU m Qtot hcalls hparse hout hfair hQ hcU L d x
    (fun v => advProg K.p data (next v) L)
    (fun v budget s P Ms => XS K data.root data wbar Fail model m (next v) L budget s P Ms d)
    (fun v budget s P Ms R hI => h v budget s P Ms d R hI) budget s P Ms R hI

/-- **O3 (`hpure` of `goodK_advProg`): the end of the game** (the verifier's hash queries). -/
theorem goodK_pure (hcalls : digestCalls = 1)
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none)
    (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0)
    {Cmax : ℕ} (hfair : FairS wbar Cmax Lmax) (hQ : Qtot ≤ Cmax)
    (hcU : ν * ((signatureLimit : ℝ≥0∞) * revRate + m) ≤ cU)
    (L : QueryLog SigningSpec) (forgery : Forgery) :
    GoodK K data wbar Fail Lmax T model cU m Qtot (pure forgery) L := by
  intro budget s P Ms d R hI
  rw [advProg_pure, XS_pure]
  unfold finishGame
  exact goodKC_liftHash K data wbar Fail Lmax T model cU m Qtot hcalls hparse hout hfair hQ hcU L d _
    (fun v => (forgery, L, v)) budget s P Ms R hI

end Obligations

end FORS.Security.SWRoute
