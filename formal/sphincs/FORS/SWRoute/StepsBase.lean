import FORS.SWRoute.State

/-! **The SW route: basic facts of its state.** The bad set only grows along the run, so the weight
`weightA` is at most the survival weight and a supermartingale of every step; a fresh digest block
does not raise it. The invariant `InvS` of the route's steps (the saturation invariant, the small
route's invariant, the FORS leaf values known, the pending inputs counted by the probes), and the
combinator that chains one step with the rest of the run. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost PotentialA GraphView ForsPotential

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

section Mono

variable (K : Ctx) (root : Digest)

variable {K} in
theorem fr_mono {s s' : St} (h : Extends s s') {x : HashInput} {u : HashOutput} (hf : K.Fr s x u) :
    K.Fr s' x u := ⟨h.1 x u hf.1, hf.2⟩

variable {K} in
theorem contactB_mono {s s' : St} (h : Extends s s') (l : OtsKey) (i : ChainIndex) :
    K.ContactB s l i ⊆ K.ContactB s' l i := by
  rintro v ⟨x, u, hB, hf, ht⟩
  exact ⟨x, u, hB, fr_mono h hf, ht⟩

variable {K} in
theorem aAns_mono {s s' : St} (h : Extends s s') (l : OtsKey) (i : ChainIndex) :
    K.AAns s l i ⊆ K.AAns s' l i := by
  rintro t ⟨x, u, hA, hf, ht⟩
  exact ⟨x, u, hA, fr_mono h hf, ht⟩

variable {K} in
theorem marker_mono {s s' : St} (h : Extends s s') {l : OtsKey} {i : ChainIndex} (hm : K.Marker s l i) :
    K.Marker s' l i := by
  obtain ⟨msg, ctr, u, hf, ht⟩ := hm
  exact ⟨msg, ctr, u, fr_mono h hf, ht⟩

variable {K} in
theorem badLeaf_mono {s s' : St} (h : Extends s s') {l : OtsKey} (hb : K.BadLeaf s l) : K.BadLeaf s' l := by
  rcases hb with ⟨i, v, hv⟩ | ⟨i, hc, hm⟩ | ⟨i, i', hne, hc, hc'⟩
  · exact Or.inl ⟨i, v, contactB_mono h l i hv.1, aAns_mono h l i hv.2⟩
  · exact Or.inr (Or.inl ⟨i, hc.mono (contactB_mono h l i), marker_mono h hm⟩)
  · exact Or.inr (Or.inr ⟨i, i', hne, hc.mono (contactB_mono h l i), hc'.mono (contactB_mono h l i')⟩)

variable {K} in
theorem wotsBad_mono {s s' : St} (h : Extends s s') (hb : K.WotsBad s) : K.WotsBad s' := by
  obtain ⟨l, hl, hb⟩ := hb
  exact ⟨l, hl, badLeaf_mono h hb⟩

variable {K} in
theorem fck_mono {s s' : St} (h : Extends s s') {f : FIn} (hf : FCk K s f) : FCk K s' f := by
  obtain ⟨u, hfr, ht⟩ := hf
  exact ⟨u, fr_mono h hfr, ht⟩

variable {K} in
theorem wContact_mono {s s' : St} (h : Extends s s') (hw : WContact K s) : WContact K s' := by
  obtain ⟨l, i, hl, hc⟩ := hw
  exact ⟨l, i, hl, hc.mono (contactB_mono h l i)⟩

variable {K} in
theorem fContact_mono {s s' : St} (h : Extends s s') (hf : FContact K s) : FContact K s' := by
  obtain ⟨f, hf⟩ := hf
  exact ⟨f, fck_mono h hf⟩

variable {K} in
theorem armedW_mono {s s' : St} (h : Extends s s') (ha : ArmedW K s) : ArmedW K s' := by
  obtain ⟨l, hl, ⟨i, hm⟩ | ⟨i, hc⟩⟩ := ha
  · exact ⟨l, hl, Or.inl ⟨i, marker_mono h hm⟩⟩
  · exact ⟨l, hl, Or.inr ⟨i, hc.mono (contactB_mono h l i)⟩⟩

variable {K} in
theorem dead_mono {s s' : St} (h : Extends s s') (hd : Dead K s) : Dead K s' := by
  rcases hd with ⟨l, i, v, l', i', v', hl, hl', hv, hv', hne⟩ | ⟨f, g, hne, hf, hg⟩ | ⟨hw, hf⟩
  · exact Or.inl ⟨l, i, v, l', i', v', hl, hl', contactB_mono h l i hv, contactB_mono h l' i' hv', hne⟩
  · exact Or.inr (Or.inl ⟨f, g, hne, fck_mono h hf, fck_mono h hg⟩)
  · exact Or.inr (Or.inr ⟨wContact_mono h hw, fContact_mono h hf⟩)

variable {K root} in
theorem nearLeaf_mono {s s' : St} (h : Extends s s') {index : Index} {κ : FTree} {leaf : FLeaf}
    (hn : NearLeaf K root s index κ leaf) : NearLeaf K root s' index κ leaf := by
  obtain ⟨m, rr, d, hd, hl, hi, hlf, hk⟩ := hn
  refine ⟨m, rr, d, cachedDigest_mono h hd, hl, hi, hlf, fun κ' hκ' => ?_⟩
  intro hnone
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hk κ' hκ')
  rw [h.2.1 _ _ hv] at hnone
  cases hnone

variable {K root} in
theorem nearContact_mono {s s' : St} (h : Extends s s') (hn : NearContact K root s) :
    NearContact K root s' := by
  obtain ⟨f, hf, hk | hn⟩ := hn
  · refine ⟨f, fck_mono h hf, Or.inl fun hnone => ?_⟩
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hk
    rw [h.2.1 _ _ hv] at hnone
    cases hnone
  · exact ⟨f, fck_mono h hf, Or.inr (nearLeaf_mono h hn)⟩

variable {K root} in
/-- **The bad set grows along the run.** -/
theorem badP_mono {s s' : St} (h : Extends s s') (hb : BadP K root s) : BadP K root s' := by
  rcases hb with hr | hw | hd | hn
  · exact Or.inl (realized_of_extends K.tg K.initial h hr)
  · exact Or.inr (Or.inl (wotsBad_mono h hw))
  · exact Or.inr (Or.inr (Or.inl (dead_mono h hd)))
  · exact Or.inr (Or.inr (Or.inr (nearContact_mono h hn)))

end Mono

/-! ### The weight -/

section Weight

variable (K : Ctx) (root : Digest)

/-- The bad set without the decided first-order hits. -/
def BadR (s : St) : Prop := K.WotsBad s ∨ Dead K s ∨ NearContact K root s

theorem badP_iff (s : St) : BadP K root s ↔ Realized K.tg K.initial s ∨ BadR K root s := Iff.rfl

variable {K root} in
theorem badR_mono {s s' : St} (h : Extends s s') (hb : BadR K root s) : BadR K root s' := by
  rcases hb with hw | hd | hn
  · exact Or.inl (wotsBad_mono h hw)
  · exact Or.inr (Or.inl (dead_mono h hd))
  · exact Or.inr (Or.inr (nearContact_mono h hn))

theorem weightA_eq (s : St) :
    weightA K root s = if BadR K root s then 0 else weight K.tg K.initial s := by
  unfold weightA weight
  by_cases hr : Realized K.tg K.initial s
  · have : BadP K root s := Or.inl hr
    simp [this, hr]
  · by_cases hb : BadR K root s
    · have : BadP K root s := Or.inr hb
      simp [this, hb]
    · have : ¬BadP K root s := fun h => h.elim hr hb
      simp [this, hb, hr]

theorem weightA_le_weight (s : St) : weightA K root s ≤ weight K.tg K.initial s := by
  rw [weightA_eq]
  split_ifs
  · exact bot_le
  · exact le_rfl

theorem weightA_le_one (s : St) : weightA K root s ≤ 1 :=
  (weightA_le_weight K root s).trans (weight_le_one K.tg K.initial s)

theorem weightA_ne_top (s : St) : weightA K root s ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (weightA_le_one K root s)

theorem weightA_of_badP {s : St} (h : BadP K root s) : weightA K root s = 0 := by
  rw [weightA, if_pos h]

theorem weightA_of_not_badR {s : St} (h : ¬BadR K root s) : weightA K root s = weight K.tg K.initial s := by
  rw [weightA_eq, if_neg h]

variable {K root} in
theorem weightA_le_of_extends {s s' : St} (h : Extends s s') (hknown : s'.known = s.known) :
    weightA K root s' ≤ weightA K root s := by
  by_cases hb : BadR K root s
  · rw [weightA_eq, if_pos (badR_mono h hb)]
    exact bot_le
  · rw [weightA_of_not_badR K root hb]
    exact (weightA_le_weight K root s').trans (weight_le_of_extendsW K.tg K.initial h hknown)

/-- **The weight is a supermartingale of every step** (no invariant needed). -/
theorem weightA_step_le {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)
    (input : CostSpec.Domain) (s : St) :
    ∑' r, Pr[= r | costStep model input s] * weightA K root r.2 ≤ weightA K root s := by
  by_cases hb : BadR K root s
  · have hz : ∀ r ∈ support (costStep model input s), weightA K root r.2 = 0 := fun r hr => by
      rw [weightA_eq, if_pos (badR_mono (extends_costStep model input s r hr) hb)]
    calc ∑' r, Pr[= r | costStep model input s] * weightA K root r.2
        = ∑' r, Pr[= r | costStep model input s] * 0 := by
          refine tsum_congr fun r => ?_
          by_cases hr : r ∈ support (costStep model input s)
          · rw [hz r hr]
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ ≤ _ := by simp
  · rw [weightA_of_not_badR K root hb]
    calc ∑' r, Pr[= r | costStep model input s] * weightA K root r.2
        ≤ ∑' r, Pr[= r | costStep model input s] * weight K.tg K.initial r.2 :=
          ENNReal.tsum_le_tsum fun r => mul_le_mul_right (weightA_le_weight K root r.2) _
      _ ≤ _ := meanWeight_costStep_leW K.tg K.initial model input s

/-- **A fresh untargeted store does not raise the weight** (in particular a fresh digest block). -/
theorem weightA_store_le_of_untargeted (s : St) (x : HashInput) (u : HashOutput) (hx : s.cache x = none)
    (hk : K.tg.kind x = .none) : weightA K root (s.store x u) ≤ weightA K root s := by
  by_cases hb : BadR K root s
  · rw [weightA_eq, if_pos (badR_mono (extends_store s x u hx) hb)]
    exact bot_le
  · rw [weightA_of_not_badR K root hb]
    exact (weightA_le_weight K root _).trans (le_of_eq (weight_store_untargetedW K.tg K.initial s x u hk))

/-- The weight at a digest block: `WtSpec.store_le` for the weighted potentials (fresh blocks). -/
theorem weightA_store_digest_le (hmsg : ∀ x, ForsSigner.IsMsgInput x → K.tg.kind x = .none) (s : St)
    (x : HashInput) (u : HashOutput) (hx : s.cache x = none) (hd : ForsSigner.IsMsgInput x) :
    weightA K root (s.store x u) ≤ weightA K root s :=
  weightA_store_le_of_untargeted K root s x u hx (hmsg x hd)

/-- The weight times the pending credit is finite. -/
theorem pendA_le (s : St) : pendA K s ≤ ν / 2 * ((K.UAset s).encard : ℝ≥0∞) := by
  unfold pendA
  split_ifs
  · exact bot_le
  · exact le_rfl

end Weight

/-! ### The weight before the completed contacts -/

section WeightB

variable (K : Ctx) (root : Digest)

/-- The part of `BadQ` that reads the cache only. -/
def BadW (s : St) : Prop := K.WotsBad s ∨ Dead K s

variable {K} in
theorem badW_mono {s s' : St} (h : Extends s s') (hb : BadW K s) : BadW K s' := by
  rcases hb with hw | hd
  · exact Or.inl (wotsBad_mono h hw)
  · exact Or.inr (dead_mono h hd)

theorem weightB_eq (s : St) : weightB K s = if BadW K s then 0 else weight K.tg K.initial s := by
  unfold weightB weight BadQ BadW
  by_cases hr : Realized K.tg K.initial s
  · simp [hr]
  · by_cases hb : K.WotsBad s ∨ Dead K s
    · simp [hb]
    · simp only [hr, false_or, hb, if_false]

theorem weightA_eq_weightB (s : St) :
    weightA K root s = if NearContact K root s then 0 else weightB K s := by
  unfold weightA weightB BadP BadQ
  by_cases hn : NearContact K root s
  · simp [hn]
  · simp only [hn, if_false, or_false]
    split_ifs <;> rfl

theorem weightB_le_weight (s : St) : weightB K s ≤ weight K.tg K.initial s := by
  rw [weightB_eq]
  split_ifs
  · exact bot_le
  · exact le_rfl

theorem weightB_le_one (s : St) : weightB K s ≤ 1 :=
  (weightB_le_weight K s).trans (weight_le_one K.tg K.initial s)

theorem weightA_le_weightB (s : St) : weightA K root s ≤ weightB K s := by
  rw [weightA_eq_weightB]
  split_ifs
  · exact bot_le
  · exact le_rfl

/-- `weightB` is a supermartingale of every step. -/
theorem weightB_step_le {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)
    (input : CostSpec.Domain) (s : St) :
    ∑' r, Pr[= r | costStep model input s] * weightB K r.2 ≤ weightB K s := by
  by_cases hb : BadW K s
  · have hz : ∀ r ∈ support (costStep model input s), weightB K r.2 = 0 := fun r hr => by
      rw [weightB_eq, if_pos (badW_mono (extends_costStep model input s r hr) hb)]
    calc ∑' r, Pr[= r | costStep model input s] * weightB K r.2
        = ∑' r, Pr[= r | costStep model input s] * 0 := by
          refine tsum_congr fun r => ?_
          by_cases hr : r ∈ support (costStep model input s)
          · rw [hz r hr]
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ ≤ _ := by simp
  · rw [weightB_eq K s, if_neg hb]
    calc ∑' r, Pr[= r | costStep model input s] * weightB K r.2
        ≤ ∑' r, Pr[= r | costStep model input s] * weight K.tg K.initial r.2 :=
          ENNReal.tsum_le_tsum fun r => mul_le_mul_right (weightB_le_weight K r.2) _
      _ ≤ _ := meanWeight_costStep_leW K.tg K.initial model input s

/-- A fresh untargeted store does not raise `weightB`. -/
theorem weightB_store_le_of_untargeted (s : St) (x : HashInput) (u : HashOutput) (hx : s.cache x = none)
    (hk : K.tg.kind x = .none) : weightB K (s.store x u) ≤ weightB K s := by
  by_cases hb : BadW K s
  · rw [weightB_eq, if_pos (badW_mono (extends_store s x u hx) hb)]
    exact bot_le
  · rw [weightB_eq K s, if_neg hb]
    exact (weightB_le_weight K _).trans (le_of_eq (weight_store_untargetedW K.tg K.initial s x u hk))

/-- `weightB` at a fresh digest block (`WtSpec.store_le`). -/
theorem weightB_store_digest_le (hmsg : ∀ x, ForsSigner.IsMsgInput x → K.tg.kind x = .none) (s : St)
    (x : HashInput) (u : HashOutput) (hx : s.cache x = none) (hd : ForsSigner.IsMsgInput x) :
    weightB K (s.store x u) ≤ weightB K s :=
  weightB_store_le_of_untargeted K s x u hx (hmsg x hd)

theorem badW_expose (s : St) (c : Coordinate) (v : Digest) : BadW K (s.expose c v) ↔ BadW K s := Iff.rfl

/-- **Exact mean of `weightB` at an exposure.** -/
theorem weightB_expose_mean (s : St) (c : Coordinate) (hc : s.known c = none) :
    ∑' v, Pr[= v | ($ᵗ Digest : ProbComp Digest)] * weightB K (s.expose c v) = weightB K s := by
  by_cases hb : BadW K s
  · have hz : ∀ v, weightB K (s.expose c v) = 0 := fun v => by
      rw [weightB_eq, if_pos ((badW_expose K s c v).2 hb)]
    simp only [hz, mul_zero, tsum_zero]
    rw [weightB_eq, if_pos hb]
  · have he : ∀ v, weightB K (s.expose c v) = weight K.tg K.initial (s.expose c v) := fun v => by
      rw [weightB_eq, if_neg (fun h => hb ((badW_expose K s c v).1 h))]
    simp only [he]
    rw [weightB_eq K s, if_neg hb]
    exact weight_expose_mean K.tg K.initial s c hc (Set.toFinite _)

/-- **Exact mean of `weightB` at a reveal step.** -/
theorem weightB_sample_mean (c : Coordinate) (s : St) :
    ∑' r, Pr[= r | sampleCoordinate c s] * weightB K r.2 = weightB K s := by
  cases hc : s.known c with
  | some v => rw [sampleCoordinate_known c s v hc, tsum_probOutput_pure_mul]
  | none =>
      rw [sampleCoordinate_unknown c s hc, tsum_probOutput_map_mul]
      exact weightB_expose_mean K s c hc

end WeightB

/-! ### The invariant of the route -/

section Inv

variable (K : Ctx) (root : Digest)

/-- **The invariant of the route** after `probes` hazardous steps. -/
structure InvS (s : St) (probes : ℕ) : Prop where
  sat : HiddenDebt.Inv K.tg K.initial s probes
  lin : K.Inv s
  leaf : ∀ f : FIn, s.known f.outC = some (K.F f.outC)
  ua : (K.UAset s).encard ≤ probes

variable {K} in
theorem pendA_ne_top {s : St} {probes : ℕ} (h : InvS K s probes) : pendA K s ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (pendA_le K s)
  refine ENNReal.mul_ne_top (ENNReal.div_ne_top ν_ne_top (by norm_num)) ?_
  refine ne_top_of_le_ne_top (ENNReal.natCast_ne_top probes) ?_
  exact_mod_cast h.ua

end Inv

/-! ### Chaining one step with the rest of the run -/

/-- **The step combinator** of the S-part: the step bound `a + b + E X ≤ E Y + c` and, at every
outcome, the bound of the rest `Y + Z + U ≤ V + X + W`, give the bound of the whole, once `E X` is
finite (`X` is the weight times the pending credit after the step). -/
theorem combineS {β : Type} (step : ProbComp β) (a b c : ℝ≥0∞) (X Y Z U V W : β → ℝ≥0∞)
    (hstep : a + b + ∑' x, Pr[= x | step] * X x ≤ ∑' x, Pr[= x | step] * Y x + c)
    (hih : ∀ x ∈ support step, Y x + Z x + U x ≤ V x + X x + W x)
    (hfin : ∑' x, Pr[= x | step] * X x ≠ ⊤) :
    a + b + ∑' x, Pr[= x | step] * Z x + ∑' x, Pr[= x | step] * U x ≤
      ∑' x, Pr[= x | step] * V x + c + ∑' x, Pr[= x | step] * W x := by
  have hpt : ∀ x, Pr[= x | step] * (Y x + Z x + U x) ≤ Pr[= x | step] * (V x + X x + W x) := by
    intro x
    by_cases hx : x ∈ support step
    · exact mul_le_mul_right (hih x hx) _
    · rw [probOutput_eq_zero_of_not_mem_support hx, zero_mul, zero_mul]
  have hsum : ∑' x, Pr[= x | step] * Y x + ∑' x, Pr[= x | step] * Z x + ∑' x, Pr[= x | step] * U x ≤
      ∑' x, Pr[= x | step] * V x + ∑' x, Pr[= x | step] * X x + ∑' x, Pr[= x | step] * W x := by
    simp only [← ENNReal.tsum_add, ← mul_add]
    exact ENNReal.tsum_le_tsum hpt
  set EX := ∑' x, Pr[= x | step] * X x
  set EY := ∑' x, Pr[= x | step] * Y x
  set EZ := ∑' x, Pr[= x | step] * Z x
  set EU := ∑' x, Pr[= x | step] * U x
  set EV := ∑' x, Pr[= x | step] * V x
  set EW := ∑' x, Pr[= x | step] * W x
  have key : a + b + EZ + EU + EX ≤ EV + c + EW + EX :=
    calc a + b + EZ + EU + EX = (a + b + EX) + EZ + EU := by ring
      _ ≤ (EY + c) + EZ + EU := by gcongr
      _ = (EY + EZ + EU) + c := by ring
      _ ≤ (EV + EX + EW) + c := by gcongr
      _ = EV + c + EW + EX := by ring
  exact (ENNReal.add_le_add_iff_right hfin).1 key

end FORS.Security.SWRoute
