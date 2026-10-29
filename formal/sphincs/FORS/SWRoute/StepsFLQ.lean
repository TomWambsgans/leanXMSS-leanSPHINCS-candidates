import FORS.SWRoute.StepsHelp

/-! **The SW route: a FORS leaf query.** A fresh query whose secret is unknown records its guess;
its answer is a contact with chance `2^-128`. The contact survives (exponent `3`, and the query
pays the contact coefficient `cU`) when the cell is not a near cell and no contact exists yet;
otherwise it kills the weight, which the armed exponent pays. A fresh query whose secret is known
makes an unrecorded contact, which kills. Cached queries and canonical continuations change no
predicate. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost PotentialA GraphView ForsPotential

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

theorem meanD_mul' (c : ℝ≥0∞) (G : Digest → ℝ≥0∞) : meanD (fun t => c * G t) = c * meanD G := by
  simp only [meanD, ← Finset.mul_sum]
  ring

section FLQ

variable (K : Ctx) (root : Digest) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (ρ β δ cU : ℝ)

theorem weightA_eq_weight_of {s : St} (hb : ¬BadP K root s) : weightA K root s = weight K.tg K.initial s :=
  weightA_of_not_badR K root (fun h => hb (Or.inr h))

/-- **A fresh FORS leaf query with a guess.** -/
theorem step_flq_guess {total : ℕ} (hN : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (hH : StepHyp K model)
    (f : FIn) (s : St) (flag : Bool) (p r0 : ℕ) (hinv : InvS K s p) (hb : ¬BadP K root s)
    (hx : s.cache (f.input K.p) = none) (hk : s.known f.inC = none) (hle : p + r0 + 1 ≤ total) :
    StepBound K root model ρ β δ cU (flq K f) s flag p (r0 + 1) (p + 1) := by
  set x := f.input K.p with hxdef
  set s0 := s.record (f.inC, f.v) with hs0
  have hcs : costStep model (flq K f) s = readOutside x s0 := by
    rw [costStep_inl, lazyStep_guess model x s (Address.fleaf f.index f.κ f.leaf, f.v)
      (by rw [hH.parse]; exact parse_fleaf K f) (by rw [hH.incoming]; exact hk), hH.incoming]
    rfl
  have hx0 : s0.cache x = none := hx
  have hi : K.initial x = none := hH.fleaf f
  have hkind : K.tg.kind x = .none := hH.sec x (Or.inr ⟨f.index, f.κ, f.leaf, f.v, rfl⟩)
  have hM : ¬ForsSigner.IsMsgInput x := not_msg_fleaf K f
  have hw : weightA K root s = weight K.tg K.initial s := weightA_eq_weight_of K root hb
  have hp : (p : ℝ) < spaceReal := by have := sw_hp hN hle; linarith
  set W0 := weight K.tg K.initial s0 with hW0
  have hW0ge : probeFactor p * weightA K root s ≤ W0 := by
    rw [hw]; exact weight_record K.tg K.initial s (f.inC, f.v) hk (hinv.sat.finite _) p (hinv.sat.bound _) hp
  have hW0le : W0 ≤ weightA K root s := by
    rw [hw]; exact weight_le_of_extendsW K.tg K.initial (extends_record s _) rfl
  -- the state after the step
  have hsame : ∀ u, ∀ l, Retained K.p l → K.SameLeaf s (s0.store x u) l := fun u =>
    sameLeaf_store_fleaf K u hx0 hi rfl
  have hnear : ∀ u I κ L, NearLeaf K root (s0.store x u) I κ L ↔ NearLeaf K root s I κ L :=
    fun u => nearLeaf_store_of_not K root u hM
  have hknown : ∀ u c, (s0.store x u).known c = none ↔ s.known c = none := fun u c => Iff.rfl
  have hfck : ∀ u g, FCk K (s0.store x u) g ↔ FCk K s g ∨ (g = f ∧ truncateHash u = K.F f.outC) := by
    intro u g
    rw [fck_store K u hx0 hi g]
    constructor
    · rintro (h | ⟨hxg, ht⟩)
      · exact Or.inl h
      · have : g = f := fleaf_inj hxg.symm
        subst this
        exact Or.inr ⟨rfl, ht⟩
    · rintro (h | ⟨rfl, ht⟩)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, ht⟩
  have hweight : ∀ u, weight K.tg K.initial (s0.store x u) = W0 := fun u =>
    weight_store_untargetedW K.tg K.initial s0 x u hkind
  have hbr : ¬BadR K root s := fun h => hb (Or.inr h)
  have hpend : ∀ u, pendA K (s0.store x u) ≤ pendA K s := by
    intro u
    unfold pendA
    rw [wContact_congr (hsame u)]
    split_ifs
    · exact le_rfl
    · gcongr
      exact K.uaSet_store_of_not u hx0 hi fun l i _ hA => Ctx.isA_ne_fleaf hA f rfl
  have hP : ∀ u, weightA K root (s0.store x u) * pendA K (s0.store x u) ≤ weightA K root s * pendA K s + 0 := by
    intro u
    rw [add_zero]
    refine mul_le_mul' ?_ (hpend u)
    calc weightA K root (s0.store x u) ≤ weight K.tg K.initial (s0.store x u) := weightA_le_weight K root _
      _ = W0 := hweight u
      _ ≤ _ := hW0le
  set fl := nextFlag K root flag s (flq K f) with hfl
  set e0 := expo K ρ fl s with he0
  -- no contact: nothing changes but the weight factor
  have hnocontact : ∀ u, truncateHash u ≠ K.F f.outC →
      weightA K root (s0.store x u) = W0 ∧ expo K ρ fl (s0.store x u) = e0 := by
    intro u ht
    have hf' : ∀ g, FCk K (s0.store x u) g ↔ FCk K s g := fun g => by
      rw [hfck u g]
      exact ⟨fun h => h.resolve_right fun h' => ht h'.2, Or.inl⟩
    refine ⟨?_, expo_congr ρ fl (hsame u) hf'⟩
    rw [weightA_eq, hweight, if_neg (fun h => hbr ((badR_congr (hsame u) hf' (hnear u) (hknown u)).1 h))]
  -- a surviving contact: exponent 3
  have hcontact : ∀ u, truncateHash u = K.F f.outC → SurvivesAt K root s f →
      weightA K root (s0.store x u) = W0 ∧ expo K ρ fl (s0.store x u) = 3 := by
    intro u ht hsv
    obtain ⟨_, hnl, hnf, hnw⟩ := hsv
    have hFf : FCk K (s0.store x u) f := (hfck u f).2 (Or.inr ⟨rfl, ht⟩)
    have honly : ∀ g, FCk K (s0.store x u) g → g = f := fun g hg => by
      rcases (hfck u g).1 hg with h | ⟨rfl, -⟩
      · exact absurd ⟨g, h⟩ hnf
      · rfl
    have hW' : ¬WContact K (s0.store x u) := fun h => hnw ((wContact_congr (hsame u)).1 h)
    have hnot : ¬BadR K root (s0.store x u) := by
      rintro (hwb | hd | hn)
      · exact hbr (Or.inl ((wotsBad_congr (hsame u)).1 hwb))
      · rcases hd with ⟨l, i, v, l', i', v', hl, hl', h1, h2, hne⟩ | ⟨g, g', hne, h1, h2⟩ | ⟨hw', -⟩
        · refine hbr (Or.inr (Or.inl (Or.inl ⟨l, i, v, l', i', v', hl, hl', ?_, ?_, hne⟩)))
          · rwa [(hsame u l hl).1 i] at h1
          · rwa [(hsame u l' hl').1 i'] at h2
        · exact hne ((honly g h1).trans (honly g' h2).symm)
        · exact hW' hw'
      · obtain ⟨g, hg, hk' | hn'⟩ := hn
        · rw [honly g hg] at hk'
          exact hk' hk
        · rw [honly g hg] at hn'
          exact hnl ((hnear u _ _ _).1 hn')
    refine ⟨by rw [weightA_eq, hweight, if_neg hnot], ?_⟩
    unfold expo
    rw [if_pos (show ArmedS K fl (s0.store x u) from Or.inr (Or.inr ⟨f, hFf⟩)), if_neg hW',
      if_pos (show FContact K (s0.store x u) from ⟨f, hFf⟩)]
    norm_num
  have harm := arm_conv K root hN (flq K f) s flag p (r0 + 1) (by omega)
  set B : ℝ → ℝ≥0∞ := fun e => budgetE e (p + 1) r0 with hB
  have hfinB : ∀ e, probeFactor p * (ν * B e) ≠ ⊤ := fun e =>
    ENNReal.mul_ne_top (probeFactor_ne_top p) (ENNReal.mul_ne_top ν_ne_top ENNReal.ofReal_ne_top)
  by_cases hsv : SurvivesAt K root s f
  · -- the contact survives: E3 (unarmed) or the armed step `2 → 3`
    obtain ⟨_, hnl, hnf, hnw⟩ := hsv
    have hnm : ¬NearMiss K root s f := fun h => hnl h.1
    have hfl' : fl = flag := nextFlag_flq_of_not K root flag s f hnm
    set G : Digest → ℝ≥0∞ := fun t => if t = K.F f.outC then B 3 else B e0 with hG
    have hmean : meanD G + ν * B e0 = B e0 + ν * B 3 := meanD_two _ _ _
    have hR : budgetE e0 p (r0 + 1) + ENNReal.ofReal (cU / 2 ^ 128) + probeFactor p * (ν * B e0) ≤
        probeFactor p * meanD G + probeFactor p * (ν * B e0) := by
      rw [← mul_add, hmean]
      by_cases harmd : ArmedS K fl s
      · have he2 : e0 = 2 := by
          rw [he0]; unfold expo; rw [if_pos harmd, if_neg hnw, if_neg hnf]; norm_num
        have h4 := swR4 hN p r0 hle
        rw [nu_eq_ofReal'] at h4
        rw [he2]
        calc budgetE 2 p (r0 + 1) + ENNReal.ofReal (cU / 2 ^ 128) + probeFactor p * (ν * B 2)
            = budgetE 2 p (r0 + 1) + ENNReal.ofReal (cU / 2 ^ 128) + probeFactor p * ν * budgetE 2 (p + 1) r0 := by
              rw [mul_assoc]
          _ ≤ probeFactor p * budgetE 2 (p + 1) r0 + probeFactor p * ν * budgetE 3 (p + 1) r0 := h4
          _ = probeFactor p * (B 2 + ν * B 3) := by simp only [hB]; ring
      · have heρ : e0 = ρ := expo_unarmed K ρ harmd
        have h3 := swR3 hN p r0 hle
        rw [nu_eq_ofReal'] at h3
        rw [heρ]
        calc budgetE ρ p (r0 + 1) + ENNReal.ofReal (cU / 2 ^ 128) + probeFactor p * (ν * B ρ)
            = budgetE ρ p (r0 + 1) + ENNReal.ofReal (cU / 2 ^ 128) + probeFactor p * ν * budgetE ρ (p + 1) r0 := by
              rw [mul_assoc]
          _ ≤ probeFactor p * budgetE ρ (p + 1) r0 + probeFactor p * ν * budgetE 3 (p + 1) r0 := h3
          _ = probeFactor p * (B ρ + ν * B 3) := by simp only [hB]; ring
    refine stepBound_fresh K root model ρ β δ cU s s0 x hcs hx0 flag p r0 (p + 1)
      (budgetE e0 p (r0 + 1)) (ENNReal.ofReal (cU / 2 ^ 128)) 0 harm ?_ hP ?_
    · rw [payF_flq K root hH.digest, payC_flq, if_pos ⟨hk, hnl, hnf, hnw⟩, mul_zero, zero_add]
    · rw [add_zero]
      refine le_trans (finish_guess hW0ge hR (hfinB e0)) ?_
      rw [← meanD_mul']
      refine meanD_le_of_pointwise _ _ fun u => ?_
      simp only [hG]
      by_cases ht : truncateHash u = K.F f.outC
      · rw [if_pos ht]
        obtain ⟨h1, h2⟩ := hcontact u ht ⟨hk, hnl, hnf, hnw⟩
        rw [h1, h2, mul_comm]
      · rw [if_neg ht]
        obtain ⟨h1, h2⟩ := hnocontact u ht
        rw [h1, h2, mul_comm]
  · -- the contact kills: the state is armed
    have harmd : ArmedS K fl s := by
      by_contra hna
      apply hsv
      refine ⟨hk, fun hnl => ?_, fun hf => hna (Or.inr (Or.inr hf)), fun hwc => hna (Or.inr (Or.inl ?_))⟩
      · have : fl = true := nextFlag_flq_of_nearMiss K root flag s f ⟨hnl, hk⟩
        exact hna (Or.inl this)
      · obtain ⟨l, i, hl, hc⟩ := hwc
        exact ⟨l, hl, Or.inr ⟨i, hc⟩⟩
    have he2 : 2 ≤ e0 := expo_ge_two K root ρ harmd hb
    set G : Digest → ℝ≥0∞ := fun t => if t = K.F f.outC then 0 else B e0 with hG
    have hmean : meanD G + ν * B e0 = B e0 + ν * 0 := meanD_two _ _ _
    rw [mul_zero, add_zero] at hmean
    have hR : budgetE e0 p (r0 + 1) + 0 + probeFactor p * (ν * B e0) ≤
        probeFactor p * meanD G + probeFactor p * (ν * B e0) := by
      rw [← mul_add, hmean, add_zero, ← mul_assoc]
      exact kill_guess hN hle he2
    refine stepBound_fresh K root model ρ β δ cU s s0 x hcs hx0 flag p r0 (p + 1)
      (budgetE e0 p (r0 + 1)) 0 0 harm ?_ hP ?_
    · rw [payF_flq K root hH.digest, payC_flq, if_neg hsv]
      simp
    · rw [add_zero]
      refine le_trans (finish_guess hW0ge hR (hfinB e0)) ?_
      rw [← meanD_mul']
      refine meanD_le_of_pointwise _ _ fun u => ?_
      simp only [hG]
      by_cases ht : truncateHash u = K.F f.outC
      · rw [if_pos ht, mul_zero]
        exact bot_le
      · rw [if_neg ht]
        obtain ⟨h1, h2⟩ := hnocontact u ht
        rw [h1, h2, mul_comm]

end FLQ

end FORS.Security.SWRoute
