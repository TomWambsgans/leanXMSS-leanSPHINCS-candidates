import FORS.SWRoute.StepsFLQ

/-! **The SW route: chain steps below the word.** A fresh chain query of a retained key below its
prepared word, with or without a guess (the factor `g`, at least the probe factor): two steps below
the word its answer adds half a unit of pending credit and completes a two-edge event only against
an existing contact; one step below the word it is a contact with chance `2^-128` (exponent `66`
when it survives, a kill otherwise); further below it has no event. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost PotentialA GraphView ForsPotential

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### Congruence from the contacts and markers alone -/

section Congr'

variable {K : Ctx}

theorem wContact_congr' {s s' : St} (hc : ∀ l i, Retained K.p l → K.ContactB s' l i = K.ContactB s l i) :
    WContact K s' ↔ WContact K s := by
  unfold WContact
  constructor
  · rintro ⟨l, i, hl, h⟩
    exact ⟨l, i, hl, by rwa [hc l i hl] at h⟩
  · rintro ⟨l, i, hl, h⟩
    exact ⟨l, i, hl, by rwa [hc l i hl]⟩

theorem armedW_congr' {s s' : St} (hc : ∀ l i, Retained K.p l → K.ContactB s' l i = K.ContactB s l i)
    (hm : ∀ l i, Retained K.p l → (K.Marker s' l i ↔ K.Marker s l i)) : ArmedW K s' ↔ ArmedW K s := by
  unfold ArmedW
  constructor
  · rintro ⟨l, hl, ⟨i, h⟩ | ⟨i, h⟩⟩
    · exact ⟨l, hl, Or.inl ⟨i, (hm l i hl).1 h⟩⟩
    · exact ⟨l, hl, Or.inr ⟨i, by rwa [hc l i hl] at h⟩⟩
  · rintro ⟨l, hl, ⟨i, h⟩ | ⟨i, h⟩⟩
    · exact ⟨l, hl, Or.inl ⟨i, (hm l i hl).2 h⟩⟩
    · exact ⟨l, hl, Or.inr ⟨i, by rwa [hc l i hl]⟩⟩

theorem dead_congr' {s s' : St} (hc : ∀ l i, Retained K.p l → K.ContactB s' l i = K.ContactB s l i)
    (hf : ∀ f, FCk K s' f ↔ FCk K s f) : Dead K s' ↔ Dead K s := by
  unfold Dead
  rw [wContact_congr' hc, fContact_congr hf]
  have hcb : ∀ (l : OtsKey) (i : ChainIndex) (v : Digest), Retained K.p l →
      (v ∈ K.ContactB s' l i ↔ v ∈ K.ContactB s l i) := fun l i v hl => by rw [hc l i hl]
  constructor
  · rintro (⟨l, i, v, l', i', v', hl, hl', h1, h2, hne⟩ | ⟨f, g, hne, h1, h2⟩ | h3)
    · exact Or.inl ⟨l, i, v, l', i', v', hl, hl', (hcb l i v hl).1 h1, (hcb l' i' v' hl').1 h2, hne⟩
    · exact Or.inr (Or.inl ⟨f, g, hne, (hf f).1 h1, (hf g).1 h2⟩)
    · exact Or.inr (Or.inr h3)
  · rintro (⟨l, i, v, l', i', v', hl, hl', h1, h2, hne⟩ | ⟨f, g, hne, h1, h2⟩ | h3)
    · exact Or.inl ⟨l, i, v, l', i', v', hl, hl', (hcb l i v hl).2 h1, (hcb l' i' v' hl').2 h2, hne⟩
    · exact Or.inr (Or.inl ⟨f, g, hne, (hf f).2 h1, (hf g).2 h2⟩)
    · exact Or.inr (Or.inr h3)

theorem expo_congr' (ρ : ℝ) (flag : Bool) {s s' : St}
    (hc : ∀ l i, Retained K.p l → K.ContactB s' l i = K.ContactB s l i)
    (hm : ∀ l i, Retained K.p l → (K.Marker s' l i ↔ K.Marker s l i))
    (hf : ∀ f, FCk K s' f ↔ FCk K s f) : expo K ρ flag s' = expo K ρ flag s := by
  unfold expo ArmedS
  rw [armedW_congr' hc hm, fContact_congr hf, wContact_congr' hc]

end Congr'

/-! ### Means over a set of at most one value -/

theorem meanD_compl_ge (S : Set Digest) (hS : S.encard ≤ 1) (b : ℝ≥0∞) :
    b ≤ meanD (fun t => if t ∈ S then 0 else b) + ν * b := by
  rcases Set.encard_le_one_iff_eq.1 hS with rfl | ⟨v, rfl⟩
  · simp only [Set.mem_empty_iff_false, if_false, meanD_const]
    exact le_self_add
  · have h := meanD_two v 0 b
    simp only [Set.mem_singleton_iff]
    rw [h, mul_zero, add_zero]

/-- Under no dead state, a chain of a retained key has at most one contact. -/
theorem contactB_encard_le {K : Ctx} {root : Digest} {s : St} (hb : ¬BadP K root s) {l : OtsKey}
    (hl : Retained K.p l) (i : ChainIndex) : (K.ContactB s l i).encard ≤ 1 := by
  rw [Set.encard_le_one_iff]
  intro a b ha hb'
  by_contra hne
  exact hb (Or.inr (Or.inr (Or.inl (Or.inl ⟨l, i, a, l, i, b, hl, hl, ha, hb', fun h => hne (by
    simp only [Prod.mk.injEq] at h; exact h.2.2)⟩))))

/-! ### The store of a chain input -/

section ChainStore

variable (K : Ctx) {s : St} {x : HashInput} (u : HashOutput)

theorem contactB_store_of_notB (hx : s.cache x = none) (hi : K.initial x = none)
    (hB : ∀ l i v, ¬K.IsB l i v x) (l : OtsKey) (i : ChainIndex) :
    K.ContactB (s.store x u) l i = K.ContactB s l i := by
  rw [K.contactB_store u hx hi]
  exact Set.union_eq_left.2 fun v hv => absurd hv.1 (hB l i v)

theorem marker_store_of_notE (hx : s.cache x = none) (hi : K.initial x = none)
    (hE : ∀ (l : OtsKey) msg ctr, x ≠ Wots.encodingInput K.p l.1 l.2.1 l.2.2 msg ctr) (l : OtsKey) (i : ChainIndex) :
    K.Marker (s.store x u) l i ↔ K.Marker s l i := by
  rw [K.marker_store u hx hi]
  exact ⟨fun h => h.resolve_right fun ⟨⟨msg, ctr, he⟩, _⟩ => hE l msg ctr he, Or.inl⟩

/-- A store two steps below the word completes a WOTS event only against an existing contact. -/
theorem badLeaf_store_A (hx : s.cache x = none) (hi : K.initial x = none) {l : OtsKey} {i : ChainIndex}
    (hA : K.IsA l i x) (l' : OtsKey) (hbad : K.BadLeaf (s.store x u) l') :
    K.BadLeaf s l' ∨ truncateHash u ∈ K.ContactB s l i := by
  have hB : ∀ l i v, ¬K.IsB l i v x := fun l' i' v' hB' => Ctx.isA_not_isB hA hB'
  have hE : ∀ (l : OtsKey) msg ctr, x ≠ Wots.encodingInput K.p l.1 l.2.1 l.2.2 msg ctr :=
    fun l' msg ctr => Ctx.isA_ne_enc hA l' msg ctr
  have hc := contactB_store_of_notB K u hx hi hB
  have hm := marker_store_of_notE K u hx hi hE
  rcases hbad with ⟨i', v', hv1, hv2⟩ | ⟨i', hc', hm'⟩ | ⟨i', i'', hne, hc1, hc2⟩
  · rw [hc] at hv1
    rw [K.aAns_store u hx hi] at hv2
    split_ifs at hv2 with hA'
    · obtain ⟨rfl, rfl⟩ := Ctx.isA_unique hA' hA
      rcases Set.mem_insert_iff.1 hv2 with rfl | hv2
      · exact Or.inr hv1
      · exact Or.inl (Or.inl ⟨i', v', hv1, hv2⟩)
    · exact Or.inl (Or.inl ⟨i', v', hv1, hv2⟩)
  · rw [hc] at hc'
    exact Or.inl (Or.inr (Or.inl ⟨i', hc', (hm l' i').1 hm'⟩))
  · rw [hc] at hc1 hc2
    exact Or.inl (Or.inr (Or.inr ⟨i', i'', hne, hc1, hc2⟩))

end ChainStore

/-! ### Two steps below the word -/

section ChainA

variable (K : Ctx) (root : Digest) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (ρ β δ cU : ℝ)

/-- **A fresh chain query two steps below the word**, with the guess factor `g`. -/
theorem step_chainA {total : ℕ} (hN : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (hH : StepHyp K model)
    (s : St) (flag : Bool) (p r0 : ℕ) (hinv : InvS K s p) (hb : ¬BadP K root s)
    {l : OtsKey} (hl : Retained K.p l) {i : ChainIndex} {x : HashInput} (hA : K.IsA l i x) (hx : s.cache x = none)
    (gs : List (Coordinate × Digest))
    (hcs : costStep model (.inl (.inr (.inl x))) s = readOutside x { s with guesses := gs })
    (g : ℝ≥0∞) (hW0ge : g * weightA K root s ≤ weight K.tg K.initial { s with guesses := gs })
    (hW0le : weight K.tg K.initial { s with guesses := gs } ≤ weightA K root s)
    (hgpf : probeFactor p ≤ g) (hgtop : g ≠ ⊤) (hle : p + r0 + 1 ≤ total) :
    StepBound K root model ρ β δ cU (.inl (.inr (.inl x))) s flag p (r0 + 1) (p + 1) := by
  set s0 : St := { s with guesses := gs } with hs0
  have hx0 : s0.cache x = none := hx
  have hi : K.initial x = none := initial_none_of_fresh K.initial s hinv.sat.prepared x hx
  have hkind : K.tg.kind x = .none := hH.sec x (K.secondOrder_of_isA hA)
  have hM : ¬ForsSigner.IsMsgInput x := by
    obtain ⟨st, pay, -, rfl⟩ := hA
    exact fun h => msg_ne_chain h rfl
  have hnF : ∀ f : FIn, x ≠ f.input K.p := fun f => Ctx.isA_ne_fleaf hA f
  have hnQ : ¬IsFLQ K (.inl (.inr (.inl x))) := fun h => by
    obtain ⟨f, hf⟩ := (isFLQ_ordinary_iff K x).1 h
    exact hnF f hf
  have hB : ∀ l i v, ¬K.IsB l i v x := fun l' i' v' hB' => Ctx.isA_not_isB hA hB'
  have hE : ∀ (l : OtsKey) msg ctr, x ≠ Wots.encodingInput K.p l.1 l.2.1 l.2.2 msg ctr :=
    fun l' msg ctr => Ctx.isA_ne_enc hA l' msg ctr
  set W0 := weight K.tg K.initial s0 with hW0
  have hweight : ∀ u, weight K.tg K.initial (s0.store x u) = W0 := fun u =>
    weight_store_untargetedW K.tg K.initial s0 x u hkind
  have hc : ∀ u l' i', Retained K.p l' → K.ContactB (s0.store x u) l' i' = K.ContactB s l' i' :=
    fun u l' i' _ => contactB_store_of_notB K u hx0 hi hB l' i'
  have hm : ∀ u l' i', Retained K.p l' → (K.Marker (s0.store x u) l' i' ↔ K.Marker s l' i') :=
    fun u l' i' _ => marker_store_of_notE K u hx0 hi hE l' i'
  have hfck : ∀ u f, FCk K (s0.store x u) f ↔ FCk K s f := fun u => fck_store_of_not K u hx0 hi hnF
  have hnear : ∀ u I κ L, NearLeaf K root (s0.store x u) I κ L ↔ NearLeaf K root s I κ L :=
    fun u => nearLeaf_store_of_not K root u hM
  have hbr : ¬BadR K root s := fun h => hb (Or.inr h)
  -- an answer outside the contacts of its chain kills nothing
  have hsafe : ∀ u, truncateHash u ∉ K.ContactB s l i →
      weightA K root (s0.store x u) = W0 ∧ expo K ρ flag (s0.store x u) = expo K ρ flag s := by
    intro u ht
    refine ⟨?_, expo_congr' ρ flag (hc u) (hm u) (hfck u)⟩
    rw [weightA_eq, hweight, if_neg]
    rintro (hw | hd | hn)
    · obtain ⟨l', hl', hbl⟩ := hw
      rcases badLeaf_store_A K u hx0 hi hA l' hbl with h | h
      · exact hbr (Or.inl ⟨l', hl', h⟩)
      · exact ht h
    · exact hbr (Or.inr (Or.inl ((dead_congr' (hc u) (hfck u)).1 hd)))
    · exact hbr (Or.inr (Or.inr ((nearContact_congr (hfck u) (hnear u) (fun c => Iff.rfl)).1 hn)))
  have hwA : ∀ u, weightA K root (s0.store x u) ≤ W0 := fun u =>
    (weightA_le_weight K root _).trans (le_of_eq (hweight u))
  have hpay0 : ENNReal.ofReal (β / 2 ^ 128) * payF K root s (.inl (.inr (.inl x))) +
      ENNReal.ofReal (cU / 2 ^ 128) * payC K root s (.inl (.inr (.inl x))) ≤ 0 * weightA K root s := by
    rw [payF_ordinary, hH.digest, if_neg hM, payC_of_not K root s _ hnQ]
    simp
  have harm0 : budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s ≤
      budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s +
        ENNReal.ofReal δ * payA K root flag s (.inl (.inr (.inl x))) := le_self_add
  have hnf : nextFlag K root flag s (.inl (.inr (.inl x))) = flag := nextFlag_of_not K root flag s _ hnQ
  rw [show ((.inl (.inr (.inl x)) : CostSpec.Domain)) = .inl (.inr (.inl x)) from rfl]
  have hpf0 : probeFactor p ≠ 0 := by
    rw [probeFactor]
    refine ENNReal.ofReal_pos.2 ?_ |>.ne'
    have := sw_hp hN hle
    have hden : 0 < spaceReal - p := by linarith
    rw [sub_pos, div_lt_one hden]
    linarith
  by_cases hwc : WContact K s
  · -- state 66: no pending credit, the answer may complete a two-edge event
    have hnfc : ¬FContact K s := fun hf => hb (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr ⟨hwc, hf⟩)))))
    have harmd : ArmedS K flag s := Or.inr (Or.inl (by
      obtain ⟨l', i', hl', hc'⟩ := hwc
      exact ⟨l', hl', Or.inr ⟨i', hc'⟩⟩))
    have he2 : 2 ≤ expo K ρ flag s := expo_ge_two K root ρ harmd hb
    have hP : ∀ u, weightA K root (s0.store x u) * pendA K (s0.store x u) ≤ weightA K root s * pendA K s + 0 := by
      intro u
      have : pendA K (s0.store x u) = 0 := by
        unfold pendA; rw [if_pos ((wContact_congr' (hc u)).2 hwc)]
      rw [this, mul_zero]
      exact bot_le
    set e0 := expo K ρ flag s with he0
    set G : Digest → ℝ≥0∞ := fun t => if t ∈ K.ContactB s l i then 0 else budgetE e0 (p + 1) r0 with hG
    have hk := kill_guess hN hle he2
    have hk' : budgetE e0 p (r0 + 1) + g * (ν * budgetE e0 (p + 1) r0) ≤ g * budgetE e0 (p + 1) r0 := by
      refine lift_factor ?_ (mul_le_of_le_one_left' nu_le_one) hgpf
      rw [← mul_assoc]; exact hk
    have hmean := meanD_compl_ge (K.ContactB s l i) (contactB_encard_le hb hl i) (budgetE e0 (p + 1) r0)
    have hR : budgetE e0 p (r0 + 1) + 0 + g * (ν * budgetE e0 (p + 1) r0) ≤
        g * meanD G + g * (ν * budgetE e0 (p + 1) r0) := by
      rw [add_zero, ← mul_add]
      exact hk'.trans (mul_le_mul_right hmean g)
    refine stepBound_fresh K root model ρ β δ cU s s0 x hcs hx0 flag p r0 (p + 1)
      (budgetE e0 p (r0 + 1)) 0 0 harm0 hpay0 hP ?_
    rw [add_zero, hnf]
    have hfin : g * (ν * budgetE e0 (p + 1) r0) ≠ ⊤ :=
      ENNReal.mul_ne_top hgtop (ENNReal.mul_ne_top ν_ne_top ENNReal.ofReal_ne_top)
    refine le_trans (finish_guess hW0ge hR hfin) ?_
    rw [← meanD_mul']
    refine meanD_le_of_pointwise _ _ fun u => ?_
    simp only [hG]
    by_cases ht : truncateHash u ∈ K.ContactB s l i
    · rw [if_pos ht, mul_zero]
      exact bot_le
    · rw [if_neg ht]
      obtain ⟨h1, h2⟩ := hsafe u ht
      rw [h1, h2, mul_comm]
  · -- states ρ, 2, 3: half a unit of pending credit, no event
    have hcl : K.ContactB s l i = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun v hv => hwc ⟨l, i, hl, ⟨v, hv⟩⟩
    have hsafe' : ∀ u, weightA K root (s0.store x u) = W0 ∧ expo K ρ flag (s0.store x u) = expo K ρ flag s :=
      fun u => hsafe u (by rw [hcl]; exact Set.notMem_empty _)
    set e0 := expo K ρ flag s with he0
    have he : e0 = ρ ∨ e0 = 2 ∨ e0 = 3 := by
      rw [he0]
      unfold expo
      rw [if_neg hwc]
      by_cases ha : ArmedS K flag s
      · rw [if_pos ha]
        by_cases hf : FContact K s
        · rw [if_pos hf]; right; right; norm_num
        · rw [if_neg hf]; right; left; norm_num
      · have hf : ¬FContact K s := fun hf => ha (Or.inr (Or.inr hf))
        rw [if_neg ha, if_neg hf]; left; ring
    have h5 := swR5 hN p r0 hle e0 he
    rw [half_nu_eq_ofReal] at h5
    have hhB : ν / 2 ≤ budgetE e0 (p + 1) r0 :=
      (ENNReal.mul_le_mul_iff_right hpf0 (probeFactor_ne_top p)).1 (le_trans le_add_self h5)
    have hR : budgetE e0 p (r0 + 1) + g * (ν / 2) ≤ g * budgetE e0 (p + 1) r0 := lift_factor h5 hhB hgpf
    have hP : ∀ u, weightA K root (s0.store x u) * pendA K (s0.store x u) ≤
        weightA K root s * pendA K s + W0 * (ν / 2) := by
      intro u
      have hpend : pendA K (s0.store x u) ≤ pendA K s + ν / 2 := by
        unfold pendA
        rw [if_neg (fun h => hwc ((wContact_congr' (hc u)).1 h)), if_neg hwc]
        calc ν / 2 * ((K.UAset (s0.store x u)).encard : ℝ≥0∞)
            ≤ ν / 2 * ((insert x (K.UAset s)).encard : ℝ≥0∞) := by
              gcongr
              exact K.uaSet_store u hx0 hi
          _ ≤ ν / 2 * ((K.UAset s).encard + 1 : ℝ≥0∞) := by gcongr; exact encard_insert_le_ennreal _ _
          _ = ν / 2 * ((K.UAset s).encard : ℝ≥0∞) + ν / 2 := by ring
      rw [(hsafe' u).1]
      calc W0 * pendA K (s0.store x u) ≤ W0 * (pendA K s + ν / 2) := mul_le_mul_right hpend _
        _ = W0 * pendA K s + W0 * (ν / 2) := by ring
        _ ≤ weightA K root s * pendA K s + W0 * (ν / 2) := by gcongr
    refine stepBound_fresh K root model ρ β δ cU s s0 x hcs hx0 flag p r0 (p + 1)
      (budgetE e0 p (r0 + 1)) 0 (W0 * (ν / 2)) harm0 hpay0 hP ?_
    rw [add_zero, hnf]
    have hrhs : ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (budgetE (expo K ρ flag (s0.store x u)) (p + 1) r0 * weightA K root (s0.store x u)) =
        W0 * budgetE e0 (p + 1) r0 := by
      simp only [(hsafe' _).1, (hsafe' _).2]
      rw [tsum_uniform_const, mul_comm]
    rw [hrhs]
    exact finish_credit hW0ge hR hhB


end ChainA

/-! ### One step below the word -/

section ChainBStore

variable (K : Ctx) {s : St} {x : HashInput} (u : HashOutput)

theorem contactB_store_B (hx : s.cache x = none) (hi : K.initial x = none) {l : OtsKey} {i : ChainIndex}
    {v : Digest} (hB : K.IsB l i v x) (l' : OtsKey) (i' : ChainIndex) (v' : Digest) :
    v' ∈ K.ContactB (s.store x u) l' i' ↔
      v' ∈ K.ContactB s l' i' ∨ (l' = l ∧ i' = i ∧ v' = v ∧ truncateHash u = K.front l i) := by
  rw [K.contactB_store u hx hi, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro (h | ⟨hB', ht⟩)
    · exact Or.inl h
    · obtain ⟨rfl, rfl, rfl⟩ := Ctx.isB_unique hB' hB
      exact Or.inr ⟨rfl, rfl, rfl, ht⟩
  · rintro (h | ⟨rfl, rfl, rfl, ht⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hB, ht⟩

theorem contactB_store_B_of_ne (hx : s.cache x = none) (hi : K.initial x = none) {l : OtsKey} {i : ChainIndex}
    {v : Digest} (hB : K.IsB l i v x) (ht : truncateHash u ≠ K.front l i) (l' : OtsKey) (i' : ChainIndex) :
    K.ContactB (s.store x u) l' i' = K.ContactB s l' i' := by
  ext v'
  rw [contactB_store_B K u hx hi hB]
  exact ⟨fun h => h.resolve_right fun h' => ht h'.2.2.2, Or.inl⟩

/-- **Releasing a pending credit**: a fresh input one step below the word whose payload is the
answer of an input two steps below takes that input out of the pending set. -/
theorem uaSet_release (hx : s.cache x = none) (hi : K.initial x = none) {l : OtsKey} (hl : Retained K.p l)
    {i : ChainIndex} {v : Digest} (hB : K.IsB l i v x) (hv : v ∈ K.AAns s l i) :
    ((K.UAset (s.store x u)).encard : ℝ≥0∞) + 1 ≤ ((K.UAset s).encard : ℝ≥0∞) := by
  obtain ⟨y, w, hyA, hyF, hyt⟩ := hv
  have hvB : v ∉ K.BPay s l i := K.not_mem_bPay hx hB
  have hyU : y ∈ K.UAset s := ⟨l, i, w, hl, hyA, hyF, by rw [hyt]; exact hvB⟩
  have hyU' : y ∉ K.UAset (s.store x u) := by
    rintro ⟨l', i', w', hl', hyA', hyF', hnot⟩
    obtain ⟨rfl, rfl⟩ := Ctx.isA_unique hyA' hyA
    have hyx : y ≠ x := fun h => Ctx.isA_not_isB hyA (h ▸ hB)
    have hw : w' = w := by
      rcases (K.fr_store u hx hi).1 hyF' with h | ⟨h, -⟩
      · exact Option.some.inj (h.1.symm.trans hyF.1)
      · exact absurd h hyx
    subst hw
    apply hnot
    rw [hyt, K.bPay_store u hx hi]
    exact Or.inr hB
  have hsub : insert y (K.UAset (s.store x u)) ⊆ K.UAset s := by
    intro z hz
    rcases Set.mem_insert_iff.1 hz with rfl | hz
    · exact hyU
    · exact K.uaSet_store_of_not u hx hi (fun l' i' _ hA => Ctx.isA_not_isB hA hB) hz
  have h1 := Set.encard_le_encard hsub
  rw [Set.encard_insert_of_notMem hyU'] at h1
  have h2 : ((K.UAset (s.store x u)).encard + 1 : ℕ∞) ≤ (K.UAset s).encard := h1
  calc ((K.UAset (s.store x u)).encard : ℝ≥0∞) + 1 = (((K.UAset (s.store x u)).encard + 1 : ℕ∞) : ℝ≥0∞) := by
        rw [ENat.toENNReal_add, ENat.toENNReal_one]
    _ ≤ _ := ENat.toENNReal_le.2 h2

end ChainBStore

section ChainB

variable (K : Ctx) (root : Digest) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (ρ β δ cU : ℝ)

/-- **A fresh chain query one step below the word**, with the guess factor `g`. -/
theorem step_chainB {total : ℕ} (hN : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (hH : StepHyp K model)
    (s : St) (flag : Bool) (p r0 : ℕ) (hinv : InvS K s p) (hb : ¬BadP K root s)
    {l : OtsKey} (hl : Retained K.p l) {i : ChainIndex} {v : Digest} {x : HashInput} (hBx : K.IsB l i v x)
    (hx : s.cache x = none) (gs : List (Coordinate × Digest))
    (hcs : costStep model (.inl (.inr (.inl x))) s = readOutside x { s with guesses := gs })
    (g : ℝ≥0∞) (hW0ge : g * weightA K root s ≤ weight K.tg K.initial { s with guesses := gs })
    (hW0le : weight K.tg K.initial { s with guesses := gs } ≤ weightA K root s)
    (hgpf : probeFactor p ≤ g) (hgtop : g ≠ ⊤) (hle : p + r0 + 1 ≤ total) :
    StepBound K root model ρ β δ cU (.inl (.inr (.inl x))) s flag p (r0 + 1) (p + 1) := by
  set s0 : St := { s with guesses := gs } with hs0
  have hx0 : s0.cache x = none := hx
  have hi : K.initial x = none := initial_none_of_fresh K.initial s hinv.sat.prepared x hx
  have hkind : K.tg.kind x = .none := hH.sec x (K.secondOrder_of_isB hBx)
  have hM : ¬ForsSigner.IsMsgInput x := by
    obtain ⟨st, -, rfl⟩ := hBx
    exact fun h => msg_ne_chain h rfl
  have hnF : ∀ f : FIn, x ≠ f.input K.p := fun f => Ctx.isB_ne_fleaf hBx f
  have hnQ : ¬IsFLQ K (.inl (.inr (.inl x))) := fun h => by
    obtain ⟨f, hf⟩ := (isFLQ_ordinary_iff K x).1 h
    exact hnF f hf
  have hA : ∀ l i, Retained K.p l → ¬K.IsA l i x := fun l' i' _ hA' => Ctx.isA_not_isB hA' hBx
  have hE : ∀ (l : OtsKey) msg ctr, x ≠ Wots.encodingInput K.p l.1 l.2.1 l.2.2 msg ctr :=
    fun l' msg ctr => Ctx.isB_ne_enc hBx l' msg ctr
  set W0 := weight K.tg K.initial s0 with hW0
  have hweight : ∀ u, weight K.tg K.initial (s0.store x u) = W0 := fun u =>
    weight_store_untargetedW K.tg K.initial s0 x u hkind
  have haa : ∀ u l' i', K.AAns (s0.store x u) l' i' = K.AAns s l' i' := fun u l' i' => by
    rw [K.aAns_store u hx0 hi, if_neg (fun h => Ctx.isA_not_isB h hBx)]
    rfl
  have hm : ∀ u l' i', Retained K.p l' → (K.Marker (s0.store x u) l' i' ↔ K.Marker s l' i') :=
    fun u l' i' _ => marker_store_of_notE K u hx0 hi hE l' i'
  have hfck : ∀ u f, FCk K (s0.store x u) f ↔ FCk K s f := fun u => fck_store_of_not K u hx0 hi hnF
  have hnear : ∀ u I κ L, NearLeaf K root (s0.store x u) I κ L ↔ NearLeaf K root s I κ L :=
    fun u => nearLeaf_store_of_not K root u hM
  have hbr : ¬BadR K root s := fun h => hb (Or.inr h)
  -- no contact: nothing changes
  have hsafe : ∀ u, truncateHash u ≠ K.front l i →
      weightA K root (s0.store x u) = W0 ∧ expo K ρ flag (s0.store x u) = expo K ρ flag s := by
    intro u ht
    have hc : ∀ l' i', Retained K.p l' → K.ContactB (s0.store x u) l' i' = K.ContactB s l' i' :=
      fun l' i' _ => contactB_store_B_of_ne K u hx0 hi hBx ht l' i'
    have hsame : ∀ l', Retained K.p l' → K.SameLeaf s (s0.store x u) l' :=
      fun l' hl' => ⟨fun i' => hc l' i' hl', fun i' => haa u l' i', fun i' => hm u l' i' hl'⟩
    refine ⟨?_, expo_congr' ρ flag hc (hm u) (hfck u)⟩
    rw [weightA_eq, hweight, if_neg (fun h => hbr ((badR_congr hsame (hfck u) (hnear u) (fun c => Iff.rfl)).1 h))]
  have hpendle : ∀ u, pendA K (s0.store x u) ≤ pendA K s := by
    intro u
    unfold pendA
    by_cases h1 : WContact K (s0.store x u)
    · rw [if_pos h1]; exact bot_le
    · have h2 : ¬WContact K s := fun h => h1 (wContact_mono (extends_store s0 x u hx0) h)
      rw [if_neg h1, if_neg h2]
      gcongr
      exact K.uaSet_store_of_not u hx0 hi hA
  have hP0 : ∀ u, weightA K root (s0.store x u) * pendA K (s0.store x u) ≤ weightA K root s * pendA K s + 0 := by
    intro u
    rw [add_zero]
    refine mul_le_mul' ?_ (hpendle u)
    exact (weightA_le_weight K root _).trans ((le_of_eq (hweight u)).trans hW0le)
  have hpay0 : ENNReal.ofReal (β / 2 ^ 128) * payF K root s (.inl (.inr (.inl x))) +
      ENNReal.ofReal (cU / 2 ^ 128) * payC K root s (.inl (.inr (.inl x))) ≤ 0 * weightA K root s := by
    rw [payF_ordinary, hH.digest, if_neg hM, payC_of_not K root s _ hnQ]
    simp
  have harm0 : budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s ≤
      budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s +
        ENNReal.ofReal δ * payA K root flag s (.inl (.inr (.inl x))) := le_self_add
  have hnf : nextFlag K root flag s (.inl (.inr (.inl x))) = flag := nextFlag_of_not K root flag s _ hnQ
  set e0 := expo K ρ flag s with he0
  set B : ℝ → ℝ≥0∞ := fun e => budgetE e (p + 1) r0 with hB
  by_cases harmd : ArmedS K flag s
  · -- armed: a contact survives (exponent 66) or kills
    have he2 : 2 ≤ e0 := expo_ge_two K root ρ harmd hb
    set G : Digest → ℝ≥0∞ := fun t => if t = K.front l i then 0 else B e0 with hG
    have hmean : meanD G + ν * B e0 = B e0 + ν * 0 := meanD_two _ _ _
    rw [mul_zero, add_zero] at hmean
    have hk : budgetE e0 p (r0 + 1) + g * (ν * B e0) ≤ g * B e0 := by
      refine lift_factor ?_ (mul_le_of_le_one_left' nu_le_one) hgpf
      rw [← mul_assoc]; exact kill_guess hN hle he2
    have hR : budgetE e0 p (r0 + 1) + 0 + g * (ν * B e0) ≤ g * meanD G + g * (ν * B e0) := by
      rw [add_zero, ← mul_add, hmean]; exact hk
    refine stepBound_fresh K root model ρ β δ cU s s0 x hcs hx0 flag p r0 (p + 1)
      (budgetE e0 p (r0 + 1)) 0 0 harm0 hpay0 hP0 ?_
    rw [add_zero, hnf]
    refine le_trans (finish_guess hW0ge hR
      (ENNReal.mul_ne_top hgtop (ENNReal.mul_ne_top ν_ne_top ENNReal.ofReal_ne_top))) ?_
    rw [← meanD_mul']
    refine meanD_le_of_pointwise _ _ fun u => ?_
    simp only [hG]
    by_cases ht : truncateHash u = K.front l i
    · rw [if_pos ht, mul_zero]; exact bot_le
    · rw [if_neg ht]
      obtain ⟨h1, h2⟩ := hsafe u ht
      rw [h1, h2, mul_comm]
  · -- unarmed: exponent ρ, no contact, no marker anywhere
    have heρ : e0 = ρ := expo_unarmed K ρ harmd
    have hnw : ¬WContact K s := fun ⟨l', i', hl', hc'⟩ => harmd (Or.inr (Or.inl ⟨l', hl', Or.inr ⟨i', hc'⟩⟩))
    have hnf' : ¬FContact K s := fun hf => harmd (Or.inr (Or.inr hf))
    have hnm : ∀ l' i', Retained K.p l' → ¬K.Marker s l' i' :=
      fun l' i' hl' hm' => harmd (Or.inr (Or.inl ⟨l', hl', Or.inl ⟨i', hm'⟩⟩))
    have hcnil : ∀ l' i' v', Retained K.p l' → v' ∉ K.ContactB s l' i' := fun l' i' v' hl' hv' => hnw ⟨l', i', hl', v', hv'⟩
    by_cases hvA : v ∈ K.AAns s l i
    · -- the payload is a pending answer: a contact kills, every answer releases its credit
      have hkill : ∀ u, truncateHash u = K.front l i → weightA K root (s0.store x u) = 0 := by
        intro u ht
        refine weightA_of_badP K root (Or.inr (Or.inl ⟨l, hl, Or.inl ⟨i, v, ?_, ?_⟩⟩))
        · exact (contactB_store_B K u hx0 hi hBx l i v).2 (Or.inr ⟨rfl, rfl, rfl, ht⟩)
        · rw [haa]; exact hvA
      have hrel : ∀ u, truncateHash u ≠ K.front l i → pendA K (s0.store x u) + ν / 2 ≤ pendA K s := by
        intro u ht
        have hw' : ¬WContact K (s0.store x u) := fun h =>
          hnw ((wContact_congr' fun l' i' _ => contactB_store_B_of_ne K u hx0 hi hBx ht l' i').1 h)
        unfold pendA
        rw [if_neg hw', if_neg hnw]
        calc ν / 2 * ((K.UAset (s0.store x u)).encard : ℝ≥0∞) + ν / 2
            = ν / 2 * (((K.UAset (s0.store x u)).encard : ℝ≥0∞) + 1) := by ring
          _ ≤ ν / 2 * ((K.UAset s).encard : ℝ≥0∞) := by
              gcongr
              exact uaSet_release K u hx0 hi hl hBx hvA
      set Prel := ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if truncateHash u = K.front l i then 0 else W0 * (ν / 2)) with hPrel
      have hPrel_top : Prel ≠ ⊤ := by
        refine ne_top_of_le_ne_top (b := W0 * (ν / 2)) ?_ (tsum_le_const_of_pointwise _ _ _ fun u => by
          split_ifs <;> simp)
        exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top (weight_le_one K.tg K.initial s0))
          (ENNReal.div_ne_top ν_ne_top (by norm_num))
      have hPexp : ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (weightA K root (s0.store x u) * pendA K (s0.store x u)) + Prel ≤ weightA K root s * pendA K s + 0 := by
        rw [hPrel, ← ENNReal.tsum_add, add_zero]
        simp_rw [← mul_add]
        refine tsum_le_const_of_pointwise _ _ _ fun u => ?_
        by_cases ht : truncateHash u = K.front l i
        · rw [hkill u ht, if_pos ht]; simp
        · rw [if_neg ht, (hsafe u ht).1, ← mul_add]
          calc W0 * (pendA K (s0.store x u) + ν / 2) ≤ W0 * pendA K s := mul_le_mul_right (hrel u ht) _
            _ ≤ _ := mul_le_mul_left hW0le _
      -- the main inequality: R6
      set Y : ℝ≥0∞ := B e0 + ν / 2 with hY
      set M := meanD (fun t => if t = K.front l i then 0 else Y) with hM'
      have hMeq : M + ν * Y = Y := by
        have := meanD_two (K.front l i) 0 Y
        rw [mul_zero, add_zero] at this
        exact this
      have hM1 : ENNReal.ofReal (1 - 1 / 2 ^ 128) * Y = M := by
        have h1 : ENNReal.ofReal (1 - 1 / 2 ^ 128) * Y + ν * Y = Y := by rw [← add_mul, one_sub_nu_add, one_mul]
        have hfin : ν * Y ≠ ⊤ := ENNReal.mul_ne_top ν_ne_top
          (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.div_ne_top ν_ne_top (by norm_num)⟩)
        exact (ENNReal.add_left_inj hfin).1 (h1.trans hMeq.symm)
      have h6 := swR6 hN p r0 hle
      rw [half_nu_eq_ofReal, heρ.symm] at h6
      have h6' : budgetE e0 p (r0 + 1) ≤ probeFactor p * M := by
        rw [← hM1, ← mul_assoc]; exact h6
      refine stepBound_fresh' K root model ρ β δ cU s s0 x hcs hx0 flag p r0 (p + 1)
        (budgetE e0 p (r0 + 1)) 0 0 Prel hPrel_top harm0 hpay0 hPexp ?_
      rw [add_zero, add_zero, hnf, hPrel, ← ENNReal.tsum_add]
      simp_rw [← mul_add]
      calc budgetE e0 p (r0 + 1) * weightA K root s ≤ probeFactor p * M * weightA K root s := mul_le_mul_left h6' _
        _ = M * (probeFactor p * weightA K root s) := by ring
        _ ≤ M * (g * weightA K root s) := by gcongr
        _ ≤ M * W0 := mul_le_mul_right hW0ge _
        _ = W0 * M := mul_comm _ _
        _ = meanD (fun t => W0 * (if t = K.front l i then 0 else Y)) := (meanD_mul' W0 _).symm
        _ ≤ _ := by
            refine meanD_le_of_pointwise _ _ fun u => ?_
            by_cases ht : truncateHash u = K.front l i
            · rw [if_pos ht, if_pos ht, mul_zero]; exact bot_le
            · rw [if_neg ht, if_neg ht, (hsafe u ht).1, (hsafe u ht).2]
              exact le_of_eq (by simp only [hY, hB]; ring)
    · -- a contact survives with exponent 66: EB
      have hcont : ∀ u, truncateHash u = K.front l i →
          weightA K root (s0.store x u) = W0 ∧ expo K ρ flag (s0.store x u) = 66 := by
        intro u ht
        have hmemC : ∀ l' i' v', Retained K.p l' → (v' ∈ K.ContactB (s0.store x u) l' i' ↔ l' = l ∧ i' = i ∧ v' = v) := by
          intro l' i' v' hl'
          rw [contactB_store_B K u hx0 hi hBx]
          constructor
          · rintro (h | ⟨h1, h2, h3, -⟩)
            · exact absurd h (hcnil l' i' v' hl')
            · exact ⟨h1, h2, h3⟩
          · rintro ⟨h1, h2, h3⟩
            exact Or.inr ⟨h1, h2, h3, ht⟩
        have hwc' : WContact K (s0.store x u) := ⟨l, i, hl, v, (hmemC l i v hl).2 ⟨rfl, rfl, rfl⟩⟩
        have hfc' : ¬FContact K (s0.store x u) := fun h => hnf' ((fContact_congr (hfck u)).1 h)
        have hnot : ¬BadR K root (s0.store x u) := by
          rintro (⟨l', hl', hbl⟩ | hd | hn)
          · rcases hbl with ⟨i', v', h1, h2⟩ | ⟨i', ⟨v', h1⟩, hm'⟩ | ⟨i', i'', hne, ⟨v', h1⟩, ⟨v'', h2⟩⟩
            · obtain ⟨rfl, rfl, rfl⟩ := (hmemC l' i' v' hl').1 h1
              rw [haa] at h2
              exact hvA h2
            · obtain ⟨rfl, rfl, rfl⟩ := (hmemC l' i' v' hl').1 h1
              exact hnm l' i' hl' ((hm u l' i' hl').1 hm')
            · obtain ⟨rfl, rfl, -⟩ := (hmemC l' i' v' hl').1 h1
              obtain ⟨-, rfl, -⟩ := (hmemC l' i'' v'' hl').1 h2
              exact hne rfl
          · rcases hd with ⟨l1, i1, v1, l2, i2, v2, hl1, hl2, h1, h2, hne⟩ | ⟨f, f', hne, h1, h2⟩ | ⟨-, hf⟩
            · obtain ⟨rfl, rfl, rfl⟩ := (hmemC l1 i1 v1 hl1).1 h1
              obtain ⟨rfl, rfl, rfl⟩ := (hmemC l2 i2 v2 hl2).1 h2
              exact hne rfl
            · exact hnf' ⟨f, (hfck u f).1 h1⟩
            · exact hfc' hf
          · exact hbr (Or.inr (Or.inr ((nearContact_congr (hfck u) (hnear u) (fun c => Iff.rfl)).1 hn)))
        refine ⟨by rw [weightA_eq, hweight, if_neg hnot], ?_⟩
        have ha' : ArmedS K flag (s0.store x u) := Or.inr (Or.inl (by
          obtain ⟨l', i', hl', hc'⟩ := hwc'
          exact ⟨l', hl', Or.inr ⟨i', hc'⟩⟩))
        unfold expo
        rw [if_pos ha', if_pos hwc', if_neg hfc']
        norm_num
      set G : Digest → ℝ≥0∞ := fun t => if t = K.front l i then B 66 else B e0 with hG
      have hmean : meanD G + ν * B e0 = B e0 + ν * B 66 := meanD_two _ _ _
      have h2 := swR2 hN p r0 hle
      rw [nu_eq_ofReal', heρ.symm] at h2
      have hR0 : budgetE e0 p (r0 + 1) + probeFactor p * (ν * B e0) ≤ probeFactor p * (B e0 + ν * B 66) := by
        calc budgetE e0 p (r0 + 1) + probeFactor p * (ν * B e0)
            = budgetE e0 p (r0 + 1) + probeFactor p * ν * budgetE e0 (p + 1) r0 := by rw [mul_assoc]
          _ ≤ probeFactor p * budgetE e0 (p + 1) r0 + probeFactor p * ν * budgetE 66 (p + 1) r0 := h2
          _ = probeFactor p * (B e0 + ν * B 66) := by simp only [hB]; ring
      have hXY : ν * B e0 ≤ B e0 + ν * B 66 := le_trans (mul_le_of_le_one_left' nu_le_one) le_self_add
      have hR : budgetE e0 p (r0 + 1) + 0 + g * (ν * B e0) ≤ g * meanD G + g * (ν * B e0) := by
        rw [add_zero, ← mul_add, hmean]
        exact lift_factor hR0 hXY hgpf
      refine stepBound_fresh K root model ρ β δ cU s s0 x hcs hx0 flag p r0 (p + 1)
        (budgetE e0 p (r0 + 1)) 0 0 harm0 hpay0 hP0 ?_
      rw [add_zero, hnf]
      refine le_trans (finish_guess hW0ge hR
        (ENNReal.mul_ne_top hgtop (ENNReal.mul_ne_top ν_ne_top ENNReal.ofReal_ne_top))) ?_
      rw [← meanD_mul']
      refine meanD_le_of_pointwise _ _ fun u => ?_
      simp only [hG]
      by_cases ht : truncateHash u = K.front l i
      · rw [if_pos ht]
        obtain ⟨h1, h2⟩ := hcont u ht
        rw [h1, h2, mul_comm]
      · rw [if_neg ht]
        obtain ⟨h1, h2⟩ := hsafe u ht
        rw [h1, h2, mul_comm]

end ChainB

/-! ### No WOTS shape -/

section NoShape

variable (K : Ctx) (root : Digest) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (ρ β δ cU : ℝ)

/-- **A fresh untargeted query of no WOTS, FORS leaf or digest shape** (a chain step far below the
word), with the guess factor `g`. -/
theorem step_noShape {total : ℕ} (hN : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (hH : StepHyp K model)
    (s : St) (flag : Bool) (p r0 : ℕ) (hinv : InvS K s p) (hb : ¬BadP K root s) {x : HashInput}
    (hx : s.cache x = none) (hkind : K.tg.kind x = .none)
    (hA : ∀ l i, Retained K.p l → ¬K.IsA l i x) (hB : ∀ l i v, Retained K.p l → ¬K.IsB l i v x)
    (hE : ∀ l msg ctr, Retained K.p l → x ≠ Wots.encodingInput K.p l.1 l.2.1 l.2.2 msg ctr)
    (hnF : ∀ f : FIn, x ≠ f.input K.p) (hM : ¬ForsSigner.IsMsgInput x)
    (gs : List (Coordinate × Digest))
    (hcs : costStep model (.inl (.inr (.inl x))) s = readOutside x { s with guesses := gs })
    (g : ℝ≥0∞) (hW0ge : g * weightA K root s ≤ weight K.tg K.initial { s with guesses := gs })
    (hW0le : weight K.tg K.initial { s with guesses := gs } ≤ weightA K root s)
    (hgpf : probeFactor p ≤ g) (hle : p + r0 + 1 ≤ total) :
    StepBound K root model ρ β δ cU (.inl (.inr (.inl x))) s flag p (r0 + 1) (p + 1) := by
  set s0 : St := { s with guesses := gs } with hs0
  have hx0 : s0.cache x = none := hx
  have hi : K.initial x = none := initial_none_of_fresh K.initial s hinv.sat.prepared x hx
  have hnQ : ¬IsFLQ K (.inl (.inr (.inl x))) := fun h => by
    obtain ⟨f, hf⟩ := (isFLQ_ordinary_iff K x).1 h
    exact hnF f hf
  set W0 := weight K.tg K.initial s0 with hW0
  have hweight : ∀ u, weight K.tg K.initial (s0.store x u) = W0 := fun u =>
    weight_store_untargetedW K.tg K.initial s0 x u hkind
  have hsame : ∀ u l, Retained K.p l → K.SameLeaf s (s0.store x u) l := fun u l hl =>
    K.sameLeaf_store u hx0 hi l (fun i => hA l i hl) (fun i v => hB l i v hl) (fun msg ctr => hE l msg ctr hl)
  have hfck : ∀ u f, FCk K (s0.store x u) f ↔ FCk K s f := fun u => fck_store_of_not K u hx0 hi hnF
  have hnear : ∀ u I κ L, NearLeaf K root (s0.store x u) I κ L ↔ NearLeaf K root s I κ L :=
    fun u => nearLeaf_store_of_not K root u hM
  have hbr : ¬BadR K root s := fun h => hb (Or.inr h)
  have hsafe : ∀ u, weightA K root (s0.store x u) = W0 ∧ expo K ρ flag (s0.store x u) = expo K ρ flag s := by
    intro u
    refine ⟨?_, expo_congr ρ flag (hsame u) (hfck u)⟩
    rw [weightA_eq, hweight, if_neg (fun h => hbr ((badR_congr (hsame u) (hfck u) (hnear u) (fun c => Iff.rfl)).1 h))]
  have hP0 : ∀ u, weightA K root (s0.store x u) * pendA K (s0.store x u) ≤ weightA K root s * pendA K s + 0 := by
    intro u
    rw [add_zero, (hsafe u).1]
    refine mul_le_mul' hW0le ?_
    unfold pendA
    rw [wContact_congr (hsame u)]
    split_ifs
    · exact le_rfl
    · gcongr
      exact K.uaSet_store_of_not u hx0 hi hA
  have hpay0 : ENNReal.ofReal (β / 2 ^ 128) * payF K root s (.inl (.inr (.inl x))) +
      ENNReal.ofReal (cU / 2 ^ 128) * payC K root s (.inl (.inr (.inl x))) ≤ 0 * weightA K root s := by
    rw [payF_ordinary, hH.digest, if_neg hM, payC_of_not K root s _ hnQ]
    simp
  have harm0 : budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s ≤
      budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s +
        ENNReal.ofReal δ * payA K root flag s (.inl (.inr (.inl x))) := le_self_add
  have hnf : nextFlag K root flag s (.inl (.inr (.inl x))) = flag := nextFlag_of_not K root flag s _ hnQ
  set e0 := expo K ρ flag s with he0
  have he1 : 1 ≤ e0 := expo_ge_one K root ρ hN.one_le_rho hb
  have hR : budgetE e0 p (r0 + 1) ≤ g * budgetE e0 (p + 1) r0 := by
    have h := lift_factor (X := 0) (Y := budgetE e0 (p + 1) r0) (Bb := budgetE e0 p (r0 + 1))
      (by rw [mul_zero, add_zero]; exact guess_plain hN hle he1) bot_le hgpf
    rwa [mul_zero, add_zero] at h
  refine stepBound_fresh K root model ρ β δ cU s s0 x hcs hx0 flag p r0 (p + 1)
    (budgetE e0 p (r0 + 1)) 0 0 harm0 hpay0 hP0 ?_
  rw [add_zero, add_zero, hnf]
  have hrhs : ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (budgetE (expo K ρ flag (s0.store x u)) (p + 1) r0 * weightA K root (s0.store x u)) =
      budgetE e0 (p + 1) r0 * W0 := by
    simp only [(hsafe _).1, (hsafe _).2]
    rw [tsum_uniform_const]
  rw [hrhs]
  calc budgetE e0 p (r0 + 1) * weightA K root s ≤ g * budgetE e0 (p + 1) r0 * weightA K root s :=
        mul_le_mul_left hR _
    _ = budgetE e0 (p + 1) r0 * (g * weightA K root s) := by ring
    _ ≤ budgetE e0 (p + 1) r0 * W0 := mul_le_mul_right hW0ge _

end NoShape

end FORS.Security.SWRoute
