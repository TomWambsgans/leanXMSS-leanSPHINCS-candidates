import FORS.SWRoute.StepsChain

/-! **The SW route: first-order answers, a FORS leaf query without guess, a fresh digest block.**
A fresh answer at an input of no FORS leaf, digest, or chain shape below the word keeps at least a
`1 - 2^-128` share of the survival weight in mean; an encoding of a retained key may also mark a
chain (arming the unarmed state, or killing at the key of a WOTS contact). A FORS leaf query whose
secret is known makes an unrecorded contact, which kills. A fresh digest block frees the digest
decrement and may complete a FORS contact (a kill, booked in `WK`). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost PotentialA GraphView ForsPotential

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

theorem one_sub_inv_space : (1 : ℝ≥0∞) - 1 / space = ENNReal.ofReal (1 - 1 / 2 ^ 128) := by
  have h := oneSub_div_space 1 Nat.one_le_two_pow
  simpa [spaceReal] using h

theorem one_sub_nu_eq : ENNReal.ofReal (1 - 1 / 2 ^ 128) = 1 - ν := by
  rw [← one_sub_nu_add, ENNReal.add_sub_cancel_right ν_ne_top]

/-- The plain kill form, as a factor `1 - 2^-128`. -/
theorem kill_plain' {ρ β δ cU : ℝ} {T : ℕ} (h : SWNumeric ρ β δ ((T : ℝ) / 2 ^ 128) cU) {p r : ℕ}
    (hle : p + r + 1 ≤ T) {e : ℝ} (he : 1 ≤ e) :
    budgetE e p (r + 1) ≤ ENNReal.ofReal (1 - 1 / 2 ^ 128) * budgetE e (p + 1) r := by
  have hk := kill_plain h hle he
  have hfin : ν * budgetE e (p + 1) r ≠ ⊤ := ENNReal.mul_ne_top ν_ne_top ENNReal.ofReal_ne_top
  rw [← ENNReal.add_le_add_iff_right hfin, ← add_mul, one_sub_nu_add, one_mul]
  exact hk

section First

variable (K : Ctx) (root : Digest) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (ρ β δ cU : ℝ)

/-- **A fresh first-order answer with a set `S` of special answers** (each costing at most `c`
times the weight). -/
theorem step_firstOrder {total : ℕ} (hN : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (hH : StepHyp K model)
    (s : St) (flag : Bool) (p r0 : ℕ) (hinv : InvS K s p) (hb : ¬BadP K root s) {x : HashInput}
    (hx : s.cache x = none) (hcs : costStep model (.inl (.inr (.inl x))) s = readOutside x s)
    (hnF : ∀ f : FIn, x ≠ f.input K.p) (hM : ¬ForsSigner.IsMsgInput x)
    (hA : ∀ l i, Retained K.p l → ¬K.IsA l i x)
    (S : Finset Digest) (n c B0 : ℝ≥0∞) (hS : (S.card : ℝ≥0∞) ≤ n) (hc : c ≠ ⊤) (hn : n ≠ ⊤)
    (hpt : ∀ u, B0 * weight K.tg K.initial (s.store x u) ≤
      budgetE (expo K ρ flag (s.store x u)) (p + 1) r0 * weightA K root (s.store x u) +
        (if truncateHash u ∈ S then c * weight K.tg K.initial (s.store x u) else 0))
    (hR : budgetE (expo K ρ flag s) p (r0 + 1) + n * ν * c ≤ ENNReal.ofReal (1 - 1 / 2 ^ 128) * B0) :
    StepBound K root model ρ β δ cU (.inl (.inr (.inl x))) s flag p (r0 + 1) (p + 1) := by
  have hi : K.initial x = none := initial_none_of_fresh K.initial s hinv.sat.prepared x hx
  have hnQ : ¬IsFLQ K (.inl (.inr (.inl x))) := fun h => by
    obtain ⟨f, hf⟩ := (isFLQ_ordinary_iff K x).1 h
    exact hnF f hf
  have hw : weightA K root s = weight K.tg K.initial s := weightA_eq_weight_of K root hb
  have hwle : ∀ u, weight K.tg K.initial (s.store x u) ≤ weight K.tg K.initial s := fun u =>
    weight_le_of_extendsW K.tg K.initial (extends_store s x u hx) rfl
  have hP0 : ∀ u, weightA K root (s.store x u) * pendA K (s.store x u) ≤ weightA K root s * pendA K s + 0 := by
    intro u
    rw [add_zero, hw]
    refine mul_le_mul' ((weightA_le_weight K root _).trans (hwle u)) ?_
    unfold pendA
    by_cases h1 : WContact K (s.store x u)
    · rw [if_pos h1]; exact bot_le
    · have h2 : ¬WContact K s := fun h => h1 (wContact_mono (extends_store s x u hx) h)
      rw [if_neg h1, if_neg h2]
      gcongr
      exact K.uaSet_store_of_not u hx hi hA
  have hpay0 : ENNReal.ofReal (β / 2 ^ 128) * payF K root s (.inl (.inr (.inl x))) +
      ENNReal.ofReal (cU / 2 ^ 128) * payC K root s (.inl (.inr (.inl x))) ≤ 0 * weightA K root s := by
    rw [payF_ordinary, hH.digest, if_neg hM, payC_of_not K root s _ hnQ]
    simp
  have harm0 : budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s ≤
      budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s +
        ENNReal.ofReal δ * payA K root flag s (.inl (.inr (.inl x))) := le_self_add
  have hnf : nextFlag K root flag s (.inl (.inr (.inl x))) = flag := nextFlag_of_not K root flag s _ hnQ
  refine stepBound_fresh K root model ρ β δ cU s s x hcs hx flag p r0 (p + 1)
    (budgetE (expo K ρ flag s) p (r0 + 1)) 0 0 harm0 hpay0 hP0 ?_
  rw [add_zero, add_zero, hnf]
  set E := ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
    (budgetE (expo K ρ flag (s.store x u)) (p + 1) r0 * weightA K root (s.store x u))
  -- the mean of the special answers
  have hspec : ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if truncateHash u ∈ S then c * weight K.tg K.initial (s.store x u) else 0) ≤
        n * ν * c * weightA K root s := by
    calc _ ≤ ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (fun t => if t ∈ S then c * weightA K root s else 0) (truncateHash u) := by
          refine ENNReal.tsum_le_tsum fun u => mul_le_mul_right ?_ _
          dsimp only
          split_ifs
          · rw [hw]; exact mul_le_mul_right (hwle u) _
          · exact le_rfl
      _ = meanD (fun t => if t ∈ S then c * weightA K root s else 0) :=
          mean_trunc (fun t => if t ∈ S then c * weightA K root s else 0)
      _ ≤ ν * ((S.card : ℝ≥0∞) * (c * weightA K root s)) := meanD_ite_le _ S (fun t h => h) _
      _ ≤ ν * (n * (c * weightA K root s)) := by gcongr
      _ = n * ν * c * weightA K root s := by ring
  -- the mean of the first-order part
  have hmean : ENNReal.ofReal (1 - 1 / 2 ^ 128) * weightA K root s ≤
      ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * weight K.tg K.initial (s.store x u) := by
    rw [← one_sub_inv_space, hw]
    exact weight_store_mean K.tg K.initial hH.trunc s x hx hi (fun c => Set.toFinite _)
  have hsum : B0 * (ENNReal.ofReal (1 - 1 / 2 ^ 128) * weightA K root s) ≤ E + n * ν * c * weightA K root s := by
    calc B0 * (ENNReal.ofReal (1 - 1 / 2 ^ 128) * weightA K root s)
        ≤ B0 * ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * weight K.tg K.initial (s.store x u) :=
          mul_le_mul_right hmean _
      _ = ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * (B0 * weight K.tg K.initial (s.store x u)) := by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun u => by ring
      _ ≤ ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (budgetE (expo K ρ flag (s.store x u)) (p + 1) r0 * weightA K root (s.store x u) +
              (if truncateHash u ∈ S then c * weight K.tg K.initial (s.store x u) else 0)) :=
          ENNReal.tsum_le_tsum fun u => mul_le_mul_right (hpt u) _
      _ = E + ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (if truncateHash u ∈ S then c * weight K.tg K.initial (s.store x u) else 0) := by
          rw [← ENNReal.tsum_add]
          exact tsum_congr fun u => by ring
      _ ≤ E + n * ν * c * weightA K root s := add_le_add le_rfl hspec
  have hfin : n * ν * c * weightA K root s ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hn ν_ne_top) hc) (weightA_ne_top K root s)
  have key : budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s + n * ν * c * weightA K root s ≤
      E + n * ν * c * weightA K root s :=
    calc _ = (budgetE (expo K ρ flag s) p (r0 + 1) + n * ν * c) * weightA K root s := by ring
      _ ≤ ENNReal.ofReal (1 - 1 / 2 ^ 128) * B0 * weightA K root s := mul_le_mul_left hR _
      _ = B0 * (ENNReal.ofReal (1 - 1 / 2 ^ 128) * weightA K root s) := by ring
      _ ≤ _ := hsum
  exact (ENNReal.add_le_add_iff_right hfin).1 key


theorem markAll_mem_iff (l : OtsKey) (t : Digest) : t ∈ K.markAll l ↔ ∃ i, t ∈ K.markSet l i := by
  constructor
  · intro h
    obtain ⟨word, hw, hd⟩ := EncodingCode.mem_decodingDigests.1 h
    obtain ⟨i, hi⟩ := EncodingCode.mem_allUnitNeighbors.1 hw
    exact ⟨i, EncodingCode.mem_decodingDigests.2 ⟨word, EncodingCode.mem_unitNeighbors.2 hi, hd⟩⟩
  · rintro ⟨i, h⟩
    exact K.markSet_subset l i h

/-- **A fresh first-order answer of no special shape.** -/
theorem step_other1 {total : ℕ} (hN : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (hH : StepHyp K model)
    (s : St) (flag : Bool) (p r0 : ℕ) (hinv : InvS K s p) (hb : ¬BadP K root s) {x : HashInput}
    (hx : s.cache x = none) (hcs : costStep model (.inl (.inr (.inl x))) s = readOutside x s)
    (hnF : ∀ f : FIn, x ≠ f.input K.p) (hM : ¬ForsSigner.IsMsgInput x)
    (hA : ∀ l i, Retained K.p l → ¬K.IsA l i x) (hB : ∀ l i v, Retained K.p l → ¬K.IsB l i v x)
    (hE : ∀ l msg ctr, Retained K.p l → x ≠ Wots.encodingInput K.p l.1 l.2.1 l.2.2 msg ctr)
    (hle : p + r0 + 1 ≤ total) :
    StepBound K root model ρ β δ cU (.inl (.inr (.inl x))) s flag p (r0 + 1) (p + 1) := by
  have hi : K.initial x = none := initial_none_of_fresh K.initial s hinv.sat.prepared x hx
  have hsame : ∀ u l, Retained K.p l → K.SameLeaf s (s.store x u) l := fun u l hl =>
    K.sameLeaf_store u hx hi l (fun i => hA l i hl) (fun i v => hB l i v hl) (fun msg ctr => hE l msg ctr hl)
  have hfck : ∀ u f, FCk K (s.store x u) f ↔ FCk K s f := fun u => fck_store_of_not K u hx hi hnF
  have hnear : ∀ u I κ L, NearLeaf K root (s.store x u) I κ L ↔ NearLeaf K root s I κ L :=
    fun u => nearLeaf_store_of_not K root u hM
  have hbr : ¬BadR K root s := fun h => hb (Or.inr h)
  have he1 : 1 ≤ expo K ρ flag s := expo_ge_one K root ρ hN.one_le_rho hb
  refine step_firstOrder K root model ρ β δ cU hN hH s flag p r0 hinv hb hx hcs hnF hM hA ∅ 0 0
    (budgetE (expo K ρ flag s) (p + 1) r0) (by simp) ENNReal.zero_ne_top ENNReal.zero_ne_top (fun u => ?_) ?_
  · rw [expo_congr ρ flag (hsame u) (hfck u), weightA_eq,
      if_neg (fun h => hbr ((badR_congr (hsame u) (hfck u) (hnear u) (fun c => Iff.rfl)).1 h))]
    simp
  · rw [mul_zero, add_zero]
    exact kill_plain' hN hle he1

/-- **A fresh encoding of a retained key.** -/
theorem step_enc {total : ℕ} (hN : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (hH : StepHyp K model)
    (s : St) (flag : Bool) (p r0 : ℕ) (hinv : InvS K s p) (hb : ¬BadP K root s)
    {l : OtsKey} (hl : Retained K.p l) (msg : HashInput) (ctr : Counter)
    (hx : s.cache (Wots.encodingInput K.p l.1 l.2.1 l.2.2 msg ctr) = none)
    (hcs : costStep model (.inl (.inr (.inl (Wots.encodingInput K.p l.1 l.2.1 l.2.2 msg ctr)))) s =
      readOutside (Wots.encodingInput K.p l.1 l.2.1 l.2.2 msg ctr) s)
    (hle : p + r0 + 1 ≤ total) :
    StepBound K root model ρ β δ cU (.inl (.inr (.inl (Wots.encodingInput K.p l.1 l.2.1 l.2.2 msg ctr)))) s
      flag p (r0 + 1) (p + 1) := by
  set x := Wots.encodingInput K.p l.1 l.2.1 l.2.2 msg ctr with hxdef
  have hi : K.initial x = none := initial_none_of_fresh K.initial s hinv.sat.prepared x hx
  have hnF : ∀ f : FIn, x ≠ f.input K.p := fun f => enc_ne_fleaf
  have hM : ¬ForsSigner.IsMsgInput x := fun h => msg_ne_enc h rfl
  have hA : ∀ l i, Retained K.p l → ¬K.IsA l i x := fun l' i' _ hA' => Ctx.isA_ne_enc hA' l msg ctr rfl
  have hBn : ∀ l i v, ¬K.IsB l i v x := fun l' i' v' hB' => Ctx.isB_ne_enc hB' l msg ctr rfl
  have hc : ∀ u l' i', K.ContactB (s.store x u) l' i' = K.ContactB s l' i' := fun u l' i' =>
    contactB_store_of_notB K u hx hi hBn l' i'
  have haa : ∀ u l' i', K.AAns (s.store x u) l' i' = K.AAns s l' i' := fun u l' i' => by
    rw [K.aAns_store u hx hi, if_neg (fun h => hA l' i' (by
      obtain ⟨st, pay, -, h'⟩ := h
      exact absurd h' chainInput_ne_enc.symm) h)]
  have hmk : ∀ u l' i, K.Marker (s.store x u) l' i ↔ K.Marker s l' i ∨ (l' = l ∧ truncateHash u ∈ K.markSet l i) := by
    intro u l' i
    rw [K.marker_store u hx hi]
    constructor
    · rintro (h | ⟨⟨msg', ctr', he⟩, ht⟩)
      · exact Or.inl h
      · obtain ⟨rfl, -, -⟩ := enc_inj he.symm
        exact Or.inr ⟨rfl, ht⟩
    · rintro (h | ⟨rfl, ht⟩)
      · exact Or.inl h
      · exact Or.inr ⟨⟨msg, ctr, rfl⟩, ht⟩
  have hfck : ∀ u f, FCk K (s.store x u) f ↔ FCk K s f := fun u => fck_store_of_not K u hx hi hnF
  have hnear : ∀ u I κ L, NearLeaf K root (s.store x u) I κ L ↔ NearLeaf K root s I κ L :=
    fun u => nearLeaf_store_of_not K root u hM
  have hbr : ¬BadR K root s := fun h => hb (Or.inr h)
  have hwc' : ∀ u, WContact K (s.store x u) ↔ WContact K s := fun u => wContact_congr' fun l' i' _ => hc u l' i'
  have hfc' : ∀ u, FContact K (s.store x u) ↔ FContact K s := fun u => fContact_congr (hfck u)
  have hnc' : ∀ u, NearContact K root (s.store x u) ↔ NearContact K root s := fun u =>
    nearContact_congr (hfck u) (hnear u) (fun c => Iff.rfl)
  have hdead : ∀ u, Dead K (s.store x u) ↔ Dead K s := fun u => dead_congr' (fun l' i' _ => hc u l' i') (hfck u)
  -- a marker kills only together with a contact at its chain
  have hbad : ∀ u, BadR K root (s.store x u) →
      ∃ i, (K.ContactB s l i).Nonempty ∧ truncateHash u ∈ K.markSet l i := by
    intro u h
    rcases h with ⟨l', hl', hbl⟩ | hd | hn
    · rcases hbl with ⟨i, v, h1, h2⟩ | ⟨i, h1, hm'⟩ | ⟨i, i', hne, h1, h2⟩
      · rw [hc] at h1; rw [haa] at h2
        exact absurd (Or.inl ⟨l', hl', Or.inl ⟨i, v, h1, h2⟩⟩) hbr
      · rw [hc] at h1
        rcases (hmk u l' i).1 hm' with hm'' | ⟨rfl, ht⟩
        · exact absurd (Or.inl ⟨l', hl', Or.inr (Or.inl ⟨i, h1, hm''⟩)⟩) hbr
        · exact ⟨i, h1, ht⟩
      · rw [hc] at h1 h2
        exact absurd (Or.inl ⟨l', hl', Or.inr (Or.inr ⟨i, i', hne, h1, h2⟩)⟩) hbr
    · exact absurd (Or.inr (Or.inl ((hdead u).1 hd))) hbr
    · exact absurd (Or.inr (Or.inr ((hnc' u).1 hn))) hbr
  set e0 := expo K ρ flag s with he0
  have he1 : 1 ≤ e0 := expo_ge_one K root ρ hN.one_le_rho hb
  by_cases hwc : WContact K s
  · -- at the key of a WOTS contact: markers of its chain kill
    have hnfc : ¬FContact K s := fun hf => hb (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr ⟨hwc, hf⟩)))))
    have harmd : ArmedS K flag s := Or.inr (Or.inl (by
      obtain ⟨l', i', hl', hc'⟩ := hwc
      exact ⟨l', hl', Or.inr ⟨i', hc'⟩⟩))
    have he66 : e0 = 66 := by
      rw [he0]; unfold expo; rw [if_pos harmd, if_pos hwc, if_neg hnfc]; norm_num
    set S : Finset Digest := Finset.univ.filter fun t => ∃ i, (K.ContactB s l i).Nonempty ∧ t ∈ K.markSet l i
      with hSdef
    have hS : (S.card : ℝ≥0∞) ≤ 63 := by
      by_cases hex : ∃ i, (K.ContactB s l i).Nonempty
      · obtain ⟨i0, hi0⟩ := hex
        have hsub : S ⊆ K.markSet l i0 := by
          intro t ht
          simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at ht
          obtain ⟨i, hi, ht⟩ := ht
          by_cases hii : i = i0
          · rw [← hii]; exact ht
          · exact absurd (Or.inl ⟨l, hl, Or.inr (Or.inr ⟨i, i0, hii, hi, hi0⟩)⟩) hbr
        calc (S.card : ℝ≥0∞) ≤ (K.markSet l i0).card := by exact_mod_cast Finset.card_le_card hsub
          _ ≤ 63 := K.markSet_card l i0
      · have : S = ∅ := by
          ext t
          simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
          rintro ⟨i, hi, -⟩
          exact hex ⟨i, hi⟩
        rw [this]; simp
    refine step_firstOrder K root model ρ β δ cU hN hH s flag p r0 hinv hb hx hcs hnF hM hA S 63
      (budgetE 66 (p + 1) r0) (budgetE 66 (p + 1) r0) hS ENNReal.ofReal_ne_top (by norm_num) (fun u => ?_) ?_
    · have hexp : expo K ρ flag (s.store x u) = 66 := by
        have ha' : ArmedS K flag (s.store x u) := Or.inr (Or.inl (by
          obtain ⟨l', i', hl', hc'⟩ := (hwc' u).2 hwc
          exact ⟨l', hl', Or.inr ⟨i', hc'⟩⟩))
        unfold expo; rw [if_pos ha', if_pos ((hwc' u).2 hwc), if_neg (fun h => hnfc ((hfc' u).1 h))]; norm_num
      rw [hexp]
      by_cases ht : truncateHash u ∈ S
      · rw [if_pos ht]; exact le_add_self
      · rw [if_neg ht, add_zero, weightA_eq, if_neg]
        intro h
        obtain ⟨i, hi, hm⟩ := hbad u h
        exact ht (by simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨i, hi, hm⟩)
    · rw [show expo K ρ flag s = 66 from he66]
      have hk := kill_enc66 hN hle
      have hfin : ν * budgetE 66 (p + 1) r0 ≠ ⊤ := ENNReal.mul_ne_top ν_ne_top ENNReal.ofReal_ne_top
      rw [← ENNReal.add_le_add_iff_right hfin, ← add_mul, one_sub_nu_add, one_mul]
      calc budgetE 66 p (r0 + 1) + 63 * ν * budgetE 66 (p + 1) r0 + ν * budgetE 66 (p + 1) r0
          = budgetE 66 p (r0 + 1) + 64 * ν * budgetE 66 (p + 1) r0 := by ring
        _ ≤ _ := hk
  · have hcnil : ∀ l' i', Retained K.p l' → K.ContactB s l' i' = ∅ := fun l' i' hl' =>
      Set.eq_empty_iff_forall_notMem.2 fun v hv => hwc ⟨l', i', hl', v, hv⟩
    have hnb : ∀ u, ¬BadR K root (s.store x u) := fun u h => by
      obtain ⟨i, hi, -⟩ := hbad u h
      rw [hcnil l i hl] at hi
      exact Set.not_nonempty_empty hi
    by_cases harmd : ArmedS K flag s
    · -- armed without contact: markers are harmless
      refine step_firstOrder K root model ρ β δ cU hN hH s flag p r0 hinv hb hx hcs hnF hM hA ∅ 0 0
        (budgetE e0 (p + 1) r0) (by simp) ENNReal.zero_ne_top ENNReal.zero_ne_top (fun u => ?_) ?_
      · have hexp : expo K ρ flag (s.store x u) = e0 := by
          have ha' : ArmedS K flag (s.store x u) := by
            rcases harmd with h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl (armedW_mono (extends_store s x u hx) h))
            · exact Or.inr (Or.inr ((hfc' u).2 h))
          rw [he0]; unfold expo
          rw [if_pos ha', if_pos harmd, hwc' u, hfc' u]
        rw [hexp, weightA_eq, if_neg (hnb u)]
        simp
      · rw [mul_zero, add_zero]
        exact kill_plain' hN hle he1
    · -- unarmed: a marker arms (exponent ρ → 2), E1
      have heρ : e0 = ρ := expo_unarmed K ρ harmd
      have hnfc : ¬FContact K s := fun hf => harmd (Or.inr (Or.inr hf))
      have hle2 : budgetE 2 (p + 1) r0 ≤ budgetE ρ (p + 1) r0 :=
        budgetE_anti_exp (by linarith [hN.low]) hN.high (p + 1) r0
          (by have := sw_lt hN hle; push_cast; linarith)
      refine step_firstOrder K root model ρ β δ cU hN hH s flag p r0 hinv hb hx hcs hnF hM hA (K.markAll l) 4032
        (budgetE ρ (p + 1) r0 - budgetE 2 (p + 1) r0) (budgetE ρ (p + 1) r0) (K.markAll_card l)
        (ENNReal.sub_ne_top ENNReal.ofReal_ne_top) (by norm_num) (fun u => ?_) ?_
      · rw [weightA_eq, if_neg (hnb u)]
        by_cases ht : truncateHash u ∈ K.markAll l
        · obtain ⟨i, hi⟩ := (markAll_mem_iff K l (truncateHash u)).1 ht
          have ha' : ArmedS K flag (s.store x u) :=
            Or.inr (Or.inl ⟨l, hl, Or.inl ⟨i, (hmk u l i).2 (Or.inr ⟨rfl, hi⟩)⟩⟩)
          have hexp : expo K ρ flag (s.store x u) = 2 := by
            unfold expo
            rw [if_pos ha', if_neg (fun h => hwc ((hwc' u).1 h)), if_neg (fun h => hnfc ((hfc' u).1 h))]
            norm_num
          simp only [ht, if_true]
          rw [hexp, ← add_mul, add_tsub_cancel_of_le hle2]
        · have hm' : ∀ l' i', Retained K.p l' → (K.Marker (s.store x u) l' i' ↔ K.Marker s l' i') := by
            intro l' i' _
            rw [hmk u l' i']
            constructor
            · rintro (h | ⟨-, h'⟩)
              · exact h
              · exact absurd ((markAll_mem_iff K l (truncateHash u)).2 ⟨i', h'⟩) ht
            · exact Or.inl
          have hexp : expo K ρ flag (s.store x u) = ρ := by
            rw [expo_congr' ρ flag (fun l' i' _ => hc u l' i') hm' (hfck u)]
            exact heρ
          simp only [ht, if_false, add_zero]
          rw [hexp]
      · rw [show expo K ρ flag s = ρ from heρ]
        have h1 := swR1 hN p r0 hle
        have h4032 : ENNReal.ofReal (4032 / 2 ^ 128) = 4032 * ν := by
          rw [← nu_eq_ofReal', ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
        rw [h4032] at h1
        have hfin : 4032 * ν * budgetE 2 (p + 1) r0 ≠ ⊤ :=
          ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ν_ne_top) ENNReal.ofReal_ne_top
        rw [← ENNReal.add_le_add_iff_right hfin]
        calc budgetE ρ p (r0 + 1) + 4032 * ν * (budgetE ρ (p + 1) r0 - budgetE 2 (p + 1) r0) +
              4032 * ν * budgetE 2 (p + 1) r0
            = budgetE ρ p (r0 + 1) + 4032 * ν * budgetE ρ (p + 1) r0 := by
              rw [add_assoc, ← mul_add, tsub_add_cancel_of_le hle2]
          _ ≤ _ := h1

/-- **A fresh FORS leaf query whose secret is known**: an unrecorded contact kills. -/
theorem step_flq_noguess {total : ℕ} (hN : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (hH : StepHyp K model)
    (f : FIn) (s : St) (flag : Bool) (p r0 : ℕ) (hinv : InvS K s p) (hb : ¬BadP K root s)
    (hx : s.cache (f.input K.p) = none) (canonical : Digest) (hk : s.known f.inC = some canonical)
    (hne : f.v ≠ canonical) (hle : p + r0 + 1 ≤ total) :
    StepBound K root model ρ β δ cU (flq K f) s flag p (r0 + 1) (p + 1) := by
  set x := f.input K.p with hxdef
  have hcs : costStep model (flq K f) s = readOutside x s := by
    rw [costStep_inl]
    exact lazyStep_other model x s (Address.fleaf f.index f.κ f.leaf, f.v)
      (by rw [hH.parse]; exact parse_fleaf K f) canonical (by rw [hH.incoming]; exact hk) hne
  have hi : K.initial x = none := hH.fleaf f
  have hkind : K.tg.kind x = .none := hH.sec x (Or.inr ⟨f.index, f.κ, f.leaf, f.v, rfl⟩)
  have hM : ¬ForsSigner.IsMsgInput x := not_msg_fleaf K f
  have hw : weightA K root s = weight K.tg K.initial s := weightA_eq_weight_of K root hb
  have hknone : s.known f.inC ≠ none := by rw [hk]; simp
  have hnm : ¬NearMiss K root s f := fun h => hknone h.2
  have hsame : ∀ u, ∀ l, Retained K.p l → K.SameLeaf s (s.store x u) l := fun u =>
    sameLeaf_store_fleaf K u hx hi rfl
  have hnear : ∀ u I κ L, NearLeaf K root (s.store x u) I κ L ↔ NearLeaf K root s I κ L :=
    fun u => nearLeaf_store_of_not K root u hM
  have hfck : ∀ u g, FCk K (s.store x u) g ↔ FCk K s g ∨ (g = f ∧ truncateHash u = K.F f.outC) := by
    intro u g
    rw [fck_store K u hx hi g]
    constructor
    · rintro (h | ⟨hxg, ht⟩)
      · exact Or.inl h
      · have : g = f := fleaf_inj hxg.symm
        subst this
        exact Or.inr ⟨rfl, ht⟩
    · rintro (h | ⟨rfl, ht⟩)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, ht⟩
  have hweight : ∀ u, weight K.tg K.initial (s.store x u) = weight K.tg K.initial s := fun u =>
    weight_store_untargetedW K.tg K.initial s x u hkind
  have hbr : ¬BadR K root s := fun h => hb (Or.inr h)
  set e0 := expo K ρ flag s with he0
  have hnocontact : ∀ u, truncateHash u ≠ K.F f.outC →
      weightA K root (s.store x u) = weight K.tg K.initial s ∧ expo K ρ flag (s.store x u) = e0 := by
    intro u ht
    have hf' : ∀ g, FCk K (s.store x u) g ↔ FCk K s g := fun g => by
      rw [hfck u g]
      exact ⟨fun h => h.resolve_right fun h' => ht h'.2, Or.inl⟩
    refine ⟨?_, expo_congr ρ flag (hsame u) hf'⟩
    rw [weightA_eq, hweight, if_neg (fun h => hbr ((badR_congr (hsame u) hf' (hnear u) (fun c => Iff.rfl)).1 h))]
  have hP : ∀ u, weightA K root (s.store x u) * pendA K (s.store x u) ≤ weightA K root s * pendA K s + 0 := by
    intro u
    rw [add_zero, hw]
    refine mul_le_mul' ((weightA_le_weight K root _).trans (le_of_eq (hweight u))) ?_
    unfold pendA
    rw [wContact_congr (hsame u)]
    split_ifs
    · exact le_rfl
    · gcongr
      exact K.uaSet_store_of_not u hx hi fun l i _ hA => Ctx.isA_ne_fleaf hA f rfl
  have hpay0 : ENNReal.ofReal (β / 2 ^ 128) * payF K root s (flq K f) +
      ENNReal.ofReal (cU / 2 ^ 128) * payC K root s (flq K f) ≤ 0 * weightA K root s := by
    rw [payF_flq K root hH.digest, payC_flq, if_neg (fun h => hknone h.1)]
    simp
  have harm0 : budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s ≤
      budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s + ENNReal.ofReal δ * payA K root flag s (flq K f) :=
    le_self_add
  have hnf : nextFlag K root flag s (flq K f) = flag := nextFlag_flq_of_not K root flag s f hnm
  have he1 : 1 ≤ e0 := expo_ge_one K root ρ hN.one_le_rho hb
  set G : Digest → ℝ≥0∞ := fun t => if t = K.F f.outC then 0 else budgetE e0 (p + 1) r0 with hG
  have hmean : meanD G + ν * budgetE e0 (p + 1) r0 = budgetE e0 (p + 1) r0 + ν * 0 := meanD_two _ _ _
  rw [mul_zero, add_zero] at hmean
  have hR : budgetE e0 p (r0 + 1) + 0 + 1 * (ν * budgetE e0 (p + 1) r0) ≤
      1 * meanD G + 1 * (ν * budgetE e0 (p + 1) r0) := by
    simp only [one_mul, add_zero]
    rw [hmean]
    exact kill_plain hN hle he1
  refine stepBound_fresh K root model ρ β δ cU s s x hcs hx flag p r0 (p + 1)
    (budgetE e0 p (r0 + 1)) 0 0 harm0 hpay0 hP ?_
  rw [add_zero, hnf]
  refine le_trans (finish_guess (g := 1) (W0 := weightA K root s) (by rw [one_mul]) hR
    (by rw [one_mul]; exact ENNReal.mul_ne_top ν_ne_top ENNReal.ofReal_ne_top)) ?_
  rw [← meanD_mul']
  refine meanD_le_of_pointwise _ _ fun u => ?_
  simp only [hG]
  by_cases ht : truncateHash u = K.F f.outC
  · rw [if_pos ht, mul_zero]; exact bot_le
  · rw [if_neg ht]
    obtain ⟨h1, h2⟩ := hnocontact u ht
    rw [h1, h2, hw, mul_comm]

/-- **A fresh digest block**: the decrement pays the digest baseline; a kill is booked. -/
theorem step_digest_fresh {total : ℕ} (hN : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (hH : StepHyp K model)
    (s : St) (flag : Bool) (p r0 : ℕ) (hinv : InvS K s p) (hb : ¬BadP K root s) {x : HashInput}
    (hx : s.cache x = none) (hd : ForsSigner.IsMsgInput x)
    (hcs : costStep model (.inl (.inr (.inl x))) s = readOutside x s) (hle : p + r0 + 1 ≤ total) :
    StepBound K root model ρ β δ cU (.inl (.inr (.inl x))) s flag p (r0 + 1) p := by
  have hi : K.initial x = none := initial_none_of_fresh K.initial s hinv.sat.prepared x hx
  have hkind : K.tg.kind x = .none := hH.msg x hd
  have hnF : ∀ f : FIn, x ≠ f.input K.p := fleaf_not_msg K hd
  have hnQ : ¬IsFLQ K (.inl (.inr (.inl x))) := fun h => by
    obtain ⟨f, hf⟩ := (isFLQ_ordinary_iff K x).1 h
    exact hnF f hf
  have hw : weightA K root s = weight K.tg K.initial s := weightA_eq_weight_of K root hb
  have hsame : ∀ u, ∀ l, Retained K.p l → K.SameLeaf s (s.store x u) l := fun u =>
    sameLeaf_store_msg K u hx hi hd
  have hfck : ∀ u f, FCk K (s.store x u) f ↔ FCk K s f := fun u => fck_store_of_not K u hx hi hnF
  have hweight : ∀ u, weight K.tg K.initial (s.store x u) = weight K.tg K.initial s := fun u =>
    weight_store_untargetedW K.tg K.initial s x u hkind
  have hbr : ¬BadR K root s := fun h => hb (Or.inr h)
  have hnc : ¬NearContact K root s := fun h => hbr (Or.inr (Or.inr h))
  have hnf : nextFlag K root flag s (.inl (.inr (.inl x))) = flag := nextFlag_of_not K root flag s _ hnQ
  unfold StepBound
  rw [show sourceCost (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inr (.inl x))) = 1 from rfl,
    Nat.add_sub_cancel, tsum_costStep_fresh model s s x hcs hx, tsum_costStep_fresh model s s x hcs hx,
    tsum_costStep_fresh model s s x hcs hx, hnf, payF_ordinary, hH.digest, if_pos hd, payC_of_not K root s _ hnQ,
    payA_of_not K root flag s _ hnQ, mul_zero, add_zero, mul_zero, add_zero]
  set e0 := expo K ρ flag s with he0
  have hexp : ∀ u, expo K ρ flag (s.store x u) = e0 := fun u => expo_congr ρ flag (hsame u) (hfck u)
  -- the weight after: unchanged, or a kill booked in WK
  have hpt : ∀ u, budgetE e0 p r0 * weightA K root s ≤
      budgetE e0 p r0 * weightA K root (s.store x u) + payK K root s (.inl (.inr (.inl x))) (s.store x u) := by
    intro u
    by_cases hn : NearContact K root (s.store x u)
    · have hk : payK K root s (.inl (.inr (.inl x))) (s.store x u) = weightA K root s := by
        unfold payK; rw [if_pos ⟨hnQ, hn, hnc⟩]
      rw [hk]
      refine le_trans ?_ le_add_self
      refine mul_le_of_le_one_left' (budgetE_le_one (expo_nonneg K ρ (by linarith [hN.low]) flag s) p r0 ?_)
      have := sw_lt hN hle; push_cast; linarith
    · have : weightA K root (s.store x u) = weightA K root s := by
        rw [weightA_eq, hweight, hw, if_neg]
        rintro (hw' | hd' | hn')
        · exact hbr (Or.inl ((wotsBad_congr (hsame u)).1 hw'))
        · exact hbr (Or.inr (Or.inl ((dead_congr (hsame u) (hfck u)).1 hd')))
        · exact hn hn'
      rw [this]
      exact le_self_add
  have hP : ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (weightA K root (s.store x u) * pendA K (s.store x u)) ≤ weightA K root s * pendA K s := by
    refine tsum_le_const_of_pointwise _ _ _ fun u => ?_
    refine mul_le_mul' ?_ ?_
    · rw [hw]; exact (weightA_le_weight K root _).trans (le_of_eq (hweight u))
    · unfold pendA
      rw [wContact_congr (hsame u)]
      split_ifs
      · exact le_rfl
      · gcongr
        exact K.uaSet_store_of_not u hx hi fun l i _ hA => by
          obtain ⟨st, pay, -, rfl⟩ := hA
          exact msg_ne_chain hd rfl
  have hdec := dec_expo_add K root hN (flag := flag) hb p r0 hle
  calc budgetE e0 p (r0 + 1) * weightA K root s + ENNReal.ofReal (β / 2 ^ 128) * weightA K root s +
        ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * (weightA K root (s.store x u) * pendA K (s.store x u))
      ≤ budgetE e0 p r0 * weightA K root s + weightA K root s * pendA K s := by
        rw [← add_mul]
        exact add_le_add (mul_le_mul_left hdec _) hP
    _ ≤ ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (budgetE e0 p r0 * weightA K root (s.store x u) + payK K root s (.inl (.inr (.inl x))) (s.store x u)) +
        weightA K root s * pendA K s :=
        add_le_add (const_le_tsum_of_support _ (tsum_probOutput_eq_one' (probFailure_uniformSample _)) _ _
          fun u _ => hpt u) le_rfl
    _ = _ := by
        simp only [hexp, mul_add, ENNReal.tsum_add]
        ring

end First

end FORS.Security.SWRoute
