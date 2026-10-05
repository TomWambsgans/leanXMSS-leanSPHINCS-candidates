import LeanSphincs.BridgeForsGeneric
import LeanSphincs.H0BoundOnce

/-! The near witness: the number of ways a target view is covered by the disclosed views at every
tree but one, summed over the free tree. It is monotone and supermodular, positive on a near
covered target, and its fresh-digest price is `24 2^-256 Σ_l cnt_l^23`. The one-coin H-term of
that price is at most `24 2^-256 2^b T_23(μ)` at the Poisson rate `μ` of the one-coin future, and a
rational check bounds it for every budget of a range. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### The near witness -/

/-- Covers of a target at every tree but `free`. -/
def nearAt (target : View) (free : FtsTree) (disclosed : Multiset View) : ℕ :=
  ∏ tree ∈ Finset.univ.erase free, matchCount target tree disclosed

/-- **The near witness count.** -/
def nearCount (target : View) (disclosed : Multiset View) : ℕ :=
  ∑ free, nearAt target free disclosed

/-- The near witness as a value. -/
noncomputable def witnessNear (v : View) (D : Multiset View) : ℝ≥0∞ := (nearCount v D : ℝ≥0∞)

theorem nearAt_mono (target : View) (free : FtsTree) {small large : Multiset View} (hle : small ≤ large) :
    nearAt target free small ≤ nearAt target free large :=
  Finset.prod_le_prod' fun tree _ => matchCount_mono target tree hle

theorem nearAt_super (target : View) (free : FtsTree) (small large extra : Multiset View) (hle : small ≤ large) :
    nearAt target free (small + extra) + nearAt target free large ≤
      nearAt target free (large + extra) + nearAt target free small := by
  have h := prod_increasing_differences (Finset.univ.erase free) (fun t => matchCount target t small)
    (fun t => matchCount target t large) (fun t => matchCount target t extra)
    (fun t => matchCount_mono target t hle)
  simp only [nearAt, matchCount_add]
  exact h

theorem witnessNear_props : WitnessProps witnessNear := by
  intro v
  refine ⟨fun small large hle => ?_, fun small large extra hle => ?_, fun _ => ENNReal.natCast_ne_top _⟩
  · show (nearCount v small : ℝ≥0∞) ≤ (nearCount v large : ℝ≥0∞)
    exact Nat.cast_le.mpr (Finset.sum_le_sum fun free _ => nearAt_mono v free hle)
  · show (nearCount v (small + extra) : ℝ≥0∞) + (nearCount v large : ℝ≥0∞) ≤
      (nearCount v (large + extra) : ℝ≥0∞) + (nearCount v small : ℝ≥0∞)
    rw [← Nat.cast_add, ← Nat.cast_add]
    refine Nat.cast_le.mpr ?_
    simp only [nearCount, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun free _ => nearAt_super v free small large extra hle

/-- A digest covered by the disclosures at every tree but one has a positive near count. -/
theorem nearCount_pos {R : List Coordinate} {d : Multiset View} (hD : DInv R d) (digest : MessageDigest)
    (free : FtsTree)
    (hnear : ∀ tree, tree ≠ free → digestLeaves digest tree ∈ HiddenBridge.revealedSet R (digestIndex digest) tree) :
    1 ≤ nearCount (Lifetime.localDigestView digest) d := by
  refine le_trans ?_ (Finset.single_le_sum (f := fun t => nearAt (Lifetime.localDigestView digest) t d)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ free))
  refine Finset.one_le_prod' fun t ht => ?_
  have hmem := hnear t (Finset.ne_of_mem_erase ht)
  simp only [HiddenBridge.revealedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  obtain ⟨w, hw, h1, h2⟩ := hD _ _ _ hmem
  unfold matchCount
  refine Multiset.card_pos.2 fun hzero => ?_
  have : w ∈ d.filter fun view => view.1 = (Lifetime.localDigestView digest).1 ∧
      view.2 t = (Lifetime.localDigestView digest).2 t :=
    Multiset.mem_filter.2 ⟨hw, by rw [localDigestView_fst, localDigestView_snd]; exact ⟨h1, h2⟩⟩
  rw [hzero] at this
  exact absurd this (Multiset.notMem_zero _)

end LeanSphincs.Security.ForsPotential

namespace LeanSphincs.Security.H0

open Concrete Domination ForsPrice ForsPotential

set_option exponentiation.threshold 512
set_option linter.unusedSectionVars false

/-! ### Count form of the near price -/

section Count

variable [Params]

theorem card_ftsLeaf : Fintype.card FtsLeaf = 2 ^ 10 := by
  show Fintype.card (Fin (2 ^ ftsTreeHeight)) = 2 ^ 10
  rw [Fintype.card_fin]
  rfl

/-- The near counts summed over all targets. -/
theorem sum_nearCount (D : Multiset View) :
    ∑ target : View, nearCount target D = 24 * (2 ^ 10 * ∑ l : Fin (2 ^ subtreeHeight), (cnt Prod.fst D l) ^ 23) := by
  have hfib : ∀ (l : Fin (2 ^ subtreeHeight)) (t : IndexGroup),
      ∑ a : FtsLeaf, (D.filter fun v : View => v.1 = l ∧ v.2 t = a).card = cnt Prod.fst D l := by
    intro l t
    have h := sum_card_filter_eq (fun v : View => v.2 t) (D.filter fun v : View => v.1 = l)
    unfold cnt
    rw [← h]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Multiset.filter_filter]
    exact congrArg Multiset.card (Multiset.filter_congr fun v _ => and_comm)
  have hone : ∀ (l : Fin (2 ^ subtreeHeight)) (free : IndexGroup),
      ∑ r : IndexGroup → FtsLeaf, nearAt (l, r) free D = 2 ^ 10 * cnt Prod.fst D l ^ 23 := by
    intro l free
    set g : IndexGroup → FtsLeaf → ℕ := fun t a =>
      if t = free then 1 else (D.filter fun v : View => v.1 = l ∧ v.2 t = a).card with hg
    have hpt : ∀ r : IndexGroup → FtsLeaf, nearAt (l, r) free D = ∏ t, g t (r t) := by
      intro r
      rw [← Finset.mul_prod_erase Finset.univ (fun t => g t (r t)) (Finset.mem_univ free)]
      simp only [hg, if_pos rfl, one_mul]
      refine Finset.prod_congr rfl fun t ht => ?_
      rw [if_neg (Finset.ne_of_mem_erase ht)]
      rfl
    simp only [hpt]
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
    rw [← Finset.mul_prod_erase Finset.univ (fun t => ∑ a, g t a) (Finset.mem_univ free)]
    simp only [hg, if_pos rfl, Finset.sum_const, Finset.card_univ, card_ftsLeaf, smul_eq_mul, mul_one]
    congr 1
    calc ∏ t ∈ Finset.univ.erase free, ∑ a, (if t = free then 1 else
          (D.filter fun v : View => v.1 = l ∧ v.2 t = a).card)
        = ∏ _t ∈ Finset.univ.erase free, cnt Prod.fst D l := by
          refine Finset.prod_congr rfl fun t ht => ?_
          simp only [if_neg (Finset.ne_of_mem_erase ht)]
          exact hfib l t
      _ = _ := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
          rfl
  calc ∑ target : View, nearCount target D
      = ∑ free : IndexGroup, ∑ target : View, nearAt target free D := by
        unfold nearCount; rw [Finset.sum_comm]
    _ = ∑ _free : IndexGroup, 2 ^ 10 * ∑ l : Fin (2 ^ subtreeHeight), cnt Prod.fst D l ^ 23 := by
        refine Finset.sum_congr rfl fun free _ => ?_
        rw [Fintype.sum_prod_type, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => hone l free
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ]
        rfl

/-- The scale of the near count price. -/
noncomputable def kappaNear : ℝ≥0∞ := 24 * ((2 : ℝ≥0∞) ^ 256)⁻¹

/-- **Count form of the near price.** -/
theorem priceNear_eq (D : Multiset View) :
    priceW witnessNear D = ∑ l : Fin (2 ^ subtreeHeight), kappaNear * (cnt Prod.fst D l : ℝ≥0∞) ^ 23 := by
  unfold priceW freshAvg witnessNear
  have hsum : ∑ target ∈ (Finset.univ : Finset View), (nearCount target D : ℝ≥0∞) =
      24 * (2 ^ 10 * ∑ l : Fin (2 ^ subtreeHeight), ((cnt Prod.fst D l : ℝ≥0∞)) ^ 23) := by
    rw [← Nat.cast_sum, sum_nearCount]; push_cast; ring
  rw [hsum, Finset.card_univ, card_view, ← Finset.mul_sum]
  have hb := (inferInstance : Params).subtreeHeight_le
  have h26 : (2 : ℝ≥0∞) ^ 266 = ((2 ^ (totalHeight - subtreeHeight) : ℕ) : ℝ≥0∞) *
      ((2 ^ subtreeHeight * 2 ^ 240 : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_mul, ← pow_add, ← pow_add]
    have : totalHeight - subtreeHeight + (subtreeHeight + 240) = 266 := by
      unfold totalHeight at hb ⊢; omega
    rw [this, Nat.cast_pow, Nat.cast_ofNat]
  have hA : ((2 ^ (totalHeight - subtreeHeight) : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  have hB : ((2 ^ (totalHeight - subtreeHeight) : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hinv : landing * ((2 ^ subtreeHeight * 2 ^ 240 : ℕ) : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0∞) ^ 266)⁻¹ := by
    unfold landing
    rw [h26, ENNReal.mul_inv (Or.inl hA) (Or.inl hB)]
  have h2 : ((2 : ℝ≥0∞) ^ 266)⁻¹ = ((2 : ℝ≥0∞) ^ 256)⁻¹ * ((2 : ℝ≥0∞) ^ 10)⁻¹ := by
    rw [show (2 : ℝ≥0∞) ^ 266 = 2 ^ 256 * 2 ^ 10 by rw [← pow_add],
      ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero)) (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))]
  have h10 : ((2 : ℝ≥0∞) ^ 10)⁻¹ * 2 ^ 10 = 1 :=
    ENNReal.inv_mul_cancel (by positivity) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hscale : landing * ((2 ^ subtreeHeight * 2 ^ 240 : ℕ) : ℝ≥0∞)⁻¹ * (24 * 2 ^ 10) = kappaNear := by
    rw [hinv, h2]
    unfold kappaNear
    calc ((2 : ℝ≥0∞) ^ 256)⁻¹ * ((2 : ℝ≥0∞) ^ 10)⁻¹ * (24 * 2 ^ 10)
        = 24 * ((2 : ℝ≥0∞) ^ 256)⁻¹ * (((2 : ℝ≥0∞) ^ 10)⁻¹ * 2 ^ 10) := by ring
      _ = _ := by rw [h10, mul_one]
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc]
  rw [show landing * (((2 ^ subtreeHeight * 2 ^ 240 : ℕ) : ℝ≥0∞))⁻¹ * 24 * 2 ^ 10 =
    landing * ((2 ^ subtreeHeight * 2 ^ 240 : ℕ) : ℝ≥0∞)⁻¹ * (24 * 2 ^ 10) by ring, hscale]

end Count

/-! ### The one-coin H-term of the near price -/

section HTerm

variable {V ι : Type} [DecidableEq ι] [Fintype ι] (idx : V → ι)

/-- **One count power.** The one-coin H-term of `cnt_l^n` is at most the Touchard polynomial at the
Poisson rate. -/
theorem hTermO_cnt_pow_le (U : Finset V) (hU : UniformIndex idx U) (hUne : U.Nonempty) (l : ι) (n K : ℕ)
    (hnK : n ≤ K + 1) (N q : ℕ) (hN : 1 ≤ N) (α w lam γ : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1)
    (hL : (Fintype.card ι : ℝ≥0∞) ≠ 0) (hLα : 1 ≤ (Fintype.card ι : ℝ≥0∞) * α)
    (hγ : lam * w * (1 + w * Fintype.card ι) ^ K ≤ Fintype.card ι * γ) :
    hTermO U w lam N q (fun d => (cnt idx d l : ℝ≥0∞) ^ n) ≤ touchard n ((N : ℝ≥0∞) * α + q * γ) := by
  classical
  have hexp : ∀ d : Multiset V, (cnt idx d l : ℝ≥0∞) ^ n =
      ∑ j ∈ Finset.range (n + 1), (Nat.stirlingSecond n j : ℝ≥0∞) * fallMono idx (Pi.single l j) d := by
    intro d
    have h := SphincsSecurity.Concrete.power_eq_stirling_descFactorial (cnt idx d l) n
    have hmono : ∀ j, fallMono idx (Pi.single l j) d = ((cnt idx d l).descFactorial j : ℝ≥0∞) := by
      intro j
      unfold fallMono
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l)]
      rw [Finset.prod_eq_one (fun l' hl' => by
        rw [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hl'), Nat.descFactorial_zero, Nat.cast_one]),
        mul_one, Pi.single_eq_same]
    simp only [hmono]
    exact_mod_cast h
  simp only [hexp]
  rw [hTermO_sum U hUne w lam hw hlam N q]
  unfold touchard
  gcongr with j hj
  have hjK : ∀ l', (Pi.single l j : ι → ℕ) l' ≤ K + 1 := by
    intro l'
    have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    by_cases hl' : l' = l
    · subst hl'; rw [Pi.single_eq_same]; omega
    · rw [Pi.single_eq_of_ne hl']; omega
  have h := H0_fallMono_leO idx U hU (Pi.single l j) K hjK N q hN α w lam γ hw hlam hL hLα hγ
  have hs : ∑ l', (Pi.single l j : ι → ℕ) l' = j := by
    rw [Finset.sum_eq_single l (fun l' _ hl' => Pi.single_eq_of_ne hl' _) (fun h => absurd (Finset.mem_univ l) h),
      Pi.single_eq_same]
  rw [hs] at h
  exact h

end HTerm

section NearHTerm

variable [Params]

/-- **The near H-term.** -/
theorem hTermO_near_le (N q : ℕ) (hN : 1 ≤ N) (α w γ : ℝ≥0∞) (hw : w ≤ 1)
    (hLα : 1 ≤ ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞) * α)
    (hγ : landing * w * (1 + w * ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞)) ^ 22 ≤
      ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞) * γ) :
    hTermO (Finset.univ : Finset View) w landing N q (priceW witnessNear) ≤
      kappaNear * (2 ^ subtreeHeight : ℝ≥0∞) * touchard 23 ((N : ℝ≥0∞) * α + q * γ) := by
  have hL : ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hfun : priceW witnessNear = fun d : Multiset View => ∑ l ∈ (Finset.univ : Finset (Fin (2 ^ subtreeHeight))),
      kappaNear * (fun l (d : Multiset View) => (cnt Prod.fst d l : ℝ≥0∞) ^ 23) l d := by
    funext d; exact priceNear_eq d
  rw [hfun, hTermO_sum _ Finset.univ_nonempty w landing hw landing_le_one N q]
  calc ∑ l ∈ (Finset.univ : Finset (Fin (2 ^ subtreeHeight))), kappaNear *
        hTermO (Finset.univ : Finset View) w landing N q (fun d => (cnt Prod.fst d l : ℝ≥0∞) ^ 23)
      ≤ ∑ _l : Fin (2 ^ subtreeHeight), kappaNear * touchard 23 ((N : ℝ≥0∞) * α + q * γ) := by
        gcongr with l
        exact hTermO_cnt_pow_le Prod.fst Finset.univ uniformIndex_univ Finset.univ_nonempty l 23 22 le_rfl N q hN
          α w landing γ hw landing_le_one hL hLα hγ
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- The near H-term at budget `q`: the start value of the near potential's new-pair forecast. -/
noncomputable def hNearOf (q : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtualOnce Finset.univ (wbarOf q)
    (excessW witnessNear 0) signatureLimit I 0) q []

theorem hNearOf_eq (q : ℕ) :
    hNearOf q = hTermO (Finset.univ : Finset View) (wbarOf q) landing signatureLimit q (priceW witnessNear) := by
  unfold hNearOf hTermO excessW
  simp only [tsub_zero]

/-! ### The rational check -/

/-- The near H-term bound at a rate bound `μ`: `24 2^b T_23(μ) / 2^256`. -/
def nearHQ (b : ℕ) (μ : ℚ) : ℚ := 24 * 2 ^ b * touchQ 23 μ / 2 ^ 256

/-- The check: the rate bound `m / 2^64` covers the one-coin rate at the right end `qb`, and the
near H-term bound is at most `c`. -/
def checkNear (b N qb m : ℕ) (c : ℚ) : Bool :=
  decide (1 ≤ N) && decide (2 * qb ≤ 2 ^ 128) && decide (muOnceQ b N qb 1 ≤ (m : ℚ) / 2 ^ 64) &&
    decide (nearHQ b ((m : ℚ) / 2 ^ 64) ≤ c)

/-- **The near H-term for every budget of a checked range.** -/
theorem hNearOf_le_of_check (b N qb m : ℕ) (c : ℚ) (hb : subtreeHeight = b) (hNs : signatureLimit = N)
    (hc : checkNear b N qb m c = true) (q : ℕ) (hq : q ≤ qb) : hNearOf q ≤ ENNReal.ofReal (c : ℝ) := by
  simp only [checkNear, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hN1, hqb2⟩, hmu⟩, hH⟩ := hc
  have hq127 : q ≤ 2 ^ 127 := by
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    omega
  set L : ℝ≥0∞ := ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞) with hLdef
  set w := wbarOf q with hwdef
  set α : ℝ≥0∞ := L⁻¹ with hαdef
  set γ : ℝ≥0∞ := landing * w * (1 + w * L) ^ (24 * 1) / L with hγdef
  have hL0 : L ≠ 0 := by rw [hLdef]; exact_mod_cast Fintype.card_ne_zero
  have hLT : L ≠ ⊤ := ENNReal.natCast_ne_top _
  have hw1 : w ≤ 1 := (fair_of q (by omega)).le_one
  have hLα : 1 ≤ L * α := by rw [hαdef, ENNReal.mul_inv_cancel hL0 hLT]
  have hγ : landing * w * (1 + w * L) ^ 22 ≤ L * γ := by
    rw [hγdef, ENNReal.mul_div_cancel hL0 hLT]
    gcongr
    · exact le_self_add
    · norm_num
  have hNs1 : 1 ≤ signatureLimit := by rw [hNs]; exact hN1
  have hmain := hTermO_near_le signatureLimit q hNs1 α w γ hw1 hLα hγ
  set μr : ℝ := (m : ℝ) / 2 ^ 64 with hμr
  have hμr0 : 0 ≤ μr := by positivity
  have hmuR : (muOnceQ b N qb 1 : ℝ) ≤ μr := by
    have := (Rat.cast_le (K := ℝ)).mpr hmu
    push_cast at this
    exact this
  have hμ : (signatureLimit : ℝ≥0∞) * α + q * γ ≤ ENNReal.ofReal μr := by
    have h := mu_leO b N 1 q qb hb hq hqb2 μr hmuR
    rw [hαdef, hγdef, hNs]
    exact h
  have hT : touchard 23 ((signatureLimit : ℝ≥0∞) * α + q * γ) ≤
      ENNReal.ofReal (∑ j ∈ Finset.range 24, (Nat.stirlingSecond 23 j : ℝ) * μr ^ j) := by
    rw [← touchard_ofReal 23 μr hμr0]
    exact touchard_mono 23 hμ
  have hHR : (24 : ℝ) * 2 ^ b * (∑ j ∈ Finset.range 24, (Nat.stirlingSecond 23 j : ℝ) * μr ^ j) / 2 ^ 256 ≤
      (c : ℝ) := by
    unfold nearHQ at hH
    have := (Rat.cast_le (K := ℝ)).mpr hH
    push_cast [touchQ_eq] at this
    exact this
  rw [hNearOf_eq]
  refine le_trans hmain ?_
  have hk : kappaNear * (2 ^ subtreeHeight : ℝ≥0∞) = ENNReal.ofReal (24 * 2 ^ b / 2 ^ 256) := by
    unfold kappaNear
    rw [hb, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_ofNat, div_eq_mul_inv]
    ring
  rw [hk]
  calc ENNReal.ofReal (24 * 2 ^ b / 2 ^ 256) * touchard 23 ((signatureLimit : ℝ≥0∞) * α + q * γ)
      ≤ ENNReal.ofReal (24 * 2 ^ b / 2 ^ 256) *
          ENNReal.ofReal (∑ j ∈ Finset.range 24, (Nat.stirlingSecond 23 j : ℝ) * μr ^ j) := by gcongr
    _ = ENNReal.ofReal (24 * 2 ^ b / 2 ^ 256 * ∑ j ∈ Finset.range 24, (Nat.stirlingSecond 23 j : ℝ) * μr ^ j) := by
        rw [ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (c : ℝ) := by
        apply ENNReal.ofReal_le_ofReal
        calc (24 * 2 ^ b / 2 ^ 256 : ℝ) * ∑ j ∈ Finset.range 24, (Nat.stirlingSecond 23 j : ℝ) * μr ^ j
            = (24 : ℝ) * 2 ^ b * (∑ j ∈ Finset.range 24, (Nat.stirlingSecond 23 j : ℝ) * μr ^ j) / 2 ^ 256 := by
              ring
          _ ≤ (c : ℝ) := hHR

end NearHTerm

end LeanSphincs.Security.H0
