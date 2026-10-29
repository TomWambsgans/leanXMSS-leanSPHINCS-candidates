import FORS.SWRoute.ForecastDomE
import FORS.SWRoute.ForecastPot

/-! **The domination of the own-cell forecast, part F: one cached pair and the fresh part.**

* `candValueG_le`: the forecast of a cached pair at the cell, with `r` trees missing from the
  disclosures at the index, is at most `φ(r) + coinR(r)` (the uniform future covers the missing
  trees with mean `φ`, the group coins of the other cached pairs add `coinR`);
* `khValueG_le`: `k` times the excess forecast of a new pair is at most `freshK` at the rate
  `μ + δ` (`δ` bounds the group coins of the cached pairs at the index);
* pattern counts: `PatOK` (no pattern is selected by more unsigned cached pairs than its cap) bounds
  the matching selectable pairs. -/

open OracleComp OracleSpec ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base FORS.Base.Domination FORS.Base.H0 FORS.Security.H0Avg ForsPrice Concrete GraphView
  ForsPotential FORS.LoopWalk

set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### Pattern counts -/

section Patterns

variable (parameter : PublicParameter) (data : PublicData) (s : State)

/-- **No pattern over its cap**: the negation of the pattern part's failure. -/
def PatOK (q : ℕ) (L : QueryLog SigningSpec) (P : List Pair) : Prop :=
  ∀ (I : Fin (2 ^ subtreeHeight)) (S : Pat), 1 ≤ patSize S →
    ((P.filter fun p => decide (Unsigned L p)).filter
      fun p => decide (PatCovers I S (pview parameter data s p))).length ≤ patCap q (patSize S)

/-- The pattern of the leaves `ℓ` on the trees of `B`. -/
def patOf (ℓ : FTree → FLeaf) (B : Finset FTree) : Pat := fun κ => if κ ∈ B then some (ℓ κ) else none

theorem patSize_patOf (ℓ : FTree → FLeaf) (B : Finset FTree) : patSize (patOf ℓ B) = B.card := by
  unfold patSize patOf
  congr 1
  ext κ
  by_cases h : κ ∈ B <;> simp [h]

theorem patCovers_patOf {I : Fin (2 ^ subtreeHeight)} {ℓ : FTree → FLeaf} {B : Finset FTree} {u : View}
    (h1 : u.1 = I) (h2 : ∀ κ' ∈ B, u.2 κ' = ℓ κ') : PatCovers I (patOf ℓ B) u := by
  refine ⟨h1, fun κ l hκ => ?_⟩
  unfold patOf at hκ
  by_cases h : κ ∈ B
  · rw [if_pos h, Option.some.injEq] at hκ
    rw [← hκ]; exact h2 κ h
  · rw [if_neg h] at hκ; cases hκ

/-- A selectable pair of a live message is an unsigned cached pair. -/
theorem hit_mem {P : List Pair} (hP : PInv parameter data s P) (L : QueryLog SigningSpec) (Ms : List Message)
    (excl : Pair → Prop) {g : Pair} (hg : g ∈ (live L Ms).toFinset ×ˢ (Finset.univ : Finset Randomness))
    (hh : HitP parameter data s excl g) : g ∈ P ∧ Unsigned L g := by
  refine ⟨(hP.mem g).2 (landedIn_of_stOf_hit hh.1), ?_⟩
  have hm := (Finset.mem_product.1 hg).1
  rw [List.mem_toFinset, mem_live] at hm
  intro entry he sig _ h
  exact hm.2 entry he h.1

/-- **A finite set of unsigned cached pairs covering a pattern** has at most the pattern's cap. -/
theorem card_le_patCap {q : ℕ} {L : QueryLog SigningSpec} {P : List Pair} (hok : PatOK parameter data s q L P)
    {I : Fin (2 ^ subtreeHeight)} {S : Pat} (hS : 1 ≤ patSize S) {Z : Finset Pair}
    (hZ : ∀ g ∈ Z, g ∈ P ∧ Unsigned L g ∧ PatCovers I S (pview parameter data s g)) :
    Z.card ≤ patCap q (patSize S) := by
  refine le_trans ?_ (hok I S hS)
  refine le_trans (Finset.card_le_card (t := ((P.filter fun p => decide (Unsigned L p)).filter
    fun p => decide (PatCovers I S (pview parameter data s p))).toFinset) ?_) (List.toFinset_card_le _)
  intro g hg
  obtain ⟨h1, h2, h3⟩ := hZ g hg
  rw [List.mem_toFinset, List.mem_filter, List.mem_filter]
  exact ⟨⟨h1, by simpa using h2⟩, by simpa using h3⟩

theorem matchSet_card_le {q : ℕ} {L : QueryLog SigningSpec} {P : List Pair} (hP : PInv parameter data s P)
    (hok : PatOK parameter data s q L P) (Ms : List Message) (excl : Pair → Prop)
    (I : Fin (2 ^ subtreeHeight)) (ℓ : FTree → FLeaf) (B : Finset FTree) (hB : B.Nonempty) :
    (matchSet parameter data s excl I ℓ (live L Ms) B).card ≤
      patCapN subtreeHeight forsHeight capFloor q B.card := by
  have hS : 1 ≤ patSize (patOf ℓ B) := by rw [patSize_patOf]; exact Finset.card_pos.2 hB
  have h := card_le_patCap parameter data s hok hS (Z := matchSet parameter data s excl I ℓ (live L Ms) B)
    (fun g hg => by
      obtain ⟨hgX, hh, hI, hm⟩ := Finset.mem_filter.1 hg
      obtain ⟨h1, h2⟩ := hit_mem parameter data s hP L Ms excl hgX hh
      exact ⟨h1, h2, patCovers_patOf hI hm⟩)
  rw [patSize_patOf] at h
  exact h

/-- **The selectable pairs at one index** number at most `2^a patCap(q, 1)`. -/
theorem hitsAt_card_le {q : ℕ} {L : QueryLog SigningSpec} {P : List Pair} (hP : PInv parameter data s P)
    (hok : PatOK parameter data s q L P) (Ms : List Message) (excl : Pair → Prop)
    (I : Fin (2 ^ subtreeHeight)) (κ0 : FTree) :
    (hitsAt parameter data s excl I (live L Ms)).card ≤ 2 ^ forsHeight * patCap q 1 := by
  set Z := hitsAt parameter data s excl I (live L Ms) with hZ
  rw [Finset.card_eq_sum_card_fiberwise (f := fun g => (pview parameter data s g).2 κ0)
    (t := (Finset.univ : Finset FLeaf)) (fun _ _ => Finset.mem_univ _)]
  calc ∑ l : FLeaf, (Z.filter fun g => (pview parameter data s g).2 κ0 = l).card
      ≤ ∑ _l : FLeaf, patCap q 1 := by
        refine Finset.sum_le_sum fun l _ => ?_
        have hS : 1 ≤ patSize (patOf (fun _ => l) {κ0}) := by rw [patSize_patOf]; simp
        have h := card_le_patCap parameter data s hok hS
          (Z := Z.filter fun g => (pview parameter data s g).2 κ0 = l) (fun g hg => by
            obtain ⟨hgZ, hl⟩ := Finset.mem_filter.1 hg
            obtain ⟨hgX, hh, hI⟩ := Finset.mem_filter.1 hgZ
            obtain ⟨h1, h2⟩ := hit_mem parameter data s hP L Ms excl hgX hh
            refine ⟨h1, h2, patCovers_patOf hI fun κ' hκ' => ?_⟩
            rw [Finset.mem_singleton.1 hκ']; exact hl)
        rwa [patSize_patOf, Finset.card_singleton] at h
    _ = 2 ^ forsHeight * patCap q 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end Patterns

/-! ### One cached pair at the cell -/

section PerPair

variable (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞)

/-- The trees other than `κ` whose leaf `ℓ` is not covered at `I` by `d`. -/
noncomputable def missT (I : Fin (2 ^ subtreeHeight)) (ℓ : FTree → FLeaf) (κ : FTree) (d : Multiset View) :
    Finset FTree :=
  (Finset.univ.erase κ).filter fun κ' => κ' ∉ covT I ℓ d

theorem ownW_le_split (c : Index × FTree × FLeaf) (v : View) (d e X : Multiset View) :
    ownW c v (e + X) ≤ ∑ S ∈ (missT (localIdx c.1) v.2 c.2.1 d).powerset,
      covI (localIdx c.1) v.2 S e * covI (localIdx c.1) v.2 (missT (localIdx c.1) v.2 c.2.1 d \ S) X := by
  unfold ownW
  split_ifs with h
  · obtain ⟨h1, _, hnear⟩ := h
    set M := missT (localIdx c.1) v.2 c.2.1 d
    set S0 := M.filter fun κ' => κ' ∈ covT (localIdx c.1) v.2 e
    have hS0 : S0 ∈ M.powerset := Finset.mem_powerset.2 (Finset.filter_subset _ _)
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun S => covI (localIdx c.1) v.2 S e *
      covI (localIdx c.1) v.2 (M \ S) X) (fun _ _ => zero_le) hS0)
    have ha : covI (localIdx c.1) v.2 S0 e = 1 := by
      unfold covI
      rw [if_pos (show S0 ⊆ covT (localIdx c.1) v.2 e from fun κ' hκ => (Finset.mem_filter.1 hκ).2)]
    have hb : covI (localIdx c.1) v.2 (M \ S0) X = 1 := by
      unfold covI
      rw [if_pos]
      intro κ' hκ
      obtain ⟨hκM, hκS⟩ := Finset.mem_sdiff.1 hκ
      have hne : κ' ≠ c.2.1 := (Finset.mem_erase.1 (Finset.mem_filter.1 hκM).1).1
      obtain ⟨x, hx, hx1, hx2⟩ := hnear κ' hne
      have hcov : κ' ∈ covT (localIdx c.1) v.2 (e + X) :=
        (mem_covT _ _).2 ⟨x, hx, by rw [hx1, h1], hx2⟩
      rw [covT_add] at hcov
      rcases Finset.mem_union.1 hcov with hc | hc
      · exact absurd (Finset.mem_filter.2 ⟨hκM, hc⟩) hκS
      · exact hc
    simp only [ha, hb, mul_one]
  · exact zero_le

theorem coinR_eq (q : ℕ) (μ : ℝ) (r : ℕ) :
    phiK forsHeight μ r + coinR subtreeHeight forsHeight capFloor q μ r =
      ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) * coinV subtreeHeight forsHeight capFloor q j *
        phiK forsHeight μ (r - j) := by
  unfold coinR
  rw [lsum_range, Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, coinV_zero, Nat.sub_zero,
    show ¬(1 ≤ 0) from by omega, if_false, add_zero]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [if_pos (by omega), chooseK_eq r (j + 1) (by have := Finset.mem_range.1 hj; omega)]

/-- **One cached pair at the cell.** -/
theorem candValueG_le (hH : totalHeight = subtreeHeight) (q : ℕ) (hw : wbar ≤ 1) (s : State)
    (Ms : List Message) (hMnd : Ms.Nodup) (L : QueryLog SigningSpec) (d : Multiset View) {n k N qq : ℕ}
    (hn : n ≤ N) (hk : k ≤ qq) (μ : ℝ≥0)
    (hμ : (N : ℝ) / 2 ^ subtreeHeight + (qq : ℝ) * (landing * wbar).toReal / 2 ^ subtreeHeight ≤ μ)
    (c : Index × FTree × FLeaf) (p : Pair)
    (hcap : ∀ B : Finset FTree, B.Nonempty →
      (matchSet parameter data s (· = p) (localIdx c.1) (pview parameter data s p).2 (live L Ms) B).card ≤
        patCapN subtreeHeight forsHeight capFloor q B.card) :
    candValueG parameter data (ownW c) wbar s Ms L d n k p ≤
      ENNReal.ofReal (phiK forsHeight (μ : ℝ)
          (missT (localIdx c.1) (pview parameter data s p).2 c.2.1 d).card +
        coinR subtreeHeight forsHeight capFloor q (μ : ℝ)
          (missT (localIdx c.1) (pview parameter data s p).2 c.2.1 d).card) := by
  set I := localIdx c.1 with hI
  set ℓ := (pview parameter data s p).2 with hℓ
  set M := missT I ℓ c.2.1 d with hM
  have hlive : (live L Ms).Nodup := live_nodup L hMnd
  unfold candValueG
  have hsplit := termO_le_sum parameter data wbar s Ms L (· = p) M.powerset
    (fun S => covI I ℓ S) (fun S => covI I ℓ (M \ S))
    (fun e X => ownW_le_split c (pview parameter data s p) d e X) d n k
  refine le_trans hsplit ?_
  have hterm : ∀ S ∈ M.powerset, grpAll parameter data s (· = p) (live L Ms) (covI I ℓ S) d *
      hTermO (Finset.univ : Finset View) wbar landing n k (covI I ℓ (M \ S)) ≤
      vE subtreeHeight forsHeight capFloor q S.card * ENNReal.ofReal (phiK forsHeight (μ : ℝ) (M.card - S.card)) := by
    intro S hS
    have hSM := Finset.mem_powerset.1 hS
    refine mul_le_mul' ?_ ?_
    · refine grpAll_cov_vE parameter data s (· = p) I ℓ hH subtreeHeight forsHeight capFloor q (live L Ms) hlive
        hcap S S.card d ?_
      congr 1
      ext κ'
      simp only [Finset.mem_sdiff, and_iff_left_iff_imp]
      intro hκ
      exact (Finset.mem_filter.1 (hSM hκ)).2
    · rw [← Finset.card_sdiff_of_subset hSM]
      exact hTermO_covI_le I ℓ (M \ S) wbar hw hn hk μ hμ
  refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
  rw [Finset.sum_powerset_apply_card (fun j => vE subtreeHeight forsHeight capFloor q j *
    ENNReal.ofReal (phiK forsHeight (μ : ℝ) (M.card - j))), coinR_eq,
    ENNReal.ofReal_sum_of_nonneg (fun j _ => by
      have := coinV_nonneg subtreeHeight forsHeight capFloor q j
      have := phiK_nonneg forsHeight (NNReal.coe_nonneg μ) (M.card - j)
      positivity)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 := coinV_nonneg subtreeHeight forsHeight capFloor q j
  have h2 := phiK_nonneg forsHeight (NNReal.coe_nonneg μ) (M.card - j)
  rw [nsmul_eq_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast]
  unfold vE
  ring

/-! ### The fresh part -/

theorem discAt_add_card (d Y : Multiset View) (I : Fin (2 ^ subtreeHeight)) (κ' : FTree) :
    (leavesAt (d + Y).toFinset I κ').card ≤ (discAt d I).card + countAt Y I := by
  unfold leavesAt
  refine le_trans Finset.card_image_le ?_
  rw [Multiset.toFinset_add, Finset.filter_union]
  refine le_trans (Finset.card_union_le _ _) (add_le_add le_rfl ?_)
  rw [← Multiset.toFinset_filter]
  exact Multiset.toFinset_card_le _

/-- **The fresh base after new disclosures.** -/
theorem excessW_ownW_le (hH : totalHeight = subtreeHeight) (c : Index × FTree × FLeaf) (d Y : Multiset View) :
    excessW (ownW c) 0 (d + Y) ≤ ((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ * ((2 : ℝ≥0∞) ^ forsHeight)⁻¹ *
      ((((discAt d (localIdx c.1)).card + countAt Y (localIdx c.1) : ℕ) : ℝ≥0∞) / 2 ^ forsHeight) ^
        (forsTrees - 1) := by
  unfold excessW priceW
  rw [landing_one hH, one_mul, tsub_zero]
  set c' : FCell := (localIdx c.1, c.2.1, c.2.2)
  have hpt : ∀ v, ownW c v (d + Y) ≤ pat c' (d + Y).toFinset (Finset.univ.erase c.2.1) v := by
    intro v
    unfold ownW
    split_ifs with h
    · obtain ⟨h1, h2, hnear⟩ := h
      unfold pat
      rw [if_pos h1, one_mul]
      refine le_of_eq (Finset.prod_eq_one fun κ'' _ => ?_).symm
      unfold patG
      by_cases hk : κ'' = c.2.1
      · rw [if_pos hk, if_pos (by rw [hk]; exact h2)]
      · rw [if_neg hk, if_pos (Finset.mem_erase.2 ⟨hk, Finset.mem_univ _⟩), if_pos]
        obtain ⟨x, hx, hx1, hx2⟩ := hnear κ'' hk
        unfold leavesAt
        refine Finset.mem_image.2 ⟨x, Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hx, ?_⟩, hx2⟩
        rw [hx1, h1]
    · exact zero_le
  calc freshAvg Finset.univ (fun v => ownW c v (d + Y))
      ≤ freshAvg Finset.univ (pat c' (d + Y).toFinset (Finset.univ.erase c.2.1)) :=
        freshAvg_mono _ fun v _ => hpt v
    _ ≤ _ := by
        have h := avg_pat_le c' (d + Y).toFinset ((discAt d (localIdx c.1)).card + countAt Y (localIdx c.1))
          (fun κ' => discAt_add_card d Y (localIdx c.1) κ') (Finset.univ.erase c.2.1) (Finset.Subset.refl _)
        rwa [card_erase_tree] at h

end PerPair

end FORS.Security.SWRoute
