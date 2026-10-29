import FORS.SWRoute.ForecastDomF
import FORS.SWRoute.StepsBase

/-! **The domination of the own-cell forecast, part G: the fresh part, list sums, near cells.**

* `khValueG_le`: `k` times the excess forecast of a new pair is at most `freshK` at the rate `μ + δ`,
  `δ` bounding the group coins of the cached pairs at the cell's index;
* list sums of `ofReal`, products of the pair factors, pattern products;
* `missing_pos`: at a FORS leaf query whose contact would survive, every cached pair at the cell
  misses a tree (else the cell would be a near cell, through the known FORS secrets of the
  disclosed views). -/

open OracleComp OracleSpec ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base FORS.Base.Domination FORS.Base.H0 FORS.Security.H0Avg ForsPrice Concrete GraphView
  ForsPotential FORS.LoopWalk HiddenGraph PotentialA HiddenBridge

set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### The fresh part -/

section Fresh

variable (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞)

theorem poisMean_const_mul (μ : ℝ≥0) (c : ℝ≥0∞) (g : ℕ → ℝ≥0∞) :
    poisMean μ (fun j => c * g j) = c * poisMean μ g := by
  unfold poisMean
  rw [← ENNReal.tsum_mul_left]
  congr 1; funext j; ring

/-- **The fresh part**: `k` future pairs complete the cell with mean at most `freshK(μ + δ)`. -/
theorem khValueG_le (hH : totalHeight = subtreeHeight) (hw : wbar ≤ 1) (s : State) (Ms : List Message)
    (hMnd : Ms.Nodup) (L : QueryLog SigningSpec) (d : Multiset View) {n k N qq : ℕ} (hn : n ≤ N) (hk : k ≤ qq)
    (μ δ : ℝ≥0)
    (hμ : (N : ℝ) / 2 ^ subtreeHeight + (qq : ℝ) * (landing * wbar).toReal / 2 ^ subtreeHeight ≤ μ)
    (c : Index × FTree × FLeaf)
    (hδ : ((hitsAt parameter data s (fun _ => False) (localIdx c.1) (live L Ms)).card : ℝ≥0) / 2 ^ 128 ≤ δ) :
    (k : ℝ≥0∞) * hValueG parameter data (ownW c) wbar 0 s Ms L d n k ≤
      ENNReal.ofReal (freshK subtreeHeight forsTrees forsHeight ((μ + δ : ℝ≥0) : ℝ) qq
        (discAt d (localIdx c.1)).card) := by
  set I := localIdx c.1 with hI
  set D := (discAt d I).card with hD
  set cA : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ forsHeight)⁻¹ ^ (forsTrees - 1) with hcA
  have hcA_top : cA ≠ ⊤ := pow_ne_top (ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero))
  set F1 : ℕ → ℝ≥0∞ := fun j => cA * ((j + D : ℕ) : ℝ≥0∞) ^ (forsTrees - 1) with hF1def
  have hF1 : Good1 F1 := ((good1_pow (forsTrees - 1)).shift D).const_mul hcA_top
  set c0 : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ * ((2 : ℝ≥0∞) ^ forsHeight)⁻¹ with hc0
  -- the base after new disclosures
  have h1 : hValueG parameter data (ownW c) wbar 0 s Ms L d n k ≤
      termO parameter data wbar s Ms L (fun _ => False) (fun Y => c0 * F1 (countAt Y I)) 0 n k := by
    unfold hValueG
    refine termO_le_shift parameter data wbar s Ms L (fun _ => False) d (fun Y => ?_) n k
    refine le_trans (excessW_ownW_le hH c d Y) (le_of_eq ?_)
    simp only [hF1def, hc0, hcA]
    rw [div_eq_mul_inv, mul_pow, Nat.add_comm D (countAt Y I)]
    ring
  -- the groups outside the future pairs
  have h2 : termO parameter data wbar s Ms L (fun _ => False) (fun Y => c0 * F1 (countAt Y I)) 0 n k =
      grpAll parameter data s (fun _ => False) (live L Ms)
        (fun e => hTermO Finset.univ wbar landing n k (fun X => c0 * F1 (countAt (X + e) I))) 0 := by
    unfold termO termBase hTermO
    rw [creations_grpAll parameter data hH s (fun _ => False) Finset.univ landing]
    congr 1
    funext e
    congr 1
    funext J
    exact (virtualOnce_shift Finset.univ wbar (fun Y => c0 * F1 (countAt Y I)) n J e).symm
  -- the future at the index
  have h3 : ∀ e, hTermO Finset.univ wbar landing n k (fun X => c0 * F1 (countAt (X + e) I)) ≤
      c0 * pois1 μ F1 (countAt e I) := by
    intro e
    have e1 : (fun X => c0 * F1 (countAt (X + e) I)) =
        fun X => c0 * (fun j => F1 (j + countAt e I)) (countAt X I) := by
      funext X; rw [countAt_add]
    rw [e1, hTermO_const_mulD]
    refine mul_le_mul_right ?_ c0
    refine le_trans (hTermO_fst_le (hF1.shift (countAt e I)) I wbar hw hn hk μ hμ) (le_of_eq ?_)
    unfold poisMean pois1
    congr 1
    funext j
    show poisW μ j * F1 (j + countAt e I) = poisW μ j * F1 (countAt e I + j)
    rw [Nat.add_comm j]
  -- the groups at the index
  have h4 : grpAll parameter data s (fun _ => False) (live L Ms) (fun e => c0 * pois1 μ F1 (countAt e I)) 0 ≤
      c0 * poisMean (μ + δ) F1 := by
    rw [grpAll_const_mul]
    refine mul_le_mul_right ?_ c0
    refine le_trans (grpAll_count_le parameter data s (fun _ => False) I hH (hF1.pois1 μ) (live L Ms)
      (live_nodup L hMnd) 0) ?_
    rw [countAt_zero', pois1_pois1, ← pois1_zero]
    refine pois1_mono_rate hF1 ?_ 0
    exact le_of_le_of_eq (add_le_add_left hδ μ) (add_comm δ μ)
  -- the Poisson mean of the fresh base
  have h5 : poisMean (μ + δ) F1 = cA * ENNReal.ofReal (freshSum (((μ + δ : ℝ≥0)) : ℝ) D) := by
    rw [hF1def, poisMean_const_mul, ← poisMean_fresh]
    congr 2
    funext j
    rw [Nat.add_comm j D]
  have hle : hValueG parameter data (ownW c) wbar 0 s Ms L d n k ≤
      c0 * (cA * ENNReal.ofReal (freshSum (((μ + δ : ℝ≥0)) : ℝ) D)) := by
    rw [← h5]
    refine le_trans h1 ?_
    rw [h2]
    exact le_trans (grpAll_le_of_le s (fun _ => False) h3 _ 0) h4
  have e1 : ((2 : ℝ≥0∞) ^ (subtreeHeight + forsHeight))⁻¹ = c0 := by
    rw [hc0, pow_add, ENNReal.mul_inv (Or.inr (pow_ne_top ofNat_ne_top)) (Or.inl (pow_ne_top ofNat_ne_top))]
  have e2 : ((2 : ℝ≥0∞) ^ (forsHeight * (forsTrees - 1)))⁻¹ = cA := by
    rw [hcA, pow_mul, ENNReal.inv_pow]
  have hS := freshSum_nonneg (μ + δ) D
  calc (k : ℝ≥0∞) * hValueG parameter data (ownW c) wbar 0 s Ms L d n k
      ≤ (k : ℝ≥0∞) * (c0 * (cA * ENNReal.ofReal (freshSum (((μ + δ : ℝ≥0)) : ℝ) D))) := mul_le_mul_right hle _
    _ ≤ (qq : ℝ≥0∞) * (c0 * (cA * ENNReal.ofReal (freshSum (((μ + δ : ℝ≥0)) : ℝ) D))) :=
        mul_le_mul_left (by exact_mod_cast hk) _
    _ = ENNReal.ofReal (freshK subtreeHeight forsTrees forsHeight ((μ + δ : ℝ≥0) : ℝ) qq D) := by
        rw [freshK_eq, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos (by positivity),
          ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, div_eq_mul_inv, div_eq_mul_inv, e1, e2]
        ring

end Fresh

/-! ### List sums -/

section Lists

theorem list_sum_ofReal {α : Type} (l : List α) (g : α → ℝ) (hg : ∀ a ∈ l, 0 ≤ g a) :
    (l.map fun a => ENNReal.ofReal (g a)).sum = ENNReal.ofReal (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih (fun b hb => hg b (List.mem_cons_of_mem _ hb)), ENNReal.ofReal_add (hg a List.mem_cons_self)
        (List.sum_nonneg fun y hy => by
          obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
          exact hg b (List.mem_cons_of_mem _ hb))]

theorem list_sum_ite_filter {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] (f : α → ℝ≥0∞) :
    (l.map fun a => if p a then f a else 0).sum = ((l.filter fun a => decide (p a)).map f).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases h : p a
      · simp [h, ih]
      · simp [h, ih]

theorem list_sum_const_filter {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] (c : ℝ) :
    (l.map fun a => if p a then c else 0).sum = c * (l.filter fun a => decide (p a)).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases h : p a
      · simp [h, ih]; ring
      · simp [h, ih]

theorem list_prod_two {α : Type} (l : List α) (p : α → Prop) [DecidablePred p] :
    (l.map fun a => if p a then (2 : ℝ≥0∞) else 1).prod = 2 ^ (l.filter fun a => decide (p a)).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases h : p a
      · simp [h, ih, pow_succ]; ring
      · simp [h, ih]

theorem list_prod_pairF (c : FCell) (Q : Finset View) (θ : ℝ) (φ : ℕ → ℝ) {α : Type} (l : List α) (g : α → View) :
    (l.map fun a => pairFφ c Q θ φ (g a)).prod = ENNReal.ofReal (Real.exp (θ * (l.map fun a => wQφ c Q φ (g a)).sum)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, ih]
      unfold pairFφ
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, mul_add]

end Lists

/-! ### Cached pairs at a surviving cell miss a tree -/

section Near

variable (K : Ctx) (root : Digest) (data : PublicData)

/-- **Known secrets**: every FORS leaf secret of a disclosed view is known. -/
def KnownInv (s : State) (d : Multiset View) : Prop :=
  ∀ v ∈ d, ∀ (κ' : FTree) (i : Index), localIdx i = v.1 → s.known (Coordinate.fors i κ' (v.2 κ') 0) ≠ none

theorem localIdx_injD (hH : totalHeight = subtreeHeight) : Function.Injective localIdx := by
  intro i j h
  have hi : i.val < 2 ^ subtreeHeight := lt_of_lt_of_eq i.isLt (by rw [hH])
  have hj : j.val < 2 ^ subtreeHeight := lt_of_lt_of_eq j.isLt (by rw [hH])
  have := congrArg Fin.val h
  simp only [localIdx, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  exact Fin.ext this

theorem mem_leavesAt_discAt {d : Multiset View} {I : Fin (2 ^ subtreeHeight)} {κ' : FTree} {x : FLeaf} :
    x ∈ leavesAt (discAt d I) I κ' ↔ ∃ v ∈ d, v.1 = I ∧ v.2 κ' = x := by
  unfold leavesAt discAt
  simp only [Finset.mem_image, Finset.mem_filter, Multiset.mem_toFinset]
  constructor
  · rintro ⟨v, ⟨⟨hv, _⟩, hI⟩, hx⟩; exact ⟨v, hv, hI, hx⟩
  · rintro ⟨v, hv, hI, hx⟩; exact ⟨v, ⟨⟨hv, hI⟩, hI⟩, hx⟩

/-- **A cached pair at a surviving cell misses a tree.** -/
theorem missing_pos (hH : totalHeight = subtreeHeight) {s : State} {P : List Pair} (hP : PInv K.p data s P)
    {d : Multiset View} (hknown : KnownInv s d) {f : FIn} (hsurv : SurvivesAt K root s f) {p : Pair} (hp : p ∈ P)
    (hop : Opens (cellOfF f) (pview K.p data s p)) :
    1 ≤ missing (cellOfF f) (discAt d (localIdx f.index)) (pview K.p data s p) := by
  by_contra hlt
  have h0 : missing (cellOfF f) (discAt d (localIdx f.index)) (pview K.p data s p) = 0 := by omega
  apply hsurv.2.1
  obtain ⟨u0, hu0, _⟩ := (hP.mem p).1 hp
  have hall := hP.all p ((hP.mem p).1 hp)
  have hsome : ∀ call, ∃ v, s.cache (pblk K.p data p call) = some v := fun call =>
    Option.ne_none_iff_exists'.1 (hall call)
  choose u hu using hsome
  have hpc := pcache_of_cached K.p data (p := p) hu
  have hview : pview K.p data s p = viewOf u := pview_of_pcache hpc
  refine ⟨p.1, p.2, truncateMessageDigest u, ?_, landed_all hH K.p _, ?_, ?_, ?_⟩
  · unfold cachedDigest
    have : pcache K.p data p.1 s p.2 = some u := hpc
    unfold pcache at this
    exact (congrArg (Option.map truncateMessageDigest) this : _)
  · apply localIdx_injD hH
    have h1 := hop.1
    rw [hview] at h1
    exact h1
  · have h2 := hop.2
    rw [hview] at h2
    exact h2
  · intro κ' hκ'
    have hmiss : (pview K.p data s p).2 κ' ∈ leavesAt (discAt d (localIdx f.index)) (localIdx f.index) κ' := by
      by_contra hn
      have : 0 < missing (cellOfF f) (discAt d (localIdx f.index)) (pview K.p data s p) := by
        unfold missing
        exact Finset.card_pos.2 ⟨κ', Finset.mem_filter.2 ⟨Finset.mem_erase.2 ⟨hκ', Finset.mem_univ _⟩, hn⟩⟩
      omega
    obtain ⟨v, hv, hvI, hvx⟩ := mem_leavesAt_discAt.1 hmiss
    have hk := hknown v hv κ' f.index hvI.symm
    rw [hvx, hview] at hk
    exact hk

/-- A view in the disclosed set misses no tree. -/
theorem missing_zero_of_mem {d : Multiset View} {c : FCell} {u : View} (hu : u ∈ discAt d c.1) :
    missing c (discAt d c.1) u = 0 := by
  unfold missing
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro κ' _ hn
  apply hn
  have hu' := Finset.mem_filter.1 hu
  exact mem_leavesAt_discAt.2 ⟨u, Multiset.mem_toFinset.1 hu'.1, hu'.2, rfl⟩

end Near

end FORS.Security.SWRoute
