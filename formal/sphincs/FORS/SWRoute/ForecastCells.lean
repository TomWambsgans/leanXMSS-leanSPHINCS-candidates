import FORS.SWRoute.ForecastLight

/-! **Cells and the pattern bound.** A cell `c = (I, κ, L)` is an index, a tree and a leaf of that
tree; a view opens `c` when it is at `I` and selects `L` in tree `κ`. Relative to a finite set `Q` of
disclosed views, the trees of a view `u` other than `κ` split into hit trees (the leaf of `u` is
disclosed at `I` by a view of `Q`) and missing trees; `missing c Q u` counts the missing ones.

**The pattern bound** (`avg_open_missing_le`): if `Q` discloses at most `D` leaves per tree at `I`,
then for every `h ≥ 0`
  `E_u[1[u opens c] h(missing c Q u)] ≤ 2^-b 2^-a Σ_{j < k} C(k-1, j) (D / 2^a)^(k-1-j) h(j)`,
since `missing = j` needs the `k-1-j` hit trees to form one of the `C(k-1, j)` patterns, each hit
with chance at most `D / 2^a`, independently over the trees of a uniform view.

**The pair factor** (`avg_pairF_le`): the weight `wQ c Q ρ u = ρ^(missing c Q u)` of a view opening
`c` outside `Q` with at least one missing tree, and `pairF = e^{θ wQ}`, averages to at most
`1 + 2^-b 2^-a Σ_{1 ≤ j < k} C(k-1, j) (D / 2^a)^(k-1-j) (e^{θ ρ^j} - 1)`.

**Subsets** (`sum_subsets_le`): the `D`-subsets of the views disclosed at `I` number at most
`C(countAt d I, D)`. -/

open ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Security FORS.Security.H0Avg FORS.Base.Domination Concrete ForsPrice

set_option linter.unusedSectionVars false

/-! ### Cells -/

/-- A cell: an index, a tree, and a leaf of that tree. -/
abbrev FCell := Fin (2 ^ subtreeHeight) × FTree × FLeaf

/-- A view opens a cell when it is at the cell's index and selects the cell's leaf in its tree. -/
def Opens (c : FCell) (v : View) : Prop := v.1 = c.1 ∧ v.2 c.2.1 = c.2.2

instance (c : FCell) (v : View) : Decidable (Opens c v) := inferInstanceAs (Decidable (_ ∧ _))

/-- The leaves of tree `κ'` disclosed at index `I` by the views of `Q`. -/
def leavesAt (Q : Finset View) (I : Fin (2 ^ subtreeHeight)) (κ' : FTree) : Finset FLeaf :=
  (Q.filter fun v => v.1 = I).image fun v => v.2 κ'

/-- The trees other than the cell's whose leaf of `u` is disclosed at the cell's index. -/
noncomputable def hitTrees (c : FCell) (Q : Finset View) (u : View) : Finset FTree :=
  (Finset.univ.erase c.2.1).filter fun κ' => u.2 κ' ∈ leavesAt Q c.1 κ'

/-- The number of trees other than the cell's whose leaf of `u` is not disclosed at the cell's index. -/
noncomputable def missing (c : FCell) (Q : Finset View) (u : View) : ℕ :=
  ((Finset.univ.erase c.2.1).filter fun κ' => u.2 κ' ∉ leavesAt Q c.1 κ').card

theorem card_erase_tree (κ : FTree) : (Finset.univ.erase κ).card = forsTrees - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, H0.card_ftree]

theorem hitTrees_card (c : FCell) (Q : Finset View) (u : View) :
    (hitTrees c Q u).card = (forsTrees - 1) - missing c Q u := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ.erase c.2.1)
    (fun κ' => u.2 κ' ∈ leavesAt Q c.1 κ')
  rw [card_erase_tree] at h
  unfold hitTrees missing
  omega

theorem missing_le (c : FCell) (Q : Finset View) (u : View) : missing c Q u ≤ forsTrees - 1 := by
  unfold missing
  rw [← card_erase_tree c.2.1]
  exact Finset.card_filter_le _ _

theorem missing_lt (c : FCell) (Q : Finset View) (u : View) : missing c Q u < forsTrees := by
  have h1 := missing_le c Q u
  have h2 : 0 < forsTrees := Fin.pos c.2.1
  omega

/-! ### Averages -/

theorem freshAvg_finset_sum {V α : Type} (U : Finset V) (s : Finset α) (g : α → V → ℝ≥0∞) :
    freshAvg U (fun u => ∑ i ∈ s, g i u) = ∑ i ∈ s, freshAvg U (g i) := by
  unfold freshAvg
  rw [Finset.sum_comm, Finset.mul_sum]

theorem freshAvg_indicator_eq {X : Type} [Fintype X] [DecidableEq X] (x0 : X) :
    freshAvg (Finset.univ : Finset X) (fun x => if x = x0 then (1 : ℝ≥0∞) else 0) =
      ((Fintype.card X : ℕ) : ℝ≥0∞)⁻¹ := by
  unfold freshAvg
  rw [Finset.sum_ite_eq' Finset.univ x0, if_pos (Finset.mem_univ _), mul_one, Finset.card_univ]

theorem freshAvg_indicator_mem {X : Type} [Fintype X] [DecidableEq X] (S : Finset X) :
    freshAvg (Finset.univ : Finset X) (fun x => if x ∈ S then (1 : ℝ≥0∞) else 0) =
      ((Fintype.card X : ℕ) : ℝ≥0∞)⁻¹ * (S.card : ℝ≥0∞) := by
  unfold freshAvg
  rw [Finset.card_univ]
  congr 1
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]

theorem card_fleafE : ((Fintype.card FLeaf : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ forsHeight := by
  rw [Fintype.card_fin]; push_cast; rfl

theorem card_indexE : ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ subtreeHeight := by
  rw [Fintype.card_fin]; push_cast; rfl

/-! ### Patterns -/

/-- The per-tree factor of a pattern `U` (a set of trees other than the cell's that must be hit). -/
noncomputable def patG (c : FCell) (Q : Finset View) (U : Finset FTree) (κ'' : FTree) (x : FLeaf) : ℝ≥0∞ :=
  if κ'' = c.2.1 then (if x = c.2.2 then 1 else 0)
  else if κ'' ∈ U then (if x ∈ leavesAt Q c.1 κ'' then 1 else 0) else 1

/-- A view opens the cell and hits every tree of the pattern `U`. -/
noncomputable def pat (c : FCell) (Q : Finset View) (U : Finset FTree) (u : View) : ℝ≥0∞ :=
  (if u.1 = c.1 then 1 else 0) * ∏ κ'', patG c Q U κ'' (u.2 κ'')

theorem pat_hit {c : FCell} {Q : Finset View} {u : View} (hu : Opens c u) : pat c Q (hitTrees c Q u) u = 1 := by
  unfold pat
  rw [if_pos hu.1, one_mul]
  refine Finset.prod_eq_one fun κ'' _ => ?_
  unfold patG
  by_cases h1 : κ'' = c.2.1
  · rw [if_pos h1, if_pos (by rw [h1]; exact hu.2)]
  · rw [if_neg h1]
    by_cases h2 : κ'' ∈ hitTrees c Q u
    · rw [if_pos h2, if_pos (Finset.mem_filter.1 h2).2]
    · rw [if_neg h2]

/-- **Pointwise pattern bound.** -/
theorem open_missing_le_pat (c : FCell) (Q : Finset View) (h : ℕ → ℝ≥0∞) (u : View) :
    (if Opens c u then h (missing c Q u) else 0) ≤
      ∑ j ∈ Finset.range forsTrees, h j *
        ∑ U ∈ (Finset.univ.erase c.2.1).powersetCard (forsTrees - 1 - j), pat c Q U u := by
  by_cases hu : Opens c u
  · rw [if_pos hu]
    set j0 := missing c Q u
    have hU : hitTrees c Q u ∈ (Finset.univ.erase c.2.1).powersetCard (forsTrees - 1 - j0) := by
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.filter_subset _ _, hitTrees_card c Q u⟩
    calc h j0 = h j0 * pat c Q (hitTrees c Q u) u := by rw [pat_hit hu, mul_one]
      _ ≤ h j0 * ∑ U ∈ (Finset.univ.erase c.2.1).powersetCard (forsTrees - 1 - j0), pat c Q U u :=
          mul_le_mul_right (Finset.single_le_sum (f := fun U => pat c Q U u) (fun _ _ => zero_le) hU) _
      _ ≤ _ := Finset.single_le_sum
          (f := fun j => h j * ∑ U ∈ (Finset.univ.erase c.2.1).powersetCard (forsTrees - 1 - j), pat c Q U u)
          (fun _ _ => zero_le) (Finset.mem_range.2 (missing_lt c Q u))
  · rw [if_neg hu]
    exact zero_le

/-- **The average of a pattern.** -/
theorem avg_pat_le (c : FCell) (Q : Finset View) (D : ℕ) (hD : ∀ κ', (leavesAt Q c.1 κ').card ≤ D)
    (U : Finset FTree) (hU : U ⊆ Finset.univ.erase c.2.1) :
    freshAvg (Finset.univ : Finset View) (pat c Q U) ≤
      ((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ * ((2 : ℝ≥0∞) ^ forsHeight)⁻¹ *
        ((D : ℝ≥0∞) / 2 ^ forsHeight) ^ U.card := by
  rw [freshAvg_prod]
  unfold pat
  rw [show (fun l : Fin (2 ^ subtreeHeight) => freshAvg Finset.univ fun m : FTree → FLeaf =>
      (if (l, m).1 = c.1 then (1 : ℝ≥0∞) else 0) * ∏ κ'', patG c Q U κ'' ((l, m).2 κ'')) =
      fun l => (freshAvg Finset.univ fun m : FTree → FLeaf => ∏ κ'', patG c Q U κ'' (m κ'')) *
        (if l = c.1 then (1 : ℝ≥0∞) else 0) from funext fun l => by
        dsimp only
        rw [freshAvg_mul (Finset.univ : Finset (FTree → FLeaf)) (if l = c.1 then (1 : ℝ≥0∞) else 0)
          (fun m => ∏ κ'', patG c Q U κ'' (m κ'')), mul_comm]]
  rw [freshAvg_mul, freshAvg_indicator_eq, card_indexE, freshAvg_pi_prod]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ c.2.1)]
  have h0 : freshAvg (Finset.univ : Finset FLeaf) (patG c Q U c.2.1) = ((2 : ℝ≥0∞) ^ forsHeight)⁻¹ := by
    unfold patG
    simp only [if_true]
    rw [freshAvg_indicator_eq, card_fleafE]
  have hrest : ∏ κ'' ∈ Finset.univ.erase c.2.1, freshAvg (Finset.univ : Finset FLeaf) (patG c Q U κ'') ≤
      ((D : ℝ≥0∞) / 2 ^ forsHeight) ^ U.card := by
    calc ∏ κ'' ∈ Finset.univ.erase c.2.1, freshAvg (Finset.univ : Finset FLeaf) (patG c Q U κ'')
        ≤ ∏ κ'' ∈ Finset.univ.erase c.2.1, (if κ'' ∈ U then (D : ℝ≥0∞) / 2 ^ forsHeight else 1) := by
          refine Finset.prod_le_prod' fun κ'' hκ'' => ?_
          have hne : κ'' ≠ c.2.1 := (Finset.mem_erase.1 hκ'').1
          unfold patG
          simp only [if_neg hne]
          by_cases hm : κ'' ∈ U
          · simp only [if_pos hm]
            rw [freshAvg_indicator_mem, card_fleafE, ENNReal.div_eq_inv_mul]
            exact mul_le_mul_right (by exact_mod_cast hD κ'') _
          · simp only [if_neg hm]
            exact le_of_eq (freshAvg_const _ Finset.univ_nonempty 1)
      _ = ∏ κ'' ∈ Finset.univ.erase c.2.1 ∩ U, (D : ℝ≥0∞) / 2 ^ forsHeight := by
          rw [Finset.prod_ite_mem]
      _ = _ := by
          rw [Finset.inter_eq_right.2 hU, Finset.prod_const]
  rw [h0]
  calc ((2 : ℝ≥0∞) ^ forsHeight)⁻¹ *
        (∏ κ'' ∈ Finset.univ.erase c.2.1, freshAvg (Finset.univ : Finset FLeaf) (patG c Q U κ'')) *
        ((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹
      ≤ ((2 : ℝ≥0∞) ^ forsHeight)⁻¹ * ((D : ℝ≥0∞) / 2 ^ forsHeight) ^ U.card *
        ((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ := by gcongr
    _ = _ := by ring

/-- **The pattern bound.** -/
theorem avg_open_missing_le (c : FCell) (Q : Finset View) (D : ℕ) (hD : ∀ κ', (leavesAt Q c.1 κ').card ≤ D)
    (h : ℕ → ℝ≥0∞) :
    freshAvg (Finset.univ : Finset View) (fun u => if Opens c u then h (missing c Q u) else 0) ≤
      ((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ * ((2 : ℝ≥0∞) ^ forsHeight)⁻¹ *
        ∑ j ∈ Finset.range forsTrees,
          (((forsTrees - 1).choose j : ℕ) : ℝ≥0∞) * ((D : ℝ≥0∞) / 2 ^ forsHeight) ^ (forsTrees - 1 - j) * h j := by
  refine le_trans (freshAvg_mono _ fun u _ => open_missing_le_pat c Q h u) ?_
  rw [freshAvg_finset_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [freshAvg_mul, freshAvg_finset_sum]
  have hcard : ((Finset.univ.erase c.2.1).powersetCard (forsTrees - 1 - j)).card = (forsTrees - 1).choose j := by
    rw [Finset.card_powersetCard, card_erase_tree]
    exact Nat.choose_symm (by have := Finset.mem_range.1 hj; omega)
  calc h j * ∑ U ∈ (Finset.univ.erase c.2.1).powersetCard (forsTrees - 1 - j),
        freshAvg (Finset.univ : Finset View) (pat c Q U)
      ≤ h j * ∑ _U ∈ (Finset.univ.erase c.2.1).powersetCard (forsTrees - 1 - j),
        ((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ * ((2 : ℝ≥0∞) ^ forsHeight)⁻¹ *
          ((D : ℝ≥0∞) / 2 ^ forsHeight) ^ (forsTrees - 1 - j) := by
        refine mul_le_mul_right (Finset.sum_le_sum fun U hU => ?_) _
        have hU' := Finset.mem_powersetCard.1 hU
        have h1 := avg_pat_le c Q D hD U hU'.1
        rwa [hU'.2] at h1
    _ = _ := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        ring

/-! ### The pair factor -/

/-- The weight of a view at a cell relative to `Q`: `ρ^(missing)` if it opens the cell, is not in
`Q`, and misses at least one tree; zero otherwise. -/
noncomputable def wQ (c : FCell) (Q : Finset View) (ρ : ℝ) (u : View) : ℝ :=
  if Opens c u ∧ u ∉ Q ∧ 1 ≤ missing c Q u then ρ ^ missing c Q u else 0

/-- The exponential pair factor `e^{θ wQ}`. -/
noncomputable def pairF (c : FCell) (Q : Finset View) (θ ρ : ℝ) (u : View) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (θ * wQ c Q ρ u))

/-- The excess of the pair factor at `j` missing trees. -/
noncomputable def pairExcess (θ ρ : ℝ) (j : ℕ) : ℝ≥0∞ :=
  if 1 ≤ j then ENNReal.ofReal (Real.exp (θ * ρ ^ j) - 1) else 0

theorem one_le_pairF (c : FCell) (Q : Finset View) {θ ρ : ℝ} (hθ : 0 ≤ θ) (hρ : 0 ≤ ρ) (u : View) :
    1 ≤ pairF c Q θ ρ u := by
  unfold pairF
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  have : 0 ≤ wQ c Q ρ u := by unfold wQ; split_ifs <;> positivity
  exact Real.one_le_exp (by positivity)

theorem pairF_le (c : FCell) (Q : Finset View) {θ ρ : ℝ} (hθ : 0 ≤ θ) (hρ : 0 ≤ ρ) (u : View) :
    pairF c Q θ ρ u ≤ 1 + (if Opens c u then pairExcess θ ρ (missing c Q u) else 0) := by
  unfold pairF wQ
  by_cases h : Opens c u ∧ u ∉ Q ∧ 1 ≤ missing c Q u
  · rw [if_pos h, if_pos h.1]
    unfold pairExcess
    rw [if_pos h.2.2]
    have h1 : 1 ≤ Real.exp (θ * ρ ^ missing c Q u) := Real.one_le_exp (by positivity)
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [if_neg h, mul_zero, Real.exp_zero, ENNReal.ofReal_one]
    exact le_self_add

/-- **The average pair factor.** -/
theorem avg_pairF_le (c : FCell) (Q : Finset View) (D : ℕ) (hD : ∀ κ', (leavesAt Q c.1 κ').card ≤ D)
    {θ ρ : ℝ} (hθ : 0 ≤ θ) (hρ : 0 ≤ ρ) :
    freshAvg (Finset.univ : Finset View) (pairF c Q θ ρ) ≤
      1 + ((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ * ((2 : ℝ≥0∞) ^ forsHeight)⁻¹ *
        ∑ j ∈ Finset.range forsTrees,
          (((forsTrees - 1).choose j : ℕ) : ℝ≥0∞) * ((D : ℝ≥0∞) / 2 ^ forsHeight) ^ (forsTrees - 1 - j) *
            pairExcess θ ρ j := by
  calc freshAvg (Finset.univ : Finset View) (pairF c Q θ ρ)
      ≤ freshAvg (Finset.univ : Finset View)
          (fun u => 1 + (if Opens c u then pairExcess θ ρ (missing c Q u) else 0)) :=
        freshAvg_mono _ fun u _ => pairF_le c Q hθ hρ u
    _ = 1 + freshAvg (Finset.univ : Finset View)
          (fun u => if Opens c u then pairExcess θ ρ (missing c Q u) else 0) := by
        rw [freshAvg_add, freshAvg_const _ Finset.univ_nonempty]
    _ ≤ _ := add_le_add le_rfl (avg_open_missing_le c Q D hD _)

/-! ### Subsets of the disclosed views at an index -/

/-- The finite sets of `D` views at index `I`. -/
noncomputable def subsetsAt (I : Fin (2 ^ subtreeHeight)) (D : ℕ) : Finset (Finset View) :=
  Finset.univ.filter fun Q => Q.card = D ∧ ∀ v ∈ Q, v.1 = I

/-- **The `D`-subsets of the views disclosed at `I`** number at most `C(countAt d I, D)`. -/
theorem sum_subsets_le (d : Multiset View) (I : Fin (2 ^ subtreeHeight)) (D : ℕ) :
    ∑ Q ∈ subsetsAt I D, (if Q ⊆ d.toFinset then (1 : ℝ≥0∞) else 0) ≤
      (((countAt d I).choose D : ℕ) : ℝ≥0∞) := by
  rw [Finset.sum_boole]
  have hset : (subsetsAt I D).filter (fun Q => Q ⊆ d.toFinset) =
      (d.toFinset.filter fun v => v.1 = I).powersetCard D := by
    ext Q
    simp only [subsetsAt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hc, hI⟩, hsub⟩
      exact ⟨fun v hv => Finset.mem_filter.2 ⟨hsub hv, hI v hv⟩, hc⟩
    · rintro ⟨hsub, hc⟩
      exact ⟨⟨hc, fun v hv => (Finset.mem_filter.1 (hsub hv)).2⟩, fun v hv => (Finset.mem_filter.1 (hsub hv)).1⟩
  rw [hset, Finset.card_powersetCard]
  have hle : (d.toFinset.filter fun v => v.1 = I).card ≤ countAt d I := by
    unfold countAt
    rw [← Multiset.toFinset_filter]
    exact Multiset.toFinset_card_le _
  exact_mod_cast Nat.choose_le_choose D hle

/-- A set of views at `I` discloses at most its size in leaves per tree. -/
theorem leavesAt_card_le (Q : Finset View) (I : Fin (2 ^ subtreeHeight)) (κ' : FTree) :
    (leavesAt Q I κ').card ≤ Q.card :=
  le_trans Finset.card_image_le (Finset.card_filter_le _ _)

end FORS.Security.SWRoute
