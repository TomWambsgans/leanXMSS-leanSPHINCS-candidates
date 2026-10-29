import FORS.SWRoute.ForecastStart

/-! **Pieces of the step lemmas of the tail potential** (WP-F-B).

* The per-pair weights are nonnegative (`touchard_nonneg`, `phiK_nonneg`), so the pair factors are
  at least one (`one_le_pairFφ`) and at most `1 + eφ` (`pairFφ_le`), where `eφ` is the excess of a
  view opening the cell outside `Q`; its average is at most the mean pair factor minus one
  (`avg_eφ_le`, `gamma_le`: the ENNReal form of `gammaR`).
* A pattern is selected by a uniform view with chance `2^-b 2^-(a |S|)` (`avg_patCovers`).
* The products over the unsigned pairs (`prodU_eqB`, `prodU_consB`, `prodU_congrB`, `prodU_le_ofB`).
* Translation invariance: a base that ignores one more disclosed view `v` stays so through the
  one-coin future and the groups (`virtualOnce_shiftB`, `grpAll_vinv`), and a new landed pair whose
  view `v` is irrelevant does not raise the forecast (`termO_newPair_inv`). -/

open OracleComp OracleSpec ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.LoopWalk ForsPotential PotentialA
open FORS.Security FORS.Security.H0 FORS.Security.H0Avg FORS.Base.H0

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-! ### Nonnegative weights -/

theorem TailPar.φ_nonneg (tp : TailPar) (r : ℕ) : 0 ≤ tp.φ r :=
  phiK_nonneg forsHeight tp.μ.2 r

/-! ### The pair factor with general weights -/

/-- The excess of the pair factor at `j` missing trees. -/
noncomputable def excφ (θ : ℝ) (φ : ℕ → ℝ) (j : ℕ) : ℝ≥0∞ :=
  if 1 ≤ j then ENNReal.ofReal (Real.exp (θ * φ j) - 1) else 0

/-- The excess of a view: it opens the cell outside `Q`. -/
noncomputable def eφ (c : FCell) (Q : Finset View) (θ : ℝ) (φ : ℕ → ℝ) (u : View) : ℝ≥0∞ :=
  if Opens c u ∧ u ∉ Q then excφ θ φ (missing c Q u) else 0

theorem wQφ_nonneg (c : FCell) (Q : Finset View) {φ : ℕ → ℝ} (hφ : ∀ r, 0 ≤ φ r) (u : View) :
    0 ≤ wQφ c Q φ u := by
  unfold wQφ; split_ifs
  · exact hφ _
  · exact le_rfl

theorem one_le_pairFφ (c : FCell) (Q : Finset View) {θ : ℝ} (hθ : 0 ≤ θ) {φ : ℕ → ℝ} (hφ : ∀ r, 0 ≤ φ r)
    (u : View) : 1 ≤ pairFφ c Q θ φ u := by
  unfold pairFφ
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hθ (wQφ_nonneg c Q hφ u)))

theorem ofReal_le_one_addB (y : ℝ) : ENNReal.ofReal y ≤ 1 + ENNReal.ofReal (y - 1) := by
  rcases le_or_gt 1 y with h | h
  · rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · calc ENNReal.ofReal y ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h.le
      _ = 1 := ENNReal.ofReal_one
      _ ≤ _ := le_self_add

theorem pairFφ_le (c : FCell) (Q : Finset View) (θ : ℝ) (φ : ℕ → ℝ) (u : View) :
    pairFφ c Q θ φ u ≤ 1 + eφ c Q θ φ u := by
  unfold pairFφ wQφ eφ
  by_cases h : Opens c u ∧ u ∉ Q ∧ 1 ≤ missing c Q u
  · rw [if_pos h, if_pos ⟨h.1, h.2.1⟩]
    unfold excφ
    rw [if_pos h.2.2]
    exact ofReal_le_one_addB _
  · rw [if_neg h, mul_zero, Real.exp_zero, ENNReal.ofReal_one]
    exact le_self_add

/-- Inside `Q` the pair factor is one. -/
theorem pairFφ_of_mem (c : FCell) {Q : Finset View} (θ : ℝ) (φ : ℕ → ℝ) {u : View} (hu : u ∈ Q) :
    pairFφ c Q θ φ u = 1 := by
  unfold pairFφ wQφ
  rw [if_neg (fun h => h.2.1 hu), mul_zero, Real.exp_zero, ENNReal.ofReal_one]

/-- **The average excess.** -/
theorem avg_eφ_le (c : FCell) (Q : Finset View) (D : ℕ) (hD : ∀ κ', (leavesAt Q c.1 κ').card ≤ D)
    (θ : ℝ) (φ : ℕ → ℝ) :
    freshAvg (Finset.univ : Finset View) (eφ c Q θ φ) ≤
      ((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ * ((2 : ℝ≥0∞) ^ forsHeight)⁻¹ *
        ∑ j ∈ Finset.range forsTrees,
          (((forsTrees - 1).choose j : ℕ) : ℝ≥0∞) * ((D : ℝ≥0∞) / 2 ^ forsHeight) ^ (forsTrees - 1 - j) *
            excφ θ φ j := by
  refine le_trans (freshAvg_mono _ fun u _ => ?_) (avg_open_missing_le c Q D hD (excφ θ φ))
  unfold eφ
  by_cases h : Opens c u ∧ u ∉ Q
  · rw [if_pos h, if_pos h.1]
  · rw [if_neg h]; exact zero_le

theorem list_sum_range_eqB {M : Type} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- **The mean pair factor** in ENNReal form: `1 + avg excess ≤ Γ_D`. -/
theorem gamma_le {θ : ℝ} (hθ : 0 ≤ θ) {φ : ℕ → ℝ} (hφ : ∀ r, 0 ≤ φ r) (D : ℕ) :
    1 + ((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ * ((2 : ℝ≥0∞) ^ forsHeight)⁻¹ *
        ∑ j ∈ Finset.range forsTrees,
          (((forsTrees - 1).choose j : ℕ) : ℝ≥0∞) * ((D : ℝ≥0∞) / 2 ^ forsHeight) ^ (forsTrees - 1 - j) *
            excφ θ φ j ≤
      ENNReal.ofReal (gammaR subtreeHeight forsTrees forsHeight θ φ D) := by
  set g : ℕ → ℝ := fun j => if 1 ≤ j then
    chooseK (forsTrees - 1) j * ((D : ℝ) / 2 ^ forsHeight) ^ (forsTrees - 1 - j) * (Real.exp (θ * φ j) - 1) else 0
    with hg
  have hexp : ∀ j, 0 ≤ Real.exp (θ * φ j) - 1 := fun j => by
    have := Real.one_le_exp (mul_nonneg hθ (hφ j)); linarith
  have hg0 : ∀ j, 0 ≤ g j := fun j => by
    simp only [hg]; split_ifs
    · exact mul_nonneg (mul_nonneg (chooseK_nonneg _ _) (by positivity)) (hexp j)
    · exact le_rfl
  have hterm : ∀ j ∈ Finset.range forsTrees, ENNReal.ofReal (g j) =
      (((forsTrees - 1).choose j : ℕ) : ℝ≥0∞) * ((D : ℝ≥0∞) / 2 ^ forsHeight) ^ (forsTrees - 1 - j) *
        excφ θ φ j := by
    intro j hj
    have hjk : j ≤ forsTrees - 1 := by have := Finset.mem_range.1 hj; omega
    simp only [hg, excφ]
    split_ifs with h1
    · have hc : chooseK (forsTrees - 1) j = (((forsTrees - 1).choose j : ℕ) : ℝ) := by
        unfold chooseK; rw [Nat.cast_choose ℝ hjk]
      rw [hc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    · simp
  have hsum : ENNReal.ofReal (((List.range forsTrees).map g).sum) =
      ∑ j ∈ Finset.range forsTrees,
        (((forsTrees - 1).choose j : ℕ) : ℝ≥0∞) * ((D : ℝ≥0∞) / 2 ^ forsHeight) ^ (forsTrees - 1 - j) *
          excφ θ φ j := by
    rw [list_sum_range_eqB, ENNReal.ofReal_sum_of_nonneg (fun j _ => hg0 j)]
    exact Finset.sum_congr rfl hterm
  have hS0 : 0 ≤ ((List.range forsTrees).map g).sum := by
    rw [list_sum_range_eqB]; exact Finset.sum_nonneg fun j _ => hg0 j
  unfold gammaR
  rw [← hg, ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_div_of_pos (by positivity), hsum, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  refine add_le_add le_rfl (le_of_eq ?_)
  rw [pow_add, ← ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero))
    (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)), ← ENNReal.div_eq_inv_mul]

theorem one_le_gamma {θ : ℝ} (hθ : 0 ≤ θ) {φ : ℕ → ℝ} (hφ : ∀ r, 0 ≤ φ r) (D : ℕ) :
    1 ≤ ENNReal.ofReal (gammaR subtreeHeight forsTrees forsHeight θ φ D) :=
  le_trans le_self_add (gamma_le hθ hφ D)

/-! ### Patterns -/

/-- The per-tree factor of a pattern. -/
noncomputable def patF (S : Pat) (κ : FTree) (x : FLeaf) : ℝ≥0∞ :=
  match S κ with
  | none => 1
  | some l => if x = l then 1 else 0

theorem patCovers_ind (I : Fin (2 ^ subtreeHeight)) (S : Pat) (u : View) :
    (haveI := Classical.propDecidable (PatCovers I S u); if PatCovers I S u then (1 : ℝ≥0∞) else 0) =
      (if u.1 = I then 1 else 0) * ∏ κ, patF S κ (u.2 κ) := by
  classical
  by_cases h : PatCovers I S u
  · rw [if_pos h, if_pos h.1, one_mul]
    refine (Finset.prod_eq_one fun κ _ => ?_).symm
    cases hS : S κ with
    | none => simp [patF, hS]
    | some l => simp [patF, hS, h.2 κ l hS]
  · rw [if_neg h]
    by_cases h1 : u.1 = I
    · rw [if_pos h1, one_mul]
      have : ∃ κ l, S κ = some l ∧ u.2 κ ≠ l := by
        by_contra hc
        push Not at hc
        exact h ⟨h1, hc⟩
      obtain ⟨κ, l, hS, hne⟩ := this
      refine (Finset.prod_eq_zero (Finset.mem_univ κ) ?_).symm
      simp [patF, hS, hne]
    · rw [if_neg h1, zero_mul]

theorem avg_patF (S : Pat) (κ : FTree) :
    freshAvg (Finset.univ : Finset FLeaf) (patF S κ) =
      if (S κ).isSome then ((2 : ℝ≥0∞) ^ forsHeight)⁻¹ else 1 := by
  unfold patF
  cases hS : S κ with
  | none => simp only [Option.isSome_none]; exact freshAvg_const _ Finset.univ_nonempty 1
  | some l =>
      simp only [Option.isSome_some, if_true]
      rw [freshAvg_indicator_eq, card_fleafE]

/-- **A pattern is selected** by a uniform view with chance `2^-b 2^-(a |S|)`. -/
theorem avg_patCovers (I : Fin (2 ^ subtreeHeight)) (S : Pat) :
    freshAvg (Finset.univ : Finset View)
        (fun u => haveI := Classical.propDecidable (PatCovers I S u); if PatCovers I S u then (1 : ℝ≥0∞) else 0) =
      ((2 : ℝ≥0∞) ^ (subtreeHeight + forsHeight * patSize S))⁻¹ := by
  classical
  simp only [patCovers_ind]
  rw [freshAvg_prod]
  rw [show (fun l : Fin (2 ^ subtreeHeight) => freshAvg Finset.univ fun m : FTree → FLeaf =>
      (if (l, m).1 = I then (1 : ℝ≥0∞) else 0) * ∏ κ, patF S κ ((l, m).2 κ)) =
      fun l => (freshAvg Finset.univ fun m : FTree → FLeaf => ∏ κ, patF S κ (m κ)) *
        (if l = I then (1 : ℝ≥0∞) else 0) from funext fun l => by
        dsimp only
        rw [freshAvg_mul (Finset.univ : Finset (FTree → FLeaf)) (if l = I then (1 : ℝ≥0∞) else 0)
          (fun m => ∏ κ, patF S κ (m κ)), mul_comm]]
  rw [freshAvg_mul, freshAvg_indicator_eq, card_indexE, freshAvg_pi_prod]
  simp only [avg_patF]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  have hcard : (Finset.univ.filter fun κ => (S κ).isSome = true).card = patSize S := rfl
  rw [hcard, pow_add, ENNReal.mul_inv (Or.inl (pow_ne_zero _ two_ne_zero))
    (Or.inl (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)), pow_mul]
  simp only [ENNReal.inv_pow]
  ring

/-! ### Products over the unsigned pairs -/

theorem prodU_eqB (L : QueryLog SigningSpec) (P : List Pair) (g : Pair → ℝ≥0∞) :
    prodU L P g = (P.map fun q => haveI := Classical.propDecidable (Unsigned L q);
      if Unsigned L q then g q else 1).prod := by
  classical
  unfold prodU
  induction P with
  | nil => simp
  | cons p P ih =>
      rw [List.filter_cons, List.map_cons, List.prod_cons]
      by_cases h : Unsigned L p
      · simp only [h, decide_true, if_true, List.map_cons, List.prod_cons]
        rw [ih]
      · simp only [h, decide_false, Bool.false_eq_true, if_false, one_mul]
        rw [ih]

theorem prodU_consB (L : QueryLog SigningSpec) (p : Pair) (P : List Pair) (g : Pair → ℝ≥0∞) :
    prodU L (p :: P) g = (haveI := Classical.propDecidable (Unsigned L p); if Unsigned L p then g p else 1) *
      prodU L P g := by
  rw [prodU_eqB, prodU_eqB, List.map_cons, List.prod_cons]

theorem prodU_congrB (L : QueryLog SigningSpec) {P : List Pair} {g g' : Pair → ℝ≥0∞} (h : ∀ q ∈ P, g q = g' q) :
    prodU L P g = prodU L P g' := by
  rw [prodU_eqB, prodU_eqB]
  congr 1
  exact List.map_congr_left fun q hq => by rw [h q hq]

/-- **Fewer unsigned pairs, smaller product**: the pairs in front are signed, the others keep
their factors and can only become signed. -/
theorem prodU_le_ofB (L L' : QueryLog SigningSpec) (new P : List Pair) (g g' : Pair → ℝ≥0∞)
    (hg1 : ∀ q, 1 ≤ g q) (hnew : ∀ q ∈ new, ¬Unsigned L' q) (hU : ∀ q, Unsigned L' q → Unsigned L q)
    (hgg : ∀ q ∈ P, g' q = g q) :
    prodU L' (new ++ P) g' ≤ prodU L P g := by
  classical
  rw [prodU_eqB, prodU_eqB, List.map_append, List.prod_append]
  have h1 : (new.map fun q => if Unsigned L' q then g' q else 1).prod = 1 := by
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    rw [if_neg (hnew q hq)]
  rw [h1, one_mul]
  refine List.prod_le_prod' fun q hq => ?_
  by_cases h' : Unsigned L' q
  · rw [if_pos h', if_pos (hU q h'), hgg q hq]
  · rw [if_neg h']
    split_ifs
    · exact hg1 q
    · exact le_rfl

/-! ### Translation invariance -/

section Shift

variable {V : Type} (U : Finset V) (w : ℝ≥0∞)

theorem fresh_shiftB (f : Multiset V → ℝ≥0∞) (x : Multiset V) :
    ∀ (m : ℕ) (d : Multiset V), fresh U f m (d + x) = fresh U (fun D => f (D + x)) m d
  | 0, _ => rfl
  | m + 1, d => by
      simp only [fresh]
      congr 1
      funext u
      rw [add_right_comm, fresh_shiftB f x m]

theorem virtualOnce_shiftB (f : Multiset V → ℝ≥0∞) (x : Multiset V) (m : ℕ) (coins : List V) (d : Multiset V) :
    virtualOnce U w f m coins (d + x) = virtualOnce U w (fun D => f (D + x)) m coins d := by
  unfold virtualOnce
  rw [← slotValue_translate]
  exact slotValue_congr (fun e => fresh_shiftB U f x m e) _ _

theorem virtualOnce_congrB {f g : Multiset V → ℝ≥0∞} (h : ∀ D, f D = g D) (m : ℕ) (coins : List V)
    (d : Multiset V) : virtualOnce U w f m coins d = virtualOnce U w g m coins d :=
  le_antisymm (virtualOnce_mono_base (fun x => (h x).le) m coins d)
    (virtualOnce_mono_base (fun x => (h x).ge) m coins d)

end Shift

theorem inDisc_add_of_not_mem {Q : Finset View} {v : View} (hv : v ∉ Q) (D : Multiset View) :
    inDisc Q (D + {v}) = inDisc Q D := by
  classical
  unfold inDisc
  have h : (D + {v}).toFinset = insert v D.toFinset := by
    ext x; simp
  rw [h, Finset.subset_insert_iff_of_notMem hv]

theorem grpAll_vinv (parameter : PublicParameter) (data : PublicData) (s : State) (excl : Pair → Prop)
    {F : Multiset View → ℝ≥0∞} {v : View} (hF : ∀ e, F (e + {v}) = F e) (Ms : List Message) (e : Multiset View) :
    grpAll parameter data s excl Ms F (e + {v}) = grpAll parameter data s excl Ms F e := by
  rw [← grpAll_shift]
  exact grpAll_congr s excl hF Ms e

theorem grp_ext_vinv {α V : Type} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (p : ℝ≥0∞) (A : ℕ) (U : Finset V)
    (st : α → LoopWalk.St) {ext ext' : α → Multiset V} {F : Multiset V → ℝ≥0∞} (d : Multiset V)
    (h : ∀ x, F (d + ext x) = F (d + ext' x)) :
    grp σ p A U st ext F d = grp σ p A U st ext' F d := by
  unfold grp
  rw [show (fun x => F (d + ext x)) = (fun x => F (d + ext' x)) from funext h]

/-- **A new landed pair whose view is irrelevant** does not raise the forecast of a term. -/
theorem termO_newPair_inv {parameter : PublicParameter} {data : PublicData} {w : ℝ≥0∞}
    {f : Multiset View → ℝ≥0∞} (hf : MonoFin f) {s : State} {Ms : List Message}
    (hM : MInv parameter data s Ms) (p : Pair) (hp0 : s.cache (pblk parameter data p firstCall) = none)
    (L : QueryLog SigningSpec) (u : DigestCall → HashOutput)
    (hl : Landed parameter (blockIndex (u firstCall))) (hinv : ∀ D, f (D + {viewOf u}) = f D)
    (d : Multiset View) (n k : ℕ) :
    termO parameter data w (withPair parameter data s p u) (addMsg Ms p.1) L (fun _ => False) f d n k ≤
      termO parameter data w s Ms L (fun _ => False) f d n k := by
  classical
  rw [← termO_addMsg hM L (fun _ => False) p.1 f d n k]
  set Ms' := addMsg Ms p.1 with hMs'
  have hnd : (live L Ms').Nodup := live_nodup L (addMsg_nodup hM.nodup _)
  unfold termO
  refine creations_mono (fun I => ?_) k []
  unfold termBase
  by_cases hmem : p.1 ∈ live L Ms'
  · set rest := (live L Ms').erase p.1 with hrest
    have hperm : (live L Ms').Perm (p.1 :: rest) := List.perm_cons_erase hmem
    have hnot : p.1 ∉ rest := fun h => (List.Nodup.mem_erase_iff hnd).1 h |>.1 rfl
    have hst : stOf parameter data p.1 s p.2 = .fresh := by
      have h : s.cache (blk parameter data p.1 p.2) = none := hp0
      simp [stOf, h]
    rw [grpAll_perm _ _ _ hperm d, grpAll_perm _ _ _ hperm d]
    simp only [grpAll]
    rw [grpM_withPair_self, if_pos hl, if_neg (fun h => h),
      grp_congr _ _ (fun e => grpAll_withPair_other s p u (fun _ => False)
        (virtualOnce Finset.univ w f n I) rest hnot e) d]
    have hFinv : ∀ e, grpAll parameter data s (fun _ => False) rest (virtualOnce Finset.univ w f n I) (e + {viewOf u}) =
        grpAll parameter data s (fun _ => False) rest (virtualOnce Finset.univ w f n I) e := by
      refine grpAll_vinv parameter data s _ (fun e => ?_) rest
      rw [virtualOnce_shiftB]
      exact virtualOnce_congrB _ _ (fun D => hinv D) n I e
    refine le_trans (le_of_eq (grp_ext_vinv _ _ _ _ _
      (ext' := Function.update (extOf parameter data s (fun _ => False) p.1) p.2 0) d ?_)) ?_
    · intro x
      by_cases hx : x = p.2
      · subst hx
        simp only [Function.update_self, add_zero]
        exact hFinv d
      · simp only [Function.update_of_ne hx]
    · exact grp_stop_le ForsPrice.landing_le_one Finset.univ_nonempty _ _
        (grpAll_mono s _ (virtualOnce_mono hf.1 n I) rest) d p.2 hst
  · exact le_of_eq (grpAll_withPair_other s p u _ _ _ hmem d)

end FORS.Security.SWRoute
