import FORS.SWRoute.Interface
import FORS.CoverBound.HTermOption

/-! **The near H-term at a baseline: a kernel-checkable option.** The SW route reserves, per budget
unit, the near H-term at a baseline `b0`: the start value `startExcessG witnessNear w b0 q`, the
one-coin H-term of the excess of the near price `Σ_l κ yN_l` over `b0`. The option splits the excess
as the cover option does (`Base/Split.lean`),
`(Σ_l y_l - c)^+ ≤ Σ_l (y_l - c1)^+ + e^{-θ c} / (e θ) Π_l e^{θ min(y_l, c1)}` with `y_l = κ yN_l`,
and bounds the per-index averages with `n` views by the mean `E[y | n] ≤ nBound n` and the support
`y ≤ UN(n) = k 2^-H (min(n, A) / A)^(k-1)`, `A = 2^a` (a near-covered target's other trees are among at
most `min(n, A)` disclosed leaves each), through the chords of the two functions on `[0, UN(n)]`:
* `(y - c1)^+ ≤ y (1 - c1 / UN)^+`, so `ḡ(n) ≥ nBound n · (1 - c1 / UN(n))^+`;
* `e^{θ min(y, c1)} ≤ 1 + y (e^{θ z} - 1) / z` with `z = min(UN(n), c1)`, so
  `h̄(n) ≥ min(e^{θ c1} - 1, nBound n · sl(n))`.
The leaf tables, their Poisson means and the bound `B ≥ 2^b Eg + (1 + Ee)^(2^b) / (e^{θ cthr} e θ)` are
checked as for `OptF` (`checkOptNB`); `buildOptNB` rebuilds an option from its scalars. -/

open ENNReal NNReal

namespace FORS.Security.H0

variable [Params]

open Concrete ForsPrice FORS.Base.H0 FORS.Base.Domination H0Avg ForsPotential

set_option linter.unusedSectionVars false

/-! ### The option and its check -/

/-- A near option at a baseline: the cap `c1`, the Chernoff parameter `θ`, the threshold `cthr`,
`s` squarings for `eC ≥ e^{θ c1}`, the leaf tables `ḡ`, `h̄ - 1` with their slopes and Poisson
means, and the bound `B`. -/
structure OptNB where
  c1 : ℚ
  θ : ℚ
  cthr : ℚ
  s : ℕ
  eC : ℚ
  gt : List ℚ
  Jg : ℚ
  ht : List ℚ
  Jh : ℚ
  Eg : ℚ
  Ee : ℚ
  B : ℚ

/-- The support bound of the near value at an index with `n` views: `k 2^-H (min(n, A) / A)^(k-1)`. -/
def UNQ (H k a n : ℕ) : ℚ := k * κQ H * (((min n (2 ^ a) : ℕ) : ℚ) / 2 ^ a) ^ (k - 1)

/-- The excess part bound at `n`. -/
def gNB (H k a : ℕ) (o : OptNB) (n : ℕ) : ℚ :=
  if UNQ H k a n ≤ o.c1 then 0 else nBound H k a n * (1 - o.c1 / UNQ H k a n)

/-- The chord slope of the capped exponential on `[0, UN(n)]`. -/
def slNB (H k a P : ℕ) (o : OptNB) (n : ℕ) : ℚ :=
  if o.c1 ≤ UNQ H k a n then (o.eC - 1) / o.c1 else (expUp (o.θ * UNQ H k a n) o.s P - 1) / UNQ H k a n

/-- The Chernoff factor bound (minus one) at `n`. -/
def hNB (H k a P : ℕ) (o : OptNB) (n : ℕ) : ℚ := min (o.eC - 1) (nBound H k a n * slNB H k a P o n)

/-- The Poisson mean of a leaf table with its linear extension, as `checkOptF` reads it. -/
def meanNB (t : PoisT) (tab : List ℚ) (J : ℚ) : ℚ :=
  ((List.range (t.n1 + 1)).map fun n => t.pb n * tab.getD n 0).sum +
    t.pb (t.n1 + 1) * (tab.getD t.n1 0 / (1 - t.r) + J / (1 - t.r) ^ 2)

/-- **The check of a near option** against a Poisson table, for subtree height `b`. -/
def checkOptNB (H b k a : ℕ) (t : PoisT) (o : OptNB) : Bool :=
  decide (0 < o.c1) && decide (0 < o.θ) && decide (0 ≤ o.cthr) && decide (o.θ * o.c1 < 2 ^ o.s) &&
    decide (expUp (o.θ * o.c1) o.s t.P ≤ o.eC) &&
    decide (t.n1 ≤ 150) && decide (o.gt.length = t.n1 + 1) && decide (o.ht.length = t.n1 + 1) &&
    checkLeaf o.gt o.Jg && checkLeaf o.ht o.Jh &&
    decide (∀ n < t.n1 + 1, gNB H k a o n ≤ o.gt.getD n 0) &&
    decide (∀ n < t.n1 + 1, hNB H k a t.P o n ≤ o.ht.getD n 0) &&
    decide ((k : ℚ) * κQ H ≤ o.gt.getD t.n1 0 + o.Jg) && decide (o.eC - 1 ≤ o.ht.getD t.n1 0 + o.Jh) &&
    decide (meanNB t o.gt o.Jg ≤ o.Eg) && decide (meanNB t o.ht o.Jh ≤ o.Ee) &&
    decide (2 ^ b * o.Eg + sqUp t.P b (1 + o.Ee) / (expLow (o.θ * o.cthr) t.J t.P * eLowQ * o.θ) ≤ o.B) &&
    decide (0 ≤ o.Eg) && decide (0 ≤ o.Ee)

theorem checkOptNB_parts {H b k a : ℕ} {t : PoisT} {o : OptNB} (h : checkOptNB H b k a t o = true) :
    0 < o.c1 ∧ 0 < o.θ ∧ 0 ≤ o.cthr ∧ o.θ * o.c1 < 2 ^ o.s ∧ expUp (o.θ * o.c1) o.s t.P ≤ o.eC ∧
      t.n1 ≤ 150 ∧ o.gt.length = t.n1 + 1 ∧ o.ht.length = t.n1 + 1 ∧
      checkLeaf o.gt o.Jg = true ∧ checkLeaf o.ht o.Jh = true ∧
      (∀ n < t.n1 + 1, gNB H k a o n ≤ o.gt.getD n 0) ∧ (∀ n < t.n1 + 1, hNB H k a t.P o n ≤ o.ht.getD n 0) ∧
      (k : ℚ) * κQ H ≤ o.gt.getD t.n1 0 + o.Jg ∧ o.eC - 1 ≤ o.ht.getD t.n1 0 + o.Jh ∧
      meanNB t o.gt o.Jg ≤ o.Eg ∧ meanNB t o.ht o.Jh ≤ o.Ee ∧
      2 ^ b * o.Eg + sqUp t.P b (1 + o.Ee) / (expLow (o.θ * o.cthr) t.J t.P * eLowQ * o.θ) ≤ o.B ∧
      0 ≤ o.Eg ∧ 0 ≤ o.Ee := by
  simp only [checkOptNB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩,
    h16⟩, h17⟩, h18⟩, h19⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩

theorem optNB_B_nonneg {H b k a : ℕ} {t : PoisT} {o : OptNB} (h : checkOptNB H b k a t o = true) : 0 ≤ o.B := by
  obtain ⟨-, hθ, hcthr, -, -, -, -, -, -, -, -, -, -, -, -, -, hB, hEg0, hEe0⟩ := checkOptNB_parts h
  refine le_trans ?_ hB
  have hL := one_le_expLow (o.θ * o.cthr) t.J t.P (mul_nonneg hθ.le hcthr)
  have he : (0 : ℚ) < eLowQ := by unfold eLowQ; norm_num
  have hsq : 0 ≤ sqUp t.P b (1 + o.Ee) := by
    have h := sqUp_ge t.P b (1 + o.Ee) ((1 + o.Ee : ℚ) : ℝ) (by push_cast; positivity) le_rfl
    have h0 : (0 : ℝ) ≤ ((1 + o.Ee : ℚ) : ℝ) ^ (2 ^ b) := by push_cast; positivity
    exact_mod_cast le_trans h0 h
  have : 0 < expLow (o.θ * o.cthr) t.J t.P * eLowQ * o.θ := by
    have : (0 : ℚ) < expLow (o.θ * o.cthr) t.J t.P := by linarith
    positivity
  positivity

theorem optNB_cthr_nonneg {H b k a : ℕ} {t : PoisT} {o : OptNB} (h : checkOptNB H b k a t o = true) :
    0 ≤ o.cthr :=
  (checkOptNB_parts h).2.2.1

/-! ### Building an option from its scalars -/

/-- The loop of `convexNB`: each entry raised to at least the line through the two before it. -/
def convexGoNB : ℚ → ℚ → List ℚ → List ℚ
  | _, _, [] => []
  | a, b, x :: xs => max x (2 * b - a) :: convexGoNB b (max x (2 * b - a)) xs

/-- The least convex increasing list above a list (from the left). -/
def convexNB : List ℚ → List ℚ
  | [] => []
  | [x] => [x]
  | x :: y :: xs => x :: max y x :: convexGoNB x (max y x) xs

/-- The extension slope of a leaf table with cap `cap`. -/
def leafJNB (n1 : ℕ) (tab : List ℚ) (cap : ℚ) : ℚ :=
  max (max (tab.getD n1 0 - tab.getD (n1 - 1) 0) (cap - tab.getD n1 0)) 0

/-- **The option with cap `c1`, Chernoff parameter `θ`, `s` squarings and threshold `cthr`**
(`fill_optNB` of `scripts/fors_sw_near.py`). -/
def buildOptNB (H b k a : ℕ) (t : PoisT) (c1 θ : ℚ) (s : ℕ) (cthr : ℚ) : OptNB :=
  let eC := expUp (θ * c1) s t.P
  let o0 : OptNB := ⟨c1, θ, cthr, s, eC, [], 0, [], 0, 0, 0, 0⟩
  let gt := convexNB ((List.range (t.n1 + 1)).map fun n => rup (gNB H k a o0 n) (64 + 127))
  let ht := convexNB ((List.range (t.n1 + 1)).map fun n => rup (hNB H k a t.P o0 n) (64 + 64))
  let Jg := leafJNB t.n1 gt ((k : ℚ) * κQ H)
  let Jh := leafJNB t.n1 ht (eC - 1)
  let Eg := rup (meanNB t gt Jg) (64 + 127 + 2 * b)
  let Ee := rup (meanNB t ht Jh) (64 + 2 * b)
  let B := rup (2 ^ b * Eg + sqUp t.P b (1 + Ee) / (expLow (θ * cthr) t.J t.P * eLowQ * θ)) (64 + 127)
  ⟨c1, θ, cthr, s, eC, gt, Jg, ht, Jh, Eg, Ee, B⟩

/-! ### The support of the near value -/

theorem φF_le_min (Xs : Multiset FLeaf) :
    φF Xs ≤ ENNReal.ofReal (((min (Multiset.card Xs) (2 ^ forsHeight) : ℕ) : ℝ) / 2 ^ forsHeight) := by
  classical
  unfold φF freshAvg CoverF
  simp only [Finset.card_univ]
  rw [show Fintype.card FLeaf = 2 ^ forsHeight from Fintype.card_fin _]
  have hc : (Finset.univ.filter fun t : FLeaf => t ∈ Xs).card ≤ min (Multiset.card Xs) (2 ^ forsHeight) := by
    refine le_min ?_ ?_
    · calc (Finset.univ.filter fun t : FLeaf => t ∈ Xs).card ≤ Xs.toFinset.card :=
            Finset.card_le_card fun t ht => by simpa using ht
        _ ≤ Multiset.card Xs := Multiset.toFinset_card_le Xs
    · calc (Finset.univ.filter fun t : FLeaf => t ∈ Xs).card ≤ (Finset.univ : Finset FLeaf).card :=
            Finset.card_filter_le _ _
        _ = 2 ^ forsHeight := by rw [Finset.card_univ]; exact Fintype.card_fin _
  calc _ = ((2 ^ forsHeight : ℕ) : ℝ≥0∞)⁻¹ * (((Finset.univ.filter fun t : FLeaf => t ∈ Xs).card : ℕ) : ℝ≥0∞) := by
        congr 1
        rw [Finset.card_filter, Nat.cast_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        split_ifs <;> simp_all
    _ ≤ ENNReal.ofReal (((min (Multiset.card Xs) (2 ^ forsHeight) : ℕ) : ℝ) / 2 ^ forsHeight) := by
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.div_eq_inv_mul,
          show ENNReal.ofReal ((2 : ℝ) ^ forsHeight) = ((2 ^ forsHeight : ℕ) : ℝ≥0∞) by
            rw [← ENNReal.ofReal_natCast]; push_cast; rfl]
        exact mul_le_mul_right (by exact_mod_cast hc) _

/-- **The support bound**: `yN ≤ k (min(n, A) / A)^(k-1)` for `n` marks. -/
theorem yN_le_supp (Ms : Multiset (FTree → FLeaf)) :
    yN Ms ≤ ENNReal.ofReal ((forsTrees : ℝ) *
      (((min (Multiset.card Ms) (2 ^ forsHeight) : ℕ) : ℝ) / 2 ^ forsHeight) ^ (forsTrees - 1)) := by
  set r : ℝ := ((min (Multiset.card Ms) (2 ^ forsHeight) : ℕ) : ℝ) / 2 ^ forsHeight with hr
  have hr0 : 0 ≤ r := by positivity
  unfold yN
  have hκ : ∀ κ : FTree, ∏ κ', nearFactor κ κ' (Ms.map fun m => m κ') ≤ ENNReal.ofReal r ^ (forsTrees - 1) := by
    intro κ
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ κ), nearFactor_self, one_mul]
    calc ∏ κ' ∈ Finset.univ.erase κ, nearFactor κ κ' (Ms.map fun m => m κ')
        ≤ ∏ _κ' ∈ Finset.univ.erase κ, ENNReal.ofReal r := by
          refine Finset.prod_le_prod' fun κ' hκ' => ?_
          rw [nearFactor_of_ne (Finset.ne_of_mem_erase hκ')]
          have := φF_le_min (Ms.map fun m => m κ')
          rwa [Multiset.card_map] at this
      _ = _ := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_ftree]
  calc ∑ κ, ∏ κ', nearFactor κ κ' (Ms.map fun m => m κ') ≤ ∑ _κ : FTree, ENNReal.ofReal r ^ (forsTrees - 1) :=
        Finset.sum_le_sum fun κ _ => hκ κ
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, card_ftree, nsmul_eq_mul, ← ENNReal.ofReal_pow hr0,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]

theorem κE_eq_ofReal (H b : ℕ) (hH : totalHeight = H) (hb : subtreeHeight = b) :
    κE = ENNReal.ofReal (κQ H : ℝ) := by
  rw [← κE_toReal H b hH hb, ENNReal.ofReal_toReal κE_ne_top]

/-- The near value at an index, in reals. -/
theorem yNR_le {H b k a : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b) (hk : forsTrees = k)
    (ha : forsHeight = a) (Ms : Multiset (FTree → FLeaf)) :
    κE.toReal * (yN Ms).toReal ≤ (UNQ H k a (Multiset.card Ms) : ℝ) := by
  have hy := yN_le_supp Ms
  have hne : yN Ms ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (yN_le Ms)
  have hκ := κE_toReal H b hH hb
  have hyr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hy
  rw [ENNReal.toReal_ofReal (by positivity)] at hyr
  rw [hκ]
  unfold UNQ
  subst hk ha
  push_cast
  have hκ0 : (0 : ℝ) ≤ (κQ H : ℝ) := by unfold κQ; positivity
  calc (κQ H : ℝ) * (yN Ms).toReal ≤ (κQ H : ℝ) * ((forsTrees : ℝ) *
        (((min (Multiset.card Ms) (2 ^ forsHeight) : ℕ) : ℝ) / 2 ^ forsHeight) ^ (forsTrees - 1)) :=
        mul_le_mul_of_nonneg_left hyr hκ0
    _ = _ := by push_cast; ring

theorem yNR_nonneg (Ms : Multiset (FTree → FLeaf)) : 0 ≤ κE.toReal * (yN Ms).toReal := by positivity

theorem ofReal_yNR (Ms : Multiset (FTree → FLeaf)) :
    ENNReal.ofReal (κE.toReal * (yN Ms).toReal) = κE * yN Ms := by
  have hne : yN Ms ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (yN_le Ms)
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal κE_ne_top, ENNReal.ofReal_toReal hne]

/-! ### The split of the near excess -/

/-- The per-index excess part of the near split. -/
noncomputable def gN (c1 : ℝ) (Ms : Multiset (FTree → FLeaf)) : ℝ≥0∞ :=
  ENNReal.ofReal (κE.toReal * (yN Ms).toReal - c1)

/-- The per-index Chernoff factor of the near split. -/
noncomputable def hN (c1 θ : ℝ) (Ms : Multiset (FTree → FLeaf)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (θ * min (κE.toReal * (yN Ms).toReal) c1))

/-- **The pointwise split** of the excess of the near price over a threshold. -/
theorem excessNear_le_split (b0 : ℝ≥0∞) (c c1 θ : ℝ) (hc : ENNReal.ofReal c ≤ b0) (hθ : 0 < θ)
    (d : Multiset View) :
    excessW witnessNear b0 d ≤ ∑ l : Fin (2 ^ subtreeHeight), gN c1 (marksAt l d) +
      ENNReal.ofReal (Real.exp (-θ * c) / (Real.exp 1 * θ)) * ∏ l : Fin (2 ^ subtreeHeight), hN c1 θ (marksAt l d) := by
  unfold excessW
  rw [priceNear_decomp]
  set y : Fin (2 ^ subtreeHeight) → ℝ := fun l => κE.toReal * (yN (marksAt l d)).toReal with hy
  have hsum : ∑ l : Fin (2 ^ subtreeHeight), κE * yN (marksAt l d) = ENNReal.ofReal (∑ l, y l) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun l _ => yNR_nonneg _)]
    exact Finset.sum_congr rfl fun l _ => (ofReal_yNR _).symm
  rw [hsum]
  calc ENNReal.ofReal (∑ l, y l) - b0 ≤ ENNReal.ofReal (∑ l, y l) - ENNReal.ofReal c := tsub_le_tsub_left hc _
    _ ≤ ENNReal.ofReal (∑ l, y l - c) := by
        rcases le_total c 0 with h0 | h0
        · rw [ENNReal.ofReal_of_nonpos h0, tsub_zero]
          exact ENNReal.ofReal_le_ofReal (by linarith)
        · rw [← ENNReal.ofReal_sub _ h0]
    _ ≤ ENNReal.ofReal (∑ l, max (y l - c1) 0 +
          Real.exp (-θ * c) / (Real.exp 1 * θ) * ∏ l, Real.exp (θ * min (y l) c1)) :=
        ENNReal.ofReal_le_ofReal (FORS.Base.H0.split_real _ c c1 θ hθ)
    _ = _ := by
        rw [ENNReal.ofReal_add (Finset.sum_nonneg fun l _ => le_max_right _ _) (by positivity),
          ENNReal.ofReal_sum_of_nonneg (fun l _ => le_max_right _ _),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_prod_of_nonneg (fun l _ => by positivity)]
        congr 1
        refine Finset.sum_congr rfl fun l _ => ?_
        unfold gN
        rcases le_total (y l - c1) 0 with h | h
        · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
        · rw [max_eq_left h]

/-- **The near H-term through the split.** -/
theorem hTermO_near_split_le (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (N q : ℕ) (b0 : ℝ≥0∞) (c c1 θ : ℝ)
    (hc : ENNReal.ofReal c ≤ b0) (hθ : 0 < θ) (gbar hbar : ℕ → ℝ≥0∞) (hgG : SepGood gbar) (hhG : SepGood hbar)
    (hg : ∀ n, avgN (gN c1) n 0 ≤ gbar n) (hh : ∀ n, avgN (hN c1 θ) n 0 ≤ hbar n)
    (α γ : ℝ≥0) (hα : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * α = 1)
    (hγ : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * γ = lam * w) (μ : ℝ≥0)
    (hμ : (N : ℝ≥0) * α + (q : ℝ≥0) * γ ≤ μ) :
    hTermO (Finset.univ : Finset View) w lam N q (excessW witnessNear b0) ≤
      (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * poisMean μ gbar +
        ENNReal.ofReal (Real.exp (-θ * c) / (Real.exp 1 * θ)) * poisMean μ hbar ^ Fintype.card (Fin (2 ^ subtreeHeight)) := by
  set A := ENNReal.ofReal (Real.exp (-θ * c) / (Real.exp 1 * θ)) with hAdef
  have hdom : Dominated (excessW witnessNear b0) (fun e : Multiset (Fin (2 ^ subtreeHeight)) =>
      ∑ l, gbar (e.count l) + A * ∏ l, hbar (e.count l)) :=
    dominated_of_split (gN c1) (hN c1 θ) A (fun d => excessNear_le_split b0 c c1 θ hc hθ d) gbar hbar hg hh
  refine le_trans (hTermO_le_of_dominated w lam N q hdom) ?_
  have hcnt : (fun e : Multiset (Fin (2 ^ subtreeHeight)) => ∑ l, gbar (e.count l) + A * ∏ l, hbar (e.count l)) =
      fun e => (fun k : Fin (2 ^ subtreeHeight) → ℕ => ∑ l, gbar (k l) + A * ∏ l, hbar (k l)) (cnt id e) := by
    funext e
    simp only [cnt_id]
  rw [hcnt]
  refine le_trans (hTermO_le_poisIID_of_le id Finset.univ uniformIndex_id
    (sep_countGood hgG hhG A ENNReal.ofReal_ne_top) w lam hw hlam α γ hα hγ N q μ hμ) (le_of_eq ?_)
  exact poisIID_sep μ gbar hbar A

/-! ### The per-index bounds -/

/-- Averages over `n` marks only see multisets of `n` marks. -/
theorem avgN_le_of_card {U : Type} [Fintype U] [Nonempty U] {φ ψ : Multiset U → ℝ≥0∞} (m : ℕ)
    (h : ∀ X : Multiset U, Multiset.card X = m → φ X ≤ ψ X) :
    ∀ j (X : Multiset U), Multiset.card X + j = m → avgN φ j X ≤ avgN ψ j X
  | 0, X, hX => h X (by simpa using hX)
  | j + 1, X, hX => freshAvg_mono _ fun u _ => avgN_le_of_card m h j (X + {u}) (by
      rw [Multiset.card_add, Multiset.card_singleton]; omega)

theorem avgN_le_of_card0 {U : Type} [Fintype U] [Nonempty U] {φ ψ : Multiset U → ℝ≥0∞} (n : ℕ)
    (h : ∀ X : Multiset U, Multiset.card X = n → φ X ≤ ψ X) : avgN φ n 0 ≤ avgN ψ n 0 :=
  avgN_le_of_card n h n 0 (by simp)

/-- The mean of the near value at an index with `n ≤ 150` views. -/
theorem avgN_κyN_le {H b k a : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b)
    (hk : forsTrees = k) (ha : forsHeight = a) (n : ℕ) (hn : n ≤ 150) :
    avgN (fun Ms => κE * yN Ms) n 0 ≤ ENNReal.ofReal (nBound H k a n : ℝ) := by
  subst hk ha
  have hκ0 : (0 : ℝ) ≤ (κQ H : ℝ) := by unfold κQ; positivity
  have hκE := κE_eq_ofReal H b hH hb
  have hcard : ∀ c : ℝ≥0∞, ∑ _κ : FTree, c = (forsTrees : ℝ≥0∞) * c := fun c => by
    simp only [Finset.sum_const, Finset.card_univ, card_ftree, nsmul_eq_mul]
  rw [avgN_const_mul, avgN_yN, hcard]
  have hP1 := Ψ1R_le_tab n hn
  have hΨ1 : 0 ≤ Ψ1R n := avgNR_nonneg coverAvg_nonneg n 0
  have hterm : ENNReal.ofReal (Ψ1R n) ^ (forsTrees - 1) ≤
      ENNReal.ofReal ((((P1tab forsHeight).getD n 0 ^ (forsTrees - 1) : ℚ)) : ℝ) := by
    rw [← ENNReal.ofReal_pow hΨ1]
    apply ENNReal.ofReal_le_ofReal
    push_cast
    exact pow_le_pow_left₀ hΨ1 hP1 (forsTrees - 1)
  calc κE * ((forsTrees : ℝ≥0∞) * ENNReal.ofReal (Ψ1R n) ^ (forsTrees - 1))
      ≤ κE * ((forsTrees : ℝ≥0∞) *
          ENNReal.ofReal ((((P1tab forsHeight).getD n 0 ^ (forsTrees - 1) : ℚ)) : ℝ)) :=
        mul_le_mul_right (mul_le_mul_right hterm _) _
    _ = ENNReal.ofReal ((nBound H forsTrees forsHeight n : ℚ) : ℝ) := by
        rw [hκE, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul hκ0]
        congr 1
        unfold nBound
        push_cast
        ring

theorem nBound_nonneg (H k a n : ℕ) : 0 ≤ nBound H k a n := by
  unfold nBound κQ
  have : 0 ≤ (P1tab a).getD n 0 := by
    rw [List.getD_eq_getElem?_getD]
    cases h : (P1tab a)[n]? with
    | none => simp
    | some x =>
        have hx := List.mem_of_getElem? h
        simp only [P1tab, List.mem_map] at hx
        obtain ⟨y, -, rfl⟩ := hx
        simp only [Option.getD_some]
        positivity
  positivity

/-- The chord of the exponential: `e^{θ z} ≤ 1 + z (e^{θ Z} - 1) / Z` on `[0, Z]`. -/
theorem exp_chord (θ z Z : ℝ) (hθ : 0 < θ) (hz : 0 ≤ z) (hzZ : z ≤ Z) (hZ : 0 < Z) :
    Real.exp (θ * z) ≤ 1 + z * ((Real.exp (θ * Z) - 1) / Z) := by
  have hq := exp_quad (θ * z) (θ * Z) (by positivity) (mul_le_mul_of_nonneg_left hzZ hθ.le) (by positivity)
  have hA : 0 ≤ Real.exp (θ * Z) - 1 - θ * Z := by linarith [Real.add_one_le_exp (θ * Z)]
  have hr : θ * z / (θ * Z) = z / Z := by field_simp
  rw [hr] at hq
  have hr0 : 0 ≤ z / Z := by positivity
  have hr1 : z / Z ≤ 1 := (div_le_one hZ).2 hzZ
  have hsq : (z / Z) ^ 2 ≤ z / Z := by nlinarith
  calc Real.exp (θ * z) ≤ 1 + θ * z + (Real.exp (θ * Z) - 1 - θ * Z) * (z / Z) ^ 2 := hq
    _ ≤ 1 + θ * z + (Real.exp (θ * Z) - 1 - θ * Z) * (z / Z) := by gcongr
    _ = _ := by field_simp; ring

theorem optNB_exp_le {H b k a : ℕ} {t : PoisT} {o : OptNB} (ho : checkOptNB H b k a t o = true) :
    Real.exp ((o.θ : ℝ) * o.c1) ≤ (o.eC : ℝ) := by
  obtain ⟨hc1, hθ, -, hs, heC, -⟩ := checkOptNB_parts ho
  have h := exp_le_expUp (o.θ * o.c1) o.s t.P (by positivity) hs
  have h' : ((expUp (o.θ * o.c1) o.s t.P : ℚ) : ℝ) ≤ (o.eC : ℝ) := by exact_mod_cast heC
  push_cast at h
  linarith

/-- **The capped exponential below its chord**, pointwise: `e^{θ min(y, c1)} ≤ 1 + sl(n) y` for
`0 ≤ y ≤ UN(n)`, and the slope is nonnegative. -/
theorem exp_le_slNB {H b k a : ℕ} {t : PoisT} {o : OptNB} (ho : checkOptNB H b k a t o = true) (n : ℕ)
    (y : ℝ) (hy0 : 0 ≤ y) (hyU : y ≤ (UNQ H k a n : ℝ)) :
    0 ≤ slNB H k a t.P o n ∧ Real.exp ((o.θ : ℝ) * min y o.c1) ≤ 1 + y * (slNB H k a t.P o n : ℝ) := by
  obtain ⟨hc1, hθ, -, hs, -⟩ := checkOptNB_parts ho
  have hc1' : (0 : ℝ) < (o.c1 : ℝ) := by exact_mod_cast hc1
  have hθ' : (0 : ℝ) < (o.θ : ℝ) := by exact_mod_cast hθ
  have hexp := optNB_exp_le ho
  unfold slNB
  by_cases hU : o.c1 ≤ UNQ H k a n
  · rw [if_pos hU]
    have h1 : 1 ≤ (o.eC : ℝ) := le_trans (Real.one_le_exp (by positivity)) hexp
    have hsl0 : (0 : ℝ) ≤ ((o.eC : ℝ) - 1) / o.c1 := div_nonneg (by linarith) hc1'.le
    refine ⟨by exact_mod_cast hsl0, ?_⟩
    have hz0 : 0 ≤ min y (o.c1 : ℝ) := le_min hy0 hc1'.le
    have hch := exp_chord (o.θ : ℝ) (min y o.c1) o.c1 hθ' hz0 (min_le_right _ _) hc1'
    push_cast
    calc Real.exp ((o.θ : ℝ) * min y o.c1) ≤ 1 + min y o.c1 * ((Real.exp ((o.θ : ℝ) * o.c1) - 1) / o.c1) := hch
      _ ≤ 1 + y * (((o.eC : ℝ) - 1) / o.c1) := by
          gcongr
          · exact div_nonneg (by linarith [Real.one_le_exp (by positivity : (0 : ℝ) ≤ (o.θ : ℝ) * o.c1)]) hc1'.le
          · exact min_le_left _ _
  · rw [if_neg hU]
    push Not at hU
    have hU' : (UNQ H k a n : ℝ) < (o.c1 : ℝ) := by exact_mod_cast hU
    have hU0 : (0 : ℝ) ≤ (UNQ H k a n : ℝ) := le_trans hy0 hyU
    have hmin : min y (o.c1 : ℝ) = y := min_eq_left (by linarith)
    rw [hmin]
    have hu0 : 0 ≤ o.θ * UNQ H k a n := mul_nonneg hθ.le (by exact_mod_cast hU0)
    have hus : o.θ * UNQ H k a n < 2 ^ o.s := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hU.le hθ.le) hs
    have hE := exp_le_expUp (o.θ * UNQ H k a n) o.s t.P hu0 hus
    push_cast at hE
    have hE1 : (1 : ℝ) ≤ (expUp (o.θ * UNQ H k a n) o.s t.P : ℝ) :=
      le_trans (Real.one_le_exp (by positivity)) hE
    have hE1q : (1 : ℚ) ≤ expUp (o.θ * UNQ H k a n) o.s t.P := by exact_mod_cast hE1
    have hU0q : (0 : ℚ) ≤ UNQ H k a n := by exact_mod_cast hU0
    refine ⟨div_nonneg (by linarith) hU0q, ?_⟩
    rcases hU0.lt_or_eq with hpos | hzero
    · have hch := exp_chord (o.θ : ℝ) y (UNQ H k a n) hθ' hy0 hyU hpos
      push_cast
      calc Real.exp ((o.θ : ℝ) * y) ≤ 1 + y * ((Real.exp ((o.θ : ℝ) * (UNQ H k a n : ℝ)) - 1) / (UNQ H k a n : ℝ)) := hch
        _ ≤ _ := by gcongr
    · have hy : y = 0 := le_antisymm (hzero ▸ hyU) hy0
      rw [hy]
      simp

/-- **The excess part is dominated by the `ḡ` table.** -/
theorem avgN_gN_le {H b k a : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b)
    (hk : forsTrees = k) (ha : forsHeight = a) {t : PoisT} {o : OptNB}
    (ho : checkOptNB H b k a t o = true) (n : ℕ) :
    avgN (gN (o.c1 : ℝ)) n 0 ≤ ENNReal.ofReal (leafQ o.gt o.Jg n : ℝ) := by
  obtain ⟨hc1, -, -, -, -, h150, hgl, -, hlg, -, hgb, -, hgend, -⟩ := checkOptNB_parts ho
  have hc1' : (0 : ℝ) < (o.c1 : ℝ) := by exact_mod_cast hc1
  have hκE := κE_eq_ofReal H b hH hb
  have hκ0 : (0 : ℝ) ≤ (κQ H : ℝ) := by unfold κQ; positivity
  have hlin : ∀ Ms, gN (o.c1 : ℝ) Ms ≤ κE * yN Ms := fun Ms => by
    unfold gN
    rw [← ofReal_yNR]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  by_cases hn : n < t.n1 + 1
  · rw [leafQ_of_lt (by omega)]
    have hgn := hgb n hn
    unfold gNB at hgn
    by_cases hU : UNQ H k a n ≤ o.c1
    · have h0 : avgN (gN (o.c1 : ℝ)) n 0 ≤ avgN (fun _ : Multiset (FTree → FLeaf) => (0 : ℝ≥0∞)) n 0 := by
        refine avgN_le_of_card0 n fun Ms hMs => le_of_eq (ENNReal.ofReal_of_nonpos ?_)
        have hy := yNR_le hH hb hk ha Ms
        rw [hMs] at hy
        have hU' : (UNQ H k a n : ℝ) ≤ (o.c1 : ℝ) := by exact_mod_cast hU
        linarith
      rw [avgN_const] at h0
      exact le_trans h0 zero_le
    · rw [if_neg hU] at hgn
      push Not at hU
      have hU' : (o.c1 : ℝ) < (UNQ H k a n : ℝ) := by exact_mod_cast hU
      have hUpos : (0 : ℝ) < (UNQ H k a n : ℝ) := lt_trans hc1' hU'
      have hf0 : (0 : ℝ) ≤ 1 - (o.c1 : ℝ) / (UNQ H k a n : ℝ) := by
        rw [sub_nonneg, div_le_one hUpos]; exact hU'.le
      have hpt : avgN (gN (o.c1 : ℝ)) n 0 ≤
          avgN (fun Ms => ENNReal.ofReal (1 - (o.c1 : ℝ) / (UNQ H k a n : ℝ)) * (κE * yN Ms)) n 0 := by
        refine avgN_le_of_card0 n fun Ms hMs => ?_
        have hy := yNR_le hH hb hk ha Ms
        rw [hMs] at hy
        have hy0 := yNR_nonneg Ms
        unfold gN
        rw [← ofReal_yNR, ← ENNReal.ofReal_mul hf0]
        apply ENNReal.ofReal_le_ofReal
        set y := κE.toReal * (yN Ms).toReal
        have : (o.c1 : ℝ) * y / (UNQ H k a n : ℝ) ≤ o.c1 := by
          rw [div_le_iff₀ hUpos]; exact mul_le_mul_of_nonneg_left hy hc1'.le
        have e : (1 - (o.c1 : ℝ) / (UNQ H k a n : ℝ)) * y = y - (o.c1 : ℝ) * y / (UNQ H k a n : ℝ) := by
          field_simp
        rw [e]; linarith
      rw [avgN_const_mul] at hpt
      refine le_trans hpt (le_trans (mul_le_mul_right (avgN_κyN_le hH hb hk ha n (by omega)) _) ?_)
      rw [← ENNReal.ofReal_mul hf0]
      apply ENNReal.ofReal_le_ofReal
      have hgn' : ((nBound H k a n * (1 - o.c1 / UNQ H k a n) : ℚ) : ℝ) ≤ (o.gt.getD n 0 : ℝ) := by
        exact_mod_cast hgn
      push_cast at hgn'
      linarith
  · have hcap : avgN (gN (o.c1 : ℝ)) n 0 ≤ ENNReal.ofReal (((k : ℚ) * κQ H : ℚ) : ℝ) := by
      subst hk
      calc avgN (gN (o.c1 : ℝ)) n 0 ≤ avgN (fun _ => κE * (forsTrees : ℝ≥0∞)) n 0 :=
            avgN_mono (fun Ms => le_trans (hlin Ms) (mul_le_mul_right (yN_le Ms) _)) n 0
        _ = κE * (forsTrees : ℝ≥0∞) := avgN_const _ n 0
        _ = _ := by
            rw [hκE, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hκ0]
            congr 1
            push_cast
            ring
    refine le_trans hcap (ENNReal.ofReal_le_ofReal ?_)
    have h := leafQ_ge_end hlg (n := n) (by omega)
    rw [hgl, show t.n1 + 1 - 1 = t.n1 by omega] at h
    exact_mod_cast le_trans hgend h

/-- **The Chernoff factor is dominated by `1 + h̄`.** -/
theorem avgN_hN_le {H b k a : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b)
    (hk : forsTrees = k) (ha : forsHeight = a) {t : PoisT} {o : OptNB}
    (ho : checkOptNB H b k a t o = true) (n : ℕ) :
    avgN (hN (o.c1 : ℝ) (o.θ : ℝ)) n 0 ≤ 1 + ENNReal.ofReal (leafQ o.ht o.Jh n : ℝ) := by
  obtain ⟨hc1, hθ, -, hs, heC, h150, -, hhl, -, hlh, -, hhb, -, hhend, -⟩ := checkOptNB_parts ho
  have hθ' : (0 : ℝ) < (o.θ : ℝ) := by exact_mod_cast hθ
  have hexp := optNB_exp_le ho
  have hcap : avgN (hN (o.c1 : ℝ) (o.θ : ℝ)) n 0 ≤ 1 + ENNReal.ofReal ((o.eC - 1 : ℚ) : ℝ) := by
    calc avgN (hN (o.c1 : ℝ) (o.θ : ℝ)) n 0 ≤ avgN (fun _ => ENNReal.ofReal (Real.exp ((o.θ : ℝ) * o.c1))) n 0 :=
          avgN_mono (fun Ms => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_left (min_le_right _ _) hθ'.le))) n 0
      _ = ENNReal.ofReal (Real.exp ((o.θ : ℝ) * o.c1)) := avgN_const _ n 0
      _ ≤ ENNReal.ofReal (1 + ((o.eC - 1 : ℚ) : ℝ)) := ENNReal.ofReal_le_ofReal (by push_cast; linarith)
      _ = _ := by
          have : (0 : ℝ) ≤ ((o.eC - 1 : ℚ) : ℝ) := by
            have := Real.one_le_exp (by positivity : (0 : ℝ) ≤ (o.θ : ℝ) * o.c1)
            push_cast; linarith
          rw [ENNReal.ofReal_add zero_le_one this, ENNReal.ofReal_one]
  by_cases hn : n < t.n1 + 1
  · rw [leafQ_of_lt (by omega)]
    set sl := slNB H k a t.P o n with hsl
    have hsl0 : 0 ≤ sl := (exp_le_slNB ho n 0 le_rfl (by
      have hU := yNR_le hH hb hk ha (Multiset.replicate n (fun _ => 0))
      rw [Multiset.card_replicate] at hU
      exact le_trans (yNR_nonneg _) hU)).1
    have hsl0' : (0 : ℝ) ≤ (sl : ℝ) := by exact_mod_cast hsl0
    have hpt : avgN (hN (o.c1 : ℝ) (o.θ : ℝ)) n 0 ≤
        avgN (fun Ms => 1 + ENNReal.ofReal (sl : ℝ) * (κE * yN Ms)) n 0 := by
      refine avgN_le_of_card0 n fun Ms hMs => ?_
      have hy := yNR_le hH hb hk ha Ms
      rw [hMs] at hy
      have hy0 := yNR_nonneg Ms
      have he := (exp_le_slNB ho n _ hy0 hy).2
      unfold hN
      rw [← ofReal_yNR, ← ENNReal.ofReal_mul hsl0', ← ENNReal.ofReal_one,
        ← ENNReal.ofReal_add zero_le_one (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [← hsl] at he
      linarith
    rw [avgN_add, avgN_const, avgN_const_mul] at hpt
    have hquad : avgN (hN (o.c1 : ℝ) (o.θ : ℝ)) n 0 ≤
        1 + ENNReal.ofReal ((nBound H k a n * sl : ℚ) : ℝ) := by
      refine le_trans hpt (add_le_add le_rfl (le_trans
        (mul_le_mul_right (avgN_κyN_le hH hb hk ha n (by omega)) _) (le_of_eq ?_)))
      rw [← ENNReal.ofReal_mul hsl0']
      congr 1
      push_cast
      ring
    have hmin : avgN (hN (o.c1 : ℝ) (o.θ : ℝ)) n 0 ≤ 1 + ENNReal.ofReal ((hNB H k a t.P o n : ℚ) : ℝ) := by
      unfold hNB
      rcases min_choice (o.eC - 1) (nBound H k a n * slNB H k a t.P o n) with h | h <;> rw [h]
      · exact hcap
      · exact hquad
    exact le_trans hmin (add_le_add le_rfl (ENNReal.ofReal_le_ofReal (by exact_mod_cast hhb n hn)))
  · refine le_trans hcap (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
    have h := leafQ_ge_end hlh (n := n) (by omega)
    rw [hhl, show t.n1 + 1 - 1 = t.n1 by omega] at h
    exact_mod_cast le_trans hhend h

/-! ### The near H-term -/

/-- **A near option bounds the near H-term** at every baseline `b0 ≥ cthr`, whenever the rate
`N / 2^b + q λ w / 2^b` is below the table rate. -/
theorem hTermO_near_le_optNB {H b k a : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b)
    (hk : forsTrees = k) (ha : forsHeight = a) (t : PoisT) (o : OptNB) (ht : checkPT t = true)
    (ho : checkOptNB H b k a t o = true) (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (N q : ℕ)
    (hrate : (N : ℝ) / 2 ^ b + (q : ℝ) * (lam * w).toReal / 2 ^ b ≤ (t.mu : ℝ))
    (b0 : ℝ≥0∞) (hb0 : ENNReal.ofReal (o.cthr : ℝ) ≤ b0) :
    hTermO (Finset.univ : Finset View) w lam N q (excessW witnessNear b0) ≤ ENNReal.ofReal (o.B : ℝ) := by
  obtain ⟨hc1, hθ, hcthr, -, -, -, hgl, hhl, hlg, hlh, -, -, -, -, hEg, hEe, hB, hEg0, hEe0⟩ :=
    checkOptNB_parts ho
  have hθ' : (0 : ℝ) < (o.θ : ℝ) := by exact_mod_cast hθ
  have hlw : lam * w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (mul_le_one' hlam hw)
  have hcard : Fintype.card (Fin (2 ^ subtreeHeight)) = 2 ^ b := by rw [Fintype.card_fin, hb]
  set α : ℝ≥0 := ((2 : ℝ≥0) ^ b)⁻¹ with hαdef
  set γ : ℝ≥0 := (lam * w).toNNReal / (2 : ℝ≥0) ^ b with hγdef
  set μ : ℝ≥0 := ⟨(t.mu : ℝ), by exact_mod_cast t.mu_nonneg⟩ with hμdef
  have h2b0 : ((2 : ℝ≥0) ^ b) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hL : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ b := by rw [hcard]; push_cast; rfl
  have hα : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * α = 1 := by
    rw [hL, hαdef, ENNReal.coe_inv h2b0]
    push_cast
    exact ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hγ : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * γ = lam * w := by
    rw [hL, hγdef, ENNReal.coe_div h2b0, ENNReal.coe_toNNReal hlw]
    push_cast
    exact ENNReal.mul_div_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hμ : (N : ℝ≥0) * α + (q : ℝ≥0) * γ ≤ μ := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [hμdef, hγdef, hαdef]
    push_cast
    calc (N : ℝ) * ((2 : ℝ) ^ b)⁻¹ + (q : ℝ) * ((lam * w).toReal / 2 ^ b)
        = (N : ℝ) / 2 ^ b + (q : ℝ) * (lam * w).toReal / 2 ^ b := by ring
      _ ≤ _ := hrate
  have hmain := hTermO_near_split_le w lam hw hlam N q b0 (o.cthr : ℝ) (o.c1 : ℝ) (o.θ : ℝ) hb0 hθ'
    (fun n => ENNReal.ofReal (leafQ o.gt o.Jg n : ℝ)) (fun n => 1 + ENNReal.ofReal (leafQ o.ht o.Jh n : ℝ))
    (leaf_sepGood hlg) (SepGood.one_add (leaf_sepGood hlh)) (avgN_gN_le hH hb hk ha ho)
    (avgN_hN_le hH hb hk ha ho) α γ hα hγ μ hμ
  rw [poisMean_one_add] at hmain
  have hg := poisMean_leaf_le ht hlg hgl
  have hh := poisMean_leaf_le ht hlh hhl
  rw [← hμdef] at hg hh
  have hEg' : poisMean μ (fun n => ENNReal.ofReal (leafQ o.gt o.Jg n : ℝ)) ≤ ENNReal.ofReal (o.Eg : ℝ) :=
    le_trans hg (ENNReal.ofReal_le_ofReal (Rat.cast_le.2 hEg))
  have hEe' : poisMean μ (fun n => ENNReal.ofReal (leafQ o.ht o.Jh n : ℝ)) ≤ ENNReal.ofReal (o.Ee : ℝ) :=
    le_trans hh (ENNReal.ofReal_le_ofReal (Rat.cast_le.2 hEe))
  have hp := pref_le o.θ o.cthr t.J t.P hθ hcthr
  set prefQ : ℚ := 1 / (expLow (o.θ * o.cthr) t.J t.P * eLowQ * o.θ) with hprefQ
  have hpref0 : 0 ≤ prefQ := by
    rw [hprefQ]
    have := one_le_expLow (o.θ * o.cthr) t.J t.P (by positivity)
    have : (0 : ℚ) < eLowQ := by unfold eLowQ; norm_num
    positivity
  have hsq0 : 0 ≤ sqUp t.P b (1 + o.Ee) := by
    have h := sqUp_ge t.P b (1 + o.Ee) ((1 + o.Ee : ℚ) : ℝ) (by push_cast; positivity) le_rfl
    have h0 : (0 : ℝ) ≤ ((1 + o.Ee : ℚ) : ℝ) ^ (2 ^ b) := by push_cast; positivity
    exact_mod_cast le_trans h0 h
  rw [hL, hcard] at hmain
  calc hTermO (Finset.univ : Finset View) w lam N q (excessW witnessNear b0)
      ≤ (2 : ℝ≥0∞) ^ b * ENNReal.ofReal (o.Eg : ℝ) +
          ENNReal.ofReal (prefQ : ℝ) * ENNReal.ofReal ((1 + o.Ee : ℚ) : ℝ) ^ (2 ^ b) := by
        refine le_trans hmain (add_le_add (mul_le_mul_right hEg' _) (mul_le_mul' (ENNReal.ofReal_le_ofReal hp) ?_))
        refine pow_le_pow_left' ?_ _
        rw [show ((1 + o.Ee : ℚ) : ℝ) = 1 + (o.Ee : ℝ) by push_cast; ring, ENNReal.ofReal_add zero_le_one
          (by exact_mod_cast hEe0), ENNReal.ofReal_one]
        exact add_le_add le_rfl hEe'
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ b * o.Eg) + ENNReal.ofReal (prefQ : ℝ) * ENNReal.ofReal (sqUp t.P b (1 + o.Ee) : ℝ) := by
        gcongr
        · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
        · exact ofReal_pow_le_sqUp t.P b (1 + o.Ee)
    _ = ENNReal.ofReal (((2 : ℚ) ^ b * o.Eg + sqUp t.P b (1 + o.Ee) * prefQ : ℚ) : ℝ) := by
        rw [← ENNReal.ofReal_mul (by exact_mod_cast hpref0), ← ENNReal.ofReal_add (by
          have : (0 : ℝ) ≤ (o.Eg : ℝ) := by exact_mod_cast hEg0
          positivity) (mul_nonneg (by exact_mod_cast hpref0) (by exact_mod_cast hsq0))]
        push_cast
        ring_nf
    _ ≤ ENNReal.ofReal (o.B : ℝ) := by
        apply ENNReal.ofReal_le_ofReal
        have h8' : ((2 : ℚ) ^ b * o.Eg + sqUp t.P b (1 + o.Ee) * prefQ) ≤ o.B := by
          rw [hprefQ, mul_one_div]
          exact hB
        exact_mod_cast h8'

theorem startExcessG_near_eq (w b0 : ℝ≥0∞) (q : ℕ) :
    ForsPotential.startExcessG ForsPotential.witnessNear w b0 q =
      hTermO (Finset.univ : Finset View) w landing signatureLimit q (excessW witnessNear b0) := rfl

/-- **The near start value of the SW route** at a baseline `b0 ≥ cthr`, for every budget `q ≤ qtop`,
from a checked Poisson table and a checked near option. -/
theorem startExcessG_near_le_optNB {H b k a N qtop : ℕ} (hH : totalHeight = H) (hb : subtreeHeight = b)
    (hk : forsTrees = k) (ha : forsHeight = a) (hN : signatureLimit = N) (t : PoisT) (o : OptNB)
    (hr : checkRate H b N qtop t = true) (ht : checkPT t = true) (ho : checkOptNB H b k a t o = true)
    (q : ℕ) (hq : q ≤ qtop) (b0 : ℝ≥0∞) (hb0 : ENNReal.ofReal (o.cthr : ℝ) ≤ b0) :
    ForsPotential.startExcessG ForsPotential.witnessNear (wbarOf q) b0 q ≤ ENNReal.ofReal (o.B : ℝ) := by
  rw [startExcessG_near_eq]
  have hw1 : wbarOf q ≤ 1 := wbar_le_one q (fair_of_rate H b N qtop t hr hH hb q hq)
  exact hTermO_near_le_optNB hH hb hk ha t o ht ho (wbarOf q) landing hw1 ForsPrice.landing_le_one
    signatureLimit q (rate_le_tableF H b N qtop t hr hH hb hN q hq) b0 hb0

end FORS.Security.H0
