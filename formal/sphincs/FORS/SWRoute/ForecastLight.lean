import FORS.CoverBound.NearOption

/-! **Per-index forecasts: the light cap.** A per-index base `perIndex g` applies `g` to the number of
disclosed views at every index and sums over the indices. If `g` is below a separable good majorant
`ḡ` (monotone, convex, at most exponential), the one-coin H-term of `perIndex g` (the start value of
its forecast) is at most `2^b E_μ[ḡ]` at the table rate `μ` (`hTermO_perIndex_le`,
`startPerIndex_le`).

Two instances:
* the light failure `lightFail n*` (the number of indices with more than `n*` disclosed views) through
  the convex majorant `(n - n*)⁺`, with the rational Poisson tail `lightTail t n*` of a checked table
  (`startLight_le`);
* the binomial counts `C(n, D)` (the number of `D`-subsets of the views at an index), whose Poisson
  mean is `μ^D / D!` (`startChoose_le`). -/

open ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Security FORS.Security.H0 FORS.Security.H0Avg FORS.Base.H0 FORS.Base.Domination Concrete ForsPrice
  ForsPotential

set_option linter.unusedSectionVars false

/-! ### Per-index bases -/

/-- The number of disclosed views at index `l`. -/
def countAt (D : Multiset View) (l : Fin (2 ^ subtreeHeight)) : ℕ := (D.filter fun v => v.1 = l).card

/-- A per-index base: `g` of the number of disclosed views at every index, summed over the indices. -/
noncomputable def perIndex (g : ℕ → ℝ≥0∞) (D : Multiset View) : ℝ≥0∞ := ∑ l, g (countAt D l)

theorem countAt_mono {D D' : Multiset View} (h : D ≤ D') (l : Fin (2 ^ subtreeHeight)) :
    countAt D l ≤ countAt D' l :=
  Multiset.card_le_card (Multiset.filter_le_filter _ h)

theorem perIndex_mono {g : ℕ → ℝ≥0∞} (hg : Monotone g) : Monotone' (perIndex g) := fun _ _ h =>
  Finset.sum_le_sum fun l _ => hg (countAt_mono h l)

theorem card_marksAt (l : Fin (2 ^ subtreeHeight)) (D : Multiset View) : (marksAt l D).card = countAt D l := by
  unfold marksAt countAt
  rw [Multiset.card_map]

theorem avgN_card {U : Type} [Fintype U] [Nonempty U] (ψ : ℕ → ℝ≥0∞) :
    ∀ n (X : Multiset U), avgN (fun Y => ψ Y.card) n X = ψ (X.card + n)
  | 0, X => rfl
  | n + 1, X => by
      simp only [avgN]
      simp only [avgN_card ψ n, Multiset.card_add, Multiset.card_singleton]
      rw [show X.card + 1 + n = X.card + (n + 1) by ring]
      exact freshAvg_const _ Finset.univ_nonempty _

/-- **The H-term of a per-index base** through a separable good majorant. -/
theorem hTermO_perIndex_le (g gbar : ℕ → ℝ≥0∞) (hgG : SepGood gbar) (hg : ∀ n, g n ≤ gbar n)
    (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (N q : ℕ)
    (α γ : ℝ≥0) (hα : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * α = 1)
    (hγ : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * γ = lam * w) (μ : ℝ≥0)
    (hμ : (N : ℝ≥0) * α + (q : ℝ≥0) * γ ≤ μ) :
    hTermO (Finset.univ : Finset View) w lam N q (perIndex g) ≤
      (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * poisMean μ gbar := by
  have hdom : Dominated (perIndex g) (fun e : Multiset (Fin (2 ^ subtreeHeight)) =>
      ∑ l, gbar (e.count l) + 0 * ∏ l, (fun _ : ℕ => (1 : ℝ≥0∞)) (e.count l)) :=
    dominated_of_split (fun Ms => g Ms.card) (fun _ => 1) 0
      (fun d => by
        rw [zero_mul, add_zero]
        unfold perIndex
        exact le_of_eq (Finset.sum_congr rfl fun l _ => by rw [card_marksAt]))
      gbar (fun _ => 1)
      (fun n => by rw [avgN_card]; simpa using hg n)
      (fun n => le_of_eq (avgN_const 1 n 0))
  refine le_trans (hTermO_le_of_dominated w lam N q hdom) ?_
  have hcnt : (fun e : Multiset (Fin (2 ^ subtreeHeight)) =>
      ∑ l, gbar (e.count l) + 0 * ∏ l, (fun _ : ℕ => (1 : ℝ≥0∞)) (e.count l)) =
      fun e => (fun k : Fin (2 ^ subtreeHeight) → ℕ => ∑ l, gbar (k l) + 0 * ∏ l, (fun _ : ℕ => (1 : ℝ≥0∞)) (k l))
        (cnt id e) := by
    funext e
    simp only [cnt_id]
  rw [hcnt]
  refine le_trans (hTermO_le_poisIID_of_le id Finset.univ uniformIndex_id
    (sep_countGood hgG SepGood.one 0 ENNReal.zero_ne_top) w lam hw hlam α γ hα hγ N q μ hμ) (le_of_eq ?_)
  rw [poisIID_sep μ gbar (fun _ => 1) 0, zero_mul, add_zero]

/-- **The start value of a per-index forecast at the table rate.** For every budget `q ≤ qtop` of a
checked rate table, the H-term of `perIndex g` (coin `wbarOf q`, creations at `landing`) is at most
`2^b E_μ[ḡ]`. -/
theorem startPerIndex_le (H b N qtop : ℕ) (hH : totalHeight = H) (hb : subtreeHeight = b)
    (hN : signatureLimit = N) (t : PoisT) (hr : checkRate H b N qtop t = true)
    (g gbar : ℕ → ℝ≥0∞) (hgG : SepGood gbar) (hg : ∀ n, g n ≤ gbar n) (q : ℕ) (hq : q ≤ qtop) :
    hTermO (Finset.univ : Finset View) (wbarOf q) landing signatureLimit q (perIndex g) ≤
      (2 : ℝ≥0∞) ^ b * poisMean ⟨(t.mu : ℝ), by exact_mod_cast t.mu_nonneg⟩ gbar := by
  set w := wbarOf q with hwdef
  have hw1 : w ≤ 1 := wbar_le_one q (fair_of_rate H b N qtop t hr hH hb q hq)
  have hlw : landing * w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (mul_le_one' ForsPrice.landing_le_one hw1)
  have hcard : Fintype.card (Fin (2 ^ subtreeHeight)) = 2 ^ b := by rw [Fintype.card_fin, hb]
  set α : ℝ≥0 := ((2 : ℝ≥0) ^ b)⁻¹ with hαdef
  set γ : ℝ≥0 := (landing * w).toNNReal / (2 : ℝ≥0) ^ b with hγdef
  set μ : ℝ≥0 := ⟨(t.mu : ℝ), by exact_mod_cast t.mu_nonneg⟩ with hμdef
  have h2b0 : ((2 : ℝ≥0) ^ b) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hL : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ b := by rw [hcard]; push_cast; rfl
  have hα : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * α = 1 := by
    rw [hL, hαdef, ENNReal.coe_inv h2b0]
    push_cast
    exact ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hγ : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * γ = landing * w := by
    rw [hL, hγdef, ENNReal.coe_div h2b0, ENNReal.coe_toNNReal hlw]
    push_cast
    exact ENNReal.mul_div_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hμ : (signatureLimit : ℝ≥0) * α + (q : ℝ≥0) * γ ≤ μ := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [hμdef, hγdef, hαdef]
    push_cast
    calc (signatureLimit : ℝ) * ((2 : ℝ) ^ b)⁻¹ + (q : ℝ) * ((landing * w).toReal / 2 ^ b)
        = (signatureLimit : ℝ) / 2 ^ b + (q : ℝ) * (landing * w).toReal / 2 ^ b := by ring
      _ ≤ _ := rate_le_tableF H b N qtop t hr hH hb hN q hq
  have h := hTermO_perIndex_le g gbar hgG hg w landing hw1 ForsPrice.landing_le_one signatureLimit q α γ hα hγ μ hμ
  rwa [hL] at h

/-! ### The light failure -/

/-- **The light failure** at cap `n*`: the number of indices with more than `n*` disclosed views. -/
noncomputable def lightFail (nstar : ℕ) : Multiset View → ℝ≥0∞ :=
  perIndex fun n => if nstar < n then 1 else 0

theorem lightFail_mono (nstar : ℕ) : Monotone' (lightFail nstar) :=
  perIndex_mono fun a b hab => by
    by_cases ha : nstar < a
    · rw [if_pos ha, if_pos (lt_of_lt_of_le ha hab)]
    · rw [if_neg ha]; exact zero_le

theorem lightFail_le_card (nstar : ℕ) (D : Multiset View) :
    lightFail nstar D ≤ (2 : ℝ≥0∞) ^ subtreeHeight := by
  unfold lightFail perIndex
  calc ∑ l : Fin (2 ^ subtreeHeight), (if nstar < countAt D l then (1 : ℝ≥0∞) else 0)
      ≤ ∑ _l : Fin (2 ^ subtreeHeight), (1 : ℝ≥0∞) := Finset.sum_le_sum fun l _ => by split_ifs <;> simp
    _ = _ := by simp

theorem lightFail_props (nstar : ℕ) : MonoFin (lightFail nstar) :=
  ⟨lightFail_mono nstar, fun D => ne_top_of_le_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
    (lightFail_le_card nstar D)⟩

/-- An index whose count exceeds the cap is counted. -/
theorem one_le_lightFail {nstar : ℕ} {D : Multiset View} {l : Fin (2 ^ subtreeHeight)}
    (h : nstar < countAt D l) : 1 ≤ lightFail nstar D := by
  unfold lightFail perIndex
  calc (1 : ℝ≥0∞) = if nstar < countAt D l then 1 else 0 := by rw [if_pos h]
    _ ≤ _ := Finset.single_le_sum (f := fun l => if nstar < countAt D l then (1 : ℝ≥0∞) else 0)
        (fun _ _ => zero_le) (Finset.mem_univ l)

/-- The convex majorant `(n - n*)⁺` of the light failure, tabulated up to `n1` (slope one beyond). -/
def lightTab (n1 nstar : ℕ) : List ℚ := (List.range (n1 + 1)).map fun n => ((n - nstar : ℕ) : ℚ)

theorem lightTab_length (n1 nstar : ℕ) : (lightTab n1 nstar).length = n1 + 1 := by
  simp [lightTab]

theorem lightTab_getD {n1 nstar n : ℕ} (hn : n < n1 + 1) :
    (lightTab n1 nstar).getD n 0 = ((n - nstar : ℕ) : ℚ) := by
  unfold lightTab
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  simp

theorem checkLeaf_lightTab {n1 : ℕ} (h1 : 1 ≤ n1) (nstar : ℕ) : checkLeaf (lightTab n1 nstar) 1 = true := by
  simp only [checkLeaf, Bool.and_eq_true, decide_eq_true_eq, lightTab_length]
  refine ⟨⟨⟨⟨by omega, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [lightTab_getD (by omega)]
    positivity
  · intro n hn
    rw [lightTab_getD (by omega), lightTab_getD (by omega)]
    exact_mod_cast (show n - nstar ≤ n + 1 - nstar by omega)
  · intro n hn
    rw [lightTab_getD (by omega), lightTab_getD (by omega), lightTab_getD (by omega)]
    have : 2 * (n + 1 - nstar) ≤ (n - nstar) + (n + 2 - nstar) := by omega
    exact_mod_cast this
  · rw [lightTab_getD (by omega), lightTab_getD (by omega)]
    have h : n1 + 1 - 1 - nstar ≤ (n1 + 1 - 2 - nstar) + 1 := by omega
    have h' : ((n1 + 1 - 1 - nstar : ℕ) : ℚ) ≤ ((n1 + 1 - 2 - nstar : ℕ) : ℚ) + 1 := by exact_mod_cast h
    linarith

theorem lightFail_le_leafQ {n1 : ℕ} (h1 : 1 ≤ n1) (nstar n : ℕ) :
    (if nstar < n then (1 : ℝ≥0∞) else 0) ≤ ENNReal.ofReal (leafQ (lightTab n1 nstar) 1 n : ℝ) := by
  split_ifs with hn
  · rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hq : (1 : ℚ) ≤ leafQ (lightTab n1 nstar) 1 n := by
      unfold leafQ
      rw [lightTab_length]
      split_ifs with hlt
      · rw [lightTab_getD hlt]
        exact_mod_cast (show 1 ≤ n - nstar by omega)
      · rw [lightTab_getD (by omega)]
        have h0 : (0 : ℚ) ≤ ((n1 + 1 - 1 - nstar : ℕ) : ℚ) := by positivity
        have h2 : (1 : ℚ) ≤ ((n - (n1 + 1 - 1) : ℕ) : ℚ) := by exact_mod_cast (show 1 ≤ n - (n1 + 1 - 1) by omega)
        linarith
    exact_mod_cast hq
  · exact zero_le

/-- **The light tail** of a Poisson table: the mean of `(n - n*)⁺`, head up to `n1` and geometric tail. -/
def lightTail (t : PoisT) (nstar : ℕ) : ℚ :=
  ((List.range (t.n1 + 1)).map fun n => t.pb n * ((n - nstar : ℕ) : ℚ)).sum +
    t.pb (t.n1 + 1) * (((t.n1 - nstar : ℕ) : ℚ) / (1 - t.r) + 1 / (1 - t.r) ^ 2)

theorem lightTail_nonneg {t : PoisT} (ht : checkPT t = true) (nstar : ℕ) : 0 ≤ lightTail t nstar := by
  have hr1 : t.r < 1 := (checkPT_parts ht).2.2.2
  have h1r : 0 < 1 - t.r := by linarith
  unfold lightTail
  apply add_nonneg
  · apply List.sum_nonneg
    intro x hx
    obtain ⟨n, -, rfl⟩ := List.mem_map.1 hx
    exact mul_nonneg (t.pb_nonneg n) (by positivity)
  · exact mul_nonneg (t.pb_nonneg _) (by positivity)

/-- **The light failure's start value.** For every budget `q ≤ qtop` of a checked rate table with
`n1 ≥ 1`, the H-term of the light failure at cap `n*` is at most `2^b` times the light tail. -/
theorem startLight_le (H b N qtop : ℕ) (hH : totalHeight = H) (hb : subtreeHeight = b)
    (hN : signatureLimit = N) (t : PoisT) (hr : checkRate H b N qtop t = true) (ht : checkPT t = true)
    (h1 : 1 ≤ t.n1) (nstar q : ℕ) (hq : q ≤ qtop) :
    hTermO (Finset.univ : Finset View) (wbarOf q) landing signatureLimit q (lightFail nstar) ≤
      ENNReal.ofReal ((2 ^ b * lightTail t nstar : ℚ) : ℝ) := by
  have hleaf := checkLeaf_lightTab h1 nstar
  refine le_trans (startPerIndex_le H b N qtop hH hb hN t hr _
    (fun n => ENNReal.ofReal (leafQ (lightTab t.n1 nstar) 1 n : ℝ)) (leaf_sepGood hleaf)
    (lightFail_le_leafQ h1 nstar) q hq) ?_
  have hpm := poisMean_leaf_le ht hleaf (lightTab_length t.n1 nstar)
  have hsum : (((List.range (t.n1 + 1)).map fun n => t.pb n * (lightTab t.n1 nstar).getD n 0).sum +
      t.pb (t.n1 + 1) * ((lightTab t.n1 nstar).getD t.n1 0 / (1 - t.r) + 1 / (1 - t.r) ^ 2)) =
      lightTail t nstar := by
    unfold lightTail
    rw [lightTab_getD (by omega)]
    congr 2
    refine List.map_congr_left fun n hn => ?_
    rw [lightTab_getD (List.mem_range.1 hn)]
  rw [hsum] at hpm
  have h0 : (0 : ℝ) ≤ ((lightTail t nstar : ℚ) : ℝ) := by
    exact_mod_cast lightTail_nonneg ht nstar
  calc (2 : ℝ≥0∞) ^ b * poisMean ⟨(t.mu : ℝ), by exact_mod_cast t.mu_nonneg⟩
        (fun n => ENNReal.ofReal (leafQ (lightTab t.n1 nstar) 1 n : ℝ))
      ≤ (2 : ℝ≥0∞) ^ b * ENNReal.ofReal ((lightTail t nstar : ℚ) : ℝ) := mul_le_mul_right hpm _
    _ = _ := by
        rw [show ((2 ^ b * lightTail t nstar : ℚ) : ℝ) = (2 : ℝ) ^ b * ((lightTail t nstar : ℚ) : ℝ) by
          push_cast; ring, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat]

/-! ### Binomial counts -/

theorem choose_sepGood (D : ℕ) : SepGood (fun n => ((n.choose D : ℕ) : ℝ≥0∞)) where
  mono := fun a b hab => by
    show ((a.choose D : ℕ) : ℝ≥0∞) ≤ ((b.choose D : ℕ) : ℝ≥0∞)
    exact_mod_cast Nat.choose_le_choose D hab
  convex := by
    intro n
    have h : (n + 1).choose D + (n + 1).choose D ≤ (n + 2).choose D + n.choose D := by
      rcases D with _ | d
      · simp
      · have e1 : (n + 1).choose (d + 1) = n.choose d + n.choose (d + 1) := Nat.choose_succ_succ n d
        have e2 : (n + 2).choose (d + 1) = (n + 1).choose d + (n + 1).choose (d + 1) :=
          Nat.choose_succ_succ (n + 1) d
        have e3 : n.choose d ≤ (n + 1).choose d := Nat.choose_le_choose d (Nat.le_succ n)
        omega
    show (((n + 1).choose D : ℕ) : ℝ≥0∞) + (((n + 1).choose D : ℕ) : ℝ≥0∞) ≤
      (((n + 2).choose D : ℕ) : ℝ≥0∞) + ((n.choose D : ℕ) : ℝ≥0∞)
    exact_mod_cast h
  growth := ⟨1, fun n => by
    simp only [ENNReal.coe_one, one_mul]
    exact_mod_cast Nat.choose_le_two_pow n D⟩

/-- **The Poisson factorial moment**: `E[C(N, D)] = μ^D / D!` for `N ~ Poisson(μ)`. -/
theorem poisMean_choose (μ : ℝ≥0) (D : ℕ) :
    poisMean μ (fun n => ((n.choose D : ℕ) : ℝ≥0∞)) = ENNReal.ofReal ((μ : ℝ) ^ D / D.factorial) := by
  unfold poisMean
  rw [← Summable.sum_add_tsum_nat_add' (f := fun m => poisW μ m * ((m.choose D : ℕ) : ℝ≥0∞)) (k := D)
    ENNReal.summable]
  have hhead : ∑ i ∈ Finset.range D, poisW μ i * ((i.choose D : ℕ) : ℝ≥0∞) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.1 hi)]
    simp
  rw [hhead, zero_add]
  have hterm : ∀ j : ℕ, poisW μ (j + D) * (((j + D).choose D : ℕ) : ℝ≥0∞) =
      ENNReal.ofReal ((μ : ℝ) ^ D / D.factorial) * poisW μ j := by
    intro j
    unfold poisW
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have hf' : ((j + D).choose D : ℝ) * j.factorial * D.factorial = (j + D).factorial := by
      exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial j D
    rw [← hf']
    have hC : ((j + D).choose D : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (Nat.le_add_left D j)).ne'
    have hj : (j.factorial : ℝ) ≠ 0 := by positivity
    have hD : (D.factorial : ℝ) ≠ 0 := by positivity
    rw [pow_add]
    field_simp
  simp only [hterm, ENNReal.tsum_mul_left, poisW_tsum, mul_one]

/-- **The start value of the binomial counts**: for every budget `q ≤ qtop` of a checked rate table,
the H-term of `perIndex C(·, D)` is at most `2^b μ̄^D / D!`. -/
theorem startChoose_le (H b N qtop : ℕ) (hH : totalHeight = H) (hb : subtreeHeight = b)
    (hN : signatureLimit = N) (t : PoisT) (hr : checkRate H b N qtop t = true) (D q : ℕ) (hq : q ≤ qtop) :
    hTermO (Finset.univ : Finset View) (wbarOf q) landing signatureLimit q
        (perIndex fun n => ((n.choose D : ℕ) : ℝ≥0∞)) ≤
      ENNReal.ofReal ((2 ^ b * t.mu ^ D / D.factorial : ℚ) : ℝ) := by
  refine le_trans (startPerIndex_le H b N qtop hH hb hN t hr _ _ (choose_sepGood D) (fun _ => le_rfl) q hq) ?_
  rw [poisMean_choose]
  have hmu : (0 : ℝ) ≤ (t.mu : ℝ) := by exact_mod_cast t.mu_nonneg
  rw [show ((2 ^ b * t.mu ^ D / D.factorial : ℚ) : ℝ) = (2 : ℝ) ^ b * ((t.mu : ℝ) ^ D / D.factorial) by
    push_cast; ring, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  exact le_rfl

end FORS.Security.SWRoute
