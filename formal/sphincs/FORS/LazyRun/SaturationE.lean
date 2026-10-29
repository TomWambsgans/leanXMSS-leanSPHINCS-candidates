import FORS.LazyRun.Saturation

/-! **The remaining-budget weight with a real exponent** (survival-weighted route).
`budgetE e p r = ((N - p - r) / (N - p))^e` with a real exponent `e`; `budget` is the case `e = 2`.
The survival-weighted route runs the budget at the exponent `ρ` while nothing is armed, at `2` once
armed, and higher after contacts. This file holds the budget, its probe step, its digest decrement,
and the real inequalities behind the exponent jumps. -/

open ENNReal

namespace FORS.Security.HiddenDebt

/-! ### Real inequalities -/

/-- **Bernoulli, tangent from below**: for `e ≥ 1` and `0 ≤ u ≤ w`, `e u^(e-1) (w - u) ≤ w^e - u^e`. -/
theorem rpow_sub_rpow_ge {e u w : ℝ} (he : 1 ≤ e) (hu : 0 ≤ u) (huw : u ≤ w) :
    e * u ^ (e - 1) * (w - u) ≤ w ^ e - u ^ e := by
  rcases hu.eq_or_lt with rfl | hu
  · rcases he.eq_or_lt with rfl | he'
    · simp
    · rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
      have : 0 ≤ w ^ e := Real.rpow_nonneg (by linarith) e
      simp [this]
  · have hs : -1 ≤ w / u - 1 := by
      have : 0 ≤ w / u := div_nonneg (by linarith) hu.le
      linarith
    have hb := one_add_mul_self_le_rpow_one_add hs he
    rw [add_sub_cancel, Real.div_rpow (by linarith) hu.le] at hb
    have hue : 0 < u ^ e := Real.rpow_pos_of_pos hu e
    have hsplit : u ^ e = u ^ (e - 1) * u := by
      rw [Real.rpow_sub_one hu.ne']; field_simp
    have h2 := mul_le_mul_of_nonneg_left hb hue.le
    rw [mul_div_cancel₀ _ hue.ne'] at h2
    have h3 : u ^ e * (1 + e * (w / u - 1)) = u ^ e + e * u ^ (e - 1) * (w - u) := by
      rw [hsplit]; field_simp
    linarith

/-- **Bernoulli, exponent in `[0, 1]`**: `ρ / (1 + (ρ - 1) x / (1 - x)) ≤ ρ (1 - x)^(ρ - 1)` for
`1 ≤ ρ ≤ 2` and `0 ≤ x < 1`. -/
theorem div_bernoulli_le_rpow {ρ x : ℝ} (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ρ / (1 + (ρ - 1) * x / (1 - x)) ≤ ρ * (1 - x) ^ (ρ - 1) := by
  have hy : 0 < 1 - x := by linarith
  have hs : -1 ≤ x / (1 - x) := by
    have : 0 ≤ x / (1 - x) := div_nonneg hx0 hy.le
    linarith
  have hb := rpow_one_add_le_one_add_mul_self hs (p := ρ - 1) (by linarith) (by linarith)
  have hbase : 1 + x / (1 - x) = (1 - x)⁻¹ := by field_simp; ring
  rw [hbase, Real.inv_rpow hy.le] at hb
  have hpos : 0 < (1 - x) ^ (ρ - 1) := Real.rpow_pos_of_pos hy _
  have hden : 0 < 1 + (ρ - 1) * x / (1 - x) := by
    have : 0 ≤ (ρ - 1) * x / (1 - x) := div_nonneg (mul_nonneg (by linarith) hx0) hy.le
    linarith
  rw [div_le_iff₀ hden]
  have hmul : (ρ - 1) * x / (1 - x) = (ρ - 1) * (x / (1 - x)) := by ring
  rw [hmul]
  have : 1 ≤ (1 - x) ^ (ρ - 1) * (1 + (ρ - 1) * (x / (1 - x))) := by
    rw [inv_le_iff_one_le_mul₀ hpos] at hb
    linarith [mul_comm ((1 - x) ^ (ρ - 1)) (1 + (ρ - 1) * (x / (1 - x)))]
  nlinarith

/-- **The exponent jump**: `1 - v^c ≤ c (1 - v) / v` for `0 < v` and `0 ≤ c`. -/
theorem one_sub_rpow_le_jump {v c : ℝ} (hv : 0 < v) (hc : 0 ≤ c) : 1 - v ^ c ≤ c * (1 - v) / v := by
  rw [Real.rpow_def_of_pos hv]
  have h1 := Real.add_one_le_exp (Real.log v * c)
  have h2 : Real.log v⁻¹ ≤ v⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr hv)
  rw [Real.log_inv] at h2
  have h3 : c * (1 - v) / v = c * (v⁻¹ - 1) := by field_simp
  rw [h3]
  nlinarith

/-- **The exponent jump, two exponents**: `v^a - v^b ≤ (b - a) (1 - v) / v · v^a` for `0 < v`, `a ≤ b`. -/
theorem rpow_sub_rpow_le_jump {v a b : ℝ} (hv : 0 < v) (hab : a ≤ b) :
    v ^ a - v ^ b ≤ (b - a) * (1 - v) / v * v ^ a := by
  have hsplit : v ^ b = v ^ a * v ^ (b - a) := by rw [← Real.rpow_add hv]; ring_nf
  have hj := one_sub_rpow_le_jump hv (sub_nonneg.mpr hab)
  have hva : 0 < v ^ a := Real.rpow_pos_of_pos hv a
  rw [hsplit]
  nlinarith

/-- **Arming at one point**: `v^ρ - v^2 ≤ (2 - ρ) v (1 - v)` for `0 < v` and `1 ≤ ρ ≤ 2`. -/
theorem rpow_sub_sq_le {v ρ : ℝ} (hv : 0 < v) (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) :
    v ^ ρ - v ^ 2 ≤ (2 - ρ) * v * (1 - v) := by
  have hs : -1 ≤ v⁻¹ - 1 := by have := inv_pos.mpr hv; linarith
  have hb := rpow_one_add_le_one_add_mul_self hs (p := 2 - ρ) (by linarith) (by linarith)
  rw [add_sub_cancel, Real.inv_rpow hv.le] at hb
  have hsplit : v ^ ρ = v ^ (2 : ℝ) * (v ^ (2 - ρ))⁻¹ := by
    rw [← Real.rpow_neg hv.le, ← Real.rpow_add hv]; ring_nf
  rw [hsplit, Real.rpow_two]
  have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
  have := mul_le_mul_of_nonneg_left hb hv2
  have h3 : v ^ 2 * (1 + (2 - ρ) * (v⁻¹ - 1)) = v ^ 2 + (2 - ρ) * v * (1 - v) := by field_simp
  linarith

variable [Params]

set_option linter.unusedSectionVars false

/-- Remaining-budget weight with a real exponent `e`: `((N - p - r) / (N - p))^e`. -/
noncomputable def budgetE (e : ℝ) (probes remaining : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((spaceReal - probes - remaining) / (spaceReal - probes)) ^ e)

/-- The second-order upper bound of `1 - (1 - x)^ρ` for `1 ≤ ρ ≤ 2`. -/
noncomputable def satUp (ρ x : ℝ) : ℝ := ρ * x - ρ * (ρ - 1) * x ^ 2 / 2

/-- **`1 - (1 - x)^ρ ≤ ρ x - ρ (ρ - 1) x² / 2`** for `0 ≤ x ≤ 1`, `1 ≤ ρ ≤ 2`: the third derivative
of `(1 - x)^ρ` is nonnegative. -/
theorem one_sub_rpow_le_satUp {ρ x : ℝ} (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - (1 - x) ^ ρ ≤ satUp ρ x := by
  set g : ℝ → ℝ := fun y => (1 - y) ^ ρ - 1 + ρ * y - ρ * (ρ - 1) * y ^ 2 / 2 with hg
  have hd : ∀ y, HasDerivAt g (-1 * ρ * (1 - y) ^ (ρ - 1) + ρ - ρ * (ρ - 1) * y) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    have h2 := h1.rpow_const (p := ρ) (Or.inr hρ1)
    have h3 := ((h2.sub_const 1).add ((hasDerivAt_id y).const_mul ρ)).sub
      (((hasDerivAt_pow 2 y).const_mul (ρ * (ρ - 1))).div_const 2)
    exact h3.congr_deriv (by push_cast; ring)
  have hmono : MonotoneOn g (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun y _ => (hd y).continuousAt.continuousWithinAt
    · exact fun y _ => (hd y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hd y).deriv]
      have hs : -1 ≤ -y := by linarith [hy.2]
      have hb := rpow_one_add_le_one_add_mul_self hs (p := ρ - 1) (by linarith) (by linarith)
      rw [← sub_eq_add_neg] at hb
      nlinarith
  have h := hmono ⟨le_refl 0, zero_le_one⟩ ⟨hx0, hx1⟩ hx0
  simp only [hg, sub_zero, Real.one_rpow] at h
  unfold satUp
  nlinarith

/-! ### The budget -/

theorem budgetE_two (probes remaining : ℕ) : budgetE 2 probes remaining = budget probes remaining := by
  rw [budgetE, budget, Real.rpow_two]

theorem budgetE_base_nonneg {probes remaining : ℕ} (hbudget : (probes + remaining : ℝ) ≤ spaceReal) :
    0 ≤ (spaceReal - probes - remaining) / (spaceReal - probes) :=
  div_nonneg (by linarith) (by linarith [(Nat.cast_nonneg remaining : (0 : ℝ) ≤ remaining)])

theorem budgetE_base_le_one {probes remaining : ℕ} (hbudget : (probes + remaining : ℝ) ≤ spaceReal) :
    (spaceReal - probes - remaining) / (spaceReal - probes) ≤ 1 :=
  div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg remaining : (0 : ℝ) ≤ remaining)])
    (by linarith [(Nat.cast_nonneg remaining : (0 : ℝ) ≤ remaining)])

/-- The base `v = (N - p - r) / (N - p)` is at least `1 - T / 2^128` when `p + r ≤ T ≤ N`. -/
theorem budgetE_base_ge {probes remaining total : ℕ} (hle : probes + remaining ≤ total)
    (htotal : (total : ℝ) ≤ spaceReal) (hprobes : (probes : ℝ) < spaceReal) :
    1 - (total : ℝ) / 2 ^ 128 ≤ (spaceReal - probes - remaining) / (spaceReal - probes) := by
  have hreal : (probes : ℝ) + remaining ≤ total := by exact_mod_cast hle
  have hden : 0 < spaceReal - probes := by linarith
  have hN : spaceReal = 2 ^ 128 := rfl
  rw [← hN, le_div_iff₀ hden]
  have hp : (0 : ℝ) ≤ probes := Nat.cast_nonneg _
  have hN0 := spaceReal_pos
  have : (1 - (total : ℝ) / spaceReal) * (spaceReal - probes) =
      (spaceReal - total) - (spaceReal - total) * probes / spaceReal := by field_simp
  rw [this]
  have : 0 ≤ (spaceReal - total) * probes / spaceReal := div_nonneg (mul_nonneg (by linarith) hp) hN0.le
  linarith

theorem budgetE_le_one {e : ℝ} (he : 0 ≤ e) (probes remaining : ℕ)
    (hbudget : (probes + remaining : ℝ) ≤ spaceReal) : budgetE e probes remaining ≤ 1 := by
  rw [budgetE, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_one (budgetE_base_nonneg hbudget) (budgetE_base_le_one hbudget) he)

theorem budgetE_succ_le {e : ℝ} (he : 0 ≤ e) (probes remaining : ℕ)
    (hbudget : (probes + remaining + 1 : ℝ) ≤ spaceReal) :
    budgetE e probes (remaining + 1) ≤ budgetE e probes remaining := by
  rw [budgetE, budgetE]
  apply ENNReal.ofReal_le_ofReal
  have hcast : ((remaining + 1 : ℕ) : ℝ) = remaining + 1 := by push_cast; ring
  have hlow := budgetE_base_nonneg (probes := probes) (remaining := remaining + 1) (by rw [hcast]; linarith)
  apply Real.rpow_le_rpow hlow _ he
  have hden : 0 ≤ spaceReal - probes := by linarith
  exact div_le_div_of_nonneg_right (by rw [hcast]; linarith) hden

theorem budgetE_le_of_le {e : ℝ} (he : 0 ≤ e) (probes before after : ℕ) (horder : before ≤ after)
    (hbudget : (probes + after : ℝ) ≤ spaceReal) :
    budgetE e probes after ≤ budgetE e probes before := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le horder
  induction extra with
  | zero => rfl
  | succ extra ih =>
      have hcast : ((before + (extra + 1) : ℕ) : ℝ) = (before + extra : ℕ) + 1 := by push_cast; ring
      rw [hcast] at hbudget
      exact (budgetE_succ_le he probes (before + extra) (by linarith)).trans
        (ih (by omega) (by linarith))

/-- The budget decreases in the exponent. -/
theorem budgetE_anti_exp {e e' : ℝ} (he : 0 ≤ e) (hee : e ≤ e') (probes remaining : ℕ)
    (hbudget : (probes + remaining : ℝ) ≤ spaceReal) :
    budgetE e' probes remaining ≤ budgetE e probes remaining := by
  rw [budgetE, budgetE]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge' (budgetE_base_nonneg hbudget)
    (budgetE_base_le_one hbudget) he hee)

/-- One probe step: hazards of total size `e / (N - p)` (as the factor `probeFactor p ^ e`) move one
unit of budget into the probe count. -/
theorem budgetE_probe {e : ℝ} (he : 0 ≤ e) (probes remaining : ℕ)
    (hbudget : (probes + remaining + 1 : ℝ) < spaceReal) :
    budgetE e probes (remaining + 1) = probeFactor probes ^ e * budgetE e (probes + 1) remaining := by
  have hden : 0 < spaceReal - probes - 1 := by linarith [(Nat.cast_nonneg remaining : (0 : ℝ) ≤ remaining)]
  have hden' : 0 < spaceReal - probes := by linarith
  have hfactor : 0 ≤ 1 - 1 / (spaceReal - probes) := by
    rw [sub_nonneg, div_le_one hden']
    linarith
  have hden1 : spaceReal - ((probes : ℝ) + 1) ≠ 0 := by linarith
  have hden0 : spaceReal - (probes : ℝ) ≠ 0 := hden'.ne'
  have hrest : 0 ≤ (spaceReal - ((probes + 1 : ℕ) : ℝ) - remaining) / (spaceReal - ((probes + 1 : ℕ) : ℝ)) :=
    budgetE_base_nonneg (by push_cast; linarith)
  rw [budgetE, budgetE, probeFactor, ENNReal.ofReal_rpow_of_nonneg hfactor he,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hfactor e), ← Real.mul_rpow hfactor hrest]
  congr 2
  push_cast
  field_simp
  ring

/-! ### The digest decrement -/

/-- The digest decrement as a real difference. -/
theorem budgetE_sub_eq (e : ℝ) (probes remaining : ℕ)
    (hbudget : (probes + remaining + 1 : ℝ) ≤ spaceReal) :
    budgetE e probes remaining - budgetE e probes (remaining + 1) =
      ENNReal.ofReal (((spaceReal - probes - remaining) / (spaceReal - probes)) ^ e -
        ((spaceReal - probes - (remaining + 1 : ℕ)) / (spaceReal - probes)) ^ e) := by
  rw [budgetE, budgetE, ENNReal.ofReal_sub]
  exact Real.rpow_nonneg (budgetE_base_nonneg (by push_cast; linarith)) e

/-- **Digest decrement, exponent `e ≥ 1`**: the step `(p, r + 1) → (p, r)` frees at least
`e (1 - x)^(e - 1) / 2^128` with `x = T / 2^128`, for `p + r + 1 ≤ T ≤ N`. -/
theorem budgetE_dec {e : ℝ} (he : 1 ≤ e) (total : ℕ) (htotal : (total : ℝ) ≤ spaceReal)
    (probes remaining : ℕ) (hle : probes + remaining + 1 ≤ total) :
    ENNReal.ofReal (e * (1 - (total : ℝ) / 2 ^ 128) ^ (e - 1) / 2 ^ 128) ≤
      budgetE e probes remaining - budgetE e probes (remaining + 1) := by
  have hreal : (probes : ℝ) + remaining + 1 ≤ total := by exact_mod_cast hle
  have hr : (0 : ℝ) ≤ remaining := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ probes := Nat.cast_nonneg _
  rw [budgetE_sub_eq e probes remaining (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  have hden : 0 < spaceReal - probes := by linarith
  have hN : spaceReal = 2 ^ 128 := rfl
  set u := (spaceReal - probes - (remaining + 1 : ℕ)) / (spaceReal - probes) with hu
  set w := (spaceReal - probes - remaining) / (spaceReal - probes) with hw
  have hu0 : 0 ≤ u := budgetE_base_nonneg (by push_cast; linarith)
  have hwu : w - u = 1 / (spaceReal - probes) := by rw [hu, hw]; push_cast; field_simp; ring
  have huw : u ≤ w := by
    have : 0 < 1 / (spaceReal - probes) := by positivity
    linarith
  have hlow : 1 - (total : ℝ) / 2 ^ 128 ≤ u :=
    budgetE_base_ge (probes := probes) (remaining := remaining + 1) (by omega) htotal (by linarith)
  have hx0 : 0 ≤ 1 - (total : ℝ) / 2 ^ 128 := by
    rw [sub_nonneg, div_le_one (by positivity)]; rw [hN] at htotal; exact htotal
  have hmain := rpow_sub_rpow_ge he hu0 huw
  rw [hwu] at hmain
  refine le_trans ?_ hmain
  have h1 : (1 - (total : ℝ) / 2 ^ 128) ^ (e - 1) ≤ u ^ (e - 1) :=
    Real.rpow_le_rpow hx0 hlow (by linarith)
  have h2 : 1 / (2 : ℝ) ^ 128 ≤ 1 / (spaceReal - probes) :=
    one_div_le_one_div_of_le hden (by rw [← hN]; linarith)
  have h3 : 0 ≤ (1 - (total : ℝ) / 2 ^ 128) ^ (e - 1) := Real.rpow_nonneg hx0 _
  calc e * (1 - (total : ℝ) / 2 ^ 128) ^ (e - 1) / 2 ^ 128
      = e * (1 - (total : ℝ) / 2 ^ 128) ^ (e - 1) * (1 / 2 ^ 128) := by ring
    _ ≤ e * u ^ (e - 1) * (1 / (spaceReal - probes)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left h1 (by linarith)) h2 (by positivity)
      exact mul_nonneg (by linarith) (Real.rpow_nonneg hu0 _)

/-- **Digest decrement at the unarmed exponent `ρ ∈ [1, 2]`**: it frees `β / 2^128` for
`β ≤ ρ / (1 + (ρ - 1) x / (1 - x))`, `x = T / 2^128 < 1`, `p + r + 1 ≤ T`. -/
theorem budgetE_dec_rho {ρ β : ℝ} (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (total : ℕ) (htotal : (total : ℝ) < spaceReal)
    (hβ : β ≤ ρ / (1 + (ρ - 1) * ((total : ℝ) / 2 ^ 128) / (1 - (total : ℝ) / 2 ^ 128)))
    (probes remaining : ℕ) (hle : probes + remaining + 1 ≤ total) :
    ENNReal.ofReal (β / 2 ^ 128) ≤ budgetE ρ probes remaining - budgetE ρ probes (remaining + 1) := by
  refine le_trans ?_ (budgetE_dec hρ1 total htotal.le probes remaining hle)
  apply ENNReal.ofReal_le_ofReal
  have hx1 : (total : ℝ) / 2 ^ 128 < 1 := by rw [div_lt_one (by positivity)]; exact htotal
  have hb := div_bernoulli_le_rpow hρ1 hρ2 (by positivity) hx1
  have : (0 : ℝ) < 2 ^ 128 := by positivity
  exact div_le_div_of_nonneg_right (hβ.trans hb) this.le

/-- **Digest decrement at a natural exponent `n ≥ 1`**: it frees `β / 2^128` for
`β ≤ n (1 - x)^(n - 1)`, `x = T / 2^128`, `p + r + 1 ≤ T ≤ N`. -/
theorem budgetE_dec_nat {β : ℝ} (n : ℕ) (hn : 1 ≤ n) (total : ℕ) (htotal : (total : ℝ) ≤ spaceReal)
    (hβ : β ≤ n * (1 - (total : ℝ) / 2 ^ 128) ^ (n - 1))
    (probes remaining : ℕ) (hle : probes + remaining + 1 ≤ total) :
    ENNReal.ofReal (β / 2 ^ 128) ≤ budgetE n probes remaining - budgetE n probes (remaining + 1) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine le_trans ?_ (budgetE_dec hn' total htotal probes remaining hle)
  apply ENNReal.ofReal_le_ofReal
  have hcast : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by rw [Nat.cast_sub hn]; simp
  rw [hcast, Real.rpow_natCast]
  exact div_le_div_of_nonneg_right hβ (by positivity)

/-! ### Exponent jumps on the budget -/

/-- **An exponent jump on the budget**: raising the exponent from `a` to `b` at `p + r ≤ T < N`
keeps all but a `(b - a) x / (1 - x)` share, `x = T / 2^128`. -/
theorem budgetE_jump {a b : ℝ} (hab : a ≤ b) (total : ℕ) (htotal : (total : ℝ) < spaceReal)
    (probes remaining : ℕ) (hle : probes + remaining ≤ total) :
    budgetE a probes remaining ≤ budgetE b probes remaining +
      ENNReal.ofReal ((b - a) * ((total : ℝ) / 2 ^ 128) / (1 - (total : ℝ) / 2 ^ 128)) *
        budgetE a probes remaining := by
  have hreal : (probes : ℝ) + remaining ≤ total := by exact_mod_cast hle
  have hr : (0 : ℝ) ≤ remaining := Nat.cast_nonneg _
  have hN : spaceReal = 2 ^ 128 := rfl
  have hx1 : (total : ℝ) / 2 ^ 128 < 1 := by rw [div_lt_one (by positivity)]; exact htotal
  have hx0 : (0 : ℝ) ≤ (total : ℝ) / 2 ^ 128 := by positivity
  set x := (total : ℝ) / 2 ^ 128 with hx
  set v := (spaceReal - probes - remaining) / (spaceReal - probes) with hv
  have hlow : 1 - x ≤ v := budgetE_base_ge hle htotal.le (by linarith)
  have hv0 : 0 < v := by linarith
  have hv1 : v ≤ 1 := budgetE_base_le_one (by linarith)
  rw [budgetE, budgetE, ← hv, ← ENNReal.ofReal_mul (div_nonneg (mul_nonneg (by linarith) hx0) (by linarith)),
    ← ENNReal.ofReal_add (Real.rpow_nonneg hv0.le _) (mul_nonneg (div_nonneg (mul_nonneg (by linarith) hx0)
      (by linarith)) (Real.rpow_nonneg hv0.le _))]
  apply ENNReal.ofReal_le_ofReal
  have hj := rpow_sub_rpow_le_jump hv0 hab
  have hq : (1 - v) / v ≤ x / (1 - x) := by
    rw [div_le_div_iff₀ hv0 (by linarith)]
    nlinarith
  have hva : 0 ≤ v ^ a := Real.rpow_nonneg hv0.le _
  have : (b - a) * (1 - v) / v * v ^ a ≤ (b - a) * x / (1 - x) * v ^ a := by
    apply mul_le_mul_of_nonneg_right _ hva
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hq (by linarith)
  linarith

/-- **Arming**: under the `delta` side condition at `x = T / 2^128 ≤ 1/8`, dropping the exponent
from `ρ` to `2` at `p + r ≤ T` loses at most `δ`. -/
theorem budgetE_arm {ρ δ : ℝ} (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (total : ℕ)
    (hx8 : (total : ℝ) / 2 ^ 128 ≤ 1 / 8)
    (hδ : (1 - ρ * ((total : ℝ) / 2 ^ 128) + ρ * (ρ - 1) * ((total : ℝ) / 2 ^ 128) ^ 2 / 2) * (2 - ρ) *
      ((total : ℝ) / 2 ^ 128) / (1 - (total : ℝ) / 2 ^ 128) ≤ δ)
    (probes remaining : ℕ) (hle : probes + remaining ≤ total) :
    budgetE ρ probes remaining ≤ budgetE 2 probes remaining + ENNReal.ofReal δ := by
  have hreal : (probes : ℝ) + remaining ≤ total := by exact_mod_cast hle
  have hN : spaceReal = 2 ^ 128 := rfl
  have hx0 : (0 : ℝ) ≤ (total : ℝ) / 2 ^ 128 := by positivity
  have htotal : (total : ℝ) < spaceReal := by
    rw [hN]; rw [div_le_iff₀ (by positivity)] at hx8; linarith [(by positivity : (0 : ℝ) < 2 ^ 128)]
  set x := (total : ℝ) / 2 ^ 128 with hx
  set v := (spaceReal - probes - remaining) / (spaceReal - probes) with hv
  have hlow : 1 - x ≤ v := budgetE_base_ge hle htotal.le (by linarith)
  have hv0 : 0 < v := by linarith
  have hv1 : v ≤ 1 := budgetE_base_le_one (by linarith)
  have h3 : (1 - x) ^ 2 ≤ 1 - ρ * x + ρ * (ρ - 1) * x ^ 2 / 2 := by
    have : 0 ≤ (2 - ρ) * x * (1 - (ρ + 1) * x / 2) :=
      mul_nonneg (mul_nonneg (by linarith) hx0) (by nlinarith)
    nlinarith
  rw [budgetE, budgetE, ← hv, Real.rpow_two, ← ENNReal.ofReal_add (sq_nonneg _) ?_]
  · apply ENNReal.ofReal_le_ofReal
    have h1 := rpow_sub_sq_le hv0 hρ1 hρ2
    have h2 : v * (1 - v) ≤ x * (1 - x) := by nlinarith
    have h4 : (2 - ρ) * x * (1 - x) ≤
        (1 - ρ * x + ρ * (ρ - 1) * x ^ 2 / 2) * (2 - ρ) * x / (1 - x) := by
      rw [le_div_iff₀ (by linarith)]
      have : 0 ≤ (2 - ρ) * x := mul_nonneg (by linarith) hx0
      nlinarith
    nlinarith
  · exact hδ.trans' (div_nonneg (mul_nonneg (mul_nonneg (by nlinarith [sq_nonneg (1 - x)]) (by linarith)) hx0)
      (by linarith))

/-- **Arming**, subtraction form. -/
theorem budgetE_arm_sub {ρ δ : ℝ} (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (total : ℕ)
    (hx8 : (total : ℝ) / 2 ^ 128 ≤ 1 / 8)
    (hδ : (1 - ρ * ((total : ℝ) / 2 ^ 128) + ρ * (ρ - 1) * ((total : ℝ) / 2 ^ 128) ^ 2 / 2) * (2 - ρ) *
      ((total : ℝ) / 2 ^ 128) / (1 - (total : ℝ) / 2 ^ 128) ≤ δ)
    (probes remaining : ℕ) (hle : probes + remaining ≤ total) :
    budgetE ρ probes remaining - budgetE 2 probes remaining ≤ ENNReal.ofReal δ := by
  rw [tsub_le_iff_left]
  exact budgetE_arm hρ1 hρ2 total hx8 hδ probes remaining hle

/-- The start of the route: `1 - budgetE ρ 0 q ≤ satUp ρ (q / 2^128)`. -/
theorem one_sub_budgetE_start_le {ρ : ℝ} (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (q : ℕ) (hq : (q : ℝ) ≤ spaceReal) :
    1 - budgetE ρ 0 q ≤ ENNReal.ofReal (satUp ρ ((q : ℝ) / 2 ^ 128)) := by
  have hN : spaceReal = 2 ^ 128 := rfl
  have hbase : (spaceReal - ((0 : ℕ) : ℝ) - q) / (spaceReal - ((0 : ℕ) : ℝ)) = 1 - (q : ℝ) / 2 ^ 128 := by
    rw [hN]; field_simp; ring
  have hx1 : (q : ℝ) / 2 ^ 128 ≤ 1 := by rw [div_le_one (by positivity)]; exact hq
  have hx0 : (0 : ℝ) ≤ (q : ℝ) / 2 ^ 128 := by positivity
  rw [budgetE, hbase, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (Real.rpow_nonneg (by linarith) _)]
  exact ENNReal.ofReal_le_ofReal (one_sub_rpow_le_satUp hρ1 hρ2 hx0 hx1)

end FORS.Security.HiddenDebt
