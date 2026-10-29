import FORS.SWRoute.NumericFacts

/-! **The per-class budget steps of the SW route** (requests R1-R7 of the core S-part).
Each step compares the budget before a query, `budgetE e p (r + 1) = ((1 - h) v)^e`, with the
expected budget after it, `budgetE e' (p + 1) r = v^e'`, where `h = 1 / (N - p)` is the probe hazard
and `v = (N - p - 1 - r) / (N - p - 1)`. The real forms come first (abstract in `h, ν, v`), then the
budget forms under `SWNumeric` at `x = T / 2^128` with `p + r + 1 ≤ T`. The margins use the exact
facts `ν ≤ h ≤ x` and `(1 - v) / v ≤ (T - p - 1) / (N - T)`. -/

open ENNReal

namespace FORS.Security.SWRoute

open FORS.Security HiddenDebt

/-! ### Real forms -/

/-- `(1 - h)^e ≤ (1 - h)^2` for `0 ≤ h < 1`, `e ≥ 2`. -/
theorem one_sub_rpow_le_sq {h e : ℝ} (hh0 : 0 ≤ h) (hh1 : h < 1) (he : 2 ≤ e) : (1 - h) ^ e ≤ (1 - h) ^ 2 := by
  rw [← Real.rpow_two]
  exact Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) he

/-- **R1, real form.** -/
theorem swR1_real {ρ hz ν v : ℝ} (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (hz1 : hz ≤ 1) (hν0 : 0 ≤ ν) (hν : ν ≤ hz)
    (hv0 : 0 < v) (hk : 4032 * ν * ((2 - ρ) * (1 - v) / v) ≤ (ρ - 1) * hz * (1 - hz)) :
    (1 - hz) ^ ρ * v ^ ρ + 4032 * ν * v ^ ρ ≤ (1 - ν) * v ^ ρ + 4032 * ν * v ^ (2 : ℝ) := by
  have hvρ : 0 ≤ v ^ ρ := Real.rpow_nonneg hv0.le _
  have hb := one_sub_rpow_le_mul_bernoulli hz1 hρ1 hρ2
  have hj := rpow_sub_rpow_le_jump hv0 hρ2
  have t1 := mul_le_mul_of_nonneg_right hb hvρ
  have t2 := mul_le_mul_of_nonneg_left hj (by positivity : (0 : ℝ) ≤ 4032 * ν)
  have t3 := mul_le_mul_of_nonneg_right hk hvρ
  have t4 : (ν - hz) * v ^ ρ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hvρ
  nlinarith

/-- **R2, real form.** -/
theorem swR2_real {ρ hz ν v x : ℝ} (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (hz0 : 0 ≤ hz) (hz1 : hz ≤ 1) (hν : ν ≤ hz)
    (hx1 : x < 1) (hv : 1 - x ≤ v) (hv1 : v ≤ 1) (heB : 2 - ρ ≤ (1 - x) ^ 65) :
    (1 - hz) ^ ρ * v ^ ρ + (1 - hz) * ν * v ^ ρ ≤ (1 - hz) * v ^ ρ + (1 - hz) * ν * v ^ (66 : ℝ) := by
  have hv0 : 0 < v := by linarith
  have hEB := stepEB_real hz0 hz1 hρ1 hρ2 hx1 hv hv1 heB
  have hmono : v ^ (66 : ℝ) ≤ v ^ ρ := Real.rpow_le_rpow_of_exponent_ge hv0 hv1 (by linarith)
  have t : (1 - hz) * ν * (v ^ ρ - v ^ (66 : ℝ)) ≤ (1 - hz) * hz * (v ^ ρ - v ^ (66 : ℝ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hν (by linarith)) (by linarith)
  nlinarith

/-- **R3, real form.** -/
theorem swR3_real {ρ hz ν v cU : ℝ} (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (hz1 : hz ≤ 1) (hν0 : 0 ≤ ν) (hν : ν ≤ hz)
    (hv0 : 0 < v) (hc : cU ≤ (1 - hz) * v ^ ρ * ((ρ - 1) - (3 - ρ) * (1 - v) / v)) :
    (1 - hz) ^ ρ * v ^ ρ + cU * ν + (1 - hz) * ν * v ^ ρ ≤
      (1 - hz) * v ^ ρ + (1 - hz) * ν * v ^ (3 : ℝ) := by
  have hvρ : 0 ≤ v ^ ρ := Real.rpow_nonneg hv0.le _
  have hb := one_sub_rpow_le_mul_bernoulli hz1 hρ1 hρ2
  have hj := rpow_sub_rpow_le_jump hv0 (show ρ ≤ 3 by linarith)
  have t1 := mul_le_mul_of_nonneg_right hb hvρ
  have t2 := mul_le_mul_of_nonneg_left hj (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - hz) hν0)
  have t3 : 0 ≤ (1 - hz) * v ^ ρ * (ρ - 1) * (hz - ν) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hvρ) (by linarith)) (by linarith)
  have t4 := mul_le_mul_of_nonneg_left hc hν0
  have e : (1 - hz) * ν * ((3 - ρ) * (1 - v) / v * v ^ ρ) =
      (1 - hz) * v ^ ρ * ν * ((3 - ρ) * (1 - v) / v) := by ring
  nlinarith

/-- **R4, real form.** -/
theorem swR4_real {hz ν v cU : ℝ} (hz1 : hz ≤ 1) (hν0 : 0 ≤ ν) (hν : ν ≤ hz)
    (hc : cU ≤ (1 - hz) * v ^ 3) :
    (1 - hz) ^ 2 * v ^ 2 + cU * ν + (1 - hz) * ν * v ^ 2 ≤ (1 - hz) * v ^ 2 + (1 - hz) * ν * v ^ 3 := by
  have h1 : 0 ≤ (1 - hz) * v ^ 2 * (hz - ν) :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg v)) (by linarith)
  have h2 := mul_le_mul_of_nonneg_left hc hν0
  nlinarith

/-- **R5, real form at the exponent `ρ`.** -/
theorem swR5_rho_real {ρ hz ν v : ℝ} (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (hz1 : hz ≤ 1) (hν0 : 0 ≤ ν) (hν : ν ≤ hz)
    (hv0 : 0 ≤ v) (hA : 1 / 2 ≤ (ρ - 1) * v ^ ρ) :
    (1 - hz) ^ ρ * v ^ ρ + (1 - hz) * (ν / 2) ≤ (1 - hz) * v ^ ρ := by
  have hvρ : 0 ≤ v ^ ρ := Real.rpow_nonneg hv0 _
  have hb := one_sub_rpow_le_mul_bernoulli hz1 hρ1 hρ2
  have t1 := mul_le_mul_of_nonneg_right hb hvρ
  have t2 : ν / 2 ≤ (ρ - 1) * hz * v ^ ρ := by
    have : ν * (1 / 2) ≤ ν * ((ρ - 1) * v ^ ρ) := mul_le_mul_of_nonneg_left hA hν0
    have : (ρ - 1) * v ^ ρ * ν ≤ (ρ - 1) * v ^ ρ * hz := mul_le_mul_of_nonneg_left hν (by linarith)
    nlinarith
  have t3 := mul_le_mul_of_nonneg_left t2 (by linarith : (0 : ℝ) ≤ 1 - hz)
  nlinarith

/-- **R5, real form at an exponent `e ≥ 2`** (with `v^e ≥ 1/2`). -/
theorem swR5_two_real {e hz ν v : ℝ} (he : 2 ≤ e) (hz0 : 0 ≤ hz) (hz1 : hz < 1) (hν : ν ≤ hz)
    (hv0 : 0 ≤ v) (hA : 1 / 2 ≤ v ^ e) :
    (1 - hz) ^ e * v ^ e + (1 - hz) * (ν / 2) ≤ (1 - hz) * v ^ e := by
  have hve : 0 ≤ v ^ e := Real.rpow_nonneg hv0 _
  have hs := one_sub_rpow_le_sq hz0 hz1 he
  have t1 := mul_le_mul_of_nonneg_right hs hve
  have t2 : (1 - hz) * (ν / 2) ≤ (1 - hz) * (hz * v ^ e) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith
  nlinarith

/-- **R6, real form.** -/
theorem swR6_real {ρ hz ν v : ℝ} (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (hz1 : hz ≤ 1) (hν0 : 0 ≤ ν) (hν : ν ≤ hz)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hgap : 2 - ρ ≤ (1 - ν) / 2) :
    (1 - hz) ^ ρ * v ^ ρ ≤ (1 - hz) * (1 - ν) * (v ^ ρ + ν / 2) := by
  have hvρ : 0 ≤ v ^ ρ := Real.rpow_nonneg hv0 _
  have hvρ1 : v ^ ρ ≤ 1 := Real.rpow_le_one hv0 hv1 (by linarith)
  have hb := one_sub_rpow_le_mul_bernoulli hz1 hρ1 hρ2
  have t1 := mul_le_mul_of_nonneg_right hb hvρ
  have t2 : (1 - hz) * (1 - (ρ - 1) * hz) * v ^ ρ ≤ (1 - hz) * (1 - (ρ - 1) * ν) * v ^ ρ := by
    apply mul_le_mul_of_nonneg_right _ hvρ
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith
  have t3 : (1 - (ρ - 1) * ν) * v ^ ρ ≤ (1 - ν) * (v ^ ρ + ν / 2) := by
    have : ν * (2 - ρ) * v ^ ρ ≤ ν * ((1 - ν) / 2) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hgap hν0) hvρ1 hvρ (mul_nonneg hν0 (by linarith))
    nlinarith
  have t4 := mul_le_mul_of_nonneg_left t3 (by linarith : (0 : ℝ) ≤ 1 - hz)
  nlinarith

/-! ### The probe hazard and the base after a probe -/

variable [Params]

/-- The probe hazard `h = 1 / (N - p)`. -/
noncomputable def swHz (p : ℕ) : ℝ := 1 / (spaceReal - p)

/-- The base after a probe, `v = (N - (p + 1) - r) / (N - (p + 1))`. -/
noncomputable def swV (p r : ℕ) : ℝ := (spaceReal - ((p + 1 : ℕ) : ℝ) - r) / (spaceReal - ((p + 1 : ℕ) : ℝ))

theorem probeFactor_eq_swHz (p : ℕ) : probeFactor p = ENNReal.ofReal (1 - swHz p) := rfl

theorem budgetE_succ_eq_swV (e : ℝ) (p r : ℕ) : budgetE e (p + 1) r = ENNReal.ofReal (swV p r ^ e) := rfl

theorem sw_spaceReal : spaceReal = 2 ^ 128 := rfl

section Facts

variable {ρ β δ cU : ℝ} {T : ℕ} (h : SWNumeric ρ β δ ((T : ℝ) / 2 ^ 128) cU) {p r : ℕ} (hle : p + r + 1 ≤ T)
include h hle

theorem sw_T_le : (T : ℝ) ≤ 2 ^ 128 / 8 := by
  have h8 := h.x8
  rw [div_le_iff₀ (by positivity)] at h8
  linarith

theorem sw_one_le_T : (1 : ℝ) ≤ T := by
  have : 1 ≤ T := by omega
  exact_mod_cast this

theorem sw_hreal : (p : ℝ) + r + 1 ≤ T := by exact_mod_cast hle

theorem sw_lt : (p + r + 1 : ℝ) < spaceReal := by
  have := sw_T_le h hle; have := sw_hreal h hle
  rw [sw_spaceReal]; linarith [(by positivity : (0 : ℝ) < 2 ^ 128)]

theorem swHz_pos : 0 < swHz p := by
  have := sw_lt h hle
  unfold swHz
  have : 0 < spaceReal - p := by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  positivity

theorem nu_le_swHz : 1 / (2 : ℝ) ^ 128 ≤ swHz p := by
  have := sw_lt h hle
  unfold swHz
  have : 0 < spaceReal - p := by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  exact one_div_le_one_div_of_le this (by rw [← sw_spaceReal]; linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)])

theorem swHz_le_x : swHz p ≤ (T : ℝ) / 2 ^ 128 := by
  have hT := sw_hreal h hle
  have hlt := sw_lt h hle
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  unfold swHz
  have hden : 0 < spaceReal - p := by linarith
  rw [← sw_spaceReal, div_le_div_iff₀ hden spaceReal_pos]
  have : 0 ≤ (p : ℝ) * (spaceReal - p - 1) := mul_nonneg hp (by linarith)
  nlinarith

theorem swHz_lt_one : swHz p < 1 := by
  have := swHz_le_x h hle; have := h.x8; linarith

theorem nu_le_x : 1 / (2 : ℝ) ^ 128 ≤ (T : ℝ) / 2 ^ 128 :=
  div_le_div_of_nonneg_right (sw_one_le_T h hle) (by positivity)

theorem swV_ge : 1 - (T : ℝ) / 2 ^ 128 ≤ swV p r := by
  have hlt := sw_lt h hle
  exact budgetE_base_ge (probes := p + 1) (remaining := r) (by omega)
    (by rw [sw_spaceReal]; linarith [sw_T_le h hle])
    (by push_cast; linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])

theorem swV_le_one : swV p r ≤ 1 :=
  budgetE_base_le_one (by push_cast; linarith [sw_lt h hle])

theorem swV_pos : 0 < swV p r := by
  have := swV_ge h hle; have := h.x8; linarith

theorem swV_seven_eighths : 7 / 8 ≤ swV p r := by
  have := swV_ge h hle; have := h.x8; linarith

/-- `(1 - v) / v ≤ x / (1 - x)`. -/
theorem swV_ratio_le : (1 - swV p r) / swV p r ≤ (T : ℝ) / 2 ^ 128 / (1 - (T : ℝ) / 2 ^ 128) := by
  have hv := swV_ge h hle; have hv0 := swV_pos h hle; have h8 := h.x8; have hx0 := h.x0
  rw [div_le_div_iff₀ hv0 (by linarith)]
  nlinarith

/-- **The exact marker margin** behind R1: `4032 ν (2 - ρ) (1 - v) / v ≤ (ρ - 1) h (1 - h)`. -/
theorem sw_jump_exact :
    4032 * (1 / 2 ^ 128) * ((2 - ρ) * (1 - swV p r) / swV p r) ≤ (ρ - 1) * swHz p * (1 - swHz p) := by
  have hT := sw_hreal h hle
  have hT1 := sw_one_le_T h hle
  have hTN := sw_T_le h hle
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hρ1 := h.one_le_rho; have hρ2 := h.high
  set N : ℝ := spaceReal with hN
  have hN' : N = 2 ^ 128 := rfl
  have hNpos : 0 < N := spaceReal_pos
  have hNT : 0 < N - T := by rw [hN']; linarith
  -- (1 - v) / v = r / (N - p - 1 - r)
  have hratio : (1 - swV p r) / swV p r = r / (N - p - 1 - r) := by
    unfold swV
    rw [← hN]
    push_cast
    have h1 : N - (p + 1) ≠ 0 := by linarith
    have h2 : N - (p + 1) - r ≠ 0 := by linarith
    have h3 : N - p - 1 - r ≠ 0 := by linarith
    field_simp
    ring
  -- e1 at x = T / N: 4032 (2 - ρ) T ≤ (ρ - 1) (N - T)
  have he1 : 4032 * (2 - ρ) * T ≤ (ρ - 1) * (N - T) := by
    have e := h.e1
    rw [← hN'] at e
    have : 4032 * (2 - ρ) * ((T : ℝ) / N) / (1 - (T : ℝ) / N) = 4032 * (2 - ρ) * T / (N - T) := by
      field_simp
    rw [this, div_le_iff₀ hNT] at e
    exact e
  have s1 : r / (N - p - 1 - r) ≤ (T - p - 1) / (N - T) :=
    div_le_div₀ (by linarith) (by linarith) hNT (by linarith)
  have s2 : 4032 * (2 - ρ) * ((T - p - 1) / (N - T)) ≤ (ρ - 1) * ((T - p - 1) / T) := by
    rw [mul_div_assoc', mul_div_assoc', div_le_div_iff₀ hNT (by linarith)]
    have : 0 ≤ T - p - 1 := by linarith
    nlinarith
  have s3 : (T - p - 1) / T ≤ (N - p - 1) / (N - p) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have : 0 ≤ (p : ℝ) * (N - p - 1) := mul_nonneg hp (by linarith)
    nlinarith
  have hz : swHz p = 1 / (N - p) := rfl
  have s4 : (N - p - 1) / (N - p) * (1 / N) ≤ swHz p * (1 - swHz p) := by
    rw [hz]
    have hNp : 0 < N - p := by linarith
    have : 1 - 1 / (N - p) = (N - p - 1) / (N - p) := by field_simp
    rw [this, div_mul_div_comm, div_mul_div_comm, one_mul, mul_one]
    exact div_le_div_of_nonneg_left (by linarith) (mul_pos hNp hNp) (by nlinarith)
  rw [mul_div_assoc, hratio, ← hN']
  have hA : 0 ≤ 2 - ρ := by linarith
  calc 4032 * (1 / N) * ((2 - ρ) * (r / (N - p - 1 - r)))
      = (1 / N) * (4032 * (2 - ρ) * (r / (N - p - 1 - r))) := by ring
    _ ≤ (1 / N) * (4032 * (2 - ρ) * ((T - p - 1) / (N - T))) := by
      refine mul_le_mul_of_nonneg_left ?_ (one_div_pos.mpr hNpos).le
      exact mul_le_mul_of_nonneg_left s1 (by linarith)
    _ ≤ (1 / N) * ((ρ - 1) * ((N - p - 1) / (N - p))) := by
      refine mul_le_mul_of_nonneg_left ?_ (one_div_pos.mpr hNpos).le
      exact s2.trans (mul_le_mul_of_nonneg_left s3 (by linarith))
    _ = (ρ - 1) * ((N - p - 1) / (N - p) * (1 / N)) := by ring
    _ ≤ (ρ - 1) * (swHz p * (1 - swHz p)) := mul_le_mul_of_nonneg_left s4 (by linarith)
    _ = (ρ - 1) * swHz p * (1 - swHz p) := by ring

/-- The probe step in real form: `budgetE e p (r + 1) = ofReal ((1 - h)^e v^e)`. -/
theorem budgetE_probe_sw {e : ℝ} (he : 0 ≤ e) :
    budgetE e p (r + 1) = ENNReal.ofReal ((1 - swHz p) ^ e * swV p r ^ e) := by
  have hg : 0 ≤ 1 - swHz p := by linarith [swHz_lt_one h hle]
  rw [budgetE_probe he p r (sw_lt h hle), probeFactor_eq_swHz, budgetE_succ_eq_swV,
    ENNReal.ofReal_rpow_of_nonneg hg he, ← ENNReal.ofReal_mul (Real.rpow_nonneg hg e)]

/-- The cover coefficient is small: `cU ≤ (1 - x)^2 (1 - 2x)` (from `e3` with `ρ ≤ 2`). -/
theorem cU_le_e3 : cU ≤ (1 - (T : ℝ) / 2 ^ 128) ^ 2 * (1 - 2 * ((T : ℝ) / 2 ^ 128)) := by
  have e := h.e3
  have hy := h.one_sub_x_pos; have hx0 := h.x0; have hρ2 := h.high
  set x := (T : ℝ) / 2 ^ 128
  have hy3 : 0 < (1 - x) ^ 3 := by positivity
  have h1 : cU / (1 - x) ^ 3 ≤ (ρ - 1) - (3 - ρ) * x / (1 - x) := by linarith
  have h2 : (3 - ρ) * x / (1 - x) ≥ x / (1 - x) := by
    rw [ge_iff_le, div_le_div_iff_of_pos_right hy]; nlinarith
  rw [div_le_iff₀ hy3] at h1
  have h3 : ((ρ - 1) - (3 - ρ) * x / (1 - x)) * (1 - x) ^ 3 ≤ (1 - x / (1 - x)) * (1 - x) ^ 3 :=
    mul_le_mul_of_nonneg_right (by linarith) hy3.le
  have h4 : (1 - x / (1 - x)) * (1 - x) ^ 3 = (1 - x) ^ 2 * (1 - 2 * x) := by
    field_simp; ring
  linarith

end Facts

/-! ### The requested budget steps -/

section Requests

variable {ρ β δ cU : ℝ} {T : ℕ}

/-- **R1** (an encoding, unarmed: first-order factor `1 - ν`, markers `≤ 4032 ν` jump `ρ → 2`). -/
theorem swR1 (h : SWNumeric ρ β δ ((T : ℝ) / 2 ^ 128) cU) (p r : ℕ) (hle : p + r + 1 ≤ T) :
    budgetE ρ p (r + 1) + ENNReal.ofReal (4032 / 2 ^ 128) * budgetE ρ (p + 1) r ≤
      ENNReal.ofReal (1 - 1 / 2 ^ 128) * budgetE ρ (p + 1) r +
        ENNReal.ofReal (4032 / 2 ^ 128) * budgetE 2 (p + 1) r := by
  have hρ1 := h.one_le_rho; have hρ2 := h.high
  have hv0 := swV_pos h hle
  have key := swR1_real hρ1 hρ2 (swHz_lt_one h hle).le (by positivity) (nu_le_swHz h hle) hv0
    (sw_jump_exact h hle)
  rw [budgetE_probe_sw h hle (by linarith), budgetE_succ_eq_swV, budgetE_succ_eq_swV,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (mul_nonneg (Real.rpow_nonneg (by linarith [swHz_lt_one h hle]) _)
      (Real.rpow_nonneg hv0.le _)) (mul_nonneg (by positivity) (Real.rpow_nonneg hv0.le _)),
    ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (Real.rpow_nonneg hv0.le _))
      (mul_nonneg (by positivity) (Real.rpow_nonneg hv0.le _))]
  apply ENNReal.ofReal_le_ofReal
  have e1 : (4032 : ℝ) / 2 ^ 128 = 4032 * (1 / 2 ^ 128) := by ring
  rw [e1]
  linarith

/-- **R2** (a chain step one below the word, unarmed: a guess, a contact `ν` jumping `ρ → 66`). -/
theorem swR2 (h : SWNumeric ρ β δ ((T : ℝ) / 2 ^ 128) cU) (p r : ℕ) (hle : p + r + 1 ≤ T) :
    budgetE ρ p (r + 1) + probeFactor p * ENNReal.ofReal (1 / 2 ^ 128) * budgetE ρ (p + 1) r ≤
      probeFactor p * budgetE ρ (p + 1) r +
        probeFactor p * ENNReal.ofReal (1 / 2 ^ 128) * budgetE 66 (p + 1) r := by
  have hρ1 := h.one_le_rho; have hρ2 := h.high
  have hv0 := swV_pos h hle
  have hg : 0 ≤ 1 - swHz p := by linarith [swHz_lt_one h hle]
  have key := swR2_real hρ1 hρ2 (swHz_pos h hle).le (swHz_lt_one h hle).le (nu_le_swHz h hle) h.x_lt_one
    (swV_ge h hle) (swV_le_one h hle) h.eB
  rw [budgetE_probe_sw h hle (by linarith), budgetE_succ_eq_swV, budgetE_succ_eq_swV, probeFactor_eq_swHz,
    ← ENNReal.ofReal_mul hg, ← ENNReal.ofReal_mul (mul_nonneg hg (by positivity)),
    ← ENNReal.ofReal_mul hg, ← ENNReal.ofReal_mul (mul_nonneg hg (by positivity)),
    ← ENNReal.ofReal_add (mul_nonneg (Real.rpow_nonneg hg _) (Real.rpow_nonneg hv0.le _))
      (mul_nonneg (mul_nonneg hg (by positivity)) (Real.rpow_nonneg hv0.le _)),
    ← ENNReal.ofReal_add (mul_nonneg hg (Real.rpow_nonneg hv0.le _))
      (mul_nonneg (mul_nonneg hg (by positivity)) (Real.rpow_nonneg hv0.le _))]
  exact ENNReal.ofReal_le_ofReal key

/-- **R3** (a FORS leaf query, unarmed: a guess, a contact `ν` jumping `ρ → 3`, the payment `cU`). -/
theorem swR3 (h : SWNumeric ρ β δ ((T : ℝ) / 2 ^ 128) cU) (p r : ℕ) (hle : p + r + 1 ≤ T) :
    budgetE ρ p (r + 1) + ENNReal.ofReal (cU / 2 ^ 128) +
        probeFactor p * ENNReal.ofReal (1 / 2 ^ 128) * budgetE ρ (p + 1) r ≤
      probeFactor p * budgetE ρ (p + 1) r +
        probeFactor p * ENNReal.ofReal (1 / 2 ^ 128) * budgetE 3 (p + 1) r := by
  have hρ1 := h.one_le_rho; have hρ2 := h.high
  have hv0 := swV_pos h hle
  have hv := swV_ge h hle
  have hzx := swHz_le_x h hle
  have hg : 0 ≤ 1 - swHz p := by linarith [swHz_lt_one h hle]
  have hy := h.one_sub_x_pos; have hx0 := h.x0
  have hq := swV_ratio_le h hle
  set x := (T : ℝ) / 2 ^ 128 with hx
  set v := swV p r
  set hz := swHz p
  -- the contact condition at `v` from `e3` at `x`
  have hc : cU ≤ (1 - hz) * v ^ ρ * ((ρ - 1) - (3 - ρ) * (1 - v) / v) := by
    have e := h.e3
    have hy3 : 0 < (1 - x) ^ 3 := by positivity
    have hBx : cU / (1 - x) ^ 3 ≤ (ρ - 1) - (3 - ρ) * x / (1 - x) := by linarith
    have hB0 : 0 ≤ (ρ - 1) - (3 - ρ) * x / (1 - x) := le_trans (div_nonneg h.cU0 hy3.le) hBx
    have hBv : (ρ - 1) - (3 - ρ) * x / (1 - x) ≤ (ρ - 1) - (3 - ρ) * (1 - v) / v := by
      rw [mul_div_assoc, mul_div_assoc]
      have := mul_le_mul_of_nonneg_left hq (by linarith : (0 : ℝ) ≤ 3 - ρ)
      linarith
    have hpow : (1 - x) ^ 3 ≤ (1 - hz) * v ^ ρ := by
      have h1 : (1 - x) ^ (2 : ℝ) ≤ (1 - x) ^ ρ :=
        Real.rpow_le_rpow_of_exponent_ge hy (by linarith) hρ2
      have h2 : (1 - x) ^ ρ ≤ v ^ ρ := Real.rpow_le_rpow hy.le hv (by linarith)
      rw [Real.rpow_two] at h1
      have h3 : 1 - x ≤ 1 - hz := by linarith
      calc (1 - x) ^ 3 = (1 - x) * (1 - x) ^ 2 := by ring
        _ ≤ (1 - hz) * v ^ ρ := mul_le_mul h3 (h1.trans h2) (sq_nonneg _) hg
    rw [div_le_iff₀ hy3] at hBx
    calc cU ≤ ((ρ - 1) - (3 - ρ) * x / (1 - x)) * (1 - x) ^ 3 := hBx
      _ ≤ ((ρ - 1) - (3 - ρ) * (1 - v) / v) * ((1 - hz) * v ^ ρ) := mul_le_mul hBv hpow hy3.le (hB0.trans hBv)
      _ = _ := by ring
  have key := swR3_real hρ1 hρ2 (swHz_lt_one h hle).le (by positivity) (nu_le_swHz h hle) hv0 hc
  have hcU0 := h.cU0
  rw [budgetE_probe_sw h hle (by linarith), budgetE_succ_eq_swV, budgetE_succ_eq_swV, probeFactor_eq_swHz,
    ← ENNReal.ofReal_mul hg, ← ENNReal.ofReal_mul (mul_nonneg hg (by positivity)),
    ← ENNReal.ofReal_mul hg, ← ENNReal.ofReal_mul (mul_nonneg hg (by positivity)),
    ← ENNReal.ofReal_add (mul_nonneg (Real.rpow_nonneg hg _) (Real.rpow_nonneg hv0.le _)) (by positivity),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg (Real.rpow_nonneg hg _) (Real.rpow_nonneg hv0.le _))
      (by positivity)) (mul_nonneg (mul_nonneg hg (by positivity)) (Real.rpow_nonneg hv0.le _)),
    ← ENNReal.ofReal_add (mul_nonneg hg (Real.rpow_nonneg hv0.le _))
      (mul_nonneg (mul_nonneg hg (by positivity)) (Real.rpow_nonneg hv0.le _))]
  apply ENNReal.ofReal_le_ofReal
  have e1 : cU / 2 ^ 128 = cU * (1 / 2 ^ 128) := by ring
  rw [e1]
  linarith

/-- **R4** (a FORS leaf query, armed at `2`: a guess, a contact jumping `2 → 3`, the payment `cU`). -/
theorem swR4 (h : SWNumeric ρ β δ ((T : ℝ) / 2 ^ 128) cU) (p r : ℕ) (hle : p + r + 1 ≤ T) :
    budgetE 2 p (r + 1) + ENNReal.ofReal (cU / 2 ^ 128) +
        probeFactor p * ENNReal.ofReal (1 / 2 ^ 128) * budgetE 2 (p + 1) r ≤
      probeFactor p * budgetE 2 (p + 1) r +
        probeFactor p * ENNReal.ofReal (1 / 2 ^ 128) * budgetE 3 (p + 1) r := by
  have hv0 := swV_pos h hle
  have hv := swV_ge h hle
  have hzx := swHz_le_x h hle
  have hg : 0 ≤ 1 - swHz p := by linarith [swHz_lt_one h hle]
  have hy := h.one_sub_x_pos; have hx0 := h.x0
  have hcU := cU_le_e3 h hle
  have hcU0 := h.cU0
  have ν0 : (0 : ℝ) ≤ 1 / 2 ^ 128 := by positivity
  have hc : cU ≤ (1 - swHz p) * swV p r ^ 3 := by
    clear h
    generalize swV p r = v at *
    generalize swHz p = hz at *
    generalize (T : ℝ) / 2 ^ 128 = x at *
    have h1 : (1 - x) ^ 2 * (1 - 2 * x) ≤ (1 - x) ^ 4 := by
      have : 1 - 2 * x ≤ (1 - x) ^ 2 := by nlinarith
      calc (1 - x) ^ 2 * (1 - 2 * x) ≤ (1 - x) ^ 2 * (1 - x) ^ 2 :=
            mul_le_mul_of_nonneg_left this (sq_nonneg _)
        _ = (1 - x) ^ 4 := by ring
    have h2 : (1 - x) ^ 3 ≤ v ^ 3 := pow_le_pow_left₀ hy.le hv 3
    have h3 : (1 - x) ^ 4 ≤ (1 - hz) * v ^ 3 := by
      calc (1 - x) ^ 4 = (1 - x) * (1 - x) ^ 3 := by ring
        _ ≤ (1 - hz) * v ^ 3 := mul_le_mul (by linarith) h2 (pow_nonneg hy.le 3) hg
    linarith
  have key := swR4_real (swHz_lt_one h hle).le ν0 (nu_le_swHz h hle) hc
  have hv2 : 0 ≤ swV p r ^ 2 := sq_nonneg _
  have hv3 : 0 ≤ swV p r ^ 3 := pow_nonneg hv0.le 3
  have hX : 0 ≤ (1 - swHz p) ^ 2 * swV p r ^ 2 := mul_nonneg (sq_nonneg _) hv2
  have hY : 0 ≤ cU / 2 ^ 128 := div_nonneg hcU0 (by positivity)
  have hZ : 0 ≤ (1 - swHz p) * (1 / 2 ^ 128) * swV p r ^ 2 := mul_nonneg (mul_nonneg hg ν0) hv2
  have hW : 0 ≤ (1 - swHz p) * swV p r ^ 2 := mul_nonneg hg hv2
  have hU : 0 ≤ (1 - swHz p) * (1 / 2 ^ 128) * swV p r ^ 3 := mul_nonneg (mul_nonneg hg ν0) hv3
  have h3 : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
  rw [budgetE_probe_sw h hle (e := 2) (by norm_num), budgetE_succ_eq_swV, budgetE_succ_eq_swV,
    probeFactor_eq_swHz]
  simp only [Real.rpow_two]
  rw [h3, Real.rpow_natCast]
  simp only [← ENNReal.ofReal_mul hg, ← ENNReal.ofReal_mul (mul_nonneg hg ν0)]
  rw [← ENNReal.ofReal_add hX hY, ← ENNReal.ofReal_add (add_nonneg hX hY) hZ, ← ENNReal.ofReal_add hW hU]
  apply ENNReal.ofReal_le_ofReal
  linarith

/-- **R5** (a chain step two below the word: a guess, half a unit of pending credit), at `e = ρ`
(using `eA`), `e = 2` and `e = 3`. -/
theorem swR5 (h : SWNumeric ρ β δ ((T : ℝ) / 2 ^ 128) cU) (p r : ℕ) (hle : p + r + 1 ≤ T)
    (e : ℝ) (he : e = ρ ∨ e = 2 ∨ e = 3) :
    budgetE e p (r + 1) + probeFactor p * ENNReal.ofReal (1 / 2 ^ 129) ≤ probeFactor p * budgetE e (p + 1) r := by
  have hρ1 := h.one_le_rho; have hρ2 := h.high
  have hv0 := swV_pos h hle
  have hg : 0 ≤ 1 - swHz p := by linarith [swHz_lt_one h hle]
  have he0 : 0 ≤ e := by rcases he with rfl | rfl | rfl <;> linarith
  have key : (1 - swHz p) ^ e * swV p r ^ e + (1 - swHz p) * ((1 / 2 ^ 128) / 2) ≤
      (1 - swHz p) * swV p r ^ e := by
    rcases he with rfl | he
    · exact swR5_rho_real hρ1 hρ2 (swHz_lt_one h hle).le (by positivity) (nu_le_swHz h hle) hv0.le
        (stepEA_real hρ1 h.x_lt_one.le (swV_ge h hle) h.eA)
    · have he2 : 2 ≤ e := by rcases he with rfl | rfl <;> norm_num
      have he3 : e ≤ 3 := by rcases he with rfl | rfl <;> norm_num
      have hA : 1 / 2 ≤ swV p r ^ e := by
        have h78 := swV_seven_eighths h hle
        have h1 : swV p r ^ (3 : ℝ) ≤ swV p r ^ e :=
          Real.rpow_le_rpow_of_exponent_ge hv0 (swV_le_one h hle) he3
        have h3 : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
        rw [h3, Real.rpow_natCast] at h1
        have h2 : (7 / 8 : ℝ) ^ 3 ≤ swV p r ^ 3 := pow_le_pow_left₀ (by norm_num) h78 3
        norm_num at h2
        linarith
      exact swR5_two_real he2 (swHz_pos h hle).le (swHz_lt_one h hle) (nu_le_swHz h hle) hv0.le hA
  rw [budgetE_probe_sw h hle he0, budgetE_succ_eq_swV, probeFactor_eq_swHz,
    ← ENNReal.ofReal_mul hg, ← ENNReal.ofReal_mul hg,
    ← ENNReal.ofReal_add (mul_nonneg (Real.rpow_nonneg hg _) (Real.rpow_nonneg hv0.le _))
      (mul_nonneg hg (by positivity))]
  apply ENNReal.ofReal_le_ofReal
  have e1 : (1 : ℝ) / 2 ^ 129 = (1 / 2 ^ 128) / 2 := by norm_num
  rw [e1]
  exact key

/-- **R6** (a chain step one below the word, unarmed, whose payload is an A answer: a guess, a
contact that kills, half a unit of credit released). -/
theorem swR6 (h : SWNumeric ρ β δ ((T : ℝ) / 2 ^ 128) cU) (p r : ℕ) (hle : p + r + 1 ≤ T) :
    budgetE ρ p (r + 1) ≤
      probeFactor p * ENNReal.ofReal (1 - 1 / 2 ^ 128) * (budgetE ρ (p + 1) r + ENNReal.ofReal (1 / 2 ^ 129)) := by
  have hρ1 := h.one_le_rho; have hρ2 := h.high
  have hv0 := swV_pos h hle
  have hg : 0 ≤ 1 - swHz p := by linarith [swHz_lt_one h hle]
  have hνx := nu_le_x h hle
  have hgap : 2 - ρ ≤ (1 - 1 / 2 ^ 128) / 2 := by
    have eA := h.eA
    have h8 := h.x8; have hx0 := h.x0
    set x := (T : ℝ) / 2 ^ 128
    have hy : 0 < 1 - ρ * x := by nlinarith
    have h1 : (2 - ρ) * (2 * (1 - ρ * x)) ≤ (1 - ρ * x) ^ 2 := by nlinarith [sq_nonneg (ρ * x)]
    have h2 : 2 - ρ ≤ (1 - ρ * x) / 2 := by
      rw [le_div_iff₀ (by norm_num)]
      nlinarith
    have h3 : 1 / (2 : ℝ) ^ 128 ≤ ρ * x := by nlinarith
    linarith
  have key := swR6_real hρ1 hρ2 (swHz_lt_one h hle).le (by positivity) (nu_le_swHz h hle) hv0.le
    (swV_le_one h hle) hgap
  rw [budgetE_probe_sw h hle (by linarith), budgetE_succ_eq_swV, probeFactor_eq_swHz,
    ← ENNReal.ofReal_mul hg, ← ENNReal.ofReal_add (Real.rpow_nonneg hv0.le _) (by positivity),
    ← ENNReal.ofReal_mul (mul_nonneg hg (by norm_num))]
  apply ENNReal.ofReal_le_ofReal
  have e1 : (1 : ℝ) / 2 ^ 129 = (1 / 2 ^ 128) / 2 := by norm_num
  rw [e1]
  exact key

/-- **R7** (a cached FORS leaf query pays `cU` from the digest decrement), at `e = ρ` and `e = 2`. -/
theorem swR7 (h : SWNumeric ρ β δ ((T : ℝ) / 2 ^ 128) cU) (p r : ℕ) (hle : p + r + 1 ≤ T)
    (e : ℝ) (he : e = ρ ∨ e = 2) :
    ENNReal.ofReal (cU / 2 ^ 128) ≤ budgetE e p r - budgetE e p (r + 1) := by
  have hρ1 := h.one_le_rho; have hρ2 := h.high
  have he1 : 1 ≤ e := by rcases he with rfl | rfl <;> linarith
  have he2 : e ≤ 2 := by rcases he with rfl | rfl <;> linarith
  refine le_trans ?_ (budgetE_dec he1 T (h.total_lt_space).le p r hle)
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hcU := cU_le_e3 h hle
  have hy := h.one_sub_x_pos; have hx0 := h.x0
  set x := (T : ℝ) / 2 ^ 128
  have h1 : (1 - x) ^ 2 * (1 - 2 * x) ≤ 1 - x := by
    have : (1 - x) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have h2 : (1 - x) ^ (1 : ℝ) ≤ (1 - x) ^ (e - 1) :=
    Real.rpow_le_rpow_of_exponent_ge hy (by linarith) (by linarith)
  rw [Real.rpow_one] at h2
  have h3 : 0 ≤ (1 - x) ^ (e - 1) := Real.rpow_nonneg hy.le _
  nlinarith

end Requests

end FORS.Security.SWRoute
