import FORS.SWRoute.Interface

/-! **Real facts about the SW route's side conditions.** `SWNumeric` is monotone in `x` (each condition
gets easier as `x` shrinks), its simple consequences, and the budget steps it pays for: the digest
decrement at the exponents `ρ, 2, 3, 66, 67` and the arming loss `δ`. -/

open ENNReal

namespace FORS.Security.SWRoute

open FORS.Security HiddenDebt

/-! ### Simple consequences -/

namespace SWNumeric

variable {ρ β δ x cU : ℝ}

theorem one_le_rho (h : SWNumeric ρ β δ x cU) : 1 ≤ ρ := by linarith [h.low]

theorem rho_pos (h : SWNumeric ρ β δ x cU) : 0 < ρ := by linarith [h.low]

theorem x_lt_one (h : SWNumeric ρ β δ x cU) : x < 1 := by linarith [h.x8]

theorem one_sub_x_pos (h : SWNumeric ρ β δ x cU) : 0 < 1 - x := by linarith [h.x8]

theorem seven_eighths_le (h : SWNumeric ρ β δ x cU) : 7 / 8 ≤ 1 - x := by linarith [h.x8]

theorem one_sub_x_le_one (h : SWNumeric ρ β δ x cU) : 1 - x ≤ 1 := by linarith [h.x0]

/-- The second-order factor of the `delta` condition is at least `(1 - x)^2`, hence positive. -/
theorem sq_le_deltaFactor (h : SWNumeric ρ β δ x cU) :
    (1 - x) ^ 2 ≤ 1 - ρ * x + ρ * (ρ - 1) * x ^ 2 / 2 := by
  have h1 := h.x0; have h2 := h.x8; have h3 := h.low; have h4 := h.high
  have : 0 ≤ (2 - ρ) * x * (1 - (ρ + 1) * x / 2) :=
    mul_nonneg (mul_nonneg (by linarith) h1) (by nlinarith)
  nlinarith

theorem delta_nonneg (h : SWNumeric ρ β δ x cU) : 0 ≤ δ := by
  have hf := h.sq_le_deltaFactor
  have hx := h.one_sub_x_pos
  refine le_trans ?_ h.delta
  apply div_nonneg _ hx.le
  exact mul_nonneg (mul_nonneg (le_trans (sq_nonneg _) hf) (by linarith [h.high])) h.x0

theorem beta_le_two (h : SWNumeric ρ β δ x cU) : β ≤ 2 := by
  have := h.dA; linarith [h.x0]

/-! ### Monotonicity in `x` -/

private theorem div_one_sub_mono {c x xb : ℝ} (hc : 0 ≤ c) (hxb : x ≤ xb) (h1 : xb < 1) :
    c * x / (1 - x) ≤ c * xb / (1 - xb) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have : 0 ≤ c * (xb - x) := mul_nonneg hc (by linarith)
  nlinarith

/-- The left side of the `delta` condition increases in `x` on `[0, 1/8]`:
`D = (b - a) (1 - ρ (a + b) + ρ a b + ρ (ρ - 1) / 2 (a² + a b + b² - a b (a + b)))`. -/
theorem deltaLHS_mono {ρ a b : ℝ} (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1 / 8) :
    (1 - ρ * a + ρ * (ρ - 1) * a ^ 2 / 2) * (2 - ρ) * a / (1 - a) ≤
      (1 - ρ * b + ρ * (ρ - 1) * b ^ 2 / 2) * (2 - ρ) * b / (1 - b) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  have hk : 0 ≤ ρ * (ρ - 1) / 2 := by nlinarith
  have hq0 : 0 ≤ a ^ 2 + a * b + b ^ 2 - a * b * (a + b) := by
    have : 0 ≤ a * b * (1 - (a + b)) := mul_nonneg (mul_nonneg ha (by linarith)) (by linarith)
    nlinarith [sq_nonneg a, sq_nonneg b]
  have hQ : 0 ≤ 1 - ρ * (a + b) + ρ * a * b + ρ * (ρ - 1) / 2 * (a ^ 2 + a * b + b ^ 2 - a * b * (a + b)) := by
    have : ρ * (a + b) ≤ 1 / 2 := by nlinarith
    have : 0 ≤ ρ * a * b := mul_nonneg (mul_nonneg (by linarith) ha) (by linarith)
    have : 0 ≤ ρ * (ρ - 1) / 2 * (a ^ 2 + a * b + b ^ 2 - a * b * (a + b)) := mul_nonneg hk hq0
    linarith
  have hD : (1 - ρ * b + ρ * (ρ - 1) * b ^ 2 / 2) * (2 - ρ) * b * (1 - a) -
      (1 - ρ * a + ρ * (ρ - 1) * a ^ 2 / 2) * (2 - ρ) * a * (1 - b) =
      (2 - ρ) * ((b - a) * (1 - ρ * (a + b) + ρ * a * b +
        ρ * (ρ - 1) / 2 * (a ^ 2 + a * b + b ^ 2 - a * b * (a + b)))) := by ring
  have : 0 ≤ (2 - ρ) * ((b - a) * (1 - ρ * (a + b) + ρ * a * b +
        ρ * (ρ - 1) / 2 * (a ^ 2 + a * b + b ^ 2 - a * b * (a + b)))) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) hQ)
  linarith

/-- **`SWNumeric` is monotone in `x`**: the side conditions at `xb` give them at every `x ∈ [0, xb]`. -/
theorem mono {xb : ℝ} (h : SWNumeric ρ β δ xb cU) (hx0 : 0 ≤ x) (hx : x ≤ xb) : SWNumeric ρ β δ x cU := by
  have h8 := h.x8; have hl := h.low; have hh := h.high
  have hxb1 : xb < 1 := by linarith
  have hy : 0 < 1 - xb := by linarith
  have hyx : 1 - xb ≤ 1 - x := by linarith
  have hpow : ∀ n : ℕ, (1 - xb) ^ n ≤ (1 - x) ^ n := fun n => pow_le_pow_left₀ hy.le hyx n
  refine ⟨hx0, hx.trans h8, hl, hh, ?_, ?_, ?_, ?_, h.cU0, h.beta0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := h.eA
    have : 0 ≤ (ρ - 1) * ρ * (xb - x) := mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith
  · exact (div_one_sub_mono (by linarith) hx hxb1).trans h.e1
  · exact h.eB.trans (hpow 65)
  · refine le_trans ?_ h.e3
    have h1 := div_one_sub_mono (c := 3 - ρ) (by linarith) hx hxb1
    have h2 : cU / (1 - x) ^ 3 ≤ cU / (1 - xb) ^ 3 :=
      div_le_div_of_nonneg_left h.cU0 (by positivity) (hpow 3)
    linarith
  · refine h.beta.trans ?_
    have h1 := div_one_sub_mono (c := ρ - 1) (by linarith) hx hxb1
    have h0 : 0 < 1 + (ρ - 1) * x / (1 - x) := by
      have : 0 ≤ (ρ - 1) * x / (1 - x) := div_nonneg (mul_nonneg (by linarith) hx0) (by linarith)
      linarith
    exact div_le_div_of_nonneg_left (by linarith) h0 (by linarith)
  · exact h.dA.trans (by linarith)
  · exact h.d3.trans (mul_le_mul_of_nonneg_left (hpow 2) (by norm_num))
  · exact h.d66.trans (mul_le_mul_of_nonneg_left (hpow 65) (by norm_num))
  · exact h.d67.trans (mul_le_mul_of_nonneg_left (hpow 66) (by norm_num))
  · exact (deltaLHS_mono (by linarith) hh hx0 hx h8).trans h.delta

end SWNumeric

/-! ### The per-class step inequalities (real forms, design §2.2) -/

/-- **Bernoulli for a probe hazard**: `(1 - h)^t ≤ 1 - t h` for `h ≤ 1`, `0 ≤ t ≤ 1`. -/
theorem one_sub_rpow_le_bernoulli {h t : ℝ} (hh1 : h ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - h) ^ t ≤ 1 - t * h := by
  have := rpow_one_add_le_one_add_mul_self (s := -h) (by linarith) ht0 ht1
  rw [← sub_eq_add_neg] at this
  linarith

/-- **`(1 - h)^ρ ≤ (1 - h) (1 - (ρ - 1) h)`** for `h ≤ 1`, `1 ≤ ρ ≤ 2`. -/
theorem one_sub_rpow_le_mul_bernoulli {h ρ : ℝ} (hh1 : h ≤ 1) (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) :
    (1 - h) ^ ρ ≤ (1 - h) * (1 - (ρ - 1) * h) := by
  have hsplit : (1 - h) ^ ρ = (1 - h) * (1 - h) ^ (ρ - 1) := by
    rcases (sub_nonneg.mpr hh1).eq_or_lt with h0 | h0
    · rw [← h0, Real.zero_rpow (by linarith)]; simp
    · rw [Real.rpow_sub_one h0.ne']; field_simp
  rw [hsplit]
  exact mul_le_mul_of_nonneg_left (one_sub_rpow_le_bernoulli hh1 (by linarith) (by linarith))
    (by linarith)

/-- **E1, real form** (an encoding at a retained key, unarmed): with the hazard `h ∈ [0, 1]`, the
remaining base `v ∈ [1 - x, 1]` and `4032 (2 - ρ) x / (1 - x) ≤ ρ - 1`,
`(1 - h)^ρ ≤ (1 - h) (1 - 4032 h (1 - v^(2 - ρ)))`. -/
theorem stepE1_real {h ρ x v : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (hx1 : x < 1)
    (hv : 1 - x ≤ v) (he1 : 4032 * (2 - ρ) * x / (1 - x) ≤ ρ - 1) :
    (1 - h) ^ ρ ≤ (1 - h) * (1 - 4032 * h * (1 - v ^ (2 - ρ))) := by
  refine (one_sub_rpow_le_mul_bernoulli hh1 hρ1 hρ2).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  have hv0 : 0 < v := by linarith
  have hj := one_sub_rpow_le_jump hv0 (c := 2 - ρ) (by linarith)
  have hq : (1 - v) / v ≤ x / (1 - x) := by
    rw [div_le_div_iff₀ hv0 (by linarith)]; nlinarith
  have hc : (2 - ρ) * (1 - v) / v ≤ (2 - ρ) * x / (1 - x) := by
    rw [mul_div_assoc, mul_div_assoc]; exact mul_le_mul_of_nonneg_left hq (by linarith)
  have hk : 4032 * (1 - v ^ (2 - ρ)) ≤ ρ - 1 := by
    have : 4032 * ((2 - ρ) * x / (1 - x)) ≤ ρ - 1 := by
      rw [show 4032 * ((2 - ρ) * x / (1 - x)) = 4032 * (2 - ρ) * x / (1 - x) by ring]; exact he1
    linarith
  nlinarith

/-- **EB, real form** (a chain step one below the word, unarmed): a guess `h` and a contact jumping
the exponent to `66`; with `v ∈ [1 - x, 1]` and `2 - ρ ≤ (1 - x)^65`,
`(1 - h)^ρ v^ρ ≤ (1 - h) (v^ρ - h (v^ρ - v^66))`. -/
theorem stepEB_real {h ρ x v : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (hx1 : x < 1)
    (hv : 1 - x ≤ v) (hv1 : v ≤ 1) (heB : 2 - ρ ≤ (1 - x) ^ 65) :
    (1 - h) ^ ρ * v ^ ρ ≤ (1 - h) * (v ^ ρ - h * (v ^ ρ - v ^ (66 : ℝ))) := by
  have hv0 : 0 < v := by linarith
  have hvρ : 0 ≤ v ^ ρ := Real.rpow_nonneg hv0.le _
  have hsplit : v ^ (66 : ℝ) = v ^ ρ * v ^ (66 - ρ) := by rw [← Real.rpow_add hv0]; ring_nf
  have h65 : (1 - x) ^ 65 ≤ v ^ (66 - ρ) := by
    calc (1 - x) ^ 65 ≤ v ^ (65 : ℕ) := pow_le_pow_left₀ (by linarith) hv 65
      _ = v ^ (65 : ℝ) := (Real.rpow_natCast v 65).symm
      _ ≤ v ^ (66 - ρ) := Real.rpow_le_rpow_of_exponent_ge hv0 hv1 (by linarith)
  have hb := one_sub_rpow_le_mul_bernoulli hh1 hρ1 hρ2
  have key : (1 - h) * (1 - (ρ - 1) * h) ≤ (1 - h) * (1 - h * (1 - v ^ (66 - ρ))) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by linarith)
  have : (1 - h) * (v ^ ρ - h * (v ^ ρ - v ^ (66 : ℝ))) = (1 - h) * (1 - h * (1 - v ^ (66 - ρ))) * v ^ ρ := by
    rw [hsplit]; ring
  rw [this]
  exact mul_le_mul_of_nonneg_right (hb.trans key) hvρ

/-- **EA, rpow form**: `1/2 ≤ (ρ - 1) v^ρ` for `v ∈ [1 - x, 1]` under `1/2 ≤ (ρ - 1)(1 - ρ x)`. -/
theorem stepEA_real {ρ x v : ℝ} (hρ1 : 1 ≤ ρ) (hx1 : x ≤ 1) (hv : 1 - x ≤ v)
    (heA : 1 / 2 ≤ (ρ - 1) * (1 - ρ * x)) : 1 / 2 ≤ (ρ - 1) * v ^ ρ := by
  have hb := one_add_mul_self_le_rpow_one_add (s := -x) (by linarith) hρ1
  rw [← sub_eq_add_neg] at hb
  have hmono : (1 - x) ^ ρ ≤ v ^ ρ := Real.rpow_le_rpow (by linarith) hv (by linarith)
  have : (ρ - 1) * (1 - ρ * x) ≤ (ρ - 1) * v ^ ρ :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

/-! ### The budget steps paid by the side conditions (at `x = T / 2^128`) -/

variable [Params]

namespace SWNumeric

variable {ρ β δ cU : ℝ} {total : ℕ}

theorem total_lt_space (h : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) : (total : ℝ) < spaceReal := by
  have h8 := h.x8
  rw [div_le_iff₀ (by positivity)] at h8
  have : spaceReal = 2 ^ 128 := rfl
  rw [this]
  linarith [(by positivity : (0 : ℝ) < 2 ^ 128)]

/-- A digest query at the unarmed exponent `ρ` frees `β / 2^128`. -/
theorem dec_rho (h : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (probes remaining : ℕ)
    (hle : probes + remaining + 1 ≤ total) :
    ENNReal.ofReal (β / 2 ^ 128) ≤ budgetE ρ probes remaining - budgetE ρ probes (remaining + 1) :=
  budgetE_dec_rho h.one_le_rho h.high total h.total_lt_space h.beta probes remaining hle

/-- A digest query at a natural exponent `n` frees `β / 2^128` once `β ≤ n (1 - x)^(n - 1)`. -/
theorem dec_nat (h : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (n : ℕ) (hn : 1 ≤ n)
    (hβ : β ≤ n * (1 - (total : ℝ) / 2 ^ 128) ^ (n - 1)) (probes remaining : ℕ)
    (hle : probes + remaining + 1 ≤ total) :
    ENNReal.ofReal (β / 2 ^ 128) ≤ budgetE n probes remaining - budgetE n probes (remaining + 1) :=
  budgetE_dec_nat n hn total h.total_lt_space.le hβ probes remaining hle

/-- A digest query at the armed exponent `2` frees `β / 2^128`. -/
theorem dec_two (h : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (probes remaining : ℕ)
    (hle : probes + remaining + 1 ≤ total) :
    ENNReal.ofReal (β / 2 ^ 128) ≤ budgetE 2 probes remaining - budgetE 2 probes (remaining + 1) := by
  have := h.dec_nat 2 (by norm_num) (by simpa using h.dA) probes remaining hle
  simpa using this

/-- A digest query at the exponent `3` frees `β / 2^128`. -/
theorem dec_three (h : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (probes remaining : ℕ)
    (hle : probes + remaining + 1 ≤ total) :
    ENNReal.ofReal (β / 2 ^ 128) ≤ budgetE 3 probes remaining - budgetE 3 probes (remaining + 1) := by
  have := h.dec_nat 3 (by norm_num) (by simpa using h.d3) probes remaining hle
  simpa using this

/-- A digest query at the exponent `66` frees `β / 2^128`. -/
theorem dec_66 (h : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (probes remaining : ℕ)
    (hle : probes + remaining + 1 ≤ total) :
    ENNReal.ofReal (β / 2 ^ 128) ≤ budgetE 66 probes remaining - budgetE 66 probes (remaining + 1) := by
  have := h.dec_nat 66 (by norm_num) (by simpa using h.d66) probes remaining hle
  simpa using this

/-- A digest query at the exponent `67` frees `β / 2^128`. -/
theorem dec_67 (h : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (probes remaining : ℕ)
    (hle : probes + remaining + 1 ≤ total) :
    ENNReal.ofReal (β / 2 ^ 128) ≤ budgetE 67 probes remaining - budgetE 67 probes (remaining + 1) := by
  have := h.dec_nat 67 (by norm_num) (by simpa using h.d67) probes remaining hle
  simpa using this

/-- **Arming** (exponent `ρ → 2`) at `p + r ≤ T` loses at most `δ`. -/
theorem arm (h : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (probes remaining : ℕ)
    (hle : probes + remaining ≤ total) :
    budgetE ρ probes remaining ≤ budgetE 2 probes remaining + ENNReal.ofReal δ :=
  budgetE_arm h.one_le_rho h.high total h.x8 h.delta probes remaining hle

/-- **Arming**, subtraction form. -/
theorem arm_sub (h : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (probes remaining : ℕ)
    (hle : probes + remaining ≤ total) :
    budgetE ρ probes remaining - budgetE 2 probes remaining ≤ ENNReal.ofReal δ :=
  budgetE_arm_sub h.one_le_rho h.high total h.x8 h.delta probes remaining hle

end SWNumeric

end FORS.Security.SWRoute
