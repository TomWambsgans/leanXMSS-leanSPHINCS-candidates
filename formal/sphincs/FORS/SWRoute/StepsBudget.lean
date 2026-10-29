import FORS.SWRoute.StepsStore
import FORS.SWRoute.StepReal

/-! **The SW route: budget steps by class.** The exponent of a state with positive weight is one of
`ρ, 2, 3, 66`; a digest query frees `β / 2^128` at each of them; arming costs at most `δ`; a step
whose only hazards are a guess and a killing contact, or a first-order hazard and a killing event,
fits at any exponent at least `2` (resp. `1`, resp. `66` with `64` killing values). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost PotentialA GraphView ForsPotential

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### Units -/

theorem nu_eq_ofReal' : ENNReal.ofReal (1 / 2 ^ 128) = ν := by
  rw [ν_eq_ofReal, one_div]

theorem half_nu_eq_ofReal : ENNReal.ofReal (1 / 2 ^ 129) = ν / 2 := by
  rw [show (1 : ℝ) / 2 ^ 129 = (1 / 2 ^ 128) / 2 by norm_num, ENNReal.ofReal_div_of_pos (by norm_num),
    nu_eq_ofReal', ENNReal.ofReal_ofNat]

theorem nu_le_one : ν ≤ 1 := by
  unfold ν
  exact ENNReal.inv_le_one.2 (one_le_pow₀ (by norm_num))

theorem one_sub_nu_add : ENNReal.ofReal (1 - 1 / 2 ^ 128) + ν = 1 := by
  rw [← nu_eq_ofReal', ← ENNReal.ofReal_add (by norm_num) (by positivity), sub_add_cancel, ENNReal.ofReal_one]

theorem probeFactor_add_nu_le (p : ℕ) (hp : (p : ℝ) + 1 < spaceReal) : probeFactor p + ν ≤ 1 := by
  have hN : spaceReal = 2 ^ 128 := rfl
  have hden : 0 < spaceReal - p := by linarith
  have h1 : 1 / spaceReal ≤ 1 / (spaceReal - p) :=
    one_div_le_one_div_of_le hden (by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)])
  have h2 : 1 / (spaceReal - p) ≤ 1 := by rw [div_le_one hden]; linarith
  rw [probeFactor, ← nu_eq_ofReal', ← hN, ← ENNReal.ofReal_add (by linarith) (div_nonneg zero_le_one spaceReal_pos.le), ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by linarith)

theorem probeFactor_le_one' (p : ℕ) (hp : (p : ℝ) + 1 < spaceReal) : probeFactor p ≤ 1 :=
  le_trans le_self_add (probeFactor_add_nu_le p hp)

theorem probeFactor_ne_top (p : ℕ) : probeFactor p ≠ ⊤ := ENNReal.ofReal_ne_top

/-! ### Kill forms -/

theorem one_sub_mul_le_inv_pow {hz : ℝ} (h1 : hz ≤ 1) (n : ℕ) :
    (1 - hz) ^ n * (1 + n * hz) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hg : 0 ≤ 1 - hz := by linarith
      calc (1 - hz) ^ (n + 1) * (1 + ((n + 1 : ℕ) : ℝ) * hz)
          = (1 - hz) ^ n * ((1 - hz) * (1 + (n + 1) * hz)) := by push_cast; ring
        _ ≤ (1 - hz) ^ n * (1 + n * hz) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg hg n)
            nlinarith [sq_nonneg hz]
        _ ≤ 1 := ih

section Kill

variable {ρ β δ cU : ℝ} {T : ℕ} (h : SWNumeric ρ β δ ((T : ℝ) / 2 ^ 128) cU) {p r : ℕ} (hle : p + r + 1 ≤ T)
include h hle

theorem sw_hp : (p : ℝ) + 1 < spaceReal := by
  have := sw_lt h hle
  linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

theorem rpow_probeFactor_le_sq {e : ℝ} (he : 2 ≤ e) : probeFactor p ^ e ≤ probeFactor p * probeFactor p := by
  have hpf := probeFactor_le_one' p (sw_hp h hle)
  calc probeFactor p ^ e ≤ probeFactor p ^ (2 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_ge hpf he
    _ = probeFactor p * probeFactor p := by rw [ENNReal.rpow_two, sq]

theorem rpow_probeFactor_le {e : ℝ} (he : 1 ≤ e) : probeFactor p ^ e ≤ probeFactor p := by
  have hpf := probeFactor_le_one' p (sw_hp h hle)
  calc probeFactor p ^ e ≤ probeFactor p ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_ge hpf he
    _ = probeFactor p := ENNReal.rpow_one _

/-- **Guess and killing contact** at an exponent `e ≥ 2`. -/
theorem kill_guess {e : ℝ} (he : 2 ≤ e) :
    budgetE e p (r + 1) + probeFactor p * ν * budgetE e (p + 1) r ≤ probeFactor p * budgetE e (p + 1) r := by
  rw [budgetE_probe (by linarith) p r (sw_lt h hle)]
  have hk := probeFactor_add_nu_le p (sw_hp h hle)
  calc probeFactor p ^ e * budgetE e (p + 1) r + probeFactor p * ν * budgetE e (p + 1) r
      ≤ probeFactor p * probeFactor p * budgetE e (p + 1) r + probeFactor p * ν * budgetE e (p + 1) r := by
        gcongr
        exact rpow_probeFactor_le_sq h hle he
    _ = probeFactor p * (probeFactor p + ν) * budgetE e (p + 1) r := by ring
    _ ≤ probeFactor p * 1 * budgetE e (p + 1) r := by gcongr
    _ = _ := by rw [mul_one]

/-- **A killing event of mean `2^-128` without guess** at an exponent `e ≥ 1`. -/
theorem kill_plain {e : ℝ} (he : 1 ≤ e) :
    budgetE e p (r + 1) + ν * budgetE e (p + 1) r ≤ budgetE e (p + 1) r := by
  rw [budgetE_probe (by linarith) p r (sw_lt h hle)]
  have hk := probeFactor_add_nu_le p (sw_hp h hle)
  calc probeFactor p ^ e * budgetE e (p + 1) r + ν * budgetE e (p + 1) r
      ≤ probeFactor p * budgetE e (p + 1) r + ν * budgetE e (p + 1) r := by
        gcongr
        exact rpow_probeFactor_le h hle he
    _ = (probeFactor p + ν) * budgetE e (p + 1) r := by ring
    _ ≤ 1 * budgetE e (p + 1) r := by gcongr
    _ = _ := one_mul _

/-- A guess without any event at an exponent `e ≥ 1`. -/
theorem guess_plain {e : ℝ} (he : 1 ≤ e) :
    budgetE e p (r + 1) ≤ probeFactor p * budgetE e (p + 1) r := by
  rw [budgetE_probe (by linarith) p r (sw_lt h hle)]
  gcongr
  exact rpow_probeFactor_le h hle he

/-- **Encoding at the key of a WOTS contact**: a first-order hazard and `63` killing marker values
fit at the exponent `66`. -/
theorem kill_enc66 :
    budgetE 66 p (r + 1) + 64 * ν * budgetE 66 (p + 1) r ≤ budgetE 66 (p + 1) r := by
  have hz0 := swHz_pos h hle
  have hz1 := swHz_lt_one h hle
  have hν := nu_le_swHz h hle
  have hzs : swHz p ≤ 2 / 2 ^ 128 := by
    have hT := sw_T_le h hle
    have hreal := sw_hreal h hle
    unfold swHz
    have hN : spaceReal = 2 ^ 128 := rfl
    rw [hN, div_le_div_iff₀ (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]) (by positivity)]
    nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hv0 := swV_pos h hle
  have hpow := one_sub_mul_le_inv_pow hz1.le 66
  have key : (1 - swHz p) ^ (66 : ℕ) + 64 * (1 / 2 ^ 128) ≤ 1 := by
    have hpos : 0 < 1 + (66 : ℕ) * swHz p := by positivity
    have hle1 : (1 - swHz p) ^ (66 : ℕ) ≤ 1 / (1 + (66 : ℕ) * swHz p) := by
      rw [le_div_iff₀ hpos]; exact hpow
    have h2 : 1 / (1 + (66 : ℕ) * swHz p) ≤ 1 - 64 * swHz p := by
      rw [div_le_iff₀ hpos]
      push_cast
      nlinarith
    linarith
  rw [budgetE_probe_sw h hle (by norm_num), budgetE_succ_eq_swV]
  rw [show (64 : ℝ≥0∞) * ν = ENNReal.ofReal (64 * (1 / 2 ^ 128)) by
    rw [ENNReal.ofReal_mul (by norm_num), nu_eq_ofReal']; simp]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hg : 0 ≤ 1 - swHz p := by linarith
  rw [show ((66 : ℝ)) = ((66 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    Real.rpow_natCast]
  have hvp : 0 ≤ swV p r ^ (66 : ℕ) := pow_nonneg hv0.le _
  nlinarith

end Kill

/-! ### Exponents of states with positive weight -/

section Expo

variable (K : Ctx) (root : Digest) (ρ : ℝ)

theorem expo_unarmed {flag : Bool} {s : St} (h : ¬ArmedS K flag s) : expo K ρ flag s = ρ := by
  have hw : ¬WContact K s := fun hw => h (Or.inr (Or.inl (by
    obtain ⟨l, i, hl, hc⟩ := hw
    exact ⟨l, hl, Or.inr ⟨i, hc⟩⟩)))
  have hf : ¬FContact K s := fun hf => h (Or.inr (Or.inr hf))
  unfold expo
  rw [if_neg h, if_neg hw, if_neg hf]
  ring

theorem expo_armed {flag : Bool} {s : St} (h : ArmedS K flag s) (hb : ¬BadP K root s) :
    expo K ρ flag s = 2 ∨ expo K ρ flag s = 3 ∨ expo K ρ flag s = 66 := by
  have hnd : ¬(WContact K s ∧ FContact K s) := fun hd => hb (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr hd)))))
  unfold expo
  rw [if_pos h]
  by_cases hw : WContact K s
  · have hf : ¬FContact K s := fun hf => hnd ⟨hw, hf⟩
    rw [if_pos hw, if_neg hf]
    right; right; norm_num
  · rw [if_neg hw]
    by_cases hf : FContact K s
    · rw [if_pos hf]; right; left; norm_num
    · rw [if_neg hf]; left; norm_num

theorem expo_cases {flag : Bool} {s : St} (hb : ¬BadP K root s) :
    expo K ρ flag s = ρ ∨ expo K ρ flag s = 2 ∨ expo K ρ flag s = 3 ∨ expo K ρ flag s = 66 := by
  by_cases h : ArmedS K flag s
  · exact Or.inr (expo_armed K root ρ h hb)
  · exact Or.inl (expo_unarmed K ρ h)

theorem expo_ge_two {flag : Bool} {s : St} (h : ArmedS K flag s) (hb : ¬BadP K root s) : 2 ≤ expo K ρ flag s := by
  rcases expo_armed K root ρ h hb with he | he | he <;> rw [he] <;> norm_num

theorem expo_ge_one (hρ : 1 ≤ ρ) {flag : Bool} {s : St} (hb : ¬BadP K root s) : 1 ≤ expo K ρ flag s := by
  rcases expo_cases K root ρ hb with h | h | h | h <;> rw [h] <;> linarith

theorem expo_nonneg (hρ : 0 ≤ ρ) (flag : Bool) (s : St) : 0 ≤ expo K ρ flag s := by
  unfold expo
  split_ifs <;> linarith

end Expo

/-! ### Digest decrement and arming -/

section Dec

variable (K : Ctx) (root : Digest) {ρ β δ cU : ℝ} {T : ℕ} (h : SWNumeric ρ β δ ((T : ℝ) / 2 ^ 128) cU)

include h in
/-- **A digest query frees `β / 2^128`** at the exponent of every state with positive weight. -/
theorem dec_expo {flag : Bool} {s : St} (hb : ¬BadP K root s) (p r : ℕ) (hle : p + r + 1 ≤ T) :
    ENNReal.ofReal (β / 2 ^ 128) ≤ budgetE (expo K ρ flag s) p r - budgetE (expo K ρ flag s) p (r + 1) := by
  rcases expo_cases K root ρ hb with he | he | he | he <;> rw [he]
  · exact h.dec_rho p r hle
  · exact h.dec_two p r hle
  · exact h.dec_three p r hle
  · exact h.dec_66 p r hle

include h in
/-- The decrement in additive form. -/
theorem dec_expo_add {flag : Bool} {s : St} (hb : ¬BadP K root s) (p r : ℕ) (hle : p + r + 1 ≤ T) :
    budgetE (expo K ρ flag s) p (r + 1) + ENNReal.ofReal (β / 2 ^ 128) ≤ budgetE (expo K ρ flag s) p r := by
  have hd := dec_expo K root h (flag := flag) hb p r hle
  have hmono : budgetE (expo K ρ flag s) p (r + 1) ≤ budgetE (expo K ρ flag s) p r :=
    budgetE_succ_le (expo_nonneg K ρ (by linarith [h.low]) flag s) p r
      (by have := sw_lt h hle; linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)])
  calc budgetE (expo K ρ flag s) p (r + 1) + ENNReal.ofReal (β / 2 ^ 128)
      ≤ budgetE (expo K ρ flag s) p (r + 1) +
          (budgetE (expo K ρ flag s) p r - budgetE (expo K ρ flag s) p (r + 1)) := add_le_add le_rfl hd
    _ = _ := add_tsub_cancel_of_le hmono

include h in
/-- **Arming at a FORS leaf query** costs at most `δ` times the weight. -/
theorem arm_conv (input : CostSpec.Domain) (s : St) (flag : Bool) (p r : ℕ) (hle : p + r ≤ T) :
    budgetE (expo K ρ flag s) p r * weightA K root s ≤
      budgetE (expo K ρ (nextFlag K root flag s input) s) p r * weightA K root s +
        ENNReal.ofReal δ * payA K root flag s input := by
  cases flag with
  | true =>
      have : nextFlag K root true s input = true := by simp [nextFlag]
      rw [this]
      exact le_self_add
  | false =>
      by_cases hA : ArmsAt K root s input
      · have hn : nextFlag K root false s input = true := by simp [nextFlag, hA]
        have hp : payA K root false s input = weightA K root s := by simp [payA, hA]
        rw [hn, hp]
        by_cases harm : ArmedS K false s
        · have harm' : ArmedS K true s := Or.inl rfl
          have : expo K ρ false s = expo K ρ true s := by
            unfold expo; rw [if_pos harm, if_pos harm']
          rw [this]
          exact le_self_add
        · have h1 : expo K ρ false s = ρ := expo_unarmed K ρ harm
          have hw : ¬WContact K s := fun hw => harm (Or.inr (Or.inl (by
            obtain ⟨l, i, hl, hc⟩ := hw
            exact ⟨l, hl, Or.inr ⟨i, hc⟩⟩)))
          have hf : ¬FContact K s := fun hf => harm (Or.inr (Or.inr hf))
          have h2 : expo K ρ true s = 2 := by
            unfold expo; rw [if_pos (show ArmedS K true s from Or.inl rfl), if_neg hw, if_neg hf]; ring
          rw [h1, h2]
          calc budgetE ρ p r * weightA K root s ≤ (budgetE 2 p r + ENNReal.ofReal δ) * weightA K root s :=
                mul_le_mul_left (h.arm p r hle) _
            _ = _ := by ring
      · have hn : nextFlag K root false s input = false := by simp [nextFlag, hA]
        rw [hn]
        exact le_self_add

end Dec

end FORS.Security.SWRoute
