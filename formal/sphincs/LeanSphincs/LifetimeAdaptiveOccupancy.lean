import LeanSphincs.LifetimePoolGrinding
import Mathlib.Analysis.Complex.ExponentialBounds

/-! An adaptive occupancy bound. Every transition may depend on the complete private state;
only its conditional chance of hitting the selected index is bounded. Thus a history can
contain actual signing calls followed by an independent hypothetical continuation. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal
set_option exponentiation.threshold 1024

noncomputable def adaptiveHitCount {State : Type} (step : Nat → State → ProbComp (Bool × State)) :
    Nat → State → ProbComp Nat
  | 0, _ => pure 0
  | n + 1, state => do
      let next ← step n state
      let count ← adaptiveHitCount step n next.2
      return count + if next.1 then 1 else 0

/-- The exponential moment survives arbitrary adaptation of the private state. -/
theorem adaptiveHitCount_moment {State : Type} (step : Nat → State → ProbComp (Bool × State))
    (rate : ℝ≥0∞)
    (hstep : ∀ n state, Pr[fun next => next.1 | step n state] ≤ rate)
    (n : Nat) (state : State) :
    (∑' count, Pr[= count | adaptiveHitCount step n state] * (8 : ℝ≥0∞) ^ count) ≤
      (1 + 7 * rate) ^ n := by
  induction n generalizing state with
  | zero => simp [adaptiveHitCount, tsum_probOutput_pure_mul]
  | succ n ih =>
      simp only [adaptiveHitCount, tsum_probOutput_bind_mul, tsum_probOutput_pure_mul, pow_add, pow_one]
      have hmoment : (∑' next, Pr[= next | step n state] *
          ((8 : ℝ≥0∞) ^ (if next.1 then 1 else 0))) ≤ 1 + 7 * rate := by
        have hpoint (next : Bool × State) :
            (8 : ℝ≥0∞) ^ (if next.1 then 1 else 0) =
              1 + 7 * if next.1 then 1 else 0 := by cases next.1 <;> norm_num
        simp_rw [hpoint, mul_add, mul_one]
        rw [ENNReal.tsum_add, tsum_probOutput_of_liftM_PMF]
        simp_rw [mul_left_comm (Pr[= _ | step n state]) 7]
        rw [ENNReal.tsum_mul_left]
        simp only [mul_ite, mul_one, mul_zero]
        rw [← probEvent_eq_tsum_ite]
        exact add_le_add le_rfl (mul_le_mul' le_rfl (hstep n state))
      calc
        _ ≤ ∑' next, Pr[= next | step n state] *
            ((1 + 7 * rate) ^ n * 8 ^ (if next.1 then 1 else 0)) := by
          apply ENNReal.tsum_le_tsum
          intro next
          apply mul_le_mul' le_rfl
          calc
            _ = (∑' count, Pr[= count | adaptiveHitCount step n next.2] * 8 ^ count) *
                8 ^ (if next.1 then 1 else 0) := by
              simp_rw [← mul_assoc]
              rw [ENNReal.tsum_mul_right]
            _ ≤ _ := mul_le_mul' (ih next.2) le_rfl
        _ = (1 + 7 * rate) ^ n *
            (∑' next, Pr[= next | step n state] * 8 ^ (if next.1 then 1 else 0)) := by
          simp_rw [mul_left_comm (Pr[= _ | step n state]) ((1 + 7 * rate) ^ n)]
          rw [ENNReal.tsum_mul_left]
        _ ≤ _ := mul_le_mul' le_rfl hmoment

/-- Exponential Markov bound; the count process need not have independent increments. -/
theorem adaptiveHitCount_tail {State : Type} (step : Nat → State → ProbComp (Bool × State))
    (rate : ℝ≥0∞)
    (hstep : ∀ n state, Pr[fun next => next.1 | step n state] ≤ rate)
    (n threshold : Nat) (state : State) :
    Pr[fun count => threshold ≤ count | adaptiveHitCount step n state] * 8 ^ threshold ≤
      (1 + 7 * rate) ^ n := by
  refine le_trans ?_ (adaptiveHitCount_moment step rate hstep n state)
  rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro count
  by_cases hc : threshold ≤ count
  · simp only [hc, if_true]
    exact mul_le_mul' le_rfl (pow_le_pow_right₀ (by norm_num : (1 : ℝ≥0∞) ≤ 8) hc)
  · simp only [hc, if_false, zero_mul]
    exact bot_le

/-- Mean at most32 gives a256-hit tail at most2^-320. This intentionally uses a coarse
`exp(1)≤4` bound so the numerical certificate is small. -/
theorem occupancy_exponential_bound (n : Nat) (rate : ℝ) (hrate : 0 ≤ rate)
    (hmean : (n : ℝ) * rate ≤ 32) :
    (1 + 7 * rate) ^ n / (8 : ℝ) ^ 256 ≤ 1 / (2 : ℝ) ^ 320 := by
  have hbase : 1 + 7 * rate ≤ Real.exp (7 * rate) := by
    simpa [add_comm] using Real.add_one_le_exp (7 * rate)
  have hexp : (1 + 7 * rate) ^ n ≤ Real.exp 224 := by
    calc
      _ ≤ (Real.exp (7 * rate)) ^ n := pow_le_pow_left₀ (by positivity) hbase _
      _ = Real.exp ((n : ℝ) * (7 * rate)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp 224 := Real.exp_le_exp.mpr (by nlinarith)
  have hone : Real.exp 1 ≤ 4 := le_trans Real.exp_one_lt_three.le (by norm_num)
  have h224 : Real.exp 224 ≤ (4 : ℝ) ^ 224 := by
    calc
      _ = (Real.exp 1) ^ 224 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hone _
  exact (div_le_div_of_nonneg_right (hexp.trans h224) (by positivity)).trans (by norm_num)

/-- The explicit per-index numerical tail used for localization. -/
theorem adaptiveHitCount_tail_256 {State : Type} (step : Nat → State → ProbComp (Bool × State))
    (rate : ℝ) (hrate : 0 ≤ rate)
    (hstep : ∀ n state, Pr[fun next => next.1 | step n state] ≤ ENNReal.ofReal rate)
    (n : Nat) (hmean : (n : ℝ) * rate ≤ 32) (state : State) :
    Pr[fun count => 256 ≤ count | adaptiveHitCount step n state] ≤ 1 / (2 : ℝ≥0∞) ^ 320 := by
  have h := adaptiveHitCount_tail step (ENNReal.ofReal rate) hstep n 256 state
  have hdiv : Pr[fun count => 256 ≤ count | adaptiveHitCount step n state] ≤
      (1 + 7 * ENNReal.ofReal rate) ^ n / 8 ^ 256 := by
    exact (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by finiteness))).mpr h
  have hreal := ENNReal.ofReal_le_ofReal (occupancy_exponential_bound n rate hrate hmean)
  have hbase : ENNReal.ofReal (1 + 7 * rate) = 1 + 7 * ENNReal.ofReal rate := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_mul (by norm_num)]
    norm_num
  have hnum : ENNReal.ofReal ((8 : ℝ) ^ 256) = (8 : ℝ≥0∞) ^ 256 := by simp
  have hden : ENNReal.ofReal ((2 : ℝ) ^ 320) = (2 : ℝ≥0∞) ^ 320 := by simp
  simp only [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 8 ^ 256),
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ 320),
    ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 1 + 7 * rate), hbase, hnum, hden,
    ENNReal.ofReal_one] at hreal
  exact hdiv.trans hreal

/-- Union over all2^26 global leaf positions. This statement concerns one common trace
law, so no independence between indices is required. -/
theorem global_occupancy_tail {α : Type} (program : ProbComp α) (count : α → Index → Nat)
    (hindex : ∀ index, Pr[fun result => 256 ≤ count result index | program] ≤
      1 / (2 : ℝ≥0∞) ^ 320) :
    Pr[fun result => ∃ index, 256 ≤ count result index | program] ≤
      1 / (2 : ℝ≥0∞) ^ 294 := by
  have h := probEvent_exists_finset_le_sum Finset.univ program
    (fun index result => 256 ≤ count result index)
  simp only [Finset.mem_univ, true_and] at h
  refine h.trans ((Finset.sum_le_sum (fun index _ => hindex index)).trans ?_)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : Fintype.card Index = 2 ^ 26 := Fintype.card_fin _
  rw [hc]
  have hreal : (2 : ℝ) ^ 26 * (1 / (2 : ℝ) ^ 320) ≤ 1 / (2 : ℝ) ^ 294 := by norm_num
  have hh := ENNReal.ofReal_le_ofReal hreal
  simpa only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ 26),
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ 320),
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ 294),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_one, Nat.cast_pow, Nat.cast_ofNat] using hh

end LeanSphincs.Lifetime
