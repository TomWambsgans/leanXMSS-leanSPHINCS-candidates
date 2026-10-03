import SphincsSecurity.Proof.Base.BinomialMoments
import Mathlib.Data.Nat.Choose.Cast

/-!
Exact arithmetic for the FORS lifetime estimate. The generic binomial-moment identities are
reused from leanVM b7a107256; all parameters and the degree-26 majorant below are new.
These bounds do not by themselves connect an adaptive signing experiment to independent
binomial occupancy. That probabilistic reduction must be supplied separately.
-/

namespace LeanSphincs.Lifetime

theorem pow_one_sub_le_quadratic {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : Nat) :
    (1 - p) ^ n ≤ 1 - n * p + (n.choose 2 : ℝ) * p ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hp1)
    rw [pow_succ (1 - p)]
    simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
    nlinarith [mul_nonneg (Nat.cast_nonneg (n.choose 2) : (0 : ℝ) ≤ n.choose 2)
      (pow_nonneg hp 3)]

theorem cubic_le_pow_one_sub {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : Nat) :
    1 - n * p + (n.choose 2 : ℝ) * p ^ 2 - (n.choose 3 : ℝ) * p ^ 3 ≤
      (1 - p) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hp1)
    rw [pow_succ (1 - p)]
    simp only [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
    nlinarith [mul_nonneg (Nat.cast_nonneg (n.choose 3) : (0 : ℝ) ≤ n.choose 3)
      (pow_nonneg hp 4)]

theorem cast_choose_three (n : Nat) :
    (n.choose 3 : ℝ) = n * (n - 1) * (n - 2) / 6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.choose_succ_succ, Nat.cast_add, ih, Nat.cast_choose_two]
    push_cast
    ring

/-- Second-order Taylor upper bound, with a sum of nonnegative monomials as its remainder. -/
theorem power24_le_quadratic {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 24 + 24 * y ^ 23 * (y - x) ≤
      y ^ 24 + 276 * y ^ 22 * (y - x) ^ 2 := by
  have hy := hx.trans hxy
  have hr : 0 ≤ (y - x) ^ 3 *
      ∑ i ∈ Finset.range 22, ((i + 2).choose 2 : ℝ) * y ^ i * x ^ (21 - i) := by
    apply mul_nonneg (pow_nonneg (sub_nonneg.mpr hxy) _)
    exact Finset.sum_nonneg (fun i _ => by positivity)
  have heq : y ^ 24 + 276 * y ^ 22 * (y - x) ^ 2 -
      (x ^ 24 + 24 * y ^ 23 * (y - x)) = (y - x) ^ 3 *
      ∑ i ∈ Finset.range 22, ((i + 2).choose 2 : ℝ) * y ^ i * x ^ (21 - i) := by
    norm_num [Finset.sum_range_succ, Nat.choose]
    ring
  linarith only [hr, heq]

/-- A globally valid degree-26 majorant for 24 independent FORS leaf-hit events. -/
theorem fors_power_majorant {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (r : Nat) :
    (1 - (1 - p) ^ r) ^ 24 ≤ p ^ 24 *
      ((1 + 12 * p + 77 * p ^ 2) * (r : ℝ) ^ 24 -
        (12 * p + 150 * p ^ 2) * (r : ℝ) ^ 25 + 73 * p ^ 2 * (r : ℝ) ^ 26) := by
  let x := 1 - (1 - p) ^ r
  let y := (r : ℝ) * p
  have hx : 0 ≤ x := sub_nonneg.mpr (pow_le_one₀ (sub_nonneg.mpr hp1) (by linarith))
  have hxy : x ≤ y := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -p by linarith) r
    dsimp [x, y]
    simp only [mul_neg, ← sub_eq_add_neg] at h
    linarith
  have hlo : (r.choose 2 : ℝ) * p ^ 2 - (r.choose 3 : ℝ) * p ^ 3 ≤ y - x := by
    have h := cubic_le_pow_one_sub hp hp1 r
    dsimp [x, y]
    linarith
  have hhi : y - x ≤ (r.choose 2 : ℝ) * p ^ 2 := by
    have h := pow_one_sub_le_quadratic hp hp1 r
    dsimp [x, y]
    linarith
  have hsquare : (y - x) ^ 2 ≤ ((r.choose 2 : ℝ) * p ^ 2) ^ 2 :=
    pow_le_pow_left₀ (sub_nonneg.mpr hxy) hhi 2
  have hlinear := mul_le_mul_of_nonneg_left hlo
    (show 0 ≤ 24 * y ^ 23 by dsimp [y]; positivity)
  have hquadratic := mul_le_mul_of_nonneg_left hsquare
    (show 0 ≤ 276 * y ^ 22 by dsimp [y]; positivity)
  have hmajor := power24_le_quadratic hx hxy
  have hbound : x ^ 24 ≤ y ^ 24 -
      24 * y ^ 23 * ((r.choose 2 : ℝ) * p ^ 2 - (r.choose 3 : ℝ) * p ^ 3) +
      276 * y ^ 22 * ((r.choose 2 : ℝ) * p ^ 2) ^ 2 := by
    linarith only [hmajor, hlinear, hquadratic]
  calc
    _ = x ^ 24 := rfl
    _ ≤ _ := hbound
    _ = _ := by rw [Nat.cast_choose_two, cast_choose_three]; dsimp [y]; ring

end LeanSphincs.Lifetime
