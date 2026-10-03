import LeanSphincs.LifetimeCoverage

/-! A real-valued binomial expectation and its exact factorial moments. The proof route is
adapted from leanVM b7a107256's generic `BinomialMoments.lean`. -/

namespace LeanSphincs.Lifetime

noncomputable def binomialMean (rate : ℝ) : Nat → (Nat → ℝ) → ℝ
  | 0, f => f 0
  | n + 1, f => (1 - rate) * binomialMean rate n f +
      rate * binomialMean rate n (fun r => f (r + 1))

theorem binomialMean_add (rate : ℝ) (n : Nat) (f g : Nat → ℝ) :
    binomialMean rate n (fun r => f r + g r) =
      binomialMean rate n f + binomialMean rate n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [binomialMean, ih]; ring

theorem binomialMean_sub (rate : ℝ) (n : Nat) (f g : Nat → ℝ) :
    binomialMean rate n (fun r => f r - g r) =
      binomialMean rate n f - binomialMean rate n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [binomialMean, ih]; ring

theorem binomialMean_mul (rate factor : ℝ) (n : Nat) (f : Nat → ℝ) :
    binomialMean rate n (fun r => factor * f r) =
      factor * binomialMean rate n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [binomialMean, ih]; ring

theorem binomialMean_sum {α : Type*} (rate : ℝ) (n : Nat) (s : Finset α)
    (f : α → Nat → ℝ) :
    binomialMean rate n (fun r => ∑ i ∈ s, f i r) =
      ∑ i ∈ s, binomialMean rate n (f i) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [binomialMean, ih, Finset.mul_sum, Finset.sum_add_distrib]

theorem binomialMean_mono {rate : ℝ} (h0 : 0 ≤ rate) (h1 : rate ≤ 1) (n : Nat)
    {f g : Nat → ℝ} (hfg : ∀ r, f r ≤ g r) :
    binomialMean rate n f ≤ binomialMean rate n g := by
  induction n generalizing f g with
  | zero => exact hfg 0
  | succ n ih =>
    exact add_le_add (mul_le_mul_of_nonneg_left (ih hfg) (sub_nonneg.mpr h1))
      (mul_le_mul_of_nonneg_left (ih (fun r => hfg (r + 1))) h0)

theorem binomialMean_const (rate : ℝ) (n : Nat) (x : ℝ) :
    binomialMean rate n (fun _ => x) = x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [binomialMean, ih]; ring

theorem binomialMean_nonneg {rate : ℝ} (h0 : 0 ≤ rate) (h1 : rate ≤ 1) (n : Nat)
    {f : Nat → ℝ} (hf : ∀ r, 0 ≤ f r) : 0 ≤ binomialMean rate n f := by
  simpa only [binomialMean_const] using binomialMean_mono h0 h1 n hf

theorem binomialMean_mono_steps {rate : ℝ} (h0 : 0 ≤ rate) (h1 : rate ≤ 1)
    {f : Nat → ℝ} (hf : Monotone f) : Monotone (fun n => binomialMean rate n f) := by
  apply monotone_nat_of_le_succ
  intro n
  have hshift := binomialMean_mono h0 h1 n (fun r => hf (Nat.le_succ r))
  have hmul := mul_le_mul_of_nonneg_left hshift h0
  rw [binomialMean]
  nlinarith only [hmul]

theorem binomialMean_choose (rate : ℝ) (n k : Nat) :
    binomialMean rate n (fun r => (r.choose k : ℝ)) = (n.choose k : ℝ) * rate ^ k := by
  induction n generalizing k with
  | zero => cases k <;> simp [binomialMean]
  | succ n ih =>
    cases k with
    | zero => simp [binomialMean_const]
    | succ k =>
      simp only [binomialMean, Nat.choose_succ_succ, Nat.cast_add]
      rw [binomialMean_add]
      simp only [ih, pow_succ]
      ring

theorem binomialMean_descFactorial (rate : ℝ) (n k : Nat) :
    binomialMean rate n (fun r => (r.descFactorial k : ℝ)) =
      (n.descFactorial k : ℝ) * rate ^ k := by
  simp_rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  rw [binomialMean_mul, binomialMean_choose]
  ring

theorem binomialMean_power (rate : ℝ) (n d : Nat) :
    binomialMean rate n (fun r => (r : ℝ) ^ d) =
      ∑ k ∈ Finset.range (d + 1), (Nat.stirlingSecond d k : ℝ) *
        (n.descFactorial k : ℝ) * rate ^ k := by
  have hp (r : Nat) : (r : ℝ) ^ d = ∑ k ∈ Finset.range (d + 1),
      (Nat.stirlingSecond d k : ℝ) * (r.descFactorial k : ℝ) := by
    exact_mod_cast SphincsSecurity.Concrete.power_eq_stirling_descFactorial r d
  simp_rw [hp]
  rw [binomialMean_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [binomialMean_mul, binomialMean_descFactorial]
  ring

def momentNumerator (b n d : Nat) : Nat :=
  ∑ k ∈ Finset.range (d + 1),
    Nat.stirlingSecond d k * n.descFactorial k * (2 ^ b) ^ (d - k)

theorem binomialMean_power_numerator (b n d : Nat) :
    binomialMean ((2 : ℝ) ^ b)⁻¹ n (fun r => (r : ℝ) ^ d) =
      (momentNumerator b n d : ℝ) / ((2 : ℝ) ^ b) ^ d := by
  rw [binomialMean_power]
  simp only [momentNumerator, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hd : ((2 : ℝ) ^ b) ^ d = ((2 : ℝ) ^ b) ^ (d - k) * ((2 : ℝ) ^ b) ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  rw [hd, inv_pow]
  field_simp

/-- The majorant is a combination of only the 24th, 25th, and 26th binomial moments. -/
theorem binomialMean_fors_le {rate : ℝ} (hr0 : 0 ≤ rate) (hr1 : rate ≤ 1)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : Nat) :
    binomialMean rate n (fun r => (1 - (1 - p) ^ r) ^ 24) ≤ p ^ 24 *
      ((1 + 12 * p + 77 * p ^ 2) * binomialMean rate n (fun r => (r : ℝ) ^ 24) -
        (12 * p + 150 * p ^ 2) * binomialMean rate n (fun r => (r : ℝ) ^ 25) +
        73 * p ^ 2 * binomialMean rate n (fun r => (r : ℝ) ^ 26)) := by
  convert binomialMean_mono hr0 hr1 n (fors_power_majorant hp hp1) using 1
  simp only [binomialMean_mul, binomialMean_add, binomialMean_sub]

end LeanSphincs.Lifetime
