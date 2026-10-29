import FORS.SWRoute.ContactGood

/-! **The coin of the contact potential at the start fits `coinSW`.** With the cell threshold
`T ≥ (3/2) · revRate · q'` and `T ≥ 2^12`, and `revRate ≤ 2^-31` (`31 ≤ b + a`), the coin forecast
`coinPotK T q'` is at most `x²/2^30 + x/2^100` (`x = q'/2^128`) once `T ≤ (3/2) revRate q' + 4097`, and the
coin cap at the start is at most `2^-180`: there are at most `2^46` cells, and
`(1 + revRate/2)^q' (2/3)^T ≤ (e^{1/3} · 2/3)^T ≤ (14/15)^4096 ≤ 2^-372`. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.LoopWalk ForsPotential PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

theorem cinv_eq_ν : cinv = ν := by
  unfold cinv ν
  rw [show (Fintype.card Randomness : ℝ≥0∞) = 2 ^ 128 from by
    rw [show Fintype.card Randomness = 2 ^ 128 from HiddenDebt.card_digest]; norm_num]

theorem revRate_eq : revRate = ENNReal.ofReal (1 / (2 ^ subtreeHeight * 2 ^ forsHeight)) := by
  unfold revRate
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one, one_div]
  congr 1
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]
  push_cast
  rfl

theorem card_cell_le : Fintype.card Cell ≤ 2 ^ 46 := by
  have h1 : Fintype.card Index = 2 ^ totalHeight := by simp [Index]
  have h2 : Fintype.card FTree = forsTrees := by simp [FTree]
  have h3 : Fintype.card FLeaf = 2 ^ forsHeight := by simp [FLeaf]
  rw [show Fintype.card Cell = Fintype.card Index * (Fintype.card FTree * Fintype.card FLeaf) from by
    simp [Cell, Fintype.card_prod], h1, h2, h3]
  have ht : 2 ^ totalHeight ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) Params.totalHeight_le
  have hk : forsTrees ≤ 64 := Params.forsTrees_le
  have ha : 2 ^ forsHeight ≤ 2 ^ 12 := Nat.pow_le_pow_right (by norm_num) Params.forsHeight_le
  calc 2 ^ totalHeight * (forsTrees * 2 ^ forsHeight) ≤ 2 ^ 28 * (64 * 2 ^ 12) := by gcongr
    _ = 2 ^ 46 := by norm_num

/-- `e^{1/3} ≤ 7/5`. -/
theorem exp_third_le : Real.exp (1 / 3) ≤ 7 / 5 := by
  by_contra h
  push Not at h
  have h3 : (7 / 5 : ℝ) ^ 3 < Real.exp (1 / 3) ^ 3 := pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  rw [← Real.exp_nat_mul] at h3
  norm_num at h3
  have := Real.exp_one_lt_d9
  linarith

/-- **The coin cap at the start.** -/
theorem capC_start_le (parameter : PublicParameter) (data : PublicData) (initial : HiddenOutside.Cache HashInput HashOutput)
    (known : HiddenReveal.Knowledge Coordinate) (T q : ℕ) (hT1 : 2 ^ 12 ≤ T)
    (hT : 3 * (q : ℝ) * (1 / (2 ^ subtreeHeight * 2 ^ forsHeight)) ≤ 2 * T) :
    capC parameter data T q (DebtState.start initial known) [] [] ≤ ENNReal.ofReal (1 / 2 ^ 180) := by
  set r : ℝ := 1 / (2 ^ subtreeHeight * 2 ^ forsHeight) with hr
  have hr0 : 0 ≤ r := by positivity
  have hterm : ∀ c : Cell, ((3 : ℝ≥0∞) / 2) ^ ncell parameter data c (DebtState.start initial known) [] [] *
      (1 + revRate / 2) ^ q * ((2 : ℝ≥0∞) / 3) ^ T = ENNReal.ofReal ((1 + r / 2) ^ q * (2 / 3) ^ T) := by
    intro c
    have hn : ncell parameter data c (DebtState.start initial known) [] [] = 0 := rfl
    have hrr : ENNReal.ofReal (1 + r / 2) = 1 + revRate / 2 := by
      rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one,
        ENNReal.ofReal_div_of_pos (by norm_num), revRate_eq, ← hr, ENNReal.ofReal_ofNat]
    have h23 : ENNReal.ofReal (2 / 3) = (2 : ℝ≥0∞) / 3 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
    rw [hn, pow_zero, one_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_pow (by norm_num), hrr, h23]
  -- the real estimate
  have hreal : (1 + r / 2) ^ q * (2 / 3 : ℝ) ^ T ≤ (1 / 2) ^ 372 := by
    have h1 : (1 + r / 2) ^ q ≤ Real.exp (T / 3) := by
      calc (1 + r / 2) ^ q ≤ Real.exp (r / 2) ^ q := by
            gcongr
            linarith [Real.add_one_le_exp (r / 2)]
        _ = Real.exp (q * (r / 2)) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp (T / 3) := Real.exp_le_exp.2 (by nlinarith)
    have h2 : Real.exp (T / 3) = Real.exp (1 / 3) ^ T := by rw [← Real.exp_nat_mul]; ring_nf
    have h3 : Real.exp (1 / 3) ^ T * (2 / 3 : ℝ) ^ T ≤ (14 / 15) ^ T := by
      rw [← mul_pow]
      gcongr
      nlinarith [exp_third_le, Real.exp_pos (1 / 3)]
    have h4 : (14 / 15 : ℝ) ^ T ≤ (14 / 15) ^ 4092 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h5 : (14 / 15 : ℝ) ^ 4092 ≤ (1 / 2) ^ 372 := by
      rw [show (4092 : ℕ) = 11 * 372 by norm_num, pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
    calc (1 + r / 2) ^ q * (2 / 3 : ℝ) ^ T ≤ Real.exp (T / 3) * (2 / 3) ^ T := by gcongr
      _ ≤ _ := by rw [h2]; exact h3.trans (h4.trans h5)
  unfold capC
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc (Fintype.card Cell : ℝ≥0∞) * ENNReal.ofReal ((1 + r / 2) ^ q * (2 / 3) ^ T)
      ≤ (2 ^ 46 : ℝ≥0∞) * ENNReal.ofReal ((1 / 2) ^ 372) := by
        gcongr
        exact_mod_cast card_cell_le
    _ = ENNReal.ofReal (2 ^ 46 * (1 / 2) ^ 372) := by
        rw [ENNReal.ofReal_mul (by norm_num), show ENNReal.ofReal ((2 : ℝ) ^ 46) = (2 : ℝ≥0∞) ^ 46 from by
          rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]]
    _ ≤ ENNReal.ofReal (1 / 2 ^ 180) := by
        apply ENNReal.ofReal_le_ofReal
        rw [one_div_pow, mul_one_div, show (2 : ℝ) ^ 372 = 2 ^ 46 * 2 ^ 326 by rw [← pow_add],
          div_mul_eq_div_div, div_self (by positivity)]
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by norm_num))

/-- **The coin forecast at the start.** -/
theorem coinPotK_le (T q : ℕ) (hab : 31 ≤ subtreeHeight + forsHeight)
    (hT : (T : ℝ) ≤ 3 * (q : ℝ) * (1 / (2 ^ subtreeHeight * 2 ^ forsHeight)) / 2 + 4097) :
    coinPotK T q ≤ ENNReal.ofReal (((q : ℝ) / 2 ^ 128) ^ 2 / 2 ^ 30 + ((q : ℝ) / 2 ^ 128) / 2 ^ 100) := by
  set r : ℝ := 1 / (2 ^ subtreeHeight * 2 ^ forsHeight) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr31 : r ≤ 1 / 2 ^ 31 := by
    rw [hr]
    apply one_div_le_one_div_of_le (by positivity)
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) hab
  have hch : ((Nat.choose q 2 : ℕ) : ℝ) ≤ (q : ℝ) ^ 2 / 2 := by
    rw [Nat.cast_choose_two]
    nlinarith [(Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
  unfold coinPotK
  rw [cinv_eq_ν, revRate_eq, ← hr]
  have hν : ν = ENNReal.ofReal (1 / 2 ^ 128) := by
    unfold ν
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one, one_div, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
  rw [hν, ← ENNReal.ofReal_mul (by norm_num), show (q : ℝ≥0∞) = ENNReal.ofReal q from (ENNReal.ofReal_natCast q).symm,
    show (T : ℝ≥0∞) = ENNReal.ofReal T from (ENNReal.ofReal_natCast T).symm,
    show ((Nat.choose q 2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (Nat.choose q 2 : ℕ) from (ENNReal.ofReal_natCast _).symm,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have key : (q : ℝ) * T + ((Nat.choose q 2 : ℕ) : ℝ) * r ≤ 2 * r * (q : ℝ) ^ 2 + 4097 * q := by
    nlinarith [mul_le_mul_of_nonneg_left hT hq0, mul_le_mul_of_nonneg_right hch hr0]
  have hx : 1 / 2 ^ 128 * (1 / 2 ^ 128) * (2 * r * (q : ℝ) ^ 2 + 4097 * q) ≤
      ((q : ℝ) / 2 ^ 128) ^ 2 / 2 ^ 30 + ((q : ℝ) / 2 ^ 128) / 2 ^ 100 := by
    have h1 : 1 / 2 ^ 128 * (1 / 2 ^ 128) * (2 * r * (q : ℝ) ^ 2) ≤ ((q : ℝ) / 2 ^ 128) ^ 2 / 2 ^ 30 := by
      have : 2 * r ≤ 1 / 2 ^ 30 := by linarith
      have hq2 : (0 : ℝ) ≤ (q : ℝ) ^ 2 := sq_nonneg _
      calc 1 / 2 ^ 128 * (1 / 2 ^ 128) * (2 * r * (q : ℝ) ^ 2) = (2 * r) * ((q : ℝ) / 2 ^ 128) ^ 2 := by ring
        _ ≤ (1 / 2 ^ 30) * ((q : ℝ) / 2 ^ 128) ^ 2 := by gcongr
        _ = _ := by ring
    have h2 : 1 / 2 ^ 128 * (1 / 2 ^ 128) * (4097 * (q : ℝ)) ≤ ((q : ℝ) / 2 ^ 128) / 2 ^ 100 := by
      have : (1 : ℝ) / 2 ^ 128 * 4097 ≤ 1 / 2 ^ 100 := by norm_num
      calc 1 / 2 ^ 128 * (1 / 2 ^ 128) * (4097 * (q : ℝ)) = (1 / 2 ^ 128 * 4097) * ((q : ℝ) / 2 ^ 128) := by ring
        _ ≤ (1 / 2 ^ 100) * ((q : ℝ) / 2 ^ 128) := by gcongr
        _ = _ := by ring
    nlinarith
  calc 1 / 2 ^ 128 * (1 / 2 ^ 128) * ((q : ℝ) * T + ((Nat.choose q 2 : ℕ) : ℝ) * r)
      ≤ 1 / 2 ^ 128 * (1 / 2 ^ 128) * (2 * r * (q : ℝ) ^ 2 + 4097 * q) := by gcongr
    _ ≤ _ := hx

end FORS.Security.SWRoute
