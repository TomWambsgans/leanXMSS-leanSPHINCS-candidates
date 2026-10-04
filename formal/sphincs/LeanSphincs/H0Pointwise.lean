import LeanSphincs.H0Product
import SphincsSecurity.Proof.Base.BinomialMoments

/-! The moment bound of the excess, the product-form majorant, and the falling-factorial
expansion of the per-leaf factor `(1 + c k^24)^R`. -/

open ENNReal

namespace LeanSphincs.Security.H0

set_option linter.unusedSectionVars false

/-- Moment bound for the positive part, real form: `z - β ≤ c_R z^R / β^(R-1)`. -/
theorem excess_le_moment_real (z β : ℝ) (hz : 0 ≤ z) (hβ : 0 < β) (R : ℕ) (hR : 2 ≤ R) :
    z - β ≤ ((R - 1 : ℝ) ^ (R - 1) / (R : ℝ) ^ R) * z ^ R / β ^ (R - 1) := by
  have hR1 : (0 : ℝ) < R - 1 := by
    have : (2 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have hRpos : (0 : ℝ) < R := by linarith
  have hz' : z = (z / β) * β := by field_simp
  have hu0 : 0 ≤ z / β := div_nonneg hz hβ.le
  generalize hu : z / β = u at hz' hu0
  subst hz'
  -- Bernoulli at x = u (R-1)/R - 1
  have hb := one_add_mul_le_pow (a := u * (R - 1) / R - 1) (by
    have : 0 ≤ u * (R - 1) / R := div_nonneg (mul_nonneg hu0 hR1.le) hRpos.le
    linarith) R
  have hlin : 1 + (R : ℝ) * (u * (R - 1) / R - 1) = (R - 1) * (u - 1) := by
    field_simp; ring
  have hpow : (1 + (u * (R - 1) / R - 1)) ^ R = u ^ R * ((R - 1) ^ R / (R : ℝ) ^ R) := by
    rw [show 1 + (u * (R - 1) / R - 1) = u * ((R - 1) / R) by ring, mul_pow, div_pow]
  rw [hlin, hpow] at hb
  -- divide by R - 1
  have hkey : u - 1 ≤ u ^ R * ((R - 1 : ℝ) ^ (R - 1) / (R : ℝ) ^ R) := by
    have hsplit : (R - 1 : ℝ) ^ R = (R - 1) * (R - 1) ^ (R - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hsplit] at hb
    have : (R - 1 : ℝ) * (u - 1) ≤ (R - 1) * (u ^ R * ((R - 1) ^ (R - 1) / (R : ℝ) ^ R)) := by
      calc (R - 1 : ℝ) * (u - 1) ≤ u ^ R * ((R - 1) * (R - 1) ^ (R - 1) / (R : ℝ) ^ R) := hb
        _ = (R - 1) * (u ^ R * ((R - 1) ^ (R - 1) / (R : ℝ) ^ R)) := by ring
    exact le_of_mul_le_mul_left this hR1
  -- multiply back by β
  have hβpow : β ^ R = β * β ^ (R - 1) := by rw [← pow_succ']; congr 1; omega
  calc u * β - β = β * (u - 1) := by ring
    _ ≤ β * (u ^ R * ((R - 1 : ℝ) ^ (R - 1) / (R : ℝ) ^ R)) := by gcongr
    _ = ((R - 1 : ℝ) ^ (R - 1) / (R : ℝ) ^ R) * (u * β) ^ R / β ^ (R - 1) := by
        rw [mul_pow, hβpow]
        field_simp

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- `1 + Σ x ≤ Π (1 + x)`. -/
theorem one_add_sum_le_prod (x : ι → ℝ≥0∞) : 1 + ∑ l, x l ≤ ∏ l, (1 + x l) := by
  have h := prod_add_ge Finset.univ (fun _ => (1 : ℝ≥0∞)) x
  simpa using h

/-- ENNReal form of the moment bound: `z ≤ β + c_R z^R / β^(R-1)`. -/
theorem excess_le_moment (z β : ℝ≥0∞) (hz : z ≠ ⊤) (hβ0 : β ≠ 0) (hβ : β ≠ ⊤) (R : ℕ) (hR : 2 ≤ R) :
    z ≤ β + ENNReal.ofReal ((R - 1 : ℝ) ^ (R - 1) / (R : ℝ) ^ R) * z ^ R / β ^ (R - 1) := by
  have hreal := excess_le_moment_real z.toReal β.toReal ENNReal.toReal_nonneg
    (ENNReal.toReal_pos hβ0 hβ) R hR
  have hcR : 0 ≤ (R - 1 : ℝ) ^ (R - 1) / (R : ℝ) ^ R := by
    have : (0 : ℝ) ≤ R - 1 := by
      have : (2 : ℝ) ≤ R := by exact_mod_cast hR
      linarith
    positivity
  have hβpos : 0 < β.toReal ^ (R - 1) := pow_pos (ENNReal.toReal_pos hβ0 hβ) _
  calc z = ENNReal.ofReal z.toReal := (ENNReal.ofReal_toReal hz).symm
    _ ≤ ENNReal.ofReal (β.toReal + ((R - 1 : ℝ) ^ (R - 1) / (R : ℝ) ^ R) * z.toReal ^ R / β.toReal ^ (R - 1)) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ = _ := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity), ENNReal.ofReal_toReal hβ,
          ENNReal.ofReal_div_of_pos hβpos, ENNReal.ofReal_mul hcR,
          ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hz, ENNReal.ofReal_toReal hβ]

/-- The moment constant `c_R = (R-1)^(R-1) / R^R` (with `c_1 = 1`). -/
noncomputable def cMom (R : ℕ) : ℝ≥0∞ := ENNReal.ofReal (((R - 1 : ℕ) : ℝ) ^ (R - 1) / (R : ℝ) ^ R)

theorem cMom_ne_top (R : ℕ) : cMom R ≠ ⊤ := ENNReal.ofReal_ne_top

/-- The moment bound for every `R ≥ 1`: `z ≤ β + c_R z^R / β^(R-1)`; for `R ≥ 2` it needs `β ≠ 0`. -/
theorem excess_le_cMom (z β : ℝ≥0∞) (hz : z ≠ ⊤) (hβ : β ≠ ⊤) (R : ℕ) (hR : 1 ≤ R)
    (hβ0 : R = 1 ∨ β ≠ 0) : z ≤ β + cMom R * z ^ R / β ^ (R - 1) := by
  rcases Nat.lt_or_ge R 2 with h1 | h2
  · have hR1 : R = 1 := by omega
    subst hR1
    simp [cMom]
  · have hβ0' : β ≠ 0 := hβ0.resolve_left (by omega)
    have h := excess_le_moment z β hz hβ0' hβ R h2
    have hc : ENNReal.ofReal ((R - 1 : ℝ) ^ (R - 1) / (R : ℝ) ^ R) = cMom R := by
      unfold cMom
      congr 3
      push_cast [Nat.cast_sub (by omega : 1 ≤ R)]
      ring
    rwa [hc] at h

/-- Cancelling the scale `t`: `c z^R / β^(R-1) = c / (t^R β^(R-1)) · (t z)^R`. -/
theorem scale_cancel (c z β t : ℝ≥0∞) (R : ℕ) (ht0 : t ≠ 0) (ht : t ≠ ⊤) :
    c * z ^ R / β ^ (R - 1) = c / (t ^ R * β ^ (R - 1)) * (t * z) ^ R := by
  have htR : t ^ R ≠ 0 := pow_ne_zero _ ht0
  have htR' : t ^ R ≠ ⊤ := pow_ne_top ht
  rw [mul_pow, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl htR) (Or.inl htR')]
  calc (β ^ (R - 1))⁻¹ * (c * z ^ R) = ((t ^ R)⁻¹ * t ^ R) * ((β ^ (R - 1))⁻¹ * (c * z ^ R)) := by
        rw [ENNReal.inv_mul_cancel htR htR', one_mul]
    _ = _ := by ring

/-- `(t Σ Y)^R ≤ Π (1 + t Y)^R - 1`, additively. -/
theorem pow_sum_le_prod (Y : ι → ℝ≥0∞) (t : ℝ≥0∞) (R : ℕ) (hR : R ≠ 0) :
    1 + (t * ∑ l, Y l) ^ R ≤ ∏ l, (1 + t * Y l) ^ R := by
  rw [Finset.prod_pow]
  calc 1 + (t * ∑ l, Y l) ^ R = 1 ^ R + (t * ∑ l, Y l) ^ R := by rw [one_pow]
    _ ≤ (1 + t * ∑ l, Y l) ^ R := pow_add_pow_le (by positivity) (by positivity) hR
    _ ≤ (∏ l, (1 + t * Y l)) ^ R := by
        gcongr
        rw [Finset.mul_sum]
        exact one_add_sum_le_prod _

/-- **Falling-factorial expansion of the per-leaf factor.** -/
theorem leaf_expand (R : ℕ) (c : ℝ≥0∞) (k : ℕ) :
    (1 + c * (k : ℝ≥0∞) ^ 24) ^ R =
      ∑ p ∈ Finset.range (R + 1) ×ˢ Finset.range (24 * R + 1),
        ((R.choose p.1 : ℝ≥0∞) * c ^ p.1 * (Nat.stirlingSecond (24 * p.1) p.2 : ℝ≥0∞)) *
          (k.descFactorial p.2 : ℝ≥0∞) := by
  rw [add_comm, add_pow, Finset.sum_product]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsR : s ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  rw [one_pow, mul_one, mul_pow, ← pow_mul]
  have hst : (k : ℝ≥0∞) ^ (24 * s) = ∑ j ∈ Finset.range (24 * R + 1),
      (Nat.stirlingSecond (24 * s) j : ℝ≥0∞) * (k.descFactorial j : ℝ≥0∞) := by
    have h := SphincsSecurity.Concrete.power_eq_stirling_descFactorial k (24 * s)
    have hsub : Finset.range (24 * s + 1) ⊆ Finset.range (24 * R + 1) :=
      Finset.range_subset_range.mpr (by omega)
    rw [← Finset.sum_subset hsub (fun j _ hj => by
      rw [Finset.mem_range, not_lt] at hj
      simp [Nat.stirlingSecond_eq_zero_of_lt (by omega : 24 * s < j)])]
    exact_mod_cast h
  rw [hst, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- Its Poisson mean, in Touchard form. -/
theorem leaf_pois (R : ℕ) (c μ : ℝ≥0∞) :
    ∑ p ∈ Finset.range (R + 1) ×ˢ Finset.range (24 * R + 1),
        ((R.choose p.1 : ℝ≥0∞) * c ^ p.1 * (Nat.stirlingSecond (24 * p.1) p.2 : ℝ≥0∞)) * μ ^ p.2 =
      ∑ s ∈ Finset.range (R + 1), (R.choose s : ℝ≥0∞) * c ^ s *
        ∑ j ∈ Finset.range (24 * s + 1), (Nat.stirlingSecond (24 * s) j : ℝ≥0∞) * μ ^ j := by
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hsR : s ≤ R := Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
  have hsub : Finset.range (24 * s + 1) ⊆ Finset.range (24 * R + 1) :=
    Finset.range_subset_range.mpr (by omega)
  rw [← Finset.sum_subset hsub (fun j _ hj => by
      rw [Finset.mem_range, not_lt] at hj
      simp [Nat.stirlingSecond_eq_zero_of_lt (by omega : 24 * s < j)]), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

end LeanSphincs.Security.H0
