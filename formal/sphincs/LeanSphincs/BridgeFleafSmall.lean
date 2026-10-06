import LeanSphincs.BridgeFleafA4a
import LeanSphincs.BridgeSmallFinal
import LeanSphincs.BridgeRoutes
import LeanSphincs.BridgeForsAssemblyOnce
import LeanSphincs.BridgeDet
import LeanSphincs.H0BoundOnce
import LeanSphincs.H0Bound5

/-! The small-budget bound in closed form when the signature part of the FORS contact bound A4a is
paid by the linear potential: every FORS leaf query leaves `(ρ - 1 - x) 2^-128` of the linear
potential unused, so once `N 2^-b 2^-10 ≤ ρ - 1 - x` the term `x N 2^-b 2^-10` leaves the bound. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
open HiddenBridge PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

open Completeness SeedModel Graph Assembly Reduce Internalize in
attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

omit [Params] in
theorem digestCount_cons_inr {D R ι : Type} (tg : Targeting D R ι) (amount : ℕ) (entries : List (Entry D)) :
    digestCount tg (.inr amount :: entries) = digestCount tg entries := by
  simp [digestCount]

/-! ### The main term -/

/-- The sample-independent part of the small-budget bound, A4a paid per FORS leaf query. The coin
part of A4a is `2^-128 C(y, 2) rate5`, `y = q - keygenCost`. -/
noncomputable def smallMainF (ρ : ℝ) (q : ℕ) (B c : ℚ) : ℝ≥0∞ :=
  ENNReal.ofReal (ρ * (q - keygenCost : ℕ) / 2 ^ 128) + ((q - keygenCost : ℕ) : ℝ≥0∞) * ENNReal.ofReal (B : ℝ) +
    contactRate * (((q - keygenCost).choose 2 : ℕ) * rate5) +
    (((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) * ((q - keygenCost : ℕ) * ENNReal.ofReal (c : ℝ))

/-- The coin part of A4a in real form: `C(x, 2) ≤ x^2 / 2` and
`rate5 = (2 - 2^-(26 - b)) / 2^128`. -/
theorem coin5_le (x : ℕ) :
    contactRate * ((x.choose 2 : ℕ) * rate5) ≤
      ENNReal.ofReal ((x : ℝ) * (2 ^ 128)⁻¹ *
        ((x : ℝ) * (2 ^ 129 / (2 - 1 / 2 ^ (26 - subtreeHeight)))⁻¹)) := by
  have ht1 : (1 : ℝ) / 2 ^ (26 - subtreeHeight) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hC : ((x.choose 2 : ℕ) : ℝ) * 2 ≤ x * x := by
    have h : x.choose 2 * 2 ≤ x * x := by
      rw [Nat.choose_two_right]
      exact le_trans (Nat.div_mul_le_self _ _) (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
    exact_mod_cast h
  set t : ℝ := 2 - 1 / 2 ^ (26 - subtreeHeight) with ht
  have ht0 : 0 ≤ t := by rw [ht]; linarith
  have hr0 : (0 : ℝ) ≤ t / 2 ^ 128 := div_nonneg ht0 (by positivity)
  rw [contactRate_eq, H0.rate5_eq, ← ht, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [inv_div]
  have e1 : ((2 : ℝ) ^ 128)⁻¹ * (((x.choose 2 : ℕ) : ℝ) * (t / 2 ^ 128)) =
      (((x.choose 2 : ℕ) : ℝ) * 2) * (t * (((2 : ℝ) ^ 128)⁻¹ * (2 ^ 129)⁻¹)) := by
    field_simp
  have e2 : (x : ℝ) * ((2 : ℝ) ^ 128)⁻¹ * ((x : ℝ) * (t / 2 ^ 129)) =
      ((x : ℝ) * x) * (t * (((2 : ℝ) ^ 128)⁻¹ * (2 ^ 129)⁻¹)) := by
    field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right hC (mul_nonneg ht0 (by positivity))

/-! ### The closed form -/

omit [Params] in
/-- The real inequality behind the closed form, without the signature part of A4a. -/
theorem small_realF (x qh q N ρ B c Dx Dh : ℝ) (hx0 : 0 ≤ x) (hxq : x ≤ qh) (hqh : qh ≤ 2 ^ 127)
    (hq : x + 1 ≤ q) (hN0 : 0 ≤ N) (hN : N ≤ 2 ^ 70) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hDh : 0 < Dh) (hD : Dh ≤ Dx)
    (hcheck : ρ + 2 ^ 128 * B + qh / Dh + qh * c + 1 / 2 ^ 60 ≤ 2) :
    ρ * x / 2 ^ 128 + x * B + x * (2 ^ 128)⁻¹ * (x * Dx⁻¹) + x * (2 ^ 128)⁻¹ * (x * c) +
        ((x + N) + x * (2 ^ 128)⁻¹ * (x + N)) * (1 / 2) ^ 201 + 2 * (q / 2 ^ 256) ≤ q / 2 ^ 127 := by
  have h := small_real x qh q N ρ B c Dx Dh 0 hx0 hxq hqh hq hN0 hN hB hc le_rfl hDh hD
    (by rw [mul_zero, add_zero]; exact hcheck)
  simpa only [mul_zero, zero_add] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **The small-budget bound in closed form, A4a paid per FORS leaf query.** The coin part of A4a
enters as `qh (2 - 2^-(26 - b)) / 2^129`. -/
theorem small_closeF (q qh : ℕ) (hq1 : 1 ≤ q) (hq' : q - keygenCost ≤ qh) (hqh : qh ≤ 2 ^ 127)
    (hN : signatureLimit ≤ 2 ^ 70) (ρ : ℝ) (hρ : 0 ≤ ρ) (B c : ℚ) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hcheck : ρ + 2 ^ 128 * (B : ℝ) + (qh : ℝ) * (2 - 1 / 2 ^ (26 - subtreeHeight)) / 2 ^ 129 + qh * (c : ℝ) +
        1 / 2 ^ 60 ≤ 2) :
    smallMainF ρ q B c + smallFail q * (2 : ℝ≥0∞)⁻¹ ^ 201 + 2 * ((q : ℝ≥0∞) / 2 ^ 256) ≤
      (q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) := by
  set q' := q - keygenCost with hq'def
  have hK : 1 ≤ keygenCost := one_le_keygenCost
  have hq'1 : q' + 1 ≤ q := by omega
  have hB' : (0 : ℝ) ≤ B := by exact_mod_cast hB
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  have r1 : (q' : ℝ) ≤ qh := Nat.cast_le.mpr hq'
  have r2 : (qh : ℝ) ≤ 2 ^ 127 := by
    have h := (Nat.cast_le (α := ℝ)).mpr hqh
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  have r3 : (q' : ℝ) + 1 ≤ q := by
    have h := (Nat.cast_le (α := ℝ)).mpr hq'1
    rwa [Nat.cast_add, Nat.cast_one] at h
  have r4 : (signatureLimit : ℝ) ≤ 2 ^ 70 := by
    have h := (Nat.cast_le (α := ℝ)).mpr hN
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  have ht1 : (1 : ℝ) / 2 ^ (26 - subtreeHeight) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  have hcoin := coin5_le q'
  set D : ℝ := 2 ^ 129 / (2 - 1 / 2 ^ (26 - subtreeHeight)) with hDdef
  have r5 : 0 < D := div_pos (by positivity) (by linarith)
  have hcheck' : ρ + 2 ^ 128 * (B : ℝ) + (qh : ℝ) / D + qh * (c : ℝ) + 1 / 2 ^ 60 ≤ 2 := by
    rw [hDdef, div_div_eq_mul_div]
    exact hcheck
  have hreal := small_realF (q' : ℝ) qh q signatureLimit ρ B c D D (Nat.cast_nonneg _)
    r1 r2 r3 (Nat.cast_nonneg _) r4 hB' hc' r5 le_rfl hcheck'
  obtain ⟨Di, hDi⟩ : ∃ Di : NNReal, (Di : ℝ) = D⁻¹ := ⟨⟨D⁻¹, inv_nonneg.2 r5.le⟩, rfl⟩
  rw [← hDi] at hreal hcoin
  have hnat : ∀ n : ℕ, (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := fun n => (ENNReal.ofReal_natCast n).symm
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by rw [ENNReal.ofReal_ofNat]
  have hhalf : (2 : ℝ≥0∞)⁻¹ ^ 201 = ENNReal.ofReal ((1 / 2) ^ 201) := by
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  have hq256 : (q : ℝ≥0∞) / 2 ^ 256 = ENNReal.ofReal (q / 2 ^ 256) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_natCast]
  have hq127 : (q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (q / 2 ^ 127) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
    push_cast
    norm_num
  unfold smallMainF smallFail
  rw [← hq'def]
  refine le_trans (add_le_add (add_le_add (add_le_add (add_le_add le_rfl hcoin) le_rfl) le_rfl) le_rfl) ?_
  rw [hhalf, hq256, hq127, contactRate_eq, hnat q', hnat signatureLimit, h2]
  simp (disch := positivity) only [← ENNReal.ofReal_add, ← ENNReal.ofReal_mul]
  exact ENNReal.ofReal_le_ofReal hreal

end LeanSphincs.Security.ForsPotential
