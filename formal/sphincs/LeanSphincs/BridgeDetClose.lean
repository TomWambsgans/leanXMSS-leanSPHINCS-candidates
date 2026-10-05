import LeanSphincs.BridgeArmSmall
import LeanSphincs.BridgeDetW

/-! The deterministic signer with both refinements of the small route (FORS-leaf payment of A4a, near
covers arming the linear potential) and the large route at the survival-weighted baseline. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
open HiddenBridge PotentialA

variable [Params]

set_option maxRecDepth 100000 in
/-- **127 bits for the deterministic signer, A4b armed**, from the small-route check `checkSmallA`
at `qh` and the large-route bound from `qh` on. -/
theorem det_bits (hb0 : 0 < subtreeHeight) (b N : ℕ) (hb : subtreeHeight = b) (hN : signatureLimit = N)
    (qh : ℕ) (ρ : ℚ) (t : H0.PoisTable) (o : H0.OptS) (hthr : H0.checkThreshS b N t o = true)
    (m : ℕ) (c : ℚ) (hnear : H0.checkNear b N qh m c = true)
    (hsmall : checkSmallA b N qh ρ o.cthr o.B (c / 2) = true)
    (hlarge : ∀ q' : ℕ, qh ≤ q' → 2 * q' ≤ 2 ^ 128 →
      (1 - budget 0 q') + (q' : ℝ≥0∞) * H0.hOfOW q' +
          ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
        ((q' + keygenCost : ℕ) : ℝ≥0∞) / 2 ^ 127) :
    Det.HasClassicalSecurityBitsDet 127 := by
  obtain ⟨hnum, hqh, hN70, hcthr, hB, hc, hpayR, hcheck⟩ := checkSmallA_sound hsmall
  have hN70' : signatureLimit ≤ 2 ^ 70 := hN ▸ hN70
  set κ : ℚ := 2 - ρ + (qh : ℚ) / 2 ^ 128 + (N : ℚ) / (2 ^ b * 2 ^ 10) with hκdef
  have hκR : (κ : ℝ) = 2 - (ρ : ℝ) + (qh : ℝ) / 2 ^ 128 + (N : ℝ) / (2 ^ b * 2 ^ 10) := by
    rw [hκdef]
    push_cast
    ring
  have hκ0 : 0 ≤ κ := by
    have hR : (0 : ℝ) ≤ (κ : ℝ) := by
      rw [hκR]
      have h1 : (ρ : ℝ) ≤ 2 := hnum.high
      have h2 : (0 : ℝ) ≤ (qh : ℝ) / 2 ^ 128 := by positivity
      have h3 : (0 : ℝ) ≤ (N : ℝ) / (2 ^ b * 2 ^ 10) := by positivity
      linarith
    exact_mod_cast hR
  have hκ1 : κ ≤ 1 := by
    have hR : (κ : ℝ) ≤ 1 := by
      rw [hκR]
      linarith
    exact_mod_cast hR
  have hc2 : (0 : ℚ) ≤ κ * (c / 2) := mul_nonneg hκ0 hc
  have hcheck' : (ρ : ℝ) + 2 ^ 128 * (o.B : ℝ) + (qh : ℝ) / ((2 ^ 128 - (qh + 2 ^ 32) : ℕ) : ℝ) +
      qh * ((κ * (c / 2) : ℚ) : ℝ) + 1 / 2 ^ 60 ≤ 2 := by
    rw [Rat.cast_mul, hκR]
    refine le_of_eq_of_le ?_ hcheck
    ring
  intro q hq1 adversary hbound
  by_cases hbig : 2 ^ 127 ≤ q
  · refine le_trans probEvent_le_one ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
    exact_mod_cast hbig
  have hq127 : q < 2 ^ 127 := Nat.lt_of_not_le hbig
  by_cases hs : q - keygenCost ≤ qh
  · have hq2 : 2 * (q - keygenCost) ≤ 2 ^ 128 := by omega
    have hx : ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 ≤ (qh : ℝ) / 2 ^ 128 :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr hs) (by positivity)
    have hnum' : Numeric (ρ : ℝ) (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128) :=
      numeric_mono hnum hx (by positivity)
    have hκq : 2 - (ρ : ℝ) + ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
        (signatureLimit : ℝ) * ((2 : ℝ) ^ subtreeHeight * 2 ^ 10)⁻¹ ≤ (κ : ℝ) := by
      rw [hκR, hb, hN, ← div_eq_mul_inv]
      linarith
    refine le_trans (det_smallA hb0 adversary q hbound (by omega) hq2 (ρ : ℝ) hnum' κ hκ0 hκ1 hκq b N hb hN t o
      hthr hcthr qh m c hnear hs) ?_
    exact small_closeF q qh hq1 hs hqh hN70' (ρ : ℝ) (by linarith [hnum.low]) o.B (κ * (c / 2)) hB hc2 hcheck'
  · have hK : keygenCost ≤ q := by omega
    have h := det_largeW hb0 hN70' adversary q hbound hq127 hK (hlarge (q - keygenCost) (by omega) (by omega))
    refine le_trans h (le_of_eq ?_)
    rw [Nat.cast_pow, Nat.cast_ofNat]

end LeanSphincs.Security.ForsPotential
