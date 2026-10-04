import LeanSphincs.BridgeSmallFinal
import LeanSphincs.BridgeRoutesLarge

/-! The deterministic signer at 127 bits from two certificates: the small-budget route up to `qh`
(linear potential, cover potential at baseline `ρ / 2^128`, FORS contact bounds) and the
large-budget route from `qh` on (one-coin split certificates). -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
open HiddenBridge PotentialA

variable [Params]

/-- The rational small-route check at the right end `qh` of the small budgets. -/
def checkSmall (b N qh : ℕ) (ρ cthr B c : ℚ) : Bool :=
  decide (3 / 2 ≤ ρ) && decide (ρ ≤ 2) &&
    decide (1 + 4032 * (2 - ρ) * ((qh : ℚ) / 2 ^ 128) ≤ ρ) && decide (1 + 66 * ((qh : ℚ) / 2 ^ 128) ≤ ρ) &&
    decide (64 * ((qh : ℚ) / 2 ^ 128) ≤ 1) && decide (qh ≤ 2 ^ 127) && decide (N ≤ 2 ^ 70) &&
    decide (cthr ≤ ρ / 2 ^ 128) && decide (0 ≤ B) && decide (0 ≤ c) &&
    decide (ρ + 2 ^ 128 * B + (N : ℚ) / (2 ^ b * 2 ^ 10) + (qh : ℚ) / ((2 ^ 128 - (qh + 2 ^ 32) : ℕ) : ℚ) +
      qh * c + 1 / 2 ^ 60 ≤ 2)

omit [Params] in
theorem checkSmall_sound {b N qh : ℕ} {ρ cthr B c : ℚ} (h : checkSmall b N qh ρ cthr B c = true) :
    Numeric (ρ : ℝ) ((qh : ℝ) / 2 ^ 128) ∧ qh ≤ 2 ^ 127 ∧ N ≤ 2 ^ 70 ∧ (cthr : ℝ) ≤ (ρ : ℝ) / 2 ^ 128 ∧
      0 ≤ B ∧ 0 ≤ c ∧
      (ρ : ℝ) + 2 ^ 128 * (B : ℝ) + (N : ℝ) * ((2 : ℝ) ^ b * 2 ^ 10)⁻¹ +
        (qh : ℝ) / ((2 ^ 128 - (qh + 2 ^ 32) : ℕ) : ℝ) + qh * (c : ℝ) + 1 / 2 ^ 60 ≤ 2 := by
  simp only [checkSmall, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  have r1 := (Rat.cast_le (K := ℝ)).mpr h1
  have r2 := (Rat.cast_le (K := ℝ)).mpr h2
  have r3 := (Rat.cast_le (K := ℝ)).mpr h3
  have r4 := (Rat.cast_le (K := ℝ)).mpr h4
  have r5 := (Rat.cast_le (K := ℝ)).mpr h5
  have r8 := (Rat.cast_le (K := ℝ)).mpr h8
  have r9 := (Rat.cast_le (K := ℝ)).mpr h11
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_sub, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_one] at r1 r2 r3 r4 r5 r8 r9
  refine ⟨⟨r1, r2, r3, r4, r5⟩, h6, h7, r8, h9, h10, ?_⟩
  rw [← div_eq_mul_inv]
  exact r9

set_option maxRecDepth 100000 in
/-- **127 bits for the deterministic signer** from the small-route check at `qh` and the
large-route bound from `qh` on. -/
theorem det_bits (hb0 : 0 < subtreeHeight) (b N : ℕ) (hb : subtreeHeight = b) (hN : signatureLimit = N)
    (qh : ℕ) (ρ : ℚ) (t : H0.PoisTable) (o : H0.OptS) (hthr : H0.checkThreshS b N t o = true)
    (m : ℕ) (c : ℚ) (hnear : H0.checkNear b N qh m c = true)
    (hsmall : checkSmall b N qh ρ o.cthr o.B (c / 2) = true)
    (hlarge : ∀ q' : ℕ, qh ≤ q' → 2 * q' ≤ 2 ^ 128 →
      (1 - budget 0 q') + (q' : ℝ≥0∞) * H0.hOfO q' +
          ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
        ((q' + keygenCost : ℕ) : ℝ≥0∞) / 2 ^ 127) :
    Det.HasClassicalSecurityBitsDet 127 := by
  obtain ⟨hnum, hqh, hN70, hcthr, hB, hc, hcheck⟩ := checkSmall_sound hsmall
  have hN70' : signatureLimit ≤ 2 ^ 70 := hN ▸ hN70
  intro q hq1 adversary hbound
  by_cases hbig : 2 ^ 127 ≤ q
  · refine le_trans probEvent_le_one ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
    exact_mod_cast hbig
  have hq127 : q < 2 ^ 127 := Nat.lt_of_not_le hbig
  by_cases hs : q - keygenCost ≤ qh
  · have hq2 : 2 * (q - keygenCost) ≤ 2 ^ 128 := by omega
    have hnum' : Numeric (ρ : ℝ) (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128) :=
      numeric_mono hnum (div_le_div_of_nonneg_right (Nat.cast_le.mpr hs) (by positivity)) (by positivity)
    refine le_trans (det_small hb0 adversary q hbound (by omega) hq2 (ρ : ℝ) hnum' b N hb hN t o hthr hcthr qh m c
      hnear hs) ?_
    refine small_close q qh hq1 hs hqh hN70' (ρ : ℝ) (by linarith [hnum.low]) o.B (c / 2) hB hc ?_
    rw [hb, hN]
    exact hcheck
  · have hK : keygenCost ≤ q := by omega
    have h := det_large hb0 hN70' adversary q hbound hq127 hK (hlarge (q - keygenCost) (by omega) (by omega))
    refine le_trans h (le_of_eq ?_)
    rw [Nat.cast_pow, Nat.cast_ofNat]

end LeanSphincs.Security.ForsPotential
