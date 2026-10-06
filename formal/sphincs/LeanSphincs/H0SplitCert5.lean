import LeanSphincs.H0SplitCert
import LeanSphincs.H0Bound5

/-! The closing lemmas of `H0SplitCert` for the coin `wbar5` of the signer that tries
`R0, R0 + 1, ...`. The table check is the one of `H0SplitCert` (`checkTable`, unchanged): it asks
for `N / 2^b + 2^127 / ((2^127 - 2^32) 2^b) ≤ μ`, and for `q ≤ 2^127` the rate of the new coin is
`q · landing · wbar5 = q (2 - landing) / 2^128 ≤ 1 ≤ 2^127 / (2^127 - 2^32)`, so the certificates
of the large route stay valid unchanged. -/

open ENNReal NNReal

namespace LeanSphincs.Security.H0

open Concrete Domination ForsPrice

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 512

section Fors

variable [Params]

/-- The selection mass of one digest query: `landing * wbar5 = (2 - landing) / 2^128`. -/
theorem landing_mul_wbar5_toReal :
    (landing * wbar5).toReal = (2 - 1 / 2 ^ (26 - subtreeHeight)) / 2 ^ 128 := by
  have h1 : (1 : ℝ) / 2 ^ (26 - subtreeHeight) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  rw [mul_comm, wbar5_mul_landing, rate5_eq, ENNReal.toReal_ofReal (div_nonneg (by linarith) (by positivity))]

/-- The one-coin rate of the FORS H-term with the coin `wbar5` is below the table rate for every
budget `q ≤ 2^127`. -/
theorem rate_le_table5 (b N : ℕ) (t : PoisTable) (ht : checkTable b N t = true) (hN : signatureLimit = N) (q : ℕ)
    (hq : q ≤ 2 ^ 127) :
    (signatureLimit : ℝ) / 2 ^ b + (q : ℝ) * (landing * wbar5).toReal / 2 ^ b ≤ (t.mu : ℝ) := by
  obtain ⟨-, h2, -⟩ := checkTable_parts ht
  have h2' : (((N : ℚ) / 2 ^ b + 2 ^ 127 / ((2 ^ 127 - 2 ^ 32) * 2 ^ b) : ℚ) : ℝ) ≤ (t.mu : ℝ) := by
    exact_mod_cast h2
  push_cast at h2'
  rw [landing_mul_wbar5_toReal, hN]
  have hq' : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hl0 : (0 : ℝ) ≤ 1 / 2 ^ (26 - subtreeHeight) := by positivity
  have hqD : (q : ℝ) * ((2 - 1 / 2 ^ (26 - subtreeHeight)) / 2 ^ 128) ≤ 2 ^ 127 / (2 ^ 127 - 2 ^ 32) := by
    have h1 : (q : ℝ) * ((2 - 1 / 2 ^ (26 - subtreeHeight)) / 2 ^ 128) ≤ 1 := by
      rw [← mul_div_assoc, div_le_one (by positivity)]
      nlinarith
    refine le_trans h1 ?_
    rw [le_div_iff₀ (by norm_num)]
    norm_num
  have h2b : (0 : ℝ) < 2 ^ b := by positivity
  calc (N : ℝ) / 2 ^ b + (q : ℝ) * ((2 - 1 / 2 ^ (26 - subtreeHeight)) / 2 ^ 128) / 2 ^ b
      ≤ (N : ℝ) / 2 ^ b + 2 ^ 127 / (2 ^ 127 - 2 ^ 32) / 2 ^ b := by gcongr
    _ = (N : ℝ) / 2 ^ b + 2 ^ 127 / ((2 ^ 127 - 2 ^ 32) * 2 ^ b) := by rw [div_div]
    _ ≤ _ := h2'

/-- **General threshold, coin `wbar5`.** A checked table and option bound the one-coin FORS H-term
at every budget `q ≤ 2^127` and every finite threshold `β ≥ cthr`: `H ≤ B`. -/
theorem hTermO_fors_le_opt5 (b N : ℕ) (t : PoisTable) (o : OptS) (ht : checkTable b N t = true)
    (ho : checkOpt b t o = true) (hb : subtreeHeight = b) (hN : signatureLimit = N) (q : ℕ)
    (hq : 2 * q ≤ 2 ^ 128) (β : ℝ≥0∞) (hβ : β ≠ ⊤) (hβc : ENNReal.ofReal (o.cthr : ℝ) ≤ β) :
    hTermO (Finset.univ : Finset View) wbar5 landing signatureLimit q
        (fun d => countPrice (Prod.fst : View → Fin (2 ^ subtreeHeight)) kappa d - β) ≤
      ENNReal.ofReal (o.B : ℝ) := by
  have hq127 : q ≤ 2 ^ 127 := by
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    omega
  exact hTermO_le_opt (Prod.fst : View → Fin (2 ^ subtreeHeight)) Finset.univ uniformIndex_univ b N
    (by rw [Fintype.card_fin, hb]) t o ht ho kappa rfl wbar5 landing wbar5_le_one
    ForsPotential.landing_le_one signatureLimit q (rate_le_table5 b N t ht hN q hq127) β hβ hβc

/-- **General threshold, coin `wbar5`**, from one Bool check: for a rational threshold `cthr` (any
finite `β ≥ cthr`), the one-coin FORS H-term at every budget `q ≤ 2^127` is at most `B`. -/
theorem hTermO_fors_le_of_check5 (b N : ℕ) (t : PoisTable) (o : OptS) (hc : checkThreshS b N t o = true)
    (hb : subtreeHeight = b) (hN : signatureLimit = N) (q : ℕ) (hq : 2 * q ≤ 2 ^ 128) (β : ℝ≥0∞)
    (hβ : β ≠ ⊤) (hβc : ENNReal.ofReal (o.cthr : ℝ) ≤ β) :
    hTermO (Finset.univ : Finset View) wbar5 landing signatureLimit q
        (fun d => countPrice (Prod.fst : View → Fin (2 ^ subtreeHeight)) kappa d - β) ≤
      ENNReal.ofReal (o.B : ℝ) := by
  simp only [checkThreshS, Bool.and_eq_true] at hc
  exact hTermO_fors_le_opt5 b N t o hc.1 hc.2 hb hN q hq β hβ hβc

end Fors

end LeanSphincs.Security.H0
