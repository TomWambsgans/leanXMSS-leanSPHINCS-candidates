import LeanSphincs.BridgeVirtualOnce

/-! Coins of unequal probability. The expected potential `slotValue` is affine and monotone in the
probability of each coin: a coin whose probability is itself random, independent of the rest, is
worth the coin of its mean probability, and lowering a probability lowers the value. These are the
two facts a signer that scans `R0, R0 + 1, ...` needs: the selection probability of a cached value
is a martingale under further queries, not a constant. Nothing here depends on the scheme. -/

open ENNReal

namespace LeanSphincs.Security.Domination

variable {V : Type}

/-- A mixture of two probabilities for the same coin is the coin of the mixed probability. -/
theorem slotValue_mix (f : Multiset V → ℝ≥0∞) (p c1 c2 : ℝ≥0∞) (hp : p ≤ 1) (hc1 : c1 ≤ 1)
    (hc2 : c2 ≤ 1) (extra : Multiset V) (rest : List (ℝ≥0∞ × Multiset V)) (current : Multiset V) :
    p * slotValue f current ((c1, extra) :: rest) + (1 - p) * slotValue f current ((c2, extra) :: rest) =
      slotValue f current ((p * c1 + (1 - p) * c2, extra) :: rest) := by
  simp only [slotValue]
  have hsum : p * (1 - c1) + (1 - p) * (1 - c2) + (p * c1 + (1 - p) * c2) = 1 := by
    calc p * (1 - c1) + (1 - p) * (1 - c2) + (p * c1 + (1 - p) * c2)
        = p * (1 - c1 + c1) + (1 - p) * (1 - c2 + c2) := by ring
      _ = 1 := by rw [tsub_add_cancel_of_le hc1, tsub_add_cancel_of_le hc2, mul_one, mul_one,
          add_tsub_cancel_of_le hp]
  have hmix : p * c1 + (1 - p) * c2 ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc p * c1 + (1 - p) * c2
        ≤ p * (1 - c1) + (1 - p) * (1 - c2) + (p * c1 + (1 - p) * c2) := le_add_self
      _ = 1 := hsum
  have hone : 1 - (p * c1 + (1 - p) * c2) = p * (1 - c1) + (1 - p) * (1 - c2) :=
    (ENNReal.eq_sub_of_add_eq hmix hsum).symm
  rw [hone]
  ring

/-- Raising the probability of a coin raises the value of a monotone potential. -/
theorem slotValue_coin_mono (f : Multiset V → ℝ≥0∞) (hmono : Monotone' f) {c c' : ℝ≥0∞}
    (hc : c ≤ c') (hc' : c' ≤ 1) (extra : Multiset V) (rest : List (ℝ≥0∞ × Multiset V))
    (current : Multiset V) :
    slotValue f current ((c, extra) :: rest) ≤ slotValue f current ((c', extra) :: rest) := by
  simp only [slotValue]
  have hAB : slotValue f current rest ≤ slotValue f (current + extra) rest :=
    slotValue_mono f hmono rest _ _ (Multiset.le_add_right _ _)
  obtain ⟨e, rfl⟩ := exists_add_of_le hc
  have hct : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans le_self_add hc')
  have het : e ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans le_add_self hc')
  have hsplit : 1 - c = (1 - (c + e)) + e := by
    rw [← tsub_tsub, tsub_add_cancel_of_le]
    exact ENNReal.le_sub_of_add_le_left hct hc'
  rw [hsplit, add_mul, add_mul]
  calc c * slotValue f (current + extra) rest +
        ((1 - (c + e)) * slotValue f current rest + e * slotValue f current rest)
      ≤ c * slotValue f (current + extra) rest +
        ((1 - (c + e)) * slotValue f current rest + e * slotValue f (current + extra) rest) := by
        gcongr
    _ = _ := by ring

/-- A coin of probability zero changes nothing. -/
theorem slotValue_zero_coin (f : Multiset V → ℝ≥0∞) (extra : Multiset V)
    (rest : List (ℝ≥0∞ × Multiset V)) (current : Multiset V) :
    slotValue f current ((0, extra) :: rest) = slotValue f current rest := by
  simp only [slotValue, zero_mul, zero_add, tsub_zero, one_mul]

end LeanSphincs.Security.Domination
