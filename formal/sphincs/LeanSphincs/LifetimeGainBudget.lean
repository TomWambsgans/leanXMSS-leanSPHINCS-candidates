import LeanSphincs.LifetimePriorMarginal

/-! Exact first-gain accounting. The independent marginal must be paid at the actual
history, not replaced by its value at an independent history. Its current-continuation
self-bound gives a harmonic occupation budget for any centered transition sequence. -/

namespace LeanSphincs.Lifetime

open ENNReal

/-- Algebraic telescoping of the exact actual-signer centered identity. The quantities may
already include conditional target forecasts and expectations over an adaptive prefix. -/
theorem centeredGain_telescope (potential independent actual : Nat → ℝ≥0∞) (n : Nat)
    (hstep : ∀ i < n, potential (i + 1) + independent i = potential i + actual i) :
    potential 0 + ∑ i ∈ Finset.range n, actual i =
      potential n + ∑ i ∈ Finset.range n, independent i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := ih (fun i hi => hstep i (by omega))
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    calc
      _ = (potential 0 + ∑ i ∈ Finset.range n, actual i) + actual n := by ac_rfl
      _ = (potential n + ∑ i ∈ Finset.range n, independent i) + actual n := by rw [hi]
      _ = (potential n + actual n) + ∑ i ∈ Finset.range n, independent i := by ac_rfl
      _ = (potential (n + 1) + independent n) + ∑ i ∈ Finset.range n, independent i := by
        rw [hstep n (by omega)]
      _ = _ := by ac_rfl

/-- This bounds the actual selected gains, including gains chosen from an adversarial cache.
Only the nonnegative initial potential is discarded. -/
theorem actualGainSum_le (potential independent actual : Nat → ℝ≥0∞) (n : Nat)
    (hstep : ∀ i < n, potential (i + 1) + independent i = potential i + actual i) :
    (∑ i ∈ Finset.range n, actual i) ≤
      potential n + ∑ i ∈ Finset.range n, independent i := by
  rw [← centeredGain_telescope potential independent actual n hstep]
  exact le_add_self

/-- The prior-dependent pivotal estimate yields the actual continuation's occupation
budget. No empty-history estimate is substituted for any of the `potential i` terms. -/
theorem actualGainSum_occupation_le (potential independent actual : Nat → ℝ≥0∞) (n : Nat)
    (hstep : ∀ i < n, potential (i + 1) + independent i = potential i + actual i)
    (hpivotal : ∀ i < n, ((n - i : Nat) : ℝ≥0∞) * independent i ≤ 24 * potential i) :
    (∑ i ∈ Finset.range n, actual i) ≤
      potential n + 24 * ∑ i ∈ Finset.range n, potential i / (n - i : Nat) := by
  refine (actualGainSum_le potential independent actual n hstep).trans (add_le_add le_rfl ?_)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hpos : n - i ≠ 0 := by omega
  have hp := (ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hpos)) (Or.inl (by simp))).2
    (show independent i * ((n - i : Nat) : ℝ≥0∞) ≤ 24 * potential i by
      simpa only [mul_comm] using hpivotal i hin)
  simpa only [div_eq_mul_inv, mul_assoc] using hp

/-- A uniform bound on the expected continuation values closes the occupation budget with
one harmonic factor. This is a supremum of the actual history's potentials, not an assumed
independent disclosure law. -/
theorem actualGainSum_harmonic_le (potential independent actual : Nat → ℝ≥0∞) (n : Nat)
    (hstep : ∀ i < n, potential (i + 1) + independent i = potential i + actual i)
    (hpivotal : ∀ i < n, ((n - i : Nat) : ℝ≥0∞) * independent i ≤ 24 * potential i)
    (bound : ℝ≥0∞) (hbound : ∀ i ≤ n, potential i ≤ bound) :
    (∑ i ∈ Finset.range n, actual i) ≤
      (1 + 24 * ∑ i ∈ Finset.range n, (((n - i : Nat) : ℝ≥0∞))⁻¹) * bound := by
  refine (actualGainSum_occupation_le potential independent actual n hstep hpivotal).trans ?_
  calc
    _ ≤ bound + 24 * ∑ i ∈ Finset.range n, bound / (n - i : Nat) := by
      apply add_le_add (hbound n le_rfl)
      apply mul_le_mul' le_rfl
      apply Finset.sum_le_sum
      intro i hi
      exact ENNReal.div_le_div_right (hbound i (Finset.mem_range.mp hi).le) _
    _ = _ := by
      simp only [div_eq_mul_inv, ← Finset.mul_sum]
      ring

end LeanSphincs.Lifetime
