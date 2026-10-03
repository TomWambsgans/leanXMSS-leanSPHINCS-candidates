import LeanSphincs.LifetimePoolConcentration
import LeanSphincs.Landing

/-! Balanced full randomizer pools give a near-uniform accepted index law for every choice
of message. The denominator retains the actual pool's landing density. -/

namespace LeanSphincs.Lifetime
open Finset

attribute [local irreducible] poolCount

theorem PoolBalanced.count_lower {pool : IndexPool} (h : PoolBalanced pool) (index : Index) :
    (2 : ℝ) ^ 102 - (2 : ℝ) ^ 82 ≤ (poolCount index pool : ℝ) := by
  have hindex := h index
  have hl := (abs_lt.mp hindex).1
  linarith

theorem PoolBalanced.count_upper {pool : IndexPool} (h : PoolBalanced pool) (index : Index) :
    (poolCount index pool : ℝ) ≤ (2 : ℝ) ^ 102 + (2 : ℝ) ^ 82 := by
  have hindex := h index
  have hu := (abs_lt.mp hindex).2
  linarith

variable [Params]

def poolAcceptedCount (parameter : PublicParameter) (pool : IndexPool) : Nat :=
  ∑ index ∈ (Finset.univ.filter (Landed parameter)), poolCount index pool

theorem PoolBalanced.accepted_lower {pool : IndexPool} (h : PoolBalanced pool)
    (parameter : PublicParameter) :
    ((2 ^ subtreeHeight : Nat) : ℝ) * ((2 : ℝ) ^ 102 - (2 : ℝ) ^ 82) ≤
      (poolAcceptedCount parameter pool : ℝ) := by
  rw [poolAcceptedCount, Nat.cast_sum]
  have hh := Finset.sum_le_sum (s := Finset.univ.filter (Landed parameter))
    (fun index _ => h.count_lower index)
  simpa only [Finset.sum_const, landed_card, nsmul_eq_mul] using hh

theorem PoolBalanced.accepted_positive {pool : IndexPool} (h : PoolBalanced pool)
    (parameter : PublicParameter) : 0 < (poolAcceptedCount parameter pool : ℝ) := by
  exact lt_of_lt_of_le (mul_pos (by positivity) (by norm_num)) (h.accepted_lower parameter)

/-- Keeping both numerator and landing denominator yields a relative inflation below2^-18;
the coarse cached-source density factor `1+q/2^128` is absent. -/
theorem PoolBalanced.accepted_index_ratio {pool : IndexPool} (h : PoolBalanced pool)
    (parameter : PublicParameter) (index : Index) :
    (poolCount index pool : ℝ) / poolAcceptedCount parameter pool ≤
      (1 + (1 : ℝ) / 2 ^ 18) / ((2 ^ subtreeHeight : Nat) : ℝ) := by
  have hn := h.count_upper index
  have hd := h.accepted_lower parameter
  have hp := h.accepted_positive parameter
  have hm : (0 : ℝ) < ((2 ^ subtreeHeight : Nat) : ℝ) := by positivity
  apply (div_le_div_iff₀ hp hm).mpr
  have hfactor : (1 + (1 : ℝ) / 2 ^ 18) * ((2 : ℝ) ^ 102 - (2 : ℝ) ^ 82) ≥
      (2 : ℝ) ^ 102 + (2 : ℝ) ^ 82 := by norm_num
  calc
    (poolCount index pool : ℝ) * ((2 ^ subtreeHeight : Nat) : ℝ) ≤
        ((2 : ℝ) ^ 102 + (2 : ℝ) ^ 82) * ((2 ^ subtreeHeight : Nat) : ℝ) :=
      mul_le_mul_of_nonneg_right hn hm.le
    _ ≤ ((1 + (1 : ℝ) / 2 ^ 18) * ((2 : ℝ) ^ 102 - (2 : ℝ) ^ 82)) *
        ((2 ^ subtreeHeight : Nat) : ℝ) := mul_le_mul_of_nonneg_right hfactor hm.le
    _ = (1 + (1 : ℝ) / 2 ^ 18) *
        (((2 ^ subtreeHeight : Nat) : ℝ) * ((2 : ℝ) ^ 102 - (2 : ℝ) ^ 82)) := by ring
    _ ≤ (1 + (1 : ℝ) / 2 ^ 18) * (poolAcceptedCount parameter pool : ℝ) :=
      mul_le_mul_of_nonneg_left hd (by positivity)

end LeanSphincs.Lifetime
