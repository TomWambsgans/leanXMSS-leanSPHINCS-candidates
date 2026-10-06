import LeanSphincs.BridgeStateFn

/-! Helpers for the contact modules under the signer that tries `R0, R0 + 1, ...`: the card
function, whose group value `grpM m s (fun _ => False) cardFn 0` is the selection mass of the known
landed randomizers of a message (it replaces "`wbar` times the number of cached landed pairs of the
message" of the per-attempt signer), and the pool part of a signing call for weights at most one. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] digestAttemptLimit

variable [Params]

/-- The number of disclosed views. -/
noncomputable def cardFn : Multiset View → ℝ≥0∞ := fun D => (Multiset.card D : ℝ≥0∞)

theorem cardFn_mono : Monotone' cardFn := fun _ _ hle => Nat.cast_le.mpr (Multiset.card_le_card hle)

theorem cardFn_super : Supermodular cardFn := fun small large extra _ => by
  unfold cardFn
  rw [Multiset.card_add, Multiset.card_add]
  push_cast
  exact le_of_eq (by ring)

theorem cardFn_ne_top : ∀ D, cardFn D ≠ ⊤ := fun _ => ENNReal.natCast_ne_top _

theorem cardFn_props : Monotone' cardFn ∧ Supermodular cardFn ∧ ∀ D, cardFn D ≠ ⊤ :=
  ⟨cardFn_mono, cardFn_super, cardFn_ne_top⟩

theorem cardFn_zero : cardFn 0 = 0 := by simp [cardFn]

theorem gain_cardFn (d : Multiset View) (v : View) : gain cardFn d v = 1 := by
  unfold gain cardFn
  rw [Multiset.card_add, Multiset.card_singleton]
  push_cast
  exact ENNReal.add_sub_cancel_left (ENNReal.natCast_ne_top _)

/-- **The pool mass of a message.** The mean walk value of a pool weight that is at most one (and
no fresh weight) is at most the group of the message on the card function. -/
theorem pool_walk_le_grpM (parameter : PublicParameter) (data : PublicData) (m : Message) (s : State)
    (gp : Randomness → View → ℝ≥0∞) (hgp : ∀ ρ v, gp ρ v ≤ 1) :
    ((Fintype.card Randomness : ℕ) : ℝ≥0∞)⁻¹ * ∑ ρ, Walk.val (fun x : Randomness => x + 1)
        (Walk.sOf landing (stat parameter data m s)) (Walk.tOf landing (stat parameter data m s))
        (walkPay parameter data m s (fun _ => 0) gp) 0 digestAttemptLimit ρ ≤
      grpM parameter data m s (fun _ => False) cardFn 0 := by
  have hpool := Walk.grp_ge_pool (e := succR) (p := landing) (L := digestAttemptLimit) landing_le_one cardFn_mono
    (stat parameter data m s) (exB (fun _ => False) m) (0 : Multiset View)
  rw [cardFn_zero, zero_add] at hpool
  unfold grpM
  refine le_trans (mul_le_mul_right (Finset.sum_le_sum fun ρ _ => ?_) _) hpool
  refine Walk.val_mono _ _ _ (fun x => ?_) le_rfl _ ρ
  unfold walkPay
  rcases stat parameter data m s x with _ | _ | v
  · simp [freshAvg]
  · exact le_rfl
  · simp only
    rw [if_neg (fun hb => exB_iff.1 hb), gain_cardFn]
    exact hgp x v

end LeanSphincs.Security.ForsPotential
