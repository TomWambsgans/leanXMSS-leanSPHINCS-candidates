import LeanSphincs.LifetimeProbability
import SphincsSecurity.Proof.Fts.UniformProposalMoments

/-!
An independent sampling interpretation of the lifetime expression. Index histories are sampled
independently and uniformly. Conditional on the number of occurrences of a fixed target index,
the FORS leaves at those occurrences are independent uniform values in each of the 24 trees.
This proves the resulting exact probability law, without assuming that adversarially chosen or
cached message digests obey that independent law.
-/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal

abbrev LeafHistory (r : Nat) := Fin 24 → Fin r → Fin 1024

def HistoryCovered {r : Nat} (target : Fin 24 → Fin 1024) (history : LeafHistory r) : Prop :=
  ∀ tree, ∃ position, history tree position = target tree

instance {r : Nat} (target : Fin 24 → Fin 1024) : DecidablePred (@HistoryCovered r target) :=
  fun history => inferInstanceAs (Decidable (∀ tree, ∃ position, history tree position = target tree))

def missingHistoryEquiv (r : Nat) (leaf : Fin 1024) :
    {word : Fin r → Fin 1024 // ∀ i, word i ≠ leaf} ≃
      (Fin r → {value : Fin 1024 // value ≠ leaf}) where
  toFun word i := ⟨word.val i, word.property i⟩
  invFun word := ⟨fun i => (word i).val, fun i => (word i).property⟩
  left_inv := by intro word; rfl
  right_inv := by intro word; rfl

theorem missing_history_card (r : Nat) (leaf : Fin 1024) :
    Fintype.card {word : Fin r → Fin 1024 // ∀ i, word i ≠ leaf} = 1023 ^ r := by
  rw [Fintype.card_congr (missingHistoryEquiv r leaf), Fintype.card_fun,
    Fintype.card_subtype_compl (fun value : Fin 1024 => value = leaf)]
  simp

theorem hit_history_card (r : Nat) (leaf : Fin 1024) :
    Fintype.card {word : Fin r → Fin 1024 // ∃ i, word i = leaf} = 1024 ^ r - 1023 ^ r := by
  have h := Fintype.card_subtype_compl (fun word : Fin r → Fin 1024 => ∀ i, word i ≠ leaf)
  simp only [not_forall, ne_eq, not_not, Fintype.card_fun, Fintype.card_fin,
    missing_history_card] at h
  exact h

def coveredHistoryEquiv (r : Nat) (target : Fin 24 → Fin 1024) :
    {history : LeafHistory r // HistoryCovered target history} ≃
      ((tree : Fin 24) → {word : Fin r → Fin 1024 // ∃ i, word i = target tree}) where
  toFun history tree := ⟨history.val tree, history.property tree⟩
  invFun history := ⟨fun tree => (history tree).val, fun tree => (history tree).property⟩
  left_inv := by intro history; rfl
  right_inv := by intro history; rfl

theorem covered_history_card (r : Nat) (target : Fin 24 → Fin 1024) :
    Fintype.card {history : LeafHistory r // HistoryCovered target history} =
      (1024 ^ r - 1023 ^ r) ^ 24 := by
  rw [Fintype.card_congr (coveredHistoryEquiv r target), Fintype.card_pi]
  simp only [hit_history_card, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem probEvent_history_covered (r : Nat) (target : Fin 24 → Fin 1024) :
    Pr[HistoryCovered target | ($ᵗ LeafHistory r : ProbComp (LeafHistory r))] =
      (1 - (1 - (1 : ℝ≥0∞) / 1024) ^ r) ^ 24 := by
  rw [probEvent_uniformSample, ← Fintype.card_subtype, covered_history_card]
  simp only [LeafHistory, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
  rw [ENNReal.natCast_sub]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hdiv (a c : ℝ≥0∞) (k : Nat) : a ^ k / c ^ k = (a / c) ^ k := by
    rw [div_eq_mul_inv, ENNReal.inv_pow, ← mul_pow]
    rfl
  rw [hdiv, ENNReal.sub_div (by intros; positivity),
    ENNReal.div_self (by positivity) (by finiteness), hdiv]
  have hratio : (1023 : ℝ≥0∞) / 1024 = 1 - 1 / 1024 := by
    apply ENNReal.eq_sub_of_add_eq (by finiteness)
    rw [ENNReal.div_add_div_same]
    norm_num
    exact ENNReal.div_self (by norm_num) (by finiteness)
  rw [hratio]

/-- Independent index history, followed by all independent FORS leaf coordinates at its hits. -/
noncomputable def independentTargetCoverage (b n : Nat) (index : Fin (2 ^ b))
    (target : Fin 24 → Fin 1024) : ProbComp Bool := do
  let indices ← SphincsSecurity.Concrete.sampleUniformProposalWord (Fin (2 ^ b)) n
  let history ← $ᵗ LeafHistory (indices.count index)
  pure (decide (HistoryCovered target history))

theorem probEvent_independentTargetCoverage (b n : Nat) (index : Fin (2 ^ b))
    (target : Fin 24 → Fin 1024) :
    Pr[fun result => result = true | independentTargetCoverage b n index target] =
      SphincsSecurity.Concrete.binomialAverage ((2 : ℝ≥0∞) ^ b)⁻¹ n
        (fun r => (1 - (1 - (1 : ℝ≥0∞) / 1024) ^ r) ^ 24) := by
  unfold independentTargetCoverage
  rw [probEvent_bind_eq_tsum]
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, decide_eq_true_eq]
  simp_rw [probEvent_history_covered]
  convert SphincsSecurity.Concrete.expected_uniformProposalWord_count index n
    (fun r => (1 - (1 - (1 : ℝ≥0∞) / 1024) ^ r) ^ 24) using 1
  simp

theorem independent_coverage_lifetime_bound {b n : Nat} (h : Certificate b n)
    (index : Fin (2 ^ b)) (target : Fin 24 → Fin 1024) :
    (2 : ℝ≥0∞) ^ b / 2 ^ 26 *
      Pr[fun result => result = true | independentTargetCoverage b n index target] ≤
        (1 : ℝ≥0∞) / 2 ^ 127 := by
  rw [probEvent_independentTargetCoverage]
  exact forsBoundENNReal_le_of_real (forsBound_le_of_certificate b n h)

end LeanSphincs.Lifetime
