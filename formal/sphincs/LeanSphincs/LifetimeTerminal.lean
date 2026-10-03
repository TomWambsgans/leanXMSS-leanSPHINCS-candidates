import LeanSphincs.LifetimeDisclosure
import SphincsSecurity.Proof.Seeded.FreshTable
import Mathlib.Data.Fintype.Fin

/-! Exact terminal coverage law for independent uniform disclosure sets. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal

attribute [local instance] Classical.propDecidable

theorem sampleWord_eq_sequenceFin {α : Type} [SampleableType α] (n : Nat) :
    SphincsSecurity.Concrete.sampleUniformProposalWord α n =
      List.ofFn <$> SphincsSecurity.Concrete.sequenceFin (fun _ : Fin n => ($ᵗ α : ProbComp α)) := by
  induction n with
  | zero => simp [SphincsSecurity.Concrete.sampleUniformProposalWord,
      SphincsSecurity.Concrete.sequenceFin]
  | succ n ih =>
      simp only [SphincsSecurity.Concrete.sampleUniformProposalWord,
        SphincsSecurity.Concrete.sequenceFin, ih, map_bind, map_pure, bind_map_left]
      apply bind_congr
      intro head
      apply bind_congr
      intro tail
      simp

theorem evalDist_sampleWord_uniform_function {α : Type} [Fintype α] [SampleableType α] (n : Nat) :
    𝒟[SphincsSecurity.Concrete.sampleUniformProposalWord α n] =
      𝒟[List.ofFn <$> ($ᵗ (Fin n → α) : ProbComp (Fin n → α))] := by
  rw [sampleWord_eq_sequenceFin, evalDist_map, evalDist_map,
    SphincsSecurity.Seeded.evalDist_sequenceFin_uniform]

variable [Params]

def ViewCovered (target : KeptDigestView) (prior : Finset KeptDigestView) : Prop :=
  ∀ tree : IndexGroup, ∃ view ∈ prior, view.1 = target.1 ∧ view.2 tree = target.2 tree

theorem viewCovered_mono (target : KeptDigestView) : Monotone (ViewCovered target) := by
  intro left right hsub h tree
  obtain ⟨view, hmem, hview⟩ := h tree
  exact ⟨view, hsub hmem, hview⟩

def FunctionCovered {n : Nat} (target : KeptDigestView) (word : Fin n → KeptDigestView) : Prop :=
  ∀ tree : IndexGroup, ∃ position, (word position).1 = target.1 ∧
    (word position).2 tree = target.2 tree

theorem viewCovered_ofFn_iff (n : Nat) (target : KeptDigestView) (word : Fin n → KeptDigestView) :
    ViewCovered target (List.ofFn word).toFinset ↔ FunctionCovered target word := by
  simp only [ViewCovered, FunctionCovered, List.mem_toFinset, List.mem_ofFn]
  constructor
  · intro h tree
    obtain ⟨view, ⟨position, rfl⟩, hi, ht⟩ := h tree
    exact ⟨position, hi, ht⟩
  · intro h tree
    obtain ⟨position, hi, ht⟩ := h tree
    exact ⟨word position, ⟨position, rfl⟩, hi, ht⟩

theorem probEvent_uniformDisclosureSet_function (n : Nat) (target : KeptDigestView) :
    Pr[ViewCovered target | uniformDisclosureSet n ∅] =
      Pr[FunctionCovered target | ($ᵗ (Fin n → KeptDigestView) : ProbComp _)] := by
  rw [uniformDisclosureSet, probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_sampleWord_uniform_function n)]
  simp only [probEvent_map, Function.comp_def, Finset.union_empty]
  exact probEvent_ext (fun word _ => viewCovered_ofFn_iff n target word)

abbrev HitPosition {n : Nat} (indices : Fin n → Fin (2 ^ subtreeHeight))
    (index : Fin (2 ^ subtreeHeight)) := {position : Fin n // indices position = index}

noncomputable def hitHistoryEquiv {n : Nat} (indices : Fin n → Fin (2 ^ subtreeHeight))
    (index : Fin (2 ^ subtreeHeight)) :
    (HitPosition indices index → (IndexGroup → FtsLeaf)) ≃
      LeafHistory (Fintype.card (HitPosition indices index)) where
  toFun history tree position := history ((Fintype.equivFin _).symm position) tree
  invFun history position tree := history tree (Fintype.equivFin _ position)
  left_inv := by intro history; funext position tree; simp
  right_inv := by intro history; funext tree position; simp

noncomputable def selectedLeaves {n : Nat} (indices : Fin n → Fin (2 ^ subtreeHeight))
    (index : Fin (2 ^ subtreeHeight)) (leaves : Fin n → (IndexGroup → FtsLeaf)) :
    LeafHistory (Fintype.card (HitPosition indices index)) :=
  hitHistoryEquiv indices index (leaves ∘ Subtype.val)

theorem evalDist_selectedLeaves_uniform {n : Nat} (indices : Fin n → Fin (2 ^ subtreeHeight))
    (index : Fin (2 ^ subtreeHeight)) :
    𝒟[selectedLeaves indices index <$>
      ($ᵗ (Fin n → (IndexGroup → FtsLeaf)) : ProbComp _)] =
    𝒟[($ᵗ LeafHistory (Fintype.card (HitPosition indices index)) : ProbComp _)] := by
  calc
    _ = 𝒟[hitHistoryEquiv indices index <$>
        ((fun leaves : Fin n → (IndexGroup → FtsLeaf) => leaves ∘
          (Subtype.val : HitPosition indices index → Fin n)) <$> ($ᵗ _ : ProbComp _))] := by
        simp only [Functor.map_map]; rfl
    _ = 𝒟[hitHistoryEquiv indices index <$>
        ($ᵗ (HitPosition indices index → (IndexGroup → FtsLeaf)) : ProbComp _)] := by
        have h := evalDist_uniformSample_map_comp_injective
          (A := HitPosition indices index) (B := Fin n)
          (R := IndexGroup → FtsLeaf) (e := Subtype.val) Subtype.val_injective
        simpa only [bind_pure_comp, evalDist_map] using
          congrArg (fun distribution => (hitHistoryEquiv indices index) <$> distribution) h
    _ = _ := evalDist_map_bijective_uniform_cross
      (HitPosition indices index → (IndexGroup → FtsLeaf))
      (hitHistoryEquiv indices index) (hitHistoryEquiv indices index).bijective

theorem functionCovered_selected_iff {n : Nat} (indices : Fin n → Fin (2 ^ subtreeHeight))
    (target : KeptDigestView) (leaves : Fin n → (IndexGroup → FtsLeaf)) :
    FunctionCovered target (fun position => (indices position, leaves position)) ↔
      HistoryCovered target.2 (selectedLeaves indices target.1 leaves) := by
  constructor
  · intro h tree
    obtain ⟨position, hi, ht⟩ := h tree
    refine ⟨Fintype.equivFin _ ⟨position, hi⟩, ?_⟩
    change leaves (((Fintype.equivFin (HitPosition indices target.1)).symm
      (Fintype.equivFin _ ⟨position, hi⟩)).val) tree = target.2 tree
    simpa only [Equiv.symm_apply_apply] using ht
  · intro h tree
    obtain ⟨position, ht⟩ := h tree
    let hit : HitPosition indices target.1 := (Fintype.equivFin _).symm position
    exact ⟨hit.val, hit.property, ht⟩

theorem hitPosition_card {n : Nat} (indices : Fin n → Fin (2 ^ subtreeHeight))
    (index : Fin (2 ^ subtreeHeight)) :
    Fintype.card (HitPosition indices index) = (List.ofFn indices).count index := by
  rw [Fintype.card_subtype]
  simpa using Fin.card_filter_univ_eq_vector_get_eq_count index (List.Vector.ofFn indices)

theorem probEvent_functionCovered_fixed_indices {n : Nat}
    (indices : Fin n → Fin (2 ^ subtreeHeight)) (target : KeptDigestView) :
    Pr[fun leaves : Fin n → (IndexGroup → FtsLeaf) =>
      FunctionCovered target (fun position => (indices position, leaves position)) | ($ᵗ _ : ProbComp _)] =
      (1 - (1 - (1 : ℝ≥0∞) / 1024) ^ (List.ofFn indices).count target.1) ^ 24 := by
  calc
    _ = Pr[HistoryCovered target.2 |
        selectedLeaves indices target.1 <$> ($ᵗ (Fin n → (IndexGroup → FtsLeaf)) : ProbComp _)] := by
      rw [probEvent_map]
      exact probEvent_ext (fun leaves _ => functionCovered_selected_iff indices target leaves)
    _ = Pr[HistoryCovered target.2 |
        ($ᵗ LeafHistory (Fintype.card (HitPosition indices target.1)) : ProbComp _)] :=
      probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_selectedLeaves_uniform indices target.1)
    _ = _ := by rw [probEvent_history_covered, hitPosition_card]

def viewHistoryEquiv (n : Nat) :
    ((Fin n → Fin (2 ^ subtreeHeight)) × (Fin n → (IndexGroup → FtsLeaf))) ≃
      (Fin n → KeptDigestView) where
  toFun pair position := (pair.1 position, pair.2 position)
  invFun word := (fun position => (word position).1, fun position => (word position).2)
  left_inv := by intro pair; rfl
  right_inv := by intro word; rfl

theorem evalDist_uniform_views_split (n : Nat) :
    𝒟[($ᵗ (Fin n → KeptDigestView) : ProbComp _)] =
      𝒟[do
        let indices ← ($ᵗ (Fin n → Fin (2 ^ subtreeHeight)) : ProbComp _)
        let leaves ← ($ᵗ (Fin n → (IndexGroup → FtsLeaf)) : ProbComp _)
        pure (fun position => (indices position, leaves position))] := by
  symm
  calc
    _ = 𝒟[viewHistoryEquiv n <$> (do
        let indices ← ($ᵗ (Fin n → Fin (2 ^ subtreeHeight)) : ProbComp _)
        let leaves ← ($ᵗ (Fin n → (IndexGroup → FtsLeaf)) : ProbComp _)
        pure (indices, leaves))] := by
      simp only [map_bind, map_pure]; rfl
    _ = 𝒟[viewHistoryEquiv n <$>
        ($ᵗ ((Fin n → Fin (2 ^ subtreeHeight)) ×
          (Fin n → (IndexGroup → FtsLeaf))) : ProbComp _)] := by
      rw [evalDist_map, evalDist_map, SphincsSecurity.Seeded.evalDist_independent_uniform_pair]
    _ = _ := evalDist_map_bijective_uniform_cross _ _ (viewHistoryEquiv n).bijective

/-- Exact occupancy/coverage formula for the entire independent view history, with all unused
coordinates integrated out. This connects monotone disclosure domination to lifetime arithmetic. -/
theorem probEvent_uniformDisclosureSet_covered (n : Nat) (target : KeptDigestView) :
    Pr[ViewCovered target | uniformDisclosureSet n ∅] =
      SphincsSecurity.Concrete.binomialAverage ((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ n
        (fun r => (1 - (1 - (1 : ℝ≥0∞) / 1024) ^ r) ^ 24) := by
  rw [probEvent_uniformDisclosureSet_function]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (evalDist_uniform_views_split n)]
  rw [probEvent_bind_eq_tsum]
  simp only [bind_pure_comp, probEvent_map, Function.comp_def]
  simp_rw [probEvent_functionCovered_fixed_indices]
  have hword := evalDist_sampleWord_uniform_function (α := Fin (2 ^ subtreeHeight)) n
  have h := SphincsSecurity.Concrete.expected_uniformProposalWord_count target.1 n
    (fun r => (1 - (1 - (1 : ℝ≥0∞) / 1024) ^ r) ^ 24)
  have hprob (word : List (Fin (2 ^ subtreeHeight))) :
      Pr[= word | SphincsSecurity.Concrete.sampleUniformProposalWord (Fin (2 ^ subtreeHeight)) n] =
        Pr[= word | List.ofFn <$> ($ᵗ (Fin n → Fin (2 ^ subtreeHeight)) : ProbComp _)] :=
    congrArg (fun distribution => distribution word) hword
  simp_rw [hprob] at h
  rw [tsum_probOutput_map_mul] at h
  simpa using h

end LeanSphincs.Lifetime
