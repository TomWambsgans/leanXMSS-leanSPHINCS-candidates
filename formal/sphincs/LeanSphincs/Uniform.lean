import LeanSphincs.Scheme

/-! Uniform bit extraction; adapted from leanVM b7a107256. -/
namespace LeanSphincs
open OracleComp OracleSpec ENNReal
theorem hashOutput_eq_of_extract {width : Nat} (hwidth : width ≤ hashOutputBits) {x y : HashOutput}
    (hlow : x.extractLsb' 0 width = y.extractLsb' 0 width)
    (hhigh : x.extractLsb' width (hashOutputBits - width)
      = y.extractLsb' width (hashOutputBits - width)) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlt : i < width
  · have := congrArg (fun b : BitVec width => b.getLsbD i) hlow
    simpa [BitVec.getLsbD_extractLsb', hlt] using this
  · have hshift : i - width < hashOutputBits - width := by omega
    have := congrArg (fun b : BitVec (hashOutputBits - width) => b.getLsbD (i - width)) hhigh
    simp only [BitVec.getLsbD_extractLsb', hshift, decide_true, Bool.true_and] at this
    rwa [show width + (i - width) = i by omega] at this

def splitHashOutput (width : Nat) (output : HashOutput) :
    BitVec width × BitVec (hashOutputBits - width) :=
  (output.extractLsb' 0 width,
    output.extractLsb' width (hashOutputBits - width))

theorem splitHashOutput_injective {width : Nat} (hwidth : width ≤ hashOutputBits) :
    Function.Injective (splitHashOutput width) := by
  intro left right heq
  apply hashOutput_eq_of_extract hwidth
  · exact congrArg Prod.fst heq
  · exact congrArg Prod.snd heq

theorem splitHashOutput_bijective {width : Nat} (hwidth : width ≤ hashOutputBits) :
    Function.Bijective (splitHashOutput width) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨splitHashOutput_injective hwidth, ?_⟩
  rw [Fintype.card_prod, card_bitVec, card_bitVec, card_bitVec, ← pow_add]
  congr
  omega

noncomputable def splitHashOutputEquiv (width : Nat) (hwidth : width ≤ hashOutputBits) :
    HashOutput ≃ BitVec width × BitVec (hashOutputBits - width) :=
  Equiv.ofBijective (splitHashOutput width) (splitHashOutput_bijective hwidth)

/-- The 32-byte output whose first half is `low` and whose second half is `high`. -/
noncomputable def joinHalves (low high : Digest) : HashOutput :=
  (splitHashOutputEquiv digestBits (by decide)).symm (low, high)

theorem truncateHash_joinHalves (low high : Digest) : truncateHash (joinHalves low high) = low :=
  congrArg Prod.fst ((splitHashOutputEquiv digestBits (by decide)).apply_symm_apply (low, high))

theorem truncateHashHigh_joinHalves (low high : Digest) :
    truncateHashHigh (joinHalves low high) = high :=
  congrArg Prod.snd ((splitHashOutputEquiv digestBits (by decide)).apply_symm_apply (low, high))

theorem joinHalves_halves (output : HashOutput) :
    joinHalves (truncateHash output) (truncateHashHigh output) = output :=
  (splitHashOutputEquiv digestBits (by decide)).symm_apply_apply output

theorem evalDist_hashOutput_extract_uniform {width : Nat} (hwidth : width ≤ hashOutputBits) :
    𝒟[(fun output : HashOutput => output.extractLsb' 0 width) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒟[($ᵗ BitVec width : ProbComp (BitVec width))] := by
  let split := splitHashOutput width
  have hmap :
      (fun output : HashOutput => output.extractLsb' 0 width) <$>
          ($ᵗ HashOutput : ProbComp HashOutput) =
        Prod.fst <$> (split <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
    simp [Functor.map_map, split, splitHashOutput]
  rw [hmap]
  have hsplit :
      𝒟[split <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
        𝒟[($ᵗ (BitVec width × BitVec (hashOutputBits - width)) :
          ProbComp (BitVec width × BitVec (hashOutputBits - width)))] :=
    evalDist_map_bijective_uniform_cross
      (α := HashOutput) (β := BitVec width × BitVec (hashOutputBits - width))
      split (splitHashOutput_bijective hwidth)
  rw [evalDist_map, hsplit, ← evalDist_map]
  exact evalDist_map_fst_uniformSample_prod

theorem evalDist_truncateHash_uniform :
    𝒟[truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒟[($ᵗ Digest : ProbComp Digest)] := by
  change 𝒟[(fun output : HashOutput => output.extractLsb' 0 digestBits) <$>
      ($ᵗ HashOutput : ProbComp HashOutput)] = _
  exact evalDist_hashOutput_extract_uniform (width := digestBits) (by decide)

theorem probEvent_uniform_truncateHash_eq (target : Digest) :
    Pr[fun output : HashOutput => truncateHash output = target |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      (Fintype.card Digest : ℝ≥0∞)⁻¹ := by
  rw [show (fun output : HashOutput => truncateHash output = target) =
      (fun output => output = target) ∘ truncateHash from rfl]
  rw [← probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) evalDist_truncateHash_uniform]
  rw [probEvent_eq_eq_probOutput, probOutput_uniformSample]

theorem probEvent_uniform_truncateHash_mem (targets : Finset Digest) :
    Pr[fun output : HashOutput => truncateHash output ∈ targets |
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      (targets.card : ℝ≥0∞) / (Fintype.card Digest : ℝ≥0∞) := by
  rw [show (fun output : HashOutput => truncateHash output ∈ targets) =
      (fun digest => digest ∈ targets) ∘ truncateHash from rfl]
  rw [← probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) evalDist_truncateHash_uniform]
  rw [probEvent_uniformSample]
  rw [Finset.filter_univ_mem]

end LeanSphincs
