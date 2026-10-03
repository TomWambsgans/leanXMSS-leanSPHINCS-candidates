import SphincsSecurity.Proof.Scheme.Bytes
import SphincsSecurity.Proof.Ots.EncodingProbability
namespace SphincsSecurity.OtsCode

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Finset.univ

noncomputable def decodingDigests (words : Finset Encoding) : Finset Digest :=
  Finset.univ.filter fun digest => ∃ word ∈ words, decode digest = some word

theorem mem_decodingDigests {words : Finset Encoding} {digest : Digest} :
    digest ∈ decodingDigests words ↔ ∃ word ∈ words, decode digest = some word := by
  simp only [decodingDigests, Finset.mem_filter, Finset.mem_univ, true_and]

theorem decodingDigests_card_le (words : Finset Encoding) : (decodingDigests words).card ≤ words.card := by
  apply Finset.card_le_card_of_injOn (fun digest => (decode digest).getD defaultWord)
  · intro digest hd
    obtain ⟨word, hw, hdecode⟩ := mem_decodingDigests.mp hd
    simpa only [hdecode, Option.getD_some, Finset.mem_coe] using hw
  · intro left hl right hr he
    obtain ⟨leftWord, _, hleft⟩ := mem_decodingDigests.mp hl
    obtain ⟨rightWord, _, hright⟩ := mem_decodingDigests.mp hr
    simp only [hleft, hright, Option.getD_some] at he
    exact decode_some_injective hleft (by rw [he]; exact hright)

theorem decodingDigests_uniform_le (words : Finset Encoding) :
    Pr[fun output : HashOutput => truncateHash output ∈ decodingDigests words | ($ᵗ HashOutput : ProbComp HashOutput)] ≤
      (words.card : ENNReal) / Fintype.card Digest := by
  rw [probEvent_uniform_truncateHash_mem]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (decodingDigests_card_le words)) _

end SphincsSecurity.OtsCode
