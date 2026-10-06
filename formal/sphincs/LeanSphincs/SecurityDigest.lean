import LeanSphincs.ForsCoverage
import LeanSphincs.Bytes
import LeanSphincs.Search

/-!
The candidate's two-call message digest: joining the first block with the low ten bits of the
second is a bijection, so two independent uniform blocks give the uniform 266-bit digest law; and
the two block inputs of a digest call are distinct.
-/

open OracleComp OracleSpec ENNReal
set_option exponentiation.threshold 512

namespace LeanSphincs.Security
open Concrete

/-- The second hash block contributes only its low ten bits. -/
def joinDigest (blocks : HashOutput × BitVec 10) : MessageDigest :=
  blocks.2 ++ blocks.1

theorem joinDigest_injective : Function.Injective joinDigest := by
  intro x y h
  apply Prod.ext
  · have hlow := congrArg (fun d : MessageDigest => d.extractLsb' 0 256) h
    change (x.2 ++ x.1).extractLsb' 0 hashOutputBits =
      (y.2 ++ y.1).extractLsb' 0 hashOutputBits at hlow
    simpa only [BitVec.extractLsb'_append_eq_right] using hlow
  · have hhigh := congrArg (fun d : MessageDigest => d.extractLsb' 256 10) h
    change (x.2 ++ x.1).extractLsb' hashOutputBits 10 =
      (y.2 ++ y.1).extractLsb' hashOutputBits 10 at hhigh
    simpa only [BitVec.extractLsb'_append_eq_left] using hhigh

theorem joinDigest_bijective : Function.Bijective joinDigest := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨joinDigest_injective, ?_⟩
  simp only [Fintype.card_prod, card_bitVec, ← pow_add]
  rfl

theorem truncateMessageDigest_eq_join (first second : HashOutput) :
    truncateMessageDigest first second = joinDigest (first, second.extractLsb' 0 10) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi' : i < 266 := hi
  change ((second ++ first).extractLsb' 0 266).getLsbD i =
    ((second.extractLsb' 0 10) ++ first).getLsbD i
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp only [hashOutputBits, Nat.zero_add]
  by_cases hlow : i < 256
  · simp [hlow, hi']
  · have hhigh : i - 256 < 10 := by omega
    simp [hlow, hi', hhigh]

/-- The two independent oracle blocks induce exactly the uniform 266-bit digest law. -/
theorem evalDist_digestBlocks_uniform :
    𝒟[(do
      let first ← ($ᵗ HashOutput : ProbComp HashOutput)
      let second ← ($ᵗ HashOutput : ProbComp HashOutput)
      pure (truncateMessageDigest first second))] =
      𝒟[($ᵗ MessageDigest : ProbComp MessageDigest)] := by
  let pairs : ProbComp (HashOutput × BitVec 10) := do
    let first ← ($ᵗ HashOutput : ProbComp HashOutput)
    let second ← ($ᵗ HashOutput : ProbComp HashOutput)
    pure (first, second.extractLsb' 0 10)
  have hpairs : 𝒟[pairs] = 𝒟[($ᵗ (HashOutput × BitVec 10) :
      ProbComp (HashOutput × BitVec 10))] := by
    apply evalDist_ext
    intro pair
    change Pr[= pair | (do
      let first ← ($ᵗ HashOutput : ProbComp HashOutput)
      let second ← ($ᵗ HashOutput : ProbComp HashOutput)
      pure ((id first), second.extractLsb' 0 10))] = _
    rw [probOutput_bind_bind_prod_mk_eq_mul]
    simp only [id_map]
    rw [evalDist_ext_iff.mp
      (evalDist_hashOutput_extract_uniform (width := 10) (by decide)) pair.2]
    simp [ENNReal.mul_inv, Nat.cast_mul]
  have hjoin : (do
      let first ← ($ᵗ HashOutput : ProbComp HashOutput)
      let second ← ($ᵗ HashOutput : ProbComp HashOutput)
      pure (truncateMessageDigest first second)) = joinDigest <$> pairs := by
    simp only [pairs, map_bind, map_pure, truncateMessageDigest_eq_join]
  rw [hjoin, evalDist_map, hpairs, ← evalDist_map]
  exact evalDist_map_bijective_uniform_cross (α := HashOutput × BitVec 10)
    (β := MessageDigest) joinDigest joinDigest_bijective

/-- The exact byte string queried for one block of a message digest. -/
abbrev digestInput (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) (call : Fin 2) : HashInput :=
  tweakableHashInput parameter (.message call) (messageDigestPayload root message randomness)

theorem digestInput_injective (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) :
    Function.Injective (digestInput parameter root message randomness) := by
  intro left right h
  have hfields := fieldBytes_injective
    (List.append_cancel_left (List.append_cancel_right h))
  have hposition := congrArg TweakFields.hi hfields
  apply Fin.ext
  exact ofNat_inj_of_lt (by have := left.isLt; omega) (by have := right.isLt; omega) hposition

end LeanSphincs.Security
