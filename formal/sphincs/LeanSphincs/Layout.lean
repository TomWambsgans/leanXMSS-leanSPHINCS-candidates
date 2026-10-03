import LeanSphincs.Bytes

/-! Signature byte layout from `crates/sphincs/src/scheme.rs::Signature::to_bytes`. -/

namespace LeanSphincs

def serializeSignature (signature : Signature) : List UInt8 :=
  bytesLE 16 signature.randomness ++
  (List.ofFn fun tree : FtsTree => bytesLE 16 (signature.ftsSecret tree) ++
    (List.ofFn (signature.ftsPath tree)).flatMap (bytesLE 16)).flatten ++
  bytesLE 4 (signature.layers topLayer).counter ++
  (List.ofFn (signature.layers topLayer).chainValues).flatMap (bytesLE 16) ++
  (List.ofFn (signature.layers topLayer).path).flatMap (bytesLE 16)

theorem digest_vector_length {n : Nat} (values : Fin n → Digest) :
    ((List.ofFn values).flatMap (bytesLE 16)).length = n * 16 := by
  simp [List.length_flatMap, bytesLE_length]
  exact List.length_ofFn

/-- Actual serialization has 5684 bytes for every signature, including malformed signatures. -/
theorem signature_size (signature : Signature) : (serializeSignature signature).length = 5684 := by
  simp only [serializeSignature, List.length_append, bytesLE_length, digest_vector_length,
    List.length_flatten, List.map_ofFn, Function.comp_def, List.sum_ofFn,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  decide

/-- The 266 digest bits require the two distinct 256-bit message calls used by the scheme. -/
theorem message_digest_size : messageDigestBits = 266 ∧
    hashOutputBits < messageDigestBits ∧ messageDigestBits ≤ 2 * hashOutputBits := by decide

end LeanSphincs
