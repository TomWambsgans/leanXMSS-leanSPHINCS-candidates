import LeanSphincs.Scheme

/-! Byte encoding and domain separation; adapted from leanVM b7a107256. -/
namespace LeanSphincs
theorem bytesLE_injective {n : Nat} {x y : BitVec (8 * n)} (h : bytesLE n x = bytesLE n y) :
    x = y := by
  have hfun := List.ofFn_inj.mp h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hj : i / 8 < n := by omega
  have hbyte := congrFun hfun ⟨i / 8, hj⟩
  have hbits : (x.extractLsb' (8 * (i / 8)) 8) = (y.extractLsb' (8 * (i / 8)) 8) := by
    simpa using congrArg UInt8.toBitVec hbyte
  have hlsb := congrArg (fun b : BitVec 8 => b.getLsbD (i % 8)) hbits
  simp only [BitVec.getLsbD_extractLsb'] at hlsb
  have hmod : i % 8 < 8 := by omega
  have hsum : 8 * (i / 8) + i % 8 = i := by omega
  simpa [hmod, hsum] using hlsb

theorem bytesLE_length (n : Nat) (x : BitVec (8 * n)) : (bytesLE n x).length = n := by
  simp [bytesLE]

/-- A bit vector determines the natural it encodes, below the wrap. -/
theorem ofNat_inj_of_lt {w a b : Nat} (ha : a < 2 ^ w) (hb : b < 2 ^ w)
    (h : BitVec.ofNat w a = BitVec.ofNat w b) : a = b := by
  have htoNat := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at htoNat

theorem fieldBytes_injective {t1 t2 : TweakFields} (h : fieldBytes t1 = fieldBytes t2) : t1 = t2 := by
  obtain ⟨tag1, layer1, tree1, position1, index1⟩ := t1
  obtain ⟨tag2, layer2, tree2, position2, index2⟩ := t2
  simp only [fieldBytes] at h
  obtain ⟨h, hindex⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨h, htree⟩ := List.append_inj' h (by simp [bytesLE_length])
  obtain ⟨h, hposition⟩ := List.append_inj' h (by simp [bytesLE_length])
  have h := List.append_left_injective [0] h
  obtain ⟨htag, hlayer⟩ := List.append_inj' h (by simp [bytesLE_length])
  have htag := List.append_right_injective [protocolDomainSep] htag
  simp only [bytesLE_injective htag, bytesLE_injective hlayer, bytesLE_injective htree,
    bytesLE_injective hposition, bytesLE_injective hindex]

namespace Completeness
/-- Two hash inputs whose tweak fields differ in the tag differ, whatever their payloads. -/
theorem fieldInput_ne_of_tag_ne (parameter : PublicParameter) {fields1 fields2 : TweakFields}
    (htag : fields1.tag ≠ fields2.tag) (payload1 payload2 : HashInput) :
    fieldBytes fields1 ++ bytesLE 16 parameter ++ payload1
      ≠ fieldBytes fields2 ++ bytesLE 16 parameter ++ payload2 := by
  intro h
  apply htag
  obtain ⟨hprefix, _⟩ := List.append_inj h (by
    simp [fieldBytes, bytesLE_length])
  obtain ⟨hfields, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  rw [LeanSphincs.fieldBytes_injective hfields]

end Completeness
end LeanSphincs
