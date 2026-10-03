import LeanSphincs.SecurityPrefixPrepared

/-! Independent sampling of the low128-bit secret of a selected candidate chain from the full
prepared material, retaining its high128bits and every other material entry. -/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Prefix
open SeedModel SphincsSecurity.Concrete.UniformTableSplit

attribute [local instance] Classical.propDecidable

noncomputable def replaceMaterial (segment : Segment) (material : Material) (value : Digest) : Material :=
  (material.1, Function.update material.2 (.inl (address segment))
    (combine value (splitHashOutput digestBits (material.2 (.inl (address segment)))).2))

theorem replaceMaterial_parameter (segment : Segment) (material : Material) (value : Digest) :
    parameter (replaceMaterial segment material value) = parameter material := rfl

theorem replaceMaterial_self (segment : Segment) (material : Material) (value : Digest) :
    truncateHash ((replaceMaterial segment material value).2 (.inl (address segment))) = value := by
  simp only [replaceMaterial, Function.update_self, truncate_combine]

theorem replaceMaterial_other (segment : Segment) (material : Material) (value : Digest)
    (position : SecretPosition) (hother : position ≠ .inl (address segment)) :
    (replaceMaterial segment material value).2 position = material.2 position := by
  simp only [replaceMaterial, Function.update_of_ne hother]

theorem replaceMaterial_twice (segment : Segment) (material : Material) (first second : Digest) :
    replaceMaterial segment (replaceMaterial segment material first) second =
      replaceMaterial segment material second := by
  simp only [replaceMaterial, Function.update_self, split_combine, Function.update_idem]

theorem replaceMaterial_current (segment : Segment) (material : Material) :
    replaceMaterial segment material (truncateHash (material.2 (.inl (address segment)))) = material := by
  simp only [replaceMaterial, combine_split, Function.update_eq_self, Prod.mk.eta]

theorem materialSecrets_replaceMaterial (segment : Segment) (material : Material) (value : Digest) :
    materialSecrets (replaceMaterial segment material value) = replaceSecret segment (materialSecrets material) value := by
  funext chain
  by_cases hchain : chain = address segment
  · subst chain
    exact (replaceMaterial_self segment material value).trans (replaceSecret_self segment _ value).symm
  · have hpos : Sum.inl chain ≠ (Sum.inl (address segment) : SecretPosition) := by simpa using hchain
    simp only [materialSecrets, replaceMaterial_other segment material value _ hpos,
      replaceSecret, Function.update_of_ne hchain]

abbrev ErasedMaterial (segment : Segment) :=
  {material : Material // truncateHash (material.2 (.inl (address segment))) = 0}

instance (segment : Segment) : Nonempty (ErasedMaterial segment) := ⟨⟨(0, fun _ => 0), rfl⟩⟩

noncomputable def materialSplit (segment : Segment) : Material ≃ ErasedMaterial segment × Digest where
  toFun material := (⟨replaceMaterial segment material 0, replaceMaterial_self segment material 0⟩,
    truncateHash (material.2 (.inl (address segment))))
  invFun pair := replaceMaterial segment pair.1.val pair.2
  left_inv material := (replaceMaterial_twice segment material 0 _).trans
    (replaceMaterial_current segment material)
  right_inv pair := by
    apply Prod.ext
    · apply Subtype.ext
      exact (replaceMaterial_twice segment pair.1.val pair.2 0).trans
        (by simpa only [pair.1.property] using replaceMaterial_current segment pair.1.val)
    · exact replaceMaterial_self segment pair.1.val pair.2

/-- The selected secret's low128bits remain uniformly independent even when the rest of the
complete prepared material, including that output's high128bits, is supplied to a simulation. -/
theorem uniform_material (segment : Segment) :
    PMF.uniformOfFintype Material =
      (PMF.uniformOfFintype (ErasedMaterial segment)).bind (fun other =>
        (PMF.uniformOfFintype Digest).map (replaceMaterial segment other.val)) := by
  have h := PMF.uniformOfFintype_map_of_bijective (materialSplit segment).symm
    (materialSplit segment).symm.bijective
  rw [uniform_product, PMF.map_bind] at h
  simpa only [PMF.map_comp, Function.comp_def, materialSplit, Equiv.coe_fn_symm_mk] using h.symm

end LeanSphincs.Security.Prefix
