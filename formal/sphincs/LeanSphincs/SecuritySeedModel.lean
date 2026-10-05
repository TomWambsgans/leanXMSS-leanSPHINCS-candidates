import LeanSphincs.SecuritySeedGuess
import LeanSphincs.Recovery

/-!
Seed-independent prepared key material and its exact full-output oracle programming interface.
The table includes all OTS and FORS derivations and every possible surrogate. Only the parameter
derivation uses the zero public parameter; all other entries use its truncated sampled output.
This module defines and verifies the programming operation. It does not assume that an existing
honest-game cache is independent of the master seed or already has the prepared distribution.
-/

open OracleComp OracleSpec

namespace LeanSphincs.Security.SeedModel

attribute [local instance] Classical.propDecidable

abbrev OtsPosition := Layer × TreeIndex × LeafIndex × ChainIndex
abbrev ForsPosition := Index × FtsTree × FtsLeaf
abbrev SecretPosition := OtsPosition ⊕ (ForsPosition ⊕ Fin totalHeight)
abbrev SecretOutputs := SecretPosition → HashOutput

/-- Full256-bit responses are retained, including the high128bits that honest derivation discards. -/
abbrev Material := HashOutput × SecretOutputs

def parameter (material : Material) : PublicParameter := truncateHash material.1

noncomputable opaque secretOutputsSampleableType : SampleableType SecretOutputs :=
  SampleableType.ofFintype SecretOutputs

noncomputable local instance : SampleableType SecretOutputs := secretOutputsSampleableType

/-- This sampling procedure has no master seed as an input. -/
noncomputable def sampleMaterial : ProbComp Material := do
  let parameterOutput ← $ᵗ HashOutput
  let outputs ← $ᵗ SecretOutputs
  return (parameterOutput, outputs)

def secretDomain : SecretPosition → KeygenDomain
  | .inl (lay, tree, leaf, chain) => .ots lay tree leaf chain
  | .inr (.inl (index, tree, leaf)) => .fts index tree leaf
  | .inr (.inr level) => .surrogate level

theorem secretDomain_injective : Function.Injective secretDomain := by
  intro left right h
  cases left with
  | inl left =>
      rcases left with ⟨lay, tree, leaf, chain⟩
      cases right with
      | inl right => rcases right with ⟨lay', tree', leaf', chain'⟩; simpa [secretDomain] using h
      | inr right => cases right <;> cases h
  | inr left =>
      cases left with
      | inl left =>
          rcases left with ⟨index, tree, leaf⟩
          cases right with
          | inl right => cases h
          | inr right =>
              cases right with
              | inl right => rcases right with ⟨index', tree', leaf'⟩; simpa [secretDomain] using h
              | inr right => cases h
      | inr left =>
          cases right with
          | inl right => cases h
          | inr right =>
              cases right with
              | inl right => cases h
              | inr right => simpa [secretDomain] using h

theorem secretDomain_ne_parameter (position : SecretPosition) : secretDomain position ≠ .parameter := by
  cases position with
  | inl p => rcases p with ⟨_, _, _, _⟩; simp [secretDomain]
  | inr p => cases p <;> simp [secretDomain]

def parameterInput (seed : MasterSeed) : HashInput := keygenHashInput 0 .parameter seed

def secretInput (seed : MasterSeed) (material : Material) (position : SecretPosition) : HashInput :=
  keygenHashInput (parameter material) (secretDomain position) seed

theorem secretInput_injective (seed : MasterSeed) (material : Material) :
    Function.Injective (secretInput seed material) := by
  intro left right h
  exact secretDomain_injective (keygenInput_injective h).2.1

theorem secretInput_ne_parameterInput (seed : MasterSeed) (material : Material)
    (position : SecretPosition) : secretInput seed material position ≠ parameterInput seed := by
  intro h
  exact secretDomain_ne_parameter position (keygenInput_injective h).2.1

/-- Program the complete derivation table over a base cache. This definition overwrites its
specified entries; a later lemma explicitly requires those entries fresh to preserve the base. -/
noncomputable def programCache (base : QueryCache HashSpec) (seed : MasterSeed)
    (material : Material) : QueryCache HashSpec := fun input =>
  if input = parameterInput seed then some material.1
  else if h : ∃ position, input = secretInput seed material position then
    some (material.2 (Classical.choose h))
  else base input

theorem programCache_parameter (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material) :
    programCache base seed material (parameterInput seed) = some material.1 := by
  simp [programCache]

theorem programCache_secret (base : QueryCache HashSpec) (seed : MasterSeed)
    (material : Material) (position : SecretPosition) :
    programCache base seed material (secretInput seed material position) = some (material.2 position) := by
  rw [programCache, if_neg (secretInput_ne_parameterInput seed material position)]
  have h : ∃ other, secretInput seed material position = secretInput seed material other := ⟨position, rfl⟩
  rw [dif_pos h]
  exact congrArg (fun p => some (material.2 p))
    (secretInput_injective seed material (Classical.choose_spec h).symm)

/-- Precisely the addressed parameter/secret entries are programmed; other seed-bearing inputs
are left alone, including derivations under any other public parameter. -/
theorem programCache_other (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material)
    (input : HashInput) (hparameter : input ≠ parameterInput seed)
    (hsecret : ∀ position, input ≠ secretInput seed material position) :
    programCache base seed material input = base input := by
  simp only [programCache, hparameter, ↓reduceIte]
  exact dif_neg (by simpa only [not_exists] using hsecret)

def AgreeOutsideSeed (seed : MasterSeed) (left right : QueryCache HashSpec) : Prop :=
  ∀ input, ¬SeedGuess.SeedHit input seed → left input = right input

/-- Programming cannot affect an input that fails the exact hidden-seed predicate. -/
theorem programCache_agreeOutside (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material) :
    AgreeOutsideSeed seed (programCache base seed material) base := by
  intro input hnot
  apply programCache_other
  · intro heq
    exact hnot ⟨0, .parameter, heq.symm⟩
  · intro position heq
    exact hnot ⟨parameter material, secretDomain position, heq.symm⟩

/-- The concrete verifier never touches a programmed derivation entry. -/
theorem programCache_verifier (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material)
    (p : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    programCache base seed material (tweakableHashInput p domain payload) =
      base (tweakableHashInput p domain payload) := by
  apply programCache_agreeOutside
  rintro ⟨p', domain', heq⟩
  exact keygenInput_ne_hashInput p' p domain' domain seed payload heq

/-- An answer function extends the complete prepared derivation table. -/
def PreparedAgreement (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material) : Prop :=
  f (parameterInput seed) = material.1 ∧
    ∀ position, f (secretInput seed material position) = material.2 position

/-- A total oracle implementing the prepared table, with the supplied oracle everywhere else. -/
noncomputable def preparedOracle (fallback : QueryImpl HashSpec Id) (seed : MasterSeed)
    (material : Material) : QueryImpl HashSpec Id := fun input =>
  (programCache ∅ seed material input).getD (fallback input)

/-- Every OTS/FORS/surrogate derivation reads the sampled table at the actual public parameter. -/
theorem eval_secret_prepared (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material)
    (h : PreparedAgreement f seed material) (position : SecretPosition) :
    evalWithAnswerFn f (deriveKey (parameter material) (secretDomain position) seed :
      OracleComp HashSpec Digest) = truncateHash (material.2 position) := by
  rw [Completeness.eval_deriveKey]
  exact congrArg truncateHash (h.2 position)

end LeanSphincs.Security.SeedModel
