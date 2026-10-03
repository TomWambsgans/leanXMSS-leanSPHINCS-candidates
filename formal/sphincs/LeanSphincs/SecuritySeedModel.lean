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

/-- Every non-parameter derivation, including every surrogate, has exactly one table position. -/
theorem secretDomain_complete (domain : KeygenDomain) (h : domain ≠ .parameter) :
    ∃ position, secretDomain position = domain := by
  cases domain with
  | parameter => exact False.elim (h rfl)
  | ots lay tree leaf chain => exact ⟨.inl (lay, tree, leaf, chain), rfl⟩
  | fts index tree leaf => exact ⟨.inr (.inl (index, tree, leaf)), rfl⟩
  | surrogate level => exact ⟨.inr (.inr level), rfl⟩

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

/-- Freshness required before the programming operation preserves the original cache. -/
def TableFresh (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material) : Prop :=
  base (parameterInput seed) = none ∧ ∀ position, base (secretInput seed material position) = none

theorem programCache_extends (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material)
    (hfresh : TableFresh base seed material) : base ≤ programCache base seed material := by
  intro input answer hcached
  rw [programCache_other]
  · exact hcached
  · intro heq
    rw [heq, hfresh.1] at hcached
    cases hcached
  · intro position heq
    rw [heq, hfresh.2 position] at hcached
    cases hcached

/-- An answer function extends the complete prepared derivation table. -/
def PreparedAgreement (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material) : Prop :=
  f (parameterInput seed) = material.1 ∧
    ∀ position, f (secretInput seed material position) = material.2 position

theorem programCache_agrees (base : QueryCache HashSpec) (seed : MasterSeed) (material : Material)
    (f : QueryImpl HashSpec Id) (hbase : base.AgreesWithFn f)
    (hprepared : PreparedAgreement f seed material) :
    (programCache base seed material).AgreesWithFn f := by
  intro input answer hanswer
  unfold programCache at hanswer
  split at hanswer
  next heq =>
    cases Option.some.inj hanswer
    rw [heq]
    exact hprepared.1
  next =>
    split at hanswer
    next h =>
      cases Option.some.inj hanswer
      exact (congrArg (fun input : HashInput => (f input : HashOutput))
        (Classical.choose_spec h)).trans (hprepared.2 _)
    next => exact hbase hanswer

theorem preparedAgreement_of_programCache (base : QueryCache HashSpec) (seed : MasterSeed)
    (material : Material) (f : QueryImpl HashSpec Id)
    (h : (programCache base seed material).AgreesWithFn f) : PreparedAgreement f seed material :=
  ⟨h (programCache_parameter base seed material), fun position => h (programCache_secret base seed material position)⟩

/-- A total oracle implementing the prepared table, with the supplied oracle everywhere else. -/
noncomputable def preparedOracle (fallback : QueryImpl HashSpec Id) (seed : MasterSeed)
    (material : Material) : QueryImpl HashSpec Id := fun input =>
  (programCache ∅ seed material input).getD (fallback input)

theorem preparedOracle_agreement (fallback : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material) :
    PreparedAgreement (preparedOracle fallback seed material) seed material := by
  constructor
  · simp [preparedOracle, programCache_parameter]
  · intro position
    simp [preparedOracle, programCache_secret]

theorem preparedOracle_outside (fallback : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material)
    (input : HashInput) (hnot : ¬SeedGuess.SeedHit input seed) :
    preparedOracle fallback seed material input = fallback input := by
  rw [preparedOracle, programCache_agreeOutside ∅ seed material input hnot]
  rfl

theorem preparedOracle_verifier (fallback : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material)
    (p : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    preparedOracle fallback seed material (tweakableHashInput p domain payload) =
      fallback (tweakableHashInput p domain payload) := by
  rw [preparedOracle, programCache_verifier]
  rfl

/-- Parameter derivation reads its full sampled answer at `P=0`, then keeps the low128bits. -/
theorem eval_parameter_prepared (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material)
    (h : PreparedAgreement f seed material) :
    evalWithAnswerFn f (deriveKey 0 .parameter seed : OracleComp HashSpec Digest) = parameter material := by
  rw [Completeness.eval_deriveKey]
  exact congrArg truncateHash h.1

/-- Every OTS/FORS/surrogate derivation reads the sampled table at the actual public parameter. -/
theorem eval_secret_prepared (f : QueryImpl HashSpec Id) (seed : MasterSeed) (material : Material)
    (h : PreparedAgreement f seed material) (position : SecretPosition) :
    evalWithAnswerFn f (deriveKey (parameter material) (secretDomain position) seed :
      OracleComp HashSpec Digest) = truncateHash (material.2 position) := by
  rw [Completeness.eval_deriveKey]
  exact congrArg truncateHash (h.2 position)

/-- Ordinary tweakable hashes continue to use the supplied non-programmed oracle. -/
theorem eval_tweakableHash_prepared (fallback : QueryImpl HashSpec Id) (seed : MasterSeed)
    (material : Material) (p : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    evalWithAnswerFn (preparedOracle fallback seed material)
      (Concrete.tweakableHash p domain payload : OracleComp HashSpec Digest) =
      evalWithAnswerFn fallback (Concrete.tweakableHash p domain payload : OracleComp HashSpec Digest) := by
  rw [Completeness.eval_tweakableHash, Completeness.eval_tweakableHash, preparedOracle_verifier]

/-- Independently sampled seed and material can be exchanged before any later computation.
This says nothing about the distribution of a preexisting seeded-game cache. -/
theorem material_seed_swap {α : Type} (next : Material → MasterSeed → ProbComp α) :
    𝒟[sampleMaterial >>= fun material => sampleMasterSeed >>= next material] =
      𝒟[sampleMasterSeed >>= fun seed => sampleMaterial >>= fun material => next material seed] :=
  evalDist_bind_bind_swap _ _ _

end LeanSphincs.Security.SeedModel
