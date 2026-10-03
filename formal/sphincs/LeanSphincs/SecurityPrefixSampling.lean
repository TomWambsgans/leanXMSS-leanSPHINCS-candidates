import LeanSphincs.SecurityPrefixOracle
import SphincsSecurity.Proof.Base.UniformTableSplit

/-!
Exact independent sampling of one candidate WOTS secret and its prefix hash rows, adapted from
leanVM's OtsPrefixSecretSampling and OtsPrefixRawSampling. The finite table hypothesis explicitly
requires inclusion of every byte input in the selected prefix. These are distribution identities,
not claims that the actual signing transcript already hides the selected prefix.
-/

open OracleComp OracleSpec

namespace LeanSphincs.Security.Prefix
open SphincsSecurity.Concrete.UniformTableSplit

attribute [local instance] Classical.propDecidable

abbrev ChainAddress := Layer × TreeIndex × LeafIndex × ChainIndex
abbrev Secrets := ChainAddress → Digest

def address (segment : Segment) : ChainAddress :=
  (segment.lay, segment.tree, segment.leaf, segment.chainIdx)

noncomputable def replaceSecret (segment : Segment) (secrets : Secrets) (value : Digest) : Secrets :=
  Function.update secrets (address segment) value

theorem replaceSecret_self (segment : Segment) (secrets : Secrets) (value : Digest) :
    replaceSecret segment secrets value (address segment) = value := by simp [replaceSecret]

theorem replaceSecret_twice (segment : Segment) (secrets : Secrets) (first second : Digest) :
    replaceSecret segment (replaceSecret segment secrets first) second =
      replaceSecret segment secrets second := by simp [replaceSecret]

theorem replaceSecret_current (segment : Segment) (secrets : Secrets) :
    replaceSecret segment secrets (secrets (address segment)) = secrets := by simp [replaceSecret]

abbrev ErasedSecrets (segment : Segment) := {secrets : Secrets // secrets (address segment) = 0}

instance (segment : Segment) : Nonempty (ErasedSecrets segment) := ⟨⟨fun _ => 0, rfl⟩⟩

noncomputable def secretSplit (segment : Segment) : Secrets ≃ ErasedSecrets segment × Digest where
  toFun secrets := (⟨replaceSecret segment secrets 0, replaceSecret_self segment secrets 0⟩,
    secrets (address segment))
  invFun pair := replaceSecret segment pair.1.val pair.2
  left_inv secrets := (replaceSecret_twice segment secrets 0 _).trans (replaceSecret_current segment secrets)
  right_inv pair := by
    apply Prod.ext
    · apply Subtype.ext
      exact (replaceSecret_twice segment pair.1.val pair.2 0).trans
        (by simpa only [pair.1.property] using replaceSecret_current segment pair.1.val)
    · exact replaceSecret_self segment pair.1.val pair.2

/-- All other chain secrets may be exposed while this coordinate remains independently uniform. -/
theorem uniform_secrets (segment : Segment) :
    PMF.uniformOfFintype Secrets =
      (PMF.uniformOfFintype (ErasedSecrets segment)).bind (fun other =>
        (PMF.uniformOfFintype Digest).map (replaceSecret segment other.val)) := by
  have h := PMF.uniformOfFintype_map_of_bijective (secretSplit segment).symm
    (secretSplit segment).symm.bijective
  rw [uniform_product, PMF.map_bind] at h
  simpa only [PMF.map_comp, Function.comp_def, secretSplit, Equiv.coe_fn_symm_mk] using h.symm

/-- Prefix rows split into all low128-bit transition functions and all high128-bit strings. -/
noncomputable def splitRows (segment : Segment) :
    (Query segment → HashOutput) ≃
      (Fin segment.digit.val → Digest → Digest) × (Query segment → High) where
  toFun rows := (fun level value => truncateHash (rows (level, value)),
    fun query => (splitHashOutput digestBits (rows query)).2)
  invFun pair query := combine (pair.1 query.1 query.2) (pair.2 query)
  left_inv rows := funext fun query => combine_split (rows query)
  right_inv pair := Prod.ext
    (funext fun level => funext fun value => truncate_combine (pair.1 level value) (pair.2 (level, value)))
    (funext fun query => congrArg Prod.snd (split_combine (pair.1 query.1 query.2) (pair.2 query)))

theorem uniform_rows (segment : Segment) :
    PMF.uniformOfFintype (Query segment → HashOutput) =
      (PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)).bind (fun tables =>
        (PMF.uniformOfFintype (Query segment → High)).map
          (fun high query => combine (tables query.1 query.2) (high query))) := by
  have h := PMF.uniformOfFintype_map_of_bijective (splitRows segment).symm (splitRows segment).symm.bijective
  rw [uniform_product, PMF.map_bind] at h
  simpa only [PMF.map_comp, Function.comp_def, splitRows, Equiv.coe_fn_symm_mk] using h.symm

def tableCell (segment : Segment) (inputs : Finset HashInput)
    (hinputs : ∀ query, input segment query ∈ inputs) (query : Query segment) : inputs :=
  ⟨input segment query, hinputs query⟩

theorem tableCell_injective (segment : Segment) (inputs : Finset HashInput)
    (hinputs : ∀ query, input segment query ∈ inputs) :
    Function.Injective (tableCell segment inputs hinputs) := by
  intro left right heq
  exact input_injective segment (congrArg Subtype.val heq)

abbrev RemainingRows (segment : Segment) (inputs : Finset HashInput)
    (hinputs : ∀ query, input segment query ∈ inputs) :=
  SphincsSecurity.Concrete.UniformTableSplit.Outside (tableCell segment inputs hinputs) → HashOutput

noncomputable def joinFinite (segment : Segment) (inputs : Finset HashInput)
    (hinputs : ∀ query, input segment query ∈ inputs)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (remaining : RemainingRows segment inputs hinputs) : inputs → HashOutput :=
  SphincsSecurity.Concrete.UniformTableSplit.join
    (tableCell segment inputs hinputs) (tableCell_injective segment inputs hinputs)
    (fun query => combine (tables query.1 query.2) (high query)) remaining

theorem joinFinite_prefix (segment : Segment) (inputs : Finset HashInput)
    (hinputs : ∀ query, input segment query ∈ inputs)
    (tables : Fin segment.digit.val → Digest → Digest) (high : Query segment → High)
    (remaining : RemainingRows segment inputs hinputs) (query : Query segment) :
    joinFinite segment inputs hinputs tables high remaining (tableCell segment inputs hinputs query) =
      combine (tables query.1 query.2) (high query) :=
    SphincsSecurity.Concrete.UniformTableSplit.join_embed _ _ _ _ _

/-- The hidden transition tables are independent of all remaining rows and every high output
bit. The exact serialized prefix is selected by an injective map into the finite ROM table. -/
theorem uniform_finite_table (segment : Segment) (inputs : Finset HashInput)
    (hinputs : ∀ query, input segment query ∈ inputs) :
    PMF.uniformOfFintype (inputs → HashOutput) =
      (PMF.uniformOfFintype (Fin segment.digit.val → Digest → Digest)).bind (fun tables =>
        (PMF.uniformOfFintype (Query segment → High)).bind (fun high =>
          (PMF.uniformOfFintype (RemainingRows segment inputs hinputs)).map
            (joinFinite segment inputs hinputs tables high))) := by
  rw [SphincsSecurity.Concrete.UniformTableSplit.uniform_join (tableCell segment inputs hinputs)
    (tableCell_injective segment inputs hinputs), uniform_rows]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rfl

end LeanSphincs.Security.Prefix
