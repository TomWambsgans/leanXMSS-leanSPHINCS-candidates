import LeanSphincs.SecurityCacheMatch
import LeanSphincs.SecurityDomains

/-!
One structural target per exact serialized tweak. A canonical input is excluded from its own
target set; a surrogate target has no canonical input at the off-path node address. The table is
an explicit fixed reference: coupling a complete candidate graph to this table is separate.
-/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.TargetAssignment

open Concrete Completeness

attribute [local instance] Classical.propDecidable

def atFields (parameter : PublicParameter) (input : HashInput) (fields : TweakFields) : Prop :=
  ∃ payload, input = fieldBytes fields ++ bytesLE 16 parameter ++ payload

theorem atFields_unique (parameter : PublicParameter) (input : HashInput)
    {left right : TweakFields} (hl : atFields parameter input left)
    (hr : atFields parameter input right) : left = right := by
  obtain ⟨l, hl⟩ := hl
  obtain ⟨r, hr⟩ := hr
  exact (fieldInput_injective (hl.symm.trans hr)).1

noncomputable def parseFields (parameter : PublicParameter) (input : HashInput) : Option TweakFields :=
  if h : ∃ fields, atFields parameter input fields then some h.choose else none

theorem parseFields_some_iff (parameter : PublicParameter) (input : HashInput) (fields : TweakFields) :
    parseFields parameter input = some fields ↔ atFields parameter input fields := by
  rw [parseFields]
  split
  · rename_i h
    rw [Option.some.injEq]
    constructor
    · rintro rfl; exact h.choose_spec
    · intro hf; exact atFields_unique parameter input h.choose_spec hf
  · rename_i h
    constructor
    · intro heq; cases heq
    · intro hf; exact False.elim (h ⟨fields, hf⟩)

theorem parseFields_tweakable (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    parseFields parameter (tweakableHashInput parameter domain payload) =
      some (hashDomainFields domain) :=
  (parseFields_some_iff _ _ _).2 ⟨payload, rfl⟩

structure Entry where
  canonicalInput : Option HashInput
  value : Digest

abbrev Table := TweakFields → Option Entry

noncomputable def targets (parameter : PublicParameter) (table : Table) (input : HashInput) : Finset Digest :=
  match parseFields parameter input with
  | none => ∅
  | some fields => match table fields with
    | none => ∅
    | some entry => if entry.canonicalInput = some input then ∅ else {entry.value}

theorem targets_card_le_one (parameter : PublicParameter) (table : Table) (input : HashInput) :
    (targets parameter table input).card ≤ 1 := by
  rw [targets]
  split
  · simp
  · split
    · simp
    · split <;> simp

theorem targets_at_entry (parameter : PublicParameter) (table : Table) (domain : HashDomain)
    (payload : HashInput) (entry : Entry) (hentry : table (hashDomainFields domain) = some entry) :
    targets parameter table (tweakableHashInput parameter domain payload) =
      if entry.canonicalInput = some (tweakableHashInput parameter domain payload) then ∅ else {entry.value} := by
  simp only [targets, parseFields_tweakable, hentry]

theorem canonical_input_excluded (parameter : PublicParameter) (table : Table) (input : HashInput)
    (fields : TweakFields) (entry : Entry) (hfields : atFields parameter input fields)
    (hentry : table fields = some entry) (hcanonical : entry.canonicalInput = some input) :
    targets parameter table input = ∅ := by
  simp only [targets, (parseFields_some_iff parameter input fields).2 hfields, hentry,
    hcanonical, ↓reduceIte]

/-- Any cached distinct-input structural match is a cached target hit for this reference table. -/
theorem distinct_match_bad (parameter : PublicParameter) (table : Table) (cache : QueryCache HashSpec)
    (domain : HashDomain) (payload canonical : HashInput) (value : Digest) (answer : HashOutput)
    (hentry : table (hashDomainFields domain) = some ⟨some canonical, value⟩)
    (hne : tweakableHashInput parameter domain payload ≠ canonical)
    (hcache : cache (tweakableHashInput parameter domain payload) = some answer)
    (hvalue : truncateHash answer = value) : CacheMatch.Bad (targets parameter table) cache := by
  refine ⟨_, answer, hcache, ?_⟩
  rw [targets_at_entry parameter table domain payload _ hentry]
  simp only [Option.some.injEq, if_neg (Ne.symm hne), Finset.mem_singleton]
  exact hvalue

/-- Surrogates are targets with no exempt canonical node input at their address. -/
theorem surrogate_match_bad (parameter : PublicParameter) (table : Table) (cache : QueryCache HashSpec)
    (domain : HashDomain) (payload : HashInput) (value : Digest) (answer : HashOutput)
    (hentry : table (hashDomainFields domain) = some ⟨none, value⟩)
    (hcache : cache (tweakableHashInput parameter domain payload) = some answer)
    (hvalue : truncateHash answer = value) : CacheMatch.Bad (targets parameter table) cache := by
  refine ⟨_, answer, hcache, ?_⟩
  rw [targets_at_entry parameter table domain payload _ hentry]
  simpa using hvalue

theorem counted_structural_target_bound {α : Type} (parameter : PublicParameter) (table : Table)
    (oa : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (hclean : ¬CacheMatch.Bad (targets parameter table) cache) (q : Nat)
    (hbound : ∀ result ∈ support (countedRun oa cache), result.1.2 ≤ q) :
    Pr[fun result => CacheMatch.Bad (targets parameter table) result.2 |
      (simulateQ romImpl oa).run cache] ≤ (q : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 128 := by
  simpa using CacheMatch.counted_program_bound (targets parameter table) 1
    (targets_card_le_one parameter table) oa cache hclean q hbound

end LeanSphincs.Security.TargetAssignment
