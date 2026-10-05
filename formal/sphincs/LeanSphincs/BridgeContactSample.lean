import LeanSphincs.BridgeContactA

/-! One-sample facts for the FORS contact bounds A4a and A4b: the sampled model parses FORS rows
only from FORS leaf inputs and parses no message-digest block, and the prepared cache holds no FORS
leaf input. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

section Sample

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- The sampled model parses FORS rows only from FORS leaf inputs. -/
theorem ftsRows_sampleModel (parameterOutput : HashOutput) (highs : CoordinateHighs) :
    FtsRows (truncateHash parameterOutput) (sampleModel parameterOutput highs) := by
  intro x a v i t l hp hi
  rw [sampleModel_parse] at hp
  rw [sampleModel_incoming] at hi
  obtain ⟨rfl, -⟩ := (parse_some_iff _ _ x (a, v)).mp hp
  cases a with
  | chain lay tree leaf chainIdx step => simp [Address.inputCoordinate] at hi
  | ftsLeaf i' t' l' =>
      simp only [Address.inputCoordinate, Coordinate.ftsSecret.injEq] at hi
      obtain ⟨rfl, rfl, rfl⟩ := hi
      rfl

omit [Params] in
theorem fl_not_struct (parameter : PublicParameter) (position : Position) (hrow : ¬IsRowPosition position)
    (payload x : HashInput) (hx : IsFLInput x) : x ≠ tweakableHashInput parameter position.domain payload := by
  obtain ⟨p', i, t, l, payload', rfl⟩ := hx
  intro heq
  have htag := congrArg TweakFields.tag (tweakableInput_injective heq).1
  cases position <;> simp [IsRowPosition] at hrow <;> simp [Position.domain, hashDomainFields, tweakFields] at htag

/-- **The prepared cache holds no FORS leaf input.** -/
theorem prepared_cleanF (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining)) :
    ∀ x, IsFLInput x → prepared.2 x = none := by
  intro x hx
  have hrun : prepared ∈ support ((simulateQ (randomOracle (spec := HashSpec))
      (Concrete.sequenceFin fun leaf => ReferenceChoice.search (truncateHash parameterOutput) topLayer rootTree leaf
        ((sampleData parameterOutput fixed highs remaining).forsKey leaf) encodingAttemptLimit 0)).run
      (structCache (splitMaterial parameterOutput highs remaining fixed) (splitAnswers highs remaining fixed))) :=
    hprepared
  rw [randomOracle_run_avoid (P := IsFLInput) _
    (noQ_sequenceFin _ fun leaf => noQ_search (bad := IsFLInput) _ _ _ _ _
      (fun payload => not_fl_tweakable _ _ payload (by simp [hashDomainFields, tweakFields])) _ _) _ prepared hrun x hx]
  unfold structCache
  exact programGraphCache_empty_none _ _ _ _ _ x fun position hpos =>
    fl_not_struct _ position ((mem_graphOrder _ _).mp hpos).2 _ x hx

theorem prepared_cleanRows (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining)) :
    ∀ x a v i t l, (sampleModel parameterOutput highs).parse x = some (a, v) →
      (sampleModel parameterOutput highs).incoming a = .ftsSecret i t l → prepared.2 x = none := by
  intro x a v i t l hp hi
  rw [ftsRows_sampleModel parameterOutput highs x a v i t l hp hi]
  exact prepared_cleanF parameterOutput fixed highs remaining prepared hprepared _ (isFLInput_forsLeafInput _ i t l v)

theorem sampleModel_parse_blk (parameterOutput : HashOutput) (highs : CoordinateHighs) (data : PublicData)
    (p : Pair) (call : Fin 2) :
    (sampleModel parameterOutput highs).parse (pblk (truncateHash parameterOutput) data p call) = none := by
  rw [sampleModel_parse]
  exact parse_tweakable_none _ _ _ _ (fun address => by cases address <;> simp [Address.position, Position.domain])
    (by trivial)

end Sample

end LeanSphincs.Security.ForsPotential
