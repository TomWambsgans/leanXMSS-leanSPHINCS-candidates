import LeanSphincs.BridgeContactA

/-! A4a and A4b on the interpreted run of `costGameX` of an adversary that never repeats a message,
for one sample: the sampled model parses FORS rows only from FORS leaf inputs, the prepared cache
holds no FORS leaf input, and the keygen tick keeps the result, the reveals and the final state. -/

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

/-- The keygen tick keeps every event of the result, the reveals and the final state. -/
theorem costGameX_event (parameter : PublicParameter) (data : PublicData) {A : Type}
    (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
    (model : HiddenRows.Model HashInput HashOutput A Coordinate) (adversary : Adversary) (q : ℕ) (s : State)
    (E : Option HiddenBridge.Outcome → List Coordinate → State → Prop) (hE : ∀ R s, ¬E none R s) :
    Pr[fun out => E out.1.1 out.1.2.1 out.2 | interp tg initial model (costGameX parameter data adversary) q s] ≤
      Pr[fun out => E out.1.1 out.1.2.1 out.2 | interp tg initial model
        (advProg parameter data (adversary.main ⟨data.root, parameter⟩) []) (q - keygenCost) s] := by
  unfold costGameX
  by_cases hK : keygenCost ≤ q
  · rw [interp_tick_bind tg initial model _ _ q s hK, probEvent_map, costRestX_eq]
    exact le_rfl
  · rw [interp_tick_bind_abort tg initial model _ _ q s hK, probEvent_pure, if_neg (hE _ _)]
    exact zero_le

/-- **Theorem (a), one sample.** On the interpreted run of `costGameX` of an adversary that never
repeats a message, the run finishes with a valid transcript and a contact made at an unknown
secret is at a revealed leaf with probability at most `x (N 2^-b 2^-10 + y wbar landing)`, with
`y = q - keygenCost` and `x = y 2^-128`, for any leaf-value knowledge `K`. -/
theorem a4a_bound_game (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) (hmsg : ∀ x, IsMsgInput x → tg.kind x = .none)
    (K : HiddenReveal.Knowledge Coordinate) (wbar : ℝ≥0∞) (hfair : Fair wbar (q - keygenCost + digestAttemptLimit))
    (known : Knowledge Coordinate) :
    Pr[A4aRun (truncateHash parameterOutput) K | interp tg prepared.2 (sampleModel parameterOutput highs)
        (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
          (internalize adversary)) q (DebtState.start prepared.2 known)] ≤
      (((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) *
        (signatureLimit * matchRate + (q - keygenCost : ℕ) * (wbar * landing)) := by
  set param := truncateHash parameterOutput with hparam
  set data := sampleData parameterOutput fixed highs remaining with hdata
  refine le_trans (costGameX_event param data tg prepared.2 (sampleModel parameterOutput highs) (internalize adversary)
    q _ (fun o R s => ∃ outcome, o = some outcome ∧ SigningTranscript.Valid outcome.2.1 ∧ A4a param K s R)
    (fun R s ⟨_, h, _⟩ => by cases h)) ?_
  exact a4a_bound param data K wbar tg prepared.2 (sampleModel parameterOutput highs)
    (sampleModel_parse_blk parameterOutput highs data)
    (fun p call => hmsg _ (msgInput_digestInput param data.root p.1 p.2 call))
    (fun p call => prepared_clean parameterOutput fixed highs remaining prepared hprepared _
      (msgInput_digestInput param data.root p.1 p.2 call))
    (ftsRows_sampleModel parameterOutput highs)
    (prepared_cleanRows parameterOutput fixed highs remaining prepared hprepared) (q - keygenCost) hfair _
    (noRepeat_internalize_adversary adversary hnr _) known

/-- **Theorem (b), one sample.** On the interpreted run of `costGameX` of an adversary that never
repeats a message, the run finishes with a valid transcript and A4b holds with probability at most
`x · potNear(start)`, `potNear(start) = y (startNear + φ) + N φ`, `φ` the failing mass of the
prepared encodings, for any leaf-value knowledge `K`. -/
theorem a4b_bound_game (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) (hmsg : ∀ x, IsMsgInput x → tg.kind x = .none)
    (K : HiddenReveal.Knowledge Coordinate) (wbar : ℝ≥0∞) (hfair : Fair wbar (q - keygenCost + digestAttemptLimit))
    (known : Knowledge Coordinate) :
    Pr[A4bRun (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining) K |
        interp tg prepared.2 (sampleModel parameterOutput highs)
          (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
            (internalize adversary)) q (DebtState.start prepared.2 known)] ≤
      (((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) *
        ((q - keygenCost : ℕ) * (startNear wbar (q - keygenCost) + failMass (failSet prepared.1)) +
          signatureLimit * failMass (failSet prepared.1)) := by
  set param := truncateHash parameterOutput with hparam
  set data := sampleData parameterOutput fixed highs remaining with hdata
  refine le_trans (costGameX_event param data tg prepared.2 (sampleModel parameterOutput highs) (internalize adversary)
    q _ (fun o R s => ∃ outcome, o = some outcome ∧ SigningTranscript.Valid outcome.2.1 ∧ A4b param data K s outcome.2.1 R)
    (fun R s ⟨_, h, _⟩ => by cases h)) ?_
  exact a4b_bound param data K wbar (failSet prepared.1) tg prepared.2 (sampleModel parameterOutput highs)
    (sampleModel_parse_blk parameterOutput highs data)
    (fun p call => hmsg _ (msgInput_digestInput param data.root p.1 p.2 call))
    (fun p call => prepared_clean parameterOutput fixed highs remaining prepared hprepared _
      (msgInput_digestInput param data.root p.1 p.2 call))
    (ftsRows_sampleModel parameterOutput highs)
    (prepared_cleanRows parameterOutput fixed highs remaining prepared hprepared)
    (fun m ρ digest budget s1 hprep out hout hnone => finishRest_fail parameterOutput fixed highs remaining prepared
      hprepared tg m ρ digest budget s1 hprep out hout hnone) (q - keygenCost) hfair _
    (noRepeat_internalize_adversary adversary hnr _) known

end Sample

end LeanSphincs.Security.ForsPotential
