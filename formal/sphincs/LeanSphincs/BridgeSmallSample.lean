import LeanSphincs.BridgeAssemblyA
import LeanSphincs.BridgePotentialA8
import LeanSphincs.BridgeContactBound
import LeanSphincs.H0SplitCert
import LeanSphincs.BridgeContactHalf

/-! Pieces of the one-sample bound of the small-budget route, on the stopped experiment with the
above-word values exposed: flagged touches are digest queries, and the refined bad event of a final
state splits pointwise into the payoff of the linear potential (guesses, first-order hits, WOTS
second-order events, FORS pairs), the two FORS contact events and a FORS cover. `BridgeArmSmall`
assembles the sample bound. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
open HiddenBridge PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

open Completeness SeedModel Graph Assembly Reduce Internalize in
attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-! ### Flagged touches are digest queries -/

section Flagged

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
variable (tg : Targeting D R ι) (initial : HiddenOutside.Cache D R) (model : HiddenRows.Model D R A ι)

omit [Params] [Fintype ι] [SampleableType R] in
theorem flaggedCount_touch_le (state : DebtState D R ι) (input : (SourceCostSpec D R ι).Domain) :
    flaggedCount tg (touch tg initial state input) ≤ digestCount tg (recorded input) := by
  rcases input with (draw | (bytes | coordinate)) | amount
  · simp [touch, flaggedCount, recorded, digestCount]
  · by_cases hd : tg.digest bytes
    · simp only [touch, flaggedCount, recorded, digestCount, hd, List.filter_cons, List.filter_nil]
      split_ifs <;> simp_all
    · simp [touch, flaggedCount, recorded, digestCount, hd]
  · simp [touch, flaggedCount, recorded, digestCount]
  · simp [touch, flaggedCount, recorded, digestCount]

omit [Params] [Fintype ι] in
/-- Every flagged touch of a run is a recorded digest query. -/
theorem flagged_le_digest {α : Type} (comp : OracleComp (SourceCostSpec D R ι) α) :
    ∀ budget s, ∀ out ∈ support (interp tg initial model comp budget s),
      flaggedCount tg out.1.2.2.2 ≤ digestCount tg out.1.2.2.1 := by
  induction comp using OracleComp.inductionOn with
  | pure value =>
      intro budget s out hout
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      simp [flaggedCount, digestCount]
  | query_bind input next ih =>
      intro budget s out hout
      rw [interp_query_bind] at hout
      split_ifs at hout with hcost
      · rw [support_bind] at hout
        simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
        obtain ⟨result, hresult, inner, hinner, rfl⟩ := hout
        simp only [flaggedCount_append, digestCount_append]
        exact Nat.add_le_add (flaggedCount_touch_le tg initial s input) (ih result.1 _ _ inner hinner)
      · rw [support_pure, Set.mem_singleton_iff] at hout
        subst hout
        simp [flaggedCount, digestCount]

omit [Params] [Fintype ι] in
theorem expectedFlagged_le_digest {α : Type} (comp : OracleComp (SourceCostSpec D R ι) α) (budget : ℕ)
    (s : DebtState D R ι) :
    expectedFlagged tg initial model comp budget s ≤
      ∑' out, Pr[= out | interp tg initial model comp budget s] * (digestCount tg out.1.2.2.1 : ℝ≥0∞) := by
  unfold expectedFlagged
  refine ENNReal.tsum_le_tsum fun out => ?_
  by_cases hout : out ∈ support (interp tg initial model comp budget s)
  · exact mul_le_mul_right (by exact_mod_cast flagged_le_digest tg initial model comp budget s out hout) _
  · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]

end Flagged

/-! ### The pointwise split of the refined bad event -/

section Pointwise

open Completeness SeedModel Graph Assembly Reduce Internalize

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
  (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
  (known : Knowledge Coordinate)
  (hk : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
    (knownOf (truncateHash parameterOutput) fixed)))
  (ρ : ℝ) (adversary : Adversary) (q : ℕ)

include hprepared hk in
/-- **Pointwise split.** On a final state of the run and a completed table, a correct guess or the
refined bad event of a valid finished run is a payoff event of the linear potential, an event of a
FORS contact bound, or a cover without a decided hit. -/
theorem small_pointwise (out : Run HashInput Coordinate HiddenBridge.Outcome × State)
    (hout : out ∈ support (interp (targetingA parameterOutput fixed highs remaining prepared.1) prepared.2
      (sampleModel parameterOutput highs)
      (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
        (internalize adversary)) q (DebtState.start prepared.2 known)))
    (T : Coordinate → Digest) (hTe : tableExtending out.2.known T = T)
    (h : CorrectGuess T out.2 ∨ badAV parameterOutput fixed highs remaining prepared.1 T
      (((out.1.1, out.1.2.1), out.1.2.2.1), out.2.cache)) :
    payoffA parameterOutput fixed highs remaining prepared known ρ T out.2 = 1 ∨
      A4aRun (truncateHash parameterOutput) known out ∨
      A4bRun (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining) known out ∨
      finalValue (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
        (targetingA parameterOutput fixed highs remaining prepared.1) prepared.2 [] out = 1 := by
  set K := ctxA parameterOutput fixed highs remaining prepared known ρ with hK
  have hinv := inv_final parameterOutput fixed highs remaining prepared known ρ hk
    (targetingA parameterOutput fixed highs remaining prepared.1) _ q out hout
  have hfix := knownOf_extending_final (parameterOutput := parameterOutput) (fixed := fixed) (highs := highs)
    (prepared := prepared) (known := known) hk (tg := targetingA parameterOutput fixed highs remaining prepared.1)
    (comp := costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
      (internalize adversary)) (total := q) out hout T hTe
  have hpay : Hit K.tg prepared.2 T out.2 → payoffA parameterOutput fixed highs remaining prepared known ρ T out.2 = 1 := by
    intro hh
    unfold payoffA Ctx.payoff
    exact if_pos (Or.inl hh)
  -- leaf values of the exposed knowledge
  have hleaf : ∀ index tree leaf, known (.ftsValue index tree leaf) = some (K.leafValue index tree leaf) := by
    intro index tree leaf
    have hbase := (exposeR_known _ _ _ hk).1
    have hkn : knownOf (truncateHash parameterOutput) fixed (.ftsValue index tree leaf) ≠ none := by
      simp [knownOf, KnownCoordinate]
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hkn
    have hv' := hbase _ v hv
    simp only [hK, ctxA, Ctx.leafValue, hv', Option.getD_some]
  have hgr : ∀ index tree leaf, RecordedContactAt out.2 K index tree leaf →
      GRContact (truncateHash parameterOutput) known out.2 index tree leaf := by
    rintro index tree leaf ⟨secret, ⟨u, ⟨hc, -⟩, hu⟩, hg⟩
    exact ⟨secret, u, hc, hg, by rw [hleaf, hu]⟩
  rcases h with hg | ⟨hbad, outcome, hres, hvalid⟩
  · exact Or.inl (hpay (hit_of_correctGuess parameterOutput fixed highs remaining prepared known ρ out.2 T hTe hg))
  · rcases badA_split parameterOutput fixed highs remaining prepared hprepared known ρ out.2 hinv T hTe hfix
      out.1.1 out.1.2.1 out.1.2.2.1 hbad with hp | ⟨index, tree, leaf, hrev, hrec⟩ | ⟨outcome', hres', hnear | hcov⟩
    · exact Or.inl hp
    · refine Or.inr (Or.inl ⟨outcome, hres, hvalid, index, tree, leaf, hgr index tree leaf hrec, ?_⟩)
      simpa [revealedSet] using hrev
    · obtain ⟨hv, digest, hdig, hland, hunsigned, tree, hrec, hcov⟩ := hnear
      exact Or.inr (Or.inr (Or.inl ⟨outcome', hres', hv, _, tree, _, hgr _ tree _ hrec,
        outcome'.1.message, outcome'.1.signature.randomness, digest, hdig, hland, hunsigned, rfl, rfl, hcov⟩))
    · by_cases hreal : Realized K.tg prepared.2 out.2
      · exact Or.inl (hpay (Or.inl hreal))
      · refine Or.inr (Or.inr (Or.inr ?_))
        unfold finalValue
        rw [hres']
        simp only [Option.elim, List.nil_append]
        exact if_pos ⟨hcov, hreal⟩

end Pointwise

/-! ### Helpers for one sample -/

section SampleS

open Completeness SeedModel Graph Assembly Reduce Internalize

theorem targetingA_msg (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (results : Index → Option (Counter × Encoding)) (x : HashInput)
    (h : IsMsgInput x) : (targetingA parameterOutput fixed highs remaining results).kind x = .none := by
  show (if SecondOrderInput (truncateHash parameterOutput) results x then .none
    else sampleKind parameterOutput fixed highs remaining results x) = .none
  split_ifs
  · rfl
  · exact sampleTargeting_msg parameterOutput fixed highs remaining results x h

omit [Params] in
theorem numeric_mono {ρ x x' : ℝ} (h : Numeric ρ x) (hx : x' ≤ x) (_hx0 : 0 ≤ x') : Numeric ρ x' where
  low := h.low
  high := h.high
  enc := by
    have h1 := h.enc
    have h2 : 0 ≤ 2 - ρ := by linarith [h.high]
    have h3 : (2 - ρ) * x' ≤ (2 - ρ) * x := mul_le_mul_of_nonneg_left hx h2
    nlinarith
  contact := by have := h.contact; linarith
  small := by have := h.small; linarith

omit [Params] in
/-- The probability of an event of the completed table is at most the expected payoff when the
event forces the payoff to one. -/
theorem probEvent_le_endValue (payoff : (Coordinate → Digest) → State → ℝ≥0∞) (s : State)
    (E : (Coordinate → Digest) → Prop) (h : ∀ T, E T → payoff T s = 1) :
    Pr[E | completion s.known] ≤ endValue payoff s := by
  rw [probEvent_eq_tsum_ite]
  unfold endValue
  refine ENNReal.tsum_le_tsum fun T => ?_
  split_ifs with hT
  · rw [h T hT, mul_one]
  · exact bot_le

end SampleS

end LeanSphincs.Security.ForsPotential
