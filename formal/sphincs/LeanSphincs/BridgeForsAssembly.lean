import LeanSphincs.BridgeForsGame
import LeanSphincs.BridgeReplay

/-! Saturation and the FORS potential on the same lazy run: a decided hit, or a FORS cover
without one, costs at most the saturation budget plus the potential of the start. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

section Rest

variable (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A FORS cover of a completed run. -/
def CoverOf (out : Run HashInput Coordinate HiddenBridge.Outcome × State) : Prop :=
  ∃ outcome, out.1.1 = some outcome ∧
    HiddenBridge.ForsCover parameter data.root outcome out.1.2.1 out.2.cache

theorem start_pinv (hclean : ∀ p call, initial (pblk parameter data p call) = none) (known : Knowledge Coordinate) :
    PInv parameter data (DebtState.start initial known) [] := by
  refine ⟨List.nodup_nil, fun p => ?_, fun p ⟨u, hu, _⟩ => ?_, fun p _ => hclean p 1⟩
  · constructor
    · intro h; cases h
    · rintro ⟨u, hu, _⟩
      change initial (pblk parameter data p 0) = some u at hu
      rw [hclean p 0] at hu; cases hu
  · change initial (pblk parameter data p 0) = some u at hu
    rw [hclean p 0] at hu; cases hu

theorem start_count (hclean : ∀ p call, initial (pblk parameter data p call) = none) (known : Knowledge Coordinate)
    (budget : ℕ) : CountInv parameter data budget (DebtState.start initial known) budget := by
  intro m
  have : cachedCount parameter data m (DebtState.start initial known) = 0 := by
    unfold cachedCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro ρ _ h
    exact h (hclean (m, ρ) 0)
  rw [this, zero_add]

theorem start_prepared (known : Knowledge Coordinate) : Prepared initial (DebtState.start initial known) :=
  fun _ _ h => h

/-- **Hits and FORS covers of the rest of the game.** -/
theorem rest_bound (hcompat : Compatible tg model) (htrunc : UniformTruncation (R := HashOutput) tg)
    (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hclean : ∀ p call, initial (pblk parameter data p call) = none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (total : ℕ) (htotal : 2 * (total : ℝ) + 2 ≤ spaceReal)
    (hfair : Fair wbar (total + digestAttemptLimit))
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (known : Knowledge Coordinate) :
    Pr[fun r => Hit tg initial r.1 r.2.2 ∨ CoverOf parameter data r.2 |
        interp tg initial model (advProg parameter data M []) total (DebtState.start initial known) >>= fun result =>
          (fun table => (table, result)) <$> completion result.2.known] ≤
      (1 - budget 0 total) + (total * (hValue parameter data wbar (baseline total) (DebtState.start initial known) []
        0 signatureLimit total + failMass Fail) + signatureLimit * failMass Fail) := by
  set start := DebtState.start initial known (D := HashInput) (R := HashOutput) (ι := Coordinate) with hstart
  set b0 := baseline total with hb0def
  have hb0 : b0 ≠ ⊤ := ENNReal.ofReal_ne_top
  -- the FORS potential
  have hgood := good_advProg parameter data wbar b0 Fail total tg initial model hparse hkind hdigest hfail hfair hb0
    le_rfl M [] total start [] 0 [] (start_prepared initial known) (start_pinv parameter data initial hclean known)
    (fun i t l h => by cases h) (start_count parameter data initial hclean known total)
  -- saturation
  have hsat := interp_hit_bound tg initial model hcompat htrunc total (by linarith) b0
    (baseline_payment total (by linarith)) (advProg parameter data M []) known
  -- a cover without a decided hit is a final value
  have hcover : Pr[fun r => Hit tg initial r.1 r.2.2 ∨ CoverOf parameter data r.2 |
      interp tg initial model (advProg parameter data M []) total start >>= fun result =>
        (fun table => (table, result)) <$> completion result.2.known] ≤
      Pr[fun r => Hit tg initial r.1 r.2.2 |
        interp tg initial model (advProg parameter data M []) total start >>= fun result =>
          (fun table => (table, result)) <$> completion result.2.known] +
      ∑' out, Pr[= out | interp tg initial model (advProg parameter data M []) total start] *
        finalValue parameter data tg initial [] out := by
    calc _ = Pr[fun r => Hit tg initial r.1 r.2.2 ∨ (CoverOf parameter data r.2 ∧ ¬Hit tg initial r.1 r.2.2) |
          interp tg initial model (advProg parameter data M []) total start >>= fun result =>
            (fun table => (table, result)) <$> completion result.2.known] :=
          probEvent_congr' (fun r _ => by tauto) rfl
      _ ≤ _ := probEvent_or_le _ _ _
      _ ≤ _ := by
          refine add_le_add le_rfl ?_
          rw [probEvent_bind_eq_tsum]
          refine ENNReal.tsum_le_tsum fun out => mul_le_mul_right ?_ _
          rw [probEvent_map]
          by_cases hc : CoverOf parameter data out ∧ ¬Realized tg initial out.2
          · obtain ⟨⟨outcome, hres, hfc⟩, hreal⟩ := hc
            have h1 : finalValue parameter data tg initial [] out = 1 := by
              unfold finalValue
              rw [hres]
              simp only [Option.elim, List.nil_append]
              rw [if_pos ⟨hfc, hreal⟩]
            rw [h1]
            exact probEvent_le_one
          · refine le_of_eq_of_le (probEvent_eq_zero fun table _ hp => hc ⟨hp.1, fun hr => hp.2 (Or.inl hr)⟩) bot_le
  calc _ ≤ _ := hcover
    _ ≤ Pr[fun r => Hit tg initial r.1 r.2.2 |
          interp tg initial model (advProg parameter data M []) total start >>= fun result =>
            (fun table => (table, result)) <$> completion result.2.known] +
        (pot parameter data wbar b0 Fail tg initial start [] [] 0 total +
          b0 * expectedFlagged tg initial model (advProg parameter data M []) total start) := add_le_add le_rfl hgood
    _ = (b0 * expectedFlagged tg initial model (advProg parameter data M []) total start +
          Pr[fun r => Hit tg initial r.1 r.2.2 |
            interp tg initial model (advProg parameter data M []) total start >>= fun result =>
              (fun table => (table, result)) <$> completion result.2.known]) +
        pot parameter data wbar b0 Fail tg initial start [] [] 0 total := by ring
    _ ≤ _ := by
        refine add_le_add hsat ?_
        refine le_trans (pot_le_core wbar b0 Fail tg initial start [] [] 0 total) (le_of_eq ?_)
        unfold core
        simp

end Rest

section Tick

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A leading tick only shortens the budget. -/
theorem interp_tick_bind {β : Type} (amount : ℕ) (next : Unit → OracleComp CostSpec β) (budget : ℕ) (s : State)
    (h : amount ≤ budget) :
    interp tg initial model (HiddenCost.tick amount >>= next) budget s =
      (fun out => ((out.1.1, out.1.2.1, Sum.inr amount :: out.1.2.2.1, out.1.2.2.2), out.2)) <$>
        interp tg initial model (next ()) (budget - amount) s := by
  unfold HiddenCost.tick
  rw [interp_query_bind]
  split_ifs with hc
  · change (pure ((), s) : ProbComp _) >>= _ = _
    rw [pure_bind]
    rfl
  · exact absurd h hc

theorem interp_tick_bind_abort {β : Type} (amount : ℕ) (next : Unit → OracleComp CostSpec β) (budget : ℕ) (s : State)
    (h : ¬amount ≤ budget) :
    interp tg initial model (HiddenCost.tick amount >>= next) budget s = pure ((none, [], [], []), s) := by
  unfold HiddenCost.tick
  rw [interp_query_bind]
  split_ifs with hc
  · exact absurd hc h
  · rfl

/-- No hit is decided at the start, and nothing is owed. -/
theorem not_hit_start (known : Knowledge Coordinate) (table : Coordinate → Digest) :
    ¬Hit tg initial table (DebtState.start initial known) := by
  rintro (hr | ⟨c, _, hc⟩)
  · rcases hr with ⟨input, output, value, hcache, hinit, _, _⟩ | ⟨c, v, _, hv⟩
    · change initial input = some output at hcache
      rw [hcache] at hinit; cases hinit
    · rw [debts_start] at hv; exact hv
  · rw [debts_start] at hc; exact hc

end Tick

section Chain

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

theorem agrees_iff_extending (known : Knowledge Coordinate) (table : Coordinate → Digest) :
    Agrees known table ↔ tableExtending known table = table := by
  constructor
  · intro h
    funext c
    simp only [tableExtending]
    cases hc : known c with
    | none => rfl
    | some v => exact (h c v hc).symm
  · intro h c v hc
    rw [← h]
    simp [tableExtending, hc]

theorem agrees_of_completion (known : Knowledge Coordinate) (table : Coordinate → Digest)
    (h : table ∈ support (completion known)) : Agrees known table := by
  unfold completion at h
  rw [support_map] at h
  obtain ⟨t, _, rfl⟩ := h
  exact fun c v hc => completion_known known c v hc t

/-- The weakened bad event of one table. -/
def badFor (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (results : Index → Option (Counter × Encoding)) (table : Coordinate → Digest)
    (v : ((Option HiddenBridge.Outcome × List Coordinate) × List (Entry HashInput)) × QueryCache HashSpec) : Prop :=
  CacheMatch.Bad (TargetAssignment.targets (truncateHash parameterOutput)
      (compTable parameterOutput fixed highs remaining table results)) v.2 ∨
    ∃ outcome, v.1.1.1 = some outcome ∧
      ForsCover (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining).root outcome v.1.1.2 v.2

/-- One table: the stopped run against the comparison run. -/
theorem stopped_table_le (hb : 0 < subtreeHeight) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (table : Coordinate → Digest) (hagree : Agrees (knownOf (truncateHash parameterOutput) fixed) table) :
    Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stopped (sampleModel parameterOutput highs) table
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining))))
        (knownOf (truncateHash parameterOutput) fixed) prepared.2] ≤
      Pr[fun r => CorrectGuess table r.2 ∨
          badFor parameterOutput fixed highs remaining prepared.1 table (r.1, r.2.cache) |
        fixedRun (sampleModel parameterOutput highs) table
          (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining))))
          (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed))] := by
  have htable := (agrees_iff_extending _ table).1 hagree
  refine le_trans (probEvent_mono fun r hr hwin => ?_)
    (stopped_le_fixedRun (sampleModel parameterOutput highs) table _ _
      (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) hagree)
  rcases r with _ | ⟨⟨⟨res, reveals⟩, entries⟩, cacheF⟩
  · trivial
  · obtain ⟨outcome, hres, hw⟩ := hwin
    simp only at hres
    subst hres
    rcases win_implies_bad hb adversary q hq parameterOutput fixed highs remaining prepared hprepared table htable
      outcome reveals entries cacheF hr hw with h | h
    · exact Or.inl h
    · exact Or.inr ⟨outcome, rfl, h⟩

set_option maxRecDepth 100000 in
/-- **From the stopped experiment to the interpreted run.** -/
theorem stopped_le_interp (hb : 0 < subtreeHeight) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) :
    Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining))))
        (knownOf (truncateHash parameterOutput) fixed) prepared.2] ≤
      Pr[fun x => CorrectGuess x.1 x.2.2 ∨
          badFor parameterOutput fixed highs remaining prepared.1 x.1 (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2.cache) |
        interp tg prepared.2 (sampleModel parameterOutput highs)
          (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
            (internalize adversary)) q (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) >>=
          fun result => (fun table => (table, result)) <$> completion result.2.known] := by
  unfold HiddenOutside.stoppedExperiment
  rw [probEvent_bind_eq_tsum]
  calc _ ≤ ∑' table, Pr[= table | completion (knownOf (truncateHash parameterOutput) fixed)] *
        Pr[fun r => CorrectGuess table r.2 ∨
            badFor parameterOutput fixed highs remaining prepared.1 table (r.1, r.2.cache) |
          fixedRun (sampleModel parameterOutput highs) table
            (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining))))
            (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed))] := by
        refine ENNReal.tsum_le_tsum fun table => ?_
        by_cases htab : table ∈ support (completion (knownOf (truncateHash parameterOutput) fixed))
        · have hag : Agrees (knownOf (truncateHash parameterOutput) fixed) table := by
            unfold completion at htab
            rw [support_map] at htab
            obtain ⟨t, _, rfl⟩ := htab
            exact fun c v hc => completion_known _ c v hc t
          have := stopped_table_le hb adversary q hq parameterOutput fixed highs remaining prepared
            hprepared table hag
          exact mul_le_mul_right this _
        · rw [probOutput_eq_zero_of_not_mem_support htab, zero_mul, zero_mul]
    _ = Pr[fun x => CorrectGuess x.1 x.2.2 ∨
            badFor parameterOutput fixed highs remaining prepared.1 x.1 (x.2.1, x.2.2.cache) |
          withTable (fun table => fixedRun (sampleModel parameterOutput highs) table
            (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining))))
            (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)))
            (knownOf (truncateHash parameterOutput) fixed)] := by
        unfold withTable
        rw [probEvent_bind_eq_tsum]
        refine tsum_congr fun table => ?_
        rw [probEvent_map]
        rfl
    _ = Pr[fun x => CorrectGuess x.1 x.2.2 ∨
            badFor parameterOutput fixed highs remaining prepared.1 x.1 (x.2.1, x.2.2.cache) |
          lazyRun (sampleModel parameterOutput highs)
            (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
              (sampleData parameterOutput fixed highs remaining))))
            (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) >>= fun result =>
              (fun table => (table, result)) <$> completion result.2.known] :=
        probEvent_congr' (fun _ _ => Iff.rfl) (withTable_fixedRun _ _ _)
    _ = _ := by
        unfold richProgram
        rw [lazyRun_wrapped tg prepared.2]
        have hcomp : ((fun out : Run HashInput Coordinate HiddenBridge.Outcome × State =>
              (((out.1.1, out.1.2.1), out.1.2.2.1), out.2)) <$>
            interp tg prepared.2 (sampleModel parameterOutput highs)
              (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
                (internalize adversary)) q (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed))) >>=
              (fun result => (fun table => (table, result)) <$> completion result.2.known) =
            (fun x : (Coordinate → Digest) × (Run HashInput Coordinate HiddenBridge.Outcome × State) =>
              (x.1, (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2))) <$>
            (interp tg prepared.2 (sampleModel parameterOutput highs)
              (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
                (internalize adversary)) q (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) >>=
              fun result => (fun table => (table, result)) <$> completion result.2.known) := by
          rw [bind_map_left, map_bind]
          refine bind_congr fun out => ?_
          rw [Functor.map_map]
        rw [hcomp, probEvent_map]
        rfl

/-- Keygen cost credited before the adversary runs. -/
abbrev keygenCost : ℕ := 258 * 2 ^ subtreeHeight + 2 * (totalHeight - subtreeHeight)

set_option maxRecDepth 100000 in
/-- **One sample.** -/
theorem sample_bound (hb : 0 < subtreeHeight) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate)
    (hhit : ∀ table, tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table →
      ∀ s : State, Prepared prepared.2 s → Agrees s.known table →
        (CorrectGuess table s ∨ CacheMatch.Bad (TargetAssignment.targets (truncateHash parameterOutput)
          (compTable parameterOutput fixed highs remaining table prepared.1)) s.cache) →
        Hit tg prepared.2 table s)
    (hcompat : Compatible tg (sampleModel parameterOutput highs)) (htrunc : UniformTruncation (R := HashOutput) tg)
    (hmsg : ∀ x, IsMsgInput x → tg.kind x = .none ∧ tg.digest x)
    (hclean : ∀ x, IsMsgInput x → prepared.2 x = none)
    (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared prepared.2 s1 →
      ∀ out ∈ support (interp tg prepared.2 (sampleModel parameterOutput highs)
        (finishRest (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining) m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (wbar : ℝ≥0∞) (htotal : 2 * ((q - keygenCost : ℕ) : ℝ) + 2 ≤ spaceReal)
    (hfair : Fair wbar (q - keygenCost + digestAttemptLimit)) :
    Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining))))
        (knownOf (truncateHash parameterOutput) fixed) prepared.2] ≤
      (1 - budget 0 (q - keygenCost)) + ((q - keygenCost : ℕ) * (hValue (truncateHash parameterOutput)
        (sampleData parameterOutput fixed highs remaining) wbar (baseline (q - keygenCost))
        (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) [] 0 signatureLimit
        (q - keygenCost) + failMass Fail) + signatureLimit * failMass Fail) := by
  set param := truncateHash parameterOutput with hparam
  set data := sampleData parameterOutput fixed highs remaining with hdata
  set known := knownOf param fixed with hknown
  set model := sampleModel parameterOutput highs with hmodel
  set start : State := DebtState.start prepared.2 known with hstart
  have hparse : ∀ p call, model.parse (pblk param data p call) = none := fun p call =>
    hcompat.digestParse _ (hmsg _ (msgInput_digestInput param data.root p.1 p.2 call)).2
  refine le_trans (stopped_le_interp hb adversary q hq parameterOutput fixed highs remaining prepared hprepared tg) ?_
  -- a correct guess or a bad cache is a decided hit
  refine le_trans (probEvent_mono (q := fun r => Hit tg prepared.2 r.1 r.2.2 ∨ CoverOf param data r.2)
    fun x hx hp => ?_) ?_
  · rw [mem_support_bind_iff] at hx
    obtain ⟨out, hout, hx⟩ := hx
    rw [support_map] at hx
    obtain ⟨table, htab, rfl⟩ := hx
    have hext := interp_extends tg prepared.2 model _ q start out hout
    have hag : Agrees out.2.known table := by
      unfold completion at htab
      rw [support_map] at htab
      obtain ⟨t, _, rfl⟩ := htab
      exact fun c v hc => completion_known _ c v hc t
    have hag0 : Agrees known table := fun c v hc => hag c v (hext.2.1 c v hc)
    rcases hp with hg | hbad | ⟨outcome, hres, hfc⟩
    · exact Or.inl (hhit table ((agrees_iff_extending known table).1 hag0) out.2
        (fun i o hi => hext.1 i o hi) hag (Or.inl hg))
    · exact Or.inl (hhit table ((agrees_iff_extending known table).1 hag0) out.2
        (fun i o hi => hext.1 i o hi) hag (Or.inr hbad))
    · exact Or.inr ⟨outcome, hres, hfc⟩
  -- the keygen tick
  unfold costGameX
  by_cases hK : keygenCost ≤ q
  · rw [interp_tick_bind tg prepared.2 model _ _ q start hK, bind_map_left]
    refine le_trans (le_of_eq ?_) (rest_bound param data wbar Fail tg prepared.2 model hcompat htrunc hparse
      (fun p call => (hmsg _ (msgInput_digestInput param data.root p.1 p.2 call)).1)
      (fun p call => (hmsg _ (msgInput_digestInput param data.root p.1 p.2 call)).2)
      (fun p call => hclean _ (msgInput_digestInput param data.root p.1 p.2 call)) hfail (q - keygenCost) htotal hfair
      ((internalize adversary).main ⟨data.root, param⟩) known)
    rw [costRestX_eq, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    refine tsum_congr fun out => ?_
    rw [probEvent_map, probEvent_map]
    rfl
  · rw [interp_tick_bind_abort tg prepared.2 model _ _ q start hK, pure_bind]
    refine le_of_eq_of_le (probEvent_eq_zero fun x hx hp => ?_) bot_le
    rw [support_map] at hx
    obtain ⟨table, _, rfl⟩ := hx
    rcases hp with hh | ⟨outcome, hres, _⟩
    · exact not_hit_start tg prepared.2 known table hh
    · cases hres

end Chain

/-! ### Failing indices of the prepared searches -/

section FailSet

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

omit [Params] in
theorem noQ_bind {bad : HashInput → Prop} [DecidablePred bad] {α β : Type} {oa : OracleComp HashSpec α}
    {next : α → OracleComp HashSpec β} (h : oa.IsQueryBoundP bad 0)
    (hnext : ∀ value, (next value).IsQueryBoundP bad 0) : (oa >>= next).IsQueryBoundP bad 0 := by
  have := isQueryBoundP_bind (n := 0) (m := 0) h (fun value _ => hnext value)
  simpa using this

/-- The encoding search queries only encoding inputs. -/
theorem noQ_search {bad : HashInput → Prop} [DecidablePred bad]
    (hbad : ∀ parameter lay tree leaf payload, ¬bad (tweakableHashInput parameter (.encoding lay tree leaf) payload))
    (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) :
    ∀ attempts start, (ReferenceChoice.search parameter lay tree leaf message attempts start :
      OracleComp HashSpec (Option (Counter × Encoding))).IsQueryBoundP bad 0
  | 0, _ => trivial
  | attempts + 1, start => by
      rw [ReferenceChoice.search]
      refine noQ_bind ?_ fun found => ?_
      · unfold Concrete.encode Concrete.tweakableHash
        refine noQ_bind (noQ_bind ?_ fun _ => trivial) fun _ => trivial
        simp only [oracleHash, HasQuery.query]
        rw [isQueryBoundP_query_iff]
        exact fun hm => absurd hm (hbad _ _ _ _ _)
      · cases found with
        | none => exact noQ_search hbad parameter lay tree leaf message attempts (start + 1)
        | some _ => trivial

/-- Encoding inputs are not hidden rows. -/
theorem not_row_encoding (parameterOutput : HashOutput) (highs : CoordinateHighs) (parameter : PublicParameter)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (payload : HashInput) :
    (sampleModel parameterOutput highs).parse (tweakableHashInput parameter (.encoding lay tree leaf) payload) = none := by
  rw [sampleModel_parse]
  cases h : HiddenGraph.parse (truncateHash parameterOutput) (candidateActive (truncateHash parameterOutput))
      (tweakableHashInput parameter (.encoding lay tree leaf) payload) with
  | none => rfl
  | some query =>
      obtain ⟨heq, _⟩ := (HiddenGraph.parse_some_iff _ _ _ query).1 h
      have hfields := (tweakableInput_injective heq).1
      have htag := congrArg TweakFields.tag hfields
      rcases query with ⟨address, value⟩
      cases address <;> simp [Address.position, Position.domain, hashDomainFields, tweakFields] at htag

/-- Every prepared search result was recorded inside the prepared cache. -/
theorem preparation_parts (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining)) (i : Index) :
    ∃ c0, ∃ r ∈ support ((simulateQ (randomOracle (spec := HashSpec))
        (ReferenceChoice.search (truncateHash parameterOutput) topLayer rootTree i
          ((sampleData parameterOutput fixed highs remaining).forsKey i) encodingAttemptLimit 0)).run c0),
      r.1 = prepared.1 i ∧ ∀ x v, r.2 x = some v → prepared.2 x = some v :=
  sequenceFin_parts (D := HashInput) (R := HashOutput)
    (fun leaf => ReferenceChoice.search (truncateHash parameterOutput) topLayer rootTree leaf
      ((sampleData parameterOutput fixed highs remaining).forsKey leaf) encodingAttemptLimit 0)
    (structCache (splitMaterial parameterOutput highs remaining fixed) (splitAnswers highs remaining fixed))
    prepared hprepared i

/-- Local indices of some index whose prepared search failed. -/
noncomputable def failSet (results : Index → Option (Counter × Encoding)) : Finset (Fin (2 ^ subtreeHeight)) :=
  Finset.univ.filter fun l => ∃ i : Index, ForsPotential.localIdx i = l ∧ results i = none

/-- **A failed final assembly is at a failing index.** -/
theorem finishRest_fail (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs)
    (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) (m : Message) (ρ : Randomness) (digest : MessageDigest)
    (budget : ℕ) (s1 : State) (hprep : Prepared prepared.2 s1)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg prepared.2 (sampleModel parameterOutput highs)
      (finishRest (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining) m ρ digest) budget s1))
    (hnone : out.1.1 = some none) :
    (Lifetime.localDigestView digest).1 ∈ failSet prepared.1 := by
  set model := sampleModel parameterOutput highs
  rw [localDigestView_fst]
  unfold failSet
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, digestIndex digest, rfl, ?_⟩
  unfold finishRest at hout
  obtain ⟨o1, ho1, h1⟩ := interp_bind_mem tg prepared.2 model _ _ budget s1 out hout
  rcases h1 with ⟨_, hn, _⟩ | ⟨_, _, o2, ho2, hres2, _, _⟩
  · rw [hnone] at hn; cases hn
  have hext1 := interp_extends tg prepared.2 model _ budget s1 o1 ho1
  obtain ⟨o3, ho3, h3⟩ := interp_bind_mem tg prepared.2 model _ _ _ _ o2 ho2
  rcases h3 with ⟨_, hn, _⟩ | ⟨found, hfound, o4, ho4, hres4, _, _⟩
  · rw [hres2, hn] at hnone; cases hnone
  -- the search returned nothing
  have hfnone : found = none := by
    rcases found with _ | ⟨counter, word⟩
    · rfl
    · exfalso
      have hmem := interp_result_mem tg prepared.2 model _ _ _ o4 ho4 none (by rw [← hres4, ← hres2, hnone])
      revert hmem
      dsimp only
      intro hmem
      refine post_bind (fun v => v ≠ none) _ (fun _ => post_bind _ _ fun _ => post_bind _ _ fun _ => ?_) none hmem rfl
      intro v hv
      rw [support_pure, Set.mem_singleton_iff] at hv
      rw [hv]
      exact fun h => by cases h
  subst hfnone
  -- the recorded search of the same index
  obtain ⟨c0, r, hr, hr1, hr2⟩ := preparation_parts parameterOutput fixed highs remaining prepared hprepared
    (digestIndex digest)
  have ho3' : o3 ∈ support (interp tg prepared.2 model
      (liftM (ReferenceChoice.search (truncateHash parameterOutput) topLayer rootTree (digestIndex digest)
        ((sampleData parameterOutput fixed highs remaining).forsKey (digestIndex digest)) encodingAttemptLimit 0) :
        OracleComp CostSpec _) (budget - traceCost o1.1.2.2.1) o1.2) := ho3
  have hrow := noQ_search (bad := fun x => model.parse x ≠ none)
    (fun parameter lay tree leaf payload h => h (not_row_encoding parameterOutput highs parameter lay tree leaf payload))
    (truncateHash parameterOutput) topLayer rootTree (digestIndex digest)
    ((sampleData parameterOutput fixed highs remaining).forsKey (digestIndex digest)) encodingAttemptLimit 0
  have hstep := interp_liftHash_replay (D := HashInput) (R := HashOutput) tg prepared.2 model
    (ReferenceChoice.search (truncateHash parameterOutput) topLayer rootTree (digestIndex digest)
      ((sampleData parameterOutput fixed highs remaining).forsKey (digestIndex digest)) encodingAttemptLimit 0 :
        OracleComp HashSpec (Option (Counter × Encoding)))
  have hreplay := hstep hrow c0 r hr _ o1.2 (fun x v hx => hext1.1 x v (hprep x v (hr2 x v hx))) o3 ho3' none hfound
  rw [← hr1, ← hreplay]

end FailSet

/-! ### All samples -/

section Total

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- The excess forecast of a new pair at the start of the run. -/
noncomputable def startExcess (wbar b0 : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtual Finset.univ wbar (excess b0) signatureLimit I 0) k []

theorem hValue_start (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (s : State) (k : ℕ) :
    hValue parameter data wbar b0 s [] 0 signatureLimit k = startExcess wbar b0 k := rfl

/-- A bound per sample, averaged. -/
theorem tsum_bound_le {α : Type} (mx : ProbComp α) (g : α → ℝ≥0∞) (A C : ℝ≥0∞) (φ : α → ℝ≥0∞)
    (h : ∀ x ∈ support mx, g x ≤ A + C * φ x) :
    ∑' x, Pr[= x | mx] * g x ≤ A + C * ∑' x, Pr[= x | mx] * φ x := by
  calc ∑' x, Pr[= x | mx] * g x ≤ ∑' x, Pr[= x | mx] * (A + C * φ x) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · exact mul_le_mul_right (h x hx) _
        · rw [probOutput_eq_zero_of_not_mem_support hx, zero_mul, zero_mul]
    _ = (∑' x, Pr[= x | mx]) * A + C * ∑' x, Pr[= x | mx] * φ x := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, mul_left_comm _ C, ENNReal.tsum_mul_left]
    _ ≤ A + C * ∑' x, Pr[= x | mx] * φ x := add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl

/-- Expected share of failing indices over the samples and their preparations. -/
noncomputable def expectedFail : ℝ≥0∞ :=
  ∑' parameterOutput, Pr[= parameterOutput | ($ᵗ HashOutput : ProbComp HashOutput)] *
  ∑' fixed, Pr[= fixed | ($ᵗ HiddenGraph.Table : ProbComp HiddenGraph.Table)] *
  ∑' highs, Pr[= highs | ($ᵗ CoordinateHighs : ProbComp CoordinateHighs)] *
  ∑' remaining, Pr[= remaining | ($ᵗ RemainingOutputs : ProbComp RemainingOutputs)] *
  ∑' prepared, Pr[= prepared | preparation parameterOutput fixed highs remaining] *
    failMass (failSet prepared.1)

/-- **The stage-1 bound on the forging advantage.** -/
theorem stage1_forge_bound (hb : 0 < subtreeHeight) (adversary : Adversary) (q : ℕ)
    (hbound : HasHashQueryBound adversary q) (hq : q < 2 ^ 256)
    (htarget : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) →
      ∃ tg : Targeting HashInput HashOutput Coordinate,
        Compatible tg (sampleModel parameterOutput highs) ∧ UniformTruncation (R := HashOutput) tg ∧
        (∀ x, IsMsgInput x → tg.kind x = .none ∧ tg.digest x) ∧
        ∀ table, tableExtending (knownOf (truncateHash parameterOutput) fixed) table = table →
          ∀ s : State, Prepared prepared.2 s → Agrees s.known table →
            (CorrectGuess table s ∨ CacheMatch.Bad (TargetAssignment.targets (truncateHash parameterOutput)
              (compTable parameterOutput fixed highs remaining table prepared.1)) s.cache) →
            Hit tg prepared.2 table s)
    (hclean : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) → ∀ x, IsMsgInput x → prepared.2 x = none)
    (wbar : ℝ≥0∞) (hfair : Fair wbar (q - keygenCost + digestAttemptLimit))
    (htotal : 2 * ((q - keygenCost : ℕ) : ℝ) + 2 ≤ spaceReal) :
    forgeAdvantage adversary ≤
      ((1 - budget 0 (q - keygenCost)) + (q - keygenCost : ℕ) * startExcess wbar (baseline (q - keygenCost))
        (q - keygenCost)) +
      ((q - keygenCost : ℕ) + signatureLimit) * expectedFail + q / (2 : ℝ≥0∞) ^ 256 := by
  refine le_trans (forgeAdvantage_le_prep adversary q hbound) (add_le_add ?_ le_rfl)
  set A := (1 - budget 0 (q - keygenCost)) + (q - keygenCost : ℕ) * startExcess wbar (baseline (q - keygenCost))
    (q - keygenCost) with hA
  set C : ℝ≥0∞ := ((q - keygenCost : ℕ) + signatureLimit) with hC
  -- one sample
  have hsample : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) →
      Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining))))
          (knownOf (truncateHash parameterOutput) fixed) prepared.2] ≤ A + C * failMass (failSet prepared.1) := by
    intro parameterOutput fixed highs remaining prepared hprepared
    obtain ⟨tg, hcompat, htrunc, hmsg, hhit⟩ := htarget parameterOutput fixed highs remaining prepared hprepared
    refine le_trans (sample_bound hb adversary q hq parameterOutput fixed highs remaining prepared hprepared tg hhit
      hcompat htrunc hmsg (hclean _ _ _ _ _ hprepared) (failSet prepared.1)
      (fun m ρ digest budget s1 hprep out hout hnone => finishRest_fail parameterOutput fixed highs remaining prepared
        hprepared tg m ρ digest budget s1 hprep out hout hnone) wbar htotal hfair) (le_of_eq ?_)
    rw [hValue_start, hA, hC]
    push_cast
    ring
  -- average
  simp only [probEvent_bind_eq_tsum]
  refine le_trans (tsum_bound_le _ _ A C (fun parameterOutput => ∑' fixed, Pr[= fixed | ($ᵗ HiddenGraph.Table : ProbComp HiddenGraph.Table)] *
    ∑' highs, Pr[= highs | ($ᵗ CoordinateHighs : ProbComp CoordinateHighs)] *
    ∑' remaining, Pr[= remaining | ($ᵗ RemainingOutputs : ProbComp RemainingOutputs)] *
    ∑' prepared, Pr[= prepared | preparation parameterOutput fixed highs remaining] *
      failMass (failSet prepared.1)) fun parameterOutput _ => ?_) le_rfl
  refine tsum_bound_le _ _ A C _ fun fixed _ => ?_
  refine tsum_bound_le _ _ A C _ fun highs _ => ?_
  refine tsum_bound_le _ _ A C _ fun remaining _ => ?_
  exact tsum_bound_le _ _ A C _ fun prepared hprepared =>
    hsample parameterOutput fixed highs remaining prepared hprepared

end Total

end LeanSphincs.Security.ForsPotential
