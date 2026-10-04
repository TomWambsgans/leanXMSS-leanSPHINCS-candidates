import LeanSphincs.BridgeForsGame

/-! Saturation and the FORS potential on the same lazy run: a decided hit, or a FORS cover
without one, costs at most the saturation budget plus the potential of the start. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
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

end LeanSphincs.Security.ForsPotential
