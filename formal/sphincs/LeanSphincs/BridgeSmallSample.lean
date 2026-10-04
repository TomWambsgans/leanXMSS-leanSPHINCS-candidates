import LeanSphincs.BridgeAssemblyA
import LeanSphincs.BridgePotentialA8
import LeanSphincs.BridgeContactBound
import LeanSphincs.H0SplitCert

/-! One sample of the small-budget route: the stopped experiment with the above-word values exposed
is bounded by the linear potential (guesses, first-order hits, WOTS second-order events, FORS
pairs), the two FORS contact bounds and the one-coin FORS potential for covers, all on the same
interpreted run. -/

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

/-! ### One sample -/

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
theorem numeric_mono {ρ x x' : ℝ} (h : Numeric ρ x) (hx : x' ≤ x) (hx0 : 0 ≤ x') : Numeric ρ x' where
  low := h.low
  high := h.high
  enc := by
    have h1 := h.enc
    have h2 : 0 ≤ 2 - ρ := by linarith [h.high]
    have h3 : (2 - ρ) * x' ≤ (2 - ρ) * x := mul_le_mul_of_nonneg_left hx h2
    nlinarith
  contact := by have := h.contact; linarith
  small := by have := h.small; linarith

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

omit [Params] in
theorem probEvent_const_le (mx : ProbComp (Coordinate → Digest)) (Q : Prop) :
    Pr[fun _ => Q | mx] ≤ if Q then 1 else 0 := by
  split_ifs with hQ
  · exact probEvent_le_one
  · exact le_of_eq (probEvent_eq_zero fun _ _ h => hQ h)

set_option maxRecDepth 100000 in
/-- **One sample of the small-budget route.** The stopped experiment with the above-word values
exposed is at most the linear potential `ρ q / 2^128`, the one-coin FORS potential of covers at the
baseline `ρ / 2^128` (its excess certified by `o`), and the two FORS contact bounds. -/
theorem sample_boundS (hb : 0 < subtreeHeight) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (hq : q < 2 ^ 256) (hq2 : 2 * (q - keygenCost) ≤ 2 ^ 128)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (known : Knowledge Coordinate)
    (hk : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed)))
    (ρ : ℝ) (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (b N : ℕ) (hbb : subtreeHeight = b) (hNN : signatureLimit = N)
    (t : H0.PoisTable) (o : H0.OptS) (hthr : H0.checkThreshS b N t o = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128)
    (qb m : ℕ) (c : ℚ) (hnear : H0.checkNear b N qb m c = true) (hqb : q - keygenCost ≤ qb) :
    Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining)))) known prepared.2] ≤
      ENNReal.ofReal (ρ * (q - keygenCost : ℕ) / 2 ^ 128) +
        (((q - keygenCost : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + failMass (failSet prepared.1)) +
          signatureLimit * failMass (failSet prepared.1)) +
        (((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) *
          (signatureLimit * matchRate +
            (q - keygenCost : ℕ) * (((2 ^ 128 - ((q - keygenCost) + 2 ^ 32) : ℕ) : ℝ≥0∞))⁻¹) +
        (((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) *
          ((q - keygenCost : ℕ) * (ENNReal.ofReal (c : ℝ) + failMass (failSet prepared.1)) +
            signatureLimit * failMass (failSet prepared.1)) := by
  set param := truncateHash parameterOutput with hparam
  set data := sampleData parameterOutput fixed highs remaining with hdata
  set model := sampleModel parameterOutput highs with hmodel
  set tgA := targetingA parameterOutput fixed highs remaining prepared.1 with htgA
  set start : State := DebtState.start prepared.2 known with hstart
  set run := interp tgA prepared.2 model (costGameX param data (internalize adversary)) q start with hrun
  set b0 : ℝ≥0∞ := ENNReal.ofReal (ρ / 2 ^ 128) with hb0
  set pay := payoffA parameterOutput fixed highs remaining prepared known ρ with hpay
  set q' := q - keygenCost with hq'
  set φ := failMass (failSet prepared.1) with hφ
  have hmsg : ∀ x, IsMsgInput x → tgA.kind x = .none := fun x h =>
    targetingA_msg parameterOutput fixed highs remaining prepared.1 x h
  -- the contact bounds
  have hA4a := a4a_bound_fair adversary hnr q hq2 parameterOutput fixed highs remaining prepared hprepared tgA hmsg
    known known
  have hA4b := a4b_bound_check adversary hnr q b N qb m c hbb hNN hnear hqb parameterOutput fixed highs remaining
    prepared hprepared tgA hmsg known known
  -- the linear potential, after the keygen tick
  have hA3 : ∑' out, Pr[= out | run] * (endValue pay out.2 + b0 * (digestCount tgA out.1.2.2.1 : ℝ≥0∞)) ≤
      ENNReal.ofReal (ρ * (q' : ℕ) / 2 ^ 128) := by
    by_cases hK : keygenCost ≤ q
    · have hrunEq : run = (fun out => ((out.1.1, out.1.2.1, Sum.inr keygenCost :: out.1.2.2.1, out.1.2.2.2),
            out.2)) <$> interp tgA prepared.2 model
            (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start := by
        rw [hrun]
        unfold costGameX
        rw [interp_tick_bind tgA prepared.2 model _ _ q start hK, costRestX_eq]
      rw [hrunEq, tsum_probOutput_map_mul]
      refine le_trans (le_of_eq ?_) (smallRoute_potential parameterOutput fixed highs remaining prepared known ρ hk
        tgA rfl q' hN (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []))
      refine tsum_congr fun out => ?_
      congr 3 <;> simp [digestCount]
    · have hrunEq : run = interp tgA prepared.2 model (costGameX param data (internalize adversary)) 0 start := by
        rw [hrun]
        unfold costGameX
        rw [interp_tick_bind_abort tgA prepared.2 model keygenCost _ q start hK,
          interp_tick_bind_abort tgA prepared.2 model keygenCost _ 0 start (by omega)]
      rw [hrunEq]
      have hq0 : (q' : ℕ) = 0 := by omega
      refine le_trans (smallRoute_potential parameterOutput fixed highs remaining prepared known ρ hk tgA rfl 0
        (numeric_mono hN (by rw [hq0]) (by norm_num)) (costGameX param data (internalize adversary)))
        (le_of_eq ?_)
      rw [hq0]
  -- the cover potential
  have hcover : ∑' out, Pr[= out | run] * finalValue param data tgA prepared.2 [] out ≤
      (((q' : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + φ) + signatureLimit * φ) +
        b0 * ∑' out, Pr[= out | run] * (digestCount tgA out.1.2.2.1 : ℝ≥0∞) := by
    by_cases hK : keygenCost ≤ q
    · have hrunEq : run = (fun out => ((out.1.1, out.1.2.1, Sum.inr keygenCost :: out.1.2.2.1, out.1.2.2.2),
            out.2)) <$> interp tgA prepared.2 model
            (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start := by
        rw [hrun]
        unfold costGameX
        rw [interp_tick_bind tgA prepared.2 model _ _ q start hK, costRestX_eq]
      rw [hrunEq, tsum_probOutput_map_mul, tsum_probOutput_map_mul]
      have hparse : ∀ p call, model.parse (pblk param data p call) = none := fun p call =>
        sampleModel_parse_blk parameterOutput highs data p call
      have hkind : ∀ p call, tgA.kind (pblk param data p call) = .none := fun p call =>
        hmsg _ (msgInput_digestInput param data.root p.1 p.2 call)
      have hdigest : ∀ p call, tgA.digest (pblk param data p call) := fun p call =>
        msgInput_digestInput param data.root p.1 p.2 call
      have hclean : ∀ p call, prepared.2 (pblk param data p call) = none := fun p call =>
        prepared_clean parameterOutput fixed highs remaining prepared hprepared _
          (msgInput_digestInput param data.root p.1 p.2 call)
      have hfail : ∀ m ρ digest budget (s1 : State), Prepared prepared.2 s1 →
          ∀ out ∈ support (interp tgA prepared.2 model (finishRest param data m ρ digest) budget s1),
            out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ failSet prepared.1 :=
        fun m ρ digest budget s1 hprep out hout hnone => finishRest_fail parameterOutput fixed highs remaining
          prepared hprepared tgA m ρ digest budget s1 hprep out hout hnone
      have hfair : Fair (H0.wbarOf q') (q' + digestAttemptLimit) := H0.fair_of q' hq2
      have hgood := goodO_advProg param data (H0.wbarOf q') b0 (failSet prepared.1) q' tgA prepared.2 model
        hparse hkind hdigest hfail hfair ENNReal.ofReal_ne_top le_rfl
        ((internalize adversary).main ⟨data.root, param⟩) []
        (noRepeat_internalize_adversary adversary hnr ⟨data.root, param⟩) q' start [] 0 []
        (start_prepared prepared.2 known) (start_pinv param data prepared.2 hclean known)
        (fun i t l h => by cases h) (start_count param data prepared.2 hclean known q')
      have hval : hValueO param data (H0.wbarOf q') b0 start [] [] 0 signatureLimit q' ≤ ENNReal.ofReal (o.B : ℝ) := by
        rw [hValueO_start]
        change H0.hTermO (Finset.univ : Finset View) (H0.wbarOf q') landing signatureLimit q' (excess b0) ≤ _
        rw [H0.excess_eq]
        exact H0.hTermO_fors_le_of_check b N t o hthr hbb hNN q' hq2 b0 ENNReal.ofReal_ne_top
          (ENNReal.ofReal_le_ofReal hcthr)
      have hpot : potO param data (H0.wbarOf q') b0 (failSet prepared.1) tgA prepared.2 start [] [] 0 q' ≤
          ((q' : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + φ) + signatureLimit * φ := by
        refine le_trans (potO_le_coreO ..) ?_
        unfold coreO
        simp only [List.map_nil, List.sum_nil, zero_add, List.length_nil, Nat.sub_zero]
        gcongr
      calc ∑' out, Pr[= out | interp tgA prepared.2 model
              (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start] *
            finalValue param data tgA prepared.2 [] _
          = ∑' out, Pr[= out | interp tgA prepared.2 model
              (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start] *
            finalValue param data tgA prepared.2 [] out := rfl
        _ ≤ potO param data (H0.wbarOf q') b0 (failSet prepared.1) tgA prepared.2 start [] [] 0 q' +
            b0 * expectedFlagged tgA prepared.2 model
              (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start := hgood
        _ ≤ _ := by
            gcongr
            refine le_trans (expectedFlagged_le_digest tgA prepared.2 model _ q' start) (le_of_eq ?_)
            refine tsum_congr fun out => ?_
            simp [digestCount]
    · have hrunEq : run = pure ((none, [], [], []), start) := by
        rw [hrun]
        unfold costGameX
        exact interp_tick_bind_abort tgA prepared.2 model _ _ q start hK
      rw [hrunEq, tsum_probOutput_pure_mul]
      refine le_trans (le_of_eq ?_) bot_le
      rfl
  -- pointwise split and summation
  rw [hrun] at hcover
  refine le_trans (stopped_le_interp_exposeV hb adversary q hq parameterOutput fixed highs remaining prepared
    hprepared tgA known hk) ?_
  change Pr[_ | run >>= fun result => (fun table => (table, result)) <$> completion result.2.known] ≤ _
  -- pointwise
  have hstep : ∀ out, Pr[= out | run] *
      Pr[fun x => CorrectGuess x.1 x.2.2 ∨ badAV parameterOutput fixed highs remaining prepared.1 x.1
          (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2.cache) |
        (fun table => (table, out)) <$> completion out.2.known] ≤
      Pr[= out | run] * ((endValue pay out.2 + finalValue param data tgA prepared.2 [] out) +
        (if A4aRun param known out then 1 else 0) + (if A4bRun param data known out then 1 else 0)) := by
    intro out
    by_cases hout : out ∈ support run
    · refine mul_le_mul_right ?_ _
      rw [probEvent_map]
      calc Pr[_ | completion out.2.known]
          ≤ Pr[fun T => pay T out.2 = 1 ∨ (A4aRun param known out ∨ A4bRun param data known out ∨
              finalValue param data tgA prepared.2 [] out = 1) | completion out.2.known] := by
            refine probEvent_mono fun T hT h => ?_
            have hTe : tableExtending out.2.known T = T := by
              unfold completion at hT
              rw [support_map] at hT
              obtain ⟨t, _, rfl⟩ := hT
              funext c
              simp only [tableExtending]
              cases out.2.known c <;> rfl
            rcases small_pointwise parameterOutput fixed highs remaining prepared hprepared known hk ρ adversary q
              out hout T hTe h with h1 | h2 | h3 | h4
            · exact Or.inl h1
            · exact Or.inr (Or.inl h2)
            · exact Or.inr (Or.inr (Or.inl h3))
            · exact Or.inr (Or.inr (Or.inr h4))
        _ ≤ Pr[fun T => pay T out.2 = 1 | completion out.2.known] +
            Pr[fun _ => A4aRun param known out ∨ A4bRun param data known out ∨
              finalValue param data tgA prepared.2 [] out = 1 | completion out.2.known] := probEvent_or_le _ _ _
        _ ≤ endValue pay out.2 + (finalValue param data tgA prepared.2 [] out +
              (if A4aRun param known out then 1 else 0) + (if A4bRun param data known out then 1 else 0)) := by
            refine add_le_add (probEvent_le_endValue pay out.2 _ fun T h => h) ?_
            by_cases ha : A4aRun param known out
            · rw [if_pos ha]
              exact le_trans probEvent_le_one (le_trans (le_add_left le_rfl) (le_add_right le_rfl))
            · by_cases hb' : A4bRun param data known out
              · rw [if_pos hb']
                exact le_trans probEvent_le_one (le_add_left le_rfl)
              · by_cases hf : finalValue param data tgA prepared.2 [] out = 1
                · rw [hf]
                  exact le_trans probEvent_le_one (le_trans (le_add_right le_rfl) (le_add_right le_rfl))
                · refine le_trans (le_of_eq (probEvent_eq_zero fun _ _ h => ?_)) bot_le
                  rcases h with h | h | h
                  · exact ha h
                  · exact hb' h
                  · exact hf h
        _ = _ := by ring
    · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
  rw [probEvent_bind_eq_tsum]
  refine le_trans (ENNReal.tsum_le_tsum hstep) ?_
  -- split the sum
  have hsplit : ∑' out, Pr[= out | run] * ((endValue pay out.2 + finalValue param data tgA prepared.2 [] out) +
        (if A4aRun param known out then 1 else 0) + (if A4bRun param data known out then 1 else 0)) =
      (∑' out, Pr[= out | run] * endValue pay out.2 +
        ∑' out, Pr[= out | run] * finalValue param data tgA prepared.2 [] out) +
        Pr[A4aRun param known | run] + Pr[A4bRun param data known | run] := by
    rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine tsum_congr fun out => ?_
    split_ifs <;> ring
  rw [hsplit]
  -- the linear potential and the cover potential
  have hA3' : ∑' out, Pr[= out | run] * endValue pay out.2 +
      b0 * ∑' out, Pr[= out | run] * (digestCount tgA out.1.2.2.1 : ℝ≥0∞) ≤
        ENNReal.ofReal (ρ * (q' : ℕ) / 2 ^ 128) := by
    refine le_trans (le_of_eq ?_) hA3
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    refine tsum_congr fun out => ?_
    ring
  have hmain : ∑' out, Pr[= out | run] * endValue pay out.2 +
      ∑' out, Pr[= out | run] * finalValue param data tgA prepared.2 [] out ≤
      ENNReal.ofReal (ρ * (q' : ℕ) / 2 ^ 128) +
        (((q' : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + φ) + signatureLimit * φ) := by
    calc _ ≤ ∑' out, Pr[= out | run] * endValue pay out.2 +
          ((((q' : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + φ) + signatureLimit * φ) +
            b0 * ∑' out, Pr[= out | run] * (digestCount tgA out.1.2.2.1 : ℝ≥0∞)) := add_le_add le_rfl hcover
      _ = (∑' out, Pr[= out | run] * endValue pay out.2 +
            b0 * ∑' out, Pr[= out | run] * (digestCount tgA out.1.2.2.1 : ℝ≥0∞)) +
          (((q' : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + φ) + signatureLimit * φ) := by ring
      _ ≤ _ := add_le_add hA3' le_rfl
  exact add_le_add (add_le_add hmain hA4a) hA4b

end SampleS

end LeanSphincs.Security.ForsPotential
