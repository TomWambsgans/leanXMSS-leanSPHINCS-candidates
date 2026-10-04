import LeanSphincs.BridgeForsAssembly
import LeanSphincs.BridgeNoRepeat

/-! Stage 1 with the one-coin FORS potential, for adversaries that never request a signature on
the same message twice: saturation of the targets, the one-coin potential through the adversary,
and the certified one-coin excess bound. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security

/-- 127-bit security against adversaries that never request a signature on the same message
twice. -/
def HasClassicalSecurityBitsNR [Params] (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary : Adversary, adversary.NoRepeat → HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

end LeanSphincs.Security

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

section RestO

variable (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

theorem rest_boundO (hcompat : Compatible tg model) (htrunc : UniformTruncation (R := HashOutput) tg)
    (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hclean : ∀ p call, initial (pblk parameter data p call) = none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (total : ℕ) (htotal : 2 * (total : ℝ) + 2 ≤ spaceReal)
    (hfair : Fair wbar (total + digestAttemptLimit))
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M []) (known : Knowledge Coordinate) :
    Pr[fun r => Hit tg initial r.1 r.2.2 ∨ CoverOf parameter data r.2 |
        interp tg initial model (advProg parameter data M []) total (DebtState.start initial known) >>= fun result =>
          (fun table => (table, result)) <$> completion result.2.known] ≤
      (1 - budget 0 total) + (total * (hValueO parameter data wbar (baseline total) (DebtState.start initial known) [] []
        0 signatureLimit total + failMass Fail) + signatureLimit * failMass Fail) := by
  set start := DebtState.start initial known (D := HashInput) (R := HashOutput) (ι := Coordinate) with hstart
  set b0 := baseline total with hb0def
  have hb0 : b0 ≠ ⊤ := ENNReal.ofReal_ne_top
  -- the FORS potential
  have hgood := goodO_advProg parameter data wbar b0 Fail total tg initial model hparse hkind hdigest hfail hfair hb0
    le_rfl M [] hnr total start [] 0 [] (start_prepared initial known) (start_pinv parameter data initial hclean known)
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
        (potO parameter data wbar b0 Fail tg initial start [] [] 0 total +
          b0 * expectedFlagged tg initial model (advProg parameter data M []) total start) := add_le_add le_rfl hgood
    _ = (b0 * expectedFlagged tg initial model (advProg parameter data M []) total start +
          Pr[fun r => Hit tg initial r.1 r.2.2 |
            interp tg initial model (advProg parameter data M []) total start >>= fun result =>
              (fun table => (table, result)) <$> completion result.2.known]) +
        potO parameter data wbar b0 Fail tg initial start [] [] 0 total := by ring
    _ ≤ _ := by
        refine add_le_add hsat ?_
        refine le_trans (potO_le_coreO wbar b0 Fail tg initial start [] [] 0 total) (le_of_eq ?_)
        unfold coreO
        simp

end RestO

section ChainO

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

set_option maxRecDepth 100000 in
/-- **One sample.** -/
theorem sample_boundO (hb : 0 < subtreeHeight) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ) (hq : q < 2 ^ 256)
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
      (1 - budget 0 (q - keygenCost)) + ((q - keygenCost : ℕ) * (hValueO (truncateHash parameterOutput)
        (sampleData parameterOutput fixed highs remaining) wbar (baseline (q - keygenCost))
        (DebtState.start prepared.2 (knownOf (truncateHash parameterOutput) fixed)) [] [] 0 signatureLimit
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
    refine le_trans (le_of_eq ?_) (rest_boundO param data wbar Fail tg prepared.2 model hcompat htrunc hparse
      (fun p call => (hmsg _ (msgInput_digestInput param data.root p.1 p.2 call)).1)
      (fun p call => (hmsg _ (msgInput_digestInput param data.root p.1 p.2 call)).2)
      (fun p call => hclean _ (msgInput_digestInput param data.root p.1 p.2 call)) hfail (q - keygenCost) htotal hfair
      ((internalize adversary).main ⟨data.root, param⟩)
      (noRepeat_internalize_adversary adversary hnr _) known)
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

end ChainO

section TotalO

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- The one-coin excess forecast of a new pair at the start of the run. -/
noncomputable def startExcessO (wbar b0 : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtualOnce Finset.univ wbar (excess b0) signatureLimit I 0) k []

theorem hValueO_start (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (s : State) (k : ℕ) :
    hValueO parameter data wbar b0 s [] [] 0 signatureLimit k = startExcessO wbar b0 k := rfl

theorem stage1_forge_boundO (hb : 0 < subtreeHeight) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
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
      ((1 - budget 0 (q - keygenCost)) + (q - keygenCost : ℕ) * startExcessO wbar (baseline (q - keygenCost))
        (q - keygenCost)) +
      ((q - keygenCost : ℕ) + signatureLimit) * expectedFail + q / (2 : ℝ≥0∞) ^ 256 := by
  refine le_trans (forgeAdvantage_le_prep adversary q hbound) (add_le_add ?_ le_rfl)
  set A := (1 - budget 0 (q - keygenCost)) + (q - keygenCost : ℕ) * startExcessO wbar (baseline (q - keygenCost))
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
    refine le_trans (sample_boundO hb adversary hnr q hq parameterOutput fixed highs remaining prepared hprepared tg hhit
      hcompat htrunc hmsg (hclean _ _ _ _ _ hprepared) (failSet prepared.1)
      (fun m ρ digest budget s1 hprep out hout hnone => finishRest_fail parameterOutput fixed highs remaining prepared
        hprepared tg m ρ digest budget s1 hprep out hout hnone) wbar htotal hfair) (le_of_eq ?_)
    rw [hValueO_start, hA, hC]
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

end TotalO

section CloseO

open HiddenBridge Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- **Stage 1 closes** for adversaries that never repeat a message, once the targeting exists and the
one-coin excess forecast is small. -/
theorem stage1_closeO (hb : 0 < subtreeHeight) (hN : signatureLimit ≤ 2 ^ 70)
    (htarget : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) →
      TargetingFor parameterOutput fixed highs remaining prepared)
    (wbar : ℕ → ℝ≥0∞) (hfair : ∀ q' : ℕ, 2 * q' ≤ 2 ^ 128 → Fair (wbar q') (q' + digestAttemptLimit))
    (hH0 : ∀ q' : ℕ, 2 * q' ≤ 2 ^ 128 →
      (1 - budget 0 q') + (q' : ℝ≥0∞) * startExcessO (wbar q') (baseline q') q' +
        ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q' + keygenCost : ℕ) : ℝ≥0∞) / 2 ^ 127) :
    Security.HasClassicalSecurityBitsNR 127 := by
  intro q hq1 adversary hnr hbound
  have hcast : (((2 ^ 127 : ℕ)) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 127 := by rw [Nat.cast_pow, Nat.cast_ofNat]
  rw [hcast]
  by_cases hbig : 2 ^ 127 ≤ q
  · refine le_trans probEvent_le_one ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by simp)), one_mul]
    exact_mod_cast hbig
  push Not at hbig
  set q' := q - keygenCost with hq'
  have hq'le : 2 * q' ≤ 2 ^ 128 := by omega
  have htotal : 2 * ((q' : ℕ) : ℝ) + 2 ≤ spaceReal := by
    unfold spaceReal
    have : (2 * q' + 2 : ℕ) ≤ 2 ^ 128 := by omega
    exact_mod_cast this
  have hmain := stage1_forge_boundO hb adversary hnr q hbound (by omega) htarget
    (fun _ _ _ _ _ hprep => prepared_clean _ _ _ _ _ hprep) (wbar q') (hfair q' hq'le) htotal
  refine le_trans hmain ?_
  have hE := expectedFail_le
  have hq1' : (1 : ℝ≥0∞) ≤ q := by exact_mod_cast hq1
  by_cases hK : keygenCost ≤ q
  · have hsum : q' + keygenCost = q := by omega
    -- the negligible terms fit in the slack
    have hslack : ((q' : ℝ≥0∞) + signatureLimit) * expectedFail + (q : ℝ≥0∞) / 2 ^ 256 ≤
        ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 := by
      have h256 : (q : ℝ≥0∞) / 2 ^ 256 ≤ (((q' + keygenCost : ℕ) : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ 201 := by
        rw [div_two_pow, hsum]
        exact mul_le_mul' le_rfl (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num))
      have hnat : ((q' : ℝ≥0∞) + signatureLimit) + ((q' + keygenCost : ℕ) : ℝ≥0∞) ≤
          2 * ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) := by
        have h : (q' + signatureLimit) + (q' + keygenCost) ≤ 2 * (q' + keygenCost + signatureLimit) := by omega
        have h' : (((q' + signatureLimit) + (q' + keygenCost) : ℕ) : ℝ≥0∞) ≤
            ((2 * (q' + keygenCost + signatureLimit) : ℕ) : ℝ≥0∞) := by exact_mod_cast h
        push_cast at h' ⊢
        exact h'
      calc _ ≤ ((q' : ℝ≥0∞) + signatureLimit) * (2 : ℝ≥0∞)⁻¹ ^ 201 +
            (((q' + keygenCost : ℕ) : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ 201 := add_le_add (mul_le_mul' le_rfl hE) h256
        _ = (((q' : ℝ≥0∞) + signatureLimit) + ((q' + keygenCost : ℕ) : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ 201 := by
            ring
        _ ≤ (2 * ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞)) * (2 : ℝ≥0∞)⁻¹ ^ 201 :=
            mul_le_mul' hnat le_rfl
        _ = _ := by rw [mul_comm (2 : ℝ≥0∞), mul_assoc, two_mul_inv_pow_succ]
    calc _ ≤ ((1 - budget 0 q') + (q' : ℝ≥0∞) * startExcessO (wbar q') (baseline q') q') +
          ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 := by
          rw [add_assoc]
          exact add_le_add le_rfl hslack
      _ ≤ ((q' + keygenCost : ℕ) : ℝ≥0∞) / 2 ^ 127 := hH0 q' hq'le
      _ = (q : ℝ≥0∞) / 2 ^ 127 := by rw [hsum]
  · -- the keygen tick does not fit: only negligible terms remain
    have hq0 : q - keygenCost = 0 := by omega
    simp only [hq0, budget_zero_zero, tsub_self, Nat.cast_zero, zero_mul, add_zero, zero_add]
    have hN' : (signatureLimit : ℝ≥0∞) ≤ 2 ^ 70 := by exact_mod_cast hN
    have h1 : (signatureLimit : ℝ≥0∞) * expectedFail ≤ (q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 := by
      calc (signatureLimit : ℝ≥0∞) * expectedFail ≤ 2 ^ 70 * (2 : ℝ≥0∞)⁻¹ ^ 201 := mul_le_mul' hN' hE
        _ = (2 : ℝ≥0∞)⁻¹ ^ 131 := by
            rw [show (201 : ℕ) = 70 + 131 by norm_num, pow_add, ← mul_assoc, ← mul_pow,
              ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]
        _ ≤ 1 * (2 : ℝ≥0∞)⁻¹ ^ 128 := by
            rw [one_mul]
            exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
        _ ≤ _ := mul_le_mul' hq1' le_rfl
    have h2 : (q : ℝ≥0∞) / 2 ^ 256 ≤ (q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 := by
      rw [div_two_pow]
      exact mul_le_mul' le_rfl (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num))
    calc _ ≤ (q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 + (q : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 := add_le_add h1 h2
      _ = (q : ℝ≥0∞) / 2 ^ 127 := by
          rw [← two_mul, div_two_pow, mul_left_comm, two_mul_inv_pow_succ]

end CloseO

end LeanSphincs.Security.ForsPotential
