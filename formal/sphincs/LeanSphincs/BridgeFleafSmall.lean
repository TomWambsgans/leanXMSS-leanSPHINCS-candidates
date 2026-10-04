import LeanSphincs.BridgeFleafA4a
import LeanSphincs.BridgeDetFinal

/-! The small-budget route with the signature part of the FORS contact bound A4a paid by the linear
potential. Every FORS leaf query leaves `(ρ - 1 - x) 2^-128` of the linear potential unused, and A4a
costs at most `2^-128 N 2^-b 2^-10` per FORS leaf query plus `x (y wbar landing)`. Once
`N 2^-b 2^-10 ≤ ρ - 1 - x`, the payments cancel on the same interpreted run and the term
`x N 2^-b 2^-10` leaves the small-budget bound. -/

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

omit [Params] in
theorem digestCount_cons_inr {D R ι : Type} (tg : Targeting D R ι) (amount : ℕ) (entries : List (Entry D)) :
    digestCount tg (.inr amount :: entries) = digestCount tg entries := by
  simp [digestCount]

/-- The A4a payment per FORS leaf query is at most the slack of the linear potential. -/
theorem pay_le_slack (ρ x : ℝ) (hpay : (signatureLimit : ℝ) * ((2 : ℝ) ^ subtreeHeight * 2 ^ 10)⁻¹ ≤ ρ - 1 - x) :
    contactRate * ((signatureLimit : ℝ≥0∞) * matchRate) ≤ ENNReal.ofReal ((ρ - 1 - x) / 2 ^ 128) := by
  rw [contactRate_eq, matchRate_eq, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hpay (by positivity)

/-! ### One sample -/

section SampleSF

open Completeness SeedModel Graph Assembly Reduce Internalize

set_option maxRecDepth 100000 in
/-- **One sample of the small-budget route, A4a paid per FORS leaf query.** The stopped experiment
with the above-word values exposed is at most the linear potential `ρ q / 2^128`, the one-coin FORS
potential of covers, the coin part `x (y / (2^128 - y - 2^32))` of A4a and the bound A4b, once
`N 2^-b 2^-10 ≤ ρ - 1 - y / 2^128`, `y = q - keygenCost`. -/
theorem sample_boundSF (hb : 0 < subtreeHeight) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (hq : q < 2 ^ 256) (hq2 : 2 * (q - keygenCost) ≤ 2 ^ 128)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (known : Knowledge Coordinate)
    (hk : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed)))
    (ρ : ℝ) (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (hpay : (signatureLimit : ℝ) * ((2 : ℝ) ^ subtreeHeight * 2 ^ 10)⁻¹ ≤
      ρ - 1 - ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128)
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
          ((q - keygenCost : ℕ) * (((2 ^ 128 - ((q - keygenCost) + 2 ^ 32) : ℕ) : ℝ≥0∞))⁻¹) +
        (((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) *
          ((q - keygenCost : ℕ) * (ENNReal.ofReal ((c / 2 : ℚ) : ℝ) + failMass (failSet prepared.1)) +
            signatureLimit * failMass (failSet prepared.1)) := by
  set param := truncateHash parameterOutput with hparam
  set data := sampleData parameterOutput fixed highs remaining with hdata
  set model := sampleModel parameterOutput highs with hmodel
  set tgA := targetingA parameterOutput fixed highs remaining prepared.1 with htgA
  set start : State := DebtState.start prepared.2 known with hstart
  set run := interp tgA prepared.2 model (costGameX param data (internalize adversary)) q start with hrun
  set b0 : ℝ≥0∞ := ENNReal.ofReal (ρ / 2 ^ 128) with hb0
  set pay := payoffA parameterOutput fixed highs remaining prepared known ρ with hpay'
  set q' := q - keygenCost with hq'
  set φ := failMass (failSet prepared.1) with hφ
  set c0 : ℝ≥0∞ := ENNReal.ofReal ((ρ - 1 - ((q' : ℕ) : ℝ) / 2 ^ 128) / 2 ^ 128) with hc0
  set IsF := IsFleafIn param with hIsF
  have hmsg : ∀ x, IsMsgInput x → tgA.kind x = .none := fun x h =>
    targetingA_msg parameterOutput fixed highs remaining prepared.1 x h
  -- the contact bounds
  have hA4a := a4a_bound_fairF adversary hnr q hq2 parameterOutput fixed highs remaining prepared hprepared tgA hmsg
    known known
  have hA4b := a4b_bound_check_half adversary hnr q b N qb m c hbb hNN hnear hqb parameterOutput fixed highs remaining
    prepared hprepared tgA hmsg known known
  -- the linear potential with both payments, after the keygen tick
  have hA3 : ∑' out, Pr[= out | run] * (endValue pay out.2 + b0 * (digestCount tgA out.1.2.2.1 : ℝ≥0∞) +
      c0 * (fleafCount IsF out.1.2.2.1 : ℝ≥0∞)) ≤ ENNReal.ofReal (ρ * (q' : ℕ) / 2 ^ 128) := by
    by_cases hK : keygenCost ≤ q
    · have hrunEq : run = (fun out => ((out.1.1, out.1.2.1, Sum.inr keygenCost :: out.1.2.2.1, out.1.2.2.2),
            out.2)) <$> interp tgA prepared.2 model
            (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start := by
        rw [hrun]
        unfold costGameX
        rw [interp_tick_bind tgA prepared.2 model _ _ q start hK, costRestX_eq]
      rw [hrunEq, tsum_probOutput_map_mul]
      refine le_trans (le_of_eq ?_) (smallRoute_potentialF parameterOutput fixed highs remaining prepared known ρ hk
        tgA rfl q' hN (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []))
      refine tsum_congr fun out => ?_
      simp only [digestCount_cons_inr, fleafCount_cons_inr]
      rfl
    · have hrunEq : run = interp tgA prepared.2 model (costGameX param data (internalize adversary)) 0 start := by
        rw [hrun]
        unfold costGameX
        rw [interp_tick_bind_abort tgA prepared.2 model keygenCost _ q start hK,
          interp_tick_bind_abort tgA prepared.2 model keygenCost _ 0 start (by omega)]
      rw [hrunEq]
      have hq0 : (q' : ℕ) = 0 := by omega
      rw [hc0, hq0]
      exact smallRoute_potentialF parameterOutput fixed highs remaining prepared known ρ hk tgA rfl 0
        (numeric_mono hN (by rw [hq0]) (by norm_num)) (costGameX param data (internalize adversary))
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
  have hsplit : ∑' out, Pr[= out | run] * ((endValue pay out.2 + finalValue param data tgA prepared.2 [] out) +
        (if A4aRun param known out then 1 else 0) + (if A4bRun param data known out then 1 else 0)) =
      (∑' out, Pr[= out | run] * endValue pay out.2 +
        ∑' out, Pr[= out | run] * finalValue param data tgA prepared.2 [] out) +
        Pr[A4aRun param known | run] + Pr[A4bRun param data known | run] := by
    rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite, ← ENNReal.tsum_add, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine tsum_congr fun out => ?_
    split_ifs <;> ring
  rw [hsplit]
  set Ev := ∑' out, Pr[= out | run] * endValue pay out.2 with hEv
  set Ed := ∑' out, Pr[= out | run] * (digestCount tgA out.1.2.2.1 : ℝ≥0∞) with hEd
  set Ef := ∑' out, Pr[= out | run] * (fleafCount IsF out.1.2.2.1 : ℝ≥0∞) with hEf
  have hA3' : Ev + b0 * Ed + c0 * Ef ≤ ENNReal.ofReal (ρ * (q' : ℕ) / 2 ^ 128) := by
    refine le_trans (le_of_eq ?_) hA3
    rw [hEv, hEd, hEf, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine tsum_congr fun out => ?_
    ring
  have hpc : contactRate * ((signatureLimit : ℝ≥0∞) * matchRate) ≤ c0 := pay_le_slack ρ _ hpay
  have hmain : (Ev + ∑' out, Pr[= out | run] * finalValue param data tgA prepared.2 [] out) +
      Pr[A4aRun param known | run] ≤
      ENNReal.ofReal (ρ * (q' : ℕ) / 2 ^ 128) +
        (((q' : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + φ) + signatureLimit * φ) +
        (((q' : ℕ) : ℝ≥0∞) * contactRate) *
          ((q' : ℕ) * (((2 ^ 128 - ((q') + 2 ^ 32) : ℕ) : ℝ≥0∞))⁻¹) := by
    calc (Ev + ∑' out, Pr[= out | run] * finalValue param data tgA prepared.2 [] out) +
          Pr[A4aRun param known | run]
        ≤ (Ev + ((((q' : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + φ) + signatureLimit * φ) + b0 * Ed)) +
          ((((q' : ℕ) : ℝ≥0∞) * contactRate) *
              ((q' : ℕ) * (((2 ^ 128 - ((q') + 2 ^ 32) : ℕ) : ℝ≥0∞))⁻¹) +
            (contactRate * ((signatureLimit : ℝ≥0∞) * matchRate)) * Ef) :=
          add_le_add (add_le_add le_rfl hcover) hA4a
      _ ≤ (Ev + ((((q' : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + φ) + signatureLimit * φ) + b0 * Ed)) +
          ((((q' : ℕ) : ℝ≥0∞) * contactRate) *
              ((q' : ℕ) * (((2 ^ 128 - ((q') + 2 ^ 32) : ℕ) : ℝ≥0∞))⁻¹) + c0 * Ef) := by
          gcongr
      _ = (Ev + b0 * Ed + c0 * Ef) +
          (((q' : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + φ) + signatureLimit * φ) +
          (((q' : ℕ) : ℝ≥0∞) * contactRate) *
            ((q' : ℕ) * (((2 ^ 128 - ((q') + 2 ^ 32) : ℕ) : ℝ≥0∞))⁻¹) := by ring
      _ ≤ _ := add_le_add (add_le_add hA3' le_rfl) le_rfl
  exact add_le_add hmain hA4b

end SampleSF

/-! ### The seed-free bound and the deterministic signer -/

/-- The sample-independent part of the small-budget bound, A4a paid per FORS leaf query. -/
noncomputable def smallMainF (ρ : ℝ) (q : ℕ) (B c : ℚ) : ℝ≥0∞ :=
  ENNReal.ofReal (ρ * (q - keygenCost : ℕ) / 2 ^ 128) + ((q - keygenCost : ℕ) : ℝ≥0∞) * ENNReal.ofReal (B : ℝ) +
    (((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) *
      ((q - keygenCost : ℕ) * (((2 ^ 128 - ((q - keygenCost) + 2 ^ 32) : ℕ) : ℝ≥0∞))⁻¹) +
    (((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) * ((q - keygenCost : ℕ) * ENNReal.ofReal (c : ℝ))

section Close

open Completeness SeedModel Graph Assembly Reduce Internalize

set_option maxRecDepth 100000 in
/-- **Small budgets, seed-free win, A4a paid per FORS leaf query.** -/
theorem small_seedFree_boundF (hb : 0 < subtreeHeight) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (hq : q < 2 ^ 256) (hq2 : 2 * (q - keygenCost) ≤ 2 ^ 128)
    (ρ : ℝ) (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (hpay : (signatureLimit : ℝ) * ((2 : ℝ) ^ subtreeHeight * 2 ^ 10)⁻¹ ≤
      ρ - 1 - ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128)
    (b N : ℕ) (hbb : subtreeHeight = b) (hNN : signatureLimit = N)
    (t : H0.PoisTable) (o : H0.OptS) (hthr : H0.checkThreshS b N t o = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128)
    (qb m : ℕ) (c : ℚ) (hnear : H0.checkNear b N qb m c = true) (hqb : q - keygenCost ≤ qb) :
    Pr[Win | seedFreeExperiment (internalize adversary) q] ≤
      smallMainF ρ q o.B (c / 2) + smallFail q * expectedFail := by
  refine le_trans (seedFree_le_exposeP adversary q) ?_
  set A := smallMainF ρ q o.B (c / 2) with hA
  set C := smallFail q with hC
  have hsample : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) →
      ∀ known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
        (knownOf (truncateHash parameterOutput) fixed)),
      Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining)))) known prepared.2] ≤
        A + C * failMass (failSet prepared.1) := by
    intro parameterOutput fixed highs remaining prepared hprepared known hk
    refine le_trans (sample_boundSF hb adversary hnr q hq hq2 parameterOutput fixed highs remaining prepared
      hprepared known hk ρ hN hpay b N hbb hNN t o hthr hcthr qb m c hnear hqb) (le_of_eq ?_)
    rw [hA, hC]
    unfold smallMainF smallFail
    ring
  simp only [probEvent_bind_eq_tsum]
  refine le_trans (tsum_bound_le _ _ A C (fun parameterOutput => ∑' fixed, Pr[= fixed | ($ᵗ HiddenGraph.Table :
    ProbComp HiddenGraph.Table)] *
    ∑' highs, Pr[= highs | ($ᵗ CoordinateHighs : ProbComp CoordinateHighs)] *
    ∑' remaining, Pr[= remaining | ($ᵗ RemainingOutputs : ProbComp RemainingOutputs)] *
    ∑' prepared, Pr[= prepared | preparation parameterOutput fixed highs remaining] *
      failMass (failSet prepared.1)) fun parameterOutput _ => ?_) le_rfl
  refine tsum_bound_le _ _ A C _ fun fixed _ => ?_
  refine tsum_bound_le _ _ A C _ fun highs _ => ?_
  refine tsum_bound_le _ _ A C _ fun remaining _ => ?_
  refine tsum_bound_le _ _ A C _ fun prepared hprepared => ?_
  refine le_trans (tsum_bound_le _ _ A C (fun _ => failMass (failSet prepared.1))
    fun known hk => hsample parameterOutput fixed highs remaining prepared hprepared known hk) ?_
  refine add_le_add le_rfl (mul_le_mul_right ?_ _)
  rw [ENNReal.tsum_mul_right]
  exact mul_le_of_le_one_left' tsum_probOutput_le_one

/-- **Small budgets, deterministic signer, A4a paid per FORS leaf query.** -/
theorem det_smallF (hb : 0 < subtreeHeight) (adversary : Adversary) (q : ℕ)
    (hbound : Det.HasHashQueryBoundDet adversary q) (hq : q < 2 ^ 256) (hq2 : 2 * (q - keygenCost) ≤ 2 ^ 128)
    (ρ : ℝ) (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (hpay : (signatureLimit : ℝ) * ((2 : ℝ) ^ subtreeHeight * 2 ^ 10)⁻¹ ≤
      ρ - 1 - ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128)
    (b N : ℕ) (hbb : subtreeHeight = b) (hNN : signatureLimit = N)
    (t : H0.PoisTable) (o : H0.OptS) (hthr : H0.checkThreshS b N t o = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128)
    (qb m : ℕ) (c : ℚ) (hnear : H0.checkNear b N qb m c = true) (hqb : q - keygenCost ≤ qb) :
    Det.forgeAdvantageDet adversary ≤
      smallMainF ρ q o.B (c / 2) + smallFail q * (2 : ℝ≥0∞)⁻¹ ^ 201 + 2 * ((q : ℝ≥0∞) / 2 ^ 256) := by
  refine le_trans (Det.forgeAdvantageDet_le_seedFree adversary q hbound) (add_le_add ?_ le_rfl)
  refine le_trans (small_seedFree_boundF hb (Memo.memoAdv adversary) (Memo.memoAdv_noRepeat adversary) q hq hq2 ρ hN
    hpay b N hbb hNN t o hthr hcthr qb m c hnear hqb) ?_
  exact add_le_add le_rfl (mul_le_mul_right expectedFail_le _)

end Close

/-! ### The closed form -/

/-- The real inequality behind the closed form, without the signature part of A4a. -/
theorem small_realF (x qh q N ρ B c Dx Dh : ℝ) (hx0 : 0 ≤ x) (hxq : x ≤ qh) (hqh : qh ≤ 2 ^ 127)
    (hq : x + 1 ≤ q) (hN0 : 0 ≤ N) (hN : N ≤ 2 ^ 70) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hDh : 0 < Dh) (hD : Dh ≤ Dx)
    (hcheck : ρ + 2 ^ 128 * B + qh / Dh + qh * c + 1 / 2 ^ 60 ≤ 2) :
    ρ * x / 2 ^ 128 + x * B + x * (2 ^ 128)⁻¹ * (x * Dx⁻¹) + x * (2 ^ 128)⁻¹ * (x * c) +
        ((x + N) + x * (2 ^ 128)⁻¹ * (x + N)) * (1 / 2) ^ 201 + 2 * (q / 2 ^ 256) ≤ q / 2 ^ 127 := by
  have h := small_real x qh q N ρ B c Dx Dh 0 hx0 hxq hqh hq hN0 hN hB hc le_rfl hDh hD
    (by rw [mul_zero, add_zero]; exact hcheck)
  simpa only [mul_zero, zero_add] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- **The small-budget bound in closed form, A4a paid per FORS leaf query.** -/
theorem small_closeF (q qh : ℕ) (hq1 : 1 ≤ q) (hq' : q - keygenCost ≤ qh) (hqh : qh ≤ 2 ^ 127)
    (hN : signatureLimit ≤ 2 ^ 70) (ρ : ℝ) (hρ : 0 ≤ ρ) (B c : ℚ) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hcheck : ρ + 2 ^ 128 * (B : ℝ) + (qh : ℝ) / ((2 ^ 128 - (qh + 2 ^ 32) : ℕ) : ℝ) + qh * (c : ℝ) +
        1 / 2 ^ 60 ≤ 2) :
    smallMainF ρ q B c + smallFail q * (2 : ℝ≥0∞)⁻¹ ^ 201 + 2 * ((q : ℝ≥0∞) / 2 ^ 256) ≤
      (q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) := by
  set q' := q - keygenCost with hq'def
  have hK : 1 ≤ keygenCost := one_le_keygenCost
  have hq'1 : q' + 1 ≤ q := by omega
  have hqh' : qh + 2 ^ 32 < 2 ^ 128 := lt_of_le_of_lt (Nat.add_le_add_right hqh _) (by norm_num)
  have hDh : 0 < 2 ^ 128 - (qh + 2 ^ 32) := Nat.sub_pos_of_lt hqh'
  have hD : 2 ^ 128 - (qh + 2 ^ 32) ≤ 2 ^ 128 - (q' + 2 ^ 32) :=
    Nat.sub_le_sub_left (Nat.add_le_add_right hq' _) _
  have hDq : 0 < 2 ^ 128 - (q' + 2 ^ 32) := lt_of_lt_of_le hDh hD
  have hB' : (0 : ℝ) ≤ B := by exact_mod_cast hB
  have hc' : (0 : ℝ) ≤ c := by exact_mod_cast hc
  have r1 : (q' : ℝ) ≤ qh := Nat.cast_le.mpr hq'
  have r2 : (qh : ℝ) ≤ 2 ^ 127 := by
    have h := (Nat.cast_le (α := ℝ)).mpr hqh
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  have r3 : (q' : ℝ) + 1 ≤ q := by
    have h := (Nat.cast_le (α := ℝ)).mpr hq'1
    rwa [Nat.cast_add, Nat.cast_one] at h
  have r4 : (signatureLimit : ℝ) ≤ 2 ^ 70 := by
    have h := (Nat.cast_le (α := ℝ)).mpr hN
    rwa [Nat.cast_pow, Nat.cast_ofNat] at h
  have r5 : (0 : ℝ) < ((2 ^ 128 - (qh + 2 ^ 32) : ℕ) : ℝ) := Nat.cast_pos.mpr hDh
  have r6 : ((2 ^ 128 - (qh + 2 ^ 32) : ℕ) : ℝ) ≤ ((2 ^ 128 - (q' + 2 ^ 32) : ℕ) : ℝ) := Nat.cast_le.mpr hD
  have hreal := small_realF (q' : ℝ) qh q signatureLimit ρ B c ((2 ^ 128 - (q' + 2 ^ 32) : ℕ) : ℝ)
    ((2 ^ 128 - (qh + 2 ^ 32) : ℕ) : ℝ) (Nat.cast_nonneg _)
    r1 r2 r3 (Nat.cast_nonneg _) r4 hB' hc' r5 r6 hcheck
  have hnat : ∀ n : ℕ, (n : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) := fun n => (ENNReal.ofReal_natCast n).symm
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by rw [ENNReal.ofReal_ofNat]
  have hhalf : (2 : ℝ≥0∞)⁻¹ ^ 201 = ENNReal.ofReal ((1 / 2) ^ 201) := by
    rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  have hq256 : (q : ℝ≥0∞) / 2 ^ 256 = ENNReal.ofReal (q / 2 ^ 256) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_natCast]
  have hq127 : (q : ℝ≥0∞) / ((2 ^ 127 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (q / 2 ^ 127) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat]
    push_cast
    norm_num
  have hDinv : (((2 ^ 128 - (q' + 2 ^ 32) : ℕ) : ℝ≥0∞))⁻¹ =
      ENNReal.ofReal ((((2 ^ 128 - (q' + 2 ^ 32) : ℕ) : ℝ))⁻¹) := ofReal_natCast_inv hDq
  unfold smallMainF smallFail
  rw [← hq'def, hDinv, hhalf, hq256, hq127, contactRate_eq, hnat q', hnat signatureLimit, h2]
  have hD0 : (0 : ℝ) ≤ (((2 ^ 128 - (q' + 2 ^ 32) : ℕ) : ℝ))⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  simp (disch := positivity) only [← ENNReal.ofReal_add, ← ENNReal.ofReal_mul]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ### The rational check and the 127-bit statement -/

/-- The rational small-route check at the right end `qh` of the small budgets, with the signature
part of A4a paid by the linear potential: `checkSmall` without `N 2^-b 2^-10` in the main
inequality, plus `N 2^-b 2^-10 ≤ ρ - 1 - qh / 2^128`. -/
def checkSmallF (b N qh : ℕ) (ρ cthr B c : ℚ) : Bool :=
  decide (3 / 2 ≤ ρ) && decide (ρ ≤ 2) &&
    decide (1 + 4032 * (2 - ρ) * ((qh : ℚ) / 2 ^ 128) ≤ ρ) && decide (1 + 66 * ((qh : ℚ) / 2 ^ 128) ≤ ρ) &&
    decide (64 * ((qh : ℚ) / 2 ^ 128) ≤ 1) && decide (qh ≤ 2 ^ 127) && decide (N ≤ 2 ^ 70) &&
    decide (cthr ≤ ρ / 2 ^ 128) && decide (0 ≤ B) && decide (0 ≤ c) &&
    decide ((N : ℚ) / (2 ^ b * 2 ^ 10) ≤ ρ - 1 - (qh : ℚ) / 2 ^ 128) &&
    decide (ρ + 2 ^ 128 * B + (qh : ℚ) / ((2 ^ 128 - (qh + 2 ^ 32) : ℕ) : ℚ) + qh * c + 1 / 2 ^ 60 ≤ 2)

omit [Params] in
theorem checkSmallF_sound {b N qh : ℕ} {ρ cthr B c : ℚ} (h : checkSmallF b N qh ρ cthr B c = true) :
    Numeric (ρ : ℝ) ((qh : ℝ) / 2 ^ 128) ∧ qh ≤ 2 ^ 127 ∧ N ≤ 2 ^ 70 ∧ (cthr : ℝ) ≤ (ρ : ℝ) / 2 ^ 128 ∧
      0 ≤ B ∧ 0 ≤ c ∧
      (N : ℝ) * ((2 : ℝ) ^ b * 2 ^ 10)⁻¹ ≤ (ρ : ℝ) - 1 - (qh : ℝ) / 2 ^ 128 ∧
      (ρ : ℝ) + 2 ^ 128 * (B : ℝ) + (qh : ℝ) / ((2 ^ 128 - (qh + 2 ^ 32) : ℕ) : ℝ) + qh * (c : ℝ) +
        1 / 2 ^ 60 ≤ 2 := by
  simp only [checkSmallF, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  have r1 := (Rat.cast_le (K := ℝ)).mpr h1
  have r2 := (Rat.cast_le (K := ℝ)).mpr h2
  have r3 := (Rat.cast_le (K := ℝ)).mpr h3
  have r4 := (Rat.cast_le (K := ℝ)).mpr h4
  have r5 := (Rat.cast_le (K := ℝ)).mpr h5
  have r8 := (Rat.cast_le (K := ℝ)).mpr h8
  have r11 := (Rat.cast_le (K := ℝ)).mpr h11
  have r12 := (Rat.cast_le (K := ℝ)).mpr h12
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_sub, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_one] at r1 r2 r3 r4 r5 r8 r11 r12
  refine ⟨⟨r1, r2, r3, r4, r5⟩, h6, h7, r8, h9, h10, ?_, r12⟩
  rw [← div_eq_mul_inv]
  exact r11

set_option maxRecDepth 100000 in
/-- **127 bits for the deterministic signer, A4a paid per FORS leaf query**, from the small-route
check `checkSmallF` at `qh` and the large-route bound from `qh` on. -/
theorem det_bitsF (hb0 : 0 < subtreeHeight) (b N : ℕ) (hb : subtreeHeight = b) (hN : signatureLimit = N)
    (qh : ℕ) (ρ : ℚ) (t : H0.PoisTable) (o : H0.OptS) (hthr : H0.checkThreshS b N t o = true)
    (m : ℕ) (c : ℚ) (hnear : H0.checkNear b N qh m c = true)
    (hsmall : checkSmallF b N qh ρ o.cthr o.B (c / 2) = true)
    (hlarge : ∀ q' : ℕ, qh ≤ q' → 2 * q' ≤ 2 ^ 128 →
      (1 - budget 0 q') + (q' : ℝ≥0∞) * H0.hOfO q' +
          ((q' + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
        ((q' + keygenCost : ℕ) : ℝ≥0∞) / 2 ^ 127) :
    Det.HasClassicalSecurityBitsDet 127 := by
  obtain ⟨hnum, hqh, hN70, hcthr, hB, hc, hpayQ, hcheck⟩ := checkSmallF_sound hsmall
  have hN70' : signatureLimit ≤ 2 ^ 70 := hN ▸ hN70
  intro q hq1 adversary hbound
  by_cases hbig : 2 ^ 127 ≤ q
  · refine le_trans probEvent_le_one ?_
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (ENNReal.natCast_ne_top _)), one_mul]
    exact_mod_cast hbig
  have hq127 : q < 2 ^ 127 := Nat.lt_of_not_le hbig
  by_cases hs : q - keygenCost ≤ qh
  · have hq2 : 2 * (q - keygenCost) ≤ 2 ^ 128 := by omega
    have hnum' : Numeric (ρ : ℝ) (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128) :=
      numeric_mono hnum (div_le_div_of_nonneg_right (Nat.cast_le.mpr hs) (by positivity)) (by positivity)
    have hpay : (signatureLimit : ℝ) * ((2 : ℝ) ^ subtreeHeight * 2 ^ 10)⁻¹ ≤
        (ρ : ℝ) - 1 - ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 := by
      rw [hb, hN]
      have hx : ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 ≤ (qh : ℝ) / 2 ^ 128 :=
        div_le_div_of_nonneg_right (Nat.cast_le.mpr hs) (by positivity)
      linarith
    refine le_trans (det_smallF hb0 adversary q hbound (by omega) hq2 (ρ : ℝ) hnum' hpay b N hb hN t o hthr hcthr
      qh m c hnear hs) ?_
    exact small_closeF q qh hq1 hs hqh hN70' (ρ : ℝ) (by linarith [hnum.low]) o.B (c / 2) hB hc hcheck
  · have hK : keygenCost ≤ q := by omega
    have h := det_large hb0 hN70' adversary q hbound hq127 hK (hlarge (q - keygenCost) (by omega) (by omega))
    refine le_trans h (le_of_eq ?_)
    rw [Nat.cast_pow, Nat.cast_ofNat]

end LeanSphincs.Security.ForsPotential
