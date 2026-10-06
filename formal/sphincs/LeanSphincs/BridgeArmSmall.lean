import LeanSphincs.BridgeArmA4b
import LeanSphincs.BridgeFleafSmall
import LeanSphincs.H0SplitCert5

/-! The small-budget route with A4b armed. Every FORS leaf query leaves `(ρ - 1 - x) 2^-128` of the
linear potential unused; A4a takes `N 2^-b 2^-10 2^-128` of it and A4b the rest,
`(1 - κ) 2^-128` with `κ ≥ 2 - ρ + x + N 2^-b 2^-10`. In exchange the near term of A4b is
multiplied by `κ`. The main inequality of the rational check becomes

  `ρ + 2^128 B + qh (2 - 2^-(26 - b)) / 2^129 + (2 - ρ + qh / 2^128 + N / (2^b 2^10)) qh c + 2^-60 ≤ 2`

with `c` half the certified near H-term, and no further term. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
open HiddenBridge PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] digestAttemptLimit

variable [Params]

open Completeness SeedModel Graph Assembly Reduce Internalize in
attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-! ### The two payments per FORS leaf query -/

omit [Params] in
/-- One contact split between the A4b payment `(1 - κ) 2^-128` and `κ 2^-128`. -/
theorem arm_split (κ : ℝ) :
    contactRate ≤ contactRate * ENNReal.ofReal (1 - κ) + ENNReal.ofReal κ * contactRate :=
  calc contactRate = contactRate * ENNReal.ofReal ((1 - κ) + κ) := by
        rw [sub_add_cancel, ENNReal.ofReal_one, mul_one]
    _ ≤ contactRate * (ENNReal.ofReal (1 - κ) + ENNReal.ofReal κ) := mul_le_mul_right ENNReal.ofReal_add_le _
    _ = _ := by ring

/-- **The A4a and A4b payments per FORS leaf query fit in the slack of the linear potential.** -/
theorem arm_pays (ρ x κ : ℝ) (hκ1 : κ ≤ 1)
    (hκ : 2 - ρ + x + (signatureLimit : ℝ) * ((2 : ℝ) ^ subtreeHeight * 2 ^ 10)⁻¹ ≤ κ) :
    contactRate * ((signatureLimit : ℝ≥0∞) * matchRate) + contactRate * ENNReal.ofReal (1 - κ) ≤
      ENNReal.ofReal ((ρ - 1 - x) / 2 ^ 128) := by
  have hm : (0 : ℝ) ≤ (signatureLimit : ℝ) * ((2 : ℝ) ^ subtreeHeight * 2 ^ 10)⁻¹ := by positivity
  have hν : (0 : ℝ) ≤ ((2 : ℝ) ^ 128)⁻¹ := by positivity
  have h1 : (0 : ℝ) ≤ 1 - κ := by linarith
  rw [contactRate_eq, matchRate_eq, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ← ENNReal.ofReal_mul hν, ← ENNReal.ofReal_mul hν, ← ENNReal.ofReal_add (mul_nonneg hν hm) (mul_nonneg hν h1)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_eq_inv_mul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (by linarith) hν

/-! ### One sample -/

section SampleSA

open Completeness SeedModel Graph Assembly Reduce Internalize

set_option maxRecDepth 100000 in
/-- **One sample of the small-budget route, A4b armed.** The stopped experiment with the
above-word values exposed is at most the linear potential `ρ q / 2^128`, the one-coin FORS
potential of covers, the coin part `2^-128 C(y, 2) rate5` of A4a, and `κ` times the near term of A4b, once
`2 - ρ + y / 2^128 + N 2^-b 2^-10 ≤ κ ≤ 1`, `y = q - keygenCost`. -/
theorem sample_boundSA (hb : 0 < subtreeHeight) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (hq : q < 2 ^ 256) (hq2 : 2 * (q - keygenCost) ≤ 2 ^ 128)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (known : Knowledge Coordinate)
    (hk : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed)))
    (ρ : ℝ) (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (κ : ℝ) (hκ : 2 - ρ + ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
      (signatureLimit : ℝ) * ((2 : ℝ) ^ subtreeHeight * 2 ^ 10)⁻¹ ≤ κ) (hκ1 : κ ≤ 1)
    (b N : ℕ) (hbb : subtreeHeight = b) (hNN : signatureLimit = N)
    (t : H0.PoisTable) (o : H0.OptS) (hthr : H0.checkThreshS b N t o = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128)
    (qb m : ℕ) (c : ℚ) (hnear : H0.checkNear b N qb m c = true) (hqb : q - keygenCost ≤ qb) :
    Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining)))) known prepared.2] ≤
      ENNReal.ofReal (ρ * (q - keygenCost : ℕ) / 2 ^ 128) +
        (((q - keygenCost : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + failMass (failSet prepared.1)) +
          signatureLimit * failMass (failSet prepared.1)) +
        contactRate * (((q - keygenCost).choose 2 : ℕ) * rate5) +
        (ENNReal.ofReal κ * ((((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) *
            ((q - keygenCost : ℕ) * ENNReal.ofReal ((c / 2 : ℚ) : ℝ))) +
          (((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) *
            ((q - keygenCost : ℕ) * failMass (failSet prepared.1) + signatureLimit * failMass (failSet prepared.1))) := by
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
  set κE : ℝ≥0∞ := ENNReal.ofReal κ with hκE
  set payB : ℝ≥0∞ := contactRate * ENNReal.ofReal (1 - κ) with hpayB
  have hmsg : ∀ x, IsMsgInput x → tgA.kind x = .none := fun x h =>
    targetingA_msg parameterOutput fixed highs remaining prepared.1 x h
  -- the contact bounds
  have hA4a := a4a_bound_gameF adversary hnr q parameterOutput fixed highs remaining prepared hprepared tgA hmsg
    known known
  have hA4b := a4b_bound_checkArm adversary hnr q b N qb m c hbb hNN hnear hqb parameterOutput fixed highs remaining
    prepared hprepared tgA hmsg known (arm_split κ) known
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
      have hfair : Fair5 H0.wbar5 := H0.fair5
      have hgood := goodO_advProg param data H0.wbar5 b0 (failSet prepared.1) q' tgA prepared.2 model
        hparse hkind hdigest hfail hfair ENNReal.ofReal_ne_top
        ((internalize adversary).main ⟨data.root, param⟩) []
        (noRepeat_internalize_adversary adversary hnr ⟨data.root, param⟩) q' start [] 0 []
        (start_prepared prepared.2 known) (start_pinv param data prepared.2 hclean known)
        (fun i t l h => by cases h) (start_count param data prepared.2 hclean known q')
      have hval : hValueO param data H0.wbar5 b0 start [] [] 0 signatureLimit q' ≤ ENNReal.ofReal (o.B : ℝ) := by
        rw [hValueO_start param data H0.wbar5 b0 start (fun m ρ => hclean (m, ρ) 0)]
        change H0.hTermO (Finset.univ : Finset View) H0.wbar5 landing signatureLimit q' (excess b0) ≤ _
        rw [H0.excess_eq]
        exact H0.hTermO_fors_le_of_check5 b N t o hthr hbb hNN q' hq2 b0 ENNReal.ofReal_ne_top
          (ENNReal.ofReal_le_ofReal hcthr)
      have hpot : potO param data H0.wbar5 b0 (failSet prepared.1) tgA prepared.2 start [] [] 0 q' ≤
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
        _ ≤ potO param data H0.wbar5 b0 (failSet prepared.1) tgA prepared.2 start [] [] 0 q' +
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
  set Efin := ∑' out, Pr[= out | run] * finalValue param data tgA prepared.2 [] out with hEfin
  set Ed := ∑' out, Pr[= out | run] * (digestCount tgA out.1.2.2.1 : ℝ≥0∞) with hEd
  set Ef := ∑' out, Pr[= out | run] * (fleafCount IsF out.1.2.2.1 : ℝ≥0∞) with hEf
  have hA3' : Ev + b0 * Ed + c0 * Ef ≤ ENNReal.ofReal (ρ * (q' : ℕ) / 2 ^ 128) := by
    refine le_trans (le_of_eq ?_) hA3
    rw [hEv, hEd, hEf, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine tsum_congr fun out => ?_
    ring
  have hpc : contactRate * ((signatureLimit : ℝ≥0∞) * matchRate) + payB ≤ c0 := arm_pays ρ _ κ hκ1 hκ
  have hκ1' : κE ≤ 1 := ENNReal.ofReal_le_one.2 hκ1
  set cov : ℝ≥0∞ := ((q' : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (o.B : ℝ) + φ) + signatureLimit * φ with hcov
  set coin : ℝ≥0∞ := contactRate * (((q' : ℕ).choose 2 : ℕ) * rate5) with hcoin
  set nearM : ℝ≥0∞ := (((q' : ℕ) : ℝ≥0∞) * contactRate) * ((q' : ℕ) * ENNReal.ofReal ((c / 2 : ℚ) : ℝ)) with hnearM
  set nearF : ℝ≥0∞ := (((q' : ℕ) : ℝ≥0∞) * contactRate) * ((q' : ℕ) * φ + signatureLimit * φ) with hnearF
  set payA : ℝ≥0∞ := contactRate * ((signatureLimit : ℝ≥0∞) * matchRate) with hpayA
  have hnear' : κE * ((((q' : ℕ) : ℝ≥0∞) * contactRate) *
      ((q' : ℕ) * (ENNReal.ofReal ((c / 2 : ℚ) : ℝ) + φ) + signatureLimit * φ)) ≤ κE * nearM + nearF := by
    calc κE * ((((q' : ℕ) : ℝ≥0∞) * contactRate) *
          ((q' : ℕ) * (ENNReal.ofReal ((c / 2 : ℚ) : ℝ) + φ) + signatureLimit * φ))
        = κE * nearM + κE * nearF := by rw [hnearM, hnearF]; ring
      _ ≤ κE * nearM + 1 * nearF := by gcongr
      _ = κE * nearM + nearF := by rw [one_mul]
  calc (Ev + Efin) + Pr[A4aRun param known | run] + Pr[A4bRun param data known | run]
      ≤ (Ev + (cov + b0 * Ed)) + (coin + payA * Ef) +
          (κE * ((((q' : ℕ) : ℝ≥0∞) * contactRate) *
            ((q' : ℕ) * (ENNReal.ofReal ((c / 2 : ℚ) : ℝ) + φ) + signatureLimit * φ)) + payB * Ef) :=
        add_le_add (add_le_add (add_le_add le_rfl hcover) hA4a) hA4b
    _ ≤ (Ev + (cov + b0 * Ed)) + (coin + payA * Ef) + ((κE * nearM + nearF) + payB * Ef) := by
        gcongr
    _ = (Ev + b0 * Ed + (payA + payB) * Ef) + cov + coin + (κE * nearM + nearF) := by ring
    _ ≤ (Ev + b0 * Ed + c0 * Ef) + cov + coin + (κE * nearM + nearF) := by gcongr
    _ ≤ ENNReal.ofReal (ρ * (q' : ℕ) / 2 ^ 128) + cov + coin + (κE * nearM + nearF) := by gcongr

end SampleSA

/-! ### The seed-free bound and the deterministic signer -/

section Close

open Completeness SeedModel Graph Assembly Reduce Internalize

set_option maxRecDepth 100000 in
/-- **Small budgets, seed-free win, A4b armed.** The near term enters at `κ` times half the
certified near H-term, with `κ` rational. -/
theorem small_seedFree_boundA (hb : 0 < subtreeHeight) (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (hq : q < 2 ^ 256) (hq2 : 2 * (q - keygenCost) ≤ 2 ^ 128)
    (ρ : ℝ) (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (κ : ℚ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hκ : 2 - ρ + ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
      (signatureLimit : ℝ) * ((2 : ℝ) ^ subtreeHeight * 2 ^ 10)⁻¹ ≤ (κ : ℝ))
    (b N : ℕ) (hbb : subtreeHeight = b) (hNN : signatureLimit = N)
    (t : H0.PoisTable) (o : H0.OptS) (hthr : H0.checkThreshS b N t o = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128)
    (qb m : ℕ) (c : ℚ) (hnear : H0.checkNear b N qb m c = true) (hqb : q - keygenCost ≤ qb) :
    Pr[Win | seedFreeExperiment (internalize adversary) q] ≤
      smallMainF ρ q o.B (κ * (c / 2)) + smallFail q * expectedFail := by
  refine le_trans (seedFree_le_exposeP adversary q) ?_
  set A := smallMainF ρ q o.B (κ * (c / 2)) with hA
  set C := smallFail q with hC
  have hκ1R : (κ : ℝ) ≤ 1 := by exact_mod_cast hκ1
  have hsample : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) →
      ∀ known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
        (knownOf (truncateHash parameterOutput) fixed)),
      Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining)))) known prepared.2] ≤
        A + C * failMass (failSet prepared.1) := by
    intro parameterOutput fixed highs remaining prepared hprepared known hk
    refine le_trans (sample_boundSA hb adversary hnr q hq hq2 parameterOutput fixed highs remaining prepared
      hprepared known hk ρ hN (κ : ℝ) hκ hκ1R b N hbb hNN t o hthr hcthr qb m c hnear hqb) (le_of_eq ?_)
    rw [hA, hC]
    unfold smallMainF smallFail
    rw [Rat.cast_mul, ENNReal.ofReal_mul (Rat.cast_nonneg.2 hκ0)]
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

/-- **Small budgets, deterministic signer, A4b armed.** -/
theorem det_smallA (hb : 0 < subtreeHeight) (adversary : Adversary) (q : ℕ)
    (hbound : Det.HasHashQueryBoundDet adversary q) (hq : q < 2 ^ 256) (hq2 : 2 * (q - keygenCost) ≤ 2 ^ 128)
    (ρ : ℝ) (hN : Numeric ρ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128))
    (κ : ℚ) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hκ : 2 - ρ + ((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 +
      (signatureLimit : ℝ) * ((2 : ℝ) ^ subtreeHeight * 2 ^ 10)⁻¹ ≤ (κ : ℝ))
    (b N : ℕ) (hbb : subtreeHeight = b) (hNN : signatureLimit = N)
    (t : H0.PoisTable) (o : H0.OptS) (hthr : H0.checkThreshS b N t o = true) (hcthr : (o.cthr : ℝ) ≤ ρ / 2 ^ 128)
    (qb m : ℕ) (c : ℚ) (hnear : H0.checkNear b N qb m c = true) (hqb : q - keygenCost ≤ qb) :
    Det.forgeAdvantageDet adversary ≤
      smallMainF ρ q o.B (κ * (c / 2)) + smallFail q * (2 : ℝ≥0∞)⁻¹ ^ 201 + 2 * ((q : ℝ≥0∞) / 2 ^ 256) := by
  refine le_trans (Det.forgeAdvantageDet_le_seedFree adversary q hbound) (add_le_add ?_ le_rfl)
  refine le_trans (small_seedFree_boundA hb (Memo.memoAdv adversary) (Memo.memoAdv_noRepeat adversary) q hq hq2 ρ hN
    κ hκ0 hκ1 hκ b N hbb hNN t o hthr hcthr qb m c hnear hqb) ?_
  exact add_le_add le_rfl (mul_le_mul_right expectedFail_le _)

end Close

/-! ### The rational check -/

/-- The rational small-route check at the right end `qh` of the small budgets, with A4b armed: the
near term is multiplied by `2 - ρ + qh / 2^128 + N / (2^b 2^10)`. The coin part of A4a enters as
`qh (2 - 2^-(26 - b)) / 2^129`. -/
def checkSmallA (b N qh : ℕ) (ρ cthr B c : ℚ) : Bool :=
  decide (3 / 2 ≤ ρ) && decide (ρ ≤ 2) &&
    decide (1 + 4032 * (2 - ρ) * ((qh : ℚ) / 2 ^ 128) ≤ ρ) && decide (1 + 66 * ((qh : ℚ) / 2 ^ 128) ≤ ρ) &&
    decide (64 * ((qh : ℚ) / 2 ^ 128) ≤ 1) && decide (qh ≤ 2 ^ 127) && decide (N ≤ 2 ^ 70) &&
    decide (cthr ≤ ρ / 2 ^ 128) && decide (0 ≤ B) && decide (0 ≤ c) &&
    decide ((N : ℚ) / (2 ^ b * 2 ^ 10) ≤ ρ - 1 - (qh : ℚ) / 2 ^ 128) &&
    decide (ρ + 2 ^ 128 * B + (qh : ℚ) * (2 - 1 / 2 ^ (26 - b)) / 2 ^ 129 +
      (2 - ρ + (qh : ℚ) / 2 ^ 128 + (N : ℚ) / (2 ^ b * 2 ^ 10)) * qh * c + 1 / 2 ^ 60 ≤ 2)

omit [Params] in
theorem checkSmallA_sound {b N qh : ℕ} {ρ cthr B c : ℚ} (h : checkSmallA b N qh ρ cthr B c = true) :
    Numeric (ρ : ℝ) ((qh : ℝ) / 2 ^ 128) ∧ qh ≤ 2 ^ 127 ∧ N ≤ 2 ^ 70 ∧ (cthr : ℝ) ≤ (ρ : ℝ) / 2 ^ 128 ∧
      0 ≤ B ∧ 0 ≤ c ∧
      (N : ℝ) / (2 ^ b * 2 ^ 10) ≤ (ρ : ℝ) - 1 - (qh : ℝ) / 2 ^ 128 ∧
      (ρ : ℝ) + 2 ^ 128 * (B : ℝ) + (qh : ℝ) * (2 - 1 / 2 ^ (26 - b)) / 2 ^ 129 +
        (2 - (ρ : ℝ) + (qh : ℝ) / 2 ^ 128 + (N : ℝ) / (2 ^ b * 2 ^ 10)) * qh * (c : ℝ) + 1 / 2 ^ 60 ≤ 2 := by
  simp only [checkSmallA, Bool.and_eq_true, decide_eq_true_eq] at h
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
  exact ⟨⟨r1, r2, r3, r4, r5⟩, h6, h7, r8, h9, h10, r11, r12⟩

end LeanSphincs.Security.ForsPotential
