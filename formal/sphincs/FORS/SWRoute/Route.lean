import FORS.SWRoute.Events
import FORS.SWRoute.SignBound

/-! **The SW route on one sample.** The S-part from the start state of the sample's comparison,
the event decomposition, and the P-part combine into the bound of the stopped experiment:

  `Pr[win] ≤ (1 - budgetE ρ 0 q') + Rp`

whenever the P-part bounds the weighted cover value, the arming costs and the kills by `Rp`, the
contact payments `cU · WC` and the digest payments `(b0c + δ b0n) · WF` with `b0c + δ b0n ≤ β/2^128`. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost PotentialA GraphView ForsPotential HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### The payment accounts are finite -/

section AcctFinite

variable {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- An account whose payment per step is at most the step's cost is at most the budget. -/
theorem acct_le_budget (pay : St → CostSpec.Domain → St → ℝ≥0∞)
    (hpay : ∀ s input s', pay s input s' ≤ (sourceCost input : ℝ≥0∞)) {α : Type} (comp : OracleComp CostSpec α) :
    ∀ budget s, acct model pay comp budget s ≤ budget := by
  induction comp using OracleComp.inductionOn with
  | pure value => intro budget s; rw [acct_pure]; exact bot_le
  | query_bind input next ih =>
      intro budget s
      rw [acct_query_bind]
      split_ifs with hcost
      · calc ∑' r, Pr[= r | costStep model input s] *
              (pay s input r.2 + acct model pay (next r.1) (budget - sourceCost input) r.2)
            ≤ ∑' r, Pr[= r | costStep model input s] *
                ((sourceCost input : ℝ≥0∞) + ((budget - sourceCost input : ℕ) : ℝ≥0∞)) :=
              ENNReal.tsum_le_tsum fun r => mul_le_mul_right (add_le_add (hpay _ _ _) (ih r.1 _ _)) _
          _ ≤ (sourceCost input : ℝ≥0∞) + ((budget - sourceCost input : ℕ) : ℝ≥0∞) :=
              tsum_le_const_of_pointwise _ _ _ fun _ => le_rfl
          _ = budget := by rw [← Nat.cast_add, Nat.add_sub_cancel' hcost]
      · exact bot_le

theorem payF_le_cost (K : Ctx) (root : Digest) (s : St) (input : CostSpec.Domain) :
    payF K root s input ≤ (sourceCost input : ℝ≥0∞) := by
  rcases input with (n | (x | c)) | n
  · rw [payF_draw]; exact bot_le
  · exact (payF_le_weight K root s _).trans (by
      rw [show sourceCost (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inr (.inl x))) = 1 from rfl,
        Nat.cast_one]
      exact weightA_le_one K root s)
  · rw [payF_reveal]; exact bot_le
  · rw [payF_tick]; exact bot_le

theorem payC_le_cost (K : Ctx) (root : Digest) (s : St) (input : CostSpec.Domain) :
    payC K root s input ≤ (sourceCost input : ℝ≥0∞) := by
  by_cases h : IsFLQ K input
  · obtain ⟨f, rfl⟩ := h
    refine (payC_le_weight K root s _).trans ?_
    rw [show sourceCost (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inr (.inl (f.input K.p)))) = 1
      from rfl, Nat.cast_one]
    exact weightA_le_one K root s
  · rw [payC_of_not K root s _ h]; exact bot_le

theorem WF_le (K : Ctx) (root : Digest) {α : Type} (comp : OracleComp CostSpec α) (budget : ℕ) (s : St) :
    WF model K root comp budget s ≤ budget :=
  acct_le_budget model _ (fun s input _ => payF_le_cost K root s input) comp budget s

theorem WC_le (K : Ctx) (root : Digest) {α : Type} (comp : OracleComp CostSpec α) (budget : ℕ) (s : St) :
    WC model K root comp budget s ≤ budget :=
  acct_le_budget model _ (fun s input _ => payC_le_cost K root s input) comp budget s

end AcctFinite

/-! ### The sample's setting -/

section SampleSetting

open Completeness SeedModel Graph Assembly Reduce Internalize

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs) (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
  (known : Knowledge Coordinate) (ρ : ℝ)

include fixed remaining in
/-- **The setting of the route's steps holds for the sample.** -/
theorem stepHyp_sample (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining)) :
    StepHyp (ctxA parameterOutput fixed highs remaining prepared known ρ) (sampleModel parameterOutput highs) where
  parse := sampleModel_parse parameterOutput highs
  incoming := sampleModel_incoming parameterOutput highs
  outgoing := sampleModel_outgoing parameterOutput highs
  sec := ctxA_sec parameterOutput fixed highs remaining prepared known ρ
  msg := ctxA_msg parameterOutput fixed highs remaining prepared known ρ
  digest := rfl
  fleaf f := initial_none_of_not prepared fun a h =>
    prepared_not_fleaf parameterOutput fixed highs remaining prepared hprepared h
  trunc := uniformTruncation_of_trunc _ rfl
  parsedFresh x q hq := by
    obtain ⟨rfl, -⟩ := (parse_some_iff _ _ x q).1 hq
    obtain ⟨addr, v⟩ := q
    cases addr with
    | chain lay tree leaf chain step =>
        exact initial_none_of_not prepared fun a h =>
          prepared_not_chain parameterOutput fixed highs remaining prepared hprepared
            (l := (lay, tree, leaf)) (i := chain) (st := step) (v := v) h
    | fleaf index κ leaf =>
        exact initial_none_of_not prepared fun a h =>
          prepared_not_fleaf parameterOutput fixed highs remaining prepared hprepared (f := ⟨index, κ, leaf, v⟩) h

/-- **The route's invariant at the start.** -/
theorem invS_start (hk : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed))) :
    InvS (ctxA parameterOutput fixed highs remaining prepared known ρ) (DebtState.start prepared.2 known) 0 where
  sat := HiddenDebt.inv_start _ prepared.2 known
  lin := PotentialA.inv_start parameterOutput fixed highs remaining prepared known ρ hk
  leaf f := known_fleaf parameterOutput fixed highs remaining prepared known ρ hk f
  ua := by
    have : (ctxA parameterOutput fixed highs remaining prepared known ρ).UAset (DebtState.start prepared.2 known) = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨l, i, u, -, -, hfr, -⟩
      exact fr_start _ known x u hfr
    rw [this, Set.encard_empty]
    rfl

theorem not_fr_start (K : Ctx) (x : HashInput) (u : HashOutput) : ¬K.Fr (DebtState.start K.initial known) x u :=
  fr_start K known x u

theorem badR_start (K : Ctx) (root : Digest) : ¬BadR K root (DebtState.start K.initial known) := by
  have hcb : ∀ l i, K.ContactB (DebtState.start K.initial known) l i = ∅ := fun l i => by
    ext v
    simp only [Ctx.ContactB, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨x, u, -, h, -⟩
    exact not_fr_start known K x u h
  have hfc : ∀ f, ¬FCk K (DebtState.start K.initial known) f := fun f hf => by
    obtain ⟨u, h, -⟩ := hf
    exact not_fr_start known K _ u h
  rintro (⟨l, -, hb⟩ | hd | ⟨f, hf, -⟩)
  · rcases hb with ⟨i, v, h1, -⟩ | ⟨i, ⟨v, h1⟩, -⟩ | ⟨i, -, -, ⟨v, h1⟩, -⟩ <;> rw [hcb] at h1 <;> exact h1
  · rcases hd with ⟨l, i, v, -, -, -, -, -, h1, -, -⟩ | ⟨f, -, -, hf, -⟩ | ⟨-, ⟨f, hf⟩⟩
    · rw [hcb] at h1; exact h1
    · exact hfc f hf
    · exact hfc f hf
  · exact hfc f hf

theorem weightA_start (K : Ctx) (root : Digest) : weightA K root (DebtState.start K.initial known) = 1 := by
  rw [weightA_of_not_badR K root (badR_start known K root), weight_start]

theorem pendA_start (K : Ctx) : pendA K (DebtState.start K.initial known) = 0 := by
  have : K.UAset (DebtState.start K.initial known) = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨l, i, u, -, -, hfr, -⟩
    exact not_fr_start known K x u hfr
  unfold pendA
  rw [this, Set.encard_empty]
  simp

theorem expo_start (K : Ctx) (ρ : ℝ) : expo K ρ false (DebtState.start K.initial known) = ρ := by
  refine expo_unarmed K ρ ?_
  rintro (h | ⟨l, -, ⟨i, msg, ctr, u, hfr, -⟩ | ⟨i, v, x, u, -, hfr, -⟩⟩ | ⟨f, u, hfr, -⟩)
  · cases h
  · exact not_fr_start known K _ u hfr
  · exact not_fr_start known K x u hfr
  · exact not_fr_start known K _ u hfr

end SampleSetting

/-! ### The S-part from the start -/

section SStart

variable (K : Ctx) (root : Digest) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (ρ β δ cU : ℝ)

/-- **The S-part from a start state** (weight one, exponent `ρ`, no pending credit). -/
theorem sPart_start {total : ℕ} (hN : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (hH : StepHyp K model)
    {α : Type} (comp : OracleComp CostSpec α) (s0 : St) (hinv : InvS K s0 0) (hw : weightA K root s0 = 1)
    (hP : pendA K s0 = 0) (he : expo K ρ false s0 = ρ) :
    budgetE ρ 0 total + (ENNReal.ofReal (β / 2 ^ 128) * WF model K root comp total s0 +
        ENNReal.ofReal (cU / 2 ^ 128) * WC model K root comp total s0) ≤
      endW model K root comp total s0 +
        (ENNReal.ofReal δ * WA model K root comp total s0 false + WK model K root comp total s0) := by
  have h := sPart_run K root model ρ β δ cU hN hH comp total s0 0 false hinv (by omega)
  rw [hw, he, hP, mul_one, mul_zero, zero_add] at h
  exact le_trans le_self_add h

end SStart


/-! ### Combining the parts -/

/-- **The closing algebra of one sample**: from the S-part `B + X ≤ E + A` (`X` finite), the
P-part `F + A ≤ Rp + X`, and `E ≤ 1`, the mean `(1 - E) + F` is at most `(1 - B) + Rp`. -/
theorem combine_parts {B X E A F Rp : ℝ≥0∞} (hS : B + X ≤ E + A) (hP : F + A ≤ Rp + X) (hX : X ≠ ⊤)
    (hE : E ≤ 1) (hB : B ≤ 1) : (1 - E) + F ≤ (1 - B) + Rp := by
  by_cases hA : A = ⊤
  · have : Rp = ⊤ := by
      rw [hA, add_top, top_le_iff] at hP
      exact (ENNReal.add_eq_top.1 hP).resolve_right hX
    rw [this, add_top]
    exact le_top
  have hsum : B + X + (F + A) ≤ E + A + (Rp + X) := add_le_add hS hP
  have h1 : B + F + (X + A) ≤ E + Rp + (X + A) := by
    calc B + F + (X + A) = B + X + (F + A) := by ring
      _ ≤ E + A + (Rp + X) := hsum
      _ = E + Rp + (X + A) := by ring
  have h2 : B + F ≤ E + Rp := (ENNReal.add_le_add_iff_right (ENNReal.add_ne_top.2 ⟨hX, hA⟩)).1 h1
  have hB' : B ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hB
  have h3 : (1 - E) + F + B ≤ 1 + Rp :=
    calc (1 - E) + F + B = (1 - E) + (B + F) := by ring
      _ ≤ (1 - E) + (E + Rp) := add_le_add le_rfl h2
      _ = (1 - E + E) + Rp := by ring
      _ = 1 + Rp := by rw [tsub_add_cancel_of_le hE]
  calc (1 - E) + F ≤ (1 + Rp) - B := ENNReal.le_sub_of_add_le_right hB' h3
    _ = (1 - B) + Rp := by rw [ENNReal.sub_add_eq_add_sub hB hB']

section Sample

open Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

set_option maxRecDepth 100000 in
/-- **One sample of the SW route.** With the P-part of the sample's run as a hypothesis (in the form
of `ppart_full`'s conclusion, with the coefficient `cU / 2^128`): the stopped experiment is at most the
missing saturation `1 - budgetE ρ 0 q'` plus the P-part's bound `Rp`. -/
theorem sample_boundSW (hb : 0 < keptHeight topLayer) (adversary : Adversary) (q : ℕ) (hq : q < 2 ^ 256)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (steps : Message → Randomness)
    (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (known : Knowledge Coordinate)
    (hk : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
      (knownOf (truncateHash parameterOutput) fixed)))
    (ρ β δ cU : ℝ) (hN : SWNumeric ρ β δ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128) cU)
    (b0c b0n : ℝ≥0∞) (hb0 : b0c + ENNReal.ofReal δ * b0n ≤ ENNReal.ofReal (β / 2 ^ 128)) (Rp : ℝ≥0∞)
    (hP : keygenCost ≤ q →
      ∑' out, Pr[= out | interp (targetingA parameterOutput fixed highs remaining prepared.1) prepared.2
          (sampleModel parameterOutput highs)
          (advProg (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
            ((internalize adversary).main ⟨(sampleData parameterOutput fixed highs remaining steps).root,
              truncateHash parameterOutput⟩) []) (q - keygenCost) (DebtState.start prepared.2 known)] *
          (weightA (ctxA parameterOutput fixed highs remaining prepared known ρ)
              (sampleData parameterOutput fixed highs remaining steps).root out.2 *
            finalValue (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
              (targetingA parameterOutput fixed highs remaining prepared.1) prepared.2 [] out) +
        ENNReal.ofReal δ * WA (sampleModel parameterOutput highs) (ctxA parameterOutput fixed highs remaining prepared known ρ)
          (sampleData parameterOutput fixed highs remaining steps).root
          (advProg (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
            ((internalize adversary).main ⟨(sampleData parameterOutput fixed highs remaining steps).root,
              truncateHash parameterOutput⟩) []) (q - keygenCost) (DebtState.start prepared.2 known) false +
        WK (sampleModel parameterOutput highs) (ctxA parameterOutput fixed highs remaining prepared known ρ)
          (sampleData parameterOutput fixed highs remaining steps).root
          (advProg (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
            ((internalize adversary).main ⟨(sampleData parameterOutput fixed highs remaining steps).root,
              truncateHash parameterOutput⟩) []) (q - keygenCost) (DebtState.start prepared.2 known) ≤
      Rp + ENNReal.ofReal (cU / 2 ^ 128) * WC (sampleModel parameterOutput highs)
          (ctxA parameterOutput fixed highs remaining prepared known ρ)
          (sampleData parameterOutput fixed highs remaining steps).root
          (advProg (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
            ((internalize adversary).main ⟨(sampleData parameterOutput fixed highs remaining steps).root,
              truncateHash parameterOutput⟩) []) (q - keygenCost) (DebtState.start prepared.2 known) +
        (b0c + ENNReal.ofReal δ * b0n) * WF (sampleModel parameterOutput highs)
          (ctxA parameterOutput fixed highs remaining prepared known ρ)
          (sampleData parameterOutput fixed highs remaining steps).root
          (advProg (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
            ((internalize adversary).main ⟨(sampleData parameterOutput fixed highs remaining steps).root,
              truncateHash parameterOutput⟩) []) (q - keygenCost) (DebtState.start prepared.2 known)) :
    Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
        (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
          (sampleData parameterOutput fixed highs remaining steps)))) known prepared.2] ≤
      (1 - budgetE ρ 0 (q - keygenCost)) + Rp := by
  set param := truncateHash parameterOutput with hparam
  set data := sampleData parameterOutput fixed highs remaining steps with hdata
  set model := sampleModel parameterOutput highs with hmodel
  set tgA := targetingA parameterOutput fixed highs remaining prepared.1 with htgA
  set K := ctxA parameterOutput fixed highs remaining prepared known ρ with hK
  set start : State := DebtState.start prepared.2 known with hstart
  set q' := q - keygenCost with hq'
  set run := interp tgA prepared.2 model (costGameX param data (internalize adversary)) q start with hrun
  set w : State → ℝ≥0∞ := weightA K data.root with hw
  set fv := finalValue param data tgA prepared.2 [] with hfv
  -- the event decomposition
  refine le_trans (stopped_le_interp_exposeV hb adversary q hq parameterOutput fixed highs remaining steps prepared
    hprepared tgA known hk) ?_
  change Pr[_ | run >>= fun result => (fun table => (table, result)) <$> completion result.2.known] ≤ _
  rw [probEvent_bind_eq_tsum]
  have hpt : ∀ out ∈ support run, Pr[fun x => CorrectGuess x.1 x.2.2 ∨ badAV parameterOutput fixed highs remaining
        prepared.1 x.1 (((x.2.1.1, x.2.1.2.1), x.2.1.2.2.1), x.2.2.cache) |
        (fun table => (table, out)) <$> completion out.2.known] ≤ (1 - w out.2) + w out.2 * fv out := by
    intro out hout
    rw [probEvent_map]
    exact sw_pointwise parameterOutput fixed highs remaining prepared hprepared known hk ρ adversary q steps out hout
  refine le_trans (ENNReal.tsum_le_tsum fun out => ?_) (le_of_eq_of_le (rfl :
    ∑' out, Pr[= out | run] * ((1 - w out.2) + w out.2 * fv out) = _) ?_)
  · by_cases hout : out ∈ support run
    · exact mul_le_mul_right (hpt out hout) _
    · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
  by_cases hK : keygenCost ≤ q
  swap
  · -- the keygen tick aborts: nothing is won
    have hrunA : run = pure ((none, [], [], []), start) := by
      rw [hrun]; unfold costGameX; exact interp_tick_bind_abort tgA prepared.2 model _ _ q start hK
    rw [hrunA, tsum_probOutput_pure_mul]
    have h1 : w start = 1 := weightA_start known K data.root
    have h0 : fv ((none, [], [], []), start) = 0 := rfl
    dsimp only
    rw [h1, h0, tsub_self, zero_add, mul_zero]
    exact bot_le
  have hrunK : run = (fun out => ((out.1.1, out.1.2.1, Sum.inr keygenCost :: out.1.2.2.1, out.1.2.2.2), out.2)) <$>
      interp tgA prepared.2 model (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start := by
    rw [hrun]
    unfold costGameX
    rw [interp_tick_bind tgA prepared.2 model _ _ q start hK, costRestX_eq]
  rw [hrunK, tsum_probOutput_map_mul]
  have hmap : ∀ x : Run HashInput Coordinate HiddenBridge.Outcome × State,
      fv ((x.1.1, x.1.2.1, Sum.inr keygenCost :: x.1.2.2.1, x.1.2.2.2), x.2) = fv x := fun x => rfl
  dsimp only
  simp only [hmap]
  set μ := interp tgA prepared.2 model (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start
    with hμ
  set E := ∑' out, Pr[= out | μ] * w out.2 with hE
  set F := ∑' out, Pr[= out | μ] * (w out.2 * fv out) with hF
  have hmass : ∑' out, Pr[= out | μ] = 1 := tsum_probOutput_eq_one' probFailure_eq_zero
  have hE1 : E ≤ 1 := le_trans (ENNReal.tsum_le_tsum fun out => mul_le_of_le_one_right' (weightA_le_one K data.root out.2))
    tsum_probOutput_le_one
  have hsplit : ∑' out, Pr[= out | μ] * ((1 - w out.2) + w out.2 * fv out) = (1 - E) + F := by
    have hc : ∑' out, Pr[= out | μ] * (1 - w out.2) = 1 - E := by
      have hs : ∑' out, Pr[= out | μ] * (1 - w out.2) + E = 1 := by
        rw [hE, ← ENNReal.tsum_add]
        calc _ = ∑' out, Pr[= out | μ] := tsum_congr fun out => by
              rw [← mul_add, tsub_add_cancel_of_le (weightA_le_one K data.root out.2), mul_one]
          _ = 1 := hmass
      exact ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top hE1) hs
    rw [← hc, hF, ← ENNReal.tsum_add]
    exact tsum_congr fun out => by rw [mul_add]
  rw [hsplit]
  -- the S-part
  have hH := stepHyp_sample parameterOutput fixed highs remaining prepared known ρ hprepared
  have hS := sPart_start K data.root model ρ β δ cU hN hH
    (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) start
    (invS_start parameterOutput fixed highs remaining prepared known ρ hk) (weightA_start known K data.root)
    (pendA_start known K) (expo_start known K ρ)
  -- the P-part
  have hP' := hP hK
  set X := ENNReal.ofReal (β / 2 ^ 128) * WF model K data.root
      (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start +
    ENNReal.ofReal (cU / 2 ^ 128) * WC model K data.root
      (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start with hX
  have hXtop : X ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_⟩
    · exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (WF_le model K data.root _ q' start)
    · exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (WC_le model K data.root _ q' start)
  have hP2 : F + (ENNReal.ofReal δ * WA model K data.root
        (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start false +
      WK model K data.root (advProg param data ((internalize adversary).main ⟨data.root, param⟩) []) q' start) ≤
      Rp + X := by
    rw [← add_assoc]
    refine hP'.trans ?_
    rw [hX, add_comm (ENNReal.ofReal (β / 2 ^ 128) * _), ← add_assoc]
    gcongr
  have hB1 : budgetE ρ 0 q' ≤ 1 := budgetE_le_one (by linarith [hN.low]) 0 q'
    (by have := hN.total_lt_space; push_cast; linarith)
  exact combine_parts hS hP2 hXtop hE1 hB1

end Sample


/-! ### Averaging over the samples and the seed -/

section Close

open Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

set_option maxRecDepth 100000 in
/-- **The seed-free win from a bound of every sample** (with the above-word exposure). -/
theorem seedFree_boundSW (adversary : Adversary) (q : ℕ) (steps : Message → Randomness) (A C : ℝ≥0∞)
    (hsample : ∀ parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) →
      ∀ known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
        (knownOf (truncateHash parameterOutput) fixed)),
      Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (erase (trace (richProgram (internalize adversary) q (truncateHash parameterOutput)
            (sampleData parameterOutput fixed highs remaining steps)))) known prepared.2] ≤
        A + C * failMass (failSet prepared.1)) :
    Pr[Win | seedFreeExperiment (internalize adversary) q steps] ≤ A + C * expectedFail := by
  refine le_trans (seedFree_le_exposeP adversary q steps) ?_
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

/-- **The deterministic signer from a bound of every sample of the truncated memoizing adversary**
(which never repeats a request and asks at most `signatureLimit` signatures). -/
theorem det_of_samplesSW (adversary : Adversary) (q : ℕ) (hbound : HasHashQueryBound adversary q) (A C : ℝ≥0∞)
    (hsample : ∀ steps parameterOutput fixed highs remaining prepared,
      prepared ∈ support (preparation parameterOutput fixed highs remaining) →
      ∀ known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
        (knownOf (truncateHash parameterOutput) fixed)),
      Pr[HiddenReveal.StopOr RichWin | HiddenOutside.stoppedExperiment (sampleModel parameterOutput highs)
          (erase (trace (richProgram (internalize (truncSign (Memo.memoAdv adversary) signatureLimit)) q
            (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)))) known
          prepared.2] ≤
        A + C * failMass (failSet prepared.1)) :
    forgeAdvantage adversary ≤ A + C * (2 : ℝ≥0∞)⁻¹ ^ 201 + 2 * ((q : ℝ≥0∞) / 2 ^ 256) := by
  refine le_trans (forgeAdvantage_le_seedFree_signBound adversary q hbound (A + C * expectedFail)
    fun steps => seedFree_boundSW _ q steps A C (hsample steps)) ?_
  gcongr
  exact expectedFail_le

end Close

end FORS.Security.SWRoute
