import LeanSphincs.SecurityHiddenCost
import LeanSphincs.SecuritySeedGuess

/-! Seed monitoring and domain allocation on the shared capped hidden-coordinate comparison.
Every expectation below is evaluated on that comparison's actual joint trace. No count from
the earlier material-only game is reused after changing the oracle experiment. -/

open OracleComp OracleSpec ENNReal
namespace LeanSphincs.Security.HiddenCost
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 100000
attribute [local instance] Classical.propDecidable

def traceCharge {D : Type} (weight : Entry D → Nat) (entries : List (Entry D)) : Nat :=
  (entries.map weight).sum

theorem traceCharge_add_le {D : Type} (left right : Entry D → Nat)
    (hweight : ∀ entry, left entry + right entry ≤ entryCost entry) (entries : List (Entry D)) :
    traceCharge left entries + traceCharge right entries ≤ traceCost entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      have h := hweight entry
      simp only [traceCharge, traceCost, List.map_cons, List.sum_cons] at ih ⊢
      omega

noncomputable def expectedTraceCharge {D Ω : Type} (program : ProbComp Ω)
    (entries : Ω → List (Entry D)) (weight : Entry D → Nat) : ℝ≥0∞ :=
  ∑' result, Pr[= result | program] * (traceCharge weight (entries result) : ℝ≥0∞)

/-- Complementary domain charges share the realized total cost, including any virtual ticks. -/
theorem expectedTraceCharge_add_le {D Ω : Type} (program : ProbComp Ω)
    (entries : Ω → List (Entry D)) (left right : Entry D → Nat)
    (hweight : ∀ entry, left entry + right entry ≤ entryCost entry)
    (budget : Nat) (hbudget : ∀ result ∈ support program, traceCost (entries result) ≤ budget) :
    expectedTraceCharge program entries left + expectedTraceCharge program entries right ≤ budget := by
  unfold expectedTraceCharge
  rw [← ENNReal.tsum_add]
  calc
    _ ≤ ∑' result, Pr[= result | program] * (budget : ℝ≥0∞) := by
      apply ENNReal.tsum_le_tsum
      intro result
      rw [← mul_add, ← Nat.cast_add]
      by_cases hr : result ∈ support program
      · exact mul_le_mul' le_rfl (by exact_mod_cast
          (traceCharge_add_le left right hweight (entries result)).trans (hbudget result hr))
      · rw [probOutput_eq_zero_of_not_mem_support hr]
        simp
    _ ≤ _ := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left zero_le tsum_probOutput_le_one

noncomputable def seedWeight : Entry HashInput → Nat
  | .inl input => if (SeedGuess.parseSeed input).isSome then 1 else 0
  | .inr _ => 0

noncomputable def nonseedWeight : Entry HashInput → Nat
  | .inl input => if (SeedGuess.parseSeed input).isSome then 0 else 1
  | .inr _ => 0

theorem seed_nonseed_entry_le (entry : Entry HashInput) :
    seedWeight entry + nonseedWeight entry ≤ entryCost entry := by
  cases entry with
  | inl input => simp only [seedWeight, nonseedWeight, entryCost]; split <;> omega
  | inr amount => simp [seedWeight, nonseedWeight, entryCost]

theorem seedWeight_verifier (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    seedWeight (.inl (tweakableHashInput parameter domain payload)) = 0 := by
  simp [seedWeight, SeedGuess.parseSeed_verifier]

theorem seedWeight_keygen (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    seedWeight (.inl (keygenHashInput parameter domain seed)) = 1 := by
  simp [seedWeight, SeedGuess.parseSeed_keygen]

def EntrySeedHit (entry : Entry HashInput) (seed : MasterSeed) : Prop :=
  match entry with
  | .inl input => SeedGuess.SeedHit input seed
  | .inr _ => False

def TraceSeedHit (entries : List (Entry HashInput)) (seed : MasterSeed) : Prop :=
  ∃ entry ∈ entries, EntrySeedHit entry seed

theorem entry_seed_probability (entry : Entry HashInput) :
    Pr[EntrySeedHit entry | sampleMasterSeed] ≤ (seedWeight entry : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 := by
  cases entry with
  | inr amount => simp [EntrySeedHit, seedWeight]
  | inl input =>
      cases hp : SeedGuess.parseSeed input with
      | some seed =>
          change Pr[SeedGuess.SeedHit input | sampleMasterSeed] ≤ _
          simpa only [seedWeight, hp, Option.isSome_some, ↓reduceIte, Nat.cast_one] using
            SeedGuess.seedHit_probability_le input
      | none =>
          have hfalse : EntrySeedHit (.inl input) = fun _ => False := by
            funext seed
            apply propext
            constructor
            · intro h
              have hs := (SeedGuess.parseSeed_eq_some_iff input seed).mpr h
              rw [hp] at hs
              cases hs
            · exact False.elim
          simp [hfalse, seedWeight, hp]

theorem trace_seed_probability (entries : List (Entry HashInput)) :
    Pr[TraceSeedHit entries | sampleMasterSeed] ≤
      (traceCharge seedWeight entries : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 := by
  induction entries with
  | nil => simp [TraceSeedHit, traceCharge]
  | cons entry entries ih =>
      have hevent : TraceSeedHit (entry :: entries) =
          fun seed => EntrySeedHit entry seed ∨ TraceSeedHit entries seed := by
        funext seed
        simp [TraceSeedHit]
      rw [hevent]
      calc
        _ ≤ Pr[EntrySeedHit entry | sampleMasterSeed] + Pr[TraceSeedHit entries | sampleMasterSeed] :=
          probEvent_or_le _ _ _
        _ ≤ (seedWeight entry : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 +
            (traceCharge seedWeight entries : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 :=
          add_le_add (entry_seed_probability entry) ih
        _ = _ := by simp [traceCharge, Nat.cast_add, ENNReal.add_div]

/-- The seed is sampled independently of the entire concrete trace-producing comparison;
adaptive failed guesses need no conditional-uniformity hypothesis. -/
theorem seed_monitor_bound {Ω : Type} (program : ProbComp Ω)
    (entries : Ω → List (Entry HashInput)) :
    Pr[= true | sampleMasterSeed >>= fun seed =>
      (fun result => decide (TraceSeedHit (entries result) seed)) <$> program] ≤
      expectedTraceCharge program entries seedWeight / (2 : ℝ≥0∞) ^ 256 := by
  calc
    _ = Pr[= true | program >>= fun result =>
        (fun seed => decide (TraceSeedHit (entries result) seed)) <$> sampleMasterSeed] := by
      simp only [← bind_pure_comp]
      exact probOutput_bind_bind_swap _ _ _ _
    _ ≤ ∑' result, Pr[= result | program] *
        ((traceCharge seedWeight (entries result) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256) := by
      simp only [probOutput_bind_eq_tsum, probOutput_map, decide_eq_true_eq]
      exact ENNReal.tsum_le_tsum fun result => mul_le_mul' le_rfl (trace_seed_probability (entries result))
    _ = _ := by simp only [div_eq_mul_inv, ← mul_assoc, ENNReal.tsum_mul_right, expectedTraceCharge]

theorem common_seed_bound {R A ι α : Type} [Fintype ι]
    (model : HiddenRows.Model HashInput R A ι) (outside : HashInput → R)
    (computation : OracleComp (SourceCostSpec HashInput R ι) α) (known : HiddenReveal.Knowledge ι) :
    Pr[= true | sampleMasterSeed >>= fun seed =>
      (fun result => decide (TraceSeedHit result.1.2 seed)) <$> comparison model outside computation known] ≤
      expectedTraceCharge (comparison model outside computation known) (fun result => result.1.2)
        seedWeight / (2 : ℝ≥0∞) ^ 256 :=
  seed_monitor_bound _ _

/-- The seed-domain charge and all remaining ordinary domains share one capped trace. -/
theorem capped_seed_nonseed_allocation {R A ι α : Type} [Fintype ι]
    (model : HiddenRows.Model HashInput R A ι) (outside : HashInput → R)
    (computation : OracleComp (SourceCostSpec HashInput R ι) α) (known : HiddenReveal.Knowledge ι)
    (budget : Nat) :
    expectedTraceCharge (comparison model outside (cap computation budget) known)
        (fun result => result.1.2) seedWeight +
      expectedTraceCharge (comparison model outside (cap computation budget) known)
        (fun result => result.1.2) nonseedWeight ≤ budget :=
  expectedTraceCharge_add_le _ _ seedWeight nonseedWeight seed_nonseed_entry_le budget
    (capped_comparison_cost_le model outside computation known budget)

end LeanSphincs.Security.HiddenCost
