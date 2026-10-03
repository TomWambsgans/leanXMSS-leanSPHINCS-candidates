import LeanSphincs.SecurityDomains
import LeanSphincs.Uniform

/-!
Exact derivation-input parsing and adaptive hidden-seed guessing. The hidden seed in this module
is sampled independently of the strategy's initial state and private randomness. The strategy
learns only whether each selected input names that seed, and may adapt after every failed guess.
Connecting this experiment to the actual seeded signature game remains a separate coupling proof.
-/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.SeedGuess

attribute [local instance] Classical.propDecidable
set_option maxRecDepth 10000

/-- This complete byte input is a candidate derivation query naming the given master seed. -/
def SeedHit (input : HashInput) (seed : MasterSeed) : Prop :=
  ∃ parameter domain, keygenHashInput parameter domain seed = input

/-- Whatever derivation address an input uses, it can name at most one 256-bit seed. -/
theorem seedHit_unique {input : HashInput} {seed seed' : MasterSeed}
    (h : SeedHit input seed) (h' : SeedHit input seed') : seed = seed' := by
  obtain ⟨parameter, domain, heq⟩ := h
  obtain ⟨parameter', domain', heq'⟩ := h'
  exact (keygenInput_injective (heq.trans heq'.symm)).2.2

/-- Exact logical parser for derivation inputs. Invalid inputs produce `none`; valid inputs
produce the unique seed whose actual 32-byte little-endian serialization occupies the payload. -/
noncomputable def parseSeed (input : HashInput) : Option MasterSeed :=
  if h : ∃ seed, SeedHit input seed then some (Classical.choose h) else none

theorem parseSeed_eq_some_iff (input : HashInput) (seed : MasterSeed) :
    parseSeed input = some seed ↔ SeedHit input seed := by
  classical
  unfold parseSeed
  split
  next h =>
    constructor
    · intro heq
      cases Option.some.inj heq
      exact Classical.choose_spec h
    · intro hseed
      exact congrArg some (seedHit_unique (Classical.choose_spec h) hseed)
  next h =>
    constructor
    · simp
    · intro hseed
      exact False.elim (h ⟨seed, hseed⟩)

theorem parseSeed_keygen (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) :
    parseSeed (keygenHashInput parameter domain seed) = some seed :=
  (parseSeed_eq_some_iff _ _).2 ⟨parameter, domain, rfl⟩

/-- Verifier inputs can never be mistaken for derivation inputs, even across public parameters. -/
theorem parseSeed_verifier (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    parseSeed (tweakableHashInput parameter domain payload) = none := by
  cases h : parseSeed (tweakableHashInput parameter domain payload) with
  | none => rfl
  | some seed =>
      obtain ⟨parameter', domain', heq⟩ := (parseSeed_eq_some_iff _ _).1 h
      exact False.elim (keygenInput_ne_hashInput parameter' parameter domain' domain seed payload heq)

/-- Each fixed byte input contributes at most one equality guess against a uniform hidden seed. -/
theorem seedHit_probability_le (input : HashInput) :
    Pr[SeedHit input | sampleMasterSeed] ≤ 1 / (2 : ℝ≥0∞) ^ 256 := by
  classical
  letI := SampleableType.ofFintype MasterSeed
  rw [show sampleMasterSeed = ($ᵗ MasterSeed : ProbComp MasterSeed) from rfl,
    probEvent_uniformSample]
  have hcard : (Finset.univ.filter (SeedHit input)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro seed hseed seed' hseed'
    exact seedHit_unique (Finset.mem_filter.mp hseed).2 (Finset.mem_filter.mp hseed').2
  rw [show Fintype.card MasterSeed = 2 ^ 256 by simp, Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.div_le_div_right (by exact_mod_cast hcard) _

def SeedHitLog (inputs : List HashInput) (seed : MasterSeed) : Prop :=
  ∃ input ∈ inputs, SeedHit input seed

/-- A seed-independent query list of length `q` names at most `q` candidate seeds. -/
theorem seedHitLog_probability_le (inputs : List HashInput) :
    Pr[SeedHitLog inputs | sampleMasterSeed] ≤ (inputs.length : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 := by
  induction inputs with
  | nil => simp [SeedHitLog]
  | cons input inputs ih =>
      have hevent : SeedHitLog (input :: inputs) =
          fun seed => SeedHit input seed ∨ SeedHitLog inputs seed := by
        funext seed
        simp [SeedHitLog]
      rw [hevent]
      calc
        _ ≤ Pr[SeedHit input | sampleMasterSeed] + Pr[SeedHitLog inputs | sampleMasterSeed] :=
          probEvent_or_le _ _ _
        _ ≤ 1 / (2 : ℝ≥0∞) ^ 256 + (inputs.length : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 :=
          add_le_add (seedHit_probability_le input) ih
        _ = _ := by simp [List.length_cons, Nat.cast_add, ENNReal.add_div, add_comm]

/-- An adaptive query choice and its state transition after an equality-oracle reply. -/
structure Trial (σ : Type) where
  input : HashInput
  next : Bool → σ

/-- Private random choices depend on prior state, never directly on the hidden seed. -/
abbrev Strategy (σ : Type) := σ → ProbComp (Option (Trial σ))

/-- At most `q` adaptive equality guesses. The strategy sees each failed guess, and stops on the
first success. The input is parsed using the actual candidate derivation layouts. -/
noncomputable def monitor {σ : Type} (choose : Strategy σ) (seed : MasterSeed) :
    Nat → σ → ProbComp Bool
  | 0, _ => pure false
  | q + 1, state => do
      let some trial ← choose state | return false
      if parseSeed trial.input = some seed then return true
      else monitor choose seed q (trial.next false)

/-- The hidden seed is sampled once and retained for every adaptive guess. -/
noncomputable def experiment {σ : Type} (choose : Strategy σ) (q : Nat) (state : σ) : ProbComp Bool :=
  sampleMasterSeed >>= fun seed => monitor choose seed q state

private theorem probe_then_continue_le (input : HashInput) (tail : MasterSeed → ProbComp Bool) :
    Pr[fun hit => hit = true | sampleMasterSeed >>= fun seed =>
      if parseSeed input = some seed then pure true else tail seed] ≤
        Pr[SeedHit input | sampleMasterSeed] +
          Pr[fun hit => hit = true | sampleMasterSeed >>= tail] := by
  classical
  rw [probEvent_bind_eq_tsum, probEvent_eq_tsum_ite (p := SeedHit input),
    probEvent_bind_eq_tsum, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro seed
  by_cases hhit : SeedHit input seed
  · have hparse := (parseSeed_eq_some_iff _ _).2 hhit
    simp only [hparse, ↓reduceIte, probEvent_pure, hhit, mul_one]
    exact le_add_right le_rfl
  · have hparse : parseSeed input ≠ some seed := fun h => hhit ((parseSeed_eq_some_iff _ _).1 h)
    simp [hhit, hparse]

/-- Private randomness and failed-guess feedback do not improve `q` equality guesses beyond
`q / 2^256`. The strategy may select completely different inputs after each failure. -/
theorem adaptive_seed_guess_bound {σ : Type} (choose : Strategy σ) : ∀ (q : Nat) (state : σ),
    Pr[fun hit => hit = true | experiment choose q state] ≤ (q : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 := by
  intro q
  induction q with
  | zero => intro state; simp [experiment, monitor]
  | succ q ih =>
      intro state
      rw [experiment]
      simp only [monitor]
      rw [probEvent_bind_bind_swap]
      apply probEvent_bind_le_of_forall_le
      intro selection _
      cases selection with
      | none => simp
      | some trial =>
          calc
            _ ≤ Pr[SeedHit trial.input | sampleMasterSeed] +
                Pr[fun hit => hit = true | experiment choose q (trial.next false)] :=
              probe_then_continue_le trial.input _
            _ ≤ 1 / (2 : ℝ≥0∞) ^ 256 + (q : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 :=
              add_le_add (seedHit_probability_le _) (ih _)
            _ = _ := by rw [Nat.cast_add, Nat.cast_one, ENNReal.add_div, add_comm]

/-- A privately randomized initial state remains safe when sampled independently of the seed. -/
theorem initialized_adaptive_seed_guess_bound {σ : Type} (choose : Strategy σ) (q : Nat)
    (initial : ProbComp σ) :
    Pr[fun hit => hit = true | initial >>= fun state => experiment choose q state] ≤
      (q : ℝ≥0∞) / (2 : ℝ≥0∞) ^ 256 :=
  probEvent_bind_le_of_forall_le (fun state _ => adaptive_seed_guess_bound choose q state)

end LeanSphincs.Security.SeedGuess
