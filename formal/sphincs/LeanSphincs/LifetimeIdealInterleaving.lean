import LeanSphincs.LifetimeFutureBank
import LeanSphincs.Statement

/-!
Adaptive interleaving of actual digest-block queries with independent kept-view disclosures.
The adversary selects both query targets and the ordering of queries and disclosures from
the entire state. No averaged-price hypothesis is assumed: the exact occupancy forecast
pays every query. This is an intermediate experiment, not the actual signing experiment
when its randomizer selects an adversarially prequeried candidate.
-/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness

theorem expected_bind_le_of_support {α β : Type} (sample : ProbComp α) (next : α → ProbComp β)
    (weight : β → ℝ≥0∞) (bound : α → ℝ≥0∞)
    (h : ∀ value ∈ support sample, (∑' result, Pr[= result | next value] * weight result) ≤ bound value) :
    (∑' result, Pr[= result | sample >>= next] * weight result) ≤
      ∑' value, Pr[= value | sample] * bound value := by
  rw [tsum_probOutput_bind_mul]
  apply ENNReal.tsum_le_tsum
  intro value
  by_cases hvalue : value ∈ support sample
  · exact mul_le_mul' le_rfl (h value hvalue)
  · rw [probOutput_eq_zero_of_not_mem_support hvalue, zero_mul, zero_mul]

theorem expected_bind_le_constant {α β : Type} (sample : ProbComp α) (next : α → ProbComp β)
    (weight : β → ℝ≥0∞) (bound : ℝ≥0∞)
    (h : ∀ value ∈ support sample, (∑' result, Pr[= result | next value] * weight result) ≤ bound) :
    (∑' result, Pr[= result | sample >>= next] * weight result) ≤ bound := by
  refine (expected_bind_le_of_support sample next weight (fun _ => bound) h).trans ?_
  rw [ENNReal.tsum_mul_right]
  exact mul_le_of_le_one_left' tsum_probOutput_le_one

variable [Params]

abbrev FutureBankState := Finset KeptDigestView × DigestBankState

/-- `true` asks to query, while `false` asks for an independent disclosure. The budgets
force the remaining kind of action after the other budget is exhausted. -/
abbrev BankChoice (State : Type) := Bool × DigestCandidate × Fin 2 × State

noncomputable def idealInterleavedBank {State : Type} (sk : Seeded.SecretKey)
    (choose : Nat → Nat → State → FutureBankState → ProbComp (BankChoice State)) :
    Nat → Nat → State → FutureBankState → ProbComp FutureBankState
  | 0, 0, _, state => pure state
  | 0, n + 1, privateState, state => do
      let view ← ($ᵗ KeptDigestView : ProbComp KeptDigestView)
      idealInterleavedBank sk choose 0 n privateState (insert view state.1, state.2)
  | q + 1, 0, privateState, state => do
      let choice ← choose (q + 1) 0 privateState state
      let next ← digestBankStep sk choice.2.1 choice.2.2.1 state.2
      idealInterleavedBank sk choose q 0 choice.2.2.2 (state.1, next)
  | q + 1, n + 1, privateState, state => do
      let choice ← choose (q + 1) (n + 1) privateState state
      if choice.1 then
        let next ← digestBankStep sk choice.2.1 choice.2.2.1 state.2
        idealInterleavedBank sk choose q (n + 1) choice.2.2.2 (state.1, next)
      else
        let view ← ($ᵗ KeptDigestView : ProbComp KeptDigestView)
        idealInterleavedBank sk choose (q + 1) n choice.2.2.2 (insert view state.1, state.2)
termination_by q n _ _ => (q, n)

theorem expected_idealInterleavedBank_le {State : Type} (sk : Seeded.SecretKey)
    (choose : Nat → Nat → State → FutureBankState → ProbComp (BankChoice State)) :
    ∀ q n privateState state, DigestQueriesRecorded sk state.2.1 state.2.2 →
      (∑' final, Pr[= final | idealInterleavedBank sk choose q n privateState state] *
        futureBankPotential sk 0 0 final.1 final.2) ≤
          futureBankPotential sk q n state.1 state.2 := by
  intro q
  induction q with
  | zero =>
    intro n
    induction n with
    | zero =>
      intro privateState state _
      simp only [idealInterleavedBank, tsum_probOutput_pure_mul, le_rfl]
    | succ n ih =>
      intro privateState state hrecorded
      rw [idealInterleavedBank]
      refine (expected_bind_le_of_support _ _ _
        (fun view => futureBankPotential sk 0 n (insert view state.1) state.2) ?_).trans_eq
          (futureBankPotential_disclosure sk 0 n state.1 state.2)
      intro view _
      exact ih privateState (insert view state.1, state.2) hrecorded
  | succ q ihq =>
    intro n
    induction n with
    | zero =>
      intro privateState state hrecorded
      rw [idealInterleavedBank]
      apply expected_bind_le_constant
      intro choice _
      refine (expected_bind_le_of_support _ _ _
        (fun next => futureBankPotential sk q 0 state.1 next) ?_).trans
          (futureBankPotential_query sk q 0 state.1 state.2 hrecorded choice.2.1 choice.2.2.1)
      intro next hnext
      exact ihq 0 choice.2.2.2 (state.1, next)
        (digestBankStep_preserves sk choice.2.1 choice.2.2.1 state.2 hrecorded next hnext)
    | succ n ihn =>
      intro privateState state hrecorded
      rw [idealInterleavedBank]
      apply expected_bind_le_constant
      intro choice _
      cases hchoice : choice.1
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine (expected_bind_le_of_support _ _ _
          (fun view => futureBankPotential sk (q + 1) n (insert view state.1) state.2) ?_).trans_eq
            (futureBankPotential_disclosure sk (q + 1) n state.1 state.2)
        intro view _
        exact ihn choice.2.2.2 (insert view state.1, state.2) hrecorded
      · simp only [↓reduceIte]
        refine (expected_bind_le_of_support _ _ _
          (fun next => futureBankPotential sk q (n + 1) state.1 next) ?_).trans
            (futureBankPotential_query sk q (n + 1) state.1 state.2 hrecorded choice.2.1 choice.2.2.1)
        intro next hnext
        exact ihq (n + 1) choice.2.2.2 (state.1, next)
          (digestBankStep_preserves sk choice.2.1 choice.2.2.1 state.2 hrecorded next hnext)

def BankCovered (sk : Seeded.SecretKey) (state : FutureBankState) : Prop :=
  ∃ candidate ∈ state.2.1, ∃ first second,
    state.2.2 (candidateInput sk candidate 0) = some first ∧
    state.2.2 (candidateInput sk candidate 1) = some second ∧
    Landed sk.parameter (blockIndex first) ∧
    ViewCovered (localDigestView (truncateMessageDigest first second)) state.1

theorem probEvent_idealInterleavedBank_le {State : Type} (sk : Seeded.SecretKey)
    (choose : Nat → Nat → State → FutureBankState → ProbComp (BankChoice State))
    (q n : Nat) (privateState : State) (state : FutureBankState)
    (hrecorded : DigestQueriesRecorded sk state.2.1 state.2.2) :
    Pr[BankCovered sk | idealInterleavedBank sk choose q n privateState state] ≤
      futureBankPotential sk q n state.1 state.2 := by
  classical
  refine le_trans ?_ (expected_idealInterleavedBank_le sk choose q n privateState state hrecorded)
  rw [probEvent_eq_tsum_ite]
  apply ENNReal.tsum_le_tsum
  intro final
  by_cases hcovered : BankCovered sk final
  · rw [if_pos hcovered]
    obtain ⟨candidate, hmem, first, second, hfirst, hsecond, hland, hcover⟩ := hcovered
    simpa only [mul_one] using mul_le_mul' le_rfl
      (covered_candidate_le_futureBankPotential sk 0 final.1 final.2 candidate hmem first second
        hfirst hsecond hland hcover)
  · rw [if_neg hcovered]
    exact bot_le

/-- No fresh-price assumption: the explicit potential proves the full `q` times exact
occupancy bound for adaptive block search interleaved with independent disclosures. -/
theorem ideal_interleaving_lifetime_bound {State : Type} (sk : Seeded.SecretKey)
    (choose : Nat → Nat → State → FutureBankState → ProbComp (BankChoice State))
    (q n : Nat) (privateState : State) (cache : QueryCache HashSpec)
    (hfresh : ∀ candidate call, cache (candidateInput sk candidate call) = none) :
    Pr[BankCovered sk | idealInterleavedBank sk choose q n privateState (∅, ∅, cache)] ≤
      q * forsBoundENNReal subtreeHeight n := by
  refine (probEvent_idealInterleavedBank_le sk choose q n privateState (∅, ∅, cache)
    (fun candidate _ call => hfresh candidate call)).trans_eq ?_
  exact initial_futureBankPotential sk q n cache

theorem ideal_interleaving_after_keygen_bound {State : Type} (seed : MasterSeed)
    (result : (PublicKey × Seeded.SecretKey) × QueryCache HashSpec)
    (hsupport : result ∈ support ((simulateQ randomOracle (Seeded.keygenFromSeed seed)).run ∅))
    (choose : Nat → Nat → State → FutureBankState → ProbComp (BankChoice State))
    (q n : Nat) (privateState : State) :
    Pr[BankCovered result.1.2 |
      idealInterleavedBank result.1.2 choose q n privateState (∅, ∅, result.2)] ≤
        q * forsBoundENNReal subtreeHeight n :=
  ideal_interleaving_lifetime_bound result.1.2 choose q n privateState result.2
    (fun candidate call => keygen_message_inputs_fresh seed result hsupport candidate.1 candidate.2 call)

/-- This proposition is for the independent-disclosure intermediate experiment. It does not
assert replacement of the actual signer on an adversarially populated message cache. -/
def IdealInterleavingLifetimeBound : Prop :=
  ∀ (State : Type) (seed : MasterSeed)
    (result : (PublicKey × Seeded.SecretKey) × QueryCache HashSpec),
    result ∈ support ((simulateQ randomOracle (Seeded.keygenFromSeed seed)).run ∅) →
    ∀ (choose : Nat → Nat → State → FutureBankState → ProbComp (BankChoice State))
      (q n : Nat), n ≤ signatureLimit → ∀ privateState,
      Pr[BankCovered result.1.2 |
        idealInterleavedBank result.1.2 choose q n privateState (∅, ∅, result.2)] ≤
          (q : ℝ≥0∞) / 2 ^ 127

theorem idealInterleavingLifetimeBound_of_fors
    (hbound : ∀ n, n ≤ signatureLimit → forsBoundENNReal subtreeHeight n ≤ (1 : ℝ≥0∞) / 2 ^ 127) :
    IdealInterleavingLifetimeBound := by
  intro State seed result hsupport choose q n hn privateState
  refine (ideal_interleaving_after_keygen_bound seed result hsupport choose q n privateState).trans ?_
  simpa only [div_eq_mul_inv, one_mul] using mul_le_mul' (le_refl (q : ℝ≥0∞)) (hbound n hn)

open Lifetimes

omit [Params] in
theorem requested_ideal_interleaving_bounds :
    @IdealInterleavingLifetimeBound full ∧ @IdealInterleavingLifetimeBound pruned20 ∧
    @IdealInterleavingLifetimeBound pruned13 ∧ @IdealInterleavingLifetimeBound pruned14 ∧
    @IdealInterleavingLifetimeBound pruned12 ∧ @IdealInterleavingLifetimeBound pruned10 := by
  exact ⟨@idealInterleavingLifetimeBound_of_fors full (fun _ h => fors_lifetime_ennreal_full h),
    @idealInterleavingLifetimeBound_of_fors pruned20 (fun _ h => fors_lifetime_ennreal_pruned20 h),
    @idealInterleavingLifetimeBound_of_fors pruned13 (fun _ h => fors_lifetime_ennreal_pruned13 h),
    @idealInterleavingLifetimeBound_of_fors pruned14 (fun _ h => fors_lifetime_ennreal_pruned14 h),
    @idealInterleavingLifetimeBound_of_fors pruned12 (fun _ h => fors_lifetime_ennreal_pruned12 h),
    @idealInterleavingLifetimeBound_of_fors pruned10 (fun _ h => fors_lifetime_ennreal_pruned10 h)⟩

end LeanSphincs.Lifetime
