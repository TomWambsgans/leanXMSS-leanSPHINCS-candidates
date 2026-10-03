import LeanSphincs.LifetimePreparedOccupancy

/-! Empty-ROM occupancy of actual adaptive signing, obtained by reifying the accepted-index
record as part of the oracle program before applying finite-table presampling. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness Security
set_option backward.isDefEq.respectTransparency false
noncomputable local instance : SampleableType FirstPoolTable := firstPoolTableSampleableType
attribute [local instance] Classical.propDecidable
attribute [local irreducible] firstPoolCache Security.SeedCoupling.cacheTable Security.SeedCoupling.cacheFin
variable [Params]

noncomputable def indexedSignProgram (sk : Seeded.SecretKey) (message : Message) :
    OracleComp OracleWorld (Option Index × Option Signature) := do
  let randomness ← Randomized.signDigestLoop sk message digestAttemptLimit
  match randomness with
  | none => pure (none, none)
  | some randomness =>
      let digest ← (liftM (messageDigest sk.parameter sk.root message randomness : OracleComp HashSpec MessageDigest) :
        OracleComp OracleWorld MessageDigest)
      let signature ← (liftM (finishSignBody sk randomness digest) : OracleComp OracleWorld (Option Signature))
      pure (some (digestIndex digest), signature)

theorem indexedSignProgram_erase (sk : Seeded.SecretKey) (message : Message) :
    Prod.snd <$> indexedSignProgram sk message = Randomized.sign sk message := by
  simp only [indexedSignProgram, Randomized.sign, map_bind]
  apply bind_congr
  intro result
  cases result with
  | none => rfl
  | some rho =>
      dsimp only
      rw [finishSign_eq_digest_body]
      simp only [liftM_bind, map_bind, map_pure, bind_pure]

theorem run_indexedSignProgram (sk : Seeded.SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (indexedSignProgram sk message)).run cache =
      (fun result => ((result.1, result.2.1), result.2.2)) <$> indexedSign sk message cache := by
  simp only [indexedSignProgram, indexedSign, signWithSources, simulateQ_bind, StateT.run_bind,
    Functor.map_map, map_bind]
  apply bind_congr
  rintro ⟨loop, middle⟩
  cases loop with
  | none => simp only [simulateQ_pure, StateT.run_pure, map_pure]; rfl
  | some rho =>
      simp only [simulate_lift_hash, simulateQ_bind, StateT.run_bind, map_bind,
        simulateQ_pure, StateT.run_pure, map_pure]
      rfl

noncomputable def interleavedIndexProgram {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) : Nat → State → OracleComp OracleWorld (List (Option Index))
  | 0, _ => pure []
  | n + 1, state => do
      let request ← interlude n state
      let signed ← indexedSignProgram sk request.1
      let rest ← interleavedIndexProgram sk interlude update n (update request.2 signed.2)
      pure (signed.1 :: rest)

/-- The executable index observer exactly realizes the probability transition system used
by the occupancy estimate; every interlude, signing response, and shared cache is retained. -/
theorem run'_interleavedIndexProgram {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (n : Nat) (state : State) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (interleavedIndexProgram sk interlude update n state)).run' cache =
      adaptiveIndexTrace (interleavedIndexStep sk interlude update) n (state, cache) := by
  induction n generalizing state cache with
  | zero => simp only [interleavedIndexProgram, adaptiveIndexTrace, simulateQ_pure,
      StateT.run'_eq, StateT.run_pure, map_pure]
  | succ n ih =>
      simp only [interleavedIndexProgram, adaptiveIndexTrace, interleavedIndexStep,
        simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind, bind_assoc,
        run_indexedSignProgram, bind_map_left, pure_bind, simulateQ_pure, StateT.run_pure, map_pure]
      apply bind_congr
      intro request
      apply bind_congr
      intro signed
      have h := congrArg (Functor.map (fun rest => signed.1 :: rest))
        (ih (update request.1.2 signed.2.1) signed.2.2)
      simpa only [StateT.run'_eq, Functor.map_map, bind_pure_comp, Function.comp_def] using h

/-- Actual lazy-ROM signing has the prepared occupancy bound plus the independently
certified probability that some global first-block grinding pool is unbalanced. -/
theorem actual_interleaved_signing_occupancy {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (n : Nat)
    (hpair : (subtreeHeight, n) ∈ requestedLifetimePairs) (state : State) :
    Pr[fun trace => ∃ index, 256 ≤ trace.count (some index) |
      adaptiveIndexTrace (interleavedIndexStep sk interlude update) n (state, ∅)] ≤
      1 / (2 : ℝ≥0∞) ^ 400 + 1 / 2 ^ 294 := by
  rw [← run'_interleavedIndexProgram]
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_firstPool_continuation (interleavedIndexProgram sk interlude update n state))]
  refine (probEvent_bind_le_probEvent_add (p := fun table => ¬AllPoolsBalanced (firstPoolIndexes table)) ?_).trans
    (add_le_add probEvent_firstPool_unbalanced le_rfl)
  intro table _ hbalanced
  have hbalanced' : AllPoolsBalanced (firstPoolIndexes table) := Classical.not_not.mp hbalanced
  rw [run'_interleavedIndexProgram]
  have hcache : firstPoolCache table ≤ firstPoolCache table := fun _ _ h => h
  have hbound := interleaved_signing_occupancy (State := State) table hbalanced' sk interlude update n hpair
    (state, firstPoolCache table) hcache
  convert hbound using 1

end LeanSphincs.Lifetime
