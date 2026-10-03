import LeanSphincs.LifetimeActualOccupancy

/-! The same occupancy estimate for a real adaptive prefix followed by independent uniform
kept views. The switch is explicit, and the number of total positions remains the exact N. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness Security
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] firstPoolCache Security.SeedCoupling.cacheTable Security.SeedCoupling.cacheFin
noncomputable local instance : SampleableType FirstPoolTable := firstPoolTableSampleableType
variable [Params]

noncomputable def uniformKeptIndex (parameter : PublicParameter) : ProbComp Index :=
  (fun view : KeptDigestView => (keptLeafEquiv parameter view.1).val) <$> ($ᵗ KeptDigestView)

theorem uniformKeptIndex_bound (parameter : PublicParameter) (index : Index) :
    Pr[fun result => result = index | uniformKeptIndex parameter] ≤
      ENNReal.ofReal ((1 + (1 : ℝ) / 2 ^ 18) / (2 : ℝ) ^ subtreeHeight) := by
  have hfst : 𝒟[Prod.fst <$> ($ᵗ KeptDigestView : ProbComp KeptDigestView)] =
      𝒟[($ᵗ Fin (2 ^ subtreeHeight) : ProbComp (Fin (2 ^ subtreeHeight)))] := by
    exact evalDist_map_fst_uniformSample_prod
  have hevent : Pr[fun result => result = index | uniformKeptIndex parameter] =
      Pr[fun j : Fin (2 ^ subtreeHeight) => (keptLeafEquiv parameter j).val = index | $ᵗ Fin (2 ^ subtreeHeight)] := by
    rw [uniformKeptIndex, probEvent_map]
    change Pr[(fun j : Fin (2 ^ subtreeHeight) => (keptLeafEquiv parameter j).val = index) ∘ Prod.fst | _] = _
    rw [← probEvent_map]
    exact probEvent_congr' (fun _ _ => Iff.rfl) hfst
  rw [hevent]
  have hbase : Pr[fun j : Fin (2 ^ subtreeHeight) => (keptLeafEquiv parameter j).val = index |
      $ᵗ Fin (2 ^ subtreeHeight)] ≤ 1 / ((2 ^ subtreeHeight : Nat) : ℝ≥0∞) := by
    by_cases hland : Landed parameter index
    · have heq (j : Fin (2 ^ subtreeHeight)) : (keptLeafEquiv parameter j).val = index ↔
          j = (keptLeafEquiv parameter).symm ⟨index, hland⟩ := by
        rw [Equiv.eq_symm_apply]
        constructor
        · intro h
          apply Subtype.ext
          exact h
        · exact congrArg Subtype.val
      simp_rw [heq]
      rw [probEvent_eq_eq_probOutput, probOutput_uniformSample, Fintype.card_fin]
      simp only [one_div, le_refl]
    · have hempty : Pr[fun j : Fin (2 ^ subtreeHeight) => (keptLeafEquiv parameter j).val = index |
          $ᵗ Fin (2 ^ subtreeHeight)] = 0 := by
        apply probEvent_eq_zero
        intro j _ heq
        exact hland (heq ▸ (keptLeafEquiv parameter j).property)
      rw [hempty]
      exact bot_le
  refine hbase.trans ?_
  have hnum : ENNReal.ofReal (1 + (1 : ℝ) / 2 ^ 18) = 1 + (1 : ℝ≥0∞) / 2 ^ 18 := by
    rw [ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ 1 / 2 ^ 18),
      ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ 18)]
    norm_num
  simp only [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ subtreeHeight), hnum,
    ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  exact ENNReal.div_le_div_right (le_add_of_nonneg_right (by positivity)) _

noncomputable def hybridIndexStep {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (actual : Nat → Bool)
    (n : Nat) (state : State × QueryCache HashSpec) : ProbComp (Option Index × (State × QueryCache HashSpec)) :=
  if actual n then interleavedIndexStep sk interlude update n state
  else (fun index => (some index, state)) <$> uniformKeptIndex sk.parameter

noncomputable def hybridIndexProgram {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (actual : Nat → Bool) :
    Nat → State → OracleComp OracleWorld (List (Option Index))
  | 0, _ => pure []
  | n + 1, state =>
      if actual n then do
        let request ← interlude n state
        let signed ← indexedSignProgram sk request.1
        let rest ← hybridIndexProgram sk interlude update actual n (update request.2 signed.2)
        pure (signed.1 :: rest)
      else do
        let index ← (liftM (uniformKeptIndex sk.parameter) : OracleComp OracleWorld Index)
        let rest ← hybridIndexProgram sk interlude update actual n state
        pure (some index :: rest)

theorem run'_hybridIndexProgram {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (actual : Nat → Bool) (n : Nat)
    (state : State) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (hybridIndexProgram sk interlude update actual n state)).run' cache =
      adaptiveIndexTrace (hybridIndexStep sk interlude update actual) n (state, cache) := by
  induction n generalizing state cache with
  | zero => simp only [hybridIndexProgram, adaptiveIndexTrace, simulateQ_pure,
      StateT.run'_eq, StateT.run_pure, map_pure]
  | succ n ih =>
      rw [hybridIndexProgram, adaptiveIndexTrace, hybridIndexStep]
      split
      · simp only [interleavedIndexStep, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
          map_bind, bind_assoc, run_indexedSignProgram, bind_map_left, pure_bind,
          simulateQ_pure, StateT.run_pure, map_pure]
        apply bind_congr
        intro request
        apply bind_congr
        intro signed
        have h := congrArg (Functor.map (fun rest => signed.1 :: rest))
          (ih (update request.1.2 signed.2.1) signed.2.2)
        simpa only [StateT.run'_eq, Functor.map_map, bind_pure_comp, Function.comp_def] using h
      · simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind, bind_map_left,
          run_lift_prob, simulateQ_pure, StateT.run_pure, map_pure]
        apply bind_congr
        intro index
        have h := congrArg (Functor.map (fun rest => some index :: rest)) (ih state cache)
        simpa only [StateT.run'_eq, Functor.map_map, bind_pure_comp, Function.comp_def] using h

theorem prepared_hybrid_occupancy {State : Type} (table : FirstPoolTable)
    (hbalanced : AllPoolsBalanced (firstPoolIndexes table)) (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (actual : Nat → Bool) (n : Nat)
    (hpair : (subtreeHeight, n) ∈ requestedLifetimePairs) (state : State × QueryCache HashSpec)
    (hcache : firstPoolCache table ≤ state.2) :
    Pr[fun trace => ∃ index, 256 ≤ trace.count (some index) |
      adaptiveIndexTrace (hybridIndexStep sk interlude update actual) n state] ≤ 1 / (2 : ℝ≥0∞) ^ 294 := by
  apply adaptiveIndexTrace_tail_of_invariant (fun state : State × QueryCache HashSpec => firstPoolCache table ≤ state.2)
    (hybridIndexStep sk interlude update actual) _
    ((1 + (1 : ℝ) / 2 ^ 18) / (2 : ℝ) ^ subtreeHeight) (by positivity) _
    n (requested_pool_occupancy_mean hpair) state hcache
  · intro remaining current hcurrent result hresult
    rw [hybridIndexStep] at hresult
    split at hresult
    · exact hcurrent.trans (interleavedIndexStep_cache_le sk interlude update remaining current result hresult)
    · rw [support_map] at hresult
      obtain ⟨_, _, rfl⟩ := hresult
      exact hcurrent
  · intro remaining current hcurrent index
    rw [hybridIndexStep]
    split
    · exact interleavedIndexStep_prepared_bound table hbalanced sk interlude update remaining current hcurrent index
    · simpa only [probEvent_map, Function.comp_def, Option.some.injEq] using uniformKeptIndex_bound sk.parameter index

/-- Covers every deterministic placement of the real prefix/uniform suffix switch. -/
theorem actual_hybrid_occupancy {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (actual : Nat → Bool) (n : Nat)
    (hpair : (subtreeHeight, n) ∈ requestedLifetimePairs) (state : State) :
    Pr[fun trace => ∃ index, 256 ≤ trace.count (some index) |
      adaptiveIndexTrace (hybridIndexStep sk interlude update actual) n (state, ∅)] ≤
      1 / (2 : ℝ≥0∞) ^ 400 + 1 / 2 ^ 294 := by
  rw [← run'_hybridIndexProgram]
  rw [probEvent_congr' (fun _ _ => Iff.rfl)
    (evalDist_firstPool_continuation (hybridIndexProgram sk interlude update actual n state))]
  refine (probEvent_bind_le_probEvent_add (p := fun table => ¬AllPoolsBalanced (firstPoolIndexes table)) ?_).trans
    (add_le_add probEvent_firstPool_unbalanced le_rfl)
  intro table _ hbalanced
  have hbalanced' : AllPoolsBalanced (firstPoolIndexes table) := Classical.not_not.mp hbalanced
  rw [run'_hybridIndexProgram]
  have hcache : firstPoolCache table ≤ firstPoolCache table := fun _ _ h => h
  exact prepared_hybrid_occupancy table hbalanced' sk interlude update actual n hpair (state, firstPoolCache table) hcache

end LeanSphincs.Lifetime
