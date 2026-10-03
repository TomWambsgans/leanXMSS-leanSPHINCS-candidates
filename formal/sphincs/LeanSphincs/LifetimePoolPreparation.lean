import LeanSphincs.SecuritySeedCoupling
import LeanSphincs.LifetimePoolConcentration
import LeanSphincs.Landing
import LeanSphincs.LifetimePoolGrinding

/-! Presampling the complete finite first-digest-block table. Every public parameter, root,
message, and randomizer has a distinct byte input. The generic deferred-sampling theorem
therefore applies to the actual private-sampling/shared-ROM program, preserving its output
and any query counter included in that output. Preparation itself is unobserved. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness Security Security.SeedCoupling

abbrev FirstPoolPosition := PoolKey × Randomness
abbrev FirstPoolTable := FirstPoolPosition → HashOutput

noncomputable opaque firstPoolTableSampleableType : SampleableType FirstPoolTable :=
  SampleableType.ofFintype FirstPoolTable
noncomputable local instance : SampleableType FirstPoolTable := firstPoolTableSampleableType

def firstPoolInput (position : FirstPoolPosition) : HashInput :=
  tweakableHashInput position.1.1 (.message 0)
    (messageDigestPayload position.1.2.1 position.1.2.2 position.2)

theorem firstPoolInput_injective : Function.Injective firstPoolInput := by
  rintro ⟨⟨parameter, root, message⟩, rho⟩ ⟨⟨parameter', root', message'⟩, rho'⟩ heq
  obtain ⟨_, hp, hbody⟩ := tweakableInput_injective heq
  have hparts := List.append_inj hbody (by simp [messageDigestPayload, bytesLE_length])
  have hm : message = message' := bytesLE_injective hparts.2
  have hfirst := List.append_inj hparts.1 (by simp [bytesLE_length])
  have hrho : rho = rho' := bytesLE_injective hfirst.1
  have hroot : root = root' := bytesLE_injective hfirst.2
  cases hp; cases hroot; cases hm; cases hrho
  rfl

noncomputable def firstPoolCache (table : FirstPoolTable) : QueryCache HashSpec :=
  cacheTable ∅ firstPoolInput table

attribute [local irreducible] cacheTable cacheFin

theorem firstPoolCache_apply (table : FirstPoolTable) (position : FirstPoolPosition) :
    firstPoolCache table (firstPoolInput position) = some (table position) :=
  cacheTable_apply ∅ firstPoolInput firstPoolInput_injective table position

theorem evalDist_firstPool_preparation :
    𝒟[(simulateQ randomOracle (queryTable firstPoolInput)).run (∅ : QueryCache HashSpec)] =
      𝒟[(fun table : FirstPoolTable => (table, firstPoolCache table)) <$> ($ᵗ FirstPoolTable)] :=
  evalDist_queryTable_fresh firstPoolInput firstPoolInput_injective ∅ (fun _ => rfl)

/-- Exact lazy-to-presampled equivalence for arbitrary adaptive actual-world programs. -/
theorem evalDist_firstPool_continuation {α : Type} (program : OracleComp OracleWorld α) :
    𝒟[(simulateQ romImpl program).run' ∅] =
      𝒟[do
        let table ← $ᵗ FirstPoolTable
        (simulateQ romImpl program).run' (firstPoolCache table)] := by
  rw [evalDist_presample_computation program
    (liftM (queryTable firstPoolInput) : OracleComp OracleWorld FirstPoolTable) ∅,
    simulate_lift_hash]
  trans 𝒟[((fun table : FirstPoolTable => (table, firstPoolCache table)) <$> ($ᵗ FirstPoolTable)) >>=
    fun result => (simulateQ romImpl program).run' result.2]
  · rw [evalDist_bind, evalDist_firstPool_preparation, evalDist_bind]
  · rw [bind_map_left]

/-- An arbitrary finite table inherits coordinatewise uniformity through a uniform map. -/
theorem evalDist_uniform_table_map {J A B : Type} [Fintype J] [Fintype A] [Fintype B]
    [SampleableType A] [SampleableType B] [SampleableType (J → A)] [SampleableType (J → B)]
    (f : A → B) (hf : 𝒟[f <$> ($ᵗ A : ProbComp A)] = 𝒟[($ᵗ B : ProbComp B)]) :
    𝒟[(fun table : J → A => fun j => f (table j)) <$> ($ᵗ (J → A))] =
      𝒟[($ᵗ (J → B))] := by
  classical
  have htable (R : Type) [Fintype R] [SampleableType R] [SampleableType (J → R)] :
      𝒟[finTableEquiv J R <$> sequenceFin (fun _ : Fin (Fintype.card J) => ($ᵗ R : ProbComp R))] =
        𝒟[($ᵗ (J → R))] := by
    rw [evalDist_map, evalDist_sequenceFin_uniform, ← evalDist_map]
    exact evalDist_map_bijective_uniform_cross (α := Fin (Fintype.card J) → R) (β := J → R) (finTableEquiv J R) (finTableEquiv J R).bijective
  rw [evalDist_map, ← htable A, ← evalDist_map, Functor.map_map, ← htable B]
  have hfun : (fun table : Fin (Fintype.card J) → A =>
      fun j => f (finTableEquiv J A table j)) =
      fun table => finTableEquiv J B (fun i => f (table i)) := rfl
  rw [hfun, ← Functor.map_map, ← sequenceFin_map]
  rw [evalDist_map, evalDist_map]
  exact congrArg _ (evalDist_sequenceFin_congr _ _ (fun _ => hf))

def firstPoolIndexes (table : FirstPoolTable) : IndexPoolFamily := fun key rho =>
  blockIndex (table (key, rho))

theorem evalDist_firstPoolIndexes_uniform :
    𝒟[firstPoolIndexes <$> ($ᵗ FirstPoolTable)] = 𝒟[($ᵗ IndexPoolFamily)] := by
  let curry : (FirstPoolPosition → Index) → IndexPoolFamily := fun values key rho => values (key, rho)
  have hcurry : Function.Bijective curry := by
    constructor
    · intro left right heq
      funext pair
      exact congrFun (congrFun heq pair.1) pair.2
    · intro values
      exact ⟨fun pair => values pair.1 pair.2, rfl⟩
  have hm : firstPoolIndexes <$> ($ᵗ FirstPoolTable) =
      curry <$> ((fun table : FirstPoolTable => fun position => blockIndex (table position)) <$>
        ($ᵗ FirstPoolTable)) := by rw [Functor.map_map]; rfl
  rw [hm, evalDist_map, evalDist_uniform_table_map blockIndex evalDist_blockIndex_uniform,
    ← evalDist_map]
  exact evalDist_map_bijective_uniform_cross (α := FirstPoolPosition → Index) (β := IndexPoolFamily) curry hcurry

/-- The table presampled in the actual-ROM equivalence satisfies all pool balance constraints
except with probability2^-400; this holds simultaneously for adaptively selected messages. -/
theorem probEvent_firstPool_unbalanced :
    Pr[fun table => ¬AllPoolsBalanced (firstPoolIndexes table) | ($ᵗ FirstPoolTable)] ≤
      1 / (2 : ℝ≥0∞) ^ 400 := by
  classical
  rw [show (fun table => ¬AllPoolsBalanced (firstPoolIndexes table)) =
    (fun family => ¬AllPoolsBalanced family) ∘ firstPoolIndexes from rfl, ← probEvent_map]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) evalDist_firstPoolIndexes_uniform]
  have hprob : Pr[fun family => ¬AllPoolsBalanced family | ($ᵗ IndexPoolFamily)] =
      indexPoolFamilyMeasure {family | ¬AllPoolsBalanced family} := by
    rw [probEvent_eq_tsum_ite, indexPoolFamilyMeasure_eq_uniform,
      PMF.toMeasure_apply _ ((Set.toFinite _).measurableSet)]
    apply tsum_congr
    intro family
    simp only [Set.indicator_apply, Set.mem_setOf_eq, probOutput_uniformSample,
      PMF.uniformOfFintype_apply]
  rw [hprob]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, MeasureTheory.Measure.real] using poolFamily_unbalanced_negligible

variable [Params]

/-- Once presampled, actual grinding uses only cached first blocks and leaves the cache
unchanged, while retaining every private randomizer draw and exhaustion outcome. -/
theorem run_signDigestLoop_firstPool (table : FirstPoolTable) (sk : Seeded.SecretKey)
    (message : Message) (attempts : Nat) (cache : QueryCache HashSpec)
    (hcache : firstPoolCache table ≤ cache) :
    (simulateQ romImpl (Randomized.signDigestLoop sk message attempts)).run cache =
      (fun result => (result, cache)) <$>
        poolGrindRandomness sk.parameter (firstPoolIndexes table (sk.parameter, sk.root, message)) attempts := by
  induction attempts with
  | zero => simp only [Randomized.signDigestLoop, poolGrindRandomness, simulateQ_pure,
      StateT.run_pure, map_pure]
  | succ attempts ih =>
      rw [run_randomizedDigest_succ, poolGrindRandomness, map_bind]
      apply bind_congr
      intro rho
      have hlookup : cache (msgInput sk message rho) =
          some (table ((sk.parameter, sk.root, message), rho)) :=
        hcache (firstPoolCache_apply table ((sk.parameter, sk.root, message), rho))
      rw [QueryImpl.withCaching_run_some _ hlookup, pure_bind]
      simp only [firstPoolIndexes]
      split <;> simp only [map_pure, ih]

end LeanSphincs.Lifetime
