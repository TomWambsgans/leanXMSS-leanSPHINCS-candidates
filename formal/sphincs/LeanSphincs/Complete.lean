import LeanSphincs.Fresh
import LeanSphincs.RandomizedDigest

/-! Honest randomized signing: composition of the two exhaustion bounds. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Completeness

open Concrete

/-- No WOTS+C encoding input has yet been queried, for any key or message. -/
def EncodingFresh (cache : QueryCache HashSpec) : Prop :=
  ∀ parameter lay tree leaf message c, cache (encodeInput parameter lay tree leaf message c) = none

theorem encodingFresh_empty : EncodingFresh (∅ : QueryCache HashSpec) := by
  intro parameter lay tree leaf message c
  rfl

/-- Structural computation preserves the entire unused encoding domain. -/
theorem encodingFresh_of_preserves {α : Type} (oa : OracleComp HashSpec α)
    (h : ∀ parameter lay tree leaf message c,
      PreservesFresh (encodeInput parameter lay tree leaf message c) oa)
    (cache : QueryCache HashSpec) (hfresh : EncodingFresh cache)
    (r : α × QueryCache HashSpec) (hr : r ∈ support ((simulateQ randomOracle oa).run cache)) :
    EncodingFresh r.2 := by
  intro parameter lay tree leaf message c
  exact h parameter lay tree leaf message c cache r hr (hfresh ..)

variable [Params]

attribute [local irreducible] encodingAttemptLimit digestAttemptLimit
  Seeded.treePath Seeded.ftsKey Seeded.ftsOpen Seeded.otsSign Concrete.sequenceFin

/-- A single layer can fail only in its counter search. -/
theorem signLayer_exhaustion_bound (sk : Seeded.SecretKey) (index : Index) (lay : Layer)
    (cache : QueryCache HashSpec) (hfresh : EncodingFresh cache) :
    Pr[fun r => r.1 = none | (simulateQ randomOracle
      (Seeded.signLayer sk index lay : OracleComp HashSpec (Option (LayerSignature lay)))).run cache]
      ≤ (2⁻¹ : ℝ≥0∞) ^ (2 ^ 22) := by
  rw [Seeded.signLayer]
  apply probEvent_bind_le
  intro mid hmid
  have hmidfresh : EncodingFresh mid.2 := encodingFresh_of_preserves _
    (fun parameter lay tree leaf message c =>
      PreservesFresh.ftsKey (structuralFresh_encoding parameter lay tree leaf message c) _ _ _)
    cache hfresh mid hmid
  refine (show _ ≤ Pr[fun r => r.1 = none |
    (simulateQ randomOracle (Seeded.otsSign sk.parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) sk.seed mid.1 : OracleComp HashSpec _)).run mid.2] from ?_).trans
        (encoding_exhaustion_bound _ _ _ _ _ _ _ (fun c _ => hmidfresh ..))
  rw [simulateQ_bind, StateT.run_bind]
  apply probEvent_bind_le_probEvent
  intro r _ hsome
  cases h : r.1 with
  | none => exact False.elim (hsome h)
  | some value =>
      simp only [simulateQ_bind, StateT.run_bind]
      apply le_antisymm _ zero_le
      apply probEvent_bind_le_of_forall_le
      intro result _
      simp

/-- Signature assembly has just one WOTS+C search. FORS work and digest calls preserve its
unused encoding domain, so they need no independent random-oracle assumption. -/
theorem finishSign_exhaustion_bound (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) (hfresh : EncodingFresh cache) :
    Pr[fun r => r.1 = none |
      (simulateQ randomOracle (Randomized.finishSign sk message randomness)).run cache]
      ≤ (2⁻¹ : ℝ≥0∞) ^ (2 ^ 22) := by
  rw [Randomized.finishSign]
  apply probEvent_bind_le
  intro digest hdigest
  have hdigestfresh : EncodingFresh digest.2 := encodingFresh_of_preserves _
    (fun parameter lay tree leaf m c => PreservesFresh.messageDigest _ _ _ _
      (fun block => messageInput_ne_encoding _ _ _ _ block parameter lay tree leaf m c))
    cache hfresh digest hdigest
  apply probEvent_bind_le
  intro secrets hsecrets
  have hsecretsfresh : EncodingFresh secrets.2 := encodingFresh_of_preserves _
    (fun parameter lay tree leaf m c => PreservesFresh.sequenceFin _ _ fun _ =>
      PreservesFresh.deriveKey _ _ _ _
        ((structuralFresh_encoding parameter lay tree leaf m c).derive _ _ _))
    digest.2 hdigestfresh secrets hsecrets
  apply probEvent_bind_le
  intro paths hpaths
  have hpathsfresh : EncodingFresh paths.2 := encodingFresh_of_preserves _
    (fun parameter lay tree leaf m c => PreservesFresh.ftsOpen
      (structuralFresh_encoding parameter lay tree leaf m c) _ _ _ _)
    secrets.2 hsecretsfresh paths hpaths
  simp only [sequenceLayers, bind_assoc]
  refine (show _ ≤ Pr[fun r => r.1 = none |
    (simulateQ randomOracle (Seeded.signLayer sk (digestIndex digest.1) topLayer
      : OracleComp HashSpec _)).run paths.2] from ?_).trans
        (signLayer_exhaustion_bound sk _ _ _ hpathsfresh)
  rw [simulateQ_bind, StateT.run_bind]
  apply probEvent_bind_le_probEvent
  intro r _ hsome
  cases h : r.1 with
  | none => exact False.elim (hsome h)
  | some value => simp

omit [Params] in
theorem randomOracle_preserves_encoding (sk : Seeded.SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) (hfresh : EncodingFresh cache)
    (r : HashOutput × QueryCache HashSpec)
    (hr : r ∈ support ((randomOracle (spec := HashSpec) (msgInput sk message randomness)).run cache)) :
    EncodingFresh r.2 := by
  refine encodingFresh_of_preserves (oracleHash (msgInput sk message randomness)) ?_ cache hfresh r ?_
  · intro parameter lay tree leaf m c
    exact PreservesFresh.query (messageInput_ne_encoding _ _ _ _ _ _ _ _ _ _ _)
  · simpa only [oracleHash, HasQuery.query, simulateQ_spec_query] using hr

/-- Grinding reads only the message domain and never consumes an encoding input. -/
theorem randomizedDigest_preserves_encoding (sk : Seeded.SecretKey) (message : Message) :
    ∀ n (cache : QueryCache HashSpec), EncodingFresh cache →
      ∀ r ∈ support ((simulateQ romImpl (Randomized.signDigestLoop sk message n)).run cache),
        EncodingFresh r.2 := by
  intro n
  induction n with
  | zero =>
      intro cache hfresh r hr
      simp only [Randomized.signDigestLoop, simulateQ_pure, StateT.run_pure, support_pure,
        Set.mem_singleton_iff] at hr
      exact hr ▸ hfresh
  | succ n ih =>
      intro cache hfresh r hr
      rw [run_randomizedDigest_succ, mem_support_bind_iff] at hr
      obtain ⟨randomness, _, hr⟩ := hr
      rw [mem_support_bind_iff] at hr
      obtain ⟨answer, hanswer, hr⟩ := hr
      have hnext := randomOracle_preserves_encoding sk message randomness cache hfresh answer hanswer
      split at hr
      · simp only [support_pure, Set.mem_singleton_iff] at hr
        exact hr ▸ hnext
      · exact ih answer.2 hnext r hr

/-- The complete randomized signer has only the two bounded exhaustion cases. -/
theorem randomized_sign_exhaustion_bound (sk : Seeded.SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (hencoding : EncodingFresh cache)
    (hmessage : ∀ randomness, cache (msgInput sk message randomness) = none) :
    Pr[fun r => r.1 = none | (simulateQ romImpl (Randomized.sign sk message)).run cache]
      ≤ (2⁻¹ : ℝ≥0∞) ^ (2 ^ (subtreeHeight + 5)) + (2⁻¹ : ℝ≥0∞) ^ (2 ^ 22) := by
  rw [Randomized.sign, simulateQ_bind, StateT.run_bind]
  refine (probEvent_bind_le_probEvent_add (p := fun r => r.1 = none)
    (ε := (2⁻¹ : ℝ≥0∞) ^ (2 ^ 22)) ?_).trans
      (add_le_add (randomized_digest_exhaustion_bound sk message cache hmessage) le_rfl)
  intro r hr hsome
  have hrencoding := randomizedDigest_preserves_encoding sk message _ cache hencoding r hr
  cases h : r.1 with
  | none => exact False.elim (hsome h)
  | some randomness =>
      rw [simulate_lift_hash]
      exact finishSign_exhaustion_bound sk message randomness r.2 hrencoding

/-- Key generation leaves every encoding and message input fresh, including surrogate keygen. -/
theorem keygen_fresh (seed : MasterSeed)
    (r : (PublicKey × Seeded.SecretKey) × QueryCache HashSpec)
    (hr : r ∈ support ((simulateQ randomOracle (Seeded.keygenFromSeed seed)).run ∅)) :
    EncodingFresh r.2 ∧ ∀ message randomness, r.2 (msgInput r.1.2 message randomness) = none := by
  constructor
  · exact encodingFresh_of_preserves _ (fun parameter lay tree leaf message c =>
      PreservesFresh.keygenFromSeed (structuralFresh_encoding parameter lay tree leaf message c) seed)
      ∅ encodingFresh_empty r hr
  · intro message randomness
    exact PreservesFresh.keygenFromSeed
      (structuralFresh_message r.1.2.parameter r.1.2.root message randomness 0) seed ∅ r hr rfl

/-- An honest key generation followed by one signature, with independent uniform randomizers. -/
noncomputable def honestSign (message : Message) : OracleComp OracleWorld (Option Signature) := do
  let seed ← liftM sampleMasterSeed
  let (_, sk) ← liftM (Seeded.keygenFromSeed seed)
  Randomized.sign sk message

/-- End-to-end exhaustion bound, with all freshness conditions discharged from the empty cache. -/
theorem honest_sign_exhaustion_bound (message : Message) :
    Pr[fun r => r.1 = none | (simulateQ romImpl (honestSign message)).run ∅]
      ≤ (2⁻¹ : ℝ≥0∞) ^ (2 ^ (subtreeHeight + 5)) + (2⁻¹ : ℝ≥0∞) ^ (2 ^ 22) := by
  rw [honestSign, simulateQ_bind, StateT.run_bind, run_lift_prob]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  apply probEvent_bind_le_of_forall_le
  intro seed _
  rw [simulateQ_bind, StateT.run_bind, simulate_lift_hash]
  apply probEvent_bind_le_of_forall_le
  intro r hr
  obtain ⟨hencoding, hmessage⟩ := keygen_fresh seed r hr
  exact randomized_sign_exhaustion_bound r.1.2 message r.2 hencoding (hmessage message)

/-- Every requested pruning height has a per-signature exhaustion probability below 2^-32767. -/
theorem honest_sign_exhaustion_negligible (hb : 10 ≤ subtreeHeight) (message : Message) :
    Pr[fun r => r.1 = none | (simulateQ romImpl (honestSign message)).run ∅]
      ≤ (2⁻¹ : ℝ≥0∞) ^ 32767 := by
  refine (honest_sign_exhaustion_bound message).trans ?_
  have he : 2 ^ 15 ≤ (2 : Nat) ^ (subtreeHeight + 5) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  calc
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ (32767 + 1) + (2⁻¹ : ℝ≥0∞) ^ (32767 + 1) :=
      add_le_add (inv_two_pow_anti he) (inv_two_pow_anti (by decide))
    _ = _ := inv_two_pow_succ_add 32767

end LeanSphincs.Completeness
