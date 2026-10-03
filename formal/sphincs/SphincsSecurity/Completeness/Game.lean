import SphincsSecurity.Completeness
import SphincsSecurity.Completeness.Recovery
import SphincsSecurity.Completeness.Search
import SphincsSecurity.Proof.Scheme.Support

/-!
# From the game to one hash-only run

The experiment samples a seed and then runs key generation, signing and verification against the
random oracle. `experiment_eq` pulls the sampling out front, leaving one hash-only computation per
seed. Recovery then removes verification from the failure event: on every reachable path where the
signer produced a signature, replaying the path under an answer function agreeing with its cache
shows the verifier accepts, so the honest run fails only where signing returned `none`.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Completeness

open Concrete

/-- One seed's honest run, as a hash-only computation. -/
def honest (seed : MasterSeed) (message : Message) : OracleComp HashSpec Bool := do
  let keys ← Seeded.keygenFromSeed seed
  let result ← (Seeded.sign keys.2 message : OracleComp HashSpec (Option Signature))
  match result with
  | some signature => (Concrete.verify keys.1 message signature : OracleComp HashSpec Bool)
  | none => pure false

theorem gameCore_eq (message : Message) :
    gameCore message = (liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed) >>= fun seed =>
      (liftM (honest seed message) : OracleComp OracleWorld Bool) := by
  unfold gameCore honest
  refine bind_congr fun seed => ?_
  simp only [liftM_bind]
  refine bind_congr fun keys => ?_
  obtain ⟨pk, sk⟩ := keys
  refine bind_congr fun result => ?_
  cases result <;> simp

theorem experiment_eq (message : Message) :
    experiment message = sampleMasterSeed >>= fun seed =>
      Prod.fst <$> (simulateQ (randomOracle : QueryImpl HashSpec _) (honest seed message)).run ∅ := by
  rw [experiment, gameCore_eq, simulateQ_bind, StateT.run'_eq, StateT.run_bind,
    show simulateQ romImpl (liftM sampleMasterSeed : OracleComp OracleWorld MasterSeed)
      = simulateQ (unifFwdImpl HashSpec) sampleMasterSeed from
        QueryImpl.simulateQ_add_liftM_left _ _ _,
    unifFwdImpl.simulateQ_run]
  simp [map_eq_bind_pure_comp, bind_assoc, romImpl, QueryImpl.simulateQ_add_liftM_right]

theorem probEvent_prob_bind_le {α β : Type} (mx : ProbComp α) (my : α → ProbComp β)
    (p : β → Prop) (b : ℝ≥0∞) (h : ∀ x ∈ support mx, Pr[p | my x] ≤ b) :
    Pr[p | mx >>= my] ≤ b := by
  rw [probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[p | my x] ≤ ∑' x, Pr[= x | mx] * b := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hx : x ∈ support mx
        · exact mul_le_mul_right (h x hx) _
        · simp [probOutput_eq_zero_of_not_mem_support hx]
    _ ≤ b := by
        rw [ENNReal.tsum_mul_right]
        have hmass : ∑' x, Pr[= x | mx] ≤ 1 := tsum_probOutput_le_one
        exact mul_le_of_le_one_left' hmass

/-- Key generation followed by signing, keeping the keys. -/
def signedWithKeys (seed : MasterSeed) (message : Message) :
    OracleComp HashSpec ((PublicKey × Seeded.SecretKey) × Option Signature) := do
  let keys ← Seeded.keygenFromSeed seed
  let result ← (Seeded.sign keys.2 message : OracleComp HashSpec (Option Signature))
  pure (keys, result)

theorem honest_eq (seed : MasterSeed) (message : Message) :
    honest seed message = signedWithKeys seed message >>= fun kr =>
      match kr.2 with
      | some signature => (Concrete.verify kr.1.1 message signature : OracleComp HashSpec Bool)
      | none => pure false := by
  unfold honest signedWithKeys
  simp only [bind_assoc, pure_bind]

attribute [local irreducible] Seeded.signDigestLoop Seeded.signLayer Seeded.ftsOpen Seeded.treeRoot
  sequenceFin digestAttemptLimit encodingAttemptLimit

set_option maxHeartbeats 1000000 in
/-- A signature the signer produces for a generated key verifies, under every hash function. -/
theorem correct : SphincsCorrectnessStatement := by
  intro hash seed publicKey secretKey message signature hkeys hsign
  simp only [Seeded.keygenFromSeed, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Prod.mk.injEq]
    at hkeys
  obtain ⟨rfl, rfl⟩ := hkeys
  exact verify_of_sign hash _ message rfl hsign

set_option maxHeartbeats 1000000 in
/-- A signature the signer produced always verifies, so the honest run fails only when signing does. -/
theorem probEvent_honest_false_le (seed : MasterSeed) (message : Message) :
    Pr[fun r => r.1 = false | (simulateQ (randomOracle : QueryImpl HashSpec _) (honest seed message)).run ∅]
      ≤ Pr[fun r => r.1.2 = none |
          (simulateQ (randomOracle : QueryImpl HashSpec _) (signedWithKeys seed message)).run ∅] := by
  rw [honest_eq]
  refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1.2 = none) _ ∅ 0 ?_) (by rw [add_zero])
  rintro ⟨⟨⟨pk, sk⟩, result⟩, cache⟩ hr hsome
  obtain ⟨signature, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
  dsimp only
  rw [nonpos_iff_eq_zero, probEvent_eq_zero_iff]
  rintro ⟨b, cache'⟩ hr'
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := HashSpec) cache'
  obtain ⟨hle, hverify, _⟩ := replay_of_mem_support _ cache b cache' hr' f hf
  obtain ⟨hsigned, _⟩ := replay_of_mem_support_of_le _ ∅ _ cache cache' hr hle f hf
  simp only [signedWithKeys, evalWithAnswerFn_bind, evalWithAnswerFn_pure] at hsigned
  have hkeys : evalWithAnswerFn f (Seeded.keygenFromSeed seed) = (pk, sk) := congrArg Prod.fst hsigned
  have hsign := congrArg Prod.snd hsigned
  rw [hkeys] at hsign
  simp only [Seeded.keygenFromSeed, evalWithAnswerFn_bind, evalWithAnswerFn_pure, Prod.mk.injEq]
    at hkeys
  obtain ⟨rfl, rfl⟩ := hkeys
  have htrue := verify_of_sign f _ message rfl hsign
  try dsimp only at hverify
  rw [htrue] at hverify
  try dsimp only
  rw [← hverify]
  decide

end SphincsSecurity.Completeness
