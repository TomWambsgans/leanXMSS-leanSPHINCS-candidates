import LeanSphincs.LifetimeTerminal
import LeanSphincs.LifetimeSigningDisclosure
import LeanSphincs.Statement

/-!
Exact FORS reuse bounds after actual adaptive signing calls. The terminal digest is a fresh
independent target. Adversarial hash interleaving and adaptive target search are separate steps
of the full SUF-CMA reduction.
-/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete Completeness

attribute [local instance] Classical.propDecidable

variable [Params]

noncomputable def freshDisclosureCoverage (parameter : PublicParameter)
    (process : ProbComp (Finset KeptDigestView)) : ProbComp Bool := do
  let prior ← process
  let digest ← ($ᵗ MessageDigest : ProbComp MessageDigest)
  pure (decide (Landed parameter (digestIndex digest) ∧ ViewCovered (localDigestView digest) prior))

theorem freshDisclosureCoverage_bound (parameter : PublicParameter)
    (process : ProbComp (Finset KeptDigestView)) (mass : ℝ≥0∞)
    (h : ∀ target, Pr[ViewCovered target | process] ≤ mass) :
    Pr[fun result => result = true | freshDisclosureCoverage parameter process] ≤
      (2 : ℝ≥0∞) ^ subtreeHeight / 2 ^ 26 * mass := by
  have hswap :
      Pr[fun pair : KeptDigestView × Finset KeptDigestView => ViewCovered pair.1 pair.2 |
        (do let prior ← process; let target ← ($ᵗ KeptDigestView : ProbComp _); pure (target, prior))] ≤ mass := by
    rw [probEvent_bind_bind_swap]
    apply probEvent_uniform_bind_le
    intro target
    simpa only [bind_pure_comp, probEvent_map, Function.comp_def] using h target
  rw [freshDisclosureCoverage, probEvent_bind_eq_tsum]
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, decide_eq_true_eq]
  have hsum :
      (∑' prior : Finset KeptDigestView, Pr[= prior | process] *
        Pr[fun target => ViewCovered target prior | ($ᵗ KeptDigestView : ProbComp _)]) ≤ mass := by
    simpa only [probEvent_bind_eq_tsum, bind_pure_comp, probEvent_map, Function.comp_def] using hswap
  calc
    _ = ((2 ^ (totalHeight - subtreeHeight) : Nat) : ℝ≥0∞)⁻¹ *
        ∑' prior : Finset KeptDigestView, Pr[= prior | process] *
          Pr[fun target => ViewCovered target prior | ($ᵗ KeptDigestView : ProbComp _)] := by
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro prior
      rw [probEvent_landed_localDigest parameter (fun target => ViewCovered target prior)]
      ac_rfl
    _ ≤ ((2 ^ (totalHeight - subtreeHeight) : Nat) : ℝ≥0∞)⁻¹ * mass := mul_le_mul_right hsum _
    _ = _ := by
      congr 1
      rw [Nat.cast_pow, Nat.cast_ofNat, ENNReal.inv_pow]
      have hb : subtreeHeight ≤ 26 := Params.subtreeHeight_le
      simpa only [totalHeight, Nat.add_sub_of_le hb] using
        (two_pow_div_two_pow subtreeHeight (26 - subtreeHeight)).symm

noncomputable def signingFreshCoverage (sk : Seeded.SecretKey) (cache : QueryCache HashSpec)
    (request : DisclosureState → Message) (n : Nat) : ProbComp Bool :=
  freshDisclosureCoverage sk.parameter
    (disclosureProcess (signingDisclosureStep sk request) Prod.fst n (∅, cache))

/-- After any supported key generation, N complete sign calls satisfy the exact FORS lifetime
expression against one fresh independent target. Requests may adapt to the full cache. -/
theorem signingFreshCoverage_after_keygen_bound (seed : MasterSeed)
    (result : (PublicKey × Seeded.SecretKey) × QueryCache HashSpec)
    (hsupport : result ∈ support ((simulateQ randomOracle (Seeded.keygenFromSeed seed)).run ∅))
    (request : DisclosureState → Message) (n : Nat) :
    Pr[fun value => value = true | signingFreshCoverage result.1.2 result.2 request n] ≤
      forsBoundENNReal subtreeHeight n := by
  apply freshDisclosureCoverage_bound
  intro target
  exact (signing_disclosures_after_keygen_le_uniform seed result hsupport request n
    (ViewCovered target) (viewCovered_mono target)).trans_eq
      (probEvent_uniformDisclosureSet_covered n target)

def SigningLifetimeBound : Prop :=
  ∀ (seed : MasterSeed) (result : (PublicKey × Seeded.SecretKey) × QueryCache HashSpec),
    result ∈ support ((simulateQ randomOracle (Seeded.keygenFromSeed seed)).run ∅) →
    ∀ (request : DisclosureState → Message) (n : Nat), n ≤ signatureLimit →
      Pr[fun value => value = true | signingFreshCoverage result.1.2 result.2 request n] ≤
        (1 : ℝ≥0∞) / 2 ^ 127

theorem signingLifetimeBound_of_fors
    (h : ∀ n, n ≤ signatureLimit → forsBoundENNReal subtreeHeight n ≤ (1 : ℝ≥0∞) / 2 ^ 127) :
    SigningLifetimeBound := by
  intro seed result hs request n hn
  exact (signingFreshCoverage_after_keygen_bound seed result hs request n).trans (h n hn)

end LeanSphincs.Lifetime

namespace LeanSphincs.Lifetimes

open Lifetime

/-- All six literal lifetime targets, now for complete signing calls and a fresh independent
FORS target. This theorem is not the adaptive SUF-CMA claim `RequestedSecurity`. -/
theorem requested_signing_lifetime_bounds :
    @SigningLifetimeBound full ∧ @SigningLifetimeBound pruned20 ∧
    @SigningLifetimeBound pruned13 ∧ @SigningLifetimeBound pruned14 ∧
    @SigningLifetimeBound pruned12 ∧ @SigningLifetimeBound pruned10 := by
  exact ⟨@signingLifetimeBound_of_fors full (fun _ h => fors_lifetime_ennreal_full (h.trans (by decide))),
    @signingLifetimeBound_of_fors pruned20 (fun _ h => fors_lifetime_ennreal_pruned20 (h.trans (by decide))),
    @signingLifetimeBound_of_fors pruned13 (fun _ h => fors_lifetime_ennreal_pruned13 (h.trans (by decide))),
    @signingLifetimeBound_of_fors pruned14 (fun _ h => fors_lifetime_ennreal_pruned14 (h.trans (by decide))),
    @signingLifetimeBound_of_fors pruned12 (fun _ h => fors_lifetime_ennreal_pruned12 (h.trans (by decide))),
    @signingLifetimeBound_of_fors pruned10 (fun _ h => fors_lifetime_ennreal_pruned10 h)⟩

end LeanSphincs.Lifetimes
