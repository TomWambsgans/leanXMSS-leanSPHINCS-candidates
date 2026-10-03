import LeanSphincs.LifetimePairedBankInclusion
import LeanSphincs.LifetimeSampling

/-! Completing an adaptively stopped first-touch digest transcript to an independent uniform
word. This is a joint sampling bridge for fixed query-slot tuples; selected cached candidates
are not asserted to be uniform. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness Security
open Security.ExponentialCharge
set_option backward.isDefEq.respectTransparency false

noncomputable def padDigestWord : Nat → List MessageDigest → ProbComp (List MessageDigest)
  | 0, _ => pure []
  | n + 1, [] => SphincsSecurity.Concrete.sampleUniformProposalWord MessageDigest (n + 1)
  | n + 1, digest :: rest => List.cons digest <$> padDigestWord n rest

theorem padDigestWord_nil (n : Nat) : padDigestWord n [] =
    SphincsSecurity.Concrete.sampleUniformProposalWord MessageDigest n := by
  cases n <;> rfl

noncomputable def freshDigestWord (sk : Seeded.SecretKey) (trace : List QueryRecord) : List MessageDigest :=
  (freshCandidateTrace sk trace).map Prod.snd

noncomputable def pairedWord {α : Type} (sk : Seeded.SecretKey) (program : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (length : Nat) : ProbComp (List MessageDigest) := do
  let trace ← traceRun (pairedRom sk) program cache
  padDigestWord length (freshDigestWord sk trace.2.1)

private theorem evalDist_bind_constant {α β : Type} (sample : ProbComp α)
    (next : α → ProbComp β) (fixed : ProbComp β)
    (h : ∀ result ∈ support sample, 𝒟[next result] = 𝒟[fixed]) :
    𝒟[sample >>= next] = 𝒟[fixed] := by
  trans 𝒟[sample >>= fun _ => fixed]
  · exact evalDist_bind_congr h
  · apply evalDist_ext
    intro value
    rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

private theorem pairedWord_zero {α : Type} (sk : Seeded.SecretKey) (program : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) : 𝒟[pairedWord sk program cache 0] = 𝒟[(pure [] : ProbComp (List MessageDigest))] := by
  apply evalDist_bind_constant
  intro result _
  rfl

/-- The unconditionally padded word is iid, despite adaptive candidate labels and stopping. -/
theorem evalDist_pairedWord {α : Type} (sk : Seeded.SecretKey) (program : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (hpaired : PairedCache sk cache) (length : Nat) :
    𝒟[pairedWord sk program cache length] =
      𝒟[SphincsSecurity.Concrete.sampleUniformProposalWord MessageDigest length] := by
  induction program using OracleComp.inductionOn generalizing cache length with
  | pure value => simp only [pairedWord, traceRun_pure, pure_bind, freshDigestWord,
      freshCandidateTrace, List.filterMap_nil, List.map_nil, padDigestWord_nil]
  | query_bind input next ih =>
      cases length with
      | zero => exact pairedWord_zero sk _ cache
      | succ length =>
          simp only [pairedWord, traceRun_query_bind, bind_assoc, pure_bind]
          cases input with
          | inl input =>
              apply evalDist_bind_constant
              intro first hfirst
              have hmid := (pairedRom_support_paired sk (.inl input) cache hpaired first.1 first.2 hfirst).1
              simpa only [pairedWord, freshDigestWord, freshCandidateTrace, List.filterMap_cons, freshCandidateRecord] using
                ih first.1 first.2 hmid (length + 1)
          | inr input =>
              cases hp : decodeCandidateInput sk input with
              | none =>
                  apply evalDist_bind_constant
                  intro first hfirst
                  have hmid := (pairedRom_support_paired sk (.inr input) cache hpaired first.1 first.2 hfirst).1
                  simpa only [pairedWord, freshDigestWord, freshCandidateTrace, List.filterMap_cons, freshCandidateRecord, hp] using
                    ih first.1 first.2 hmid (length + 1)
              | some position =>
                  by_cases hfresh : cache (candidateInput sk position.1 position.2) = none
                  · have hinput := decodeCandidateInput_some sk input position hp
                    subst input
                    let head : HashOutput × QueryCache HashSpec → MessageDigest := fun result =>
                      cachedPairDigest sk position.1 result.2
                    trans 𝒟[do
                      let first ← (pairedHash sk (candidateInput sk position.1 position.2)).run cache
                      List.cons (head first) <$> SphincsSecurity.Concrete.sampleUniformProposalWord MessageDigest length]
                    · apply evalDist_bind_congr
                      intro first hfirst
                      have hmid := (pairedRom_support_paired sk (.inr (candidateInput sk position.1 position.2))
                        cache hpaired first.1 first.2 hfirst).1
                      simp only [freshDigestWord, freshCandidateTrace, List.filterMap_cons,
                        freshCandidateRecord, decodeCandidateInput_self, hfresh, ↓reduceIte,
                        List.map_cons, padDigestWord]
                      rw [← map_bind]
                      simpa only [pairedWord, freshDigestWord, freshCandidateTrace, freshCandidateRecord, head, evalDist_map]
                        using congrArg (Functor.map (List.cons (head first))) (ih first.1 first.2 hmid length)
                    · have hhead : 𝒟[head <$> (pairedHash sk (candidateInput sk position.1 position.2)).run cache] =
                          𝒟[($ᵗ MessageDigest : ProbComp MessageDigest)] :=
                        evalDist_pairedHash_fresh_digest sk position.1 position.2 cache (hpaired.fresh _ _ hfresh)
                      trans 𝒟[(head <$> (pairedHash sk (candidateInput sk position.1 position.2)).run cache) >>=
                        fun digest => List.cons digest <$> SphincsSecurity.Concrete.sampleUniformProposalWord MessageDigest length]
                      · rw [bind_map_left]
                      · rw [evalDist_bind, hhead, ← evalDist_bind]
                        rfl
                  · apply evalDist_bind_constant
                    intro first hfirst
                    have hmid := (pairedRom_support_paired sk (.inr input) cache hpaired first.1 first.2 hfirst).1
                    simpa only [pairedWord, freshDigestWord, freshCandidateTrace, List.filterMap_cons,
                      freshCandidateRecord, hp, hfresh, ↓reduceIte] using
                      ih first.1 first.2 hmid (length + 1)

end LeanSphincs.Lifetime
