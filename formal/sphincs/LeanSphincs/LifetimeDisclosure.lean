import LeanSphincs.LifetimeReuse
import LeanSphincs.LifetimeSampling

/-!
Iteration of one-step disclosure domination. The abstract state can include the random-oracle
cache and an adaptive request history. Invariant preservation and the one-step domination law
are explicit hypotheses; no independence between actual transitions is assumed.
-/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete

variable [Params]

noncomputable def uniformDisclosureSet (n : Nat) (prior : Finset KeptDigestView) :
    ProbComp (Finset KeptDigestView) :=
  (fun word : List KeptDigestView => word.toFinset ∪ prior) <$>
    SphincsSecurity.Concrete.sampleUniformProposalWord KeptDigestView n

theorem uniformDisclosureSet_zero (prior : Finset KeptDigestView) :
    uniformDisclosureSet 0 prior = pure prior := by
  simp [uniformDisclosureSet, SphincsSecurity.Concrete.sampleUniformProposalWord]

theorem uniformDisclosureSet_succ (n : Nat) (prior : Finset KeptDigestView) :
    uniformDisclosureSet (n + 1) prior =
      ($ᵗ KeptDigestView : ProbComp KeptDigestView) >>= fun view =>
        uniformDisclosureSet n (insert view prior) := by
  simp only [uniformDisclosureSet, SphincsSecurity.Concrete.sampleUniformProposalWord,
    map_bind, map_pure, List.toFinset_cons]
  apply bind_congr
  intro view
  apply bind_congr
  intro word
  congr 1
  ext x
  simp only [Finset.mem_union, Finset.mem_insert]
  tauto

/-- The state may carry arbitrary adaptive information; only its disclosure projection matters. -/
noncomputable def disclosureProcess {State : Type} (step : State → ProbComp State)
    (views : State → Finset KeptDigestView) : Nat → State → ProbComp (Finset KeptDigestView)
  | 0, state => pure (views state)
  | n + 1, state => step state >>= disclosureProcess step views n

theorem uniformDisclosureSet_mono (n : Nat) (event : Finset KeptDigestView → Prop)
    [DecidablePred event] (hmono : Monotone event) {left right : Finset KeptDigestView}
    (hsub : left ⊆ right) :
    Pr[event | uniformDisclosureSet n left] ≤ Pr[event | uniformDisclosureSet n right] := by
  simp only [uniformDisclosureSet, probEvent_map, Function.comp_def]
  exact probEvent_mono'' (fun word h => hmono (Finset.union_subset_union_right hsub) h)

/-- N adaptive transitions are dominated by N independent uniform insertions whenever each
transition preserves its invariant and satisfies the one-step monotone-event bound. -/
theorem disclosureProcess_le_uniform {State : Type} (step : State → ProbComp State)
    (views : State → Finset KeptDigestView) (invariant : State → Prop)
    (hpreserve : ∀ state, invariant state → ∀ next ∈ support (step state), invariant next)
    (hstep : ∀ state, invariant state → ∀ (event : Finset KeptDigestView → Prop)
      [DecidablePred event], Monotone event →
      Pr[fun next => event (views next) | step state] ≤
        Pr[fun view => event (insert view (views state)) |
          ($ᵗ KeptDigestView : ProbComp KeptDigestView)]) :
    ∀ (n : Nat) (state : State), invariant state →
      ∀ (event : Finset KeptDigestView → Prop) [DecidablePred event], Monotone event →
      Pr[event | disclosureProcess step views n state] ≤
        Pr[event | uniformDisclosureSet n (views state)] := by
  intro n
  induction n with
  | zero =>
    intro state hinvariant event _ hmono
    simp only [disclosureProcess, uniformDisclosureSet_zero]
    exact le_rfl
  | succ n ih =>
    intro state hinvariant event _ hmono
    rw [disclosureProcess]
    calc
      _ ≤ Pr[event | step state >>= fun next => uniformDisclosureSet n (views next)] := by
        apply probEvent_bind_mono
        intro next hnext
        exact ih next (hpreserve state hinvariant next hnext) event hmono
      _ = Pr[event | SphincsSecurity.Concrete.sampleUniformProposalWord KeptDigestView n >>= fun word =>
          step state >>= fun next => pure (word.toFinset ∪ views next)] := by
        simp only [uniformDisclosureSet, map_eq_bind_pure_comp, Function.comp_def]
        exact probEvent_bind_bind_swap _ _ _ _
      _ ≤ Pr[event | SphincsSecurity.Concrete.sampleUniformProposalWord KeptDigestView n >>= fun word =>
          ($ᵗ KeptDigestView : ProbComp KeptDigestView) >>= fun view =>
            pure (word.toFinset ∪ insert view (views state))] := by
        apply probEvent_bind_mono
        intro word _
        simp only [bind_pure_comp, probEvent_map, Function.comp_def]
        exact hstep state hinvariant (fun set => event (word.toFinset ∪ set))
          (fun _ _ hsub h => hmono (Finset.union_subset_union_right hsub) h)
      _ = Pr[event | ($ᵗ KeptDigestView : ProbComp KeptDigestView) >>= fun view =>
          SphincsSecurity.Concrete.sampleUniformProposalWord KeptDigestView n >>= fun word =>
            pure (word.toFinset ∪ insert view (views state))] := probEvent_bind_bind_swap _ _ _ _
      _ = _ := by
        rw [uniformDisclosureSet_succ]
        simp only [uniformDisclosureSet, map_eq_bind_pure_comp, Function.comp_def]

end LeanSphincs.Lifetime
