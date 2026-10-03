import LeanSphincs.LifetimeHybridUnion

/-! Full accepted digest views coupled to the exact index observer. Actual sign responses
and caches are preserved; ideal suffix draws retain all24 independent FORS coordinates. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness Security
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable [Params]

noncomputable def viewedSign (sk : Seeded.SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    ProbComp (Option FullDigestView × Option Signature × QueryCache HashSpec) :=
  (fun result => (result.2.1.head?.map (fun record => fullDigestView record.digest), result.1, result.2.2)) <$>
    signWithSources sk message ([], cache)

theorem viewedSign_index (sk : Seeded.SecretKey) (message : Message) (cache : QueryCache HashSpec) :
    (fun result => (result.1.map Prod.fst, result.2)) <$> viewedSign sk message cache =
      indexedSign sk message cache := by
  simp only [viewedSign, indexedSign, Functor.map_map]
  congr 1
  funext result
  simp only [Function.comp_def, Option.map_map, fullDigestView]

theorem viewedSign_landed (sk : Seeded.SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (result : Option FullDigestView × Option Signature × QueryCache HashSpec)
    (hresult : result ∈ support (viewedSign sk message cache)) :
    ∀ view ∈ result.1, Landed sk.parameter view.1 := by
  rw [viewedSign, support_map] at hresult
  obtain ⟨source, hsource, rfl⟩ := hresult
  have hconsistent := (signWithSources_preserves sk message ([], cache)
    (by intro record h; cases h) source hsource).2.2
  intro view hview
  cases hrecords : source.2.1 with
  | nil => simp only [hrecords, List.head?_nil, Option.map_none, Option.not_mem_none] at hview
  | cons record records =>
      simp only [hrecords, List.head?_cons, Option.map_some, Option.mem_some_iff] at hview
      subst view
      exact (hconsistent record (by rw [hrecords]; exact List.mem_cons_self)).2.1

noncomputable def fullViewStep {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (actual : Nat → Bool)
    (n : Nat) (state : State × QueryCache HashSpec) :
    ProbComp (Option FullDigestView × (State × QueryCache HashSpec)) :=
  if actual n then do
    let request ← (simulateQ romImpl (interlude n state.1)).run state.2
    let signed ← viewedSign sk request.1.1 request.2
    pure (signed.1, update request.1.2 signed.2.1, signed.2.2)
  else (fun view : KeptDigestView => (some (keptViewEquiv sk.parameter view).val, state)) <$> ($ᵗ KeptDigestView)

/-- This is a joint index/state/cache equality, sufficient to compose adaptive continuations. -/
theorem fullViewStep_index {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (actual : Nat → Bool)
    (n : Nat) (state : State × QueryCache HashSpec) :
    (fun result => (result.1.map Prod.fst, result.2)) <$> fullViewStep sk interlude update actual n state =
      hybridIndexStep sk interlude update actual n state := by
  rw [fullViewStep, hybridIndexStep]
  split
  · simp only [interleavedIndexStep, map_bind, map_pure]
    apply bind_congr
    intro request
    rw [← viewedSign_index, bind_map_left]
  · simp only [uniformKeptIndex, Functor.map_map, Function.comp_def, Option.map_some, keptViewEquiv,
      Equiv.coe_fn_mk]

theorem fullViewStep_landed {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (actual : Nat → Bool)
    (n : Nat) (state : State × QueryCache HashSpec)
    (result : Option FullDigestView × (State × QueryCache HashSpec))
    (hresult : result ∈ support (fullViewStep sk interlude update actual n state)) :
    ∀ view ∈ result.1, Landed sk.parameter view.1 := by
  rw [fullViewStep] at hresult
  split at hresult
  · simp only [mem_support_bind_iff, mem_support_pure_iff] at hresult
    obtain ⟨request, _, signed, hsigned, rfl⟩ := hresult
    exact viewedSign_landed _ _ _ signed hsigned
  · rw [support_map] at hresult
    obtain ⟨view, _, rfl⟩ := hresult
    intro result hresult
    cases Option.mem_some_iff.mp hresult
    exact (keptViewEquiv sk.parameter view).property

noncomputable def fullViewTrace {State : Type}
    (step : Nat → State → ProbComp (Option FullDigestView × State)) : Nat → State → ProbComp (List (Option FullDigestView))
  | 0, _ => pure []
  | n + 1, state => do
      let next ← step n state
      let rest ← fullViewTrace step n next.2
      pure (next.1 :: rest)

def fullViewPositions (trace : List (Option FullDigestView)) : List (Option Index) :=
  trace.map (Option.map Prod.fst)

theorem fullViewTrace_index {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (actual : Nat → Bool)
    (n : Nat) (state : State × QueryCache HashSpec) :
    fullViewPositions <$> fullViewTrace (fullViewStep sk interlude update actual) n state =
      adaptiveIndexTrace (hybridIndexStep sk interlude update actual) n state := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      rw [fullViewTrace, adaptiveIndexTrace, ← fullViewStep_index]
      simp only [map_bind, bind_map_left, map_pure]
      apply bind_congr
      intro next
      rw [← ih]
      simp only [bind_map_left]
      rfl

theorem fullViewTrace_landed {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (actual : Nat → Bool)
    (n : Nat) (state : State × QueryCache HashSpec) (trace : List (Option FullDigestView))
    (htrace : trace ∈ support (fullViewTrace (fullViewStep sk interlude update actual) n state)) :
    ∀ entry ∈ trace, ∀ view ∈ entry, Landed sk.parameter view.1 := by
  induction n generalizing state trace with
  | zero =>
      simp only [fullViewTrace, mem_support_pure_iff] at htrace
      subst trace
      simp only [List.not_mem_nil, false_implies, implies_true]
  | succ n ih =>
      simp only [fullViewTrace, mem_support_bind_iff, mem_support_pure_iff] at htrace
      obtain ⟨first, hfirst, rest, hrest, rfl⟩ := htrace
      intro entry hentry view hview
      rcases List.mem_cons.mp hentry with rfl | hentry
      · exact fullViewStep_landed sk interlude update actual n state first hfirst view hview
      · exact ih first.2 rest hrest entry hentry view hview

def fullViewLocals (trace : List (Option FullDigestView)) : List KeptDigestView :=
  trace.filterMap (fun entry => entry.map localFullView)

theorem localFullView_index_iff (parameter : PublicParameter) (view : FullDigestView)
    (hland : Landed parameter view.1) (index : Fin (2 ^ subtreeHeight)) :
    (localFullView view).1 = index ↔ view.1 = (keptLeafEquiv parameter index).val := by
  have hlocal : (localFullView view).1 = (keptLeafEquiv parameter).symm ⟨view.1, hland⟩ := rfl
  rw [hlocal, Equiv.symm_apply_eq]
  constructor
  · exact congrArg Subtype.val
  · intro h
    apply Subtype.ext
    exact h

/-- Every local index count corresponds to one global kept index, with no independence premise. -/
theorem fullViewLocals_count (parameter : PublicParameter) (trace : List (Option FullDigestView))
    (hland : ∀ entry ∈ trace, ∀ view ∈ entry, Landed parameter view.1) (index : Fin (2 ^ subtreeHeight)) :
    ((fullViewLocals trace).map Prod.fst).count index =
      (fullViewPositions trace).count (some (keptLeafEquiv parameter index).val) := by
  induction trace with
  | nil => rfl
  | cons entry trace ih =>
      have htail := ih (fun item hitem view hview => hland item (List.mem_cons_of_mem _ hitem) view hview)
      cases entry with
      | none => simpa only [fullViewLocals, List.filterMap_cons, Option.map_none, fullViewPositions,
          List.map_cons, List.count_cons, reduceCtorEq, beq_iff_eq, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using htail
      | some view =>
          have hv := hland (some view) List.mem_cons_self view (by rfl)
          have heq := localFullView_index_iff parameter view hv index
          simp only [fullViewLocals, List.filterMap_cons, Option.map_some, List.map_cons,
            fullViewPositions, List.count_cons, beq_iff_eq, Option.some.injEq]
          simp only [heq]
          exact congrArg (fun x => x + if view.1 = (keptLeafEquiv parameter index).val then 1 else 0) htail

/-- Overflow of the distinct disclosed view set implies overflow of its coupled index trace. -/
theorem fullViewLocals_cap (parameter : PublicParameter) (trace : List (Option FullDigestView))
    (hland : ∀ entry ∈ trace, ∀ view ∈ entry, Landed parameter view.1)
    (hcounts : ∀ index, (fullViewPositions trace).count (some index) < 256) :
    ViewCap 255 (fullViewLocals trace).toFinset := by
  apply viewCap_of_list_counts
  intro index
  rw [fullViewLocals_count parameter trace hland index]
  exact hcounts _

/-- The full real-prefix/uniform-suffix view process has the same proved overflow reserve. -/
theorem actual_hybrid_view_overflow {State : Type} (sk : Seeded.SecretKey)
    (interlude : Nat → State → OracleComp OracleWorld (Message × State))
    (update : State → Option Signature → State) (actual : Nat → Bool) (n : Nat)
    (hpair : (subtreeHeight, n) ∈ requestedLifetimePairs) (state : State) :
    Pr[fun trace => ¬ViewCap 255 (fullViewLocals trace).toFinset |
      fullViewTrace (fullViewStep sk interlude update actual) n (state, ∅)] ≤
      1 / (2 : ℝ≥0∞) ^ 400 + 1 / 2 ^ 294 := by
  have h := actual_hybrid_occupancy sk interlude update actual n hpair state
  rw [← fullViewTrace_index, probEvent_map] at h
  refine le_trans ?_ h
  apply probEvent_mono
  intro trace htrace hbad
  change ∃ index, 256 ≤ (fullViewPositions trace).count (some index)
  by_contra hcounts
  push Not at hcounts
  exact hbad (fullViewLocals_cap sk.parameter trace
    (fullViewTrace_landed sk interlude update actual n (state, ∅) trace htrace) hcounts)

end LeanSphincs.Lifetime
