import FORS.SWRoute.PPart

/-! **What the lazy run exposes.** Two facts about the interpreted run that the SW route's release
lemmas need:
* a coordinate becomes known only if it was known, was revealed, or is the output of a parsed row
  (`known_interp`); FORS secrets (position 0) are the output of no row, so they become known only
  by a reveal;
* a completed signature reveals the FORS secret of every tree at the leaf its pair's digest
  selects (`sign_reveals_all`). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.LoopWalk ForsPotential

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

section Known

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- An ordinary query exposes at most the output coordinate of its row. -/
theorem known_ordinary (x : HashInput) (s : State) (r : HashOutput × State)
    (hr : r ∈ support (ordinaryStep model x s.known s)) (c : Coordinate) (hc : r.2.known c ≠ none) :
    s.known c ≠ none ∨ ∃ a, c = model.outgoing a := by
  have hread : ∀ s1 : State, s1.known = s.known → ∀ r ∈ support (readOutside x s1), r.2.known = s.known := by
    intro s1 hs1 r hr
    rcases readOutside_support x s1 r hr with h | ⟨_, h⟩
    · rw [h, hs1]
    · rw [h]
      exact hs1
  unfold ordinaryStep at hr
  cases hp : model.parse x with
  | none =>
      simp only [hp] at hr
      left
      rwa [hread s rfl r hr] at hc
  | some q =>
      simp only [hp] at hr
      cases hk : s.known (model.incoming q.1) with
      | none =>
          simp only [hk] at hr
          left
          rwa [hread (s.record (model.incoming q.1, q.2)) rfl r hr] at hc
      | some canonical =>
          simp only [hk] at hr
          split_ifs at hr with heq
          · rw [support_map] at hr
            obtain ⟨res, hres, rfl⟩ := hr
            rw [sampleCoordinate_expose _ s res hres] at hc
            by_cases hca : c = model.outgoing q.1
            · exact Or.inr ⟨q.1, hca⟩
            · left
              simp only [DebtState.expose] at hc
              simpa [QueryCache.cacheQuery, hca] using hc
          · left
            rwa [hread s rfl r hr] at hc

/-- **A coordinate known after a run** was known before, was revealed by the run, or is the output
coordinate of a row. -/
theorem known_interp {α : Type} (comp : OracleComp CostSpec α) :
    ∀ budget (s : State), ∀ out ∈ support (interp tg initial model comp budget s), ∀ c, out.2.known c ≠ none →
      s.known c ≠ none ∨ c ∈ out.1.2.1 ∨ ∃ a, c = model.outgoing a := by
  induction comp using OracleComp.inductionOn with
  | pure value =>
      intro budget s out hout c hc
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      subst hout
      exact Or.inl hc
  | query_bind input next ih =>
      intro budget s out hout c hc
      rw [interp_query_bind] at hout
      split_ifs at hout with hcost
      · rw [support_bind] at hout
        simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
        obtain ⟨res, hres, inner, hinner, rfl⟩ := hout
        show s.known c ≠ none ∨ c ∈ HiddenBridge.revealed input ++ inner.1.2.1 ∨ ∃ a, c = model.outgoing a
        rcases ih res.1 _ res.2 inner hinner c hc with h | h | h
        · rcases input with (draw | (bytes | coordinate)) | amount
          · change res ∈ support ((fun v => (v, s)) <$> (liftM (unifSpec.query draw) : ProbComp _)) at hres
            rw [support_map] at hres
            obtain ⟨v, _, rfl⟩ := hres
            exact Or.inl h
          · rw [costStep_ordinary] at hres
            rcases known_ordinary model bytes s res hres c h with h' | h'
            · exact Or.inl h'
            · exact Or.inr (Or.inr h')
          · change res ∈ support (sampleCoordinate coordinate s) at hres
            rw [sampleCoordinate_expose coordinate s res hres] at h
            by_cases hca : c = coordinate
            · subst hca
              exact Or.inr (Or.inl (List.mem_append_left _ (by simp [HiddenBridge.revealed])))
            · left
              simp only [DebtState.expose] at h
              simpa [QueryCache.cacheQuery, hca] using h
          · change res ∈ support (pure ((), s) : ProbComp _) at hres
            rw [support_pure, Set.mem_singleton_iff] at hres
            subst hres
            exact Or.inl h
        · exact Or.inr (Or.inl (List.mem_append_right _ h))
        · exact Or.inr (Or.inr h)
      · rw [support_pure, Set.mem_singleton_iff] at hout
        subst hout
        exact Or.inl hc

end Known

section Reveals

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A reveal is in the trace of every run that starts with it: it costs nothing, so it never
aborts. -/
theorem reveal_bind_mem (c : Coordinate) {β : Type} (k : Digest → OracleComp CostSpec β) (budget : ℕ) (s : State)
    (out : Run HashInput Coordinate β × State)
    (hout : out ∈ support (interp tg initial model
      (HiddenCost.reveal (D := HashInput) (R := HashOutput) c >>= k) budget s)) :
    c ∈ out.1.2.1 := by
  unfold HiddenCost.reveal at hout
  rw [interp_query_bind] at hout
  split_ifs at hout with h0
  swap
  · exact absurd (Nat.zero_le budget) h0
  rw [support_bind] at hout
  simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
  obtain ⟨res, _, inner, _, rfl⟩ := hout
  exact List.mem_append_left _ (by simp [HiddenBridge.revealed])

/-- A FORS opening reveals the secret of its leaf, whatever follows. -/
theorem tree_reveal_mem (data : PublicData) (index : Index) (κ : FTree) (leaf : FLeaf) {β : Type}
    (k : TreeOpening → OracleComp CostSpec β) (budget : ℕ) (s : State) (out : Run HashInput Coordinate β × State)
    (hout : out ∈ support (interp tg initial model (treeCostSource data index κ leaf >>= k) budget s)) :
    Coordinate.fors index κ leaf 0 ∈ out.1.2.1 := by
  unfold treeCostSource at hout
  simp only [Concrete.sequenceFin, bind_assoc, pure_bind] at hout
  exact reveal_bind_mem tg initial model _ _ budget s out hout

/-- **A completed family of computations** each of which reveals a coordinate whatever follows,
reveals all of them. -/
theorem seq_reveal_mem {α β : Type} : ∀ {n : ℕ} (f : Fin n → OracleComp CostSpec α) (c : Fin n → Coordinate),
    (∀ i {γ : Type} (k : α → OracleComp CostSpec γ) (b : ℕ) (s : State) (o : Run HashInput Coordinate γ × State),
      o ∈ support (interp tg initial model (f i >>= k) b s) → c i ∈ o.1.2.1) →
    ∀ (k : (Fin n → α) → OracleComp CostSpec β) (b : ℕ) (s : State) (out : Run HashInput Coordinate β × State),
      out ∈ support (interp tg initial model (Concrete.sequenceFin f >>= k) b s) → out.1.1 ≠ none →
      ∀ i, c i ∈ out.1.2.1
  | 0, _, _, _, _, _, _, _, _, _, i => i.elim0
  | n + 1, f, c, hf, k, b, s, out, hout, hsome, i => by
      have hstep : Concrete.sequenceFin f >>= k =
          f 0 >>= fun head => Concrete.sequenceFin (fun j : Fin n => f j.succ) >>= fun tail =>
            k (Fin.cons head tail) := by
        simp only [Concrete.sequenceFin, bind_assoc, pure_bind]; rfl
      rw [hstep] at hout
      cases i using Fin.cases with
      | zero => exact hf 0 _ b s out hout
      | succ j =>
          obtain ⟨o1, ho1, h1⟩ := interp_bind_mem tg initial model _ _ b s out hout
          rcases h1 with ⟨_, hn, _⟩ | ⟨v, _, o2, ho2, hres2, hrev2, _⟩
          · exact absurd hn hsome
          · rw [hrev2]
            refine List.mem_append_right _ ?_
            exact seq_reveal_mem (fun j : Fin n => f j.succ) (fun j => c j.succ) (fun j => hf j.succ)
              (fun tail => k (Fin.cons v tail)) _ _ o2 ho2 (by rw [← hres2]; exact hsome) j

/-- **A completed final assembly reveals every tree's secret at the digest's leaf.** -/
theorem finishRest_reveal_mem (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) (digest : MessageDigest) (budget : ℕ) (s : State)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (finishRest parameter data message randomness digest) budget s))
    (sig : Signature) (hsig : out.1.1 = some (some sig)) (κ : FTree) :
    Coordinate.fors (digestIndex digest) κ (digestLeaves digest κ) 0 ∈ out.1.2.1 := by
  unfold finishRest at hout
  obtain ⟨o1, _, h1⟩ := interp_bind_mem tg initial model _ _ budget s out hout
  rcases h1 with ⟨_, hn, _⟩ | ⟨_, _, o2, ho2, hres2, hrev2, _⟩
  · rw [hsig] at hn; cases hn
  rw [hrev2]
  refine List.mem_append_right _ ?_
  obtain ⟨o3, _, h3⟩ := interp_bind_mem tg initial model _ _ _ _ o2 ho2
  rcases h3 with ⟨_, hn, _⟩ | ⟨found, _, o4, ho4, hres4, hrev4, _⟩
  · rw [hn] at hres2; rw [hres2] at hsig; cases hsig
  rw [hrev4]
  refine List.mem_append_right _ ?_
  have hsig4 : o4.1.1 = some (some sig) := by rw [← hres4, ← hres2, hsig]
  rcases found with _ | found
  · change o4 ∈ support (interp tg initial model (pure none) _ _) at ho4
    rw [interp_pure, support_pure, Set.mem_singleton_iff] at ho4
    rw [ho4] at hsig4
    cases hsig4
  · obtain ⟨o5, _, h5⟩ := interp_bind_mem tg initial model _ _ _ _ o4 ho4
    rcases h5 with ⟨_, hn, _⟩ | ⟨_, _, o6, ho6, hres6, hrev6, _⟩
    · rw [hsig4] at hn; cases hn
    rw [hrev6]
    refine List.mem_append_right _ ?_
    exact seq_reveal_mem tg initial model _ (fun κ => Coordinate.fors (digestIndex digest) κ (digestLeaves digest κ) 0)
      (fun κ _ k b s o ho => tree_reveal_mem tg initial model data _ κ _ k b s o ho) _ _ _ o6 ho6
      (by rw [← hres6, hsig4]; simp) κ

/-- **A completed final assembly from a pair** caches the pair and reveals every tree's secret at
the leaf its digest selects. -/
theorem finishCost_reveal_mem (parameter : PublicParameter) (data : PublicData) (message : Message)
    (hparse : ∀ ρ call, model.parse (GraphView.pblk parameter data message ρ call) = none)
    (ρ : Randomness) (budget : ℕ) (s : State) (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) budget s))
    (sig : Signature) (hsig : out.1.1 = some (some sig)) :
    ∃ u, pcache parameter data message out.2 ρ = some u ∧
      ∀ κ, Coordinate.fors (digestIndex (truncateMessageDigest u)) κ
        (digestLeaves (truncateMessageDigest u) κ) 0 ∈ out.1.2.1 := by
  rw [finishCostSource_eq] at hout
  obtain ⟨u, b, s2, o, _, hs2, _, _, ho, hres, hrev, hst⟩ :=
    all_read_support tg initial model _ (pblk_injective parameter data message ρ) (hparse ρ) s _
      budget out hout (by rw [hsig]; simp)
  have hpc : pcache parameter data message out.2 ρ = some u := by
    unfold pcache
    refine allSome_of_eq _ u fun call => ?_
    rw [hst]
    exact (interp_extends tg initial model _ b s2 o ho).1 _ _ (hs2 call)
  refine ⟨u, hpc, fun κ => ?_⟩
  rw [hrev]
  exact finishRest_reveal_mem tg initial model parameter data message ρ _ b s2 o ho sig (by rw [← hres, hsig]) κ

end Reveals

end FORS.Security.SWRoute
