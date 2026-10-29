import FORS.SWRoute.Saturation

/-! **The SW route: the events of a final state.** On the stopped experiment with the above-word
values exposed, a correct guess or the refined bad event of a finished run is a decided hit of the
completed table, a state in the route's bad set, or a cover: a FORS payoff event and the event of
A4 (a recorded contact at a revealed secret, or a near cover with a recorded contact) are completed
FORS contacts, decided by the state because the FORS leaf values are known. Hence, pointwise,

  `Pr[win | completion] ≤ (1 - w_end) + w_end · finalValue (cover)`. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost PotentialA GraphView ForsPotential HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### Revealed coordinates are exposed -/

section Reveals

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
attribute [local instance] saturationDecEqCoordinate
variable (tg : Targeting D R ι) (initial : HiddenOutside.Cache D R) (model : HiddenRows.Model D R A ι)

omit [Fintype ι] in
/-- **Every coordinate revealed by a run is exposed at its end.** -/
theorem interp_reveals_known {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    ∀ budget (state : DebtState D R ι), ∀ out ∈ support (interp tg initial model computation budget state),
      ∀ c ∈ out.1.2.1, out.2.known c ≠ none := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state out hout c hc
      rw [interp_pure, support_pure, Set.mem_singleton_iff] at hout
      rw [hout] at hc
      cases hc
  | query_bind input next ih =>
      intro budget state out hout c hc
      rw [interp_query_bind] at hout
      split_ifs at hout with hcost
      · rw [support_bind] at hout
        simp only [Set.mem_iUnion, support_map, Set.mem_image] at hout
        obtain ⟨result, hresult, inner, hinner, rfl⟩ := hout
        rcases List.mem_append.1 hc with hc | hc
        · -- the coordinate revealed by this step
          rcases input with (draw | (bytes | coordinate)) | amount
          · cases hc
          · cases hc
          · rw [show revealed (D := D) (R := R) (.inl (.inr (.inr coordinate))) = [coordinate] from rfl,
              List.mem_singleton] at hc
            subst hc
            have hk : result.2.known c ≠ none := by
              rw [costStep_inl, lazyStep_reveal] at hresult
              cases hkc : state.known c with
              | some w =>
                  rw [sampleCoordinate_known c state w hkc, support_pure, Set.mem_singleton_iff] at hresult
                  rw [hresult, hkc]; simp
              | none =>
                  rw [sampleCoordinate_expose c state result hresult]
                  simp [DebtState.expose]
            obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hk
            have hext := interp_extends tg initial model (next result.1) _ result.2 inner hinner
            rw [hext.2.1 c w hw]
            simp
          · cases hc
        · exact ih result.1 _ result.2 inner hinner c hc
      · rw [support_pure, Set.mem_singleton_iff] at hout
        rw [hout] at hc
        cases hc

end Reveals

/-! ### The pointwise decomposition -/

section Pointwise

open Completeness SeedModel Graph Assembly Reduce Internalize

variable (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
  (remaining : RemainingOutputs) (prepared : (OtsKey → Option (Counter × Encoding)) × QueryCache HashSpec)
  (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
  (known : Knowledge Coordinate)
  (hk : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
    (knownOf (truncateHash parameterOutput) fixed)))
  (ρ : ℝ) (adversary : Adversary) (q : ℕ)

/-- The FORS leaf values are known from the start of the sample's comparison. -/
theorem known_fleaf (hk : known ∈ support (exposeR (aboveList (truncateHash parameterOutput) prepared.1)
    (knownOf (truncateHash parameterOutput) fixed))) (f : FIn) :
    known f.outC = some ((ctxA parameterOutput fixed highs remaining prepared known ρ).F f.outC) := by
  have hbase : knownOf (truncateHash parameterOutput) fixed f.outC ≠ none := by
    unfold knownOf
    rw [if_pos (show KnownCoordinate (truncateHash parameterOutput) f.outC from rfl)]
    simp
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hbase
  have h1 := (PotentialA.exposeR_known _ _ _ hk).1 _ _ hv
  change known f.outC = some ((known f.outC).getD 0)
  rw [h1]
  rfl

include hprepared hk in
/-- **Pointwise decomposition.** A correct guess or the refined bad event of a finished run has,
over the completion of its final state, probability at most the missing route weight plus the
route weight times the cover value. -/
theorem sw_pointwise (steps : Message → Randomness) (out : Run HashInput Coordinate HiddenBridge.Outcome × State)
    (hout : out ∈ support (interp (targetingA parameterOutput fixed highs remaining prepared.1) prepared.2
      (sampleModel parameterOutput highs)
      (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
        (internalize adversary)) q (DebtState.start prepared.2 known))) :
    Pr[fun T => CorrectGuess T out.2 ∨ badAV parameterOutput fixed highs remaining prepared.1 T
        (((out.1.1, out.1.2.1), out.1.2.2.1), out.2.cache) | completion out.2.known] ≤
      (1 - weightA (ctxA parameterOutput fixed highs remaining prepared known ρ)
          (sampleData parameterOutput fixed highs remaining steps).root out.2) +
        weightA (ctxA parameterOutput fixed highs remaining prepared known ρ)
            (sampleData parameterOutput fixed highs remaining steps).root out.2 *
          finalValue (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
            (targetingA parameterOutput fixed highs remaining prepared.1) prepared.2 [] out := by
  set K := ctxA parameterOutput fixed highs remaining prepared known ρ with hK
  set root := (sampleData parameterOutput fixed highs remaining steps).root with hroot
  have hroot' : (sampleData parameterOutput fixed highs remaining).root = root := rfl
  set s := out.2 with hs
  set fv := finalValue (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining steps)
    (targetingA parameterOutput fixed highs remaining prepared.1) prepared.2 [] out with hfv
  have hinv := inv_final parameterOutput fixed highs remaining prepared known ρ hk
    (targetingA parameterOutput fixed highs remaining prepared.1) _ q out hout
  have hext := interp_extends (targetingA parameterOutput fixed highs remaining prepared.1) prepared.2
    (sampleModel parameterOutput highs) _ q _ out hout
  have hleaf : ∀ f : FIn, s.known f.outC = some (K.F f.outC) := fun f =>
    hext.2.1 _ _ (known_fleaf parameterOutput fixed highs remaining prepared known ρ hk f)
  have hrev := interp_reveals_known (targetingA parameterOutput fixed highs remaining prepared.1) prepared.2
    (sampleModel parameterOutput highs) _ q _ out hout
  have hw1 : weightA K root s ≤ 1 := weightA_le_one K root s
  -- a bad state: the bound is one
  by_cases hbad : BadP K root s
  · rw [weightA_of_badP K root hbad, tsub_zero, zero_mul, add_zero]
    exact probEvent_le_one
  -- a cover: the bound is one
  by_cases hcov : fv = 1
  · rw [hcov, mul_one, tsub_add_cancel_of_le hw1]
    exact probEvent_le_one
  -- otherwise the event is a hit of the completed table
  have hw : weightA K root s = weight K.tg K.initial s := weightA_eq_weight_of K root hbad
  refine le_trans ?_ le_self_add
  rw [hw]
  -- FORS contacts against an extending table are the state's contacts
  have hfct : ∀ T, tableExtending s.known T = T → ∀ f, K.FCT T s f → FCk K s f := by
    intro T hT f ⟨u, hfr, ht⟩
    have hag := (ForsPotential.agrees_iff_extending _ T).2 hT
    have hTf : T f.outC = K.F f.outC := hag _ _ (hleaf f)
    exact ⟨u, hfr, ht.trans hTf⟩
  have hsub : ∀ T, tableExtending s.known T = T →
      (CorrectGuess T s ∨ badAV parameterOutput fixed highs remaining prepared.1 T
        (((out.1.1, out.1.2.1), out.1.2.2.1), s.cache)) → Hit K.tg K.initial T s := by
    intro T hT hev
    rcases small_pointwiseF parameterOutput fixed highs remaining prepared hprepared known hk ρ adversary q
      steps out hout T hT hev with hpay | ⟨outcome, hres, -, ha4⟩ | hf
    · -- a payoff event
      unfold payoffA Ctx.payoff at hpay
      split_ifs at hpay with hp
      · rcases hp with hh | hwb | ⟨f, hf, hnr⟩ | ⟨f, g, hrel, hf, hg⟩
        · exact hh
        · exact absurd (Or.inr (Or.inl hwb)) hbad
        · -- an unrecorded contact has its secret known
          have hfc := hfct T hT f hf
          have hkn : s.known f.inC ≠ none := by
            obtain ⟨u, hfr, -⟩ := hfct T hT f hf
            exact fun hnone =>
              hnr (hinv.guessed _ u (Address.fleaf f.index f.κ f.leaf, f.v) hfr (parse_fleaf K f) hnone)
          exact absurd (Or.inr (Or.inr (Or.inr ⟨f, hfc, Or.inl hkn⟩))) hbad
        · have hne : f ≠ g := fun h => by rw [h] at hrel; exact hrel.2 rfl
          exact absurd (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ⟨f, g, hne, hfct T hT f hf, hfct T hT g hg⟩))))) hbad
      · exact absurd hpay (by norm_num)
    · -- the event of A4 is a completed contact
      exfalso
      rw [hroot'] at ha4
      rcases ha4 with ⟨index, κ, leaf, hrv, v, hf, -⟩ | ⟨-, digest, hcd, hland, -, κ, ⟨v, hf, -⟩, hcov'⟩
      · exact hbad (Or.inr (Or.inr (Or.inr ⟨⟨index, κ, leaf, v⟩, hfct T hT _ hf, Or.inl (hrev _ hrv)⟩)))
      · refine hbad (Or.inr (Or.inr (Or.inr ⟨⟨digestIndex digest, κ, digestLeaves digest κ, v⟩, hfct T hT _ hf,
          Or.inr ⟨outcome.1.message, outcome.1.signature.randomness, digest, hcd, hland, rfl, rfl,
            fun κ' hκ' => ?_⟩⟩)))
        have h := hcov' κ' hκ'
        unfold TreeCov at h
        simp only [fullDigestView, revealedSet, Finset.mem_filter, Finset.mem_univ, true_and] at h
        exact hrev _ h
    · exact absurd hf hcov
  calc Pr[fun T => CorrectGuess T s ∨ badAV parameterOutput fixed highs remaining prepared.1 T
          (((out.1.1, out.1.2.1), out.1.2.2.1), s.cache) | completion s.known]
      ≤ Pr[fun T => Hit K.tg K.initial T s | completion s.known] := by
        refine probEvent_mono fun T hT hev => hsub T ?_ hev
        unfold completion at hT
        rw [support_map] at hT
        obtain ⟨t, _, rfl⟩ := hT
        funext c
        simp only [tableExtending]
        cases s.known c <;> rfl
    _ ≤ 1 - weight K.tg K.initial s := by
        have hsplit := probEvent_compl (completion s.known) (fun T => Hit K.tg K.initial T s)
        rw [probFailure_eq_zero, tsub_zero] at hsplit
        have hle := weight_le_noHit K.tg K.initial s
        calc Pr[fun T => Hit K.tg K.initial T s | completion s.known]
            = 1 - Pr[fun T => ¬Hit K.tg K.initial T s | completion s.known] :=
              ENNReal.eq_sub_of_add_eq (ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one) hsplit
          _ ≤ _ := tsub_le_tsub_left hle _

end Pointwise

end FORS.Security.SWRoute
