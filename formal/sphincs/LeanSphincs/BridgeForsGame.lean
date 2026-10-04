import LeanSphincs.BridgeForsPotential

/-! The FORS potential through an arbitrary adaptive adversary: every adversary step is a draw,
an ordinary hash query or a signing call, and verification is a lifted hash computation. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

section Program

variable (parameter : PublicParameter) (data : PublicData)

/-- Verification of the forgery, with the log so far. -/
noncomputable def finishGame (L : QueryLog SigningSpec) (forgery : Forgery) : OracleComp CostSpec HiddenBridge.Outcome := do
  let verified ← liftM (Concrete.verify (⟨data.root, parameter⟩ : PublicKey) forgery.message forgery.signature :
    OracleComp HashSpec Bool)
  return (forgery, L, verified)

/-- The rest of the game from an adversary computation and a log prefix. -/
noncomputable def advProg (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec) :
    OracleComp CostSpec HiddenBridge.Outcome :=
  (simulateQ (costInteraction parameter data) M).run >>= fun r => finishGame parameter data (L ++ r.2) r.1

theorem costRestX_eq (adversary : Adversary) :
    HiddenBridge.costRestX parameter data adversary =
      advProg parameter data (adversary.main ⟨data.root, parameter⟩) [] := by
  unfold HiddenBridge.costRestX advProg finishGame
  refine bind_congr fun r => ?_
  rcases r with ⟨forgery, log⟩
  simp only [List.nil_append]

theorem advProg_pure (forgery : Forgery) (L : QueryLog SigningSpec) :
    advProg parameter data (pure forgery) L = finishGame parameter data L forgery := by
  unfold advProg
  rw [simulateQ_pure, WriterT.run_pure, pure_bind]
  simp

theorem advProg_draw (draw : ℕ) (next : Fin (draw + 1) → OracleComp (OracleWorld + SigningSpec) Forgery)
    (L : QueryLog SigningSpec) :
    advProg parameter data (liftM ((OracleWorld + SigningSpec).query (.inl (.inl draw))) >>= next) L =
      liftM (CostSpec.query (.inl (.inl draw))) >>= fun v => advProg parameter data (next v) L := by
  unfold advProg
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  change (((fun v => (v, (∅ : QueryLog SigningSpec))) <$> (liftM (CostSpec.query (.inl (.inl draw))) :
      OracleComp CostSpec _)) >>= _) >>= _ = _
  simp only [bind_map_left, bind_assoc]
  rfl

theorem advProg_hash (bytes : HashInput) (next : HashOutput → OracleComp (OracleWorld + SigningSpec) Forgery)
    (L : QueryLog SigningSpec) :
    advProg parameter data (liftM ((OracleWorld + SigningSpec).query (.inl (.inr bytes))) >>= next) L =
      liftM (CostSpec.query (.inl (.inr (.inl bytes)))) >>= fun v => advProg parameter data (next v) L := by
  unfold advProg
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  change (((fun v => (v, (∅ : QueryLog SigningSpec))) <$> (liftM (CostSpec.query (.inl (.inr (.inl bytes)))) :
      OracleComp CostSpec _)) >>= _) >>= _ = _
  simp only [bind_map_left, bind_assoc]
  rfl

theorem advProg_sign (message : Message) (next : Option Signature → OracleComp (OracleWorld + SigningSpec) Forgery)
    (L : QueryLog SigningSpec) :
    advProg parameter data (liftM ((OracleWorld + SigningSpec).query (.inr message)) >>= next) L =
      signCostSource parameter data message >>= fun r => advProg parameter data (next r) (L ++ [⟨message, r⟩]) := by
  unfold advProg
  rw [simulateQ_bind, WriterT.run_bind, simulateQ_spec_query]
  change ((QueryImpl.withLogging (spec := SigningSpec) (m := OracleComp CostSpec)
      (fun message => GraphView.signCostSource parameter data message) message).run >>= _) >>= _ = _
  rw [QueryImpl.run_withLogging_apply]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun r => ?_
  rw [bind_map_left]
  refine bind_congr fun r' => ?_
  simp only [List.append_assoc]

end Program

section Induction

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

theorem good_finish (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (L : QueryLog SigningSpec) (forgery : Forgery) :
    Good parameter data wbar b0 Fail Qtot tg initial model L (finishGame parameter data L forgery) := by
  unfold finishGame
  exact good_liftHash parameter data wbar b0 Fail Qtot tg initial model hparse hkind hdigest hw hb0 L _ _
    fun v => good_pure parameter data wbar b0 Fail Qtot tg initial model hw L forgery v

/-- **The potential through any adversary.** -/
theorem good_advProg (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    {Cmax : ℕ} (hfair : Fair wbar Cmax) (hb0 : b0 ≠ ⊤) (hQ : Qtot + digestAttemptLimit ≤ Cmax) :
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec),
      Good parameter data wbar b0 Fail Qtot tg initial model L (advProg parameter data M L) := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L
      rw [advProg_pure]
      exact good_finish parameter data wbar b0 Fail Qtot tg initial model hparse hkind hdigest hfair.le_one hb0 L forgery
  | query_bind input next ih =>
      intro L
      rcases input with (draw | bytes) | message
      · rw [advProg_draw]
        exact good_draw parameter data wbar b0 Fail Qtot tg initial model L draw _ fun v => ih v L
      · rw [advProg_hash]
        exact good_ordinary parameter data wbar b0 Fail Qtot tg initial model hparse hkind hdigest hfair.le_one hb0 L
          bytes _ fun v => ih v L
      · rw [advProg_sign]
        exact good_sign tg initial model parameter data wbar b0 Fail Qtot hparse hfail hfair hb0 hQ L message _
          fun r => ih r _

end Induction

end LeanSphincs.Security.ForsPotential
