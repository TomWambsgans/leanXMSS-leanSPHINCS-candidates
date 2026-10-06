import LeanSphincs.BridgeForsGame
import LeanSphincs.BridgeForsPotentialOnce

/-! The one-coin FORS potential through an adversary that never requests a signature on the same
message twice. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-- The program never requests a signature on a message of `S`, nor twice on the same message. -/
def NoRepeat {α : Type} (M : OracleComp (OracleWorld + SigningSpec) α) : List Message → Prop :=
  OracleComp.construct (C := fun _ => List Message → Prop) (fun _ _ => True)
    (fun input _ rec S => match input with
      | .inl _ => ∀ v, rec v S
      | .inr m => m ∉ S ∧ ∀ r, rec r (S ++ [m])) M

omit [Params] in
theorem noRepeat_sign {α : Type} (m : Message)
    (next : Option Signature → OracleComp (OracleWorld + SigningSpec) α) (S : List Message) :
    NoRepeat (liftM ((OracleWorld + SigningSpec).query (.inr m)) >>= next) S ↔
      m ∉ S ∧ ∀ r, NoRepeat (next r) (S ++ [m]) :=
  Iff.rfl

/-- An adversary that never requests a signature on the same message twice. -/
def _root_.LeanSphincs.Security.Adversary.NoRepeat (adversary : Adversary) : Prop :=
  ∀ pk, ForsPotential.NoRepeat (adversary.main pk) []

section Induction

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)

theorem goodO_finish (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hfair : Fair5 wbar) (hb0 : b0 ≠ ⊤) (L : QueryLog SigningSpec) (forgery : Forgery) :
    GoodO parameter data wbar b0 Fail Qtot tg initial model L (finishGame parameter data L forgery) := by
  unfold finishGame
  exact goodO_liftHash parameter data wbar b0 Fail Qtot tg initial model hparse hkind hdigest hfair hb0 L _ _
    fun v => goodO_pure parameter data wbar b0 Fail Qtot tg initial model hfair.le_one L forgery v

/-- **The one-coin potential through any adversary that never repeats a message.** -/
theorem goodO_advProg (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hfair : Fair5 wbar) (hb0 : b0 ≠ ⊤) :
    ∀ (M : OracleComp (OracleWorld + SigningSpec) Forgery) (L : QueryLog SigningSpec),
      NoRepeat M (L.map Sigma.fst) → GoodO parameter data wbar b0 Fail Qtot tg initial model L (advProg parameter data M L) := by
  intro M
  induction M using OracleComp.inductionOn with
  | pure forgery =>
      intro L _
      rw [advProg_pure]
      exact goodO_finish parameter data wbar b0 Fail Qtot tg initial model hparse hkind hdigest hfair hb0 L forgery
  | query_bind input next ih =>
      intro L hnr
      rcases input with (draw | bytes) | message
      · rw [advProg_draw]
        exact goodO_draw parameter data wbar b0 Fail Qtot tg initial model L draw _ fun v => ih v L (hnr v)
      · rw [advProg_hash]
        exact goodO_ordinary parameter data wbar b0 Fail Qtot tg initial model hparse hkind hdigest hfair hb0 L
          bytes _ fun v => ih v L (hnr v)
      · rw [advProg_sign]
        obtain ⟨hnot, hrest⟩ := (noRepeat_sign message next _).1 hnr
        have hm : ∀ entry ∈ L, entry.1 ≠ message := by
          intro entry he heq
          exact hnot (heq ▸ List.mem_map_of_mem he)
        refine goodO_sign tg initial model parameter data wbar b0 Fail Qtot message hparse hfail hfair hb0 L hm _
          fun r => ih r _ ?_
        rw [List.map_append]
        exact hrest r

end Induction

end LeanSphincs.Security.ForsPotential
