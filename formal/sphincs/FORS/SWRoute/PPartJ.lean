import FORS.SWRoute.Release

/-! **The P-part with the release discharged.** `ppart_of_A4` with the run invariant `JInv`
(known FORS secrets were revealed; signed pairs have all their secrets known): it holds at the start
when no FORS secret is known, and no row of the model outputs a FORS secret. What remains of the
P-part is the bound `hA4` of the kill account by the contact potential A4'. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.LoopWalk ForsPotential PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable (K : Ctx) (data : PublicData) {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (wbar b0c b0n : ℝ≥0∞) (δ : ℝ) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Lmax : ℕ)

/-- **The P-part from the contact part.** -/
theorem ppart_of_A4J (hcalls : digestCalls = 1) (hW : WtSpec model (weightA K data.root) IsMsgInput)
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none)
    (hkind : ∀ p call, K.tg.kind (pblk K.p data p call) = .none)
    (hdigest : ∀ p call, K.tg.digest (pblk K.p data p call))
    (hclean : ∀ p call, K.initial (pblk K.p data p call) = none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared K.initial s1 →
      ∀ out ∈ support (interp K.tg K.initial model (finishRest K.p data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0)
    (total : ℕ) (hfair : FairS wbar (total + digestAttemptLimit) Lmax) (hb0n : b0n ≠ ⊤)
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M [])
    (hsb : SignBound M signatureLimit) (known : HiddenReveal.Knowledge Coordinate)
    (hknown : ∀ i κ l, known (Coordinate.fors i κ l 0) = none)
    (hw1 : weightA K data.root (DebtState.start K.initial known) = 1)
    (B4 : ℝ≥0∞)
    (hA4 : WK model K data.root (advProg K.p data M []) total (DebtState.start K.initial known) ≤ B4) :
    ∑' out, Pr[= out | interp K.tg K.initial model (advProg K.p data M []) total (DebtState.start K.initial known)] *
        (weightA K data.root out.2 * finalValue K.p data K.tg K.initial [] out) +
      ENNReal.ofReal δ * WA model K data.root (advProg K.p data M []) total (DebtState.start K.initial known) false +
      WK model K data.root (advProg K.p data M []) total (DebtState.start K.initial known) ≤
    (total * startExcessO wbar b0c total + ENNReal.ofReal δ * (total * startExcessG witnessNear wbar b0n total)) +
      B4 + (b0c + ENNReal.ofReal δ * b0n) *
        WF model K data.root (advProg K.p data M []) total (DebtState.start K.initial known) +
      (1 + ENNReal.ofReal δ) * ((total * failMass Fail + signatureLimit * failMass Fail) + lam Lmax 0 total) :=
  ppart_of_A4 K data model wbar b0c b0n δ Fail Lmax hcalls hW hparse hkind hdigest hclean hfail total hfair hb0n
    (JInv K.p data)
    (fun s P Ms L d R n k input hP hD hJ harm =>
      release_coreG K data wbar b0n Fail hfair.le_one s P Ms L d R n k input hP hD hJ harm)
    (fun s L R x r hr hJ => jInv_ordinary K.p data model hout s L R x r hr hJ)
    (fun s L R p u hfresh hJ => jInv_withPair K.p data model hout s L R p u hfresh hJ)
    (fun budget s L R m o1 r ho1 hr hJ => jInv_sign K.p data K.tg K.initial model hout hparse budget s L R m o1 r ho1 hr hJ)
    M hnr hsb known hw1 (jInv_start K.p data K.initial known hknown) B4 hA4

end FORS.Security.SWRoute
