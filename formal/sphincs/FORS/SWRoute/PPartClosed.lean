import FORS.SWRoute.PPartFull
import FORS.SWRoute.ContactStep

/-! **The P-part with the hash steps of the contact potential discharged.** `ppart_full` with the
step obligations `hhash` (`goodK_hash`) and `hpure` (`goodK_pure`) of `goodK_advProg` proved; the
signing step `hsign` stays a hypothesis (`ppart_of_sign`). -/

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
  (wbar b0c b0n : ℝ≥0∞) (δ : ℝ) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Lmax T : ℕ) (cU m : ℝ≥0∞)

/-- **The P-part from the signing step of the contact potential** (the hash steps proved). -/
theorem ppart_of_sign (hcalls : digestCalls = 1) (hW : WtSpec model (weightA K data.root) IsMsgInput)
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none)
    (hkind : ∀ p call, K.tg.kind (pblk K.p data p call) = .none)
    (hdigest : ∀ p call, K.tg.digest (pblk K.p data p call))
    (hclean : ∀ p call, K.initial (pblk K.p data p call) = none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared K.initial s1 →
      ∀ out ∈ support (interp K.tg K.initial model (finishRest K.p data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0)
    (total : ℕ) (hfair : FairS wbar (total + digestAttemptLimit) Lmax) (hb0n : b0n ≠ ⊤)
    (hcU : ν * ((signatureLimit : ℝ≥0∞) * revRate + m) ≤ cU)
    (hsign : ∀ (L : QueryLog SigningSpec) (msg : Message)
      (next : Option Signature → OracleComp (OracleWorld + SigningSpec) Forgery),
      MsgLive L msg → L.length < signatureLimit →
      (∀ r, GoodK K data wbar Fail Lmax T model cU m total (next r) (L ++ [⟨msg, r⟩])) →
        GoodK K data wbar Fail Lmax T model cU m total (liftM ((OracleWorld + SigningSpec).query (.inr msg)) >>= next) L)
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M [])
    (hsb : SignBound M signatureLimit) (known : HiddenReveal.Knowledge Coordinate)
    (hknown : ∀ i κ l, known (Coordinate.fors i κ l 0) = none)
    (hw1 : weightA K data.root (DebtState.start K.initial known) = 1) :
    ∑' out, Pr[= out | interp K.tg K.initial model (advProg K.p data M []) total (DebtState.start K.initial known)] *
        (weightA K data.root out.2 * finalValue K.p data K.tg K.initial [] out) +
      ENNReal.ofReal δ * WA model K data.root (advProg K.p data M []) total (DebtState.start K.initial known) false +
      WK model K data.root (advProg K.p data M []) total (DebtState.start K.initial known) ≤
    (total * startExcessO wbar b0c total + ENNReal.ofReal δ * (total * startExcessG witnessNear wbar b0n total)) +
      ((coinPotK T total + capC K.p data T total (DebtState.start K.initial known) [] [] + lam Lmax 0 total) +
        cU * WC model K data.root (advProg K.p data M []) total (DebtState.start K.initial known) +
        ν * XS K data.root data wbar Fail model m M [] total (DebtState.start K.initial known) [] [] 0) +
      (b0c + ENNReal.ofReal δ * b0n) *
        WF model K data.root (advProg K.p data M []) total (DebtState.start K.initial known) +
      (1 + ENNReal.ofReal δ) * ((total * failMass Fail + signatureLimit * failMass Fail) + lam Lmax 0 total) :=
  ppart_full K data model wbar b0c b0n δ Fail Lmax T cU m hcalls hW hparse hkind hdigest hclean hfail hout total hfair
    hb0n
    (fun L x next h => goodK_hash K data wbar Fail Lmax T model cU m total hcalls hparse hout hfair
      (Nat.le_add_right _ _) hcU L x next h)
    hsign
    (fun L forgery => goodK_pure K data wbar Fail Lmax T model cU m total hcalls hparse hout hfair
      (Nat.le_add_right _ _) hcU L forgery)
    M hnr hsb known hknown hw1

end FORS.Security.SWRoute
