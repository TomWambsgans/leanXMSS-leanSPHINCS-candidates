import FORS.SWRoute.PPartJ
import FORS.SWRoute.ContactGood

/-! **The P-part with the contact potential.** `ppart_of_A4J` with the kill account bounded by the
contact potential A4' from the start (`wk_start_le`): the coin forecast, the coin cap and the
landed-pair cap at the start, `cU` per weighted surviving FORS leaf query (`WC`) and `ν` times the
excess account (`XS m`, WP-F). The contact potential's three step obligations (`hhash`, `hsign`,
`hpure` of `goodK_advProg`) are hypotheses here. -/

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

/-- **The P-part** (A4' step obligations as hypotheses). -/
theorem ppart_full (hcalls : digestCalls = 1) (hW : WtSpec model (weightA K data.root) IsMsgInput)
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none)
    (hkind : ∀ p call, K.tg.kind (pblk K.p data p call) = .none)
    (hdigest : ∀ p call, K.tg.digest (pblk K.p data p call))
    (hclean : ∀ p call, K.initial (pblk K.p data p call) = none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared K.initial s1 →
      ∀ out ∈ support (interp K.tg K.initial model (finishRest K.p data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0)
    (total : ℕ) (hfair : FairS wbar (total + digestAttemptLimit) Lmax) (hb0n : b0n ≠ ⊤)
    (hhash : ∀ (L : QueryLog SigningSpec) (x : HashInput) (next : HashOutput → OracleComp (OracleWorld + SigningSpec) Forgery),
      (∀ v, GoodK K data wbar Fail Lmax T model cU m total (next v) L) →
        GoodK K data wbar Fail Lmax T model cU m total (liftM ((OracleWorld + SigningSpec).query (.inl (.inr x))) >>= next) L)
    (hsign : ∀ (L : QueryLog SigningSpec) (msg : Message)
      (next : Option Signature → OracleComp (OracleWorld + SigningSpec) Forgery),
      MsgLive L msg → L.length < signatureLimit →
      (∀ r, GoodK K data wbar Fail Lmax T model cU m total (next r) (L ++ [⟨msg, r⟩])) →
        GoodK K data wbar Fail Lmax T model cU m total (liftM ((OracleWorld + SigningSpec).query (.inr msg)) >>= next) L)
    (hpure : ∀ (L : QueryLog SigningSpec) (forgery : Forgery), GoodK K data wbar Fail Lmax T model cU m total (pure forgery) L)
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
  ppart_of_A4J K data model wbar b0c b0n δ Fail Lmax hcalls hW hparse hkind hdigest hclean hfail hout total hfair hb0n
    M hnr hsb known hknown hw1 _
    (wk_start_le K data wbar Fail Lmax T model cU m total hhash hsign hpure hclean M hnr hsb known hknown)

end FORS.Security.SWRoute
