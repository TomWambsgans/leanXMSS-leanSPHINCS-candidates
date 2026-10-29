import FORS.SWRoute.ForecastXS
import FORS.SWRoute.ForecastDom

/-! **The tail account of the own-cell near forecast, closed** (WP-F, CORE-P's WP-F CONTRACT):
`xs_bound` with its per-query input `hexc` discharged by the domination `excPay_le_psi`:

  `ν · XS … ∅ … (ofReal m) M [] q' start [] [] 0 ≤ ofReal (q' / 2^128 · Pb)`   under `ForecastTail m q' Pb`. -/

open OracleComp OracleSpec ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.LoopWalk ForsPotential PotentialA
open FORS.Security FORS.Security.H0 FORS.Security.H0Avg FORS.Base.H0

/-- **The excess account is paid by the per-entry tail** `x · Pb` (no further hypothesis on the
excess payments). -/
theorem xs_bound_closed (K : Ctx) (data : PublicData) {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)
    (wbar : ℝ≥0∞) (m Pb : ℝ) (q' : ℕ) (hFT : ForecastTail m q' Pb) (hwbar : wbar = wbarOf q')
    (hH : totalHeight = subtreeHeight) (hcalls : digestCalls = 1)
    (hparse : ∀ p call, model.parse (pblk K.p data p call) = none)
    (hkind : ∀ p call, K.tg.kind (pblk K.p data p call) = .none)
    (hclean : ∀ p call, K.initial (pblk K.p data p call) = none)
    (hfail : ∀ msg ρ digest budget (s1 : State), Prepared K.initial s1 →
      ∀ out ∈ support (interp K.tg K.initial model (finishRest K.p data msg ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ (∅ : Finset (Fin (2 ^ subtreeHeight))))
    (hout : ∀ a i κ l, model.outgoing a ≠ Coordinate.fors i κ l 0)
    {Cmax Lmax : ℕ} (hfair : FairS wbar Cmax Lmax) (hQ : q' ≤ Cmax) (hlam0 : lam Lmax 0 q' ≤ (2 : ℝ≥0∞)⁻¹ ^ 101)
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M []) (hsb : SignBound M signatureLimit)
    (known : HiddenReveal.Knowledge Coordinate) (hknown : ∀ i κ l, known (Coordinate.fors i κ l 0) = none) :
    ν * XS K data.root data wbar ∅ model (ENNReal.ofReal m) M [] q' (DebtState.start K.initial known) [] [] 0 ≤
      ENNReal.ofReal ((q' : ℝ) / 2 ^ 128 * Pb) :=
  xs_bound K data model wbar m Pb q' hFT hwbar hH hcalls hparse hkind hclean hfail hout hfair hQ hlam0 M hnr hsb
    known hknown
    (fun tp s P Ms L d k x hH' hw hP hM hL hk hθ hn0 hrate hcoin hkn =>
      excPay_le_psi K data.root data wbar tp s P Ms L d k x hH' hw hP hM hL hk hθ hn0 hrate hcoin hkn)

end FORS.Security.SWRoute
