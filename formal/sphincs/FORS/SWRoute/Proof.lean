import FORS.SWRoute.DetSW
import FORS.SWRoute.ForecastFinal

/-! **The SW route is proved.** `DetSW` (`SWRoute/Interface.lean`) follows from `detSW_of`
(`SWRoute/DetSW.lean`) and the excess account's tail bound `xs_bound_closed`
(`SWRoute/ForecastFinal.lean`). -/

namespace FORS.Security.SWRoute

variable [Params]

/-- **The survival-weighted route**, for every parameter set. -/
theorem detSW : DetSW :=
  detSW_of fun K data model wbar m Pb q' hFT hw hH hc hp hk hcl hf ho _ _ hfair hQ hlam M hnr hsb known hkn =>
    xs_bound_closed K data model wbar m Pb q' hFT hw hH hc hp hk hcl hf ho hfair hQ hlam M hnr hsb known hkn

end FORS.Security.SWRoute
