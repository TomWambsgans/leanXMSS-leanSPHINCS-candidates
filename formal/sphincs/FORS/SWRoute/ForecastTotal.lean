import FORS.SWRoute.ForecastXS

/-! **The crude total of the excess account.** For any failing set `Fail` and any cap `m ≥ 0`, the
excess account of the whole game is at most one weight unit per budget unit: each FORS leaf query
pays `w (min(1, Π_c) - m)⁺ ≤ 1`, so `ν · XS ≤ q' / 2^128` (`xs_le_total`; from `XS_le_budget`). The
route uses it for samples with a nonempty failing set, where `xs_bound` (which needs `Fail = ∅`)
does not apply. -/

open OracleComp OracleSpec ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.LoopWalk ForsPotential PotentialA

/-- **The crude total**: `ν · XS ≤ q' / 2^128` for every failing set and every cap `m ≥ 0`. -/
theorem xs_le_total (K : Ctx) (data : PublicData) {A : Type} (model : HiddenRows.Model HashInput HashOutput A Coordinate)
    (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (m : ℝ) (hm : 0 ≤ m) (q' : ℕ)
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (s : State) :
    ν * XS K data.root data wbar Fail model (ENNReal.ofReal m) M [] q' s [] [] 0 ≤
      ENNReal.ofReal ((q' : ℝ) / 2 ^ 128) := by
  have h := XS_le_budget K data wbar Fail model m M [] q' s [] [] 0
  have h1 : ENNReal.ofReal (1 - m) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc ν * XS K data.root data wbar Fail model (ENNReal.ofReal m) M [] q' s [] [] 0
      ≤ ν * ((q' : ℝ≥0∞) * ENNReal.ofReal (1 - m)) := mul_le_mul_right h ν
    _ ≤ ν * (q' : ℝ≥0∞) := mul_le_mul_right (mul_le_of_le_one_right' h1) ν
    _ = ENNReal.ofReal ((q' : ℝ) / 2 ^ 128) := by
        unfold ν
        rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat, ENNReal.div_eq_inv_mul]

end FORS.Security.SWRoute
