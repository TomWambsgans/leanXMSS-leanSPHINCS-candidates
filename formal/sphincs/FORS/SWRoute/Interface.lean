import FORS.LazyRun.SaturationE
import FORS.LargeBudget.Route
import FORS.CoverBound.NearOption
import FORS.SWRoute.ForecastTail

/-! **The survival-weighted route: its interface.** Between the small route (budgets up to `q_h`)
and the large route, the survival-weighted route ("SW route") bounds the deterministic signer at
budgets `q' = q - keygenCost` with `x = q' / 2^128`:

  `Pr[win] ≤ (1 - (1 - x)^ρ) + q' · H_cover(b0c) + δ · q' · H_near(b0n) + coin + slack`,

with the survival weight times the budget at a state-dependent exponent (`ρ` unarmed, `2` armed by a
marker, a WOTS contact, a near cover or a FORS contact, higher after contacts), the weighted one-coin
cover potential at the baseline `b0c`, the weighted near potential at the baseline `b0n` gated by the
armed status, the contact potential A4, and the leaf-restricted coin. A digest query pays
`b0c + δ · b0n ≤ β / 2^128`; arming costs at most `δ`.

This file fixes the side conditions `SWNumeric` (real, polynomial in `ρ, β, δ, x`), the coin term,
the near start value, and the statement `DetSW` of the route that the potential argument proves and
the closing (`SWRoute/Closing.lean`) uses. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.ForsPotential

variable [Params]

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
  FORS.Base.Domination

/-- The generic witness's excess forecast of a new pair at the start of the run (`startExcessO` is
the cover witness's). -/
noncomputable def startExcessG (W : View → Multiset View → ℝ≥0∞) (wbar b0 : ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtualOnce Finset.univ wbar (excessW W b0) signatureLimit I 0) k []

end FORS.Security.ForsPotential

namespace FORS.Security.SWRoute

open FORS.Security ForsPotential HiddenDebt

/-- **The side conditions of the SW route** at `x = q' / 2^128` (all polynomial):
* `eA` (a chain step two below the word: a guess, then half a unit of pending two-edge credit),
  `e1` (an encoding: a marker arms at most `4032 ν`), `eB` (a chain step one below the word: a WOTS
  contact jumps the exponent to `66`), `e3` (a FORS leaf query: a guess, a decided contact jumping to
  `3`, and the contact coefficient `cU`);
* `beta` (the least digest decrement of the budget at exponent `ρ`) and the decrements at the armed
  and contact exponents `2, 3, 66, 67` (`dA`, `d3`, `d66`, `d67`);
* `delta` (arming: `v^ρ - v^2 ≤ δ` for `v ∈ [1 - x, 1]`). -/
structure SWNumeric (ρ β δ x cU : ℝ) : Prop where
  x0 : 0 ≤ x
  x8 : x ≤ 1 / 8
  low : 3 / 2 ≤ ρ
  high : ρ ≤ 2
  eA : 1 / 2 ≤ (ρ - 1) * (1 - ρ * x)
  e1 : 4032 * (2 - ρ) * x / (1 - x) ≤ ρ - 1
  eB : 2 - ρ ≤ (1 - x) ^ 65
  e3 : 1 + (3 - ρ) * x / (1 - x) + cU / (1 - x) ^ 3 ≤ ρ
  cU0 : 0 ≤ cU
  beta0 : 0 ≤ β
  beta : β ≤ ρ / (1 + (ρ - 1) * x / (1 - x))
  dA : β ≤ 2 * (1 - x)
  d3 : β ≤ 3 * (1 - x) ^ 2
  d66 : β ≤ 66 * (1 - x) ^ 65
  d67 : β ≤ 67 * (1 - x) ^ 66
  delta : (1 - ρ * x + ρ * (ρ - 1) * x ^ 2 / 2) * (2 - ρ) * x / (1 - x) ≤ δ

variable [Params]

/-- **The leaf-restricted coin**: the chance that a signature reveals a contact through a cached
landed pair of its message, at budget `q`, plus the failure of the cell-count bound. -/
noncomputable def coinSW (q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((q : ℝ) / 2 ^ 128) ^ 2 / 2 ^ 30 + ((q : ℝ) / 2 ^ 128) / 2 ^ 100 + 1 / 2 ^ 180)

/-- **The SW route** (proved by the potential argument, used by the closing). For an adversary with
`q < 2^127` hash queries and `q' = q - keygenCost`: if the side conditions hold at `x = q' / 2^128`
with a contact coefficient `cU ≥ N / 2^(b+a) + m` (the reveal rate of the signatures and the cap `m`
of the own-leaf near forecast at a surviving FORS leaf query), the forecast's tail `Pb` beyond `m`
(`ForecastTail`), the digest payment `b0c + δ b0n` fits in `β / 2^128`,
and the route's terms (saturation at `ρ`, the cover and near start values, the coin, `x · Pb`) plus the slack
fit in `(q' + keygenCost) / 2^127`, then the advantage is at most `q / 2^127`. -/
def DetSW : Prop :=
  ∀ (_hb : 0 < keptHeight topLayer) (adversary : Adversary) (q : ℕ),
    totalHeight = subtreeHeight → 31 ≤ subtreeHeight + forsHeight → digestCalls = 1 →
    HasHashQueryBound adversary q → q < 2 ^ 127 → keygenCost ≤ q → signatureLimit ≤ 2 ^ 70 →
    q - keygenCost + 2 ^ 32 + (H0.scanM - 1) * H0.LmaxOf (q - keygenCost) + (2 * H0.scanM - 1) ≤ 2 ^ 128 →
    ∀ (ρ β δ cU m Pb : ℝ) (b0c b0n : ℝ≥0∞),
      SWNumeric ρ β δ (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128) cU →
      (signatureLimit : ℝ) / (2 ^ subtreeHeight * 2 ^ forsHeight) + m ≤ cU →
      ForecastTail m (q - keygenCost) Pb →
      b0c + ENNReal.ofReal δ * b0n ≤ ENNReal.ofReal (β / 2 ^ 128) →
      (1 - budgetE ρ 0 (q - keygenCost)) +
          ((q - keygenCost : ℕ) : ℝ≥0∞) * startExcessO (H0.wbarOf (q - keygenCost)) b0c (q - keygenCost) +
          ENNReal.ofReal δ * (((q - keygenCost : ℕ) : ℝ≥0∞) *
            startExcessG witnessNear (H0.wbarOf (q - keygenCost)) b0n (q - keygenCost)) +
          coinSW (q - keygenCost) + ENNReal.ofReal (((q - keygenCost : ℕ) : ℝ) / 2 ^ 128 * Pb) +
          ((q - keygenCost + keygenCost + signatureLimit : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
        ((q - keygenCost + keygenCost : ℕ) : ℝ≥0∞) / 2 ^ 127 →
      forgeAdvantage adversary ≤ q / 2 ^ 127

end FORS.Security.SWRoute
