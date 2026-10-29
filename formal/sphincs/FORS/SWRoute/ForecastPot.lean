import FORS.SWRoute.ContactAcct
import FORS.SWRoute.ForecastCert
import FORS.SWRoute.ForecastCells

/-! **The tail potential of the own-cell near forecast** (WP-F, toward `xs_bound`). On the ghost
states of the excess account `XS` (state `s`, cached landed pairs `P`, touched messages `Ms`, signing
log `L`, disclosed views `d`, budget `k`; `n = N - |L|` signatures left) the potential
`psi = psiL + psiC + psiP` has three parts, for tail parameters `tp` (the witnesses of
`ForecastTail`: cap `n0`, rate `μ`, Chernoff parameters `θ_D`, the cap `m`, the budget `q`):

* `psiL`: the one-coin forecast of the light failure `lightFail (n0 - 1)` (an index with at least
  `n0` disclosed views);
* `psiC`: for every cell `c`, every `D < n0` and every set `Q` of `D` views at `c`'s index, the
  Chernoff factor `e^{-θ_D t_D}` (`t_D = m - fresh_D - coinSlack`), the product of the pair factors
  `e^{θ_D wQφ}` of the unsigned cached pairs (weights `φ(r) = phiK a μ r` at `r ≥ 1` missing trees),
  `Γ_D^k` for the future pairs, and the forecast of `1[Q ⊆ disclosed]`;
* `psiP`: the multi-leaf pattern counts: for every index and every nonempty pattern `S` (a leaf in
  some trees), `2^{-T_S}` times `2` per unsigned cached pair selecting `S` times `(1 + 2^-(b + a|S|))^k`.

Planned theorems: `excPay_le_psi` (at a surviving FORS leaf query the excess payment is at most
`(1 - m)⁺ psi`), the step lemmas (`psi` is a supermartingale through new pairs, other queries and
signing calls), `psi_start_le` (`psi` at the start is at most `tailSum`), and `xs_bound`. -/

open OracleComp OracleSpec ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.LoopWalk ForsPotential PotentialA

set_option linter.unusedSectionVars false

/-! ### Weights with a general per-pair weight function -/

/-- The weight of a view at a cell relative to `Q` with per-pair weights `φ`. -/
noncomputable def wQφ (c : FCell) (Q : Finset View) (φ : ℕ → ℝ) (u : View) : ℝ :=
  if Opens c u ∧ u ∉ Q ∧ 1 ≤ missing c Q u then φ (missing c Q u) else 0

/-- The exponential pair factor `e^{θ wQφ}`. -/
noncomputable def pairFφ (c : FCell) (Q : Finset View) (θ : ℝ) (φ : ℕ → ℝ) (u : View) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (θ * wQφ c Q φ u))

/-! ### Ghost-state notions -/

/-- The views disclosed at index `I`. -/
noncomputable def discAt (d : Multiset View) (I : Fin (2 ^ subtreeHeight)) : Finset View :=
  d.toFinset.filter fun v => v.1 = I

/-- The local cell of a FORS leaf query. -/
def cellOfF (f : FIn) : FCell := (localIdx f.index, f.κ, f.leaf)

/-- The disclosure indicator of a finite set of views. -/
noncomputable def inDisc (Q : Finset View) (D : Multiset View) : ℝ≥0∞ :=
  haveI := Classical.propDecidable (Q ⊆ D.toFinset)
  if Q ⊆ D.toFinset then 1 else 0

/-- A pattern: a leaf in some trees. -/
abbrev Pat := FTree → Option FLeaf

/-- The number of trees of a pattern. -/
noncomputable def patSize (S : Pat) : ℕ := (Finset.univ.filter fun κ => (S κ).isSome).card

/-- A view at index `I` selects every leaf of the pattern. -/
def PatCovers (I : Fin (2 ^ subtreeHeight)) (S : Pat) (u : View) : Prop :=
  u.1 = I ∧ ∀ κ l, S κ = some l → u.2 κ = l

/-- **The pattern cap** (`capFloor` is in `ForecastTail.lean`; `patCap q s = patCapN b a capFloor q s`) at budget `q` and size `s`: `max(6 q / 2^(b + a s) + 1, capFloor)`. -/
def patCap (q s : ℕ) : ℕ := max (6 * q / 2 ^ (subtreeHeight + forsHeight * s) + 1) capFloor

/-- The tail parameters (the witnesses of `ForecastTail`). -/
structure TailPar where
  n0 : ℕ
  μ : ℝ≥0
  θ : ℕ → ℝ
  m : ℝ
  q : ℕ

/-- `t_D = m - fresh_D - coinSlack`. -/
noncomputable def TailPar.thr (tp : TailPar) (D : ℕ) : ℝ :=
  tp.m - freshK subtreeHeight forsTrees forsHeight (tp.μ : ℝ) tp.q D - coinSlack

/-- The per-pair weights `φ(r) = T_r(μ) / 2^(a r)`. -/
noncomputable def TailPar.φ (tp : TailPar) : ℕ → ℝ := phiK forsHeight (tp.μ : ℝ)

/-! ### The potential -/

section Defs

variable (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (tp : TailPar)

/-- **The light part**: the forecast of an index with at least `n0` disclosed views. -/
noncomputable def psiL (s : State) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ) :
    ℝ≥0∞ :=
  termO parameter data wbar s Ms L (fun _ => False) (lightFail (tp.n0 - 1)) d (signatureLimit - L.length) k

/-- The product of a factor over the unsigned pairs of a list. -/
noncomputable def prodU (L : QueryLog SigningSpec) (P : List Pair) (g : Pair → ℝ≥0∞) : ℝ≥0∞ :=
  haveI := Classical.decPred (Unsigned L)
  ((P.filter fun p => decide (Unsigned L p)).map g).prod

/-- **The cell part.** -/
noncomputable def psiC (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (k : ℕ) : ℝ≥0∞ :=
  ∑ c : FCell, ∑ D ∈ Finset.range tp.n0, ∑ Q ∈ subsetsAt c.1 D,
    ENNReal.ofReal (Real.exp (-(tp.θ D * tp.thr D))) *
      prodU L P (fun p => pairFφ c Q (tp.θ D) tp.φ (pview parameter data s p)) *
      ENNReal.ofReal (gammaR subtreeHeight forsTrees forsHeight (tp.θ D) tp.φ D) ^ k *
      termO parameter data wbar s Ms L (fun _ => False) (inDisc Q) d (signatureLimit - L.length) k

/-- **The pattern part** (no disclosures involved). -/
noncomputable def psiP (s : State) (P : List Pair) (L : QueryLog SigningSpec) (k : ℕ) : ℝ≥0∞ :=
  haveI := Classical.propDecidable
  ∑ I : Fin (2 ^ subtreeHeight), ∑ S ∈ (Finset.univ : Finset Pat).filter (fun S => 1 ≤ patSize S),
    (2 : ℝ≥0∞)⁻¹ ^ patCap tp.q (patSize S) *
      prodU L P (fun p => if PatCovers I S (pview parameter data s p) then 2 else 1) *
      (1 + ((2 : ℝ≥0∞) ^ (subtreeHeight + forsHeight * patSize S))⁻¹) ^ k

/-- **The tail potential.** -/
noncomputable def psi (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (k : ℕ) : ℝ≥0∞ :=
  psiL parameter data wbar tp s Ms L d k + psiC parameter data wbar tp s P Ms L d k + psiP parameter data tp s P L k

end Defs

end FORS.Security.SWRoute
