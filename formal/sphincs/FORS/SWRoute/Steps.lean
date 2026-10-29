import FORS.SWRoute.StepsBase

/-! **The SW route: one step.** For every input of the interpreted run, the budget at the route's
exponent times the weight, the payments of the step (the digest baseline `β`, the contact
coefficient `cU` of a FORS leaf query whose contact would survive) and the pending credit after the
step are at most the budget times the weight after the step, the pending credit before, the arming
cost `δ` and the kills of the step. The input classes are those of the small route: digest blocks,
FORS leaf queries, encodings, chain steps one and two below the word, other inputs, cached reads,
guesses, canonical continuations, reveals, draws and ticks. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost PotentialA GraphView ForsPotential

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-- **The setting of the route's steps**: the sample model parses exactly the active rows of the
graph, second-order inputs and digest blocks are untargeted, the digest predicate is the digest
blocks, and the prepared cache holds no FORS leaf query. -/
structure StepHyp (K : Ctx) (model : HiddenRows.Model HashInput HashOutput Address Coordinate) : Prop where
  parse : model.parse = HiddenGraph.parse K.p (candidateActive K.p)
  incoming : model.incoming = Address.inputCoordinate
  outgoing : model.outgoing = Address.outputCoordinate
  sec : ∀ x, SecondOrderInput K.p K.R x → K.tg.kind x = .none
  msg : ∀ x, ForsSigner.IsMsgInput x → K.tg.kind x = .none
  digest : K.tg.digest = ForsSigner.IsMsgInput
  fleaf : ∀ f : FIn, K.initial (f.input K.p) = none
  trunc : UniformTruncation (R := HashOutput) K.tg
  parsedFresh : ∀ x q, HiddenGraph.parse K.p (candidateActive K.p) x = some q → K.initial x = none

section Step

variable (K : Ctx) (root : Digest) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (ρ β δ cU : ℝ)

/-- **The step bound** of the S-part at one input, from `(probes, remaining)` to
`(probes', remaining - cost)`. -/
def StepBound (input : CostSpec.Domain) (s : St) (flag : Bool) (probes remaining probes' : ℕ) : Prop :=
  budgetE (expo K ρ flag s) probes remaining * weightA K root s +
      (ENNReal.ofReal (β / 2 ^ 128) * payF K root s input + ENNReal.ofReal (cU / 2 ^ 128) * payC K root s input) +
      ∑' r, Pr[= r | costStep model input s] * (weightA K root r.2 * pendA K r.2) ≤
    ∑' r, Pr[= r | costStep model input s] *
        (budgetE (expo K ρ (nextFlag K root flag s input) r.2) probes' (remaining - sourceCost input) *
          weightA K root r.2) +
      (weightA K root s * pendA K s + ENNReal.ofReal δ * payA K root flag s input +
        ∑' r, Pr[= r | costStep model input s] * payK K root s input r.2)

end Step

end FORS.Security.SWRoute
