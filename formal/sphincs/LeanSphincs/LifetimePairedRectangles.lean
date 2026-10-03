import LeanSphincs.LifetimePairedTrace
import LeanSphincs.LifetimeRectangles

/-! Rectangle concentration in the actual paired random-oracle transcript, with the exact
original source hash-query budget and no independence assumptions on adversarial choices. -/

namespace LeanSphincs.Lifetime
open OracleComp OracleSpec ENNReal Concrete Completeness Security Security.SeedCoupling
open Security.ExponentialCharge
attribute [local instance] Classical.propDecidable
variable [Params]

theorem paired_trace_rectangle_tail {α : Type} (sk : Seeded.SecretKey)
    (rectangle : DigestRectangle) (hsmall : SmallRectangle rectangle)
    (program : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hpaired : PairedCache sk cache)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hbound : ∀ result ∈ support ((simulateQ romImpl (countHashQueries program)).run' cache), result.2 ≤ q) :
    Pr[fun result => 2 ^ 56 ≤ traceHits (pairedWorldHit sk (InRectangle sk.parameter rectangle)) result.2.1 |
      traceRun (pairedRom sk) program cache] ≤ (1 : ℝ≥0∞) / 2 ^ 25002 := by
  have h := paired_trace_tail sk (InRectangle sk.parameter rectangle) 7 program cache hpaired q (2 ^ 56) hbound
  have hcap : Pr[fun result => 2 ^ 56 ≤
      traceHits (pairedWorldHit sk (InRectangle sk.parameter rectangle)) result.2.1 |
      traceRun (pairedRom sk) program cache] ≤
      (1 + 7 * ((1 : ℝ≥0∞) / 2 ^ 74)) ^ q / 8 ^ (2 ^ 56) := by
    refine h.trans ?_
    simp only [show (7 + 1 : Nat) = 8 from rfl, Nat.cast_ofNat]
    gcongr
    exact probEvent_inRectangle_le sk.parameter rectangle hsmall
  have hreal := ENNReal.ofReal_le_ofReal (rectangle_exponential_bound q hq)
  simp only [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 8 ^ (2 ^ 56)),
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ 25002),
    ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 1 + 7 * (1 / 2 ^ 74)),
    ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ 7 * (1 / 2 ^ 74)),
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 7),
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ 74),
    ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 8),
    ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2), ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at hreal
  exact hcap.trans hreal

/-- Uniformly over every small rectangle, arbitrary adaptive private-sampling programs
with at mostq original hash calls have fewer than2^56 latent candidates in it, except2^-400. -/
theorem paired_trace_rectangles_negligible {α : Type} (sk : Seeded.SecretKey)
    (program : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hpaired : PairedCache sk cache)
    (q : Nat) (hq : q ≤ 2 ^ 127)
    (hbound : ∀ result ∈ support ((simulateQ romImpl (countHashQueries program)).run' cache), result.2 ≤ q) :
    Pr[fun result => ∃ rectangle, SmallRectangle rectangle ∧
      2 ^ 56 ≤ traceHits (pairedWorldHit sk (InRectangle sk.parameter rectangle)) result.2.1 |
      traceRun (pairedRom sk) program cache] ≤ (1 : ℝ≥0∞) / 2 ^ 400 := by
  apply rectangle_union_bound
  intro rectangle hsmall
  exact paired_trace_rectangle_tail sk rectangle hsmall program cache hpaired q hq hbound

end LeanSphincs.Lifetime
