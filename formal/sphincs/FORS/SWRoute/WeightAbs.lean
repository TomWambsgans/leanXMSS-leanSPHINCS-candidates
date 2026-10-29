import FORS.LargeBudget.WeightedPotential

/-! **An abstract survival weight.** The SW route weights its potentials by a weight `wt` of the
lazy-run state (the route's `weightA`: zero once a payoff event is decided, the survival weight
otherwise). Everything the weighted potentials need from it: it is at most one, its mean does not
grow through any step of the interpreted run, and storing a message-digest block does not raise it.
This file restates, for such a weight, the facts of `LargeBudget/SurvivalWeight` that the weighted
potentials use: the supermartingale through a run and the weighted payment accounts (a payment of
the current weight per query of a class). With one digest call per pair (`digestCalls = 1`) a new
pair is read whole by its query, so no presampling is needed (`presample_one`). -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open HiddenCost HiddenBridge HiddenOutside HiddenReveal HiddenDebt

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

section Generic

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
attribute [local instance] saturationDecEqCoordinate
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

/-- **An abstract weight**: at most one, a supermartingale of every step of the lazy run, and not
raised by a store at an input of the class `Dig` (the message-digest blocks). -/
structure WtSpec (wt : DebtState D R ι → ℝ≥0∞) (Dig : D → Prop) : Prop where
  le_one : ∀ s, wt s ≤ 1
  step : ∀ input s, ∑' r, Pr[= r | costStep model input s] * wt r.2 ≤ wt s
  store_le : ∀ s x u, Dig x → s.cache x = none → wt (s.store x u) ≤ wt s

variable {model} {wt : DebtState D R ι → ℝ≥0∞} {Dig : D → Prop}

/-- **Supermartingale.** The expected final weight of an interpreted run is at most the initial
weight. -/
theorem interp_wt_le (hW : WtSpec model wt Dig) {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    ∀ budget (state : DebtState D R ι),
      ∑' out, Pr[= out | interp tg initial model computation budget state] * wt out.2 ≤ wt state := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state
      rw [interp_pure, tsum_probOutput_pure_mul]
  | query_bind input next ih =>
      intro budget state
      rw [interp_query_bind]
      split_ifs with hcost
      · rw [tsum_probOutput_bind_mul]
        simp only [tsum_probOutput_map_mul]
        calc _ ≤ ∑' r, Pr[= r | costStep model input state] * wt r.2 :=
              ENNReal.tsum_le_tsum fun r => mul_le_mul_right (ih r.1 _ r.2) _
          _ ≤ _ := hW.step input state
      · rw [tsum_probOutput_pure_mul]

/-- A pointwise bound on the support turns into the bound times the initial weight. -/
theorem interp_wt_mul_le (hW : WtSpec model wt Dig) {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α)
    (budget : ℕ) (state : DebtState D R ι) (G : Run D ι α × DebtState D R ι → ℝ≥0∞) (K : ℝ≥0∞)
    (hG : ∀ out ∈ support (interp tg initial model computation budget state), G out ≤ K) :
    ∑' out, Pr[= out | interp tg initial model computation budget state] * (wt out.2 * G out) ≤
      wt state * K := by
  calc _ ≤ ∑' out, Pr[= out | interp tg initial model computation budget state] * (wt out.2 * K) := by
        refine ENNReal.tsum_le_tsum fun out => ?_
        by_cases hout : out ∈ support (interp tg initial model computation budget state)
        · exact mul_le_mul_right (mul_le_mul_right (hG out hout) _) _
        · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
    _ = (∑' out, Pr[= out | interp tg initial model computation budget state] * wt out.2) * K := by
        rw [← ENNReal.tsum_mul_right]
        exact tsum_congr fun out => by ring
    _ ≤ _ := mul_le_mul_left (interp_wt_le tg initial hW computation budget state) _

/-- The weighted mass of a constant. -/
theorem interp_wt_const (hW : WtSpec model wt Dig) {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α)
    (budget : ℕ) (state : DebtState D R ι) (c : ℝ≥0∞) :
    ∑' out, Pr[= out | interp tg initial model computation budget state] * (wt out.2 * c) ≤ wt state * c :=
  interp_wt_mul_le tg initial hW computation budget state (fun _ => c) c fun _ _ => le_rfl

/-- Storing fresh answers at a whole injective family of the class does not raise the weight. -/
theorem wt_storeAll_le (hW : WtSpec model wt Dig) : ∀ {n : ℕ} (x : Fin n → D) (u : Fin n → R)
    (state : DebtState D R ι), Function.Injective x → (∀ i, Dig (x i)) → (∀ i, state.cache (x i) = none) →
      wt (storeAll x u state) ≤ wt state
  | 0, _, _, _, _, _, _ => le_rfl
  | _ + 1, x, u, state, hx, hk, hc => by
      rw [storeAll_succ]
      refine (wt_storeAll_le hW (Fin.tail x) (Fin.tail u) _ (fun a b e => Fin.succ_injective _ (hx e))
        (fun i => hk i.succ) fun i => ?_).trans (hW.store_le state (x 0) (u 0) (hk 0) (hc 0))
      show (state.store (x 0) (u 0)).cache (x i.succ) = none
      rw [store_cache_ne state (x 0) _ (fun e => Fin.succ_ne_zero i (hx e))]
      exact hc i.succ

end Generic

/-! ### One input per family: the query reads the whole family -/

section One

variable {D R ι : Type} [Fintype ι] [SampleableType R] [Fintype R]

/-- **A family of one input is read by its query.** A uniform answer at the input, followed by any
function of the answer and the state, is the average over the answers of the whole family. -/
theorem presample_one {n : ℕ} (hn : n = 1) (x : Fin n → D) (c : Fin n) (state : DebtState D R ι)
    (F : R → DebtState D R ι → ℝ≥0∞) :
    ∑' v, Pr[= v | ($ᵗ R : ProbComp R)] * F v (state.store (x c) v) =
      ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → R, F (u c) (storeAll x u state) := by
  subst hn
  have hc : c = 0 := Subsingleton.elim _ _
  subst hc
  rw [tsum_uniform_eq, pow_one]
  congr 1
  refine Fintype.sum_equiv (Equiv.funUnique (Fin 1) R).symm _ _ fun v => ?_
  rfl

end One

/-! ### Weighted payment accounts -/

section Accounts

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
attribute [local instance] saturationDecEqCoordinate
variable (model : HiddenRows.Model D R A ι) (wt : DebtState D R ι → ℝ≥0∞) (Pay : D → Prop)

/-- An ordinary query of the class `Pay` pays the current weight. -/
noncomputable def wpaysA (state : DebtState D R ι) : (SourceCostSpec D R ι).Domain → ℝ≥0∞
  | .inl (.inr (.inl bytes)) => if Pay bytes then wt state else 0
  | _ => 0

/-- **The weighted account of a class**: the expected sum, over the ordinary queries of the class,
of the weight at the moment of the query (before it). The digest account `WF` is
`wcount … tg.digest`, the FORS-leaf account `WC` is `wcount … (IsFleafIn parameter)`. -/
noncomputable def wcount {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α) :
    ℕ → DebtState D R ι → ℝ≥0∞ :=
  OracleComp.construct (C := fun _ => ℕ → DebtState D R ι → ℝ≥0∞) (fun _ _ _ => 0)
    (fun input _ next budget state =>
      if sourceCost input ≤ budget then
        ∑' result, Pr[= result | costStep model input state] *
          (wpaysA wt Pay state input + next result.1 (budget - sourceCost input) result.2)
      else 0) computation

theorem wcount_pure {α : Type} (value : α) (budget : ℕ) (state : DebtState D R ι) :
    wcount model wt Pay (pure value : OracleComp (SourceCostSpec D R ι) α) budget state = 0 := rfl

theorem wcount_query_bind {α : Type} (input : (SourceCostSpec D R ι).Domain)
    (next : (SourceCostSpec D R ι).Range input → OracleComp (SourceCostSpec D R ι) α)
    (budget : ℕ) (state : DebtState D R ι) :
    wcount model wt Pay (liftM ((SourceCostSpec D R ι).query input) >>= next) budget state =
      if sourceCost input ≤ budget then
        ∑' result, Pr[= result | costStep model input state] *
          (wpaysA wt Pay state input + wcount model wt Pay (next result.1) (budget - sourceCost input) result.2)
      else 0 := rfl

variable (tg : Targeting D R ι) (initial : Cache D R)

/-- The account of a sequential run splits at the end of the first computation. -/
theorem wcount_bind {α β : Type} (first : OracleComp (SourceCostSpec D R ι) α)
    (next : α → OracleComp (SourceCostSpec D R ι) β) :
    ∀ budget (state : DebtState D R ι),
      wcount model wt Pay (first >>= next) budget state =
        wcount model wt Pay first budget state +
          ∑' o1, Pr[= o1 | interp tg initial model first budget state] *
            o1.1.1.elim 0 (fun value => wcount model wt Pay (next value) (budget - traceCost o1.1.2.2.1) o1.2) := by
  induction first using OracleComp.inductionOn with
  | pure value =>
      intro budget state
      rw [pure_bind, wcount_pure, interp_pure, tsum_probOutput_pure_mul, zero_add]
      simp only [Option.elim, traceCost, List.map_nil, List.sum_nil, Nat.sub_zero]
  | query_bind input rest ih =>
      intro budget state
      rw [bind_assoc, wcount_query_bind, wcount_query_bind, interp_query_bind]
      split_ifs with hcost
      · rw [tsum_probOutput_bind_mul, ← ENNReal.tsum_add]
        refine tsum_congr fun r => ?_
        rw [tsum_probOutput_map_mul, ih r.1 (budget - sourceCost input) r.2]
        simp only [traceCost_append, recorded_cost, Nat.sub_sub]
        ring
      · rw [tsum_probOutput_pure_mul]
        simp

end Accounts

end FORS.Security.SWRoute
