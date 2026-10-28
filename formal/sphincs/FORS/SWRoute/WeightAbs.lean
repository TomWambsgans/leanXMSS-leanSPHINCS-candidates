import FORS.LargeBudget.WeightedPotential

/-! **An abstract survival weight.** The SW route weights its potentials by a weight `wt` of the
lazy-run state (the route's `weightA`: zero once a payoff event is decided, the survival weight
otherwise). Everything the weighted potentials need from it: it is at most one, its mean does not
grow through any step of the interpreted run, and storing a message-digest block leaves it alone.
This file restates, for such a weight, the facts of `LargeBudget/SurvivalWeight` and
`LargeBudget/WeightedScan` that the weighted potentials use: the supermartingale through a run,
presampling, the weighted payment accounts (a payment of the current weight per query of a class),
and the scan signer's bounds weighted by the final weight. -/

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

/-- **An abstract weight**: at most one, a supermartingale of every step of the lazy run, and kept
by every store at an input of the class `Dig` (the message-digest blocks). -/
structure WtSpec (wt : DebtState D R ι → ℝ≥0∞) (Dig : D → Prop) : Prop where
  le_one : ∀ s, wt s ≤ 1
  step : ∀ input s, ∑' r, Pr[= r | costStep model input s] * wt r.2 ≤ wt s
  store : ∀ s x u, Dig x → wt (s.store x u) = wt s

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

/-- Storing at a whole family of the class keeps the weight. -/
theorem wt_storeAll (hW : WtSpec model wt Dig) : ∀ {n : ℕ} (x : Fin n → D) (u : Fin n → R) (state : DebtState D R ι),
    (∀ i, Dig (x i)) → wt (storeAll x u state) = wt state
  | 0, _, _, _, _ => rfl
  | _ + 1, x, u, state, hk => by
      rw [storeAll_succ, wt_storeAll hW (Fin.tail x) (Fin.tail u) _ fun i => hk i.succ,
        hW.store state (x 0) (u 0) (hk 0)]

variable [Fintype R]

/-- Presampling one fresh untargeted input of the class, weighted. -/
theorem interp_presample_freshA (hW : WtSpec model wt Dig) (x : D) (hk : tg.kind x = .none) (hd : Dig x) {α : Type}
    (computation : OracleComp (SourceCostSpec D R ι) α) (budget : ℕ) (state : DebtState D R ι)
    (hx : state.cache x = none) (V : Run D ι α × DebtState D R ι → ℝ≥0∞)
    (hV : ∀ out (y : D) (v : R), out.2.cache y = none → V out ≤ V (out.1, out.2.store y v)) :
    ∑' out, Pr[= out | interp tg initial model computation budget state] * (wt out.2 * V out) ≤
      (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr[= out | interp tg initial model computation budget
        (state.store x v)] * (wt out.2 * V out) := by
  refine le_trans (interp_presample_le tg initial model x hk computation budget state
    (fun out => wt out.2 * V out) fun out s hs => ?_) ?_
  · cases hc : out.2.cache x with
    | some w =>
        rw [presample_cached x out.2 w hc, support_pure, Set.mem_singleton_iff] at hs
        rw [hs]
    | none =>
        rw [presample_fresh x out.2 hc, support_map] at hs
        obtain ⟨v, _, rfl⟩ := hs
        simp only
        rw [hW.store out.2 x v hd]
        exact mul_le_mul_right (hV out x v hc) _
  · rw [presample_fresh x state hx, tsum_probOutput_map_mul, tsum_uniform_eq]

/-- **Presampling an injective family of fresh untargeted inputs of the class**, weighted. -/
theorem interp_presampleAllA (hW : WtSpec model wt Dig) {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α)
    (budget : ℕ) (V : Run D ι α × DebtState D R ι → ℝ≥0∞)
    (hV : ∀ out (y : D) (v : R), out.2.cache y = none → V out ≤ V (out.1, out.2.store y v)) :
    ∀ {n : ℕ} (x : Fin n → D), Function.Injective x → (∀ i, tg.kind (x i) = .none) → (∀ i, Dig (x i)) →
      ∀ state : DebtState D R ι, (∀ i, state.cache (x i) = none) →
        ∑' out, Pr[= out | interp tg initial model computation budget state] * (wt out.2 * V out) ≤
          ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → R,
            ∑' out, Pr[= out | interp tg initial model computation budget (storeAll x u state)] *
              (wt out.2 * V out)
  | 0, x, _, _, _, state, _ => by
      simp only [pow_zero, inv_one, one_mul]
      rw [Fintype.sum_unique]
      rfl
  | n + 1, x, hx, hk, hd, state, hfresh => by
      have hxt : Function.Injective (Fin.tail x) := fun a b e => Fin.succ_injective _ (hx e)
      refine le_trans (interp_presample_freshA tg initial hW (x 0) (hk 0) (hd 0) computation budget state
        (hfresh 0) V hV) ?_
      have hrest : ∀ v, ∑' out, Pr[= out | interp tg initial model computation budget (state.store (x 0) v)] *
          (wt out.2 * V out) ≤
          ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ w : Fin n → R, ∑' out, Pr[= out | interp tg initial model
            computation budget (storeAll (Fin.tail x) w (state.store (x 0) v))] * (wt out.2 * V out) := fun v =>
        interp_presampleAllA hW computation budget V hV (Fin.tail x) hxt (fun i => hk i.succ)
          (fun i => hd i.succ) _ fun i => by
          show (state.store (x 0) v).cache (x i.succ) = none
          rw [store_cache_ne state (x 0) _ (fun e => Fin.succ_ne_zero i (hx e))]
          exact hfresh i.succ
      calc (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr[= out | interp tg initial model computation budget
              (state.store (x 0) v)] * (wt out.2 * V out)
          ≤ (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, (((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ w : Fin n → R,
              ∑' out, Pr[= out | interp tg initial model computation budget
                (storeAll (Fin.tail x) w (state.store (x 0) v))] * (wt out.2 * V out)) := by
            gcongr with v
            exact hrest v
        _ = ((Fintype.card R : ℝ≥0∞) ^ (n + 1))⁻¹ * ∑ v, ∑ w : Fin n → R,
              ∑' out, Pr[= out | interp tg initial model computation budget
                (storeAll x (Fin.cons v w) state)] * (wt out.2 * V out) := by
            rw [← Finset.mul_sum, ← mul_assoc, pow_succ', ENNReal.mul_inv (Or.inr (by simp))
              (Or.inl (ENNReal.natCast_ne_top _))]
            rfl
        _ = _ := by
            congr 1
            rw [← Fintype.sum_prod_type']
            exact Fintype.sum_equiv (Fin.consEquiv fun _ => R) _ _ fun p => rfl

/-- **A query of one input of a fresh family of the class**, weighted. -/
theorem interp_presample_newA (hW : WtSpec model wt Dig) {α : Type} {n : ℕ} (x : Fin n → D)
    (hx : Function.Injective x) (hk : ∀ i, tg.kind (x i) = .none) (hd : ∀ i, Dig (x i)) (c : Fin n)
    (next : R → OracleComp (SourceCostSpec D R ι) α)
    (budget : ℕ) (state : DebtState D R ι) (hfresh : ∀ i, state.cache (x i) = none)
    (V : Run D ι α × DebtState D R ι → ℝ≥0∞)
    (hV : ∀ out (y : D) (v : R), out.2.cache y = none → V out ≤ V (out.1, out.2.store y v)) :
    ∑' v, Pr[= v | ($ᵗ R : ProbComp R)] *
        ∑' out, Pr[= out | interp tg initial model (next v) budget (state.store (x c) v)] * (wt out.2 * V out) ≤
      ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → R,
        ∑' out, Pr[= out | interp tg initial model (next (u c)) budget (storeAll x u state)] *
          (wt out.2 * V out) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := c.isLt; omega⟩
  set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 c with hσ
  set x' : Fin (m + 1) → D := x ∘ σ with hx'
  have hx'inj : Function.Injective x' := hx.comp σ.injective
  have hx'0 : x' 0 = x c := by simp [hx', hσ]
  have hxt : Function.Injective (Fin.tail x') := fun a b e => Fin.succ_injective _ (hx'inj e)
  have hrest : ∀ v, ∑' out, Pr[= out | interp tg initial model (next v) budget (state.store (x c) v)] *
      (wt out.2 * V out) ≤
      ((Fintype.card R : ℝ≥0∞) ^ m)⁻¹ * ∑ w : Fin m → R, ∑' out, Pr[= out | interp tg initial model
        (next v) budget (storeAll x' (Fin.cons v w) state)] * (wt out.2 * V out) := by
    intro v
    rw [← hx'0]
    exact interp_presampleAllA tg initial hW (next v) budget V hV (Fin.tail x') hxt (fun i => hk _)
      (fun i => hd _) _ fun i => by
        show (state.store (x' 0) v).cache (x' i.succ) = none
        rw [store_cache_ne state (x' 0) _ (fun e => Fin.succ_ne_zero i (hx'inj e))]
        exact hfresh _
  rw [tsum_uniform_eq]
  calc (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, ∑' out, Pr[= out | interp tg initial model (next v) budget
          (state.store (x c) v)] * (wt out.2 * V out)
      ≤ (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, (((Fintype.card R : ℝ≥0∞) ^ m)⁻¹ * ∑ w : Fin m → R,
          ∑' out, Pr[= out | interp tg initial model (next v) budget
            (storeAll x' (Fin.cons v w) state)] * (wt out.2 * V out)) := by
        gcongr with v
        exact hrest v
    _ = ((Fintype.card R : ℝ≥0∞) ^ (m + 1))⁻¹ * ∑ u' : Fin (m + 1) → R,
          ∑' out, Pr[= out | interp tg initial model (next (u' 0)) budget (storeAll x' u' state)] *
            (wt out.2 * V out) := by
        rw [← Finset.mul_sum, ← mul_assoc, pow_succ', ENNReal.mul_inv (Or.inr (by simp))
          (Or.inl (ENNReal.natCast_ne_top _))]
        congr 1
        rw [← Fintype.sum_prod_type']
        exact Fintype.sum_equiv (Fin.consEquiv fun _ => R) _ _ fun p => rfl
    _ = _ := by
        congr 1
        refine Fintype.sum_equiv (σ.arrowCongr (Equiv.refl R)) _ _ fun u' => ?_
        have hu : (σ.arrowCongr (Equiv.refl R)) u' ∘ σ = u' := by
          funext i
          simp [Equiv.arrowCongr_apply, hσ, Equiv.swap_apply_self]
        conv_lhs => rw [← hu]
        rw [storeAll_perm x hx _ σ state]
        congr 3

end Generic

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
of the weight at the moment of the query. The digest account `WF` is `wcount … tg.digest`, the
FORS-leaf account `WC` is `wcount … (IsFleafIn parameter)`. -/
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

variable {model wt} {Dig : D → Prop}

/-- **Presampling an untargeted input of the class keeps the weighted account.** -/
theorem wcount_presample_eq (hW : WtSpec model wt Dig) (x : D) (hd : Dig x) {α : Type}
    (computation : OracleComp (SourceCostSpec D R ι) α) :
    ∀ (budget : ℕ) (state : DebtState D R ι),
      ∑' s, Pr[= s | presample x state] * wcount model wt Pay computation budget s =
        wcount model wt Pay computation budget state := by
  induction computation using OracleComp.inductionOn with
  | pure value =>
      intro budget state
      simp only [wcount_pure, mul_zero, tsum_zero]
  | query_bind input next ih =>
      intro budget state
      have hw : ∀ s ∈ support (presample x state), wt s = wt state := by
        intro s hs
        cases hc : state.cache x with
        | some v =>
            rw [presample_cached x state v hc, support_pure, Set.mem_singleton_iff] at hs
            rw [hs]
        | none =>
            rw [presample_fresh x state hc, support_map] at hs
            obtain ⟨v, _, rfl⟩ := hs
            exact hW.store state x v hd
      have hpay : ∀ s ∈ support (presample x state),
          wpaysA wt Pay s input = wpaysA wt Pay state input := by
        intro s hs
        have h := hw s hs
        rcases input with (draw | (bytes | coordinate)) | amount
        · rfl
        · simp only [wpaysA, h]
        · rfl
        · rfl
      simp only [wcount_query_bind]
      split_ifs with hcost
      · set K : (SourceCostSpec D R ι).Range input × DebtState D R ι → ℝ≥0∞ := fun r =>
          wpaysA wt Pay state input + wcount model wt Pay (next r.1) (budget - sourceCost input) r.2 with hK
        have hleft : ∑' s, Pr[= s | presample x state] *
            ∑' r, Pr[= r | costStep model input s] *
              (wpaysA wt Pay s input + wcount model wt Pay (next r.1) (budget - sourceCost input) r.2) =
            ∑' s, Pr[= s | presample x state] * ∑' r, Pr[= r | costStep model input s] * K r := by
          refine tsum_congr fun s => ?_
          by_cases hs : s ∈ support (presample x state)
          · rw [hpay s hs]
          · rw [probOutput_eq_zero_of_not_mem_support hs, zero_mul, zero_mul]
        have hcomm := presample_costStep model x input state (fun r => (pure r : ProbComp _))
        simp only [bind_pure] at hcomm
        rw [hleft, ← tsum_probOutput_bind_mul]
        calc ∑' r, Pr[= r | presample x state >>= fun s => costStep model input s] * K r
            = ∑' r, Pr[= r | costStep model input state >>= fun r =>
                presample x r.2 >>= fun s => (pure (r.1, s) : ProbComp _)] * K r :=
              tsum_congr fun r => congrArg (· * K r) (probOutput_congr rfl hcomm)
          _ = ∑' r, Pr[= r | costStep model input state] *
                ∑' s, Pr[= s | presample x r.2] * K (r.1, s) := by
              rw [tsum_probOutput_bind_mul]
              refine tsum_congr fun r => congrArg _ ?_
              rw [tsum_probOutput_bind_mul]
              exact tsum_congr fun s => by rw [tsum_probOutput_pure_mul]
          _ = ∑' r, Pr[= r | costStep model input state] * K r := by
              refine tsum_congr fun r => congrArg _ ?_
              simp only [hK]
              have hsplit : (∑' s, Pr[= s | presample x r.2] *
                    (wpaysA wt Pay state input + wcount model wt Pay (next r.1) (budget - sourceCost input) s)) =
                  (∑' s, Pr[= s | presample x r.2] * wpaysA wt Pay state input) +
                    ∑' s, Pr[= s | presample x r.2] *
                      wcount model wt Pay (next r.1) (budget - sourceCost input) s := by
                rw [← ENNReal.tsum_add]
                exact tsum_congr fun s => mul_add _ _ _
              rw [hsplit, ENNReal.tsum_mul_right, presample_mass, one_mul,
                ih r.1 (budget - sourceCost input) r.2]
      · simp only [mul_zero, tsum_zero]

variable [Fintype R]

theorem wcount_presample_fresh_eq (hW : WtSpec model wt Dig) (x : D) (hd : Dig x) {α : Type}
    (computation : OracleComp (SourceCostSpec D R ι) α) (budget : ℕ) (state : DebtState D R ι)
    (hx : state.cache x = none) :
    wcount model wt Pay computation budget state =
      (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, wcount model wt Pay computation budget (state.store x v) := by
  rw [← wcount_presample_eq Pay hW x hd computation budget state, presample_fresh x state hx,
    tsum_probOutput_map_mul, tsum_uniform_eq]

theorem wcount_presampleAll_eq (hW : WtSpec model wt Dig) {α : Type} (computation : OracleComp (SourceCostSpec D R ι) α)
    (budget : ℕ) :
    ∀ {n : ℕ} (x : Fin n → D), Function.Injective x → (∀ i, Dig (x i)) →
      ∀ state : DebtState D R ι, (∀ i, state.cache (x i) = none) →
        wcount model wt Pay computation budget state =
          ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → R,
            wcount model wt Pay computation budget (storeAll x u state)
  | 0, x, _, _, state, _ => by
      simp only [pow_zero, inv_one, one_mul]
      rw [Fintype.sum_unique]
      rfl
  | n + 1, x, hx, hd, state, hfresh => by
      have hxt : Function.Injective (Fin.tail x) := fun a b e => Fin.succ_injective _ (hx e)
      rw [wcount_presample_fresh_eq Pay hW (x 0) (hd 0) computation budget state (hfresh 0)]
      have hrest : ∀ v, wcount model wt Pay computation budget (state.store (x 0) v) =
          ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ w : Fin n → R,
            wcount model wt Pay computation budget (storeAll (Fin.tail x) w (state.store (x 0) v)) := fun v =>
        wcount_presampleAll_eq hW computation budget (Fin.tail x) hxt (fun i => hd i.succ) _ fun i => by
          show (state.store (x 0) v).cache (x i.succ) = none
          rw [store_cache_ne state (x 0) _ (fun e => Fin.succ_ne_zero i (hx e))]
          exact hfresh i.succ
      calc (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, wcount model wt Pay computation budget (state.store (x 0) v)
          = (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, (((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ w : Fin n → R,
              wcount model wt Pay computation budget (storeAll (Fin.tail x) w (state.store (x 0) v))) :=
            congrArg (fun A => (Fintype.card R : ℝ≥0∞)⁻¹ * A) (Finset.sum_congr rfl fun v _ => hrest v)
        _ = ((Fintype.card R : ℝ≥0∞) ^ (n + 1))⁻¹ * ∑ v, ∑ w : Fin n → R,
              wcount model wt Pay computation budget (storeAll x (Fin.cons v w) state) := by
            rw [← Finset.mul_sum, ← mul_assoc, pow_succ', ENNReal.mul_inv (Or.inr (by simp))
              (Or.inl (ENNReal.natCast_ne_top _))]
            rfl
        _ = _ := by
            congr 1
            rw [← Fintype.sum_prod_type']
            exact Fintype.sum_equiv (Fin.consEquiv fun _ => R) _ _ fun p => rfl

/-- **A query of one input of a fresh family of the class**, for the weighted account. -/
theorem wcount_presample_new_eq (hW : WtSpec model wt Dig) {α : Type} {n : ℕ} (x : Fin n → D)
    (hx : Function.Injective x) (hd : ∀ i, Dig (x i)) (c : Fin n)
    (next : R → OracleComp (SourceCostSpec D R ι) α)
    (budget : ℕ) (state : DebtState D R ι) (hfresh : ∀ i, state.cache (x i) = none) :
    ∑' v, Pr[= v | ($ᵗ R : ProbComp R)] * wcount model wt Pay (next v) budget (state.store (x c) v) =
      ((Fintype.card R : ℝ≥0∞) ^ n)⁻¹ * ∑ u : Fin n → R,
        wcount model wt Pay (next (u c)) budget (storeAll x u state) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := c.isLt; omega⟩
  set σ : Equiv.Perm (Fin (m + 1)) := Equiv.swap 0 c with hσ
  set x' : Fin (m + 1) → D := x ∘ σ with hx'
  have hx'inj : Function.Injective x' := hx.comp σ.injective
  have hx'0 : x' 0 = x c := by simp [hx', hσ]
  have hxt : Function.Injective (Fin.tail x') := fun a b e => Fin.succ_injective _ (hx'inj e)
  have hrest : ∀ v, wcount model wt Pay (next v) budget (state.store (x c) v) =
      ((Fintype.card R : ℝ≥0∞) ^ m)⁻¹ * ∑ w : Fin m → R,
        wcount model wt Pay (next v) budget (storeAll x' (Fin.cons v w) state) := by
    intro v
    rw [← hx'0]
    exact wcount_presampleAll_eq Pay hW (next v) budget (Fin.tail x') hxt (fun i => hd _) _
      fun i => by
        show (state.store (x' 0) v).cache (x' i.succ) = none
        rw [store_cache_ne state (x' 0) _ (fun e => Fin.succ_ne_zero i (hx'inj e))]
        exact hfresh _
  rw [tsum_uniform_eq]
  calc (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, wcount model wt Pay (next v) budget (state.store (x c) v)
      = (Fintype.card R : ℝ≥0∞)⁻¹ * ∑ v, (((Fintype.card R : ℝ≥0∞) ^ m)⁻¹ * ∑ w : Fin m → R,
          wcount model wt Pay (next v) budget (storeAll x' (Fin.cons v w) state)) :=
        congrArg (fun A => (Fintype.card R : ℝ≥0∞)⁻¹ * A) (Finset.sum_congr rfl fun v _ => hrest v)
    _ = ((Fintype.card R : ℝ≥0∞) ^ (m + 1))⁻¹ * ∑ u' : Fin (m + 1) → R,
          wcount model wt Pay (next (u' 0)) budget (storeAll x' u' state) := by
        rw [← Finset.mul_sum, ← mul_assoc, pow_succ', ENNReal.mul_inv (Or.inr (by simp))
          (Or.inl (ENNReal.natCast_ne_top _))]
        congr 1
        rw [← Fintype.sum_prod_type']
        exact Fintype.sum_equiv (Fin.consEquiv fun _ => R) _ _ fun p => rfl
    _ = _ := by
        congr 1
        refine Fintype.sum_equiv (σ.arrowCongr (Equiv.refl R)) _ _ fun u' => ?_
        have hu : (σ.arrowCongr (Equiv.refl R)) u' ∘ σ = u' := by
          funext i
          simp [Equiv.arrowCongr_apply, hσ, Equiv.swap_apply_self]
        have hc0 : ((σ.arrowCongr (Equiv.refl R)) u') c = u' 0 := by
          conv_rhs => rw [← hu]
          simp [hσ, Equiv.swap_apply_left]
        have hstore : storeAll x' u' state = storeAll x ((σ.arrowCongr (Equiv.refl R)) u') state := by
          conv_lhs => rw [hx', ← hu]
          exact storeAll_perm x hx _ σ state
        rw [hc0, hstore]

end Accounts

end FORS.Security.SWRoute
