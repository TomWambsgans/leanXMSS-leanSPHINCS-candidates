import FORS.SWRoute.ForecastPot

/-! **The start value of the tail potential** (WP-F-B, toward `xs_bound`). At a ghost state with no
cached pairs, no touched messages, no signatures and no disclosures, every one-coin forecast is the
H-term of its base (`termO_nilB`), so

* the light part is at most `2^b E_μ[(n - (n0 - 1))⁺]` (`psiL_start_le`, through the convex majorant
  `(n - (n0 - 1))⁺` of the light failure);
* the cell part is at most `Σ_{D < n0} k 2^a 2^b (μ^D / D!) e^{-θ_D t_D} Γ_D^q` (`psiC_start_le`: the
  `D`-subsets of the views disclosed at an index number at most `C(count, D)`, whose Poisson mean is
  `μ^D / D!`);
* the pattern part is at most `2^-101` (`psiP_start_le`: `(1 + 1/M)^q ≤ 4^(q/M + 1)` against the cap
  `2^-T`, `T ≥ 6 q / M + 1` and `T ≥ capFloor`, and at most `2^b 2^((a+1)k)` index-pattern pairs);

hence `psi ≤ tailSum` at the start (`psi_start_le`), for every rate `μ` above the one-coin rate. -/

open OracleComp OracleSpec ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.LoopWalk ForsPotential PotentialA
open FORS.Security FORS.Security.H0 FORS.Security.H0Avg FORS.Base.H0

set_option linter.unusedSectionVars false

/-! ### The H-term operator: linearity and monotonicity -/

theorem hTermO_mono_baseB {w lam : ℝ≥0∞} {N q : ℕ} {f g : Multiset View → ℝ≥0∞} (h : ∀ D, f D ≤ g D) :
    hTermO (Finset.univ : Finset View) w lam N q f ≤ hTermO (Finset.univ : Finset View) w lam N q g := by
  unfold hTermO
  exact creations_mono (fun I => virtualOnce_mono_base h N I 0) q []

theorem hTermO_const_mulB (w lam : ℝ≥0∞) (N q : ℕ) (c : ℝ≥0∞) (f : Multiset View → ℝ≥0∞) :
    hTermO (Finset.univ : Finset View) w lam N q (fun D => c * f D) =
      c * hTermO (Finset.univ : Finset View) w lam N q f := by
  unfold hTermO
  simp only [virtualOnce_const_mul]
  exact creations_const_mul c _ q []

theorem virtualOnce_finset_sumB {κ : Type} [DecidableEq κ] (w : ℝ≥0∞) (S : Finset κ)
    (f : κ → Multiset View → ℝ≥0∞) (N : ℕ) (I : List View) (d : Multiset View) :
    virtualOnce (Finset.univ : Finset View) w (fun D => ∑ i ∈ S, f i D) N I d =
      ∑ i ∈ S, virtualOnce (Finset.univ : Finset View) w (f i) N I d := by
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      have h := virtualOnce_const_mul (U := (Finset.univ : Finset View)) (w := w) 0 (fun _ => (1 : ℝ≥0∞)) N I d
      simpa using h
  | insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      rw [virtualOnce_add Finset.univ_nonempty (f a) (fun D => ∑ i ∈ S, f i D), ih]

theorem hTermO_finset_sumB {κ : Type} [DecidableEq κ] (w lam : ℝ≥0∞) (N q : ℕ) (S : Finset κ)
    (f : κ → Multiset View → ℝ≥0∞) :
    hTermO (Finset.univ : Finset View) w lam N q (fun D => ∑ i ∈ S, f i D) =
      ∑ i ∈ S, hTermO (Finset.univ : Finset View) w lam N q (f i) := by
  unfold hTermO
  simp only [virtualOnce_finset_sumB]
  exact creations_finset_sum S _ q []

/-- **No touched message, no disclosure: the forecast is the H-term.** -/
theorem termO_nilB (parameter : PublicParameter) (data : PublicData) (w : ℝ≥0∞) (s : State)
    (L : QueryLog SigningSpec) (excl : Pair → Prop) (f : Multiset View → ℝ≥0∞) (n k : ℕ) :
    termO parameter data w s [] L excl f 0 n k = hTermO (Finset.univ : Finset View) w landing n k f := rfl

/-! ### The rate -/

/-- **The H-term of a per-index base at a rate above the one-coin rate.** -/
theorem hTermO_perIndex_rate (g gbar : ℕ → ℝ≥0∞) (hgG : SepGood gbar) (hg : ∀ n, g n ≤ gbar n)
    (w : ℝ≥0∞) (hw1 : w ≤ 1) (q : ℕ) (μ : ℝ≥0)
    (hrate : (signatureLimit : ℝ) / 2 ^ subtreeHeight + (q : ℝ) * (landing * w).toReal / 2 ^ subtreeHeight ≤ μ) :
    hTermO (Finset.univ : Finset View) w landing signatureLimit q (perIndex g) ≤
      (2 : ℝ≥0∞) ^ subtreeHeight * poisMean μ gbar := by
  set b := subtreeHeight with hbdef
  have hlw : landing * w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (mul_le_one' ForsPrice.landing_le_one hw1)
  have hcard : Fintype.card (Fin (2 ^ subtreeHeight)) = 2 ^ b := by rw [Fintype.card_fin]
  set α : ℝ≥0 := ((2 : ℝ≥0) ^ b)⁻¹ with hαdef
  set γ : ℝ≥0 := (landing * w).toNNReal / (2 : ℝ≥0) ^ b with hγdef
  have h2b0 : ((2 : ℝ≥0) ^ b) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hL : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ b := by rw [hcard]; push_cast; rfl
  have hα : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * α = 1 := by
    rw [hL, hαdef, ENNReal.coe_inv h2b0]
    push_cast
    exact ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hγ : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * γ = landing * w := by
    rw [hL, hγdef, ENNReal.coe_div h2b0, ENNReal.coe_toNNReal hlw]
    push_cast
    exact ENNReal.mul_div_cancel (pow_ne_zero _ two_ne_zero) (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
  have hμ : (signatureLimit : ℝ≥0) * α + (q : ℝ≥0) * γ ≤ μ := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [hγdef, hαdef]
    push_cast
    calc (signatureLimit : ℝ) * ((2 : ℝ) ^ b)⁻¹ + (q : ℝ) * ((landing * w).toReal / 2 ^ b)
        = (signatureLimit : ℝ) / 2 ^ b + (q : ℝ) * (landing * w).toReal / 2 ^ b := by ring
      _ ≤ _ := hrate
  have h := hTermO_perIndex_le g gbar hgG hg w landing hw1 ForsPrice.landing_le_one signatureLimit q α γ hα hγ μ hμ
  rwa [hL] at h

/-! ### The light part -/

theorem tsub_sepGoodB (c : ℕ) : SepGood (fun n => ((n - c : ℕ) : ℝ≥0∞)) where
  mono := fun a b hab => by
    show ((a - c : ℕ) : ℝ≥0∞) ≤ ((b - c : ℕ) : ℝ≥0∞)
    exact_mod_cast Nat.sub_le_sub_right hab c
  convex := by
    intro n
    show ((n + 1 - c : ℕ) : ℝ≥0∞) + ((n + 1 - c : ℕ) : ℝ≥0∞) ≤ ((n + 2 - c : ℕ) : ℝ≥0∞) + ((n - c : ℕ) : ℝ≥0∞)
    have h : (n + 1 - c) + (n + 1 - c) ≤ (n + 2 - c) + (n - c) := by omega
    exact_mod_cast h
  growth := ⟨1, fun n => by
    simp only [ENNReal.coe_one, one_mul]
    have h : n - c ≤ 2 ^ n := le_trans (Nat.sub_le n c) (Nat.lt_two_pow_self).le
    exact_mod_cast h⟩

theorem lightFail_le_tsub (nstar n : ℕ) : (if nstar < n then (1 : ℝ≥0∞) else 0) ≤ ((n - nstar : ℕ) : ℝ≥0∞) := by
  split_ifs with h
  · exact_mod_cast (show 1 ≤ n - nstar by omega)
  · exact zero_le

/-- **The light part at the start.** -/
theorem psiL_start_le (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (hw1 : wbar ≤ 1)
    (tp : TailPar) (s : State)
    (hrate : (signatureLimit : ℝ) / 2 ^ subtreeHeight + (tp.q : ℝ) * (landing * wbar).toReal / 2 ^ subtreeHeight
      ≤ tp.μ) :
    psiL parameter data wbar tp s [] [] 0 tp.q ≤
      (2 : ℝ≥0∞) ^ subtreeHeight * poisMean tp.μ (fun n => ((n - (tp.n0 - 1) : ℕ) : ℝ≥0∞)) := by
  unfold psiL
  rw [List.length_nil, Nat.sub_zero, termO_nilB]
  exact hTermO_perIndex_rate _ _ (tsub_sepGoodB (tp.n0 - 1)) (lightFail_le_tsub (tp.n0 - 1)) wbar hw1 tp.q tp.μ hrate

/-! ### The cell part -/

theorem prodU_nilB (L : QueryLog SigningSpec) (g : Pair → ℝ≥0∞) : prodU L [] g = 1 := by
  unfold prodU
  simp

theorem sum_cell_eqB (F : Fin (2 ^ subtreeHeight) → ℝ≥0∞) :
    ∑ c : FCell, F c.1 = (forsTrees : ℝ≥0∞) * 2 ^ forsHeight * ∑ I, F I := by
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Fintype.card_fin]
  push_cast
  ring

/-- Pointwise: the cell indicators of all `D`-sets sum to at most `k 2^a` binomial counts. -/
theorem sum_cells_inDisc_le (D : ℕ) (d : Multiset View) :
    ∑ c : FCell, ∑ Q ∈ subsetsAt c.1 D, inDisc Q d ≤
      (forsTrees : ℝ≥0∞) * 2 ^ forsHeight * perIndex (fun n => ((n.choose D : ℕ) : ℝ≥0∞)) d := by
  rw [sum_cell_eqB (fun I => ∑ Q ∈ subsetsAt I D, inDisc Q d)]
  refine mul_le_mul_right (Finset.sum_le_sum fun I _ => ?_) _
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun Q _ => ?_)) (sum_subsets_le d I D)
  unfold inDisc
  split_ifs <;> rfl

/-- The cell-forecasts of all cells and all `D`-sets at the start. -/
theorem sum_cells_hTerm_le (wbar : ℝ≥0∞) (hw1 : wbar ≤ 1) (q D : ℕ) (μ : ℝ≥0)
    (hrate : (signatureLimit : ℝ) / 2 ^ subtreeHeight + (q : ℝ) * (landing * wbar).toReal / 2 ^ subtreeHeight ≤ μ) :
    ∑ c : FCell, ∑ Q ∈ subsetsAt c.1 D,
        hTermO (Finset.univ : Finset View) wbar landing signatureLimit q (inDisc Q) ≤
      (forsTrees : ℝ≥0∞) * 2 ^ forsHeight * 2 ^ subtreeHeight * ENNReal.ofReal ((μ : ℝ) ^ D / D.factorial) := by
  have hsum : ∑ c : FCell, ∑ Q ∈ subsetsAt c.1 D,
        hTermO (Finset.univ : Finset View) wbar landing signatureLimit q (inDisc Q) =
      hTermO (Finset.univ : Finset View) wbar landing signatureLimit q
        (fun d => ∑ c : FCell, ∑ Q ∈ subsetsAt c.1 D, inDisc Q d) := by
    rw [hTermO_finset_sumB]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hTermO_finset_sumB]
  rw [hsum]
  refine le_trans (hTermO_mono_baseB (sum_cells_inDisc_le D)) ?_
  rw [hTermO_const_mulB, mul_assoc ((forsTrees : ℝ≥0∞) * 2 ^ forsHeight)]
  refine mul_le_mul_right ?_ _
  refine le_trans (hTermO_perIndex_rate _ _ (choose_sepGood D) (fun _ => le_rfl) wbar hw1 q μ hrate) ?_
  rw [poisMean_choose]

/-- **The cell part at the start.** -/
theorem psiC_start_le (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (hw1 : wbar ≤ 1)
    (tp : TailPar) (s : State)
    (hrate : (signatureLimit : ℝ) / 2 ^ subtreeHeight + (tp.q : ℝ) * (landing * wbar).toReal / 2 ^ subtreeHeight
      ≤ tp.μ) :
    psiC parameter data wbar tp s [] [] [] 0 tp.q ≤
      ∑ D ∈ Finset.range tp.n0, (forsTrees : ℝ≥0∞) * 2 ^ forsHeight * 2 ^ subtreeHeight *
        ENNReal.ofReal ((tp.μ : ℝ) ^ D / D.factorial) *
        ENNReal.ofReal (Real.exp (-(tp.θ D * (tp.m - freshK subtreeHeight forsTrees forsHeight (tp.μ : ℝ) tp.q D -
          coinSlack)))) *
        ENNReal.ofReal (gammaR subtreeHeight forsTrees forsHeight (tp.θ D) (phiK forsHeight (tp.μ : ℝ)) D) ^ tp.q := by
  unfold psiC
  simp only [prodU_nilB, mul_one, List.length_nil, Nat.sub_zero, termO_nilB]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun D _ => ?_
  set E := ENNReal.ofReal (Real.exp (-(tp.θ D * tp.thr D)))
  set G := ENNReal.ofReal (gammaR subtreeHeight forsTrees forsHeight (tp.θ D) tp.φ D) ^ tp.q
  have h1 : ∑ c : FCell, ∑ Q ∈ subsetsAt c.1 D,
        E * G * hTermO (Finset.univ : Finset View) wbar landing signatureLimit tp.q (inDisc Q) =
      E * G * ∑ c : FCell, ∑ Q ∈ subsetsAt c.1 D,
        hTermO (Finset.univ : Finset View) wbar landing signatureLimit tp.q (inDisc Q) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
  rw [h1]
  calc E * G * ∑ c : FCell, ∑ Q ∈ subsetsAt c.1 D,
        hTermO (Finset.univ : Finset View) wbar landing signatureLimit tp.q (inDisc Q)
      ≤ E * G * ((forsTrees : ℝ≥0∞) * 2 ^ forsHeight * 2 ^ subtreeHeight *
          ENNReal.ofReal ((tp.μ : ℝ) ^ D / D.factorial)) :=
        mul_le_mul_right (sum_cells_hTerm_le wbar hw1 tp.q D tp.μ hrate) _
    _ = _ := by
        simp only [E, G, TailPar.thr, TailPar.φ]
        ring

/-! ### The pattern part -/

/-- `(1 + 1/M)^q ≤ 4^(q/M + 1)` for `M = 2^e`. -/
theorem one_add_inv_pow_le (e q : ℕ) :
    (1 + ((2 : ℝ≥0∞) ^ e)⁻¹) ^ q ≤ (4 : ℝ≥0∞) ^ (q / 2 ^ e + 1) := by
  set M : ℕ := 2 ^ e with hM
  have hMpos : 0 < M := pow_pos (by norm_num) e
  have hconv : (1 + ((2 : ℝ≥0∞) ^ e)⁻¹) = ENNReal.ofReal (1 + ((M : ℝ))⁻¹) := by
    rw [ENNReal.ofReal_add (by norm_num) (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_inv_of_pos (by exact_mod_cast hMpos), ENNReal.ofReal_natCast, hM]
    push_cast
    rfl
  rw [hconv, ← ENNReal.ofReal_pow (by positivity), show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
    ← ENNReal.ofReal_pow (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  set y : ℝ := 1 + (M : ℝ)⁻¹
  have hy1 : 1 ≤ y := le_add_of_nonneg_right (by positivity)
  have hqle : q ≤ M * (q / M + 1) := by
    have := Nat.lt_mul_div_succ q hMpos
    omega
  have hyM : y ^ M ≤ 4 := by
    have h1 : y ≤ Real.exp ((M : ℝ)⁻¹) := by
      have := Real.add_one_le_exp ((M : ℝ)⁻¹)
      simp only [y]; linarith
    calc y ^ M ≤ Real.exp ((M : ℝ)⁻¹) ^ M := pow_le_pow_left₀ (by linarith) h1 M
      _ = Real.exp ((M : ℝ) * (M : ℝ)⁻¹) := (Real.exp_nat_mul _ M).symm
      _ = Real.exp 1 := by rw [mul_inv_cancel₀ (by exact_mod_cast hMpos.ne')]
      _ ≤ 4 := by have := Real.exp_one_lt_d9; linarith
  calc y ^ q ≤ y ^ (M * (q / M + 1)) := pow_le_pow_right₀ hy1 hqle
    _ = (y ^ M) ^ (q / M + 1) := pow_mul y M _
    _ ≤ 4 ^ (q / M + 1) := pow_le_pow_left₀ (by positivity) hyM _

/-- **One pattern term** is at most `2^-(b + (a+1)k + 101)`. -/
theorem patTerm_le (q s : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ patCap q s * (1 + ((2 : ℝ≥0∞) ^ (subtreeHeight + forsHeight * s))⁻¹) ^ q ≤
      (2 : ℝ≥0∞)⁻¹ ^ (subtreeHeight + (forsHeight + 1) * forsTrees + 101) := by
  set e := subtreeHeight + forsHeight * s with he
  set B := subtreeHeight + (forsHeight + 1) * forsTrees with hB
  set j := q / 2 ^ e with hj
  set T := patCap q s with hT
  have hT1 : 6 * j + 1 ≤ T := by
    have h := Nat.mul_div_le_mul_div_assoc 6 q (2 ^ e)
    have h2 : 6 * q / 2 ^ e + 1 ≤ T := by rw [hT, patCap]; exact le_max_left _ _
    omega
  have hT2 : 2 * (B + 101) ≤ T := by
    have h : capFloor ≤ T := by rw [hT, patCap]; exact le_max_right _ _
    unfold capFloor at h
    omega
  have hjT : 2 * (2 * j + 2) ≤ T := by
    rcases Nat.lt_or_ge j 2 with h | h
    · omega
    · omega
  have hsplit : T = (T - (2 * j + 2)) + (2 * j + 2) := by omega
  calc (2 : ℝ≥0∞)⁻¹ ^ T * (1 + ((2 : ℝ≥0∞) ^ e)⁻¹) ^ q
      ≤ (2 : ℝ≥0∞)⁻¹ ^ T * (4 : ℝ≥0∞) ^ (j + 1) := mul_le_mul_right (one_add_inv_pow_le e q) _
    _ = (2 : ℝ≥0∞)⁻¹ ^ (T - (2 * j + 2)) := by
        conv_lhs => rw [hsplit]
        rw [pow_add, show (4 : ℝ≥0∞) = 2 ^ 2 by norm_num, ← pow_mul, show 2 * (j + 1) = 2 * j + 2 by ring,
          mul_assoc, ← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, mul_one]
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ (B + 101) :=
        pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.2 one_le_two) (by omega)

theorem card_patB : Fintype.card Pat = (2 ^ forsHeight + 1) ^ forsTrees := by
  rw [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Fintype.card_fin]

/-- **The pattern part at the start** is at most `2^-101`. -/
theorem psiP_start_le' (parameter : PublicParameter) (data : PublicData) (tp : TailPar) (s : State) :
    psiP parameter data tp s [] [] tp.q ≤ (2 : ℝ≥0∞)⁻¹ ^ 101 := by
  unfold psiP
  simp only [prodU_nilB, mul_one]
  set B := subtreeHeight + (forsHeight + 1) * forsTrees with hB
  calc _ ≤ ∑ _I : Fin (2 ^ subtreeHeight), ∑ _S : Pat, (2 : ℝ≥0∞)⁻¹ ^ (B + 101) := by
        refine Finset.sum_le_sum fun I _ => ?_
        refine le_trans (Finset.sum_le_sum_of_subset (Finset.subset_univ _)) ?_
        exact Finset.sum_le_sum fun S _ => patTerm_le tp.q (patSize S)
    _ = (2 : ℝ≥0∞) ^ subtreeHeight * ((2 ^ forsHeight + 1) ^ forsTrees : ℕ) * (2 : ℝ≥0∞)⁻¹ ^ (B + 101) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ, card_patB, Fintype.card_fin,
          nsmul_eq_mul, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ (2 : ℝ≥0∞) ^ subtreeHeight * (2 : ℝ≥0∞) ^ ((forsHeight + 1) * forsTrees) * (2 : ℝ≥0∞)⁻¹ ^ (B + 101) := by
        gcongr
        have h : (2 ^ forsHeight + 1) ^ forsTrees ≤ 2 ^ ((forsHeight + 1) * forsTrees) := by
          rw [pow_mul]
          exact Nat.pow_le_pow_left (by rw [pow_succ]; have := Nat.one_le_two_pow (n := forsHeight); omega) _
        exact_mod_cast h
    _ = (2 : ℝ≥0∞)⁻¹ ^ 101 := by
        rw [hB, pow_add, pow_add, ← mul_assoc]
        rw [show (2 : ℝ≥0∞) ^ subtreeHeight * 2 ^ ((forsHeight + 1) * forsTrees) *
            ((2 : ℝ≥0∞)⁻¹ ^ subtreeHeight * (2 : ℝ≥0∞)⁻¹ ^ ((forsHeight + 1) * forsTrees)) =
            ((2 : ℝ≥0∞) * 2⁻¹) ^ subtreeHeight * ((2 : ℝ≥0∞) * 2⁻¹) ^ ((forsHeight + 1) * forsTrees) by
          rw [mul_pow, mul_pow]; ring]
        rw [ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_pow, one_mul, one_mul]

/-- The pattern part at the start, in the form of `tailSum`'s slack. -/
theorem psiP_start_le (parameter : PublicParameter) (data : PublicData) (tp : TailPar) (s : State) :
    psiP parameter data tp s [] [] tp.q ≤ ENNReal.ofReal (1 / 2 ^ 99) := by
  refine (psiP_start_le' parameter data tp s).trans ?_
  rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat, ← ENNReal.inv_pow]
  exact ENNReal.inv_le_inv.2 (pow_le_pow_right₀ one_le_two (by norm_num))

/-! ### The start value -/

/-- **The tail potential at the start** is at most the tail sum. -/
theorem psi_start_le (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (hw1 : wbar ≤ 1)
    (tp : TailPar) (s : State)
    (hrate : (signatureLimit : ℝ) / 2 ^ subtreeHeight + (tp.q : ℝ) * (landing * wbar).toReal / 2 ^ subtreeHeight
      ≤ tp.μ) :
    psi parameter data wbar tp s [] [] [] 0 tp.q ≤
      tailSum subtreeHeight forsTrees forsHeight tp.n0 tp.μ tp.θ tp.m tp.q := by
  unfold psi tailSum
  exact add_le_add (add_le_add (psiL_start_le parameter data wbar hw1 tp s hrate)
    (psiC_start_le parameter data wbar hw1 tp s hrate)) (psiP_start_le parameter data tp s)

end FORS.Security.SWRoute
