import FORS.SWRoute.ForecastDomA
import FORS.SWRoute.ForecastCells
import FORS.SWRoute.ForecastTail

/-! **The domination of the own-cell forecast, part B: Poisson moments at one index.**

* `touchard_eq_mom`: `T_r(μ) = E_{j ~ Pois(μ)}[j^r]` (the Touchard recursion of `touchardGo` is the
  moment recursion `E[j^(r+1)] = μ E[(j + 1)^r]`), hence `E[(j / 2^a)^r] = φ(r)` (`poisMean_phi`) and
  `E[((D + j) / 2^a)^(k-1)]` is the fresh sum of `freshK` (`poisMean_fresh`);
  `touchard_scale`: `T_r(μ') ≤ (μ' / μ)^r T_r(μ)`;
* one-index count functions `H(count at I)` with `H` monotone, convex and at most exponential
  (`Good1`) are good count functions; their one-coin H-term is at most the Poisson mean `E_μ[H]`
  at a rate `μ` above the rate of the future (`hTermO_fst_le`, `hTermO_dom_le`);
* the cover indicator of a set `T` of trees of a target at index `I` is dominated, after averaging
  the marks of the new views, by `(n_I / 2^a)^|T|` (`covI_dominated`). -/

open ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base.Domination FORS.Base.H0 FORS.Security.H0Avg ForsPrice Concrete

set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

theorem lsum_range {M : Type} [AddCommMonoid M] (f : ℕ → M) : ∀ n,
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by
      rw [List.range_succ, List.map_append, List.sum_append, lsum_range f n, Finset.sum_range_succ]
      simp

/-! ### Poisson moments -/

/-- The Poisson moment `E[j^r]`. -/
noncomputable def poisMom (μ : ℝ≥0) (r : ℕ) : ℝ≥0∞ := poisMean μ (fun j => (j : ℝ≥0∞) ^ r)

theorem poisMom_zero (μ : ℝ≥0) : poisMom μ 0 = 1 := by
  simp [poisMom, poisMean, poisW_tsum]

theorem poisMom_succ (μ : ℝ≥0) (r : ℕ) :
    poisMom μ (r + 1) = (μ : ℝ≥0∞) * ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ≥0∞) * poisMom μ i := by
  unfold poisMom poisMean
  rw [tsum_eq_zero_add' ENNReal.summable]
  have h0 : poisW μ 0 * ((0 : ℕ) : ℝ≥0∞) ^ (r + 1) = 0 := by simp
  rw [h0, zero_add]
  have h : ∀ n : ℕ, poisW μ (n + 1) * ((n + 1 : ℕ) : ℝ≥0∞) ^ (r + 1) =
      ∑ i ∈ Finset.range (r + 1), (μ : ℝ≥0∞) * ((r.choose i : ℝ≥0∞) * (poisW μ n * (n : ℝ≥0∞) ^ i)) := by
    intro n
    have hs := poisW_succ μ n
    calc poisW μ (n + 1) * ((n + 1 : ℕ) : ℝ≥0∞) ^ (r + 1)
        = (poisW μ (n + 1) * ((n + 1 : ℕ) : ℝ≥0∞)) * ((n + 1 : ℕ) : ℝ≥0∞) ^ r := by rw [pow_succ]; ring
      _ = (μ : ℝ≥0∞) * poisW μ n * ((n : ℝ≥0∞) + 1) ^ r := by rw [hs, Nat.cast_succ]
      _ = _ := by
          rw [add_pow, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [one_pow, mul_one]
          ring
  rw [tsum_congr h, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]

theorem poisMom_ne_top (μ : ℝ≥0) (r : ℕ) : poisMom μ r ≠ ⊤ := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    rcases r with _ | r
    · rw [poisMom_zero]; exact one_ne_top
    · rw [poisMom_succ]
      refine mul_ne_top coe_ne_top (ENNReal.sum_ne_top.2 fun i hi => ?_)
      exact mul_ne_top (natCast_ne_top _) (ih i (by have := Finset.mem_range.1 hi; omega))

theorem poisMom_toReal_succ (μ : ℝ≥0) (r : ℕ) :
    (poisMom μ (r + 1)).toReal =
      (μ : ℝ) * ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * (poisMom μ i).toReal := by
  rw [poisMom_succ, ENNReal.toReal_mul,
    ENNReal.toReal_sum (fun i _ => mul_ne_top (natCast_ne_top _) (poisMom_ne_top μ i))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.coe_toReal]

theorem chooseK_eq (n i : ℕ) (h : i ≤ n) : (chooseK n i : ℝ) = (n.choose i : ℝ) := by
  unfold chooseK
  rw [Nat.cast_choose ℝ h]

theorem touchardGo_mom (μ : ℝ≥0) : ∀ s n,
    touchardGo (μ : ℝ) s n ((List.range (n + 1)).map fun i => (poisMom μ i).toReal) =
      (List.range (n + 1 + s)).map fun i => (poisMom μ i).toReal
  | 0, n => rfl
  | s + 1, n => by
      simp only [touchardGo]
      have hnew : (μ : ℝ) * ((List.range (n + 1)).map fun i => chooseK n i *
          ((List.range (n + 1)).map fun i => (poisMom μ i).toReal).getD i 0).sum =
          (poisMom μ (n + 1)).toReal := by
        rw [poisMom_toReal_succ, lsum_range]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map, List.getElem_range,
          chooseK_eq n i (by omega)]
      rw [hnew]
      have happ : (List.range (n + 1)).map (fun i => (poisMom μ i).toReal) ++ [(poisMom μ (n + 1)).toReal] =
          (List.range (n + 1 + 1)).map fun i => (poisMom μ i).toReal := by
        rw [@List.range_succ (n + 1), List.map_append, List.map_singleton]
      rw [happ, touchardGo_mom μ s (n + 1)]
      congr 2
      omega

/-- **Touchard**: `T_r(μ) = E_{Pois(μ)}[j^r]`. -/
theorem touchard_eq_mom (μ : ℝ≥0) (r : ℕ) : touchard (μ : ℝ) r = (poisMom μ r).toReal := by
  unfold touchard
  have h1 : ([1] : List ℝ) = (List.range (0 + 1)).map fun i => (poisMom μ i).toReal := by
    simp [poisMom_zero]
  rw [h1, touchardGo_mom, List.getD_eq_getElem _ _ (by simp), List.getElem_map, List.getElem_range]

theorem touchard_nonneg' (μ : ℝ≥0) (r : ℕ) : 0 ≤ touchard (μ : ℝ) r := by
  rw [touchard_eq_mom]; exact ENNReal.toReal_nonneg

theorem ofReal_touchard (μ : ℝ≥0) (r : ℕ) : ENNReal.ofReal (touchard (μ : ℝ) r) = poisMom μ r := by
  rw [touchard_eq_mom, ENNReal.ofReal_toReal (poisMom_ne_top μ r)]

theorem touchard_succ (μ : ℝ≥0) (r : ℕ) :
    touchard (μ : ℝ) (r + 1) = (μ : ℝ) * ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * touchard (μ : ℝ) i := by
  simp only [touchard_eq_mom]
  exact poisMom_toReal_succ μ r

/-- **Touchard scaling**: `T_r(μ') ≤ (μ' / μ)^r T_r(μ)` for `0 < μ ≤ μ'`. -/
theorem touchard_scale {μ μ' : ℝ≥0} (hμ : 0 < μ) (hle : μ ≤ μ') (r : ℕ) :
    touchard (μ' : ℝ) r ≤ ((μ' : ℝ) / μ) ^ r * touchard (μ : ℝ) r := by
  have hμr : (0 : ℝ) < μ := hμ
  have hc : (1 : ℝ) ≤ (μ' : ℝ) / μ := by rw [one_le_div hμr]; exact_mod_cast hle
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    rcases r with _ | r
    · simp [touchard_eq_mom, poisMom_zero]
    · rw [touchard_succ, touchard_succ]
      have hsum : ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * touchard (μ' : ℝ) i ≤
          ((μ' : ℝ) / μ) ^ r * ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * touchard (μ : ℝ) i := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ r := by have := Finset.mem_range.1 hi; omega
        have h1 := ih i (by omega)
        have h2 : ((μ' : ℝ) / μ) ^ i ≤ ((μ' : ℝ) / μ) ^ r := pow_le_pow_right₀ hc hi'
        have h3 := touchard_nonneg' μ i
        have h4 : (0 : ℝ) ≤ r.choose i := by positivity
        calc (r.choose i : ℝ) * touchard (μ' : ℝ) i ≤ (r.choose i : ℝ) * (((μ' : ℝ) / μ) ^ i * touchard (μ : ℝ) i) :=
              mul_le_mul_of_nonneg_left h1 h4
          _ ≤ (r.choose i : ℝ) * (((μ' : ℝ) / μ) ^ r * touchard (μ : ℝ) i) := by gcongr
          _ = _ := by ring
      set c : ℝ := (μ' : ℝ) / μ with hcdef
      have hcμ : c * μ = μ' := by rw [hcdef]; field_simp
      calc (μ' : ℝ) * ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * touchard (μ' : ℝ) i
          ≤ (μ' : ℝ) * (c ^ r * ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * touchard (μ : ℝ) i) :=
            mul_le_mul_of_nonneg_left hsum (NNReal.coe_nonneg _)
        _ = (c * μ) * (c ^ r * ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * touchard (μ : ℝ) i) := by
            rw [hcμ]
        _ = c ^ (r + 1) * ((μ : ℝ) * ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * touchard (μ : ℝ) i) := by
            ring

/-! ### The per-pair weights and the fresh sum as Poisson means -/

theorem poisMean_mul_const (μ : ℝ≥0) (g : ℕ → ℝ≥0∞) (c : ℝ≥0∞) :
    poisMean μ (fun j => g j * c) = poisMean μ g * c := by
  unfold poisMean
  simp only [← mul_assoc]
  rw [ENNReal.tsum_mul_right]

/-- `E[(j / 2^a)^r] = φ(r)`. -/
theorem poisMean_phi (μ : ℝ≥0) (r : ℕ) :
    poisMean μ (fun j => ((j : ℝ≥0∞) / 2 ^ forsHeight) ^ r) = ENNReal.ofReal (phiK forsHeight (μ : ℝ) r) := by
  have e : ∀ j : ℕ, ((j : ℝ≥0∞) / 2 ^ forsHeight) ^ r = (j : ℝ≥0∞) ^ r * ((2 : ℝ≥0∞) ^ (forsHeight * r))⁻¹ := by
    intro j
    rw [div_eq_mul_inv, mul_pow, ENNReal.inv_pow, ← pow_mul, ← ENNReal.inv_pow]
  simp only [e]
  rw [poisMean_mul_const]
  unfold phiK
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (touchard_nonneg' μ r), ofReal_touchard,
    ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  rfl

theorem chooseK_nonneg' (n j : ℕ) : (0 : ℝ) ≤ chooseK n j := by unfold chooseK; positivity

/-- The fresh sum `Σ_{i < k} C(k-1, i) D^(k-1-i) T_i(μ)`. -/
noncomputable def freshSum (μ : ℝ) (D : ℕ) : ℝ :=
  ((List.range forsTrees).map fun i => chooseK (forsTrees - 1) i * (D : ℝ) ^ (forsTrees - 1 - i) * touchard μ i).sum

theorem freshSum_nonneg (μ : ℝ≥0) (D : ℕ) : 0 ≤ freshSum (μ : ℝ) D := by
  unfold freshSum
  rw [lsum_range]
  refine Finset.sum_nonneg fun i _ => ?_
  have := chooseK_nonneg' (forsTrees - 1) i
  have := touchard_nonneg' μ i
  positivity

theorem freshK_eq (μ : ℝ) (q D : ℕ) :
    freshK subtreeHeight forsTrees forsHeight μ q D =
      (q : ℝ) / 2 ^ (subtreeHeight + forsHeight) * (freshSum μ D / 2 ^ (forsHeight * (forsTrees - 1))) := rfl

/-- `E[(D + j)^(k-1)] = Σ_i C(k-1, i) D^(k-1-i) T_i(μ)`. -/
theorem poisMean_fresh (μ : ℝ≥0) (D : ℕ) :
    poisMean μ (fun j => ((D + j : ℕ) : ℝ≥0∞) ^ (forsTrees - 1)) = ENNReal.ofReal (freshSum (μ : ℝ) D) := by
  have hk : forsTrees - 1 + 1 = forsTrees := Nat.sub_add_cancel Params.forsTrees_pos
  have hpt : ∀ j : ℕ, ((D + j : ℕ) : ℝ≥0∞) ^ (forsTrees - 1) =
      ∑ i ∈ Finset.range forsTrees, ((forsTrees - 1).choose i : ℝ≥0∞) * (D : ℝ≥0∞) ^ (forsTrees - 1 - i) *
        (j : ℝ≥0∞) ^ i := by
    intro j
    rw [Nat.cast_add, add_comm, add_pow, hk]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  unfold poisMean
  simp only [hpt, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  unfold freshSum
  rw [lsum_range, ENNReal.ofReal_sum_of_nonneg (fun i _ => by
    have := chooseK_nonneg' (forsTrees - 1) i
    have := touchard_nonneg' μ i
    positivity)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ forsTrees - 1 := by have := Finset.mem_range.1 hi; omega
  have e : ∀ j, poisW μ j * (((forsTrees - 1).choose i : ℝ≥0∞) * (D : ℝ≥0∞) ^ (forsTrees - 1 - i) * (j : ℝ≥0∞) ^ i) =
      (((forsTrees - 1).choose i : ℝ≥0∞) * (D : ℝ≥0∞) ^ (forsTrees - 1 - i)) * (poisW μ j * (j : ℝ≥0∞) ^ i) := by
    intro j; ring
  simp only [e]
  rw [ENNReal.tsum_mul_left]
  change _ * poisMom μ i = _
  rw [← ofReal_touchard, chooseK_eq _ _ hi', ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

/-- **Fresh scaling**: `freshK(μ') ≤ (μ' / μ)^(k-1) freshK(μ)`. -/
theorem freshK_scale {μ μ' : ℝ≥0} (hμ : 0 < μ) (hle : μ ≤ μ') (q D : ℕ) :
    freshK subtreeHeight forsTrees forsHeight (μ' : ℝ) q D ≤
      ((μ' : ℝ) / μ) ^ (forsTrees - 1) * freshK subtreeHeight forsTrees forsHeight (μ : ℝ) q D := by
  have hμr : (0 : ℝ) < μ := hμ
  have hc : (1 : ℝ) ≤ (μ' : ℝ) / μ := by rw [one_le_div hμr]; exact_mod_cast hle
  have hS : freshSum (μ' : ℝ) D ≤ ((μ' : ℝ) / μ) ^ (forsTrees - 1) * freshSum (μ : ℝ) D := by
    unfold freshSum
    rw [lsum_range, lsum_range, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' : i ≤ forsTrees - 1 := by have := Finset.mem_range.1 hi; omega
    have h1 := touchard_scale hμ hle i
    have h2 : ((μ' : ℝ) / μ) ^ i ≤ ((μ' : ℝ) / μ) ^ (forsTrees - 1) := pow_le_pow_right₀ hc hi'
    have h3 := touchard_nonneg' μ i
    have h4 : 0 ≤ chooseK (forsTrees - 1) i * (D : ℝ) ^ (forsTrees - 1 - i) := by
      have := chooseK_nonneg' (forsTrees - 1) i; positivity
    calc chooseK (forsTrees - 1) i * (D : ℝ) ^ (forsTrees - 1 - i) * touchard (μ' : ℝ) i
        ≤ chooseK (forsTrees - 1) i * (D : ℝ) ^ (forsTrees - 1 - i) * (((μ' : ℝ) / μ) ^ i * touchard (μ : ℝ) i) :=
          mul_le_mul_of_nonneg_left h1 h4
      _ ≤ chooseK (forsTrees - 1) i * (D : ℝ) ^ (forsTrees - 1 - i) *
            (((μ' : ℝ) / μ) ^ (forsTrees - 1) * touchard (μ : ℝ) i) := by gcongr
      _ = _ := by ring
  rw [freshK_eq, freshK_eq]
  have hq : (0 : ℝ) ≤ (q : ℝ) / 2 ^ (subtreeHeight + forsHeight) := by positivity
  calc (q : ℝ) / 2 ^ (subtreeHeight + forsHeight) * (freshSum (μ' : ℝ) D / 2 ^ (forsHeight * (forsTrees - 1)))
      ≤ (q : ℝ) / 2 ^ (subtreeHeight + forsHeight) *
          (((μ' : ℝ) / μ) ^ (forsTrees - 1) * freshSum (μ : ℝ) D / 2 ^ (forsHeight * (forsTrees - 1))) := by
        gcongr
    _ = _ := by ring

/-! ### One-index count functions -/

/-- Monotone, convex, at most exponential. -/
structure Good1 (H : ℕ → ℝ≥0∞) : Prop where
  mono : Monotone H
  convex : ∀ n, H (n + 1) + H (n + 1) ≤ H (n + 2) + H n
  growth : ∃ C r : ℝ≥0, ∀ n, H n ≤ (C : ℝ≥0∞) * (r : ℝ≥0∞) ^ n

theorem Good1.ne_top {H : ℕ → ℝ≥0∞} (hH : Good1 H) (n : ℕ) : H n ≠ ⊤ := by
  obtain ⟨C, r, h⟩ := hH.growth
  exact ne_top_of_le_ne_top (mul_ne_top coe_ne_top (pow_ne_top coe_ne_top)) (h n)

theorem Good1.shift {H : ℕ → ℝ≥0∞} (hH : Good1 H) (c : ℕ) : Good1 (fun n => H (n + c)) where
  mono := fun a b hab => hH.mono (by omega)
  convex := fun n => by
    have := hH.convex (n + c)
    rw [show n + 1 + c = n + c + 1 by omega, show n + 2 + c = n + c + 2 by omega]
    exact this
  growth := by
    obtain ⟨C, r, h⟩ := hH.growth
    refine ⟨C * r ^ c, r, fun n => ?_⟩
    calc H (n + c) ≤ (C : ℝ≥0∞) * (r : ℝ≥0∞) ^ (n + c) := h _
      _ = _ := by push_cast; ring

theorem Good1.const_mul {H : ℕ → ℝ≥0∞} (hH : Good1 H) {c : ℝ≥0∞} (hc : c ≠ ⊤) : Good1 (fun n => c * H n) where
  mono := fun a b hab => mul_le_mul_right (hH.mono hab) c
  convex := fun n => by
    have := mul_le_mul_right (hH.convex n) c
    simp only [mul_add] at this
    exact this
  growth := by
    obtain ⟨C, r, h⟩ := hH.growth
    refine ⟨c.toNNReal * C, r, fun n => ?_⟩
    calc c * H n ≤ c * ((C : ℝ≥0∞) * (r : ℝ≥0∞) ^ n) := mul_le_mul_right (h n) c
      _ = _ := by push_cast; rw [ENNReal.coe_toNNReal hc]; ring

theorem pow_convex_nat (t x : ℕ) : 2 * (x + 1) ^ t ≤ (x + 2) ^ t + x ^ t := by
  have h := (convexOn_pow (𝕜 := ℝ) t).2 (Set.mem_Ici.2 (by positivity : (0 : ℝ) ≤ x))
    (Set.mem_Ici.2 (by positivity : (0 : ℝ) ≤ x + 2)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  have e : (1 / 2 : ℝ) * x + 1 / 2 * (x + 2) = x + 1 := by ring
  rw [e] at h
  have h' : (2 : ℝ) * ((x : ℝ) + 1) ^ t ≤ ((x : ℝ) + 2) ^ t + (x : ℝ) ^ t := by linarith
  exact_mod_cast h'

/-- The powers `n ↦ n^t` are good. -/
theorem good1_pow (t : ℕ) : Good1 (fun n => (n : ℝ≥0∞) ^ t) where
  mono := fun a b hab => by
    show (a : ℝ≥0∞) ^ t ≤ (b : ℝ≥0∞) ^ t
    gcongr
  convex := fun n => by
    show ((n + 1 : ℕ) : ℝ≥0∞) ^ t + ((n + 1 : ℕ) : ℝ≥0∞) ^ t ≤ ((n + 2 : ℕ) : ℝ≥0∞) ^ t + (n : ℝ≥0∞) ^ t
    have h := pow_convex_nat t n
    rw [two_mul] at h
    exact_mod_cast h
  growth := ⟨1, 2 ^ t, fun n => by
    simp only [ENNReal.coe_one, one_mul]
    have h : n ^ t ≤ (2 ^ t) ^ n := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le t
    exact_mod_cast h⟩

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- A one-index count function is good. -/
theorem countGood_single {H : ℕ → ℝ≥0∞} (hH : Good1 H) (I : ι) : CountGood (fun x : ι → ℕ => H (x I)) where
  mono := fun x y hxy => hH.mono (hxy I)
  super := by
    intro k i j hij
    simp only [Pi.add_apply, Pi.single_apply]
    by_cases hi : I = i
    · subst hi
      simp [hij]
    · by_cases hj : I = j
      · subst hj
        simp only [hi, if_false, add_zero, if_true, eq_self_iff_true]
        exact le_of_eq (add_comm _ _)
      · simp [hi, hj]
  convex := by
    intro k i
    simp only [Pi.add_apply, Pi.single_apply]
    by_cases hi : I = i
    · subst hi
      rw [if_pos rfl]
      exact hH.convex (k I)
    · simp [hi]
  growth := by
    obtain ⟨C, r, h⟩ := hH.growth
    refine ⟨C, max r 1, fun k => ?_⟩
    calc H (k I) ≤ (C : ℝ≥0∞) * (r : ℝ≥0∞) ^ (k I) := h _
      _ ≤ (C : ℝ≥0∞) * ((max r 1 : ℝ≥0) : ℝ≥0∞) ^ (k I) := by
          gcongr
          exact_mod_cast le_max_left r 1
      _ ≤ (C : ℝ≥0∞) * ((max r 1 : ℝ≥0) : ℝ≥0∞) ^ (∑ l, k l) := by
          gcongr
          · exact_mod_cast le_max_right r 1
          · exact Finset.single_le_sum (fun l _ => Nat.zero_le (k l)) (Finset.mem_univ I)

/-- The iid Poisson mean of a one-index count function. -/
theorem poisIID_single (μ : ℝ≥0) (H : ℕ → ℝ≥0∞) (I : ι) :
    poisIID μ (fun x : ι → ℕ => H (x I)) 0 = poisMean μ H := by
  have hF : (fun x : ι → ℕ => H (x I)) = fun x => ∏ l, (if l = I then H (x l) else 1) := by
    funext x
    rw [Finset.prod_ite_eq' Finset.univ I (fun l => H (x l)), if_pos (Finset.mem_univ _)]
  have h := poisList_sepProd μ (Finset.univ : Finset ι).toList (Finset.nodup_toList _)
    (fun l n => if l = I then H n else 1) 0
  simp only [Finset.mem_toList, Finset.mem_univ, if_true, Pi.zero_apply] at h
  rw [hF]
  unfold poisIID
  refine h.trans ?_
  rw [Finset.prod_eq_single I]
  · simp only [eq_self_iff_true, if_true]
    exact pois1_zero μ H
  · intro l _ hl
    simp only [hl, if_false]
    unfold pois1
    simp [ENNReal.tsum_mul_right, poisW_tsum]
  · intro h; exact absurd (Finset.mem_univ I) h

end FORS.Security.SWRoute
