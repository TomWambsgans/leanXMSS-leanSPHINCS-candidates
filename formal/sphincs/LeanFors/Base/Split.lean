import LeanFors.Base.Poisson

/-! The split majorant of the excess of a price `Σ_l y_l` over a threshold (for FORS, `y_l` is the
cover probability at index `l`, `excess_le_split`). With `m_l = min(y_l, c1)` and `M = Σ_l m_l`,
`(Σ_l y_l - β)^+ ≤ Σ_l (y_l - c1)^+ + (M - c)^+` for any real `c` with `c ≤ β`, and the last
term is bounded by the Chernoff majorant `e^{θ (M - c)} / (e θ) = e^{-θ c} / (e θ) Π_l e^{θ m_l}`.
Iid Poisson means of the separable sum and product factorize over the leaves:
`L E[g(K)]` and `E[h(K)]^L`. -/

open ENNReal NNReal

namespace LeanFors.Base.H0

open Domination

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-! ### The pointwise split majorant -/

/-- **Chernoff.** `M - c ≤ e^{-θ c} / (e θ) e^{θ M}` for `θ > 0`. -/
theorem chernoff_real (M c θ : ℝ) (hθ : 0 < θ) :
    M - c ≤ Real.exp (-θ * c) / (Real.exp 1 * θ) * Real.exp (θ * M) := by
  have h := Real.add_one_le_exp (θ * (M - c) - 1)
  have e : Real.exp (θ * (M - c) - 1) = Real.exp (-θ * c) * Real.exp (θ * M) / Real.exp 1 := by
    rw [Real.exp_sub, show θ * (M - c) = -θ * c + θ * M by ring, Real.exp_add]
  rw [e] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have h1 : 0 < Real.exp 1 := Real.exp_pos 1
  rw [le_div_iff₀ h1] at h
  nlinarith

/-- The real split: `Σ y - c ≤ Σ (y - c1)^+ + e^{-θ c} / (e θ) Π e^{θ min(y, c1)}`. -/
theorem split_real (y : ι → ℝ) (c c1 θ : ℝ) (hθ : 0 < θ) :
    ∑ l, y l - c ≤ ∑ l, max (y l - c1) 0 +
      Real.exp (-θ * c) / (Real.exp 1 * θ) * ∏ l, Real.exp (θ * min (y l) c1) := by
  have hdec : ∑ l, y l = ∑ l, max (y l - c1) 0 + ∑ l, min (y l) c1 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [max_def, min_def]
    split_ifs <;> linarith
  have hch := chernoff_real (∑ l, min (y l) c1) c θ hθ
  rw [Finset.mul_sum, Real.exp_sum] at hch
  linarith

/-! ### Iid Poisson means of separable sums and products -/

/-- One-coordinate Poisson mean `E[h(n + K)]`, `K ~ Poisson(a)`. -/
noncomputable def pois1 (a : ℝ≥0) (h : ℕ → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ := ∑' m, poisW a m * h (n + m)

/-- The Poisson mean `E[h(K)]`, `K ~ Poisson(a)`. -/
noncomputable def poisMean (a : ℝ≥0) (h : ℕ → ℝ≥0∞) : ℝ≥0∞ := ∑' m, poisW a m * h m

theorem pois1_zero (a : ℝ≥0) (h : ℕ → ℝ≥0∞) : pois1 a h 0 = poisMean a h := by
  simp [pois1, poisMean]

theorem pois_sepSum (a : ℝ≥0) (j : ι) (h : ι → ℕ → ℝ≥0∞) (k : ι → ℕ) :
    pois a j (fun x => ∑ l, h l (x l)) k = ∑ l, (if l = j then pois1 a (h l) (k l) else h l (k l)) := by
  unfold pois
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hl : l = j
  · subst hl
    simp only [if_true, Pi.add_apply, Pi.single_eq_same]
    rfl
  · simp only [if_neg hl, Pi.add_apply, Pi.single_eq_of_ne hl, add_zero]
    rw [ENNReal.tsum_mul_right, poisW_tsum, one_mul]

theorem pois_sepProd (a : ℝ≥0) (j : ι) (g : ι → ℕ → ℝ≥0∞) (k : ι → ℕ) :
    pois a j (fun x => ∏ l, g l (x l)) k = ∏ l, (if l = j then pois1 a (g l) (k l) else g l (k l)) := by
  set R := ∏ l ∈ Finset.univ.erase j, g l (k l) with hR
  have hterm : ∀ n : ℕ, ∏ l, g l ((k + Pi.single j n : ι → ℕ) l) = g j (k j + n) * R := by
    intro n
    rw [prod_split j, hR]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun l hl => ?_
      rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hl), add_zero]
  have hrest' : ∏ l ∈ Finset.univ.erase j, (if l = j then pois1 a (g l) (k l) else g l (k l)) = R := by
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [if_neg (Finset.ne_of_mem_erase hl)]
  unfold pois
  calc ∑' n, poisW a n * ∏ l, g l ((k + Pi.single j n : ι → ℕ) l)
      = ∑' n, poisW a n * g j (k j + n) * R := tsum_congr fun n => by rw [hterm n, mul_assoc]
    _ = pois1 a (g j) (k j) * R := by rw [ENNReal.tsum_mul_right]; rfl
    _ = _ := by rw [prod_split j, if_pos rfl, hrest']

theorem poisList_sepSum (a : ℝ≥0) : ∀ (ls : List ι), ls.Nodup → ∀ (h : ι → ℕ → ℝ≥0∞) (k : ι → ℕ),
    poisList a ls (fun x => ∑ l, h l (x l)) k = ∑ l, (if l ∈ ls then pois1 a (h l) (k l) else h l (k l))
  | [], _, h, k => by simp [poisList]
  | j :: ls, hnd, h, k => by
      rw [List.nodup_cons] at hnd
      simp only [poisList]
      have e : pois a j (fun x => ∑ l, h l (x l)) =
          fun x => ∑ l, (fun l n => if l = j then pois1 a (h l) n else h l n) l (x l) := by
        funext x
        rw [pois_sepSum]
      rw [e]
      refine (poisList_sepSum a ls hnd.2 (fun l n => if l = j then pois1 a (h l) n else h l n) k).trans ?_
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : l = j
      · subst hl
        simp [hnd.1]
      · by_cases hm : l ∈ ls
        · simp [hl, hm]
        · simp [hl, hm]

theorem poisList_sepProd (a : ℝ≥0) : ∀ (ls : List ι), ls.Nodup → ∀ (g : ι → ℕ → ℝ≥0∞) (k : ι → ℕ),
    poisList a ls (fun x => ∏ l, g l (x l)) k = ∏ l, (if l ∈ ls then pois1 a (g l) (k l) else g l (k l))
  | [], _, g, k => by simp [poisList]
  | j :: ls, hnd, g, k => by
      rw [List.nodup_cons] at hnd
      simp only [poisList]
      have e : pois a j (fun x => ∏ l, g l (x l)) =
          fun x => ∏ l, (fun l n => if l = j then pois1 a (g l) n else g l n) l (x l) := by
        funext x
        rw [pois_sepProd]
      rw [e]
      refine (poisList_sepProd a ls hnd.2 (fun l n => if l = j then pois1 a (g l) n else g l n) k).trans ?_
      refine Finset.prod_congr rfl fun l _ => ?_
      by_cases hl : l = j
      · subst hl
        simp [hnd.1]
      · by_cases hm : l ∈ ls
        · simp [hl, hm]
        · simp [hl, hm]

/-- Iid Poisson mean of a separable sum: `Σ_l E[h(K)]`. -/
theorem poisIID_sepSum (a : ℝ≥0) (h : ℕ → ℝ≥0∞) :
    poisIID a (fun x : ι → ℕ => ∑ l, h (x l)) 0 = (Fintype.card ι : ℝ≥0∞) * poisMean a h := by
  unfold poisIID
  rw [poisList_sepSum a _ (Finset.nodup_toList _) (fun _ => h)]
  simp only [Finset.mem_toList, Finset.mem_univ, if_true, Pi.zero_apply, pois1_zero, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]

/-- Iid Poisson mean of a separable product: `E[g(K)]^L`. -/
theorem poisIID_sepProd (a : ℝ≥0) (g : ℕ → ℝ≥0∞) :
    poisIID a (fun x : ι → ℕ => ∏ l, g (x l)) 0 = poisMean a g ^ Fintype.card ι := by
  unfold poisIID
  rw [poisList_sepProd a _ (Finset.nodup_toList _) (fun _ => g)]
  simp only [Finset.mem_toList, Finset.mem_univ, if_true, Pi.zero_apply, pois1_zero, Finset.prod_const,
    Finset.card_univ]

end LeanFors.Base.H0
