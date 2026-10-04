import LeanSphincs.H0Pointwise

/-! The H-term of the excess of a count price `Z(D) = Σ_l κ cnt_l^24` over a baseline `β`, bounded
by the Poisson mean of the product-form majorant `A Π_l (1 + t κ cnt_l^24)^R`, with
`A = c_R / (t^R β^(R-1))`. Generic in the view type. -/

open ENNReal

namespace LeanSphincs.Security.H0

open Domination

set_option linter.unusedSectionVars false

variable {V ι : Type} [DecidableEq ι] [Fintype ι] (idx : V → ι)

/-- The count price `Σ_l κ cnt_l^24`. -/
noncomputable def countPrice (κ : ℝ≥0∞) (d : Multiset V) : ℝ≥0∞ := ∑ l, κ * (cnt idx d l : ℝ≥0∞) ^ 24

/-- Touchard polynomial `T_n(μ) = E[Poisson(μ)^n]`. -/
noncomputable def touchard (n : ℕ) (μ : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (n + 1), (Nat.stirlingSecond n j : ℝ≥0∞) * μ ^ j

/-- Pointwise: `(Z - β) + A ≤ A Π_l (1 + t κ cnt_l^24)^R`. -/
theorem excess_add_le_prod (κ β t : ℝ≥0∞) (hκ : κ ≠ ⊤) (R : ℕ) (hR : 1 ≤ R) (hβ0 : R = 1 ∨ β ≠ 0)
    (hβ : β ≠ ⊤) (ht0 : t ≠ 0) (ht : t ≠ ⊤) (d : Multiset V) :
    (countPrice idx κ d - β) + cMom R / (t ^ R * β ^ (R - 1)) ≤
      cMom R / (t ^ R * β ^ (R - 1)) * ∏ l, (1 + t * κ * (cnt idx d l : ℝ≥0∞) ^ 24) ^ R := by
  set A := cMom R / (t ^ R * β ^ (R - 1))
  set Z := countPrice idx κ d
  have hZ : Z ≠ ⊤ := ENNReal.sum_ne_top.2 fun l _ => ENNReal.mul_ne_top hκ (by simp)
  have hmom := excess_le_cMom Z β hZ hβ R hR hβ0
  rw [scale_cancel _ Z β t R ht0 ht] at hmom
  have hprod := pow_sum_le_prod (fun l => κ * (cnt idx d l : ℝ≥0∞) ^ 24) t R (by omega)
  have hprod' : 1 + (t * Z) ^ R ≤ ∏ l, (1 + t * κ * (cnt idx d l : ℝ≥0∞) ^ 24) ^ R := by
    simpa [Z, countPrice, mul_assoc] using hprod
  calc Z - β + A ≤ A * (t * Z) ^ R + A := by
        gcongr
        exact tsub_le_iff_left.mpr hmom
    _ = A * (1 + (t * Z) ^ R) := by ring
    _ ≤ A * ∏ l, (1 + t * κ * (cnt idx d l : ℝ≥0∞) ^ 24) ^ R := by gcongr

/-- **H-term of the excess.** With `μ = N α + q γ` the Poisson-domination rate,
`H(excess) + A ≤ A (Σ_{s≤R} C(R,s) (t κ)^s T_{24 s}(μ))^L`. -/
theorem hTerm_excess_le (U : Finset V) (hU : UniformIndex idx U) (hUne : U.Nonempty)
    (κ β t : ℝ≥0∞) (hκ : κ ≠ ⊤) (R : ℕ) (hR : 1 ≤ R) (hβ0 : R = 1 ∨ β ≠ 0) (hβ : β ≠ ⊤) (ht0 : t ≠ 0)
    (ht : t ≠ ⊤) (N q : ℕ) (α w lam γ : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1)
    (hL : (Fintype.card ι : ℝ≥0∞) ≠ 0)
    (hslack : (1 + N * w) * (1 + w * Fintype.card ι) ^ (24 * R) ≤ Fintype.card ι * α)
    (hLα : 1 ≤ (Fintype.card ι : ℝ≥0∞) * α)
    (hγ : lam * (N * w) * (1 + w * Fintype.card ι) ^ (24 * R) ≤ Fintype.card ι * γ) :
    hTerm U w lam N q (fun d => countPrice idx κ d - β) + cMom R / (t ^ R * β ^ (R - 1)) ≤
      cMom R / (t ^ R * β ^ (R - 1)) *
        ∏ _l : ι, ∑ s ∈ Finset.range (R + 1), (R.choose s : ℝ≥0∞) * (t * κ) ^ s *
          touchard (24 * s) ((N : ℝ≥0∞) * α + q * γ) := by
  set A := cMom R / (t ^ R * β ^ (R - 1))
  have hconst : hTerm U w lam N q (fun _ => A) = A := by
    unfold hTerm
    simp only [virtual_const hUne hw A]
    exact creations_const hUne hlam A q []
  calc hTerm U w lam N q (fun d => countPrice idx κ d - β) + A
      = hTerm U w lam N q (fun d => (countPrice idx κ d - β) + A) := by
        rw [hTerm_add U hUne w lam N q, hconst]
    _ ≤ hTerm U w lam N q (fun d => A * ∏ l, (1 + t * κ * (cnt idx d l : ℝ≥0∞) ^ 24) ^ R) :=
        hTerm_mono U w lam N q fun d => excess_add_le_prod idx κ β t hκ R hR hβ0 hβ ht0 ht d
    _ = A * hTerm U w lam N q (fun d => ∏ l, ∑ p ∈ Finset.range (R + 1) ×ˢ Finset.range (24 * R + 1),
          ((R.choose p.1 : ℝ≥0∞) * (t * κ) ^ p.1 * (Nat.stirlingSecond (24 * p.1) p.2 : ℝ≥0∞)) *
            ((cnt idx d l).descFactorial p.2 : ℝ≥0∞)) := by
        rw [← hTerm_const_mul]
        congr 1; funext d; congr 1
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [← leaf_expand, mul_assoc]
    _ ≤ A * ∏ _l : ι, ∑ p ∈ Finset.range (R + 1) ×ˢ Finset.range (24 * R + 1),
          ((R.choose p.1 : ℝ≥0∞) * (t * κ) ^ p.1 * (Nat.stirlingSecond (24 * p.1) p.2 : ℝ≥0∞)) *
            ((N : ℝ≥0∞) * α + q * γ) ^ p.2 := by
        have hn : ∀ p ∈ Finset.range (R + 1) ×ˢ Finset.range (24 * R + 1), (fun p : ℕ × ℕ => p.2) p ≤ 24 * R - 1 + 1 := by
          intro p hp
          have := (Finset.mem_range.mp (Finset.mem_product.mp hp).2)
          dsimp only
          omega
        have hsl : (1 + N * w) * (1 + w * Fintype.card ι) ^ (24 * R - 1) ≤ Fintype.card ι * α := by
          refine le_trans ?_ hslack
          gcongr
          · exact le_self_add
          · omega
        have hg : lam * (N * w) * (1 + w * Fintype.card ι) ^ (24 * R - 1) ≤ Fintype.card ι * γ := by
          refine le_trans ?_ hγ
          gcongr
          · exact le_self_add
          · omega
        have h := hTerm_prod_le idx U hU hUne (Finset.range (R + 1) ×ˢ Finset.range (24 * R + 1))
          (fun p : ℕ × ℕ => (R.choose p.1 : ℝ≥0∞) * (t * κ) ^ p.1 * (Nat.stirlingSecond (24 * p.1) p.2 : ℝ≥0∞))
          (fun p : ℕ × ℕ => p.2) (24 * R - 1) hn N q α w lam γ hw hlam hL hsl hLα hg
        exact mul_le_mul_right h A
    _ = _ := by
        congr 1
        refine Finset.prod_congr rfl fun _ _ => ?_
        rw [leaf_pois]
        rfl

end LeanSphincs.Security.H0
