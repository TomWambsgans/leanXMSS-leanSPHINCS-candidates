import LeanSphincs.H0Majorant

/-! Product-form base functions `Π_l h(cnt_l)` with `h` a nonnegative combination of falling
factorials. Linearity of the H-term reduces them to joint factorial moments, which are
Poisson-dominated (`H0_fallMono_le`). -/

open ENNReal

namespace LeanSphincs.Security.H0

open Domination

set_option linter.unusedSectionVars false

variable {V ι : Type} [DecidableEq ι] [Fintype ι] (idx : V → ι)

/-- The H-term operator: future-pair creations around `N` virtual slots, from no disclosures. -/
noncomputable def hTerm (U : Finset V) (w lam : ℝ≥0∞) (N q : ℕ) (f : Multiset V → ℝ≥0∞) : ℝ≥0∞ :=
  creations U lam (fun I => virtual U w f N I 0) q []

theorem hTerm_mono (U : Finset V) (w lam : ℝ≥0∞) (N q : ℕ) {f g : Multiset V → ℝ≥0∞} (hfg : ∀ d, f d ≤ g d) :
    hTerm U w lam N q f ≤ hTerm U w lam N q g :=
  creations_mono (fun I => virtual_mono_base hfg N I 0) q []

theorem hTerm_zero (U : Finset V) (hU : U.Nonempty) (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (N q : ℕ) :
    hTerm U w lam N q (fun _ => 0) = 0 := by
  unfold hTerm
  simp only [virtual_const hU hw 0]
  exact creations_const hU hlam 0 q []

theorem hTerm_add (U : Finset V) (hU : U.Nonempty) (w lam : ℝ≥0∞) (N q : ℕ) (f g : Multiset V → ℝ≥0∞) :
    hTerm U w lam N q (fun d => f d + g d) = hTerm U w lam N q f + hTerm U w lam N q g := by
  unfold hTerm
  simp only [virtual_add hU f g]
  exact creations_add _ _ q []

theorem hTerm_const_mul (U : Finset V) (w lam : ℝ≥0∞) (N q : ℕ) (c : ℝ≥0∞) (f : Multiset V → ℝ≥0∞) :
    hTerm U w lam N q (fun d => c * f d) = c * hTerm U w lam N q f := by
  unfold hTerm
  simp only [virtual_const_mul c f]
  exact creations_const_mul c _ q []

theorem hTerm_sum {τ : Type} [DecidableEq τ] (U : Finset V) (hU : U.Nonempty) (w lam : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1)
    (N q : ℕ) (s : Finset τ) (c : τ → ℝ≥0∞) (g : τ → Multiset V → ℝ≥0∞) :
    hTerm U w lam N q (fun d => ∑ x ∈ s, c x * g x d) = ∑ x ∈ s, c x * hTerm U w lam N q (g x) := by
  induction s using Finset.induction_on with
  | empty => simpa using hTerm_zero U hU w lam hw hlam N q
  | insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      rw [hTerm_add U hU w lam N q (fun d => c j * g j d) (fun d => ∑ x ∈ s, c x * g x d), ih,
        hTerm_const_mul]

/-- **Product-form base functions.** If the per-leaf function is `Σ_{i∈I} a_i (k)_{n_i}`, the
H-term is at most the `L`-th power of its Poisson(μ) mean `Σ_i a_i μ^{n_i}`. -/
theorem hTerm_prod_le {τ : Type} (U : Finset V) (hU : UniformIndex idx U) (hUne : U.Nonempty)
    (I : Finset τ) (a : τ → ℝ≥0∞) (n : τ → ℕ) (K : ℕ) (hn : ∀ i ∈ I, n i ≤ K + 1)
    (N q : ℕ) (α w lam γ : ℝ≥0∞) (hw : w ≤ 1) (hlam : lam ≤ 1) (hL : (Fintype.card ι : ℝ≥0∞) ≠ 0)
    (hslack : (1 + N * w) * (1 + w * Fintype.card ι) ^ K ≤ Fintype.card ι * α)
    (hLα : 1 ≤ (Fintype.card ι : ℝ≥0∞) * α)
    (hγ : lam * (N * w) * (1 + w * Fintype.card ι) ^ K ≤ Fintype.card ι * γ) :
    hTerm U w lam N q (fun d => ∏ l, ∑ i ∈ I, a i * ((cnt idx d l).descFactorial (n i) : ℝ≥0∞)) ≤
      ∏ _l : ι, ∑ i ∈ I, a i * ((N : ℝ≥0∞) * α + q * γ) ^ n i := by
  classical
  set μ := (N : ℝ≥0∞) * α + q * γ
  -- expand the product of sums
  have hexp : ∀ d : Multiset V, ∏ l, ∑ i ∈ I, a i * ((cnt idx d l).descFactorial (n i) : ℝ≥0∞) =
      ∑ κ ∈ Fintype.piFinset (fun _ : ι => I), (∏ l, a (κ l)) * fallMono idx (fun l => n (κ l)) d := by
    intro d
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [fallMono, ← Finset.prod_mul_distrib]
  simp only [hexp]
  rw [hTerm_sum U hUne w lam hw hlam N q]
  calc ∑ κ ∈ Fintype.piFinset (fun _ : ι => I), (∏ l, a (κ l)) * hTerm U w lam N q (fallMono idx (fun l => n (κ l)))
      ≤ ∑ κ ∈ Fintype.piFinset (fun _ : ι => I), (∏ l, a (κ l)) * μ ^ ∑ l, n (κ l) := by
        gcongr with κ hκ
        rw [Fintype.mem_piFinset] at hκ
        exact H0_fallMono_le idx U hU _ K (fun l => hn _ (hκ l)) N q α w lam γ hw hlam hL hslack hLα hγ
    _ = ∏ _l : ι, ∑ i ∈ I, a i * μ ^ n i := by
        rw [Finset.prod_univ_sum]
        refine Finset.sum_congr rfl fun κ _ => ?_
        rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]

end LeanSphincs.Security.H0
