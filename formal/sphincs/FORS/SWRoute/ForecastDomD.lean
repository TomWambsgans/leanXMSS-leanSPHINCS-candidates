import FORS.SWRoute.ForecastDomC

/-! **The domination of the own-cell forecast, part D: the group coins of the cached pairs.**
On a full key the group of a live message selects each of its cached landed pairs with chance
`ε = 2^-128` and discloses its view. For target leaves `ℓ` at index `I` and a set `S` of trees:

* `grpAll_cov_le` (the `κ0` recursion): if `κ0 ∈ S` is not covered yet, the chance that the groups
  cover `S` is at most `Σ_g ε · (chance after adding g's view)` over the selectable pairs `g`
  matching `ℓ` at `κ0`;
* `grpAll_cov_coinV`: if at most `cap(|B|)` selectable pairs match `ℓ` on every nonempty `B`, the
  chance is at most `coinV(|S \ covered|)` with `coinV (t+1) = Σ_j C(t, j) cap(j+1) ε coinV (t - j)`. -/

open ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base FORS.Base.Domination FORS.Base.H0 FORS.Security.H0Avg ForsPrice Concrete GraphView
  ForsPotential FORS.LoopWalk

set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### The recursion of `coinV` -/

section CoinV

variable (b a cf q : ℕ)

/-- The next coin bound from the list of the previous ones. -/
noncomputable def newV (n : ℕ) (L : List ℝ) : ℝ :=
  ((List.range (n + 1)).map fun j => chooseK n j * ((patCapN b a cf q (j + 1) : ℕ) : ℝ) / 2 ^ 128 *
    L.getD (n - j) 0).sum

theorem coinGo_succ' : ∀ (t n : ℕ) (L : List ℝ),
    coinGo b a cf q (t + 1) n L = coinGo b a cf q t n L ++ [newV b a cf q (n + t) (coinGo b a cf q t n L)]
  | 0, n, L => by simp [coinGo, newV]
  | t + 1, n, L => by
      rw [coinGo, coinGo_succ' t (n + 1)]
      rw [show n + 1 + t = n + (t + 1) by omega]
      rfl

theorem coinGo_length : ∀ (t n : ℕ) (L : List ℝ), (coinGo b a cf q t n L).length = L.length + t
  | 0, n, L => rfl
  | t + 1, n, L => by
      rw [coinGo, coinGo_length t (n + 1)]
      simp
      omega

theorem coinW_getD : ∀ (n i : ℕ), i ≤ n → (coinGo b a cf q n 0 [1]).getD i 0 = (coinV b a cf q i : ℝ)
  | 0, i, hi => by
      have : i = 0 := by omega
      subst this; rfl
  | n + 1, i, hi => by
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · rw [coinGo_succ', List.getD_append _ _ _ _ (by rw [coinGo_length]; simp; omega)]
        exact coinW_getD n i (by omega)
      · have : i = n + 1 := by omega
        subst this; rfl

/-- **The recursion of `coinV`.** -/
theorem coinV_succ (t : ℕ) :
    (coinV b a cf q (t + 1) : ℝ) = ∑ j ∈ Finset.range (t + 1),
      (t.choose j : ℝ) * ((patCapN b a cf q (j + 1) : ℕ) : ℝ) / 2 ^ 128 * coinV b a cf q (t - j) := by
  have h1 : (coinV b a cf q (t + 1) : ℝ) = newV b a cf q t (coinGo b a cf q t 0 [1]) := by
    unfold coinV
    rw [coinGo_succ', zero_add, List.getD_append_right _ _ _ _ (by
      rw [coinGo_length]; simp only [List.length_cons, List.length_nil]; omega)]
    rw [coinGo_length]
    simp
  rw [h1]
  unfold newV
  rw [lsum_range]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ t := by have := Finset.mem_range.1 hj; omega
  rw [coinW_getD b a cf q t (t - j) (by omega), chooseK_eq t j hj']

theorem coinV_zero : (coinV b a cf q 0 : ℝ) = 1 := rfl

theorem coinV_nonneg (t : ℕ) : 0 ≤ (coinV b a cf q t : ℝ) := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rcases t with _ | t
    · rw [coinV_zero]; norm_num
    · rw [coinV_succ]
      refine Finset.sum_nonneg fun j hj => ?_
      have := ih (t - j) (by omega)
      positivity

/-- The coin bounds in `ℝ≥0∞`. -/
noncomputable def vE (t : ℕ) : ℝ≥0∞ := ENNReal.ofReal (coinV b a cf q t)

theorem vE_zero : vE b a cf q 0 = 1 := by unfold vE; rw [coinV_zero, ENNReal.ofReal_one]

theorem vE_succ (t : ℕ) :
    vE b a cf q (t + 1) = ∑ j ∈ Finset.range (t + 1),
      (t.choose j : ℝ≥0∞) * (patCapN b a cf q (j + 1) : ℝ≥0∞) * (Fintype.card Randomness : ℝ≥0∞)⁻¹ *
        vE b a cf q (t - j) := by
  unfold vE
  rw [coinV_succ, ENNReal.ofReal_sum_of_nonneg (fun j _ => by have := coinV_nonneg b a cf q (t - j); positivity)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (Fintype.card Randomness : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2 ^ 128) := by
    rw [card_randomness, one_div, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  rw [hc, show (t.choose j : ℝ) * ((patCapN b a cf q (j + 1) : ℕ) : ℝ) / 2 ^ 128 * coinV b a cf q (t - j) =
      (t.choose j : ℝ) * ((patCapN b a cf q (j + 1) : ℕ) : ℝ) * (1 / 2 ^ 128) * coinV b a cf q (t - j) by ring,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

end CoinV

/-! ### The groups covering leaves -/

section Cover

variable (parameter : PublicParameter) (data : PublicData) (s : State) (excl : Pair → Prop)

/-- A cached pair the groups can select: a cached hit, not excluded. -/
def HitP (g : Pair) : Prop := stOf parameter data g.1 s g.2 = .hit ∧ ¬excl g

theorem gx_eq (m : Message) (ρ : Randomness) :
    gx parameter data s excl m ρ =
      if HitP parameter data s excl (m, ρ) then {pview parameter data s (m, ρ)} else 0 := by
  unfold gx HitP extOf
  by_cases h1 : stOf parameter data m s ρ = .hit
  · by_cases h2 : excl (m, ρ) <;> simp [h1, h2]
  · simp [h1]

variable (I : Fin (2 ^ subtreeHeight)) (ℓ : FTree → FLeaf)

/-- A selectable pair at `I` matching the leaves `ℓ` at `κ0`. -/
def MatchP (κ0 : FTree) (g : Pair) : Prop :=
  HitP parameter data s excl g ∧ (pview parameter data s g).1 = I ∧ (pview parameter data s g).2 κ0 = ℓ κ0

theorem freshAvg_univ_eq {α : Type} [Fintype α] (f : α → ℝ≥0∞) :
    freshAvg (Finset.univ : Finset α) f = (Fintype.card α : ℝ≥0∞)⁻¹ * ∑ x, f x := by
  unfold freshAvg; rw [Finset.card_univ]

/-- **The `κ0` recursion.** -/
theorem grpAll_cov_le (hH : totalHeight = subtreeHeight) (S : Finset FTree) (κ0 : FTree) (hκ0 : κ0 ∈ S) :
    ∀ (Ms : List Message), Ms.Nodup → ∀ e, κ0 ∉ covT I ℓ e →
      grpAll parameter data s excl Ms (covI I ℓ S) e ≤
        ∑ m ∈ Ms.toFinset, ∑ ρ, if MatchP parameter data s excl I ℓ κ0 (m, ρ) then
          (Fintype.card Randomness : ℝ≥0∞)⁻¹ *
            grpAll parameter data s excl Ms (covI I ℓ S) (e + {pview parameter data s (m, ρ)}) else 0
  | [], _, e, he => by
      simp only [grpAll]
      unfold covI
      rw [if_neg (fun h => he (h hκ0))]
      exact zero_le
  | m :: Ms, hnd, e, he => by
      rw [List.nodup_cons] at hnd
      set ε := (Fintype.card Randomness : ℝ≥0∞)⁻¹ with hε
      set G := grpAll parameter data s excl Ms (covI I ℓ S) with hG
      set G' := grpAll parameter data s excl (m :: Ms) (covI I ℓ S) with hG'
      have hG'e : ∀ e', G' e' = ε * ∑ ρ, G (e' + gx parameter data s excl m ρ) := fun e' => by
        rw [hG', grpAll, grpM_eq parameter data hH, freshAvg_univ_eq]
      have hGmono : Monotone' G := grpAll_mono s excl (covI_mono I ℓ S) Ms
      have hGle : ∀ e', G e' ≤ G' e' := fun e' => by
        rw [hG'e, ← freshAvg_univ_eq]
        calc G e' = freshAvg Finset.univ (fun _ : Randomness => G e') :=
              (freshAvg_const _ Finset.univ_nonempty _).symm
          _ ≤ _ := freshAvg_mono _ fun ρ _ => hGmono _ _ le_self_add
      set Bsum : Multiset View → ℝ≥0∞ := fun e' => ∑ m' ∈ Ms.toFinset, ∑ ρ',
        if MatchP parameter data s excl I ℓ κ0 (m', ρ') then
          ε * G (e' + {pview parameter data s (m', ρ')}) else 0 with hBsum
      have hpt : ∀ ρ, G (e + gx parameter data s excl m ρ) ≤
          (if MatchP parameter data s excl I ℓ κ0 (m, ρ) then G' (e + {pview parameter data s (m, ρ)}) else 0) +
            Bsum (e + gx parameter data s excl m ρ) := by
        intro ρ
        by_cases hmρ : MatchP parameter data s excl I ℓ κ0 (m, ρ)
        · rw [if_pos hmρ, gx_eq, if_pos hmρ.1]
          exact le_trans (hGle _) le_self_add
        · rw [if_neg hmρ, zero_add]
          refine grpAll_cov_le hH S κ0 hκ0 Ms hnd.2 _ ?_
          rw [gx_eq]
          split_ifs with hh
          · rw [covT_add_single, Finset.mem_union, not_or]
            refine ⟨he, fun h2 => hmρ ⟨hh, ?_⟩⟩
            exact (Finset.mem_filter.1 h2).2
          · rwa [add_zero]
      have hB : ε * ∑ ρ, Bsum (e + gx parameter data s excl m ρ) =
          ∑ m' ∈ Ms.toFinset, ∑ ρ', if MatchP parameter data s excl I ℓ κ0 (m', ρ') then
            ε * G' (e + {pview parameter data s (m', ρ')}) else 0 := by
        simp only [hBsum]
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m' _ => ?_
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ρ' _ => ?_
        by_cases hm' : MatchP parameter data s excl I ℓ κ0 (m', ρ')
        · simp only [if_pos hm']
          rw [hG'e, ← Finset.mul_sum]
          refine congrArg (fun z => ε * (ε * z)) (Finset.sum_congr rfl fun ρ _ => ?_)
          rw [add_right_comm]
        · simp only [if_neg hm', mul_zero, Finset.sum_const_zero]
      have hm : m ∉ Ms.toFinset := by rw [List.mem_toFinset]; exact hnd.1
      rw [show (m :: Ms).toFinset = insert m Ms.toFinset by simp, Finset.sum_insert hm]
      calc G' e = ε * ∑ ρ, G (e + gx parameter data s excl m ρ) := hG'e e
        _ ≤ ε * ∑ ρ, ((if MatchP parameter data s excl I ℓ κ0 (m, ρ) then
              G' (e + {pview parameter data s (m, ρ)}) else 0) + Bsum (e + gx parameter data s excl m ρ)) :=
            mul_le_mul_right (Finset.sum_le_sum fun ρ _ => hpt ρ) ε
        _ = (∑ ρ, if MatchP parameter data s excl I ℓ κ0 (m, ρ) then
              ε * G' (e + {pview parameter data s (m, ρ)}) else 0) +
            ε * ∑ ρ, Bsum (e + gx parameter data s excl m ρ) := by
            have hA : ε * ∑ ρ, (if MatchP parameter data s excl I ℓ κ0 (m, ρ) then
                G' (e + {pview parameter data s (m, ρ)}) else 0) =
                ∑ ρ, (if MatchP parameter data s excl I ℓ κ0 (m, ρ) then
                  ε * G' (e + {pview parameter data s (m, ρ)}) else 0) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun ρ _ => by split_ifs <;> simp
            rw [Finset.sum_add_distrib, mul_add, hA]
        _ = _ := by rw [hB]

end Cover

end FORS.Security.SWRoute
