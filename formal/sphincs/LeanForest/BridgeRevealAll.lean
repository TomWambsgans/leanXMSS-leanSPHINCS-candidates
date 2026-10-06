import LeanForest.BridgeSignerForest

/-! **The fair share for weights of the reveals of every run.** The grinding signer's fair share
(`loop_boundW`) for a weight of the reveal list rather than of the result: aborted runs count too,
and the weight of a run of the final assembly is bounded by the weight of its pair whatever the
run does after the digest call. -/

open OracleComp OracleSpec ENNReal

namespace LeanForest.Security.GraphView

open LeanSphincs.Security
open Concrete Completeness Prefix HiddenGraph HiddenCost HiddenDebt ForestSigner

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

section LoopV

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

/-- **One grinding trial.** -/
theorem trial_boundV
    (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (reference : DebtState HashInput HashOutput Coordinate) (ρ : Randomness)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (V : List Coordinate → ℝ≥0∞)
    (hV0 : V [] = 0)
    (hVfin : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ → s'.cache (blk parameter data message ρ) = some u0 →
      Landed parameter (blockIndex u0) →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        V out.1.2.1 ≤ pairWeight parameter data message reference gf gp ρ u0)
    (bound : ℝ≥0∞) (state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state) (attempts : ℕ)
    (hih : ∀ s', Related parameter data message reference s' →
      cachedCount parameter data message s' ≤ cachedCount parameter data message state + 1 → ∀ b,
        ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts) b s'] *
          V out.1.2.1 ≤ bound)
    (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model
        (liftM (CostSpec.query (.inl (.inr (.inl (blk parameter data message ρ))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
          else signCostSourceLoop parameter data message attempts) budget state] *
        V out.1.2.1 ≤
      (state.cache (blk parameter data message ρ)).elim
        (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if Landed parameter (blockIndex u0) then gf (viewOf u0) else bound))
        (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
          else bound) := by
  have hfinish : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ → s'.cache (blk parameter data message ρ) = some u0 →
      Landed parameter (blockIndex u0) →
      ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) b s'] *
          V out.1.2.1 ≤
        pairWeight parameter data message reference gf gp ρ u0 := by
    intro s' u0 b hrel' hs' hl
    calc _ ≤ ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) b s'] *
          pairWeight parameter data message reference gf gp ρ u0 := by
          refine ENNReal.tsum_le_tsum fun out => ?_
          by_cases hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s')
          · exact mul_le_mul_right (hVfin s' u0 b hrel' hs' hl out hout) _
          · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
      _ ≤ _ := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' tsum_probOutput_le_one
  rw [interp_ordinary]
  split_ifs with h1
  · rw [ordinaryStep, hparse ρ]
    simp only
    rw [tsum_probOutput_bind_mul]
    simp only [tsum_probOutput_map_mul]
    cases hc : state.cache (blk parameter data message ρ) with
    | some u0 =>
        rw [readOutside_cached _ state u0 hc, tsum_probOutput_pure_mul]
        simp only [Option.elim]
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          have href : reference.cache (blk parameter data message ρ) = some u0 := by
            rcases hrel ρ with h | ⟨_, u, hu, hnl⟩
            · rw [← h]; exact hc
            · rw [hc] at hu; cases hu; exact absurd hl hnl
          refine le_trans (hfinish state u0 _ (fun ρ' _ => hrel ρ') hc hl) (le_of_eq ?_)
          simp [pairWeight, poolValue, href, hl]
        · rw [if_neg hl, if_neg hl]
          exact hih state hrel (Nat.le_succ _) _
    | none =>
        rw [readOutside_fresh _ state hc, tsum_probOutput_map_mul]
        simp only [Option.elim]
        have href : reference.cache (blk parameter data message ρ) = none := by
          rcases hrel ρ with h | ⟨h, _⟩
          · rw [← h]; exact hc
          · exact h
        refine ENNReal.tsum_le_tsum fun u0 => mul_le_mul_right ?_ _
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          refine le_trans (hfinish _ u0 _ (fun ρ' hρ' => by
              rw [show (state.store (blk parameter data message ρ) u0).cache (blk parameter data message ρ') =
                state.cache (blk parameter data message ρ') from
                store_cache_ne state _ _ (blk_ne_of_ne parameter data message hρ') u0]
              exact hrel ρ')
            (by simp [DebtState.store]) hl) (le_of_eq ?_)
          simp only [pairWeight, href, if_true, if_pos hl]
        · rw [if_neg hl, if_neg hl]
          exact hih _ (related_store parameter data message reference state hrel ρ hc u0 hl)
            (cachedCount_store parameter data message state ρ u0) _
  · rw [tsum_probOutput_pure_mul]
    change V [] ≤ _
    rw [hV0]
    exact zero_le

/-- **Fair share of the grinding signer, for any reveal weight of all runs.** With `n` cached landed pairs of the message in the
reference state, the signed pair's weight is at most the fresh average `a` plus `e` times the pool's
excess `S - n a`, whenever `2^-128 ≤ e (n 2^-128 + (2^128 - Cmax) 2^-128 landing)`. -/
theorem loop_boundV
    (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (V : List Coordinate → ℝ≥0∞)
    (hV0 : V [] = 0)
    (hVfin : ∀ (ρ : Randomness) (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ → s'.cache (blk parameter data message ρ) = some u0 →
      Landed parameter (blockIndex u0) →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        V out.1.2.1 ≤ pairWeight parameter data message reference gf gp ρ u0)
    (B : ℝ≥0∞) (hB : B ≠ ⊤) (hgf : ∀ v, gf v ≤ B) (hgp : ∀ ρ v, gp ρ v ≤ B)
    (e : ℝ≥0∞) (he : e ≠ ⊤) (Cmax : ℕ) (hC : Cmax ≤ 2 ^ 128)
    (hu : ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ ≤
      e * ((landedCount parameter data message reference : ℝ≥0∞) * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ +
        (((2 ^ 128 - Cmax : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞)) * ForestPrice.landing)) :
    ∀ attempts budget state, Related parameter data message reference state →
      cachedCount parameter data message state + attempts ≤ Cmax →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts) budget state] *
          V out.1.2.1 ≤
        Domination.freshAvg Finset.univ gf + e * (∑ ρ, poolValue parameter data message reference gp ρ -
          (landedCount parameter data message reference : ℝ≥0∞) * Domination.freshAvg Finset.univ gf) := by
  set S := ∑ ρ, poolValue parameter data message reference gp ρ with hS
  set a := Domination.freshAvg Finset.univ gf with ha
  set n : ℝ≥0∞ := (landedCount parameter data message reference : ℝ≥0∞) with hn
  set Bnd := a + e * (S - n * a) with hBnd
  intro attempts
  induction attempts with
  | zero =>
      intro budget state hrel _
      change ∑' out, Pr[= out | interp tg initial model (pure none) budget state] *
        V out.1.2.1 ≤ _
      rw [interp_pure, tsum_probOutput_pure_mul]
      change V [] ≤ _
      rw [hV0]
      exact bot_le
  | succ attempts ih =>
      intro budget state hrel hcount
      rw [signCostSourceLoop_succ, interp_liftProb_bind, tsum_probOutput_bind_mul]
      have htrial := fun ρ => trial_boundV tg initial model parameter data message hparse reference ρ gf gp V
        hV0 (hVfin ρ) Bnd state hrel attempts (fun s' hs' hcs b => ih b s' hs' (by omega)) budget
      refine le_trans (ENNReal.tsum_le_tsum fun ρ => mul_le_mul_right (htrial ρ) _) ?_
      set u : ℝ≥0∞ := ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ with hudef
      have hpr : ∀ ρ, Pr[= ρ | ($ᵗ Randomness : ProbComp Randomness)] = u := by
        intro ρ
        rw [probOutput_uniformSample, card_randomness]
      simp only [hpr, ENNReal.tsum_mul_left]
      rw [tsum_fintype]
      set Fr := Finset.univ.filter fun ρ : Randomness => state.cache (blk parameter data message ρ) = none
      set NL := Finset.univ.filter fun ρ : Randomness => ∃ u0,
        state.cache (blk parameter data message ρ) = some u0 ∧ ¬Landed parameter (blockIndex u0)
      set LP := Finset.univ.filter fun ρ : Randomness => ∃ u0,
        reference.cache (blk parameter data message ρ) = some u0 ∧ Landed parameter (blockIndex u0)
      set fresh := ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if Landed parameter (blockIndex u0) then gf (viewOf u0) else Bnd)
      have hpoint : ∀ ρ, (state.cache (blk parameter data message ρ)).elim fresh
          (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
            else Bnd) ≤
          poolValue parameter data message reference gp ρ + (if ρ ∈ NL then Bnd else 0) +
            (if ρ ∈ Fr then fresh else 0) := by
        intro ρ
        cases hc : state.cache (blk parameter data message ρ) with
        | none =>
            have hFr : ρ ∈ Fr := by simp [Fr, hc]
            simp only [Option.elim, if_pos hFr]
            exact le_add_self
        | some u0 =>
            have hFr : ρ ∉ Fr := by simp [Fr, hc]
            simp only [Option.elim, if_neg hFr, add_zero]
            split_ifs with hl hNL
            · exact le_self_add
            · exact le_self_add
            · exact le_add_self
            · rename_i hnot
              exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, u0, hc, hl⟩) hnot
      have hsum : ∑ ρ, (state.cache (blk parameter data message ρ)).elim fresh
          (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
            else Bnd) ≤ S + (NL.card : ℝ≥0∞) * Bnd + (Fr.card : ℝ≥0∞) * fresh := by
        refine le_trans (Finset.sum_le_sum fun ρ _ => hpoint ρ) (le_of_eq ?_)
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
          Finset.univ_inter, Finset.univ_inter, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      have hfreshEq : fresh = ForestPrice.landing * a + (1 - ForestPrice.landing) * Bnd := by
        have hsplit : fresh = (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (if Landed parameter (blockIndex u0) then gf (viewOf u0) else 0)) +
            Bnd * ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (if Landed parameter (blockIndex u0) then 0 else 1) := by
          rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
          refine tsum_congr fun u0 => ?_
          split_ifs
          · simp
          · simp [mul_comm]
        rw [hsplit, unlanded_mass parameter, fresh_view_mean parameter gf]
        ring
      have hpool : ∀ ρ, poolValue parameter data message reference gp ρ ≤ B := by
        intro ρ
        unfold poolValue
        cases reference.cache (blk parameter data message ρ) with
        | none => exact bot_le
        | some u0 =>
            simp only [Option.elim]
            split_ifs
            · exact hgp _ _
            · exact bot_le
      have hSfin : S ≠ ⊤ := ENNReal.sum_ne_top.2 fun ρ _ => ne_top_of_le_ne_top hB (hpool ρ)
      have hafin : a ≠ ⊤ := Domination.freshAvg_ne_top Finset.univ_nonempty fun v => ne_top_of_le_ne_top hB (hgf v)
      have hcard : Fr.card + cachedCount parameter data message state = 2 ^ 128 := by
        rw [← card_randomness]
        exact Finset.card_filter_add_card_filter_not _
      have hdisj : LP.card + NL.card + Fr.card ≤ 2 ^ 128 := by
        rw [← card_randomness, ← Finset.card_univ]
        have h1 : Disjoint LP NL := by
          refine Finset.disjoint_left.2 fun ρ h1 h2 => ?_
          obtain ⟨_, u0, hr, hl⟩ := Finset.mem_filter.1 h1
          obtain ⟨_, u1, hs, hnl⟩ := Finset.mem_filter.1 h2
          rcases hrel ρ with h | ⟨h, _⟩
          · rw [h, hr] at hs; cases hs; exact hnl hl
          · rw [h] at hr; cases hr
        have h2 : Disjoint (LP ∪ NL) Fr := by
          refine Finset.disjoint_left.2 fun ρ h1 h2 => ?_
          have hnone := (Finset.mem_filter.1 h2).2
          rcases Finset.mem_union.1 h1 with h1 | h1
          · obtain ⟨_, u0, hr, _⟩ := Finset.mem_filter.1 h1
            rcases hrel ρ with h | ⟨h, _⟩
            · rw [h, hr] at hnone; cases hnone
            · rw [h] at hr; cases hr
          · obtain ⟨_, u1, hs, _⟩ := Finset.mem_filter.1 h1
            rw [hs] at hnone; cases hnone
        rw [← Finset.card_union_of_disjoint h1, ← Finset.card_union_of_disjoint h2]
        exact Finset.card_le_univ _
      have hland1 : ForestPrice.landing ≤ 1 := ForestPrice.landing_le_one
      have hu2 : u * ((2 ^ 128 : ℕ) : ℝ≥0∞) = 1 := ENNReal.inv_mul_cancel (by simp) (by simp)
      have hnLP : n = (LP.card : ℝ≥0∞) := rfl
      have hnNF : n * u + u * (NL.card : ℝ≥0∞) + u * (Fr.card : ℝ≥0∞) ≤ 1 := by
        rw [hnLP, mul_comm _ u, ← mul_add, ← mul_add, ← hu2]
        gcongr
        exact_mod_cast hdisj
      have hu' : u ≤ e * (n * u + u * (Fr.card : ℝ≥0∞) * ForestPrice.landing) := by
        refine le_trans hu ?_
        gcongr
        rw [ENNReal.div_eq_inv_mul]
        gcongr
        exact_mod_cast (by omega : 2 ^ 128 - Cmax ≤ Fr.card)
      have hnt : n ≠ ⊤ := ENNReal.natCast_ne_top _
      have hut : u ≠ ⊤ := by simp [hudef]
      calc u * ∑ ρ, (state.cache (blk parameter data message ρ)).elim fresh
            (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
              else Bnd)
          ≤ u * (S + (NL.card : ℝ≥0∞) * Bnd + (Fr.card : ℝ≥0∞) * fresh) := mul_le_mul_right hsum u
        _ = u * S + (u * (NL.card : ℝ≥0∞)) * Bnd + (u * (Fr.card : ℝ≥0∞)) *
              (ForestPrice.landing * a + (1 - ForestPrice.landing) * Bnd) := by
            rw [hfreshEq]
            ring
        _ ≤ Bnd := loop_arith a S e u n _ _ ForestPrice.landing hafin hSfin he hnt hut hnNF hland1 hu'

end LoopV

end LeanForest.Security.GraphView
