import LeanForest.BridgeSatW
import LeanForest.BridgeSignerForest

/-! The fair-share bounds of the grinding signer, weighted by the final survival weight. The
message-digest blocks are untargeted, so their reads keep the weight; everything after the digest
read of the final assembly lowers it in expectation. Each bound of `BridgeSignerForest` therefore
holds with the integrand multiplied by the final weight and the bound multiplied by the initial
weight. -/

open OracleComp OracleSpec ENNReal

namespace LeanForest.Security.GraphView

open LeanSphincs.Security
open Concrete Completeness Prefix HiddenGraph HiddenCost HiddenDebt ForestSigner

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable [Params]

section LoopSW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

/-- **Final assembly, one cached block, weighted.** -/
theorem finish_bound₁W (randomness : Randomness)
    (hparse : model.parse (blk parameter data message randomness) = none)
    (state : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput)
    (hc0 : state.cache (blk parameter data message randomness) = some u0)
    (g : HashOutput → ℝ≥0∞) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message randomness) budget state] *
        (weight tg initial out.2 * (if out.1.1.isSome then
          (out.2.cache (blk parameter data message randomness)).elim 0 g else 0)) ≤
      weight tg initial state * g u0 := by
  rw [finishCostSource_eq, interp_ordinary]
  split_ifs with h0
  · rw [ordinaryStep, hparse]
    simp only
    rw [readOutside_cached _ state u0 hc0, pure_bind, tsum_probOutput_map_mul]
    refine interp_weight_mul_leW tg initial model _ _ state _ _ fun out hout => ?_
    have hk0 := interp_avoids_cache tg initial model _ _ (avoids_mono (fun x hx => by
        subst hx; exact msgInput_digestInput parameter data.root message randomness)
      (avoids_finishRest parameter data message randomness _)) _ state out hout
      (blk parameter data message randomness) rfl
    split_ifs
    · rw [hk0, hc0]; rfl
    · exact bot_le
  · rw [tsum_probOutput_pure_mul]
    simp

/-- The arithmetic of one round of trials: the averaged per-randomizer bounds sum to `Bnd`. -/
theorem trials_sum_le
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (B : ℝ≥0∞) (hB : B ≠ ⊤) (hgf : ∀ v, gf v ≤ B) (hgp : ∀ ρ v, gp ρ v ≤ B)
    (e : ℝ≥0∞) (he : e ≠ ⊤) (Cmax : ℕ)
    (hu : ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ ≤
      e * ((landedCount parameter data message reference : ℝ≥0∞) * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ +
        (((2 ^ 128 - Cmax : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞)) * ForestPrice.landing))
    (state : DebtState HashInput HashOutput Coordinate) (hrel : Related parameter data message reference state)
    (hcount : cachedCount parameter data message state + 1 ≤ Cmax) :
    ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ * ∑ ρ, (state.cache (blk parameter data message ρ)).elim
        (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if Landed parameter (blockIndex u0) then gf (viewOf u0) else
            Domination.freshAvg Finset.univ gf + e * (∑ ρ, poolValue parameter data message reference gp ρ -
              (landedCount parameter data message reference : ℝ≥0∞) * Domination.freshAvg Finset.univ gf)))
        (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
          else Domination.freshAvg Finset.univ gf + e * (∑ ρ, poolValue parameter data message reference gp ρ -
            (landedCount parameter data message reference : ℝ≥0∞) * Domination.freshAvg Finset.univ gf)) ≤
      Domination.freshAvg Finset.univ gf + e * (∑ ρ, poolValue parameter data message reference gp ρ -
        (landedCount parameter data message reference : ℝ≥0∞) * Domination.freshAvg Finset.univ gf) := by
  set S := ∑ ρ, poolValue parameter data message reference gp ρ with hS
  set a := Domination.freshAvg Finset.univ gf with ha
  set n : ℝ≥0∞ := (landedCount parameter data message reference : ℝ≥0∞) with hn
  set Bnd := a + e * (S - n * a) with hBnd
  set u : ℝ≥0∞ := ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ with hudef
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

/-- **One grinding trial, weighted.** -/
theorem trial_boundSW
    (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (hkind : ∀ ρ, tg.kind (blk parameter data message ρ) = .none)
    (reference : DebtState HashInput HashOutput Coordinate) (ρ : Randomness)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (V : Option (Option Signature) → DebtState HashInput HashOutput Coordinate → ℝ≥0∞)
    (hVabort : ∀ s', V none s' = 0)
    (hVfin : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ → s'.cache (blk parameter data message ρ) = some u0 →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        V out.1.1 out.2 ≤ (if out.1.1.isSome then (out.2.cache (blk parameter data message ρ)).elim 0
          (pairWeight parameter data message reference gf gp ρ) else 0))
    (bound : ℝ≥0∞) (state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state) (attempts : ℕ)
    (hih : ∀ s', Related parameter data message reference s' →
      cachedCount parameter data message s' ≤ cachedCount parameter data message state + 1 → ∀ b,
        ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts) b s'] *
          (weight tg initial out.2 * V out.1.1 out.2) ≤ weight tg initial s' * bound)
    (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model
        (liftM (CostSpec.query (.inl (.inr (.inl (blk parameter data message ρ))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
          else signCostSourceLoop parameter data message attempts) budget state] *
        (weight tg initial out.2 * V out.1.1 out.2) ≤
      weight tg initial state * (state.cache (blk parameter data message ρ)).elim
        (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if Landed parameter (blockIndex u0) then gf (viewOf u0) else bound))
        (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
          else bound) := by
  have hfinish : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ → s'.cache (blk parameter data message ρ) = some u0 →
      ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) b s'] *
          (weight tg initial out.2 * V out.1.1 out.2) ≤
        weight tg initial s' * pairWeight parameter data message reference gf gp ρ u0 := by
    intro s' u0 b hrel' hs'
    refine le_trans (ENNReal.tsum_le_tsum fun out => ?_) (finish_bound₁W tg initial model parameter data message ρ
      (hparse ρ) s' u0 hs' _ b)
    by_cases hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s')
    · exact mul_le_mul_right (mul_le_mul_right (hVfin s' u0 b hrel' hs' out hout) _) _
    · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
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
          refine le_trans (hfinish state u0 _ (fun ρ' _ => hrel ρ') hc) (le_of_eq ?_)
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
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun u0 => ?_
        rw [mul_left_comm]
        refine mul_le_mul_right ?_ _
        have hw : weight tg initial (state.store (blk parameter data message ρ) u0) = weight tg initial state :=
          weight_store_untargetedW tg initial state _ u0 (hkind ρ)
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          refine le_trans (hfinish _ u0 _ (fun ρ' hρ' => by
              rw [show (state.store (blk parameter data message ρ) u0).cache (blk parameter data message ρ') =
                state.cache (blk parameter data message ρ') from
                store_cache_ne state _ _ (blk_ne_of_ne parameter data message hρ') u0]
              exact hrel ρ')
            (by simp [DebtState.store])) (le_of_eq ?_)
          rw [hw]
          simp only [pairWeight, href, if_true, if_pos hl]
        · rw [if_neg hl, if_neg hl]
          have h := hih _ (related_store parameter data message reference state hrel ρ hc u0 hl)
            (cachedCount_store parameter data message state ρ u0) (budget - 1)
          rwa [hw] at h
  · rw [tsum_probOutput_pure_mul]
    rw [hVabort, mul_zero]
    exact zero_le

/-- **Fair share of the grinding signer, weighted.** -/
theorem loop_boundSW
    (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (hkind : ∀ ρ, tg.kind (blk parameter data message ρ) = .none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (V : Option (Option Signature) → DebtState HashInput HashOutput Coordinate → ℝ≥0∞)
    (hVabort : ∀ s', V none s' = 0)
    (hVnone : ∀ s' : DebtState HashInput HashOutput Coordinate, Related parameter data message reference s' →
      V (some none) s' = 0)
    (hVfin : ∀ (ρ : Randomness) (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ → s'.cache (blk parameter data message ρ) = some u0 →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        V out.1.1 out.2 ≤ (if out.1.1.isSome then (out.2.cache (blk parameter data message ρ)).elim 0
          (pairWeight parameter data message reference gf gp ρ) else 0))
    (B : ℝ≥0∞) (hB : B ≠ ⊤) (hgf : ∀ v, gf v ≤ B) (hgp : ∀ ρ v, gp ρ v ≤ B)
    (e : ℝ≥0∞) (he : e ≠ ⊤) (Cmax : ℕ)
    (hu : ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ ≤
      e * ((landedCount parameter data message reference : ℝ≥0∞) * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ +
        (((2 ^ 128 - Cmax : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞)) * ForestPrice.landing)) :
    ∀ attempts budget state, Related parameter data message reference state →
      cachedCount parameter data message state + attempts ≤ Cmax →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts) budget state] *
          (weight tg initial out.2 * V out.1.1 out.2) ≤
        weight tg initial state * (Domination.freshAvg Finset.univ gf + e * (∑ ρ, poolValue parameter data message
          reference gp ρ - (landedCount parameter data message reference : ℝ≥0∞) *
            Domination.freshAvg Finset.univ gf)) := by
  set Bnd := Domination.freshAvg Finset.univ gf + e * (∑ ρ, poolValue parameter data message reference gp ρ -
    (landedCount parameter data message reference : ℝ≥0∞) * Domination.freshAvg Finset.univ gf) with hBnd
  intro attempts
  induction attempts with
  | zero =>
      intro budget state hrel _
      change ∑' out, Pr[= out | interp tg initial model (pure none) budget state] *
        (weight tg initial out.2 * V out.1.1 out.2) ≤ _
      rw [interp_pure, tsum_probOutput_pure_mul]
      change weight tg initial state * V (some none) state ≤ _
      rw [hVnone state hrel, mul_zero]
      exact bot_le
  | succ attempts ih =>
      intro budget state hrel hcount
      rw [signCostSourceLoop_succ, interp_liftProb_bind, tsum_probOutput_bind_mul]
      have htrial := fun ρ => trial_boundSW tg initial model parameter data message hparse hkind reference ρ gf gp V
        hVabort (hVfin ρ) Bnd state hrel attempts (fun s' hs' hcs b => ih b s' hs' (by omega)) budget
      refine le_trans (ENNReal.tsum_le_tsum fun ρ => mul_le_mul_right (htrial ρ) _) ?_
      have hpr : ∀ ρ, Pr[= ρ | ($ᵗ Randomness : ProbComp Randomness)] = ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ := by
        intro ρ
        rw [probOutput_uniformSample, card_randomness]
      simp only [hpr]
      rw [tsum_fintype]
      simp only [mul_left_comm _ (weight tg initial state)]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      exact mul_le_mul_right (trials_sum_le parameter data message reference gf gp B hB hgf hgp e he Cmax hu
        state hrel (by omega)) _

/-- The combined weight of a non-signing outcome vanishes. -/
theorem comb_none (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (s' : DebtState HashInput HashOutput Coordinate) (hrel : Related parameter data message reference s') :
    freshNewWeight parameter data message reference gf ((some none, [], [], []), s') +
      outWeight parameter data message reference 0 gp ((some none, [], [], []), s') = 0 := by
  simp only [freshNewWeight, outWeight, Option.isSome_some, if_true, add_zero]
  refine Finset.sum_eq_zero fun ρ _ => ?_
  split_ifs with hn
  · rcases hrel ρ with h | ⟨_, u, hu', hnl⟩
    · rw [h, hn]; rfl
    · simp only [hu', Option.elim, if_neg hnl]
  · rfl

/-- The combined weight of a completed assembly is the weight of its own pair. -/
theorem comb_fin (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (ρ : Randomness) (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ)
    (hoff : RelatedOff parameter data message reference s' ρ) (hs0 : s'.cache (blk parameter data message ρ) = some u0)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s')) :
    freshNewWeight parameter data message reference gf ((out.1.1, [], [], []), out.2) +
      outWeight parameter data message reference 0 gp ((out.1.1, [], [], []), out.2) ≤
      (if out.1.1.isSome then (out.2.cache (blk parameter data message ρ)).elim 0
        (pairWeight parameter data message reference gf gp ρ) else 0) := by
  have hkeep := finish_keeps_msg tg initial model parameter data message hparse ρ b s' u0 hs0 out hout
  have hk : ∀ ρ', out.2.cache (blk parameter data message ρ') = s'.cache (blk parameter data message ρ') :=
    fun ρ' => hkeep _ (msgInput_digestInput parameter data.root message ρ')
  by_cases hsome : out.1.1.isSome
  · rw [if_pos hsome, hk ρ, hs0]
    simp only [Option.elim]
    have hfresh : freshNewWeight parameter data message reference gf ((out.1.1, [], [], []), out.2) =
        if reference.cache (blk parameter data message ρ) = none then
          (if Landed parameter (blockIndex u0) then gf (viewOf u0) else 0) else 0 := by
      simp only [freshNewWeight, if_pos hsome]
      rw [Finset.sum_eq_single ρ]
      · simp only [hk ρ, hs0, Option.elim]
      · intro ρ' _ hne
        split_ifs with hn
        · rcases hoff ρ' hne with h | ⟨_, u, hu', hnl⟩
          · rw [hk ρ', h, hn]; rfl
          · simp only [hk ρ', hu', Option.elim, if_neg hnl]
        · rfl
      · intro h; exact absurd (Finset.mem_univ ρ) h
    rw [hfresh]
    have hout' : outWeight parameter data message reference 0 gp ((out.1.1, [], [], []), out.2) ≤
        if reference.cache (blk parameter data message ρ) = none then 0 else gp ρ (viewOf u0) := by
      have := outWeight_finish_le tg initial model parameter data message reference 0 gp ρ b s' out hout
      simp only [if_pos hsome, hk ρ, hs0, Option.elim, pairWeight] at this
      refine le_trans (le_of_eq ?_) (le_trans this (le_of_eq ?_))
      · rfl
      · split_ifs <;> rfl
    refine le_trans (add_le_add_right hout' _) (le_of_eq ?_)
    simp only [pairWeight]
    split_ifs <;> simp
  · rw [if_neg hsome]
    simp only [freshNewWeight, if_neg hsome, zero_add]
    unfold outWeight
    cases hr : out.1.1 with
    | none => rfl
    | some r => simp [hr] at hsome

/-- **Fair share of the grinding signer, with the fresh pairs it completes, weighted.** -/
theorem loop_bound_combSW
    (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (hkind : ∀ ρ, tg.kind (blk parameter data message ρ) = .none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (B : ℝ≥0∞) (hB : B ≠ ⊤) (hgf : ∀ v, gf v ≤ B) (hgp : ∀ ρ v, gp ρ v ≤ B)
    (e : ℝ≥0∞) (he : e ≠ ⊤) (Cmax : ℕ)
    (hu : ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ ≤
      e * ((landedCount parameter data message reference : ℝ≥0∞) * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ +
        (((2 ^ 128 - Cmax : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞)) * ForestPrice.landing)) :
    ∀ attempts budget state, Related parameter data message reference state →
      cachedCount parameter data message state + attempts ≤ Cmax →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts) budget state] *
          (weight tg initial out.2 * (freshNewWeight parameter data message reference gf out +
            outWeight parameter data message reference 0 gp out)) ≤
        weight tg initial state * (Domination.freshAvg Finset.univ gf + e * (∑ ρ, poolValue parameter data message
          reference gp ρ - (landedCount parameter data message reference : ℝ≥0∞) *
            Domination.freshAvg Finset.univ gf)) :=
  loop_boundSW tg initial model parameter data message hparse hkind reference gf gp
    (fun r s' => freshNewWeight parameter data message reference gf ((r, [], [], []), s') +
      outWeight parameter data message reference 0 gp ((r, [], [], []), s'))
    (fun _ => by simp [freshNewWeight, outWeight]) (comb_none parameter data message reference gf gp)
    (fun ρ s' u0 b hoff hs0 out hout => comb_fin tg initial model parameter data message hparse reference gf gp
      ρ s' u0 b hoff hs0 out hout) B hB hgf hgp e he Cmax hu

end LoopSW

end LeanForest.Security.GraphView
