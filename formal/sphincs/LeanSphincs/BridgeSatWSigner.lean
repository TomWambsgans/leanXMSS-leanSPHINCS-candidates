import LeanSphincs.BridgeSatW
import LeanSphincs.BridgeSignerFors

/-! The fair-share bounds of the grinding signer, weighted by the final survival weight. The
message-digest blocks are untargeted, so their reads keep the weight; everything after the two
digest reads of the final assembly lowers it in expectation. Each bound of `BridgeSignerFors`
therefore holds with the integrand multiplied by the final weight and the bound multiplied by
the initial weight. The signer samples one base randomizer and walks `R0, R0 + 1, ...`: the bounds
are by induction over the walk, as in `BridgeSignerFors`. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.GraphView

open Concrete Completeness Prefix HiddenGraph HiddenCost HiddenDebt ForsSigner

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] digestAttemptLimit

variable [Params]

section FinishW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- **Final assembly, both blocks, weighted.** -/
theorem finish_bound₂W (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness)
    (hparse : ∀ call, model.parse (Security.digestInput parameter data.root message randomness call) = none)
    (hkind : ∀ call, tg.kind (Security.digestInput parameter data.root message randomness call) = .none)
    (state : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput)
    (hc0 : state.cache (Security.digestInput parameter data.root message randomness 0) = some u0)
    (g : HashOutput → HashOutput → ℝ≥0∞) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message randomness) budget state] *
        (weight tg initial out.2 * (if out.1.1.isSome then
          (out.2.cache (Security.digestInput parameter data.root message randomness 0)).elim 0 (fun a =>
            (out.2.cache (Security.digestInput parameter data.root message randomness 1)).elim 0 (g a)) else 0)) ≤
      weight tg initial state * (state.cache (Security.digestInput parameter data.root message randomness 1)).elim
        (∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * g u0 u) (g u0) := by
  rw [finishCostSource_eq]
  exact two_reads_bound₂W tg initial model _ _ (digestInput_ne parameter data.root message randomness)
    (hparse 0) (hparse 1) (hkind 1) state u0 hc0
    (fun a b => finishRest parameter data message randomness (truncateMessageDigest a b))
    (fun a b => avoids_mono (fun x hx => by
        rcases hx with rfl | rfl
        · exact msgInput_digestInput parameter data.root message randomness 0
        · exact msgInput_digestInput parameter data.root message randomness 1)
      (avoids_finishRest parameter data message randomness _)) g budget

end FinishW

section LoopW

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

/-- **One grinding trial, weighted.** -/
theorem trial_boundW
    (hparse : ∀ ρ call, model.parse (blk parameter data message ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (blk parameter data message ρ call) = .none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (hnob1 : ∀ ρ, reference.cache (blk parameter data message ρ 0) = none →
      reference.cache (blk parameter data message ρ 1) = none)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (bound : ℝ≥0∞) (state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state) (cont : OracleComp CostSpec (Option Signature))
    (ρ : Randomness)
    (hih : ∀ s', (s' = state ∨ ∃ u, ¬Landed parameter (blockIndex u) ∧
        state.cache (blk parameter data message ρ 0) = none ∧ s' = state.store (blk parameter data message ρ 0) u) →
      ∀ b, ∑' out, Pr[= out | interp tg initial model cont b s'] *
          (weight tg initial out.2 * outWeight parameter data message reference gf gp out) ≤
            weight tg initial s' * bound)
    (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model
        (liftM (CostSpec.query (.inl (.inr (.inl (blk parameter data message ρ 0))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
          else cont) budget state] *
        (weight tg initial out.2 * outWeight parameter data message reference gf gp out) ≤
      weight tg initial state * (state.cache (blk parameter data message ρ 0)).elim
        (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if Landed parameter (blockIndex u0) then
            ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * gf (viewOf u0 u) else bound))
        (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
          else bound) := by
  have hfinish : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      s'.cache (blk parameter data message ρ 0) = some u0 →
      ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) b s'] *
          (weight tg initial out.2 * outWeight parameter data message reference gf gp out) ≤
        weight tg initial s' * (s'.cache (blk parameter data message ρ 1)).elim
          (∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
            pairWeight parameter data message reference gf gp ρ u0 u)
          (pairWeight parameter data message reference gf gp ρ u0) := by
    intro s' u0 b hs'
    refine le_trans (ENNReal.tsum_le_tsum fun out => ?_) (finish_bound₂W tg initial model parameter data message ρ
      (hparse ρ) (hkind ρ) s' u0 hs' _ b)
    by_cases hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s')
    · exact mul_le_mul_right (mul_le_mul_right (outWeight_finish_le tg initial model parameter data message
        reference gf gp ρ b s' out hout) _) _
    · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
  rw [interp_ordinary]
  split_ifs with h1
  · rw [ordinaryStep, hparse ρ 0]
    simp only
    rw [tsum_probOutput_bind_mul]
    simp only [tsum_probOutput_map_mul]
    cases hc : state.cache (blk parameter data message ρ 0) with
    | some u0 =>
        rw [readOutside_cached _ state u0 hc, tsum_probOutput_pure_mul]
        simp only [Option.elim]
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          have href : reference.cache (blk parameter data message ρ 0) = some u0 := by
            rcases hrel.2 ρ with h | ⟨_, u, hu, hnl⟩
            · rw [← h]; exact hc
            · rw [hc] at hu; cases hu; exact absurd hl hnl
          refine le_trans (hfinish state u0 _ hc) (le_of_eq ?_)
          have hpw : pairWeight parameter data message reference gf gp ρ u0 = fun u1 => gp ρ (viewOf u0 u1) := by
            funext u1
            simp [pairWeight, href]
          rw [hpw]
          simp only [poolValue, href, Option.elim, if_pos hl, hrel.1 ρ]
        · rw [if_neg hl, if_neg hl]
          exact hih state (Or.inl rfl) _
    | none =>
        rw [readOutside_fresh _ state hc, tsum_probOutput_map_mul]
        simp only [Option.elim]
        have href : reference.cache (blk parameter data message ρ 0) = none := by
          rcases hrel.2 ρ with h | ⟨h, _⟩
          · rw [← h]; exact hc
          · exact h
        have hb1 : state.cache (blk parameter data message ρ 1) = none := by
          rw [hrel.1 ρ]; exact hnob1 ρ href
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun u0 => ?_
        rw [mul_left_comm]
        refine mul_le_mul_right ?_ _
        have hw : weight tg initial (state.store (blk parameter data message ρ 0) u0) = weight tg initial state :=
          weight_store_untargetedW tg initial state _ u0 (hkind ρ 0)
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          refine le_trans (hfinish _ u0 _ (by simp [DebtState.store])) (le_of_eq ?_)
          have hne : blk parameter data message ρ 1 ≠ blk parameter data message ρ 0 :=
            Ne.symm (digestInput_ne parameter data.root message ρ)
          rw [store_cache_ne state _ _ hne u0, hb1, hw]
          simp only [Option.elim, pairWeight, href, if_true, if_pos hl]
        · rw [if_neg hl, if_neg hl]
          have h := hih _ (Or.inr ⟨u0, hl, hc, rfl⟩) (budget - 1)
          rwa [hw] at h
  · rw [tsum_probOutput_pure_mul]
    have h0 : outWeight parameter data message reference gf gp ((none, [], [], []), state) = 0 := rfl
    rw [h0, mul_zero]
    exact bot_le


/-- **The walk from a start, weighted.** -/
theorem walk_boundW
    (hparse : ∀ ρ call, model.parse (blk parameter data message ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (blk parameter data message ρ call) = .none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (hnob1 : ∀ ρ, reference.cache (blk parameter data message ρ 0) = none →
      reference.cache (blk parameter data message ρ 1) = none)
    (hlandb1 : ∀ ρ u0, reference.cache (blk parameter data message ρ 0) = some u0 →
      Landed parameter (blockIndex u0) → reference.cache (blk parameter data message ρ 1) ≠ none)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞) :
    ∀ attempts ρ budget state, attempts ≤ 2 ^ 128 → Related parameter data message reference state →
      (∀ j, j < attempts → state.cache (blk parameter data message ((fun x : Randomness => x + 1)^[j] ρ) 0) =
        reference.cache (blk parameter data message ((fun x : Randomness => x + 1)^[j] ρ) 0)) →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceWalk parameter data message attempts ρ) budget state] *
          (weight tg initial out.2 * outWeight parameter data message reference gf gp out) ≤
        weight tg initial state * Walk.val (fun x : Randomness => x + 1)
          (Walk.sOf ForsPrice.landing (stat parameter data message reference))
          (Walk.tOf ForsPrice.landing (stat parameter data message reference))
          (walkPay parameter data message reference gf gp) 0 attempts ρ := by
  intro attempts
  induction attempts with
  | zero =>
      intro ρ budget state _ _ _
      change ∑' out, Pr[= out | interp tg initial model (pure none) budget state] *
        (weight tg initial out.2 * outWeight parameter data message reference gf gp out) ≤ _
      rw [interp_pure, tsum_probOutput_pure_mul]
      have h0 : outWeight parameter data message reference gf gp ((some none, [], [], []), state) = 0 := rfl
      rw [h0, mul_zero]
      exact bot_le
  | succ attempts ih =>
      intro ρ budget state hatt hrel hpos
      set bound := Walk.val (fun x : Randomness => x + 1)
        (Walk.sOf ForsPrice.landing (stat parameter data message reference))
        (Walk.tOf ForsPrice.landing (stat parameter data message reference))
        (walkPay parameter data message reference gf gp) 0 attempts (ρ + 1) with hbound
      have hpos0 : state.cache (blk parameter data message ρ 0) = reference.cache (blk parameter data message ρ 0) :=
        hpos 0 (Nat.succ_pos _)
      have hih : ∀ s', (s' = state ∨ ∃ u, ¬Landed parameter (blockIndex u) ∧
          state.cache (blk parameter data message ρ 0) = none ∧ s' = state.store (blk parameter data message ρ 0) u) →
          ∀ b, ∑' out, Pr[= out | interp tg initial model (signCostSourceWalk parameter data message attempts (ρ + 1)) b s'] *
            (weight tg initial out.2 * outWeight parameter data message reference gf gp out) ≤
              weight tg initial s' * bound := by
        intro s' hs' b
        have hposS : ∀ j, j < attempts → state.cache (blk parameter data message ((fun x : Randomness => x + 1)^[j] (ρ + 1)) 0) =
            reference.cache (blk parameter data message ((fun x : Randomness => x + 1)^[j] (ρ + 1)) 0) := by
          intro j hj
          have := hpos (j + 1) (Nat.succ_lt_succ hj)
          simpa only [Function.iterate_succ_apply] using this
        rcases hs' with rfl | ⟨u, hu, hc, rfl⟩
        · exact ih (ρ + 1) b s' (by omega) hrel hposS
        · refine ih (ρ + 1) b _ (by omega) (related_store parameter data message reference state hrel ρ hc u hu)
            fun j hj => ?_
          have hne : (fun x : Randomness => x + 1)^[j] (ρ + 1) ≠ ρ := succ_iterate_ne ρ j (by omega)
          have hbl : blk parameter data message ((fun x : Randomness => x + 1)^[j] (ρ + 1)) 0 ≠
              blk parameter data message ρ 0 := fun h =>
            hne (payload_randomness_injective data.root message (tweakableInput_injective h).2.2)
          rw [store_cache_ne state _ _ hbl u]
          exact hposS j hj
      rw [signCostSourceWalk_succ]
      refine le_trans (trial_boundW tg initial model parameter data message hparse hkind reference hnob1 gf gp bound
        state hrel _ ρ hih budget) (mul_le_mul_right ?_ _)
      rw [hpos0]
      have hval : Walk.val (fun x : Randomness => x + 1)
          (Walk.sOf ForsPrice.landing (stat parameter data message reference))
          (Walk.tOf ForsPrice.landing (stat parameter data message reference))
          (walkPay parameter data message reference gf gp) 0 (attempts + 1) ρ =
          Walk.sOf ForsPrice.landing (stat parameter data message reference) ρ *
            walkPay parameter data message reference gf gp ρ +
          Walk.tOf ForsPrice.landing (stat parameter data message reference) ρ * bound := rfl
      rw [hval]
      cases hc : reference.cache (blk parameter data message ρ 0) with
      | none =>
          have hσ : stat parameter data message reference ρ = none := by simp [stat, hc]
          simp only [Option.elim, Walk.sOf, Walk.tOf, walkPay, hσ]
          exact le_of_eq (fresh_trial_eq parameter gf bound)
      | some u0 =>
          simp only [Option.elim]
          by_cases hl : Landed parameter (blockIndex u0)
          · obtain ⟨u1, h1⟩ := Option.ne_none_iff_exists'.1 (hlandb1 ρ u0 hc hl)
            have hσ : stat parameter data message reference ρ = some (some (viewOf u0 u1)) := by
              simp [stat, hc, hl, h1]
            simp only [if_pos hl, Walk.sOf, Walk.tOf, walkPay, hσ, one_mul, zero_mul, add_zero]
            simp [poolValue, hc, hl, h1]
          · have hσ : stat parameter data message reference ρ = some none := by simp [stat, hc, hl]
            simp only [if_neg hl, Walk.sOf, Walk.tOf, walkPay, hσ, one_mul, zero_mul, zero_add, le_refl]

/-- **The selection law of the grinding signer, weighted.** A uniform base, then the walk: the
expected weighted outcome of a signing call is the initial weight times the mean walk value over
the starts. -/
theorem loop_boundW
    (hparse : ∀ ρ call, model.parse (blk parameter data message ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (blk parameter data message ρ call) = .none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (hnob1 : ∀ ρ, reference.cache (blk parameter data message ρ 0) = none →
      reference.cache (blk parameter data message ρ 1) = none)
    (hlandb1 : ∀ ρ u0, reference.cache (blk parameter data message ρ 0) = some u0 →
      Landed parameter (blockIndex u0) → reference.cache (blk parameter data message ρ 1) ≠ none)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (attempts : ℕ) (hatt : attempts ≤ 2 ^ 128) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts) budget reference] *
        (weight tg initial out.2 * outWeight parameter data message reference gf gp out) ≤
      weight tg initial reference *
        (((Fintype.card Randomness : ℕ) : ℝ≥0∞)⁻¹ * ∑ ρ, Walk.val (fun x : Randomness => x + 1)
          (Walk.sOf ForsPrice.landing (stat parameter data message reference))
          (Walk.tOf ForsPrice.landing (stat parameter data message reference))
          (walkPay parameter data message reference gf gp) 0 attempts ρ) := by
  unfold signCostSourceLoop
  rw [interp_liftProb_bind, tsum_probOutput_bind_mul]
  have hpr : ∀ ρ, Pr[= ρ | ($ᵗ Randomness : ProbComp Randomness)] = ((Fintype.card Randomness : ℕ) : ℝ≥0∞)⁻¹ := by
    intro ρ
    rw [probOutput_uniformSample]
  simp only [hpr]
  rw [ENNReal.tsum_mul_left, tsum_fintype]
  set c : ℝ≥0∞ := ((Fintype.card Randomness : ℕ) : ℝ≥0∞)⁻¹ with hc
  set V : Randomness → ℝ≥0∞ := fun ρ => Walk.val (fun x : Randomness => x + 1)
    (Walk.sOf ForsPrice.landing (stat parameter data message reference))
    (Walk.tOf ForsPrice.landing (stat parameter data message reference))
    (walkPay parameter data message reference gf gp) 0 attempts ρ with hV
  have hwalk : ∀ ρ, ∑' out, Pr[= out | interp tg initial model (signCostSourceWalk parameter data message attempts ρ)
        budget reference] * (weight tg initial out.2 * outWeight parameter data message reference gf gp out) ≤
      weight tg initial reference * V ρ := fun ρ =>
    walk_boundW tg initial model parameter data message hparse hkind reference hnob1 hlandb1 gf gp attempts ρ
      budget reference hatt ⟨fun _ => rfl, fun _ => Or.inl rfl⟩ fun _ _ => rfl
  calc _ ≤ c * ∑ ρ, weight tg initial reference * V ρ :=
        mul_le_mul_right (Finset.sum_le_sum fun ρ _ => hwalk ρ) _
    _ = weight tg initial reference * (c * ∑ ρ, V ρ) := by
        rw [← Finset.mul_sum, mul_left_comm]

/-- **One trial, fresh pairs only, weighted.** -/
theorem trial_bound_freshW
    (hparse : ∀ ρ call, model.parse (blk parameter data message ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (blk parameter data message ρ call) = .none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (hnob1 : ∀ ρ, reference.cache (blk parameter data message ρ 0) = none →
      reference.cache (blk parameter data message ρ 1) = none)
    (hlandb1 : ∀ ρ u0, reference.cache (blk parameter data message ρ 0) = some u0 →
      Landed parameter (blockIndex u0) → reference.cache (blk parameter data message ρ 1) ≠ none)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (bound : ℝ≥0∞) (state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state) (cont : OracleComp CostSpec (Option Signature))
    (hih : ∀ s', Related parameter data message reference s' → ∀ b,
        ∑' out, Pr[= out | interp tg initial model cont b s'] *
          (weight tg initial out.2 * freshNewWeight parameter data message reference gf out) ≤
            weight tg initial s' * bound)
    (ρ : Randomness) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model
        (liftM (CostSpec.query (.inl (.inr (.inl (blk parameter data message ρ 0))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
          else cont) budget state] *
        (weight tg initial out.2 * freshNewWeight parameter data message reference gf out) ≤
      weight tg initial state * (state.cache (blk parameter data message ρ 0)).elim
        (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if Landed parameter (blockIndex u0) then
            ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * gf (viewOf u0 u) else bound))
        (fun u0 => if Landed parameter (blockIndex u0) then 0 else bound) := by
  rw [interp_ordinary]
  split_ifs with h1
  · rw [ordinaryStep, hparse ρ 0]
    simp only
    rw [tsum_probOutput_bind_mul]
    simp only [tsum_probOutput_map_mul]
    cases hc : state.cache (blk parameter data message ρ 0) with
    | some u0 =>
        rw [readOutside_cached _ state u0 hc, tsum_probOutput_pure_mul]
        simp only [Option.elim]
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          have href : reference.cache (blk parameter data message ρ 0) = some u0 := by
            rcases hrel.2 ρ with h | ⟨_, u, hu, hnl⟩
            · rw [← h]; exact hc
            · rw [hc] at hu; cases hu; exact absurd hl hnl
          have hb1 := hlandb1 ρ u0 href hl
          refine le_trans (le_of_eq (ENNReal.tsum_eq_zero.2 fun out => ?_)) bot_le
          change Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) (budget - 1) state] *
            (weight tg initial out.2 * freshNewWeight parameter data message reference gf out) = 0
          by_cases hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ)
            (budget - 1) state)
          · have := freshNewWeight_finish tg initial model parameter data message reference gf ρ _ state hrel.1 out hout
            rw [if_neg hb1] at this
            rw [nonpos_iff_eq_zero.1 this, mul_zero, mul_zero]
          · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul]
        · rw [if_neg hl, if_neg hl]
          exact hih state hrel _
    | none =>
        rw [readOutside_fresh _ state hc, tsum_probOutput_map_mul]
        simp only [Option.elim]
        have href : reference.cache (blk parameter data message ρ 0) = none := by
          rcases hrel.2 ρ with h | ⟨h, _⟩
          · rw [← h]; exact hc
          · exact h
        have hb1r : reference.cache (blk parameter data message ρ 1) = none := hnob1 ρ href
        have hb1 : state.cache (blk parameter data message ρ 1) = none := by rw [hrel.1 ρ]; exact hb1r
        rw [← ENNReal.tsum_mul_left]
        refine ENNReal.tsum_le_tsum fun u0 => ?_
        rw [mul_left_comm]
        refine mul_le_mul_right ?_ _
        have hw : weight tg initial (state.store (blk parameter data message ρ 0) u0) = weight tg initial state :=
          weight_store_untargetedW tg initial state _ u0 (hkind ρ 0)
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          have hs0 : (state.store (blk parameter data message ρ 0) u0).cache (blk parameter data message ρ 0) =
              some u0 := by
            simp [DebtState.store]
          have hb1rel : ∀ ρ', (state.store (blk parameter data message ρ 0) u0).cache (blk parameter data message ρ' 1) =
              reference.cache (blk parameter data message ρ' 1) := by
            intro ρ'
            rw [store_cache_ne state _ _ (blk_ne_of_ne parameter data message ρ' ρ 1 0 (Or.inr (by decide))) u0]
            exact hrel.1 ρ'
          set g' : HashOutput → HashOutput → ℝ≥0∞ := fun a u1 =>
            if Landed parameter (blockIndex a) then gf (viewOf a u1) else 0 with hg'
          calc _ ≤ ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) (budget - 1)
                (state.store (blk parameter data message ρ 0) u0)] *
                (weight tg initial out.2 * (if out.1.1.isSome then (out.2.cache (blk parameter data message ρ 0)).elim 0
                  (fun a => (out.2.cache (blk parameter data message ρ 1)).elim 0 (g' a)) else 0)) := by
                refine ENNReal.tsum_le_tsum fun out => ?_
                by_cases hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ)
                  (budget - 1) (state.store (blk parameter data message ρ 0) u0))
                · have := freshNewWeight_finish tg initial model parameter data message reference gf ρ _ _ hb1rel out hout
                  rw [if_pos hb1r] at this
                  exact mul_le_mul_right (mul_le_mul_right this _) _
                · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
            _ ≤ _ := finish_bound₂W tg initial model parameter data message ρ (hparse ρ) (hkind ρ) _ u0 hs0 g' _
            _ = _ := by
                rw [store_cache_ne state _ _ (blk_ne_of_ne parameter data message ρ ρ 1 0 (Or.inr (by decide))) u0,
                  hb1, hw]
                simp only [Option.elim, hg', if_pos hl]
        · rw [if_neg hl, if_neg hl]
          have h := hih _ (related_store parameter data message reference state hrel ρ hc u0 hl) (budget - 1)
          rwa [hw] at h
  · rw [tsum_probOutput_pure_mul]
    have h0 : freshNewWeight parameter data message reference gf ((none, [], [], []), state) = 0 := by
      simp only [freshNewWeight, Option.isSome_none]
      rfl
    rw [h0, mul_zero]
    exact bot_le

/-- Fresh pairs of the walk from any start, weighted. -/
theorem walk_bound_freshW
    (hparse : ∀ ρ call, model.parse (blk parameter data message ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (blk parameter data message ρ call) = .none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (hnob1 : ∀ ρ, reference.cache (blk parameter data message ρ 0) = none →
      reference.cache (blk parameter data message ρ 1) = none)
    (hlandb1 : ∀ ρ u0, reference.cache (blk parameter data message ρ 0) = some u0 →
      Landed parameter (blockIndex u0) → reference.cache (blk parameter data message ρ 1) ≠ none)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) :
    ∀ attempts ρ budget state, Related parameter data message reference state →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceWalk parameter data message attempts ρ) budget state] *
          (weight tg initial out.2 * freshNewWeight parameter data message reference gf out) ≤
        weight tg initial state * Domination.freshAvg Finset.univ gf := by
  set a := Domination.freshAvg Finset.univ gf with ha
  intro attempts
  induction attempts with
  | zero =>
      intro ρ budget state hrel
      change ∑' out, Pr[= out | interp tg initial model (pure none) budget state] *
        (weight tg initial out.2 * freshNewWeight parameter data message reference gf out) ≤ _
      rw [interp_pure, tsum_probOutput_pure_mul]
      have h0 : freshNewWeight parameter data message reference gf ((some none, [], [], []), state) = 0 := by
        unfold freshNewWeight
        simp only [Option.isSome_some, if_true]
        refine Finset.sum_eq_zero fun ρ _ => ?_
        split_ifs with h
        · rw [hrel.1 ρ, h]
          cases state.cache (blk parameter data message ρ 0) <;> rfl
        · rfl
      rw [h0, mul_zero]
      exact bot_le
  | succ attempts ih =>
      intro ρ budget state hrel
      rw [signCostSourceWalk_succ]
      refine le_trans (trial_bound_freshW tg initial model parameter data message hparse hkind reference hnob1
        hlandb1 gf a state hrel _ (fun s' hs' b => ih (ρ + 1) b s' hs') ρ budget) (mul_le_mul_right ?_ _)
      have hland1 : ForsPrice.landing ≤ 1 := by
        unfold ForsPrice.landing
        exact ENNReal.inv_le_one.2 (by exact_mod_cast Nat.one_le_two_pow)
      cases state.cache (blk parameter data message ρ 0) with
      | none =>
          simp only [Option.elim]
          rw [fresh_trial_eq parameter gf a, ← add_mul, add_tsub_cancel_of_le hland1, one_mul]
      | some u0 =>
          simp only [Option.elim]
          split_ifs
          · exact bot_le
          · exact le_rfl

/-- **Fresh pairs of the grinding signer, weighted.** -/
theorem loop_bound_freshW
    (hparse : ∀ ρ call, model.parse (blk parameter data message ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (blk parameter data message ρ call) = .none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (hnob1 : ∀ ρ, reference.cache (blk parameter data message ρ 0) = none →
      reference.cache (blk parameter data message ρ 1) = none)
    (hlandb1 : ∀ ρ u0, reference.cache (blk parameter data message ρ 0) = some u0 →
      Landed parameter (blockIndex u0) → reference.cache (blk parameter data message ρ 1) ≠ none)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) :
    ∀ attempts budget state, Related parameter data message reference state →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts) budget state] *
          (weight tg initial out.2 * freshNewWeight parameter data message reference gf out) ≤
        weight tg initial state * Domination.freshAvg Finset.univ gf := by
  intro attempts budget state hrel
  unfold signCostSourceLoop
  rw [interp_liftProb_bind, tsum_probOutput_bind_mul]
  calc _ ≤ ∑' ρ, Pr[= ρ | ($ᵗ Randomness : ProbComp Randomness)] *
          (weight tg initial state * Domination.freshAvg Finset.univ gf) :=
        ENNReal.tsum_le_tsum fun ρ => mul_le_mul_right
          (walk_bound_freshW tg initial model parameter data message hparse hkind reference hnob1 hlandb1 gf
            attempts ρ budget state hrel) _
    _ ≤ _ := by
        rw [ENNReal.tsum_mul_right]
        exact mul_le_of_le_one_left' tsum_probOutput_le_one

end LoopW

end LeanSphincs.Security.GraphView
