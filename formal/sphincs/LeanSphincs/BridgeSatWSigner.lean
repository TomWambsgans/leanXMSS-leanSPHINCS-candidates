import LeanSphincs.BridgeSatW
import LeanSphincs.BridgeSignerFors

/-! The fair-share bounds of the grinding signer, weighted by the final survival weight. The
message-digest blocks are untargeted, so their reads keep the weight; everything after the two
digest reads of the final assembly lowers it in expectation. Each bound of `BridgeSignerFors`
therefore holds with the integrand multiplied by the final weight and the bound multiplied by
the initial weight. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.GraphView

open Concrete Completeness Prefix HiddenGraph HiddenCost HiddenDebt ForsSigner

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

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
    (hrel : Related parameter data message reference state) (attempts : ℕ)
    (hih : ∀ s', Related parameter data message reference s' →
      cachedCount parameter data message s' ≤ cachedCount parameter data message state + 1 → ∀ b,
        ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts) b s'] *
          (weight tg initial out.2 * outWeight parameter data message reference gf gp out) ≤
            weight tg initial s' * bound)
    (ρ : Randomness) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model
        (liftM (CostSpec.query (.inl (.inr (.inl (blk parameter data message ρ 0))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
          else signCostSourceLoop parameter data message attempts) budget state] *
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
          exact hih state hrel (Nat.le_succ _) _
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
          have h := hih _ (related_store parameter data message reference state hrel ρ hc u0 hl)
            (cachedCount_store parameter data message state ρ u0) (budget - 1)
          rwa [hw] at h
  · rw [tsum_probOutput_pure_mul]
    have h0 : outWeight parameter data message reference gf gp ((none, [], [], []), state) = 0 := rfl
    rw [h0, mul_zero]
    exact bot_le

/-- **Fair share of the grinding signer, weighted.** -/
theorem loop_boundW
    (hparse : ∀ ρ call, model.parse (blk parameter data message ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (blk parameter data message ρ call) = .none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (hnob1 : ∀ ρ, reference.cache (blk parameter data message ρ 0) = none →
      reference.cache (blk parameter data message ρ 1) = none)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (B : ℝ≥0∞) (hB : B ≠ ⊤) (hgf : ∀ v, gf v ≤ B) (hgp : ∀ ρ v, gp ρ v ≤ B)
    (wbar : ℝ≥0∞) (hw : wbar ≠ ⊤) (Cmax : ℕ) (hC : Cmax ≤ 2 ^ 128)
    (hu : ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ ≤
      wbar * (((2 ^ 128 - Cmax : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞)) * ForsPrice.landing) :
    ∀ attempts budget state, Related parameter data message reference state →
      cachedCount parameter data message state + attempts ≤ Cmax →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts) budget state] *
          (weight tg initial out.2 * outWeight parameter data message reference gf gp out) ≤
        weight tg initial state *
          (Domination.freshAvg Finset.univ gf + wbar * ∑ ρ, poolValue parameter data message reference gp ρ) := by
  set S := ∑ ρ, poolValue parameter data message reference gp ρ with hS
  set a := Domination.freshAvg Finset.univ gf with ha
  set Bnd := a + wbar * S with hBnd
  intro attempts
  induction attempts with
  | zero =>
      intro budget state _ _
      change ∑' out, Pr[= out | interp tg initial model (pure none) budget state] *
        (weight tg initial out.2 * outWeight parameter data message reference gf gp out) ≤ _
      rw [interp_pure, tsum_probOutput_pure_mul]
      have h0 : outWeight parameter data message reference gf gp ((some none, [], [], []), state) = 0 := rfl
      rw [h0, mul_zero]
      exact bot_le
  | succ attempts ih =>
      intro budget state hrel hcount
      rw [signCostSourceLoop_succ, interp_liftProb_bind, tsum_probOutput_bind_mul]
      have htrial := fun ρ => trial_boundW tg initial model parameter data message hparse hkind reference hnob1 gf gp
        Bnd state hrel attempts (fun s' hs' hcs b => ih b s' hs' (by omega)) ρ budget
      refine le_trans (ENNReal.tsum_le_tsum fun ρ => mul_le_mul_right (htrial ρ) _) ?_
      simp only [mul_left_comm _ (weight tg initial state), ENNReal.tsum_mul_left]
      refine mul_le_mul_right ?_ _
      -- uniform randomizers
      set u : ℝ≥0∞ := ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ with hudef
      have hpr : ∀ ρ, Pr[= ρ | ($ᵗ Randomness : ProbComp Randomness)] = u := by
        intro ρ
        rw [probOutput_uniformSample, card_randomness]
      simp only [hpr, ENNReal.tsum_mul_left]
      rw [tsum_fintype]
      -- the three classes of randomizers
      set Fr := Finset.univ.filter fun ρ : Randomness => state.cache (blk parameter data message ρ 0) = none
      set NL := Finset.univ.filter fun ρ : Randomness => ∃ u0,
        state.cache (blk parameter data message ρ 0) = some u0 ∧ ¬Landed parameter (blockIndex u0)
      set fresh := ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if Landed parameter (blockIndex u0) then
          ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] * gf (viewOf u0 u') else Bnd)
      have hpoint : ∀ ρ, (state.cache (blk parameter data message ρ 0)).elim fresh
          (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
            else Bnd) ≤
          poolValue parameter data message reference gp ρ + (if ρ ∈ NL then Bnd else 0) +
            (if ρ ∈ Fr then fresh else 0) := by
        intro ρ
        cases hc : state.cache (blk parameter data message ρ 0) with
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
      have hsum : ∑ ρ, (state.cache (blk parameter data message ρ 0)).elim fresh
          (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
            else Bnd) ≤ S + (NL.card : ℝ≥0∞) * Bnd + (Fr.card : ℝ≥0∞) * fresh := by
        refine le_trans (Finset.sum_le_sum fun ρ _ => hpoint ρ) (le_of_eq ?_)
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
          Finset.univ_inter, Finset.univ_inter, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      -- the fresh term
      have hfreshEq : fresh = ForsPrice.landing * a + (1 - ForsPrice.landing) * Bnd := by
        have hsplit : fresh = (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
            ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (if Landed parameter (blockIndex u0) then
                gf (Lifetime.localDigestView (truncateMessageDigest u0 u')) else 0)) +
            Bnd * ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (if Landed parameter (blockIndex u0) then 0 else 1) := by
          rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
          refine tsum_congr fun u0 => ?_
          split_ifs
          · simp [viewOf]
          · simp [mul_comm]
        have hland := landed_mass parameter
        have hcompl : ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (if Landed parameter (blockIndex u0) then (0 : ℝ≥0∞) else 1) = 1 - ForsPrice.landing := by
          have htot : (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (if Landed parameter (blockIndex u0) then (1 : ℝ≥0∞) else 0)) +
            ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (if Landed parameter (blockIndex u0) then (0 : ℝ≥0∞) else 1) = 1 := by
            rw [← ENNReal.tsum_add]
            calc _ = ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] := by
                  refine tsum_congr fun u0 => ?_
                  split_ifs <;> simp
              _ = 1 := tsum_probOutput_eq_one' probFailure_eq_zero
          rw [hland] at htot
          exact ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top (by rw [add_comm]; exact htot)
        rw [hsplit, hcompl]
        have hmean := fresh_view_mean parameter gf
        rw [hmean]
        ring
      -- finiteness and class sizes
      have hpool : ∀ ρ, poolValue parameter data message reference gp ρ ≤ B := by
        intro ρ
        unfold poolValue
        cases reference.cache (blk parameter data message ρ 0) with
        | none => exact bot_le
        | some u0 =>
            simp only [Option.elim]
            split_ifs
            · cases reference.cache (blk parameter data message ρ 1) with
              | none =>
                  calc _ ≤ ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * B :=
                        ENNReal.tsum_le_tsum fun u => by gcongr; exact hgp _ _
                    _ ≤ B := by
                        rw [ENNReal.tsum_mul_right]
                        exact mul_le_of_le_one_left' tsum_probOutput_le_one
              | some u1 => exact hgp _ _
            · exact bot_le
      have hSfin : S ≠ ⊤ := ENNReal.sum_ne_top.2 fun ρ _ => ne_top_of_le_ne_top hB (hpool ρ)
      have hafin : a ≠ ⊤ := Domination.freshAvg_ne_top Finset.univ_nonempty fun v => ne_top_of_le_ne_top hB (hgf v)
      have hcard : Fr.card + cachedCount parameter data message state = 2 ^ 128 := by
        rw [← card_randomness]
        exact Finset.card_filter_add_card_filter_not _
      have hNL : NL.card ≤ cachedCount parameter data message state := by
        refine Finset.card_le_card fun ρ hρ => ?_
        obtain ⟨_, u0, hc, _⟩ := Finset.mem_filter.1 hρ
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hc]; exact Option.some_ne_none _⟩
      have hland1 : ForsPrice.landing ≤ 1 := by
        unfold ForsPrice.landing
        exact ENNReal.inv_le_one.2 (by exact_mod_cast Nat.one_le_two_pow)
      have hu2 : u * ((2 ^ 128 : ℕ) : ℝ≥0∞) = 1 := ENNReal.inv_mul_cancel (by simp) (by simp)
      have hFN : u * (Fr.card : ℝ≥0∞) + u * (NL.card : ℝ≥0∞) ≤ 1 := by
        rw [← mul_add, ← hu2]
        gcongr
        exact_mod_cast (by omega : Fr.card + NL.card ≤ 2 ^ 128)
      have hu' : u ≤ wbar * (u * (Fr.card : ℝ≥0∞)) * ForsPrice.landing := by
        refine le_trans hu ?_
        gcongr
        rw [ENNReal.div_eq_inv_mul]
        gcongr
        exact_mod_cast (by omega : 2 ^ 128 - Cmax ≤ Fr.card)
      calc u * ∑ ρ, (state.cache (blk parameter data message ρ 0)).elim fresh
            (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
              else Bnd)
          ≤ u * (S + (NL.card : ℝ≥0∞) * Bnd + (Fr.card : ℝ≥0∞) * fresh) := mul_le_mul_right hsum u
        _ = u * S + (u * (NL.card : ℝ≥0∞)) * Bnd + (u * (Fr.card : ℝ≥0∞)) *
              (ForsPrice.landing * a + (1 - ForsPrice.landing) * Bnd) := by
            rw [hfreshEq]
            ring
        _ ≤ Bnd := loop_arith a S wbar ForsPrice.landing _ _ u hafin hSfin hw hFN hland1 hu'

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
    (hrel : Related parameter data message reference state) (attempts : ℕ)
    (hih : ∀ s', Related parameter data message reference s' → ∀ b,
        ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts) b s'] *
          (weight tg initial out.2 * freshNewWeight parameter data message reference gf out) ≤
            weight tg initial s' * bound)
    (ρ : Randomness) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model
        (liftM (CostSpec.query (.inl (.inr (.inl (blk parameter data message ρ 0))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
          else signCostSourceLoop parameter data message attempts) budget state] *
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
  set a := Domination.freshAvg Finset.univ gf with ha
  intro attempts
  induction attempts with
  | zero =>
      intro budget state hrel
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
      intro budget state hrel
      rw [signCostSourceLoop_succ, interp_liftProb_bind, tsum_probOutput_bind_mul]
      have htrial := fun ρ => trial_bound_freshW tg initial model parameter data message hparse hkind reference hnob1
        hlandb1 gf a state hrel attempts (fun s' hs' b => ih b s' hs') ρ budget
      refine le_trans (ENNReal.tsum_le_tsum fun ρ => mul_le_mul_right (htrial ρ) _) ?_
      simp only [mul_left_comm _ (weight tg initial state), ENNReal.tsum_mul_left]
      refine mul_le_mul_right ?_ _
      have hfresh : ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if Landed parameter (blockIndex u0) then
            ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * gf (viewOf u0 u) else a) = a := by
        have hsplit : ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (if Landed parameter (blockIndex u0) then
              ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * gf (viewOf u0 u) else a) =
            (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
              ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] *
                (if Landed parameter (blockIndex u0) then
                  gf (Lifetime.localDigestView (truncateMessageDigest u0 u')) else 0)) +
            a * ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (if Landed parameter (blockIndex u0) then 0 else 1) := by
          rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
          refine tsum_congr fun u0 => ?_
          split_ifs
          · simp [viewOf]
          · simp [mul_comm]
        have hland := landed_mass parameter
        have hcompl : ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (if Landed parameter (blockIndex u0) then (0 : ℝ≥0∞) else 1) = 1 - ForsPrice.landing := by
          have htot : (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (if Landed parameter (blockIndex u0) then (1 : ℝ≥0∞) else 0)) +
            ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (if Landed parameter (blockIndex u0) then (0 : ℝ≥0∞) else 1) = 1 := by
            rw [← ENNReal.tsum_add]
            calc _ = ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] := by
                  refine tsum_congr fun u0 => ?_
                  split_ifs <;> simp
              _ = 1 := tsum_probOutput_eq_one' probFailure_eq_zero
          rw [hland] at htot
          exact ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top (by rw [add_comm]; exact htot)
        rw [hsplit, hcompl, fresh_view_mean parameter gf]
        have hland1 : ForsPrice.landing ≤ 1 := by
          unfold ForsPrice.landing
          exact ENNReal.inv_le_one.2 (by exact_mod_cast Nat.one_le_two_pow)
        rw [mul_comm a, ← add_mul, add_tsub_cancel_of_le hland1, one_mul]
      have hpoint : ∀ ρ, (state.cache (blk parameter data message ρ 0)).elim
          (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
            (if Landed parameter (blockIndex u0) then
              ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] * gf (viewOf u0 u) else a))
          (fun u0 => if Landed parameter (blockIndex u0) then 0 else a) ≤ a := by
        intro ρ
        cases state.cache (blk parameter data message ρ 0) with
        | none => exact le_of_eq hfresh
        | some u0 =>
            simp only [Option.elim]
            split_ifs
            · exact bot_le
            · exact le_rfl
      calc _ ≤ ∑' ρ, Pr[= ρ | ($ᵗ Randomness : ProbComp Randomness)] * a :=
            ENNReal.tsum_le_tsum fun ρ => mul_le_mul_right (hpoint ρ) _
        _ ≤ a := by
            rw [ENNReal.tsum_mul_right]
            exact mul_le_of_le_one_left' tsum_probOutput_le_one

end LoopW

end LeanSphincs.Security.GraphView
