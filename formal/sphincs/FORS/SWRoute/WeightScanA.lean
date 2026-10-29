import FORS.SWRoute.WeightAbs

/-! **The scan signer, weighted by an abstract weight.** The bounds of `LargeBudget/WeightedScan`
and the signing lemmas of `LargeBudget/WeightedPotential` (`upper_expectW`, `fresh_expectW`,
`term_expectW`) for a weight `wt` with `WtSpec … IsMsgInput`: the message-digest blocks keep it, and
it is a supermartingale of the run. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base
open Concrete Completeness Prefix HiddenGraph HiddenCost HiddenDebt ForsSigner FORS.LoopWalk GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

section LoopSA

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) {model : HiddenRows.Model HashInput HashOutput A Coordinate}
  {wt : DebtState HashInput HashOutput Coordinate → ℝ≥0∞} (hW : WtSpec model wt IsMsgInput) (hcalls : digestCalls = 1)
  (parameter : PublicParameter) (data : PublicData) (message : Message)
include hW hcalls

/-- **Final assembly from a cached pair, weighted.** -/
theorem finish_boundAllA (randomness : Randomness)
    (state : DebtState HashInput HashOutput Coordinate) (u : DigestCall → HashOutput)
    (hc : ∀ call, state.cache (pblk parameter data message randomness call) = some (u call))
    (g : (DigestCall → HashOutput) → ℝ≥0∞) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message randomness) budget state] *
        (wt out.2 * (if out.1.1.isSome then
          (pcache parameter data message out.2 randomness).elim 0 g else 0)) ≤
      wt state * g u := by
  refine interp_wt_mul_le tg initial hW _ _ state _ _ fun out hout => ?_
  have hpc : pcache parameter data message out.2 randomness = some u :=
    allSome_of_eq _ _ fun call =>
      (interp_extends tg initial model _ budget state out hout).1 _ _ (hc call)
  rw [hpc]
  split_ifs
  · rfl
  · exact bot_le

/-- **One trial of the scan, weighted**, with any continuation. -/
theorem trial_boundSA
    (hparse : ∀ ρ call, model.parse (pblk parameter data message ρ call) = none)
    (_hkind : ∀ ρ call, tg.kind (pblk parameter data message ρ call) = .none)
    (reference : DebtState HashInput HashOutput Coordinate) (ρ : Randomness)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (V : Option (Option Signature) → DebtState HashInput HashOutput Coordinate → ℝ≥0∞)
    (hVabort : ∀ s', V none s' = 0)
    (_hVstore : ∀ r (s' : DebtState HashInput HashOutput Coordinate) (y : HashInput) (v : HashOutput),
      s'.cache y = none → V r s' ≤ V r (s'.store y v))
    (hVfin : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u : DigestCall → HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ →
      (∀ call, s'.cache (pblk parameter data message ρ call) = some (u call)) →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        V out.1.1 out.2 ≤ (if out.1.1.isSome then (pcache parameter data message out.2 ρ).elim 0
          (pairWeight parameter data message reference gf gp ρ) else 0))
    (bound : ℝ≥0∞) (state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state)
    (hinv : PairInv parameter data message state)
    (hpair : ∀ call, state.cache (pblk parameter data message ρ call) =
      reference.cache (pblk parameter data message ρ call))
    (cont : OracleComp CostSpec (Option Signature))
    (hih : ∀ s', Related parameter data message reference s' → PairInv parameter data message s' →
      (∀ x, (∀ call, x ≠ pblk parameter data message ρ call) → s'.cache x = state.cache x) → ∀ b,
        ∑' out, Pr[= out | interp tg initial model cont b s'] *
          (wt out.2 * V out.1.1 out.2) ≤ wt s' * bound)
    (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model
        (liftM (CostSpec.query (.inl (.inr (.inl (blk parameter data message ρ))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
          else cont) budget state] *
        (wt out.2 * V out.1.1 out.2) ≤
      wt state * (state.cache (blk parameter data message ρ)).elim
        (∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
          (if Landed parameter (blockIndex (u firstCall)) then gf (viewOf u) else bound))
        (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
          else bound) := by
  have hdig : ∀ call, IsMsgInput (pblk parameter data message ρ call) := fun call =>
    msgInput_digestInput parameter data.root message ρ call
  have hfinish : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u : DigestCall → HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ →
      (∀ call, s'.cache (pblk parameter data message ρ call) = some (u call)) →
      ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) b s'] *
          (wt out.2 * V out.1.1 out.2) ≤
        wt s' * pairWeight parameter data message reference gf gp ρ u := by
    intro s' u b hrel' hs'
    refine le_trans (ENNReal.tsum_le_tsum fun out => ?_)
      (finish_boundAllA tg initial hW hcalls parameter data message ρ s' u hs' _ b)
    by_cases hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s')
    · exact mul_le_mul_right (mul_le_mul_right (hVfin s' u b hrel' hs' out hout) _) _
    · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
  rw [interp_ordinary]
  split_ifs with h1
  · rw [ordinaryStep, hparse ρ firstCall]
    simp only
    rw [tsum_probOutput_bind_mul]
    simp only [tsum_probOutput_map_mul]
    cases hc : state.cache (blk parameter data message ρ) with
    | some u0 =>
        rw [readOutside_cached _ state u0 hc, tsum_probOutput_pure_mul]
        simp only [Option.elim]
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          obtain ⟨u, hu, hucall⟩ :=
            pcache_of_isSome parameter data message state ρ ((hinv ρ).2 u0 hc hl)
          have hu0 : u firstCall = u0 := Option.some_inj.1 ((hucall firstCall).symm.trans hc)
          have href : reference.cache (blk parameter data message ρ) = some u0 := by
            rw [← hpair firstCall]; exact hc
          have hpcsame : pcache parameter data message reference ρ =
              pcache parameter data message state ρ := by
            unfold pcache
            exact congrArg _ (funext fun call => (hpair call).symm)
          have hpv : poolValue parameter data message reference gp ρ = gp ρ (viewOf u) := by
            unfold poolValue
            rw [hpcsame.trans hu]
            simp only [Option.elim, hu0]
            rw [if_pos hl]
          have hpw : pairWeight parameter data message reference gf gp ρ u = gp ρ (viewOf u) := by
            unfold pairWeight
            rw [if_neg (by rw [href]; simp)]
          rw [hpv, ← hpw]
          exact hfinish state u _ (fun ρ' _ => hrel ρ') hucall
        · rw [if_neg hl, if_neg hl]
          exact hih state hrel hinv (fun _ _ => rfl) _
    | none =>
        have hfresh : ∀ call, state.cache (pblk parameter data message ρ call) = none := (hinv ρ).1 hc
        have href : reference.cache (blk parameter data message ρ) = none := by
          rw [← hpair firstCall]; exact hc
        rw [readOutside_fresh _ state hc, tsum_probOutput_map_mul]
        simp only [Option.elim]
        refine le_trans (le_of_eq (presample_one hcalls (pblk parameter data message ρ) firstCall state
          (fun v s' => ∑' out, Pr[= out | interp tg initial model
            ((fun first => if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
              else cont) v) (budget - 1) s'] * (wt out.2 * V out.1.1 out.2)))) ?_
        have hcard : (Fintype.card (DigestCall → HashOutput) : ℝ≥0∞) =
            (Fintype.card HashOutput : ℝ≥0∞) ^ digestCalls := by
          rw [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
        have hrhs : wt state *
            (∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
              (if Landed parameter (blockIndex (u firstCall)) then gf (viewOf u) else bound)) =
            ((Fintype.card HashOutput : ℝ≥0∞) ^ digestCalls)⁻¹ *
              ∑ u : DigestCall → HashOutput, wt state *
                (if Landed parameter (blockIndex (u firstCall)) then gf (viewOf u) else bound) := by
          rw [tsum_uniform_eq, hcard, mul_left_comm, Finset.mul_sum]
        rw [hrhs]
        refine mul_le_mul_right (Finset.sum_le_sum fun u _ => ?_) _
        refine le_trans ?_ (mul_le_mul' (wt_storeAll_le hW (pblk parameter data message ρ) u state
          (pblk_injective parameter data message ρ) hdig hfresh) le_rfl)
        beta_reduce
        by_cases hl : Landed parameter (blockIndex (u firstCall))
        · rw [if_pos hl, if_pos hl]
          have hall : ∀ call, (storeAll (pblk parameter data message ρ) u state).cache
              (pblk parameter data message ρ call) = some (u call) :=
            fun call => storeAll_cache_self _ (pblk_injective parameter data message ρ) u state call
          have hpw : pairWeight parameter data message reference gf gp ρ u = gf (viewOf u) := by
            unfold pairWeight
            rw [if_pos href, if_pos hl]
          rw [← hpw]
          exact hfinish _ u _ (relatedOff_storeAll parameter data message reference state hrel ρ u) hall
        · rw [if_neg hl, if_neg hl]
          exact hih _ (related_storeAll parameter data message reference state hrel ρ hc u hl)
            (pairInv_storeAll parameter data message state hinv ρ u hl)
            (fun x hx => storeAll_cache_other _ _ _ _ fun call => Ne.symm (hx call)) _
  · rw [tsum_probOutput_pure_mul]
    rw [hVabort, mul_zero]
    exact zero_le

/-- **The scan from a start, weighted.** -/
theorem loop_boundSA
    (hparse : ∀ ρ call, model.parse (pblk parameter data message ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (pblk parameter data message ρ call) = .none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (V : Option (Option Signature) → DebtState HashInput HashOutput Coordinate → ℝ≥0∞)
    (hVabort : ∀ s', V none s' = 0)
    (hVstore : ∀ r (s' : DebtState HashInput HashOutput Coordinate) (y : HashInput) (v : HashOutput),
      s'.cache y = none → V r s' ≤ V r (s'.store y v))
    (hVnone : ∀ s' : DebtState HashInput HashOutput Coordinate, Related parameter data message reference s' →
      V (some none) s' = 0)
    (hVfin : ∀ (ρ : Randomness) (s' : DebtState HashInput HashOutput Coordinate)
      (u : DigestCall → HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ →
      (∀ call, s'.cache (pblk parameter data message ρ call) = some (u call)) →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        V out.1.1 out.2 ≤ (if out.1.1.isSome then (pcache parameter data message out.2 ρ).elim 0
          (pairWeight parameter data message reference gf gp ρ) else 0)) :
    ∀ attempts, attempts ≤ 2 ^ 128 → ∀ budget state ρ, Related parameter data message reference state →
      PairInv parameter data message state →
      (∀ i, i < attempts → ∀ call,
        state.cache (pblk parameter data message ((nextRand (data.steps message) ^ i) ρ) call) =
        reference.cache (pblk parameter data message ((nextRand (data.steps message) ^ i) ρ) call)) →
      ∑' out, Pr[= out | interp tg initial model
          (signCostSourceLoop parameter data message (data.step message) attempts ρ) budget state] *
          (wt out.2 * V out.1.1 out.2) ≤
        wt state * walk (nextRand (data.steps message)) ForsPrice.landing (stOf parameter data message reference)
          (poolValue parameter data message reference gp) (Domination.freshAvg Finset.univ gf) 0 attempts ρ := by
  intro attempts
  induction attempts with
  | zero =>
      intro _ budget state ρ hrel _ _
      change ∑' out, Pr[= out | interp tg initial model (pure none) budget state] *
        (wt out.2 * V out.1.1 out.2) ≤ _
      rw [interp_pure, tsum_probOutput_pure_mul]
      change wt state * V (some none) state ≤ _
      rw [hVnone state hrel, mul_zero]
      exact bot_le
  | succ attempts ih =>
      intro hA budget state ρ hrel hinv hahead
      rw [signCostSourceLoop_succ]
      have hnext : ∀ s', Related parameter data message reference s' → PairInv parameter data message s' →
          (∀ x, (∀ call, x ≠ pblk parameter data message ρ call) → s'.cache x = state.cache x) → ∀ b,
          ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message (data.step message)
              attempts (nextRand (data.steps message) ρ)) b s'] *
            (wt out.2 * V out.1.1 out.2) ≤
          wt s' * walk (nextRand (data.steps message)) ForsPrice.landing (stOf parameter data message reference)
            (poolValue parameter data message reference gp) (Domination.freshAvg Finset.univ gf) 0 attempts
            (nextRand (data.steps message) ρ) := by
        intro s' hrel' hinv' hsame b
        refine ih (Nat.le_of_succ_le hA) b s' (nextRand (data.steps message) ρ) hrel' hinv'
          fun i hi call => ?_
        have hpow : (nextRand (data.steps message) ^ i) (nextRand (data.steps message) ρ) =
            (nextRand (data.steps message) ^ (i + 1)) ρ := by
          rw [pow_succ, Equiv.Perm.mul_apply]
        rw [hpow, hsame _ fun call' => pblk_ne_of_ne parameter data message
          (nextRand_pow_ne (data.steps message) ρ (i + 1) (Nat.succ_pos i) (by omega)) call call']
        exact hahead (i + 1) (Nat.succ_lt_succ hi) call
      refine le_trans (trial_boundSA tg initial hW hcalls parameter data message hparse hkind reference ρ gf gp V
        hVabort hVstore (hVfin ρ) _ state hrel hinv (hahead 0 (Nat.succ_pos attempts)) _ hnext budget)
        (mul_le_mul_right ?_ _)
      have h0 : state.cache (blk parameter data message ρ) = reference.cache (blk parameter data message ρ) :=
        hahead 0 (Nat.succ_pos attempts) firstCall
      rw [h0]
      cases hc : reference.cache (blk parameter data message ρ) with
      | none =>
          have hst : stOf parameter data message reference ρ = .fresh := by simp [stOf, hc]
          rw [walk_succ_fresh _ _ _ _ hst]
          simp only [Option.elim]
          exact trials_sum_le parameter gf _
      | some u0 =>
          simp only [Option.elim]
          by_cases hl : Landed parameter (blockIndex u0)
          · have hst : stOf parameter data message reference ρ = .hit := by simp [stOf, hc, hl]
            rw [walk_succ_hit _ _ _ _ hst, if_pos hl]
          · have hst : stOf parameter data message reference ρ = .miss := by simp [stOf, hc, hl]
            rw [walk_succ_miss _ _ _ _ hst, if_neg hl]

/-- **The scan from a start, with the fresh pair it completes, weighted.** -/
theorem loop_bound_combSA
    (hparse : ∀ ρ call, model.parse (pblk parameter data message ρ call) = none)
    (hkind : ∀ ρ call, tg.kind (pblk parameter data message ρ call) = .none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞) :
    ∀ attempts, attempts ≤ 2 ^ 128 → ∀ budget state ρ, Related parameter data message reference state →
      PairInv parameter data message state →
      (∀ i, i < attempts → ∀ call,
        state.cache (pblk parameter data message ((nextRand (data.steps message) ^ i) ρ) call) =
        reference.cache (pblk parameter data message ((nextRand (data.steps message) ^ i) ρ) call)) →
      ∑' out, Pr[= out | interp tg initial model
          (signCostSourceLoop parameter data message (data.step message) attempts ρ) budget state] *
          (wt out.2 * (freshNewWeight parameter data message reference gf out +
            outWeight parameter data message reference 0 gp out)) ≤
        wt state * walk (nextRand (data.steps message)) ForsPrice.landing (stOf parameter data message reference)
          (poolValue parameter data message reference gp) (Domination.freshAvg Finset.univ gf) 0 attempts ρ :=
  loop_boundSA tg initial hW hcalls parameter data message hparse hkind reference gf gp
    (fun r s' => freshNewWeight parameter data message reference gf ((r, [], [], []), s') +
      outWeight parameter data message reference 0 gp ((r, [], [], []), s'))
    (fun _ => by simp [freshNewWeight, outWeight])
    (fun r s' y v hy => comb_store parameter data message reference gf gp r s' y v hy)
    (comb_none parameter data message reference gf gp)
    (fun ρ s' u b hoff hs0 out hout => comb_fin tg initial model parameter data message reference gf gp
      ρ s' u b hoff hs0 out hout)

end LoopSA

end FORS.Security.SWRoute
