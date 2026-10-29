import FORS.SWRoute.StepsFirst

/-! **The SW route: steps without a fresh answer.** A cached read keeps the state (a guess at a
cached input is already recorded), so the decrement pays the digest baseline, and at a FORS leaf
query whose contact would survive the contact coefficient, after arming if its cell is near-missing.
An exposure (a reveal or a canonical continuation) keeps the weight in mean, except a kill that
completes a FORS contact, booked in `WK`. Draws and ticks change nothing. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost PotentialA GraphView ForsPotential

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

section Misc

variable (K : Ctx) (root : Digest) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (ρ β δ cU : ℝ)

/-- Recording a guess that is already recorded keeps the survival weight. -/
theorem weight_record_of_mem (s : St) (g : Coordinate × Digest) (hg : g ∈ s.guesses) :
    weight K.tg K.initial (s.record g) = weight K.tg K.initial s := by
  have hd : ∀ c, debts K.tg K.initial (s.record g) c = debts K.tg K.initial s c := by
    intro c
    rw [debts_record]
    split_ifs with h
    · subst h
      exact Set.insert_eq_of_mem (Or.inl (by simpa using hg))
    · rfl
  have hr : Realized K.tg K.initial (s.record g) ↔ Realized K.tg K.initial s := by
    unfold Realized
    simp only [fixedHit_record, hd]
    rfl
  unfold weight survival
  simp only [hr, hd]
  rfl

theorem weightA_record_of_mem (s : St) (g : Coordinate × Digest) (hg : g ∈ s.guesses) :
    weightA K root (s.record g) = weightA K root s := by
  rw [weightA_eq, weightA_eq K root s, weight_record_of_mem K s g hg]
  rfl

/-- **A cached ordinary read** (the state after is `s0`, with the same weight, exponent and pending
credit): the decrement pays the digest baseline. -/
theorem step_cached {total : ℕ} (hN : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU)
    (s s0 : St) (flag : Bool) (p r0 : ℕ) (hb : ¬BadP K root s) (x : HashInput) (u : HashOutput)
    (hcs : costStep model (.inl (.inr (.inl x))) s = pure (u, s0))
    (hw0 : weightA K root s0 = weightA K root s) (he0 : ∀ fl, expo K ρ fl s0 = expo K ρ fl s)
    (hp0 : pendA K s0 = pendA K s) (hK : payK K root s (.inl (.inr (.inl x))) s0 = 0)
    (hC : payC K root s (.inl (.inr (.inl x))) = 0) (hA : payA K root flag s (.inl (.inr (.inl x))) = 0)
    (hnf : nextFlag K root flag s (.inl (.inr (.inl x))) = flag) (hle : p + r0 + 1 ≤ total) :
    StepBound K root model ρ β δ cU (.inl (.inr (.inl x))) s flag p (r0 + 1) p := by
  unfold StepBound
  rw [show sourceCost (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inr (.inl x))) = 1 from rfl,
    Nat.add_sub_cancel, hcs, tsum_probOutput_pure_mul, tsum_probOutput_pure_mul, tsum_probOutput_pure_mul,
    hw0, he0, hp0, hK, hC, hA, hnf, mul_zero, add_zero, mul_zero, add_zero, add_zero]
  have hdec := dec_expo_add K root hN (flag := flag) hb p r0 hle
  have hpF : payF K root s (.inl (.inr (.inl x))) ≤ weightA K root s := payF_le_weight K root s _
  calc budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s +
        ENNReal.ofReal (β / 2 ^ 128) * payF K root s (.inl (.inr (.inl x))) +
        weightA K root s * pendA K s
      ≤ budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s +
          ENNReal.ofReal (β / 2 ^ 128) * weightA K root s + weightA K root s * pendA K s := by gcongr
    _ = (budgetE (expo K ρ flag s) p (r0 + 1) + ENNReal.ofReal (β / 2 ^ 128)) * weightA K root s +
          weightA K root s * pendA K s := by ring
    _ ≤ budgetE (expo K ρ flag s) p r0 * weightA K root s + weightA K root s * pendA K s := by gcongr

/-- **A guess at a cached FORS leaf query**: after arming, the decrement pays the contact
coefficient if the contact would survive. -/
theorem step_flq_cached {total : ℕ} (hN : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (hH : StepHyp K model)
    (f : FIn) (s : St) (flag : Bool) (p r0 : ℕ) (hinv : InvS K s p) (hb : ¬BadP K root s) (u : HashOutput)
    (hx : s.cache (f.input K.p) = some u) (hk : s.known f.inC = none) (hle : p + r0 + 1 ≤ total) :
    StepBound K root model ρ β δ cU (flq K f) s flag p (r0 + 1) p := by
  set x := f.input K.p with hxdef
  have hi : K.initial x = none := hH.fleaf f
  have hg : (f.inC, f.v) ∈ s.guesses :=
    hinv.lin.guessed x u (Address.fleaf f.index f.κ f.leaf, f.v) ⟨hx, hi⟩ (parse_fleaf K f) hk
  have hcs : costStep model (flq K f) s = pure (u, s.record (f.inC, f.v)) := by
    rw [costStep_inl, lazyStep_guess model x s (Address.fleaf f.index f.κ f.leaf, f.v)
      (by rw [hH.parse]; exact parse_fleaf K f) (by rw [hH.incoming]; exact hk), hH.incoming]
    exact readOutside_cached x _ u hx
  have hw0 := weightA_record_of_mem K root s (f.inC, f.v) hg
  unfold StepBound
  rw [show sourceCost (D := HashInput) (R := HashOutput) (ι := Coordinate) (flq K f) = 1 from rfl,
    Nat.add_sub_cancel, hcs, tsum_probOutput_pure_mul, tsum_probOutput_pure_mul, tsum_probOutput_pure_mul,
    hw0, expo_record, pendA_record, payK_flq, payF_flq K root hH.digest, mul_zero, zero_add, add_zero, payC_flq]
  set fl := nextFlag K root flag s (flq K f) with hfl
  have harm := arm_conv K root hN (flq K f) s flag p (r0 + 1) (by omega)
  by_cases hsv : SurvivesAt K root s f
  · obtain ⟨_, hnl, hnf, hnw⟩ := hsv
    have hnm : ¬NearMiss K root s f := fun h => hnl h.1
    have he : expo K ρ fl s = ρ ∨ expo K ρ fl s = 2 := by
      by_cases ha : ArmedS K fl s
      · right; unfold expo; rw [if_pos ha, if_neg hnw, if_neg hnf]; norm_num
      · left; exact expo_unarmed K ρ ha
    have h7 := swR7 hN p r0 hle (expo K ρ fl s) he
    have hmono : budgetE (expo K ρ fl s) p (r0 + 1) ≤ budgetE (expo K ρ fl s) p r0 :=
      budgetE_succ_le (expo_nonneg K ρ (by linarith [hN.low]) fl s) p r0
        (by have := sw_lt hN hle; push_cast; linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)])
    have hdec : budgetE (expo K ρ fl s) p (r0 + 1) + ENNReal.ofReal (cU / 2 ^ 128) ≤ budgetE (expo K ρ fl s) p r0 :=
      calc _ ≤ budgetE (expo K ρ fl s) p (r0 + 1) +
            (budgetE (expo K ρ fl s) p r0 - budgetE (expo K ρ fl s) p (r0 + 1)) := add_le_add le_rfl h7
        _ = _ := add_tsub_cancel_of_le hmono
    rw [if_pos ⟨hk, hnl, hnf, hnw⟩]
    calc budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s + ENNReal.ofReal (cU / 2 ^ 128) * weightA K root s +
          weightA K root s * pendA K s
        ≤ (budgetE (expo K ρ fl s) p (r0 + 1) * weightA K root s + ENNReal.ofReal δ * payA K root flag s (flq K f)) +
            ENNReal.ofReal (cU / 2 ^ 128) * weightA K root s + weightA K root s * pendA K s :=
          add_le_add (add_le_add harm le_rfl) le_rfl
      _ = (budgetE (expo K ρ fl s) p (r0 + 1) + ENNReal.ofReal (cU / 2 ^ 128)) * weightA K root s +
            (weightA K root s * pendA K s + ENNReal.ofReal δ * payA K root flag s (flq K f)) := by ring
      _ ≤ budgetE (expo K ρ fl s) p r0 * weightA K root s +
            (weightA K root s * pendA K s + ENNReal.ofReal δ * payA K root flag s (flq K f)) :=
          add_le_add (mul_le_mul_left hdec _) le_rfl
      _ ≤ _ := le_of_eq (by ring)
  · rw [if_neg hsv, mul_zero, add_zero]
    have hmono : budgetE (expo K ρ fl s) p (r0 + 1) ≤ budgetE (expo K ρ fl s) p r0 :=
      budgetE_succ_le (expo_nonneg K ρ (by linarith [hN.low]) fl s) p r0
        (by have := sw_lt hN hle; push_cast; linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)])
    calc budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s + weightA K root s * pendA K s
        ≤ (budgetE (expo K ρ fl s) p (r0 + 1) * weightA K root s + ENNReal.ofReal δ * payA K root flag s (flq K f)) +
            weightA K root s * pendA K s := add_le_add harm le_rfl
      _ = budgetE (expo K ρ fl s) p (r0 + 1) * weightA K root s +
            (weightA K root s * pendA K s + ENNReal.ofReal δ * payA K root flag s (flq K f)) := by ring
      _ ≤ budgetE (expo K ρ fl s) p r0 * weightA K root s +
            (weightA K root s * pendA K s + ENNReal.ofReal δ * payA K root flag s (flq K f)) :=
          add_le_add (mul_le_mul_left hmono _) le_rfl
      _ ≤ _ := le_of_eq (by ring)

/-! ### Exposures -/

/-- **An exposure step** keeps the weight in mean up to a booked kill, and keeps the exponent and
the pending credit. -/
theorem exposure_mean (s : St) (c : Coordinate) (input : CostSpec.Domain)
    (hQ : IsFLQ K input → s.known c ≠ none) (B : ℝ≥0∞) (hB : B ≤ 1) :
    B * weightA K root s ≤
      ∑' r, Pr[= r | sampleCoordinate c s] * (B * weightA K root r.2 + payK K root s input r.2) := by
  have hmass : ∑' r, Pr[= r | sampleCoordinate c s] = 1 := tsum_probOutput_eq_one' probFailure_eq_zero
  cases hk : s.known c with
  | some v =>
      rw [sampleCoordinate_known c s v hk, tsum_probOutput_pure_mul]
      exact le_self_add
  | none =>
      rw [sampleCoordinate_unknown c s hk, tsum_probOutput_map_mul]
      have hnQ : ¬IsFLQ K input := fun h => hQ h hk
      by_cases hnc : NearContact K root s
      · rw [weightA_of_badP K root (Or.inr (Or.inr (Or.inr hnc))), mul_zero]
        exact bot_le
      by_cases hkill : NearContact K root (s.expose c 0)
      · -- every exposed value completes a contact: a booked kill
        have hall : ∀ v, NearContact K root (s.expose c v) := fun v =>
          (nearContact_expose_iff K root s c v 0).2 hkill
        have hp : ∀ v, payK K root s input (s.expose c v) = weightA K root s := fun v => by
          unfold payK; rw [if_pos ⟨hnQ, hall v, hnc⟩]
        simp only [hp]
        calc B * weightA K root s ≤ weightA K root s := mul_le_of_le_one_left' hB
          _ ≤ ∑' v, Pr[= v | ($ᵗ Digest : ProbComp Digest)] * (B * weightA K root (s.expose c v) +
                weightA K root s) :=
              const_le_tsum_of_support _ (tsum_probOutput_eq_one' (probFailure_uniformSample _)) _ _
                fun v _ => le_add_self
      · have hnone : ∀ v, ¬NearContact K root (s.expose c v) := fun v h =>
          hkill ((nearContact_expose_iff K root s c v 0).1 h)
        have hwB : ∀ v, weightA K root (s.expose c v) = weightB K (s.expose c v) := fun v => by
          rw [weightA_eq_weightB, if_neg (hnone v)]
        have hmean := weightB_expose_mean K s c hk
        rw [weightA_eq_weightB, if_neg hnc]
        calc B * weightB K s = B * ∑' v, Pr[= v | ($ᵗ Digest : ProbComp Digest)] * weightB K (s.expose c v) := by
              rw [hmean]
          _ = ∑' v, Pr[= v | ($ᵗ Digest : ProbComp Digest)] * (B * weightA K root (s.expose c v)) := by
              rw [← ENNReal.tsum_mul_left]
              exact tsum_congr fun v => by rw [hwB]; ring
          _ ≤ _ := ENNReal.tsum_le_tsum fun v => mul_le_mul_right le_self_add _

/-- An exposure keeps the pending credit and does not raise the weight times it in mean. -/
theorem exposure_pend (s : St) (c : Coordinate) :
    ∑' r, Pr[= r | sampleCoordinate c s] * (weightA K root r.2 * pendA K r.2) ≤ weightA K root s * pendA K s := by
  have hst : ∀ r ∈ support (sampleCoordinate c s), pendA K r.2 = pendA K s := fun r hr => by
    cases hk : s.known c with
    | some v =>
        rw [sampleCoordinate_known c s v hk, support_pure, Set.mem_singleton_iff] at hr
        rw [hr]
    | none =>
        rw [sampleCoordinate_expose c s r hr]
        rfl
  calc ∑' r, Pr[= r | sampleCoordinate c s] * (weightA K root r.2 * pendA K r.2)
      = ∑' r, Pr[= r | sampleCoordinate c s] * weightA K root r.2 * pendA K s := by
        refine tsum_congr fun r => ?_
        by_cases hr : r ∈ support (sampleCoordinate c s)
        · rw [hst r hr]; ring
        · rw [probOutput_eq_zero_of_not_mem_support hr]; simp
    _ = (∑' r, Pr[= r | sampleCoordinate c s] * weightA K root r.2) * pendA K s := ENNReal.tsum_mul_right
    _ ≤ weightA K root s * pendA K s := by
        gcongr
        by_cases hnc : NearContact K root s
        · have hz : ∀ r ∈ support (sampleCoordinate c s), weightA K root r.2 = 0 := fun r hr =>
            weightA_of_badP K root (badP_mono (extends_sampleCoordinate c s r hr) (Or.inr (Or.inr (Or.inr hnc))))
          exact le_trans (tsum_le_const_of_support _ _ 0 fun r hr => le_of_eq (hz r hr)) bot_le
        · calc ∑' r, Pr[= r | sampleCoordinate c s] * weightA K root r.2
              ≤ ∑' r, Pr[= r | sampleCoordinate c s] * weightB K r.2 :=
                ENNReal.tsum_le_tsum fun r => mul_le_mul_right (weightA_le_weightB K root r.2) _
            _ = weightB K s := weightB_sample_mean K c s
            _ = weightA K root s := by rw [weightA_eq_weightB, if_neg hnc]

theorem exposure_expo (s : St) (c : Coordinate) (flag : Bool) :
    ∀ r ∈ support (sampleCoordinate c s), expo K ρ flag r.2 = expo K ρ flag s := fun r hr => by
  cases hk : s.known c with
  | some v =>
      rw [sampleCoordinate_known c s v hk, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]
  | none =>
      rw [sampleCoordinate_expose c s r hr]
      rfl

end Misc

end FORS.Security.SWRoute
