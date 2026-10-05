import LeanSphincs.BridgePotentialA5

/-! The linear potential on the interpreted comparison: every step of the cost-level lazy
comparison keeps the potential in expectation while paying the digest baseline, the invariant
is preserved, and the final payoff is bounded by the decided events and the pending debts. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.PotentialA

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost HiddenReveal EncodingCode

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable [Params]

namespace Ctx

variable (K : Ctx)

/-- A reveal keeps the potential in expectation. -/
theorem sample_mean (y : ℕ) (s : St) (c : Coordinate) :
    ∑' r, Pr[= r | sampleCoordinate c s] * K.pot y r.2 ≤ K.pot y s := by
  cases hc : s.known c with
  | some v =>
      rw [sampleCoordinate_known c s v hc, tsum_probOutput_pure_mul]
  | none =>
      rw [sampleCoordinate_unknown c s hc, tsum_probOutput_map_mul]
      exact K.pot_expose_mean y s c hc

theorem inv_sample {s : St} (hinv : K.Inv s) (c : Coordinate) :
    ∀ r ∈ support (sampleCoordinate c s), K.Inv r.2 := by
  intro r hr
  cases hc : s.known c with
  | some v =>
      rw [sampleCoordinate_known c s v hc, support_pure, Set.mem_singleton_iff] at hr
      rw [hr]
      exact hinv
  | none =>
      rw [sampleCoordinate_expose c s r hr]
      exact hinv.expose c r.1 hc

theorem inv_read {s : St} (hinv : K.Inv s) (x : HashInput)
    (hguess : ∀ q, HiddenGraph.parse K.p (candidateActive K.p) x = some q →
      s.known q.1.inputCoordinate = none → (q.1.inputCoordinate, q.2) ∈ s.guesses) :
    ∀ r ∈ support (readOutside x s), K.Inv r.2 := by
  intro r hr
  rcases readOutside_support x s r hr with h | ⟨hc, h⟩
  · rw [h]
    exact hinv
  · rw [h]
    exact hinv.store x r.1 hc hguess

section Model

variable (M : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (hMp : M.parse = HiddenGraph.parse K.p (candidateActive K.p))
  (hMi : M.incoming = Address.inputCoordinate) (hMo : M.outgoing = Address.outputCoordinate)

include hMp hMi in
/-- **The invariant is preserved by every step.** -/
theorem inv_step (input : (SourceCostSpec HashInput HashOutput Coordinate).Domain) (s : St) (hinv : K.Inv s) :
    ∀ r ∈ support (costStep M input s), K.Inv r.2 := by
  intro r hr
  rcases input with (draw | (bytes | c)) | amount
  · rw [costStep_inl, lazyStep_draw, support_map] at hr
    obtain ⟨v, _, rfl⟩ := hr
    exact hinv
  · rw [costStep_inl] at hr
    cases hp : M.parse bytes with
    | none =>
        rw [lazyStep_unparsed M bytes s hp] at hr
        refine K.inv_read hinv bytes (fun q hq _ => ?_) r hr
        rw [← hMp, hp] at hq
        cases hq
    | some q =>
        have hq : HiddenGraph.parse K.p (candidateActive K.p) bytes = some q := by rw [← hMp, hp]
        have huniq : ∀ q', HiddenGraph.parse K.p (candidateActive K.p) bytes = some q' → q' = q :=
          fun q' hq' => Option.some.inj (hq'.symm.trans hq)
        cases hk : s.known (M.incoming q.1) with
        | none =>
            rw [lazyStep_guess M bytes s q hp hk, hMi] at hr
            refine K.inv_read (hinv.record _) bytes (fun q' hq' _ => ?_) r hr
            rw [huniq q' hq']
            exact List.mem_cons_self
        | some canonical =>
            by_cases heq : q.2 = canonical
            · rw [lazyStep_canonical M bytes s q hp canonical hk heq, support_map] at hr
              obtain ⟨r', hr', rfl⟩ := hr
              exact K.inv_sample hinv _ r' hr'
            · rw [lazyStep_other M bytes s q hp canonical hk heq] at hr
              refine K.inv_read hinv bytes (fun q' hq' hk' => ?_) r hr
              rw [huniq q' hq', ← hMi, hk] at hk'
              cases hk'
  · rw [costStep_inl, lazyStep_reveal] at hr
    exact K.inv_sample hinv c r hr
  · change r ∈ support (pure ((), s) : ProbComp _) at hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    rw [hr]
    exact hinv

theorem digestCount_bytes (tg' : Targeting HashInput HashOutput Coordinate) (bytes : HashInput) :
    (digestCount tg' (recorded (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inr (.inl bytes))))
      : ℝ≥0∞) = if tg'.digest bytes then 1 else 0 := by
  simp only [digestCount, recorded, List.filter_cons, List.filter_nil]
  split_ifs with h1 h2 h2 <;> simp_all

include hMp hMi hMo in
/-- **One step.** -/
theorem step (tg' : Targeting HashInput HashOutput Coordinate) (hdig : tg'.digest = ForsSigner.IsMsgInput)
    {total : ℕ} (hN : Numeric K.ρ ((total : ℝ) / 2 ^ 128))
    (hsec : ∀ x, SecondOrderInput K.p K.R x → K.tg.kind x = .none)
    (hmsg : ∀ x, ForsSigner.IsMsgInput x → K.tg.kind x = .none)
    (input : (SourceCostSpec HashInput HashOutput Coordinate).Domain) (budget : ℕ) (s : St) (hinv : K.Inv s)
    (hcost : sourceCost input ≤ budget) :
    ∑' r, Pr[= r | costStep M input s] * K.potCap total (budget - sourceCost input) r.2 +
      ENNReal.ofReal (K.ρ / 2 ^ 128) * digestCount tg' (recorded input) ≤ K.potCap total budget s := by
  unfold potCap
  by_cases hb : budget ≤ total
  swap
  · rw [if_neg hb]
    exact le_top
  rw [if_pos hb]
  have hpot : ∀ r : (SourceCostSpec HashInput HashOutput Coordinate).Range input × St,
      (if budget - sourceCost input ≤ total then K.pot (budget - sourceCost input) r.2 else ⊤) =
        K.pot (budget - sourceCost input) r.2 := fun r => if_pos ((Nat.sub_le _ _).trans hb)
  simp only [hpot]
  have hxr : (0 : ℝ) ≤ (total : ℝ) / 2 ^ 128 := by positivity
  rcases input with (draw | (bytes | c)) | amount
  · have hrec : digestCount tg' (recorded (D := HashInput) (R := HashOutput) (ι := Coordinate)
        (.inl (.inl draw))) = 0 := rfl
    rw [hrec, Nat.cast_zero, mul_zero, add_zero, costStep_inl, lazyStep_draw, tsum_probOutput_map_mul]
    simp only [sourceCost, Nat.sub_zero]
    rw [ENNReal.tsum_mul_right]
    exact mul_le_of_le_one_left' tsum_probOutput_le_one
  · have hcost1 : sourceCost (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inr (.inl bytes))) = 1 :=
      rfl
    rw [hcost1] at hcost ⊢
    obtain ⟨y', rfl⟩ : ∃ y', budget = y' + 1 := ⟨budget - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have hY : (y' : ℝ≥0∞) * ν ≤ ENNReal.ofReal ((total : ℝ) / 2 ^ 128) := budget_le_x (by omega)
    rw [digestCount_bytes, hdig, payment_eq, costStep_inl]
    cases hp : M.parse bytes with
    | none =>
        rw [lazyStep_unparsed M bytes s hp]
        cases hc : s.cache bytes with
        | some u =>
            rw [readOutside_cached bytes s u hc, tsum_probOutput_pure_mul]
            show K.pot y' s + _ ≤ _
            have h := K.pot_same hN.high (by linarith [hN.low]) y' s
              (if ForsSigner.IsMsgInput bytes then 1 else 0) (by split_ifs <;> simp)
            calc K.pot y' s + ν * ENNReal.ofReal K.ρ * (if ForsSigner.IsMsgInput bytes then 1 else 0)
                = K.pot y' s + ν * ((if ForsSigner.IsMsgInput bytes then 1 else 0) * ENNReal.ofReal K.ρ) := by ring
              _ ≤ _ := h
        | none =>
            by_cases hd : ForsSigner.IsMsgInput bytes
            · rw [if_pos hd, mul_one]
              exact K.fresh_digest hN hmsg hinv hc hd
            · rw [if_neg hd, mul_zero, add_zero]
              exact K.fresh_zero hN hxr hY hsec hinv hc
    | some q =>
        have hq : HiddenGraph.parse K.p (candidateActive K.p) bytes = some q := by rw [← hMp, hp]
        have hd : ¬ForsSigner.IsMsgInput bytes := fun hd => by
          rw [parse_msg_none _ _ bytes hd] at hq
          cases hq
        rw [if_neg hd, mul_zero, add_zero]
        cases hk : s.known (M.incoming q.1) with
        | none =>
            rw [lazyStep_guess M bytes s q hp hk, hMi]
            rw [hMi] at hk
            cases hc : s.cache bytes with
            | some u =>
                have hc' : (s.record (q.1.inputCoordinate, q.2)).cache bytes = some u := hc
                rw [readOutside_cached bytes _ u hc', tsum_probOutput_pure_mul]
                exact K.guess_cached hN y' hinv hc q hq hk
            | none => exact K.guess_fresh hN hxr hY hsec hinv hc q hq hk
        | some canonical =>
            by_cases heq : q.2 = canonical
            · rw [lazyStep_canonical M bytes s q hp canonical hk heq, tsum_probOutput_map_mul]
              calc ∑' r, Pr[= r | sampleCoordinate (M.outgoing q.1) s] * K.pot y' r.2
                  ≤ ∑' r, Pr[= r | sampleCoordinate (M.outgoing q.1) s] * K.pot (y' + 1) r.2 :=
                    ENNReal.tsum_le_tsum fun r => mul_le_mul_of_nonneg_left (K.pot_mono (Nat.le_succ _) _) bot_le
                _ ≤ _ := K.sample_mean (y' + 1) s _
            · rw [lazyStep_other M bytes s q hp canonical hk heq]
              cases hc : s.cache bytes with
              | some u =>
                  rw [readOutside_cached bytes s u hc, tsum_probOutput_pure_mul]
                  exact K.pot_mono (Nat.le_succ _) s
              | none => exact K.fresh_zero hN hxr hY hsec hinv hc
  · have hrec : digestCount tg' (recorded (D := HashInput) (R := HashOutput) (ι := Coordinate)
        (.inl (.inr (.inr c)))) = 0 := rfl
    rw [hrec, Nat.cast_zero, mul_zero, add_zero, costStep_inl, lazyStep_reveal]
    simp only [sourceCost, Nat.sub_zero]
    exact K.sample_mean budget s c
  · have hrec : digestCount tg' (recorded (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inr amount)) = 0 :=
      rfl
    rw [hrec, Nat.cast_zero, mul_zero, add_zero]
    change ∑' r, Pr[= r | (pure ((), s) : ProbComp _)] * _ ≤ _
    rw [tsum_probOutput_pure_mul]
    exact K.pot_mono (Nat.sub_le _ _) s

end Model

/-! ### The final payoff -/

theorem payoff_le_one (T : Coordinate → Digest) (s : St) : K.payoff T s ≤ 1 := by
  unfold payoff
  split_ifs <;> simp

/-- Completing an unexposed coordinate hits a set with its share of the space. -/
theorem completion_mem (known : Knowledge Coordinate) (c : Coordinate) (hc : known c = none)
    (S : Set Digest) : Pr[fun T => T c ∈ S | completion known] ≤ (S.encard : ℝ≥0∞) * ν := by
  set Sf : Finset Digest := Finset.univ.filter (· ∈ S) with hSf
  have hS : (S.encard : ℝ≥0∞) = (Sf.card : ℝ≥0∞) := by
    have : S = (Sf : Set Digest) := by
      ext t
      simp [hSf]
    rw [this, Set.encard_coe_eq_coe_finsetCard, ENat.toENNReal_coe]
  calc Pr[fun T => T c ∈ S | completion known] = Pr[fun T => ∃ v ∈ Sf, T c = v | completion known] := by
        refine probEvent_ext fun T _ => ?_
        simp [hSf]
    _ ≤ ∑ v ∈ Sf, Pr[fun T => T c = v | completion known] := probEvent_exists_finset_le_sum _ _ _
    _ = ∑ _v ∈ Sf, ν := Finset.sum_congr rfl fun v _ => by rw [completion_guess known c v hc, one_div]; rfl
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hS]

/-- **Final payoff.** The expected payoff is at most the decided events plus the pending debts. -/
theorem endValue_le (s : St) (y : ℕ) : endValue K.payoff s ≤ K.pot y s := by
  have hle : endValue K.payoff s ≤ K.done s + K.pend s := by
    unfold endValue
    by_cases hb : K.Bad s
    · calc ∑' T, Pr[= T | completion s.known] * K.payoff T s ≤ ∑' T, Pr[= T | completion s.known] :=
            ENNReal.tsum_le_tsum fun T => mul_le_of_le_one_right' (K.payoff_le_one T s)
        _ ≤ 1 := tsum_probOutput_le_one
        _ = K.done s := by rw [done, if_pos hb]
        _ ≤ _ := le_self_add
    · have hpay : ∀ T, K.payoff T s ≤
          if ∃ c, s.known c = none ∧ T c ∈ debts K.tg K.initial s c then 1 else 0 := by
        intro T
        unfold payoff
        split_ifs with h1 h2
        · exact le_rfl
        · exfalso
          rcases h1 with (hr | ⟨c, hc, hT⟩) | hw | hrev | htwo
          · exact hb (Or.inl hr)
          · exact h2 ⟨c, hc, hT⟩
          · exact hb (Or.inr (Or.inl hw))
          · exact hb (Or.inr (Or.inr (Or.inl hrev)))
          · exact hb (Or.inr (Or.inr (Or.inr htwo)))
        · exact bot_le
        · exact le_rfl
      calc ∑' T, Pr[= T | completion s.known] * K.payoff T s
          ≤ ∑' T, Pr[= T | completion s.known] *
              (if ∃ c, s.known c = none ∧ T c ∈ debts K.tg K.initial s c then 1 else 0) :=
            ENNReal.tsum_le_tsum fun T => mul_le_mul_of_nonneg_left (hpay T) bot_le
        _ = Pr[fun T => ∃ c ∈ (Finset.univ : Finset Coordinate), s.known c = none ∧
              T c ∈ debts K.tg K.initial s c | completion s.known] := by
            rw [probEvent_eq_tsum_ite]
            refine tsum_congr fun T => ?_
            simp only [Finset.mem_univ, true_and]
            split_ifs <;> simp
        _ ≤ ∑ c ∈ (Finset.univ : Finset Coordinate),
              Pr[fun T => s.known c = none ∧ T c ∈ debts K.tg K.initial s c | completion s.known] :=
            probEvent_exists_finset_le_sum _ _ _
        _ ≤ K.pend s := by
            unfold pend
            refine Finset.sum_le_sum fun c _ => ?_
            by_cases hc : s.known c = none
            · rw [if_pos hc]
              calc Pr[fun T => s.known c = none ∧ T c ∈ debts K.tg K.initial s c | completion s.known]
                  ≤ Pr[fun T => T c ∈ debts K.tg K.initial s c | completion s.known] :=
                    probEvent_mono fun T _ h => h.2
                _ ≤ _ := completion_mem s.known c hc _
            · rw [if_neg hc]
              exact le_of_eq (probEvent_eq_zero fun T _ h => hc h.1)
        _ ≤ _ := le_add_self
  refine hle.trans ?_
  unfold pot
  rw [add_assoc (K.done s + K.pend s)]
  exact le_self_add

theorem endValue_le_cap (total y : ℕ) (s : St) : endValue K.payoff s ≤ K.potCap total y s := by
  unfold potCap
  split_ifs
  · exact K.endValue_le s y
  · exact le_top

end Ctx

end LeanSphincs.Security.PotentialA
