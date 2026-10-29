import FORS.SWRoute.StepsMisc

/-! **The SW route: one step, all input classes.** The dispatch of an input of the interpreted run
to its class, with the probe count after the step (one more after a fresh answer that is no digest
block) and the route's invariant after it. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open Concrete HiddenGraph HiddenDebt HiddenBridge HiddenCost PotentialA GraphView ForsPotential

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

section Step

variable (K : Ctx) (root : Digest) (model : HiddenRows.Model HashInput HashOutput Address Coordinate)
  (ρ β δ cU : ℝ)

/-! ### Invariants -/

theorem invS_aux (hH : StepHyp K model) (input : CostSpec.Domain) (s : St) (p : ℕ) (hinv : InvS K s p) :
    ∀ r ∈ support (costStep model input s), K.Inv r.2 ∧ ∀ f : FIn, r.2.known f.outC = some (K.F f.outC) := by
  intro r hr
  exact ⟨K.inv_step model hH.parse hH.incoming input s hinv.lin r hr,
    fun f => (extends_costStep model input s r hr).2.1 _ _ (hinv.leaf f)⟩

theorem uaSet_readOutside_sub (s0 : St) (x : HashInput) (hi : K.initial x = none) :
    ∀ r ∈ support (readOutside x s0), K.UAset r.2 ⊆ insert x (K.UAset s0) := by
  intro r hr
  rcases readOutside_support x s0 r hr with h | ⟨hc, h⟩
  · rw [h]; exact Set.subset_insert _ _
  · rw [h]; exact K.uaSet_store r.1 hc hi

theorem uaSet_readOutside_sub_notA (s0 : St) (x : HashInput) (hi : K.initial x = none)
    (hA : ∀ l i, Retained K.p l → ¬K.IsA l i x) :
    ∀ r ∈ support (readOutside x s0), K.UAset r.2 ⊆ K.UAset s0 := by
  intro r hr
  rcases readOutside_support x s0 r hr with h | ⟨hc, h⟩
  · rw [h]
  · rw [h]; exact K.uaSet_store_of_not r.1 hc hi hA

theorem encard_le_succ_of_sub {S T : Set HashInput} {x : HashInput} {p : ℕ} (h : S ⊆ insert x T)
    (hT : T.encard ≤ p) : S.encard ≤ (p + 1 : ℕ) :=
  calc S.encard ≤ (insert x T).encard := Set.encard_le_encard h
    _ ≤ T.encard + 1 := Set.encard_insert_le T x
    _ ≤ p + 1 := add_le_add hT le_rfl
    _ = (p + 1 : ℕ) := by push_cast; rfl

/-- The step bound holds trivially from a bad state. -/
theorem stepBound_or_bad (input : CostSpec.Domain) (s : St) (flag : Bool) (p r p' : ℕ)
    (h : ¬BadP K root s → StepBound K root model ρ β δ cU input s flag p r p') :
    StepBound K root model ρ β δ cU input s flag p r p' := by
  by_cases hb : BadP K root s
  · exact stepBound_of_badP K root model ρ β δ cU input s flag p r p' hb
  · exact h hb

/-! ### Exposure steps -/

theorem step_canonical {total : ℕ} (hN : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (s : St) (flag : Bool)
    (p r0 : ℕ) (hb : ¬BadP K root s) (x : HashInput) (c : Coordinate) (comb : Digest → HashOutput)
    (hcs : costStep model (.inl (.inr (.inl x))) s = (fun r => (comb r.1, r.2)) <$> sampleCoordinate c s)
    (hQ : IsFLQ K (.inl (.inr (.inl x))) → s.known c ≠ none) (hF : payF K root s (.inl (.inr (.inl x))) = 0)
    (hC : payC K root s (.inl (.inr (.inl x))) = 0) (hA : payA K root flag s (.inl (.inr (.inl x))) = 0)
    (hnf : nextFlag K root flag s (.inl (.inr (.inl x))) = flag) (hle : p + r0 + 1 ≤ total) :
    StepBound K root model ρ β δ cU (.inl (.inr (.inl x))) s flag p (r0 + 1) p := by
  unfold StepBound
  rw [show sourceCost (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inr (.inl x))) = 1 from rfl,
    Nat.add_sub_cancel, hcs, tsum_probOutput_map_mul, tsum_probOutput_map_mul, tsum_probOutput_map_mul,
    hF, hC, hA, hnf, mul_zero, mul_zero, add_zero, add_zero, mul_zero, add_zero]
  have hexp := exposure_expo K ρ s c flag
  have hB1 : budgetE (expo K ρ flag s) p r0 ≤ 1 :=
    budgetE_le_one (expo_nonneg K ρ (by linarith [hN.low]) flag s) p r0
      (by have := sw_lt hN hle; push_cast; linarith)
  have hmono : budgetE (expo K ρ flag s) p (r0 + 1) ≤ budgetE (expo K ρ flag s) p r0 :=
    budgetE_succ_le (expo_nonneg K ρ (by linarith [hN.low]) flag s) p r0
      (by have := sw_lt hN hle; push_cast; linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)])
  have hm := exposure_mean K root s c _ hQ _ hB1
  have hp := exposure_pend K root s c
  have hsum : ∑' r, Pr[= r | sampleCoordinate c s] *
        (budgetE (expo K ρ flag r.2) p r0 * weightA K root r.2) +
      ∑' r, Pr[= r | sampleCoordinate c s] * payK K root s (.inl (.inr (.inl x))) r.2 =
      ∑' r, Pr[= r | sampleCoordinate c s] *
        (budgetE (expo K ρ flag s) p r0 * weightA K root r.2 + payK K root s (.inl (.inr (.inl x))) r.2) := by
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun r => ?_
    by_cases hr : r ∈ support (sampleCoordinate c s)
    · rw [hexp r hr, mul_add]
    · rw [probOutput_eq_zero_of_not_mem_support hr]; simp
  calc budgetE (expo K ρ flag s) p (r0 + 1) * weightA K root s +
        ∑' r, Pr[= r | sampleCoordinate c s] * (weightA K root r.2 * pendA K r.2)
      ≤ budgetE (expo K ρ flag s) p r0 * weightA K root s + weightA K root s * pendA K s :=
        add_le_add (mul_le_mul_left hmono _) hp
    _ ≤ (∑' r, Pr[= r | sampleCoordinate c s] *
          (budgetE (expo K ρ flag r.2) p r0 * weightA K root r.2) +
        ∑' r, Pr[= r | sampleCoordinate c s] * payK K root s (.inl (.inr (.inl x))) r.2) +
          weightA K root s * pendA K s := by rw [hsum]; exact add_le_add hm le_rfl
    _ = _ := by ring

theorem step_reveal {total : ℕ} (hN : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (s : St) (flag : Bool)
    (p r : ℕ) (hb : ¬BadP K root s) (c : Coordinate) (hle : p + r ≤ total) :
    StepBound K root model ρ β δ cU (.inl (.inr (.inr c))) s flag p r p := by
  have hnQ := not_isFLQ_reveal K c
  have hcs : costStep model (.inl (.inr (.inr c))) s = (fun r' => (r'.1, r'.2)) <$> sampleCoordinate c s := by
    rw [costStep_inl, lazyStep_reveal]
    simp
  unfold StepBound
  rw [show sourceCost (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inr (.inr c))) = 0 from rfl,
    Nat.sub_zero, hcs, tsum_probOutput_map_mul, tsum_probOutput_map_mul, tsum_probOutput_map_mul,
    payF_reveal, payC_of_not K root s _ hnQ, payA_of_not K root flag s _ hnQ, nextFlag_of_not K root flag s _ hnQ,
    mul_zero, mul_zero, add_zero, add_zero, mul_zero, add_zero]
  have hexp := exposure_expo K ρ s c flag
  have hB1 : budgetE (expo K ρ flag s) p r ≤ 1 :=
    budgetE_le_one (expo_nonneg K ρ (by linarith [hN.low]) flag s) p r
      (by have := hN.total_lt_space; have h' : ((p + r : ℕ) : ℝ) ≤ total := by exact_mod_cast hle
          push_cast at h'; linarith)
  have hm := exposure_mean K root s c _ (fun h => absurd h hnQ) _ hB1
  have hp := exposure_pend K root s c
  have hsum : ∑' r', Pr[= r' | sampleCoordinate c s] *
        (budgetE (expo K ρ flag r'.2) p r * weightA K root r'.2) +
      ∑' r', Pr[= r' | sampleCoordinate c s] * payK K root s (.inl (.inr (.inr c))) r'.2 =
      ∑' r', Pr[= r' | sampleCoordinate c s] *
        (budgetE (expo K ρ flag s) p r * weightA K root r'.2 + payK K root s (.inl (.inr (.inr c))) r'.2) := by
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun r' => ?_
    by_cases hr : r' ∈ support (sampleCoordinate c s)
    · rw [hexp r' hr, mul_add]
    · rw [probOutput_eq_zero_of_not_mem_support hr]; simp
  calc budgetE (expo K ρ flag s) p r * weightA K root s +
        ∑' r', Pr[= r' | sampleCoordinate c s] * (weightA K root r'.2 * pendA K r'.2)
      ≤ budgetE (expo K ρ flag s) p r * weightA K root s + weightA K root s * pendA K s := add_le_add le_rfl hp
    _ ≤ (∑' r', Pr[= r' | sampleCoordinate c s] *
          (budgetE (expo K ρ flag r'.2) p r * weightA K root r'.2) +
        ∑' r', Pr[= r' | sampleCoordinate c s] * payK K root s (.inl (.inr (.inr c))) r'.2) +
          weightA K root s * pendA K s := by rw [hsum]; exact add_le_add hm le_rfl
    _ = _ := by ring

/-! ### Chain steps below the word, by position -/

theorem step_chain_fresh {total : ℕ} (hN : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (hH : StepHyp K model)
    (s : St) (flag : Bool) (p r0 : ℕ) (hinv : InvS K s p) (hb : ¬BadP K root s)
    {l : OtsKey} (hl : Retained K.p l) (chain : ChainIndex) (step : ChainStep) (v : Digest)
    (hlt : step.val < (K.w l chain).val) (hx : s.cache (chainInput K.p l chain step v) = none)
    (gs : List (Coordinate × Digest))
    (hcs : costStep model (.inl (.inr (.inl (chainInput K.p l chain step v)))) s =
      readOutside (chainInput K.p l chain step v) { s with guesses := gs })
    (g : ℝ≥0∞) (hW0ge : g * weightA K root s ≤ weight K.tg K.initial { s with guesses := gs })
    (hW0le : weight K.tg K.initial { s with guesses := gs } ≤ weightA K root s)
    (hgpf : probeFactor p ≤ g) (hgtop : g ≠ ⊤) (hle : p + r0 + 1 ≤ total) :
    StepBound K root model ρ β δ cU (.inl (.inr (.inl (chainInput K.p l chain step v)))) s flag p (r0 + 1)
      (p + 1) := by
  set x := chainInput K.p l chain step v with hxdef
  by_cases h1 : step.val + 1 = (K.w l chain).val
  · exact step_chainB K root model ρ β δ cU hN hH s flag p r0 hinv hb hl ⟨step, h1, rfl⟩ hx gs hcs g hW0ge hW0le
      hgpf hgtop hle
  by_cases h2 : step.val + 2 = (K.w l chain).val
  · exact step_chainA K root model ρ β δ cU hN hH s flag p r0 hinv hb hl ⟨step, v, h2, rfl⟩ hx gs hcs g hW0ge
      hW0le hgpf hgtop hle
  have hkind : K.tg.kind x = .none := hH.sec x (Or.inl ⟨l.1, l.2.1, l.2.2, chain, step, v, rfl, fun h => by
    have : (K.w l chain).val ≤ step.val := h.2
    omega⟩)
  refine step_noShape K root model ρ β δ cU hN hH s flag p r0 hinv hb hx hkind ?_ ?_ ?_ ?_ ?_ gs hcs g hW0ge
    hW0le hgpf hle
  · rintro l' i' _ ⟨st, pay, hst, heq⟩
    obtain ⟨rfl, rfl, rfl, -⟩ := chainInput_inj heq
    exact h2 hst
  · rintro l' i' v' _ ⟨st, hst, heq⟩
    obtain ⟨rfl, rfl, rfl, -⟩ := chainInput_inj heq
    exact h1 hst
  · intro l' msg ctr _ h
    exact chainInput_ne_enc h
  · intro f h
    exact chainInput_ne_fleaf h
  · intro h
    exact msg_ne_chain h rfl

/-! ### The dispatch -/

/-- **One step of the S-part.** -/
theorem sStep {total : ℕ} (hN : SWNumeric ρ β δ ((total : ℝ) / 2 ^ 128) cU) (hH : StepHyp K model)
    (input : CostSpec.Domain) (s : St) (flag : Bool) (probes remaining : ℕ) (hinv : InvS K s probes)
    (hcost : sourceCost input ≤ remaining) (hsum : probes + remaining ≤ total) :
    ∃ probes', probes' + (remaining - sourceCost input) ≤ total ∧
      (∀ r ∈ support (costStep model input s), InvS K r.2 probes') ∧
      StepBound K root model ρ β δ cU input s flag probes remaining probes' := by
  have haux := invS_aux K model hH input s probes hinv
  have hp : (probes : ℝ) < spaceReal := by
    have := hN.total_lt_space
    have h0 : probes ≤ total := le_trans (Nat.le_add_right probes remaining) hsum
    have h' : (probes : ℝ) ≤ total := by exact_mod_cast h0
    linarith
  rcases input with (draw | (x | c)) | amount
  · -- a draw
    refine ⟨probes, by simp only [sourceCost]; omega, fun r hr => ?_, ?_⟩
    · rw [costStep_inl, lazyStep_draw, support_map] at hr
      obtain ⟨v, _, rfl⟩ := hr
      exact hinv
    · unfold StepBound
      have hnQ := not_isFLQ_draw K draw
      rw [show sourceCost (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inl draw)) = 0 from rfl,
        Nat.sub_zero, costStep_inl, lazyStep_draw, tsum_probOutput_map_mul, tsum_probOutput_map_mul,
        tsum_probOutput_map_mul, payF_draw, payC_of_not K root s _ hnQ, payA_of_not K root flag s _ hnQ,
        nextFlag_of_not K root flag s _ hnQ]
      have hk : payK K root s (.inl (.inl draw)) s = 0 := by unfold payK; simp
      simp only [hk, mul_zero, add_zero, ENNReal.tsum_mul_right]
      rw [tsum_probOutput_eq_one' probFailure_eq_zero, one_mul, one_mul]
      exact add_le_add le_rfl le_self_add
  · -- an ordinary query
    have hc1 : sourceCost (D := HashInput) (R := HashOutput) (ι := Coordinate) (.inl (.inr (.inl x))) = 1 := rfl
    rw [hc1] at hcost ⊢
    obtain ⟨r0, rfl⟩ : ∃ r0, remaining = r0 + 1 := ⟨remaining - 1, by omega⟩
    have hle : probes + r0 + 1 ≤ total := by omega
    rw [Nat.add_sub_cancel]
    have hcsO : costStep model (.inl (.inr (.inl x))) s = (lazyStep model (.inr (.inl x))).run s := costStep_inl _ _ _
    cases hpx : model.parse x with
    | none =>
        have hpx' : HiddenGraph.parse K.p (candidateActive K.p) x = none := by rw [← hH.parse]; exact hpx
        have hcs : costStep model (.inl (.inr (.inl x))) s = readOutside x s := by
          rw [hcsO]; exact lazyStep_unparsed model x s hpx
        have hnF : ∀ f : FIn, x ≠ f.input K.p := fun f h => by
          rw [h, parse_fleaf] at hpx'; cases hpx'
        have hnQ : ¬IsFLQ K (.inl (.inr (.inl x))) := fun h => by
          obtain ⟨f, hf⟩ := (isFLQ_ordinary_iff K x).1 h
          exact hnF f hf
        cases hcx : s.cache x with
        | some u =>
            -- a cached unparsed read
            have hcs' : costStep model (.inl (.inr (.inl x))) s = pure (u, s) := by
              rw [hcs]; exact readOutside_cached x s u hcx
            refine ⟨probes, by omega, fun r hr => ?_, ?_⟩
            · rw [hcs', support_pure, Set.mem_singleton_iff] at hr
              rw [hr]; exact hinv
            · refine stepBound_or_bad K root model ρ β δ cU _ s flag _ _ _ fun hb => ?_
              refine step_cached K root model ρ β δ cU hN s s flag probes r0 hb x u hcs' rfl (fun _ => rfl) rfl
                ?_ (payC_of_not K root s _ hnQ) (payA_of_not K root flag s _ hnQ)
                (nextFlag_of_not K root flag s _ hnQ) hle
              unfold payK; simp
        | none =>
            have hi : K.initial x = none := initial_none_of_fresh K.initial s hinv.sat.prepared x hcx
            have hnA : ∀ l i, Retained K.p l → ¬K.IsA l i x := fun l i hl ⟨st, pay, _, heq⟩ => by
              rw [heq, ← input_chain] at hpx'
              rw [parse_input _ _ _ hl] at hpx'
              cases hpx'
            have hnB : ∀ l i v, Retained K.p l → ¬K.IsB l i v x := fun l i v hl ⟨st, _, heq⟩ => by
              rw [heq, ← input_chain] at hpx'
              rw [parse_input _ _ _ hl] at hpx'
              cases hpx'
            by_cases hd : ForsSigner.IsMsgInput x
            · -- a fresh digest block
              refine ⟨probes, by omega, fun r hr => ?_, ?_⟩
              · rw [hcs] at hr
                exact ⟨inv_readOutside_none K.tg K.initial x s probes hinv.sat (hH.msg x hd) r hr, (haux r (hcs ▸ hr)).1,
                  (haux r (hcs ▸ hr)).2,
                  (Set.encard_le_encard (uaSet_readOutside_sub_notA K s x hi hnA r hr)).trans hinv.ua⟩
              · exact stepBound_or_bad K root model ρ β δ cU _ s flag _ _ _ fun hb =>
                  step_digest_fresh K root model ρ β δ cU hN hH s flag probes r0 hinv hb hcx hd hcs hle
            · -- a fresh first-order answer
              refine ⟨probes + 1, by omega, fun r hr => ?_, ?_⟩
              · rw [hcs] at hr
                exact ⟨inv_readOutside K.tg K.initial x s probes hinv.sat r hr, (haux r (hcs ▸ hr)).1,
                  (haux r (hcs ▸ hr)).2, encard_le_succ_of_sub (uaSet_readOutside_sub K s x hi r hr) hinv.ua⟩
              · refine stepBound_or_bad K root model ρ β δ cU _ s flag _ _ _ fun hb => ?_
                by_cases hE : ∃ (l : OtsKey) (msg : HashInput) (ctr : Counter), Retained K.p l ∧ x = Wots.encodingInput K.p l.1 l.2.1 l.2.2 msg ctr
                · obtain ⟨l, msg, ctr, hl, rfl⟩ := hE
                  exact step_enc K root model ρ β δ cU hN hH s flag probes r0 hinv hb hl msg ctr hcx hcs hle
                · push Not at hE
                  exact step_other1 K root model ρ β δ cU hN hH s flag probes r0 hinv hb hcx hcs hnF hd hnA hnB
                    (fun l msg ctr hl => hE l msg ctr hl) hle
    | some q =>
        have hpx' : HiddenGraph.parse K.p (candidateActive K.p) x = some q := by rw [← hH.parse]; exact hpx
        obtain ⟨hxq, hact⟩ := (parse_some_iff _ _ x q).1 hpx'
        have hi : K.initial x = none := hH.parsedFresh x q hpx'
        have hM : ¬ForsSigner.IsMsgInput x := fun h => by
          rw [parse_msg_none _ _ x h] at hpx'; cases hpx'
        obtain ⟨addr, v⟩ := q
        cases addr with
        | chain lay tree leaf chain step =>
            set l : OtsKey := (lay, tree, leaf) with hldef
            have hl : Retained K.p l := hact
            have hxc : x = chainInput K.p l chain step v := hxq
            have hnQ : ¬IsFLQ K (.inl (.inr (.inl x))) := fun h => by
              obtain ⟨f, hf⟩ := (isFLQ_ordinary_iff K x).1 h
              rw [hxc] at hf
              exact chainInput_ne_fleaf hf
            have hinc : model.incoming (Address.chain lay tree leaf chain step) =
                Coordinate.chain lay tree leaf chain ⟨step.val, by have := step.isLt; omega⟩ := by
              rw [hH.incoming]; rfl
            cases hk : s.known (model.incoming (Address.chain lay tree leaf chain step)) with
            | none =>
                have hcs : costStep model (.inl (.inr (.inl x))) s =
                    readOutside x (s.record (model.incoming (Address.chain lay tree leaf chain step), v)) := by
                  rw [hcsO]; exact lazyStep_guess model x s _ hpx hk
                -- the input coordinate is below the word: anchors are known
                have hlt : step.val < (K.w l chain).val := by
                  by_contra hge
                  push Not at hge
                  have hanc : K.Anchor (Coordinate.chain lay tree leaf chain ⟨step.val, by have := step.isLt; omega⟩) :=
                    ⟨hl, hge⟩
                  rw [hinc, hinv.lin.anchored _ hanc] at hk
                  cases hk
                cases hcx : s.cache x with
                | some u =>
                    -- a guess at a cached chain input: already recorded
                    have hg : (model.incoming (Address.chain lay tree leaf chain step), v) ∈ s.guesses := by
                      rw [hH.incoming] at hk ⊢
                      exact hinv.lin.guessed x u _ ⟨hcx, hi⟩ hpx' hk
                    have hcs' : costStep model (.inl (.inr (.inl x))) s =
                        pure (u, s.record (model.incoming (Address.chain lay tree leaf chain step), v)) := by
                      rw [hcs]; exact readOutside_cached x _ u hcx
                    refine ⟨probes, by omega, fun r hr => ?_, ?_⟩
                    · rw [hcs', support_pure, Set.mem_singleton_iff] at hr
                      rw [hr]
                      refine ⟨hinv.sat.same K.tg K.initial (fun c => ?_) hinv.sat.prepared, hinv.lin.record _,
                        hinv.leaf, hinv.ua⟩
                      rw [debts_record]
                      split_ifs with h
                      · subst h; exact Set.insert_eq_of_mem (Or.inl (by simpa using hg))
                      · rfl
                    · refine stepBound_or_bad K root model ρ β δ cU _ s flag _ _ _ fun hb => ?_
                      refine step_cached K root model ρ β δ cU hN s _ flag probes r0 hb x u hcs'
                        (weightA_record_of_mem K root s _ hg) (fun fl => expo_record K s _ ρ fl) (pendA_record K s _)
                        ?_ (payC_of_not K root s _ hnQ) (payA_of_not K root flag s _ hnQ)
                        (nextFlag_of_not K root flag s _ hnQ) hle
                      unfold payK; simp [nearContact_record]
                | none =>
                    -- a guess at a fresh chain input
                    refine ⟨probes + 1, by omega, fun r hr => ?_, ?_⟩
                    · rw [hcs] at hr
                      refine ⟨inv_guess K.tg K.initial x s _ probes hinv.sat ?_ r hr, (haux r (hcs ▸ hr)).1,
                        (haux r (hcs ▸ hr)).2, encard_le_succ_of_sub (uaSet_readOutside_sub K _ x hi r hr) hinv.ua⟩
                      rw [hH.sec x (Or.inl ⟨lay, tree, leaf, chain, step, v, hxc, fun h => by
                        have : (K.w l chain).val ≤ step.val := h.2
                        omega⟩)]
                      exact fun h => by cases h
                    · refine stepBound_or_bad K root model ρ β δ cU _ s flag _ _ _ fun hb => ?_
                      have hx' : s.cache (chainInput K.p l chain step v) = none := by rw [← hxc]; exact hcx
                      have hW0ge : probeFactor probes * weightA K root s ≤
                          weight K.tg K.initial (s.record (model.incoming (Address.chain lay tree leaf chain step), v)) := by
                        rw [weightA_eq_weight_of K root hb]
                        exact weight_record K.tg K.initial s _ hk (hinv.sat.finite _) probes (hinv.sat.bound _) hp
                      have hW0le : weight K.tg K.initial (s.record (model.incoming (Address.chain lay tree leaf chain step), v)) ≤
                          weightA K root s := by
                        rw [weightA_eq_weight_of K root hb]
                        exact weight_le_of_extendsW K.tg K.initial (extends_record s _) rfl
                      rw [hxc] at hcs ⊢
                      exact step_chain_fresh K root model ρ β δ cU hN hH s flag probes r0 hinv hb hl chain step v hlt hx'
                        _ hcs (probeFactor probes) hW0ge hW0le le_rfl (probeFactor_ne_top probes) hle
            | some canonical =>
                by_cases heq : v = canonical
                · -- a canonical continuation
                  have hcs : costStep model (.inl (.inr (.inl x))) s =
                      (fun r => (model.combine (Address.chain lay tree leaf chain step) r.1, r.2)) <$>
                        sampleCoordinate (model.outgoing (Address.chain lay tree leaf chain step)) s := by
                    rw [hcsO]; exact lazyStep_canonical model x s _ hpx canonical hk heq
                  refine ⟨probes, by omega, fun r hr => ?_, ?_⟩
                  · refine ⟨?_, (haux r hr).1, (haux r hr).2, ?_⟩
                    · rw [hcs, support_map] at hr
                      obtain ⟨r', hr', rfl⟩ := hr
                      cases hko : s.known (model.outgoing (Address.chain lay tree leaf chain step)) with
                      | some w =>
                          rw [sampleCoordinate_known _ s w hko, support_pure, Set.mem_singleton_iff] at hr'
                          rw [hr']; exact hinv.sat
                      | none =>
                          rw [sampleCoordinate_expose _ s r' hr']
                          exact hinv.sat.expose K.tg K.initial _ _
                    · rw [hcs, support_map] at hr
                      obtain ⟨r', hr', rfl⟩ := hr
                      cases hko : s.known (model.outgoing (Address.chain lay tree leaf chain step)) with
                      | some w =>
                          rw [sampleCoordinate_known _ s w hko, support_pure, Set.mem_singleton_iff] at hr'
                          rw [hr']; exact hinv.ua
                      | none =>
                          rw [sampleCoordinate_expose _ s r' hr']
                          exact hinv.ua
                  · refine stepBound_or_bad K root model ρ β δ cU _ s flag _ _ _ fun hb => ?_
                    refine step_canonical K root model ρ β δ cU hN s flag probes r0 hb x _ _ hcs
                      (fun h => absurd h hnQ) ?_ (payC_of_not K root s _ hnQ) (payA_of_not K root flag s _ hnQ)
                      (nextFlag_of_not K root flag s _ hnQ) hle
                    rw [payF_ordinary, hH.digest, if_neg hM]
                · have hcs : costStep model (.inl (.inr (.inl x))) s = readOutside x s := by
                    rw [hcsO]; exact lazyStep_other model x s _ hpx canonical hk heq
                  cases hcx : s.cache x with
                  | some u =>
                      have hcs' : costStep model (.inl (.inr (.inl x))) s = pure (u, s) := by
                        rw [hcs]; exact readOutside_cached x s u hcx
                      refine ⟨probes, by omega, fun r hr => ?_, ?_⟩
                      · rw [hcs', support_pure, Set.mem_singleton_iff] at hr
                        rw [hr]; exact hinv
                      · refine stepBound_or_bad K root model ρ β δ cU _ s flag _ _ _ fun hb => ?_
                        refine step_cached K root model ρ β δ cU hN s s flag probes r0 hb x u hcs' rfl (fun _ => rfl)
                          rfl ?_ (payC_of_not K root s _ hnQ) (payA_of_not K root flag s _ hnQ)
                          (nextFlag_of_not K root flag s _ hnQ) hle
                        unfold payK; simp
                  | none =>
                      refine ⟨probes + 1, by omega, fun r hr => ?_, ?_⟩
                      · rw [hcs] at hr
                        exact ⟨inv_readOutside K.tg K.initial x s probes hinv.sat r hr, (haux r (hcs ▸ hr)).1,
                          (haux r (hcs ▸ hr)).2, encard_le_succ_of_sub (uaSet_readOutside_sub K s x hi r hr) hinv.ua⟩
                      · refine stepBound_or_bad K root model ρ β δ cU _ s flag _ _ _ fun hb => ?_
                        have hx' : s.cache (chainInput K.p l chain step v) = none := by rw [← hxc]; exact hcx
                        by_cases hlt : step.val < (K.w l chain).val
                        · -- below the word, no guess: factor one
                          have hcs2 : costStep model (.inl (.inr (.inl (chainInput K.p l chain step v)))) s =
                              readOutside (chainInput K.p l chain step v) { s with guesses := s.guesses } := by
                            rw [← hxc]; exact hcs
                          rw [hxc]
                          refine step_chain_fresh K root model ρ β δ cU hN hH s flag probes r0 hinv hb hl chain step v hlt
                            hx' s.guesses hcs2 1 ?_ ?_ (probeFactor_le_one' probes (by
                              have := sw_hp hN hle; linarith)) ENNReal.one_ne_top hle
                          · rw [one_mul, weightA_eq_weight_of K root hb]
                          · rw [weightA_eq_weight_of K root hb]
                        · -- at or above the word: a first-order answer
                          push Not at hlt
                          refine step_other1 K root model ρ β δ cU hN hH s flag probes r0 hinv hb hcx hcs
                            (fun f h => by rw [hxc] at h; exact chainInput_ne_fleaf h) hM ?_ ?_ ?_ hle
                          · rintro l' i' _ ⟨st, pay, hst, heq'⟩
                            rw [hxc] at heq'
                            obtain ⟨rfl, rfl, rfl, -⟩ := chainInput_inj heq'
                            omega
                          · rintro l' i' v' _ ⟨st, hst, heq'⟩
                            rw [hxc] at heq'
                            obtain ⟨rfl, rfl, rfl, -⟩ := chainInput_inj heq'
                            omega
                          · intro l' msg ctr _ h
                            rw [hxc] at h
                            exact chainInput_ne_enc h
        | fleaf index κ leafF =>
            set f : FIn := ⟨index, κ, leafF, v⟩ with hfdef
            have hxf : x = f.input K.p := hxq
            subst hxf
            have hinc : model.incoming (Address.fleaf index κ leafF) = f.inC := by rw [hH.incoming]; rfl
            cases hk : s.known f.inC with
            | none =>
                cases hcx : s.cache (f.input K.p) with
                | some u =>
                    have hg : (f.inC, f.v) ∈ s.guesses :=
                      hinv.lin.guessed _ u (Address.fleaf f.index f.κ f.leaf, f.v) ⟨hcx, hi⟩ (parse_fleaf K f) hk
                    have hcs' : costStep model (flq K f) s = pure (u, s.record (f.inC, f.v)) := by
                      rw [hcsO, lazyStep_guess model _ s (Address.fleaf f.index f.κ f.leaf, f.v) hpx
                        (by rw [hinc]; exact hk), hinc]
                      exact readOutside_cached _ _ u hcx
                    refine ⟨probes, by omega, fun r hr => ?_, ?_⟩
                    · rw [hcs', support_pure, Set.mem_singleton_iff] at hr
                      rw [hr]
                      refine ⟨hinv.sat.same K.tg K.initial (fun c => ?_) hinv.sat.prepared, hinv.lin.record _,
                        hinv.leaf, hinv.ua⟩
                      rw [debts_record]
                      split_ifs with h
                      · subst h; exact Set.insert_eq_of_mem (Or.inl (by simpa using hg))
                      · rfl
                    · exact stepBound_or_bad K root model ρ β δ cU _ s flag _ _ _ fun hb =>
                        step_flq_cached K root model ρ β δ cU hN hH f s flag probes r0 hinv hb u hcx hk hle
                | none =>
                    have hcs : costStep model (flq K f) s = readOutside (f.input K.p) (s.record (f.inC, f.v)) := by
                      rw [hcsO, lazyStep_guess model _ s (Address.fleaf f.index f.κ f.leaf, f.v) hpx
                        (by rw [hinc]; exact hk), hinc]
                    refine ⟨probes + 1, by omega, fun r hr => ?_, ?_⟩
                    · rw [hcs] at hr
                      refine ⟨inv_guess K.tg K.initial _ s _ probes hinv.sat ?_ r hr, (haux r (hcs ▸ hr)).1,
                        (haux r (hcs ▸ hr)).2, encard_le_succ_of_sub (uaSet_readOutside_sub K _ _ hi r hr) hinv.ua⟩
                      rw [hH.sec (f.input K.p) (Or.inr ⟨f.index, f.κ, f.leaf, f.v, rfl⟩)]
                      exact fun h => by cases h
                    · exact stepBound_or_bad K root model ρ β δ cU _ s flag _ _ _ fun hb =>
                        step_flq_guess K root model ρ β δ cU hN hH f s flag probes r0 hinv hb hcx hk hle
            | some canonical =>
                by_cases heq : v = canonical
                · -- a canonical continuation: the leaf value is known
                  have hcs : costStep model (flq K f) s =
                      (fun r => (model.combine (Address.fleaf index κ leafF) r.1, r.2)) <$>
                        sampleCoordinate (model.outgoing (Address.fleaf index κ leafF)) s := by
                    rw [hcsO]; exact lazyStep_canonical model _ s _ hpx canonical (by rw [hinc]; exact hk) heq
                  have hout : model.outgoing (Address.fleaf index κ leafF) = f.outC := by rw [hH.outgoing]; rfl
                  have hko : s.known (model.outgoing (Address.fleaf index κ leafF)) = some (K.F f.outC) := by
                    rw [hout]; exact hinv.leaf f
                  have hcs' : costStep model (flq K f) s =
                      pure (model.combine (Address.fleaf index κ leafF) (K.F f.outC), s) := by
                    rw [hcs, sampleCoordinate_known _ s _ hko, map_pure]
                  have hknone : s.known f.inC ≠ none := by rw [hk]; simp
                  refine ⟨probes, by omega, fun r hr => ?_, ?_⟩
                  · rw [hcs', support_pure, Set.mem_singleton_iff] at hr
                    rw [hr]; exact hinv
                  · refine stepBound_or_bad K root model ρ β δ cU _ s flag _ _ _ fun hb => ?_
                    refine step_cached K root model ρ β δ cU hN s s flag probes r0 hb _ _ hcs' rfl (fun _ => rfl) rfl
                      (payK_flq K root s f s) ?_ (payA_flq_of_not K root flag s f fun h => hknone h.2)
                      (nextFlag_flq_of_not K root flag s f fun h => hknone h.2) hle
                    rw [payC_flq, if_neg (fun h => hknone h.1)]
                · cases hcx : s.cache (f.input K.p) with
                  | some u =>
                      have hcs' : costStep model (flq K f) s = pure (u, s) := by
                        rw [hcsO, lazyStep_other model _ s _ hpx canonical (by rw [hinc]; exact hk) heq]
                        exact readOutside_cached _ s u hcx
                      have hknone : s.known f.inC ≠ none := by rw [hk]; simp
                      refine ⟨probes, by omega, fun r hr => ?_, ?_⟩
                      · rw [hcs', support_pure, Set.mem_singleton_iff] at hr
                        rw [hr]; exact hinv
                      · refine stepBound_or_bad K root model ρ β δ cU _ s flag _ _ _ fun hb => ?_
                        refine step_cached K root model ρ β δ cU hN s s flag probes r0 hb _ u hcs' rfl (fun _ => rfl)
                          rfl (payK_flq K root s f s) ?_ (payA_flq_of_not K root flag s f fun h => hknone h.2)
                          (nextFlag_flq_of_not K root flag s f fun h => hknone h.2) hle
                        rw [payC_flq, if_neg (fun h => hknone h.1)]
                  | none =>
                      have hcs : costStep model (flq K f) s = readOutside (f.input K.p) s := by
                        rw [hcsO]; exact lazyStep_other model _ s _ hpx canonical (by rw [hinc]; exact hk) heq
                      refine ⟨probes + 1, by omega, fun r hr => ?_, ?_⟩
                      · rw [hcs] at hr
                        exact ⟨inv_readOutside K.tg K.initial _ s probes hinv.sat r hr, (haux r (hcs ▸ hr)).1,
                          (haux r (hcs ▸ hr)).2, encard_le_succ_of_sub (uaSet_readOutside_sub K s _ hi r hr) hinv.ua⟩
                      · exact stepBound_or_bad K root model ρ β δ cU _ s flag _ _ _ fun hb =>
                          step_flq_noguess K root model ρ β δ cU hN hH f s flag probes r0 hinv hb hcx canonical hk heq hle
  · -- a reveal
    refine ⟨probes, by simp only [sourceCost]; omega, fun r hr => ?_, ?_⟩
    · refine ⟨?_, (haux r hr).1, (haux r hr).2, ?_⟩
      · rw [costStep_inl, lazyStep_reveal] at hr
        cases hkc : s.known c with
        | some w =>
            rw [sampleCoordinate_known c s w hkc, support_pure, Set.mem_singleton_iff] at hr
            rw [hr]; exact hinv.sat
        | none =>
            rw [sampleCoordinate_expose c s r hr]
            exact hinv.sat.expose K.tg K.initial _ _
      · rw [costStep_inl, lazyStep_reveal] at hr
        cases hkc : s.known c with
        | some w =>
            rw [sampleCoordinate_known c s w hkc, support_pure, Set.mem_singleton_iff] at hr
            rw [hr]; exact hinv.ua
        | none =>
            rw [sampleCoordinate_expose c s r hr]
            exact hinv.ua
    · exact stepBound_or_bad K root model ρ β δ cU _ s flag _ _ _ fun hb =>
        step_reveal K root model ρ β δ cU hN s flag probes remaining hb c hsum
  · -- a tick
    refine ⟨probes, by simp only [sourceCost]; omega, fun r hr => ?_, ?_⟩
    · change r ∈ support (pure ((), s) : ProbComp _) at hr
      rw [support_pure, Set.mem_singleton_iff] at hr
      rw [hr]; exact hinv
    · unfold StepBound
      have hnQ := not_isFLQ_tick K amount
      change budgetE (expo K ρ flag s) probes remaining * weightA K root s +
          (ENNReal.ofReal (β / 2 ^ 128) * payF K root s (.inr amount) +
            ENNReal.ofReal (cU / 2 ^ 128) * payC K root s (.inr amount)) +
          ∑' r, Pr[= r | (pure ((), s) : ProbComp _)] * (weightA K root r.2 * pendA K r.2) ≤
        ∑' r, Pr[= r | (pure ((), s) : ProbComp _)] *
            (budgetE (expo K ρ (nextFlag K root flag s (.inr amount)) r.2) probes (remaining - amount) *
              weightA K root r.2) +
          (weightA K root s * pendA K s + ENNReal.ofReal δ * payA K root flag s (.inr amount) +
            ∑' r, Pr[= r | (pure ((), s) : ProbComp _)] * payK K root s (.inr amount) r.2)
      rw [tsum_probOutput_pure_mul, tsum_probOutput_pure_mul, tsum_probOutput_pure_mul, payF_tick,
        payC_of_not K root s _ hnQ, payA_of_not K root flag s _ hnQ, nextFlag_of_not K root flag s _ hnQ]
      simp only [mul_zero, add_zero]
      refine add_le_add (mul_le_mul_left ?_ _) le_self_add
      refine budgetE_le_of_le (expo_nonneg K ρ (by linarith [hN.low]) flag s) probes _ _ (Nat.sub_le _ _) ?_
      have := hN.total_lt_space
      have h' : ((probes + remaining : ℕ) : ℝ) ≤ total := by exact_mod_cast hsum
      push_cast at h'
      linarith

end Step

end FORS.Security.SWRoute
