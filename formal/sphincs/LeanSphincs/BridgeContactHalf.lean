import LeanSphincs.BridgeContactBound

/-! Ingredients of the A4b potential `C_F · potNear(y) + 2^-128 · Σ_{j < y} potNear(j)` of
`BridgeArmA4b`: the signing lemmas of `BridgeForsGeneric` with the forecast level decoupled from the
run's budget, finite sums under expectations, the new-pair step of `potNear` (a new pair moves every
level down by one), and the start sum: with `startNear y ≤ 2h`, the near potentials at the levels
below `y` sum to at most `y (y (h + φ) + N φ)`. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] digestAttemptLimit

variable [Params]

/-! ### Signing at a decoupled level -/

/-- The bound for one signing outcome with the gate and the signature limit: zero once the gate is
on or no signature is left. -/
noncomputable def canonL (parameter : PublicParameter) (data : PublicData) (W : View → Multiset View → ℝ≥0∞)
    (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (gate : State → Prop) (m : Message) (s : State)
    (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (K : ℕ)
    (out : Run HashInput Coordinate (Option Signature) × State) : ℝ≥0∞ :=
  if gate s ∨ signatureLimit ≤ L.length then 0
  else canonG parameter data W wbar b0 Fail m s P L d (signatureLimit - (L.length + 1)) K out

section SignLevel

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) {W : View → Multiset View → ℝ≥0∞} (wbar b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ) (m : Message)

/-- **The potential after one signing outcome, at any level.** The level `K` of the bound is free
of the run's budget. -/
theorem sign_pointG_level (hW : WitnessProps W) {gate : State → Prop}
    (hgate : ∀ s s' : State, Extends s s' → gate s → gate s')
    (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hfail : ∀ ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (attempts budget : ℕ) (s : State) (P : List Pair) (L : QueryLog SigningSpec)
    (d : Multiset View) (R : List Coordinate) (hprep : Prepared initial s) (hP : PInv parameter data s P)
    (hD : DInv R d) (hC : CountInv parameter data Qtot s budget)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSourceLoop parameter data m attempts) budget s))
    (r : Option Signature) (hr : out.1.1 = some r) {k' K : ℕ} (hk : k' ≤ K) :
    potG parameter data W wbar b0 Fail gate out.2 (newPairs parameter data m s out.2 ++ P) (L ++ [⟨m, r⟩])
        (discAfter parameter data m s d out) k' ≤
      canonL parameter data W wbar b0 Fail gate m s P L d K out := by
  unfold canonL
  obtain ⟨_, hP', _, _, hview⟩ := sign_params tg initial model Fail Qtot hparse hfail attempts budget
    s P d R hprep hP hD hC out hout r hr
  have hext := interp_extends tg initial model _ budget s out hout
  have hother := other_message_kept tg initial model attempts budget s out hout
  have hpost := loop_post tg initial model parameter data m (fun ρ call => hparse (m, ρ) call) Fail hfail
    attempts budget s hprep out hout r hr
  have hshape := sign_shape parameter data Fail m hpost out rfl hr
  unfold potG
  by_cases hcase : gate out.2 ∨ signatureLimit < (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length
  · rw [if_pos hcase]; exact bot_le
  rw [if_neg hcase]
  have hreal : ¬gate s := fun h => hcase (Or.inl (hgate s out.2 hext h))
  have hlen : L.length < signatureLimit := by
    have := hcase
    simp only [List.length_append, List.length_singleton, not_or, not_lt] at this
    omega
  rw [if_neg (by push Not; exact ⟨hreal, hlen⟩)]
  have hn : signatureLimit - (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length = signatureLimit - (L.length + 1) := by simp
  rw [hn]
  set n := signatureLimit - (L.length + 1) with hndef
  have hnotnew : ∀ q ∈ P, q ∉ newPairs parameter data m s out.2 := by
    intro q hq hnew
    obtain ⟨_, h0, _⟩ := (mem_newPairs parameter data m s).1 hnew
    obtain ⟨u, hu, _⟩ := (hP.mem q).1 hq
    rw [h0] at hu; cases hu
  unfold coreG canonG
  rw [List.map_append, List.sum_append]
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) le_rfl
  · rcases hshape with ⟨hnew, _⟩ | ⟨ρ, u0, u1, hnew, _, h0, hl, h1, hs0, _, hfl, hsig⟩ |
        ⟨_, _, _, _, hnew, _⟩
    · unfold newPairs; rw [hnew]; simp
    · have hs1 : s.cache (blk parameter data m ρ 1) = none := hP.first (m, ρ) hs0
      have hv : pview parameter data out.2 (m, ρ) = viewOf u0 u1 := pview_of_cached h0 h1
      have hlist : newPairs parameter data m s out.2 = [(m, ρ)] := by
        unfold newPairs; rw [hnew, Finset.toList_singleton]; rfl
      rw [hlist]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      refine le_trans ?_ (freshNewWeight_ge hr hs1 h0 hl h1 (fun v => if v.1 ∈ Fail then 1 else 0))
      unfold candG
      rw [hv]
      split_ifs with hu hF hF'
      · exact le_rfl
      · exfalso
        rcases r with _ | sig
        · exact hF (hfl rfl)
        · exact not_unsigned_signed (m := m) (L := L) (sig := sig) (by rw [hsig sig rfl]; exact hu)
      · exact bot_le
      · exact le_rfl
    · unfold newPairs; rw [hnew]; simp
  · refine List.sum_le_sum fun q hq => ?_
    unfold candG
    by_cases hU' : Unsigned (L ++ [⟨m, r⟩] : QueryLog SigningSpec) q
    · have hU := unsigned_of_append hU'
      rw [if_pos hU', if_pos hU, hview q hq]
      split_ifs with hF
      · exact le_rfl
      · unfold candValueG fut
        rw [hview q hq, stateFn_after L m r _ _ hother]
        refine post_term_leO hw (stateFn_props s _ _ (hW _)) _ n _ hk _ fun J => ?_
        refine upper_pointO hw (stateFn_props s _ _ (hW _)) hP (· = q) out r hr Fail hshape
          (fun sig hsig _ heq => ?_) J
        subst hsig
        exact not_unsigned_signed (m := m) (L := L) (by rw [heq]; exact hU')
    · rw [if_neg hU']
      exact bot_le
  · refine mul_le_mul' (by exact_mod_cast hk) (add_le_add ?_ le_rfl)
    unfold hValueG fut
    rw [stateFn_after L m r _ _ hother]
    refine post_term_leO hw (stateFn_props s _ _ (excessW_props hW hb0)) _ n _ hk _ fun J => ?_
    exact upper_pointO hw (stateFn_props s _ _ (excessW_props hW hb0)) hP (fun _ => False) out r hr Fail hshape
      (fun _ _ _ h => h) J

/-- **The signing step in expectation, at any level.** For a forecast level `K` free of the run's
budget: averaged over a signing call run with any budget, the bound at level `K` is at most the
potential at level `K` before the call. -/
theorem sign_expectG_level (hW : WitnessProps W) (gate : State → Prop)
    (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (budget K : ℕ) (s : State) (P : List Pair)
    (L : QueryLog SigningSpec) (hm : ∀ entry ∈ L, entry.1 ≠ m) (d : Multiset View) (hP : PInv parameter data s P) :
    ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m digestAttemptLimit) budget s] *
        canonL parameter data W wbar b0 Fail gate m s P L d K out ≤
      potG parameter data W wbar b0 Fail gate s P L d K := by
  unfold canonL
  by_cases hcase : gate s ∨ signatureLimit ≤ L.length
  · simp only [if_pos hcase, mul_zero, tsum_zero]
    exact bot_le
  simp only [if_neg hcase]
  have hcase' : ¬gate s ∧ L.length < signatureLimit := by push Not at hcase; exact hcase
  have hlen := hcase'.2
  unfold potG
  rw [if_neg (by rintro (h | h); exact hcase'.1 h; omega)]
  set n := signatureLimit - (L.length + 1) with hn
  have hn1 : signatureLimit - L.length = n + 1 := by omega
  rw [hn1]
  have hparse' : ∀ ρ call, model.parse (blk parameter data m ρ call) = none := fun ρ call => hparse (m, ρ) call
  have hnob1 : ∀ ρ, s.cache (blk parameter data m ρ 0) = none → s.cache (blk parameter data m ρ 1) = none :=
    fun ρ h => hP.first (m, ρ) h
  have hlandb1 : ∀ ρ u0, s.cache (blk parameter data m ρ 0) = some u0 → Landed parameter (blockIndex u0) →
      s.cache (blk parameter data m ρ 1) ≠ none := fun ρ u0 h0 hl => hP.second (m, ρ) ⟨u0, h0, hl⟩
  have hmass : ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m digestAttemptLimit) budget s] ≤ 1 :=
    tsum_probOutput_le_one
  have hFN := loop_bound_fresh tg initial model parameter data m hparse' s hnob1 hlandb1
    (fun v => if v.1 ∈ Fail then 1 else 0) digestAttemptLimit budget s (related_self parameter data m s)
  have hT : ∀ q ∈ P, ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m digestAttemptLimit) budget s] *
      (if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
        creations Finset.univ landing (fun J => upperO parameter data wbar m s n d
          (stateFn parameter data s (L ++ [⟨m, none⟩]) (· = q) (W (pview parameter data s q)))
          (· = q) out J) K []) else 0) ≤
      candG parameter data W wbar Fail s P L d (n + 1) K q := by
    intro q _
    unfold candG
    split_ifs
    · rw [ENNReal.tsum_mul_right, mul_one]; exact hmass
    · unfold candValueG
      exact term_expectO tg initial model hparse' hw (hW (pview parameter data s q)) hP (· = q) L hm
        budget K (n := n) (d := d)
    · simp
  have hH := term_expectO tg initial model (n := n) (d := d) hparse' hw (excessW_props hW hb0) hP (fun _ => False)
    L hm budget K
  have hHv : hValueG parameter data W wbar b0 s P L d (n + 1) K =
      fut parameter data wbar s L (fun _ => False) (excessW W b0) (n + 1) K d := rfl
  unfold canonG coreG
  simp only [mul_add, ENNReal.tsum_add]
  rw [tsum_list_sum]
  have hφ : freshAvg Finset.univ (fun v : View => if v.1 ∈ Fail then (1 : ℝ≥0∞) else 0) = failMass Fail := rfl
  rw [hφ] at hFN
  calc _ ≤ failMass Fail + (P.map (candG parameter data W wbar Fail s P L d (n + 1) K)).sum +
        (K * hValueG parameter data W wbar b0 s P L d (n + 1) K + K * failMass Fail) +
          n * failMass Fail := by
        refine add_le_add (add_le_add (add_le_add hFN (List.sum_le_sum hT)) (add_le_add ?_ ?_)) ?_
        · simp only [mul_left_comm _ (K : ℝ≥0∞), ENNReal.tsum_mul_left]
          rw [hHv]
          exact mul_le_mul_right hH _
        · rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' hmass
        · rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' hmass
    _ = _ := by push_cast; ring

end SignLevel

/-! ### Finite sums under expectations -/

omit [Params] in
theorem pairE_range_sum (n : ℕ) (F : HashOutput → HashOutput → ℕ → ℝ≥0∞) :
    pairE (fun a b => ∑ j ∈ Finset.range n, F a b j) = ∑ j ∈ Finset.range n, pairE (fun a b => F a b j) := by
  induction n with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact pairE_const 0
  | succ n ih =>
      simp only [Finset.sum_range_succ]
      rw [pairE_add, ih]

omit [Params] in
theorem tsum_range_sum {β : Type} (w : β → ℝ≥0∞) (n : ℕ) (f : β → ℕ → ℝ≥0∞) :
    ∑' x, w x * ∑ j ∈ Finset.range n, f x j = ∑ j ∈ Finset.range n, ∑' x, w x * f x j := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Finset.sum_range_succ, mul_add, ENNReal.tsum_add, ih]

/-! ### A new pair -/

section StepsH

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A new pair moves the near potential down by one level. -/
theorem potN_newPair (hfair : Fair5 wbar) {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) (L : QueryLog SigningSpec) (d : Multiset View) (j : ℕ) :
    pairE (fun u0 u1 => potN parameter data wbar Fail (withPair parameter data s p u0 u1) (addPair parameter P p u0)
      L d j) ≤ potN parameter data wbar Fail s P L d (j + 1) := by
  unfold potN potG
  by_cases hL : False ∨ signatureLimit < L.length
  · simp only [if_pos hL, pairE_const, le_refl]
  · simp only [if_neg hL]
    have h := coreG_newPair wbar 0 Fail witnessNear_props hfair ENNReal.zero_ne_top hP hp0 L d
      (signatureLimit - L.length) j
    rwa [add_zero] at h

end StepsH

/-! ### The start sum -/

section StartSum

/-- The near forecast at the start grows with the number of future pairs. -/
theorem startNear_mono {wbar : ℝ≥0∞} (hw : wbar ≤ 1) {j k : ℕ} (hjk : j ≤ k) :
    startNear wbar j ≤ startNear wbar k := by
  unfold startNear
  exact creations_mono_count Finset.univ_nonempty landing_le_one
    (virtualOnce_cons_le' wbar hw (excessW_props witnessNear_props ENNReal.zero_ne_top) signatureLimit 0)
    (virtualOnce_perm' wbar signatureLimit 0) hjk []

/-- **The start sum.** With `startNear y ≤ 2h`, the near potentials at the levels below `y` sum
to at most `y (y (h + φ) + N φ)`: the levels average `y / 2`. -/
theorem start_sum_le {wbar : ℝ≥0∞} (hw : wbar ≤ 1) (y : ℕ) (φ h : ℝ≥0∞) (hh : startNear wbar y ≤ 2 * h) :
    ∑ j ∈ Finset.range y, ((j : ℝ≥0∞) * (startNear wbar j + φ) + signatureLimit * φ) ≤
      y * (y * (h + φ) + signatureLimit * φ) := by
  set T : ℝ≥0∞ := ∑ j ∈ Finset.range y, (j : ℝ≥0∞) with hTdef
  have hT : T * 2 ≤ (y : ℝ≥0∞) * y := by
    have h1 : (∑ j ∈ Finset.range y, j) * 2 ≤ y * y := by
      rw [Finset.sum_range_id_mul_two]
      exact Nat.mul_le_mul_left _ (Nat.sub_le y 1)
    have h2 : (((∑ j ∈ Finset.range y, j) * 2 : ℕ) : ℝ≥0∞) ≤ ((y * y : ℕ) : ℝ≥0∞) := Nat.cast_le.2 h1
    simpa only [hTdef, Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat] using h2
  calc ∑ j ∈ Finset.range y, ((j : ℝ≥0∞) * (startNear wbar j + φ) + signatureLimit * φ)
      ≤ ∑ j ∈ Finset.range y, ((j : ℝ≥0∞) * (2 * h + φ) + signatureLimit * φ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        gcongr
        exact le_trans (startNear_mono hw (Finset.mem_range.1 hj).le) hh
    _ = T * 2 * h + T * φ + y * (signatureLimit * φ) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ y * y * h + y * y * φ + y * (signatureLimit * φ) := by
        gcongr
        exact le_trans (le_mul_of_one_le_right' one_le_two) hT
    _ = _ := by ring

omit [Params] in
theorem ofReal_half (c : ℚ) : ENNReal.ofReal (c : ℝ) = 2 * ENNReal.ofReal ((c / 2 : ℚ) : ℝ) := by
  calc ENNReal.ofReal (c : ℝ) = ENNReal.ofReal (2 * ((c / 2 : ℚ) : ℝ)) := by
        congr 1
        push_cast
        ring
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]

end StartSum

end LeanSphincs.Security.ForsPotential
