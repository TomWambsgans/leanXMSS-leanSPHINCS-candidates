import LeanSphincs.LifetimeLocalizedGain
import LeanSphincs.LifetimeAdaptiveOccupancy

/-! Uniform rectangle localization for the candidate bank. Every localized insertion gain
lies inside one retained-leaf rectangle with at most 256 choices per FORS coordinate. A
single event controlling every such rectangle is independent of the disclosure history. -/

namespace LeanSphincs.Lifetime

open OracleComp OracleSpec ENNReal Concrete

set_option exponentiation.threshold 512
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable [Params]

abbrev DigestRectangle := Fin (2 ^ subtreeHeight) × (IndexGroup → Finset FtsLeaf)

def SmallRectangle (rectangle : DigestRectangle) : Prop := ∀ tree, (rectangle.2 tree).card ≤ 256

def InRectangle (parameter : PublicParameter) (rectangle : DigestRectangle) (digest : MessageDigest) : Prop :=
  Landed parameter (digestIndex digest) ∧ FixedKeptCovered rectangle.1 rectangle.2 (localDigestView digest)

theorem digestRectangle_card_le : Fintype.card DigestRectangle ≤ 2 ^ 24602 := by
  have hindex : Fintype.card IndexGroup = 24 := by decide
  have hleaf : Fintype.card FtsLeaf = 1024 := by decide
  simp only [DigestRectangle, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_finset, hindex, hleaf]
  have hb : subtreeHeight ≤ 26 := Params.subtreeHeight_le
  calc
    _ = 2 ^ (subtreeHeight + 24576) := by rw [← pow_mul, ← pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

theorem probEvent_inRectangle_le (parameter : PublicParameter) (rectangle : DigestRectangle)
    (hsmall : SmallRectangle rectangle) :
    Pr[InRectangle parameter rectangle | ($ᵗ MessageDigest : ProbComp _)] ≤ (1 : ℝ≥0∞) / 2 ^ 74 :=
  probEvent_landed_fixedKeptCovered_le parameter rectangle.1 rectangle.2 hsmall

omit [Params] in
/-- Numerical Chernoff certificate using the already checked base-eight adaptive moment.
The large fixed threshold avoids ceilings and still leaves ample security-budget margin. -/
theorem rectangle_exponential_bound (queries : Nat) (hqueries : queries ≤ 2 ^ 127) :
    (1 + 7 * ((1 : ℝ) / 2 ^ 74)) ^ queries / 8 ^ (2 ^ 56) ≤ 1 / 2 ^ 25002 := by
  let rate : ℝ := 1 / 2 ^ 74
  change (1 + 7 * rate) ^ queries / 8 ^ (2 ^ 56) ≤ 1 / 2 ^ 25002
  have hq : (queries : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hqueries
  have hmean : (queries : ℝ) * (7 * rate) ≤ (7 * 2 ^ 53 : Nat) := by
    have hm := mul_le_mul_of_nonneg_right hq (by positivity : (0 : ℝ) ≤ 7 * rate)
    calc
      _ ≤ (2 : ℝ) ^ 127 * (7 * rate) := hm
      _ = ((7 * 2 ^ 53 : Nat) : ℝ) := by norm_num [rate]
  have hbase : 1 + 7 * rate ≤ Real.exp (7 * rate) := by
    simpa only [add_comm] using Real.add_one_le_exp (7 * rate)
  have hexp : (1 + 7 * rate) ^ queries ≤ Real.exp (7 * 2 ^ 53 : Nat) := by
    calc
      _ ≤ Real.exp (7 * rate) ^ queries := pow_le_pow_left₀ (by positivity) hbase _
      _ = Real.exp ((queries : ℝ) * (7 * rate)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hmean
  have hfour : Real.exp (7 * 2 ^ 53 : Nat) ≤ (4 : ℝ) ^ (7 * 2 ^ 53) := by
    calc
      _ = Real.exp 1 ^ (7 * 2 ^ 53) := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_one_lt_three.le.trans (by norm_num)) _
  refine (div_le_div_of_nonneg_right (hexp.trans hfour) (by positivity)).trans ?_
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 ^ (2 ^ 56))).2
  rw [one_div_mul_eq_div]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 25002)).2
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, show (8 : ℝ) = 2 ^ 3 by norm_num,
    ← pow_mul, ← pow_mul, ← pow_add]
  apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
  norm_num

omit [Params] in
/-- Applicable to the actual per-hash-query monitor once a new pair's latent full digest
is sampled uniformly. Repeated pairs and other hash domains can contribute zero. -/
theorem adaptive_rectangle_tail {State : Type} (step : Nat → State → ProbComp (Bool × State))
    (hstep : ∀ n state, Pr[fun next => next.1 | step n state] ≤ (1 : ℝ≥0∞) / 2 ^ 74)
    (queries : Nat) (hqueries : queries ≤ 2 ^ 127) (state : State) :
    Pr[fun count => 2 ^ 56 ≤ count | adaptiveHitCount step queries state] ≤
      (1 : ℝ≥0∞) / 2 ^ 25002 := by
  have h := adaptiveHitCount_tail step ((1 : ℝ≥0∞) / 2 ^ 74) hstep queries (2 ^ 56) state
  have hdiv : Pr[fun count => 2 ^ 56 ≤ count | adaptiveHitCount step queries state] ≤
      (1 + 7 * ((1 : ℝ≥0∞) / 2 ^ 74)) ^ queries / 8 ^ (2 ^ 56) := by
    exact (ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by finiteness))).mpr h
  have hreal := ENNReal.ofReal_le_ofReal (rectangle_exponential_bound queries hqueries)
  simp only [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 8 ^ (2 ^ 56)),
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ 25002),
    ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 1 + 7 * (1 / 2 ^ 74)),
    ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ 7 * (1 / 2 ^ 74)),
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 7),
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ 74),
    ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 8),
    ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ 2), ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at hreal
  exact hdiv.trans hreal

/-- One common trace is localized simultaneously for every possible disclosure rectangle.
No independence between rectangles, and no advance choice of the history, is required. -/
theorem rectangle_union_bound {α : Type} (program : ProbComp α) (count : α → DigestRectangle → Nat)
    (htail : ∀ rectangle, SmallRectangle rectangle →
      Pr[fun result => 2 ^ 56 ≤ count result rectangle | program] ≤ (1 : ℝ≥0∞) / 2 ^ 25002) :
    Pr[fun result => ∃ rectangle, SmallRectangle rectangle ∧ 2 ^ 56 ≤ count result rectangle | program] ≤
      (1 : ℝ≥0∞) / 2 ^ 400 := by
  have h := probEvent_exists_finset_le_sum Finset.univ program
    (fun rectangle result => SmallRectangle rectangle ∧ 2 ^ 56 ≤ count result rectangle)
  simp only [Finset.mem_univ, true_and] at h
  refine h.trans ((Finset.sum_le_sum (g := fun _ : DigestRectangle => (1 : ℝ≥0∞) / 2 ^ 25002)
    (fun rectangle _ => ?_)).trans ?_)
  · by_cases hsmall : SmallRectangle rectangle
    · simpa only [hsmall, true_and] using htail rectangle hsmall
    · simp only [hsmall, false_and, probEvent_False]; exact bot_le
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      _ ≤ ((2 ^ 24602 : Nat) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ 25002) := by
        gcongr
        exact_mod_cast digestRectangle_card_le
      _ = _ := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        have hpow : (2 : ℝ≥0∞) ^ 25002 = 2 ^ 24602 * 2 ^ 400 := by rw [← pow_add]
        rw [hpow, one_div, ENNReal.mul_inv (Or.inr (by finiteness)) (Or.inr (by finiteness)),
          ← mul_assoc, ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_mul]
        exact one_div _ |>.symm

noncomputable def rectangleBankCount (parameter : PublicParameter) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) (rectangle : DigestRectangle) : Nat :=
  (bank.filter (fun candidate => InRectangle parameter rectangle (digest candidate))).card

def RectangleBankSparse (parameter : PublicParameter) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) : Prop :=
  ∀ rectangle, SmallRectangle rectangle → rectangleBankCount parameter bank digest rectangle < 2 ^ 56

/-- The selected source is excluded from its own target bank, including if that pair was
queried before it was signed. The gain only counts the other candidate digests. -/
noncomputable def localizedBankGain (parameter : PublicParameter) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) (source : DigestCandidate)
    (sourceView : KeptDigestView) (views : Finset KeptDigestView) : Nat :=
  (bank.filter (fun target => target ≠ source ∧ Landed parameter (digestIndex (digest target)) ∧
    ViewCap 255 views ∧ CoverageGain (localDigestView (digest target)) sourceView views)).card

/-- The simultaneous rectangle event supplies a pointwise cap, including fully cached
targets and arbitrarily chosen actual or hypothetical signing histories. -/
theorem localizedBankGain_le (parameter : PublicParameter) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) (hsparse : RectangleBankSparse parameter bank digest)
    (source : DigestCandidate) (sourceView : KeptDigestView) (views : Finset KeptDigestView) :
    localizedBankGain parameter bank digest source sourceView views ≤ 2 ^ 56 := by
  by_cases hcap : ViewCap 255 views
  · let rectangle : DigestRectangle := (sourceView.1, viewCoordinates (insert sourceView views) sourceView.1)
    have hsmall : SmallRectangle rectangle :=
      fun tree => viewCoordinates_card_le (viewCap_insert hcap sourceView) sourceView.1 tree
    refine (Finset.card_le_card ?_).trans (hsparse rectangle hsmall).le
    intro target htarget
    obtain ⟨hmem, hne, hland, _, hgain⟩ := Finset.mem_filter.mp htarget
    exact Finset.mem_filter.mpr ⟨hmem, hland, coverageGain_fixedKeptCovered _ sourceView views hgain⟩
  · simp only [localizedBankGain, hcap, false_and, and_false, Finset.filter_false, Finset.card_empty]
    exact Nat.zero_le _

/-- This is the valid self-bounding inequality: the factor is the simultaneous rectangle
count cap, not the fresh-target measure `2^-74`. It is pointwise before any expectation. -/
theorem localizedBankGain_square_le (parameter : PublicParameter) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) (hsparse : RectangleBankSparse parameter bank digest)
    (source : DigestCandidate) (sourceView : KeptDigestView) (views : Finset KeptDigestView) :
    (localizedBankGain parameter bank digest source sourceView views : ℝ≥0∞) ^ 2 ≤
      (2 : ℝ≥0∞) ^ 56 * localizedBankGain parameter bank digest source sourceView views := by
  rw [pow_two]
  apply mul_le_mul' _ le_rfl
  exact_mod_cast localizedBankGain_le parameter bank digest hsparse source sourceView views

/-- Average over one shared independent future pool. Since the preceding inequality is
pointwise for every pool, the cap survives arbitrary changes of the preceding real history. -/
theorem expected_futureBankGain_square_le (parameter : PublicParameter) (bank : Finset DigestCandidate)
    (digest : DigestCandidate → MessageDigest) (hsparse : RectangleBankSparse parameter bank digest)
    (source : DigestCandidate) (sourceView : KeptDigestView) (n : Nat) (prior : Finset KeptDigestView) :
    (∑' views, Pr[= views | uniformDisclosureSet n prior] *
      (localizedBankGain parameter bank digest source sourceView views : ℝ≥0∞) ^ 2) ≤
      (2 : ℝ≥0∞) ^ 56 * ∑' views, Pr[= views | uniformDisclosureSet n prior] *
        localizedBankGain parameter bank digest source sourceView views := by
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro views
  simpa only [mul_left_comm] using mul_le_mul' (le_rfl :
    Pr[= views | uniformDisclosureSet n prior] ≤ Pr[= views | uniformDisclosureSet n prior])
      (localizedBankGain_square_le parameter bank digest hsparse source sourceView views)

end LeanSphincs.Lifetime
