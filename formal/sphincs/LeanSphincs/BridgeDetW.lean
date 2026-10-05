import LeanSphincs.H0SplitCert
import LeanSphincs.BridgeSatWRoutes
import LeanSphincs.BridgeFleafSmall

/-! Split-bound covers at the survival-weighted baseline `baselineW` (thresholds `betaWQ`): a
successful cover check bounds the large-route term at every budget it covers. -/

open ENNReal NNReal

namespace LeanSphincs.Security.H0

open Concrete Domination ForsPrice

section Fors

variable [Params]

/-- The one-coin excess forecast at the weighted baseline. -/
noncomputable def hOfOW (q : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtualOnce Finset.univ (wbarOf q)
    (ForsPotential.excess (HiddenDebt.baselineW q)) signatureLimit I 0) q []

/-- The check of one entry. -/
def checkEntrySW (b N : ℕ) (opts : List OptS) (e : EntryS) : Bool :=
  match opts[e.2.2]? with
  | none => false
  | some o =>
      decide (2 * e.2.1 ≤ 2 ^ 128) && decide (o.cthr ≤ ForsPotential.betaWQ e.2.1) &&
        decide ((e.2.1 : ℚ) * o.B + ((e.2.1 : ℚ) + kCredit b + N) / 2 ^ 200 ≤
          ((e.1 : ℚ) / 2 ^ 128) ^ 2 + (kCredit b : ℚ) / 2 ^ 127)

/-- Consecutive entries cover `[last, 2^127]`. -/
def chainSW (b N : ℕ) (opts : List OptS) : ℕ → List EntryS → Bool
  | last, [] => decide (2 ^ 127 < last)
  | last, e :: rest => decide (e.1 ≤ last) && checkEntrySW b N opts e && chainSW b N opts (e.2.1 + 1) rest

/-- A cover of every budget `qstart ≤ q ≤ 2^127`. -/
def checkCoverSW (b N qstart : ℕ) (c : CoverS) : Bool :=
  checkTable b N c.tab && c.opts.all (checkOpt b c.tab) && chainSW b N c.opts qstart c.entries

omit [Params] in
theorem chainSW_sound (b N : ℕ) (opts : List OptS) : ∀ (cover : List EntryS) (last : ℕ),
    chainSW b N opts last cover = true →
      ∀ q, last ≤ q → q ≤ 2 ^ 127 → ∃ e ∈ cover, e.1 ≤ q ∧ q ≤ e.2.1 ∧ checkEntrySW b N opts e = true
  | [], last, h, q, hq, hq' => by
      simp only [chainSW, decide_eq_true_eq] at h
      omega
  | e :: rest, last, h, q, hq, hq' => by
      simp only [chainSW, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨he1, he2⟩, hrest⟩ := h
      by_cases hle : q ≤ e.2.1
      · exact ⟨e, List.mem_cons_self .., by omega, hle, he2⟩
      · obtain ⟨e', he', h1, h2, h3⟩ := chainSW_sound b N opts rest _ hrest q (by omega) hq'
        exact ⟨e', List.mem_cons_of_mem _ he', h1, h2, h3⟩

omit [Params] in
theorem checkEntrySW_sound {b N : ℕ} {opts : List OptS} {e : EntryS} (h : checkEntrySW b N opts e = true) :
    ∃ o ∈ opts, 2 * e.2.1 ≤ 2 ^ 128 ∧ o.cthr ≤ ForsPotential.betaWQ e.2.1 ∧
      (e.2.1 : ℚ) * o.B + ((e.2.1 : ℚ) + kCredit b + N) / 2 ^ 200 ≤
        ((e.1 : ℚ) / 2 ^ 128) ^ 2 + (kCredit b : ℚ) / 2 ^ 127 := by
  unfold checkEntrySW at h
  rcases hget : opts[e.2.2]? with _ | o
  · rw [hget] at h; exact absurd h (by simp)
  · rw [hget] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨o, List.mem_of_getElem? hget, h.1.1, h.1.2, h.2⟩

/-- The bound for one checked entry. -/
theorem bound_of_entrySW (b N : ℕ) (t : PoisTable) (opts : List OptS) (ht : checkTable b N t = true)
    (hopts : ∀ o ∈ opts, checkOpt b t o = true) (hb : subtreeHeight = b) (hN : signatureLimit = N)
    (e : EntryS) (he : checkEntrySW b N opts e = true) (q : ℕ) (hqa : e.1 ≤ q) (hqb : q ≤ e.2.1) :
    (1 - HiddenDebt.budget 0 q) + (q : ℝ≥0∞) * hOfOW q +
        ((q + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) : ℕ) : ℝ≥0∞) / 2 ^ 127 := by
  obtain ⟨o, ho, hqb2, hcthr, hmain⟩ := checkEntrySW_sound he
  obtain ⟨qa, qb, j⟩ := e
  dsimp only at hqa hqb hqb2 hcthr hmain
  have hoc := hopts o ho
  have hq127 : q ≤ 2 ^ 127 := by
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    omega
  have hq2 : 2 * q ≤ 2 ^ 128 := by omega
  have hB0 : (0 : ℝ) ≤ (o.B : ℝ) := by exact_mod_cast opt_B_nonneg ht hoc
  -- the H-term at the baseline
  have hβc : ENNReal.ofReal (o.cthr : ℝ) ≤ HiddenDebt.baselineW q :=
    le_trans (ENNReal.ofReal_le_ofReal (by exact_mod_cast hcthr)) (ForsPotential.baselineW_ge q qb hqb)
  have hH : hOfOW q ≤ ENNReal.ofReal (o.B : ℝ) := by
    have h := hTermO_fors_le_opt b N t o ht hoc hb hN q hq2 (HiddenDebt.baselineW q) (HiddenDebt.baselineW_ne_top q)
      hβc
    unfold hOfOW
    rw [excess_eq]
    exact h
  -- the real inequality
  have hmainR : (qb : ℝ) * (o.B : ℝ) * ((1 / 2 : ℝ) / (1 - 1 / 2)) + ((qb : ℝ) + (kCredit b : ℝ) + N) / 2 ^ 200 ≤
      ((qa : ℝ) / 2 ^ 128) ^ 2 + (kCredit b : ℝ) / 2 ^ 127 := by
    have := (Rat.cast_le (K := ℝ)).mpr hmain
    push_cast at this
    norm_num
    linarith
  have hfinal := final_real (q : ℝ) (qa : ℝ) (qb : ℝ) (kCredit b : ℝ) (N : ℝ) (o.B : ℝ) (1 / 2) 1
    (by exact_mod_cast hqa) (by exact_mod_cast hqb) (Nat.cast_nonneg _) hB0 (by norm_num) (by norm_num)
    (by norm_num) hmainR
  rw [mul_one] at hfinal
  -- back to ENNReal
  rw [hb, hN, show 258 * 2 ^ b + 2 * (26 - b) = kCredit b from rfl]
  have hbud : 1 - HiddenDebt.budget 0 q =
      ENNReal.ofReal (1 - (((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0)) ^ 2) := by
    unfold HiddenDebt.budget HiddenDebt.spaceReal
    rw [Nat.cast_zero, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (sq_nonneg _)]
  have hslackE : ((q + kCredit b + N : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200 =
      ENNReal.ofReal (((q : ℝ) + kCredit b + N) / 2 ^ 200) := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (by positivity), ← inv_pow, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    congr 1
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  have hrhs : ((q + kCredit b : ℕ) : ℝ≥0∞) / 2 ^ 127 = ENNReal.ofReal (((q : ℝ) + kCredit b) / 2 ^ 127) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
    congr 1
    rw [← ENNReal.ofReal_natCast]
    push_cast
    rfl
  have hqE : (q : ℝ≥0∞) * ENNReal.ofReal (o.B : ℝ) = ENNReal.ofReal ((q : ℝ) * (o.B : ℝ)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hbud0 : 0 ≤ 1 - (((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0)) ^ 2 := by
    have hq' : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hq127
    have h0 : 0 ≤ ((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0) := by
      apply div_nonneg <;> linarith [show (2 : ℝ) ^ 128 = 2 * 2 ^ 127 by norm_num, show (0 : ℝ) ≤ q from Nat.cast_nonneg _]
    have h1 : ((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0) ≤ 1 := by
      rw [div_le_one (by norm_num)]; linarith [show (0 : ℝ) ≤ q from Nat.cast_nonneg _]
    nlinarith
  calc 1 - HiddenDebt.budget 0 q + (q : ℝ≥0∞) * hOfOW q + ((q + kCredit b + N : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200
      ≤ ENNReal.ofReal (1 - (((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0)) ^ 2) +
          ENNReal.ofReal ((q : ℝ) * (o.B : ℝ)) +
          ENNReal.ofReal (((q : ℝ) + kCredit b + N) / 2 ^ 200) := by
        rw [hbud, hslackE, ← hqE]
        gcongr
    _ = ENNReal.ofReal ((1 - (((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0)) ^ 2) +
          (q : ℝ) * (o.B : ℝ) + ((q : ℝ) + kCredit b + N) / 2 ^ 200) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add hbud0 (by positivity)]
    _ ≤ ENNReal.ofReal (((q : ℝ) + kCredit b) / 2 ^ 127) := ENNReal.ofReal_le_ofReal hfinal
    _ = _ := hrhs.symm

/-- **The one-coin H-term bound at the weighted baseline from a split-bound certificate**, for every budget
`qstart ≤ q' ≤ 2^127`. -/
theorem h0SW_bound_of_cover (b N qstart : ℕ) (cover : CoverS) (hcov : checkCoverSW b N qstart cover = true)
    (hb : subtreeHeight = b) (hN : signatureLimit = N) (q' : ℕ) (hq0 : qstart ≤ q') (hq : 2 * q' ≤ 2 ^ 128) :
    (1 - HiddenDebt.budget 0 q') + (q' : ℝ≥0∞) * hOfOW q' +
        ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) : ℕ) : ℝ≥0∞) / 2 ^ 127 := by
  have hq127 : q' ≤ 2 ^ 127 := by
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    omega
  simp only [checkCoverSW, Bool.and_eq_true, List.all_eq_true] at hcov
  obtain ⟨⟨ht, hopts⟩, hchain⟩ := hcov
  obtain ⟨e, -, h1, h2, h3⟩ := chainSW_sound b N cover.opts cover.entries qstart hchain q' hq0 hq127
  exact bound_of_entrySW b N cover.tab cover.opts ht hopts hb hN e h3 q' h1 h2

end Fors

end LeanSphincs.Security.H0
