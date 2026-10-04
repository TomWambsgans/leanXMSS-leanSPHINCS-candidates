import LeanSphincs.H0Bound
import LeanSphincs.H0Once

/-! The one-coin H-term at budget `q`: the bound
`(1 - budget 0 q) + q H_0(q) + (q + K + N) 2^-200 ≤ (q + K) / 2^127` for every budget covered by a
successful rational certificate entry, where the Poisson rate is that of the signatures plus one
coin per future pair (no inflation of the signature loads by the cached share). -/

open ENNReal

namespace LeanSphincs.Security.H0

open Concrete Domination ForsPrice

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 512

/-! ### The rational check -/

/-- Upper bound for the one-coin Poisson rate at the right end `qb` of an interval. -/
def muOnceQ (b N qb R : ℕ) : ℚ :=
  (N : ℚ) / 2 ^ b +
    ((qb : ℚ) / ((2 : ℚ) ^ 128 - qb - 2 ^ 32)) * (1 + 2 ^ 26 / ((2 : ℚ) ^ 128 - qb - 2 ^ 32)) ^ (24 * R) / 2 ^ b

/-- The check of one entry. -/
def checkIO (b N : ℕ) (c : Entry) : Bool :=
  decide (1 ≤ N) && decide (1 ≤ c.2.2.1) && decide (2 * c.2.1 ≤ 2 ^ 128) &&
    decide (muOnceQ b N c.2.1 c.2.2.1 ≤ (c.2.2.2.2 : ℚ) / 2 ^ 64) &&
    (decide (c.2.2.1 = 1) || decide (0 < betaQ c.2.1)) &&
    decide ((2 : ℚ) ^ b * (PQ c.2.2.1 c.2.2.2.1 ((c.2.2.2.2 : ℚ) / 2 ^ 64) - 1) < 1) &&
    decide (mainQ b N c.1 c.2.1 c.2.2.1 c.2.2.2.1 (PQ c.2.2.1 c.2.2.2.1 ((c.2.2.2.2 : ℚ) / 2 ^ 64)))

/-- Consecutive entries cover `[last, 2^127]`. -/
def chainO (b N : ℕ) : ℕ → List Entry → Bool
  | last, [] => decide (2 ^ 127 < last)
  | last, c :: rest => decide (c.1 ≤ last) && checkIO b N c && chainO b N (c.2.1 + 1) rest

/-- A cover of every budget `0 ≤ q ≤ 2^127`. -/
def checkCoverO (b N : ℕ) (cover : List Entry) : Bool := chainO b N 0 cover

theorem chainO_sound (b N : ℕ) : ∀ (cover : List Entry) (last : ℕ), chainO b N last cover = true →
    ∀ q, last ≤ q → q ≤ 2 ^ 127 → ∃ c ∈ cover, c.1 ≤ q ∧ q ≤ c.2.1 ∧ checkIO b N c = true
  | [], last, h, q, hq, hq' => by
      simp only [chainO, decide_eq_true_eq] at h
      omega
  | c :: rest, last, h, q, hq, hq' => by
      simp only [chainO, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hc1, hc2⟩, hrest⟩ := h
      by_cases hle : q ≤ c.2.1
      · exact ⟨c, List.mem_cons_self .., by omega, hle, hc2⟩
      · obtain ⟨c', hc', h1, h2, h3⟩ := chainO_sound b N rest _ hrest q (by omega) hq'
        exact ⟨c', List.mem_cons_of_mem _ hc', h1, h2, h3⟩

theorem checkCoverO_sound (b N : ℕ) (cover : List Entry) (h : checkCoverO b N cover = true) (q : ℕ)
    (hq : q ≤ 2 ^ 127) : ∃ c ∈ cover, c.1 ≤ q ∧ q ≤ c.2.1 ∧ checkIO b N c = true :=
  chainO_sound b N cover 0 h q (Nat.zero_le _) hq

variable [Params]

/-- The one-coin H-term at budget `q`. -/
noncomputable def hOfO (q : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtualOnce Finset.univ (wbarOf q)
    (ForsPotential.excess (HiddenDebt.baseline q)) signatureLimit I 0) q []

/-- The one-coin Poisson rate, in real form, is below the certificate bound. -/
theorem mu_leO (b N R q qb : ℕ) (hb : subtreeHeight = b) (hq : q ≤ qb) (hqb : 2 * qb ≤ 2 ^ 128) (μh : ℝ)
    (hμ : (muOnceQ b N qb R : ℝ) ≤ μh) :
    (N : ℝ≥0∞) * ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞)⁻¹ +
      (q : ℝ≥0∞) * (landing * wbarOf q *
        (1 + wbarOf q * ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞)) ^ (24 * R) /
          ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞)) ≤ ENNReal.ofReal μh := by
  have hqb127 : qb ≤ 2 ^ 127 := by
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    omega
  have hq127 : q ≤ 2 ^ 127 := le_trans hq hqb127
  have hDq := dReal_pos q hq127
  have hDb := dReal_pos qb hqb127
  rw [wbar_eq q hq127, landing_eq, card_eq, ← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_natCast q,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_inv_of_pos (by positivity)]
  simp (disch := positivity) only [← ENNReal.ofReal_mul, ← ENNReal.ofReal_add, ← ENNReal.ofReal_pow,
    ← ENNReal.ofReal_div_of_pos]
  apply ENNReal.ofReal_le_ofReal
  refine le_trans ?_ hμ
  rw [hb]
  have hb26 : b ≤ 26 := hb ▸ subtree_le_26
  have hM : (2 : ℝ) ^ (26 - b) * 2 ^ b = 2 ^ 26 := by rw [← pow_add, Nat.sub_add_cancel hb26]
  have hML : (2 : ℝ) ^ (26 - b) / ((2 : ℝ) ^ 128 - q - 2 ^ 32) * 2 ^ b = 2 ^ 26 / ((2 : ℝ) ^ 128 - q - 2 ^ 32) := by
    rw [div_mul_eq_mul_div, hM]
  rw [hML]
  have hform : (N : ℝ) * (2 ^ b)⁻¹ +
      q * (1 / 2 ^ (26 - b) * (2 ^ (26 - b) / ((2 : ℝ) ^ 128 - q - 2 ^ 32)) *
        (1 + 2 ^ 26 / ((2 : ℝ) ^ 128 - q - 2 ^ 32)) ^ (24 * R) / 2 ^ b) =
      (N : ℝ) / 2 ^ b + ((q : ℝ) / ((2 : ℝ) ^ 128 - q - 2 ^ 32)) *
        (1 + 2 ^ 26 / ((2 : ℝ) ^ 128 - q - 2 ^ 32)) ^ (24 * R) / 2 ^ b := by
    field_simp
  rw [hform]
  unfold muOnceQ
  push_cast
  have hqq : (q : ℝ) ≤ qb := by exact_mod_cast hq
  have hDle : (2 : ℝ) ^ 128 - qb - 2 ^ 32 ≤ 2 ^ 128 - q - 2 ^ 32 := by linarith
  have h1 : (2 : ℝ) ^ 26 / ((2 : ℝ) ^ 128 - q - 2 ^ 32) ≤ 2 ^ 26 / ((2 : ℝ) ^ 128 - qb - 2 ^ 32) :=
    div_le_div_of_nonneg_left (by positivity) hDb hDle
  have h2 : (q : ℝ) / ((2 : ℝ) ^ 128 - q - 2 ^ 32) ≤ (qb : ℝ) / ((2 : ℝ) ^ 128 - qb - 2 ^ 32) := by
    rw [div_le_div_iff₀ hDq hDb]
    nlinarith
  gcongr

/-! ### The bound for one certificate entry -/

theorem bound_of_entryO (b N : ℕ) (hb : subtreeHeight = b) (hN : signatureLimit = N) (c : Entry)
    (hc : checkIO b N c = true) (q : ℕ) (hqa : c.1 ≤ q) (hqb : q ≤ c.2.1) :
    (1 - HiddenDebt.budget 0 q) + (q : ℝ≥0∞) * hOfO q +
        ((q + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) : ℕ) : ℝ≥0∞) / 2 ^ 127 := by
  obtain ⟨qa, qb, R, e, m⟩ := c
  simp only [checkIO, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨hN1, hR⟩, hqb2⟩, hmu⟩, hβpos⟩, hLe⟩, hmain⟩ := hc
  dsimp only at hqa hqb hR hqb2 hmu hβpos hLe hmain
  have hq127 : q ≤ 2 ^ 127 := by
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    omega
  -- real data of the certificate
  set μr : ℝ := (m : ℝ) / 2 ^ 64 with hμr
  have hμr0 : 0 ≤ μr := by positivity
  set Pr : ℝ := pReal R e μr with hPr
  set βr : ℝ := ((betaQ qb : ℚ) : ℝ) with hβr
  set Ar : ℝ := aReal R e βr with hAr
  have hP1 : 1 ≤ Pr := one_le_pReal R e μr hμr0
  have hpos' : R = 1 ∨ 0 < βr := by
    rcases hβpos with h | h
    · exact Or.inl h
    · right; rw [hβr]; exact_mod_cast h
  have hAr0 : 0 ≤ Ar := aReal_nonneg R e βr hpos'
  have hmuR : (muOnceQ b N qb R : ℝ) ≤ μr := by
    have := (Rat.cast_le (K := ℝ)).mpr hmu
    push_cast at this
    exact this
  have hLeR : (2 : ℝ) ^ b * (Pr - 1) < 1 := by
    have := (Rat.cast_lt (K := ℝ)).mpr hLe
    push_cast [pReal_eq] at this
    exact this
  have hmainR : (qb : ℝ) * Ar * ((2 : ℝ) ^ b * (Pr - 1) / (1 - (2 : ℝ) ^ b * (Pr - 1))) +
      ((qb : ℝ) + (kCredit b : ℝ) + N) / 2 ^ 200 ≤ ((qa : ℝ) / 2 ^ 128) ^ 2 + (kCredit b : ℝ) / 2 ^ 127 := by
    unfold mainQ at hmain
    have := (Rat.cast_le (K := ℝ)).mpr hmain
    push_cast [pReal_eq, aReal_eq] at this
    exact this
  -- the ENNReal objects of the domination
  set L : ℝ≥0∞ := ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞) with hLdef
  set w := wbarOf q with hwdef
  set β := HiddenDebt.baseline q with hβdef
  set t : ℝ≥0∞ := (2 : ℝ≥0∞) ^ e with htdef
  set α : ℝ≥0∞ := L⁻¹ with hαdef
  set γ : ℝ≥0∞ := landing * w * (1 + w * L) ^ (24 * R) / L with hγdef
  set A : ℝ≥0∞ := cMom R / (t ^ R * β ^ (R - 1)) with hAdef
  have hL0 : L ≠ 0 := by
    rw [hLdef]; exact_mod_cast Fintype.card_ne_zero
  have hLT : L ≠ ⊤ := ENNReal.natCast_ne_top _
  have hw1 : w ≤ 1 := (fair_of q (by omega)).le_one
  have hβge : ENNReal.ofReal βr ≤ β := baseline_ge q qb hqb hqb2
  have hβT : β ≠ ⊤ := baseline_ne_top q
  have hβ0 : R = 1 ∨ β ≠ 0 := by
    rcases hpos' with h | h
    · exact Or.inl h
    · exact Or.inr (lt_of_lt_of_le (ENNReal.ofReal_pos.2 h) hβge).ne'
  have ht0 : t ≠ 0 := pow_ne_zero _ two_ne_zero
  have htT : t ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hLα : 1 ≤ L * α := by
    rw [hαdef, ENNReal.mul_inv_cancel hL0 hLT]
  have hγ : landing * w * (1 + w * L) ^ (24 * R) ≤ L * γ := by
    rw [hγdef, ENNReal.mul_div_cancel hL0 hLT]
  have hNs : 1 ≤ signatureLimit := by rw [hN]; exact hN1
  have hmainE := hTermO_excess_le (Prod.fst : View → Fin (2 ^ subtreeHeight)) (Finset.univ : Finset View)
    uniformIndex_univ Finset.univ_nonempty kappa β t
    kappa_ne_top R hR hβ0 hβT ht0 htT signatureLimit q hNs α w landing γ hw1 ForsPotential.landing_le_one hL0
    hLα hγ
  have hH : hOfO q = hTermO (Finset.univ : Finset View) w landing signatureLimit q
      (fun d => countPrice (Prod.fst : View → Fin (2 ^ subtreeHeight)) kappa d - β) := by
    unfold hOfO hTermO
    rw [excess_eq]
  -- the rate and the Poisson mean
  have hμ : (signatureLimit : ℝ≥0∞) * α + q * γ ≤ ENNReal.ofReal μr := by
    have h := mu_leO b N R q qb hb hqb hqb2 μr hmuR
    rw [hαdef, hγdef, hN]
    exact h
  set Pμ := ∑ s ∈ Finset.range (R + 1), (R.choose s : ℝ≥0∞) * (t * kappa) ^ s *
      touchard (24 * s) ((signatureLimit : ℝ≥0∞) * α + q * γ) with hPμ
  have hPle : Pμ ≤ ENNReal.ofReal Pr := by
    rw [hPr, ← psum_ofReal R e μr hμr0, hPμ]
    gcongr with s hs
    exact touchard_mono _ hμ
  have hA : A ≤ ENNReal.ofReal Ar := prefactor_le R e β βr hR hβge hpos'
  have hAT : A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA
  have hprod : ∏ _l : Fin (2 ^ subtreeHeight), Pμ = Pμ ^ (2 ^ b) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hb]
  have hH0 : hOfO q ≤ ENNReal.ofReal (Ar * (Pr ^ (2 ^ b) - 1)) := by
    have h1 : hOfO q + A ≤ A * Pμ ^ (2 ^ b) := by
      rw [hH, ← hprod]
      exact hmainE
    have h2 : hOfO q ≤ A * Pμ ^ (2 ^ b) - A := ENNReal.le_sub_of_add_le_right hAT h1
    have h3 : A * Pμ ^ (2 ^ b) - A = A * (Pμ ^ (2 ^ b) - 1) := by
      rw [ENNReal.mul_sub (fun _ _ => hAT), mul_one]
    calc hOfO q ≤ A * (Pμ ^ (2 ^ b) - 1) := h3 ▸ h2
      _ ≤ ENNReal.ofReal Ar * (ENNReal.ofReal Pr ^ (2 ^ b) - 1) := by
          gcongr
      _ = ENNReal.ofReal (Ar * (Pr ^ (2 ^ b) - 1)) := by
          rw [← ENNReal.ofReal_pow (show (0 : ℝ) ≤ Pr by linarith), ← ENNReal.ofReal_one,
            ← ENNReal.ofReal_sub _ zero_le_one, ← ENNReal.ofReal_mul hAr0]
  -- the real inequality
  have hY : Pr ^ (2 ^ b) - 1 ≤ (2 : ℝ) ^ b * (Pr - 1) / (1 - (2 : ℝ) ^ b * (Pr - 1)) := by
    have h := pow_sub_one_le (Pr - 1) (2 ^ b) (by linarith) (by push_cast; exact hLeR)
    rw [show 1 + (Pr - 1) = Pr by ring] at h
    push_cast at h
    exact h
  have hfinal := final_real (q : ℝ) (qa : ℝ) (qb : ℝ) (kCredit b : ℝ) (N : ℝ) Ar ((2 : ℝ) ^ b * (Pr - 1))
    (Pr ^ (2 ^ b) - 1) (by exact_mod_cast hqa) (by exact_mod_cast hqb) (Nat.cast_nonneg _) hAr0
    (mul_nonneg (by positivity) (by linarith)) hLeR hY hmainR
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
  have hqE : (q : ℝ≥0∞) * ENNReal.ofReal (Ar * (Pr ^ (2 ^ b) - 1)) =
      ENNReal.ofReal ((q : ℝ) * (Ar * (Pr ^ (2 ^ b) - 1))) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hY0 : 0 ≤ Ar * (Pr ^ (2 ^ b) - 1) := mul_nonneg hAr0 (by
    have : 1 ≤ Pr ^ (2 ^ b) := one_le_pow₀ hP1
    linarith)
  have hbud0 : 0 ≤ 1 - (((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0)) ^ 2 := by
    have hq' : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hq127
    have h0 : 0 ≤ ((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0) := by
      apply div_nonneg <;> linarith [show (2 : ℝ) ^ 128 = 2 * 2 ^ 127 by norm_num, show (0 : ℝ) ≤ q from Nat.cast_nonneg _]
    have h1 : ((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0) ≤ 1 := by
      rw [div_le_one (by norm_num)]; linarith [show (0 : ℝ) ≤ q from Nat.cast_nonneg _]
    nlinarith
  calc 1 - HiddenDebt.budget 0 q + (q : ℝ≥0∞) * hOfO q + ((q + kCredit b + N : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200
      ≤ ENNReal.ofReal (1 - (((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0)) ^ 2) +
          ENNReal.ofReal ((q : ℝ) * (Ar * (Pr ^ (2 ^ b) - 1))) +
          ENNReal.ofReal (((q : ℝ) + kCredit b + N) / 2 ^ 200) := by
        rw [hbud, hslackE, ← hqE]
        gcongr
    _ = ENNReal.ofReal ((1 - (((2 : ℝ) ^ 128 - 0 - q) / ((2 : ℝ) ^ 128 - 0)) ^ 2) +
          (q : ℝ) * (Ar * (Pr ^ (2 ^ b) - 1)) + ((q : ℝ) + kCredit b + N) / 2 ^ 200) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add hbud0 (by positivity)]
    _ ≤ ENNReal.ofReal (((q : ℝ) + kCredit b) / 2 ^ 127) := ENNReal.ofReal_le_ofReal hfinal
    _ = _ := hrhs.symm

/-- The one-coin H-term bound for every budget covered by a successful certificate. -/
theorem h0O_bound_of_cover (b N : ℕ) (cover : List Entry) (hcov : checkCoverO b N cover = true)
    (hb : subtreeHeight = b) (hN : signatureLimit = N) (q' : ℕ) (hq : 2 * q' ≤ 2 ^ 128) :
    (1 - HiddenDebt.budget 0 q') + (q' : ℝ≥0∞) * hOfO q' +
        ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q' + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) : ℕ) : ℝ≥0∞) / 2 ^ 127 := by
  have hq127 : q' ≤ 2 ^ 127 := by
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    omega
  obtain ⟨c, -, h1, h2, h3⟩ := checkCoverO_sound b N cover hcov q' hq127
  exact bound_of_entryO b N hb hN c h3 q' h1 h2

end LeanSphincs.Security.H0
