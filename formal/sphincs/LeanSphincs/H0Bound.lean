import LeanSphincs.H0Price
import LeanSphincs.H0Numeric

/-! The H-term of the lazy run: the fair-share hypotheses of the grinding signer, and the bound
`(1 - budget 0 q) + q H_0(q) + (q + K + N) 2^-200 ≤ (q + K) / 2^127` for every budget `q` covered
by a successful rational certificate entry. -/

open ENNReal

namespace LeanSphincs.Security.H0

open Concrete Domination ForsPrice

set_option linter.unusedSectionVars false
set_option exponentiation.threshold 512

variable [Params]

/-- Coin probability of the fair-share signer at budget `q` (with `Cmax = q + 2^32`). -/
noncomputable def wbarOf (q : ℕ) : ℝ≥0∞ := ((((2 ^ 128 - (q + 2 ^ 32) : ℕ) : ℝ≥0∞)) * landing)⁻¹

/-- The H-term at budget `q`. -/
noncomputable def hOf (q : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtual Finset.univ (wbarOf q)
    (ForsPotential.excess (HiddenDebt.baseline q)) signatureLimit I 0) q []

theorem subtree_le_26 : subtreeHeight ≤ 26 := (inferInstance : Params).subtreeHeight_le

theorem landing_eq : landing = ENNReal.ofReal (1 / 2 ^ (26 - subtreeHeight)) := by
  unfold landing
  rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  rw [← ENNReal.ofReal_natCast]
  congr 1
  push_cast
  rfl

theorem card_eq : ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞) = ENNReal.ofReal (2 ^ subtreeHeight) := by
  rw [Fintype.card_fin, ← ENNReal.ofReal_natCast]
  push_cast
  rfl

theorem dReal_pos (q : ℕ) (hq : q ≤ 2 ^ 127) : (0 : ℝ) < 2 ^ 128 - q - 2 ^ 32 := by
  have : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hq
  linarith [show (2 : ℝ) ^ 128 = 2 * 2 ^ 127 by norm_num, show (2 : ℝ) ^ 32 < 2 ^ 127 by norm_num]

theorem wbar_eq (q : ℕ) (hq : q ≤ 2 ^ 127) :
    wbarOf q = ENNReal.ofReal (2 ^ (26 - subtreeHeight) / ((2 : ℝ) ^ 128 - q - 2 ^ 32)) := by
  have hq' : q + 2 ^ 32 ≤ 2 ^ 128 := by
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    have : (2 : ℕ) ^ 32 ≤ 2 ^ 127 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  have hD : (((2 ^ 128 - (q + 2 ^ 32) : ℕ) : ℝ≥0∞)) = ENNReal.ofReal ((2 : ℝ) ^ 128 - q - 2 ^ 32) := by
    rw [← ENNReal.ofReal_natCast]
    congr 1
    rw [Nat.cast_sub hq']
    push_cast
    ring
  have hpos := dReal_pos q hq
  unfold wbarOf
  rw [hD, landing_eq, ← ENNReal.ofReal_mul hpos.le, ← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  field_simp

/-! ### (a) The fair-share hypotheses -/

theorem fair_of (q : ℕ) (hq : 2 * q ≤ 2 ^ 128) : ForsPotential.Fair (wbarOf q) (q + 2 ^ 32) := by
  have hq127 : q ≤ 2 ^ 127 := by
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    omega
  have hpos := dReal_pos q hq127
  have hw := wbar_eq q hq127
  have hcmax : q + 2 ^ 32 ≤ 2 ^ 128 := by
    have : (2 : ℕ) ^ 32 ≤ 2 ^ 127 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    omega
  have hland0 : landing ≠ 0 := by
    rw [landing_eq]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hlandT : landing ≠ ⊤ := by rw [landing_eq]; exact ENNReal.ofReal_ne_top
  have hD0 : (((2 ^ 128 - (q + 2 ^ 32) : ℕ) : ℝ≥0∞)) ≠ 0 := by
    have : 0 < 2 ^ 128 - (q + 2 ^ 32) := by omega
    exact_mod_cast this.ne'
  have hDT : (((2 ^ 128 - (q + 2 ^ 32) : ℕ) : ℝ≥0∞)) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hprod0 : (((2 ^ 128 - (q + 2 ^ 32) : ℕ) : ℝ≥0∞)) * landing ≠ 0 := mul_ne_zero hD0 hland0
  have hprodT : (((2 ^ 128 - (q + 2 ^ 32) : ℕ) : ℝ≥0∞)) * landing ≠ ⊤ := ENNReal.mul_ne_top hDT hlandT
  refine ⟨?_, ?_, hcmax, ?_⟩
  · unfold wbarOf; exact ENNReal.inv_ne_top.2 hprod0
  · rw [hw, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_one hpos]
    have h1 : (2 : ℝ) ^ (26 - subtreeHeight) ≤ 2 ^ 26 := pow_le_pow_right₀ (by norm_num) (by omega)
    have : (q : ℝ) ≤ 2 ^ 127 := by exact_mod_cast hq127
    have h3 : (2 : ℝ) ^ 26 + 2 ^ 32 + 2 ^ 127 ≤ 2 ^ 128 := by norm_num
    linarith
  · unfold wbarOf
    generalize (((2 ^ 128 - (q + 2 ^ 32) : ℕ) : ℝ≥0∞)) = Dn at hprod0 hprodT ⊢
    generalize ((2 ^ 128 : ℕ) : ℝ≥0∞) = T
    generalize landing = lam at hprod0 hprodT ⊢
    rw [div_eq_mul_inv]
    have : (Dn * lam)⁻¹ * (Dn * T⁻¹) * lam = ((Dn * lam)⁻¹ * (Dn * lam)) * T⁻¹ := by ring
    rw [this, ENNReal.inv_mul_cancel hprod0 hprodT, one_mul]

/-! ### Real forms of the ingredients -/

/-- The Poisson rate of the domination, in real form, is below the certificate bound. -/
theorem mu_le (b N R q qb : ℕ) (hb : subtreeHeight = b) (hq : q ≤ qb) (hqb : 2 * qb ≤ 2 ^ 128) (μh : ℝ)
    (hμ : (muExactQ b N qb R : ℝ) ≤ μh) :
    (N : ℝ≥0∞) * ((1 + N * wbarOf q) * (1 + wbarOf q * ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞)) ^ (24 * R) /
        ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞)) +
      (q : ℝ≥0∞) * (landing * (N * wbarOf q) *
        (1 + wbarOf q * ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞)) ^ (24 * R) /
          ((Fintype.card (Fin (2 ^ subtreeHeight)) : ℕ) : ℝ≥0∞)) ≤ ENNReal.ofReal μh := by
  have hqb127 : qb ≤ 2 ^ 127 := by
    have : (2 : ℕ) ^ 128 = 2 * 2 ^ 127 := by norm_num
    omega
  have hq127 : q ≤ 2 ^ 127 := le_trans hq hqb127
  have hDq := dReal_pos q hq127
  have hDb := dReal_pos qb hqb127
  rw [wbar_eq q hq127, landing_eq, card_eq, ← ENNReal.ofReal_natCast N, ← ENNReal.ofReal_natCast q,
    ← ENNReal.ofReal_one]
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
  have hform : (N : ℝ) * ((1 + N * (2 ^ (26 - b) / ((2 : ℝ) ^ 128 - q - 2 ^ 32))) *
        (1 + 2 ^ 26 / ((2 : ℝ) ^ 128 - q - 2 ^ 32)) ^ (24 * R) / 2 ^ b) +
      q * (1 / 2 ^ (26 - b) * (N * (2 ^ (26 - b) / ((2 : ℝ) ^ 128 - q - 2 ^ 32))) *
        (1 + 2 ^ 26 / ((2 : ℝ) ^ 128 - q - 2 ^ 32)) ^ (24 * R) / 2 ^ b) =
      (N / 2 ^ b) * (1 + 2 ^ 26 / ((2 : ℝ) ^ 128 - q - 2 ^ 32)) ^ (24 * R) *
        (1 + (N * 2 ^ (26 - b) + q) / ((2 : ℝ) ^ 128 - q - 2 ^ 32)) := by
    field_simp
    ring
  rw [hform]
  unfold muExactQ
  push_cast
  have hqq : (q : ℝ) ≤ qb := by exact_mod_cast hq
  have hDle : (2 : ℝ) ^ 128 - qb - 2 ^ 32 ≤ 2 ^ 128 - q - 2 ^ 32 := by linarith
  have h1 : (2 : ℝ) ^ 26 / ((2 : ℝ) ^ 128 - q - 2 ^ 32) ≤ 2 ^ 26 / ((2 : ℝ) ^ 128 - qb - 2 ^ 32) :=
    div_le_div_of_nonneg_left (by positivity) hDb hDle
  have h2 : ((N : ℝ) * 2 ^ (26 - b) + q) / ((2 : ℝ) ^ 128 - q - 2 ^ 32) ≤
      ((N : ℝ) * 2 ^ (26 - b) + qb) / ((2 : ℝ) ^ 128 - qb - 2 ^ 32) := by
    rw [div_le_div_iff₀ hDq hDb]
    have : (0 : ℝ) ≤ N * 2 ^ (26 - b) := by positivity
    nlinarith
  gcongr

/-- Touchard sums commute with `ofReal`. -/
theorem touchard_ofReal (n : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    touchard n (ENNReal.ofReal r) =
      ENNReal.ofReal (∑ j ∈ Finset.range (n + 1), (Nat.stirlingSecond n j : ℝ) * r ^ j) := by
  unfold touchard
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow hr, ENNReal.ofReal_natCast]

theorem touchard_mono (n : ℕ) {μ μ' : ℝ≥0∞} (h : μ ≤ μ') : touchard n μ ≤ touchard n μ' := by
  unfold touchard
  gcongr

/-- The Poisson mean of the per-leaf factor, as a real number. -/
noncomputable def pReal (R e : ℕ) (r : ℝ) : ℝ :=
  ∑ s ∈ Finset.range (R + 1), (R.choose s : ℝ) * ((2 : ℝ) ^ e / 2 ^ 266) ^ s *
    ∑ j ∈ Finset.range (24 * s + 1), (Nat.stirlingSecond (24 * s) j : ℝ) * r ^ j

theorem pReal_eq (R e : ℕ) (μ : ℚ) : ((PQ R e μ : ℚ) : ℝ) = pReal R e (μ : ℝ) := by
  unfold PQ pReal
  simp only [touchQ_eq]
  push_cast
  rfl

theorem one_le_pReal (R e : ℕ) (r : ℝ) (hr : 0 ≤ r) : 1 ≤ pReal R e r := by
  unfold pReal
  have h := Finset.single_le_sum (s := Finset.range (R + 1))
    (f := fun s => (R.choose s : ℝ) * ((2 : ℝ) ^ e / 2 ^ 266) ^ s *
      ∑ j ∈ Finset.range (24 * s + 1), (Nat.stirlingSecond (24 * s) j : ℝ) * r ^ j)
    (fun s _ => by positivity) (Finset.mem_range.mpr (Nat.succ_pos R))
  simpa using h

theorem kappa_mul (e : ℕ) : (2 : ℝ≥0∞) ^ e * kappa = ENNReal.ofReal ((2 : ℝ) ^ e / 2 ^ 266) := by
  unfold kappa
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, div_eq_mul_inv]

theorem psum_ofReal (R e : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    ∑ s ∈ Finset.range (R + 1), (R.choose s : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ e * kappa) ^ s *
      touchard (24 * s) (ENNReal.ofReal r) = ENNReal.ofReal (pReal R e r) := by
  unfold pReal
  rw [ENNReal.ofReal_sum_of_nonneg (fun s _ => by positivity)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [kappa_mul, touchard_ofReal _ _ hr, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]

theorem baseline_ge (q qb : ℕ) (hq : q ≤ qb) (hqb : 2 * qb ≤ 2 ^ 128) :
    ENNReal.ofReal (betaQ qb : ℝ) ≤ HiddenDebt.baseline q := by
  unfold HiddenDebt.baseline HiddenDebt.spaceReal
  exact ENNReal.ofReal_le_ofReal (betaQ_le q qb hq hqb)

theorem baseline_ne_top (q : ℕ) : HiddenDebt.baseline q ≠ ⊤ := by
  unfold HiddenDebt.baseline; exact ENNReal.ofReal_ne_top

/-- The prefactor at the certificate's baseline bound, as a real number. -/
noncomputable def aReal (R e : ℕ) (β : ℝ) : ℝ :=
  ((R - 1 : ℕ) : ℝ) ^ (R - 1) / (R : ℝ) ^ R / (((2 : ℝ) ^ e) ^ R * β ^ (R - 1))

theorem aReal_eq (R e : ℕ) (β : ℚ) : ((AQ R e β : ℚ) : ℝ) = aReal R e (β : ℝ) := by
  unfold AQ cRQ aReal
  push_cast
  rfl

theorem prefactor_le (R e : ℕ) (β : ℝ≥0∞) (βr : ℝ) (hR : 1 ≤ R) (hβ : ENNReal.ofReal βr ≤ β)
    (hpos : R = 1 ∨ 0 < βr) :
    cMom R / (((2 : ℝ≥0∞) ^ e) ^ R * β ^ (R - 1)) ≤ ENNReal.ofReal (aReal R e βr) := by
  have hden : 0 < ((2 : ℝ) ^ e) ^ R * βr ^ (R - 1) := by
    rcases hpos with h1 | h2
    · subst h1; simp
    · positivity
  have hpowβ : ENNReal.ofReal βr ^ (R - 1) = ENNReal.ofReal (βr ^ (R - 1)) := by
    rcases hpos with h1 | h2
    · subst h1; simp
    · rw [ENNReal.ofReal_pow h2.le]
  calc cMom R / (((2 : ℝ≥0∞) ^ e) ^ R * β ^ (R - 1))
      ≤ cMom R / (((2 : ℝ≥0∞) ^ e) ^ R * ENNReal.ofReal βr ^ (R - 1)) := by
        gcongr
    _ = ENNReal.ofReal (aReal R e βr) := by
        unfold aReal cMom
        rw [hpowβ, show ((2 : ℝ≥0∞) ^ e) ^ R = ENNReal.ofReal (((2 : ℝ) ^ e) ^ R) by
          rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat],
          ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos hden]

/-- The final real inequality. -/
theorem final_real (q qa qb Kc Nn Ar Le Y : ℝ) (hqa : qa ≤ q) (hqb : q ≤ qb) (hqa0 : 0 ≤ qa)
    (hAr : 0 ≤ Ar) (hLe0 : 0 ≤ Le) (hLe1 : Le < 1) (hY : Y ≤ Le / (1 - Le))
    (hcheck : qb * Ar * (Le / (1 - Le)) + (qb + Kc + Nn) / 2 ^ 200 ≤ (qa / 2 ^ 128) ^ 2 + Kc / 2 ^ 127) :
    (1 - ((2 ^ 128 - 0 - q) / (2 ^ 128 - 0)) ^ 2) + q * (Ar * Y) + (q + Kc + Nn) / 2 ^ 200 ≤
      (q + Kc) / 2 ^ 127 := by
  have hq0 : 0 ≤ q := le_trans hqa0 hqa
  have hF : 0 ≤ Le / (1 - Le) := div_nonneg hLe0 (by linarith)
  have h1 : q * (Ar * Y) ≤ qb * Ar * (Le / (1 - Le)) := by
    calc q * (Ar * Y) ≤ q * (Ar * (Le / (1 - Le))) := by gcongr
      _ ≤ qb * (Ar * (Le / (1 - Le))) := by gcongr
      _ = qb * Ar * (Le / (1 - Le)) := by ring
  have h2 : (qa / 2 ^ 128) ^ 2 ≤ (q / 2 ^ 128) ^ 2 := by gcongr
  have h3 : (q + Kc + Nn) / 2 ^ 200 ≤ (qb + Kc + Nn) / 2 ^ 200 := by gcongr
  have h4 : (1 - ((2 ^ 128 - 0 - q) / (2 ^ 128 - 0)) ^ 2) = 2 * q / 2 ^ 128 - (q / 2 ^ 128) ^ 2 := by
    simp only [sub_zero]
    field_simp
    ring
  have h5 : (q + Kc) / 2 ^ 127 = 2 * q / 2 ^ 128 + Kc / 2 ^ 127 := by
    field_simp
  rw [h4, h5]
  linarith

theorem aReal_nonneg (R e : ℕ) (βr : ℝ) (hpos : R = 1 ∨ 0 < βr) : 0 ≤ aReal R e βr := by
  unfold aReal
  rcases hpos with h1 | h2
  · subst h1; simp
  · positivity

/-! ### (b) The bound for one certificate entry -/

theorem bound_of_entry (b N : ℕ) (hb : subtreeHeight = b) (hN : signatureLimit = N) (c : Entry)
    (hc : checkI b N c = true) (q : ℕ) (hqa : c.1 ≤ q) (hqb : q ≤ c.2.1) :
    (1 - HiddenDebt.budget 0 q) + (q : ℝ≥0∞) * hOf q +
        ((q + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) + signatureLimit : ℕ) : ℝ≥0∞) *
          (2 : ℝ≥0∞)⁻¹ ^ 200 ≤
      ((q + (258 * 2 ^ subtreeHeight + 2 * (26 - subtreeHeight)) : ℕ) : ℝ≥0∞) / 2 ^ 127 := by
  obtain ⟨qa, qb, R, e, m⟩ := c
  simp only [checkI, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hR, hqb2⟩, hmu⟩, hβpos⟩, hLe⟩, hmain⟩ := hc
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
  have hmuR : (muExactQ b N qb R : ℝ) ≤ μr := by
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
  set α : ℝ≥0∞ := (1 + signatureLimit * w) * (1 + w * L) ^ (24 * R) / L with hαdef
  set γ : ℝ≥0∞ := landing * (signatureLimit * w) * (1 + w * L) ^ (24 * R) / L with hγdef
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
  have hslack : (1 + signatureLimit * w) * (1 + w * L) ^ (24 * R) ≤ L * α := by
    rw [hαdef, ENNReal.mul_div_cancel hL0 hLT]
  have hLα : 1 ≤ L * α := by
    rw [hαdef, ENNReal.mul_div_cancel hL0 hLT]
    exact one_le_mul le_self_add (one_le_pow₀ le_self_add)
  have hγ : landing * (signatureLimit * w) * (1 + w * L) ^ (24 * R) ≤ L * γ := by
    rw [hγdef, ENNReal.mul_div_cancel hL0 hLT]
  have hmainE := hTerm_excess_le (Prod.fst : View → Fin (2 ^ subtreeHeight)) (Finset.univ : Finset View)
    uniformIndex_univ Finset.univ_nonempty kappa β t
    kappa_ne_top R hR hβ0 hβT ht0 htT signatureLimit q α w landing γ hw1 ForsPotential.landing_le_one hL0
    hslack hLα hγ
  have hH : hOf q = hTerm (Finset.univ : Finset View) w landing signatureLimit q
      (fun d => countPrice (Prod.fst : View → Fin (2 ^ subtreeHeight)) kappa d - β) := by
    unfold hOf hTerm
    rw [excess_eq]
  -- the rate and the Poisson mean
  have hμ : (signatureLimit : ℝ≥0∞) * α + q * γ ≤ ENNReal.ofReal μr := by
    have h := mu_le b N R q qb hb hqb hqb2 μr hmuR
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
  have hH0 : hOf q ≤ ENNReal.ofReal (Ar * (Pr ^ (2 ^ b) - 1)) := by
    have h1 : hOf q + A ≤ A * Pμ ^ (2 ^ b) := by
      rw [hH, ← hprod]
      exact hmainE
    have h2 : hOf q ≤ A * Pμ ^ (2 ^ b) - A := ENNReal.le_sub_of_add_le_right hAT h1
    have h3 : A * Pμ ^ (2 ^ b) - A = A * (Pμ ^ (2 ^ b) - 1) := by
      rw [ENNReal.mul_sub (fun _ _ => hAT), mul_one]
    calc hOf q ≤ A * (Pμ ^ (2 ^ b) - 1) := h3 ▸ h2
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
  calc 1 - HiddenDebt.budget 0 q + (q : ℝ≥0∞) * hOf q + ((q + kCredit b + N : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 200
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

end LeanSphincs.Security.H0
