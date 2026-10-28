import FORS.SWRoute.Interface

/-! **The SW route's rational checks and their real meaning.** `checkNumSW` is the rational form of
`SWNumeric` at the right end `x_b = q_b / 2^128` of an entry, with the contact coefficient
`c_U = N / (2^b 2^a) + q_b 2^b E_n / 2^a`; `swMainQ` is the entry's main inequality

  `satUp(ρ, x_a) + q_b B_c + δ q_b B_n + coin(q_b) + (q_b + K + N) / 2^200 ≤ 2 x_a + K / 2^127`.

`satUp ρ x - 2 x` decreases in `x` (`ρ ≤ 2`) and every other term grows, so the check at the ends of
`[q_a, q_b]` gives the route's inequality at every budget of the entry (`sw_entry_real`). -/

namespace FORS.Security.SWRoute

open HiddenDebt

/-! ### Rational side conditions -/

/-- The rational second-order saturation bound. -/
def satUpQ (ρ x : ℚ) : ℚ := ρ * x - ρ * (ρ - 1) * x ^ 2 / 2

/-- The rational coin bound at budget `q`. -/
def coinQ (q : ℕ) : ℚ := ((q : ℚ) / 2 ^ 128) ^ 2 / 2 ^ 30 + ((q : ℚ) / 2 ^ 128) / 2 ^ 100 + 1 / 2 ^ 180

/-- The contact coefficient at the right end `qb`, from the near mean `En` of a checked `OptN`. -/
def cUQ (b a N qb : ℕ) (En : ℚ) : ℚ := (N : ℚ) / (2 ^ b * 2 ^ a) + (qb : ℚ) * (2 ^ b * En) / 2 ^ a

/-- **The side conditions, rationally**, at `x` with contact coefficient `cU`. -/
def checkNumSW (ρ β δ x cU : ℚ) : Bool :=
  decide (0 ≤ x) && decide (x ≤ 1 / 8) && decide (3 / 2 ≤ ρ) && decide (ρ ≤ 2) &&
    decide (1 / 2 ≤ (ρ - 1) * (1 - ρ * x)) &&
    decide (4032 * (2 - ρ) * x / (1 - x) ≤ ρ - 1) &&
    decide (2 - ρ ≤ (1 - x) ^ 65) &&
    decide (1 + (3 - ρ) * x / (1 - x) + cU / (1 - x) ^ 3 ≤ ρ) &&
    decide (0 ≤ cU) && decide (0 ≤ β) &&
    decide (β ≤ ρ / (1 + (ρ - 1) * x / (1 - x))) &&
    decide (β ≤ 2 * (1 - x)) && decide (β ≤ 3 * (1 - x) ^ 2) &&
    decide (β ≤ 66 * (1 - x) ^ 65) && decide (β ≤ 67 * (1 - x) ^ 66) &&
    decide ((1 - ρ * x + ρ * (ρ - 1) * x ^ 2 / 2) * (2 - ρ) * x / (1 - x) ≤ δ)

theorem checkNumSW_sound {ρ β δ x cU : ℚ} (h : checkNumSW ρ β δ x cU = true) :
    SWNumeric (ρ : ℝ) (β : ℝ) (δ : ℝ) (x : ℝ) (cU : ℝ) := by
  simp only [checkNumSW, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩ := h
  have c : ∀ {u v : ℚ}, u ≤ v → (u : ℝ) ≤ (v : ℝ) := fun h => by exact_mod_cast h
  have r1 := c h1; have r2 := c h2; have r3 := c h3; have r4 := c h4; have r5 := c h5; have r6 := c h6
  have r7 := c h7; have r8 := c h8; have r9 := c h9; have r10 := c h10; have r11 := c h11; have r12 := c h12
  have r13 := c h13; have r14 := c h14; have r15 := c h15; have r16 := c h16
  push_cast at r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
  exact ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16⟩

/-- The main inequality of an entry `[qa, qb]` with cover bound `BC`, near bound `BN`, keygen
credit `K` and limit `N`. -/
def swMainQ (K N qa qb : ℕ) (ρ δ BC BN : ℚ) : Bool :=
  decide (satUpQ ρ ((qa : ℚ) / 2 ^ 128) + (qb : ℚ) * BC + δ * ((qb : ℚ) * BN) + coinQ qb +
      ((qb : ℚ) + K + N) / 2 ^ 200 ≤ 2 * ((qa : ℚ) / 2 ^ 128) + (K : ℚ) / 2 ^ 127)

/-! ### The real form of an entry -/

/-- **One entry in reals.** At every budget `q ∈ [qa, qb]`, the route's terms fit: the saturation
bound at `x = q / 2^128`, `q` times the cover and near bounds, the coin and the slack are at most
`(q + K) / 2^127`. -/
theorem sw_entry_real (q qa qb K N ρ δ BC BN XC XN : ℝ) (hqa : qa ≤ q) (hqb : q ≤ qb) (hqa0 : 0 ≤ qa)
    (hρ1 : 1 ≤ ρ) (hρ2 : ρ ≤ 2) (hδ : 0 ≤ δ) (hXC : XC ≤ BC) (hXN : XN ≤ BN) (hXC0 : 0 ≤ XC) (hXN0 : 0 ≤ XN)
    (coin coinB : ℝ) (hcoin : coin ≤ coinB)
    (hmain : satUp ρ (qa / 2 ^ 128) + qb * BC + δ * (qb * BN) + coinB + (qb + K + N) / 2 ^ 200 ≤
      2 * (qa / 2 ^ 128) + K / 2 ^ 127) :
    satUp ρ (q / 2 ^ 128) + q * XC + δ * (q * XN) + coin + (q + K + N) / 2 ^ 200 ≤ (q + K) / 2 ^ 127 := by
  have hq0 : 0 ≤ q := le_trans hqa0 hqa
  -- `satUp ρ x - 2 x` decreases in `x`
  have hsat : satUp ρ (q / 2 ^ 128) - 2 * (q / 2 ^ 128) ≤ satUp ρ (qa / 2 ^ 128) - 2 * (qa / 2 ^ 128) := by
    unfold satUp
    have hx : qa / 2 ^ 128 ≤ q / 2 ^ 128 := by gcongr
    have hxa : 0 ≤ qa / (2 : ℝ) ^ 128 := by positivity
    have hρρ : 0 ≤ ρ * (ρ - 1) := by nlinarith
    have hsq : (qa / 2 ^ 128) ^ 2 ≤ (q / (2 : ℝ) ^ 128) ^ 2 := by gcongr
    nlinarith
  have h1 : q * XC ≤ qb * BC := mul_le_mul hqb hXC hXC0 (by linarith)
  have h2 : δ * (q * XN) ≤ δ * (qb * BN) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hqb hXN hXN0 (by linarith)) hδ
  have h3 : (q + K + N) / 2 ^ 200 ≤ (qb + K + N) / 2 ^ 200 := by gcongr
  have e : (q + K) / (2 : ℝ) ^ 127 = 2 * (q / 2 ^ 128) + K / 2 ^ 127 := by ring
  rw [e]
  linarith

end FORS.Security.SWRoute
