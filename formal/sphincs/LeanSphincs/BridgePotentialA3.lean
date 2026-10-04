import LeanSphincs.BridgePotentialA2

/-! The invariant of the linear potential, the steps that do not store a fresh answer (reveals,
canonical continuations, guesses at cached inputs, cached reads), and the closing arithmetic of
each input class under the numeric conditions. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.PotentialA

open Concrete HiddenGraph HiddenDebt HiddenBridge EncodingCode

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-- The numeric conditions on the plain rate `ρ`, for `x = total / 2^128`. -/
structure Numeric (ρ x : ℝ) : Prop where
  low : 3 / 2 ≤ ρ
  high : ρ ≤ 2
  enc : 1 + 4032 * (2 - ρ) * x ≤ ρ
  contact : 1 + 66 * x ≤ ρ
  small : 64 * x ≤ 1

theorem ν_eq_ofReal : ν = ENNReal.ofReal ((2 : ℝ) ^ 128)⁻¹ := by
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp [ν]

theorem budget_ofReal (y : ℕ) : (y : ℝ≥0∞) * ν = ENNReal.ofReal ((y : ℝ) / 2 ^ 128) := by
  rw [ν_eq_ofReal, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _), div_eq_mul_inv]

theorem budget_le_x {y total : ℕ} (hy : y ≤ total) :
    (y : ℝ≥0∞) * ν ≤ ENNReal.ofReal ((total : ℝ) / 2 ^ 128) := by
  rw [budget_ofReal]
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (by exact_mod_cast hy) (by positivity))

theorem payment_eq (ρ : ℝ) : ENNReal.ofReal (ρ / 2 ^ 128) = ν * ENNReal.ofReal ρ := by
  rw [ν_eq_ofReal, div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul (by positivity)]

theorem mul_ofReal_le {Y : ℝ≥0∞} {x c : ℝ} (hY : Y ≤ ENNReal.ofReal x) (hx : 0 ≤ x) (hc : 0 ≤ c) :
    Y * ENNReal.ofReal c ≤ ENNReal.ofReal (x * c) := by
  rw [ENNReal.ofReal_mul hx]
  exact mul_le_mul_of_nonneg_right hY bot_le

section Arith

variable {ρ x : ℝ} (hN : Numeric ρ x) (hx : 0 ≤ x) {Y : ℝ≥0∞} (hY : Y ≤ ENNReal.ofReal x)
include hN hx hY

theorem arith_contact : 1 + Y * (ENNReal.ofReal (2 - ρ) + 64) ≤ ENNReal.ofReal ρ := by
  have h64 : ENNReal.ofReal (2 - ρ) + 64 = ENNReal.ofReal (66 - ρ) := by
    rw [show (64 : ℝ≥0∞) = ENNReal.ofReal 64 by simp, ← ENNReal.ofReal_add (by linarith [hN.high]) (by norm_num)]
    ring_nf
  rw [h64]
  calc 1 + Y * ENNReal.ofReal (66 - ρ) ≤ ENNReal.ofReal 1 + ENNReal.ofReal (x * (66 - ρ)) :=
        add_le_add (by simp) (mul_ofReal_le hY hx (by linarith [hN.high]))
    _ = ENNReal.ofReal (1 + x * (66 - ρ)) := (ENNReal.ofReal_add (by norm_num)
        (mul_nonneg hx (by linarith [hN.high]))).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [hN.contact, hN.low])

theorem arith_pair : 1 + Y ≤ ENNReal.ofReal ρ := by
  calc 1 + Y ≤ ENNReal.ofReal 1 + ENNReal.ofReal x := add_le_add (by simp) hY
    _ = ENNReal.ofReal (1 + x) := (ENNReal.ofReal_add (by norm_num) hx).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith [hN.contact])

theorem arith_small : 64 * Y ≤ 1 := by
  calc 64 * Y ≤ ENNReal.ofReal 64 * ENNReal.ofReal x := mul_le_mul_of_nonneg_left hY bot_le |>.trans_eq'
        (by simp)
    _ = ENNReal.ofReal (64 * x) := (ENNReal.ofReal_mul (by norm_num)).symm
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hN.small
    _ = 1 := by simp

theorem arith_enc : 1 + Y * (4032 * ENNReal.ofReal (2 - ρ)) ≤ ENNReal.ofReal ρ := by
  have h : (4032 : ℝ≥0∞) * ENNReal.ofReal (2 - ρ) = ENNReal.ofReal (4032 * (2 - ρ)) := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [h]
  calc 1 + Y * ENNReal.ofReal (4032 * (2 - ρ)) ≤ ENNReal.ofReal 1 + ENNReal.ofReal (x * (4032 * (2 - ρ))) :=
        add_le_add (by simp) (mul_ofReal_le hY hx (by linarith [hN.high]))
    _ = ENNReal.ofReal (1 + x * (4032 * (2 - ρ))) := (ENNReal.ofReal_add (by norm_num)
        (mul_nonneg hx (by linarith [hN.high]))).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [hN.enc])

end Arith

theorem one_le_ofReal {ρ : ℝ} (h : 1 ≤ ρ) : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ρ := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal h

theorem ofReal_le_two {ρ : ℝ} (h : ρ ≤ 2) : ENNReal.ofReal ρ ≤ 2 := by
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  exact ENNReal.ofReal_le_ofReal h

variable [Params]

namespace Ctx

variable (K : Ctx)

/-! ### The invariant -/

/-- Coordinates known from the start with fixed values: the chain values at and above the
prepared word of a landed leaf, and the FORS leaf values. -/
def Anchor (c : Coordinate) : Prop :=
  AboveWord K.p K.R c ∨ ∃ index tree leaf, c = .ftsValue index tree leaf

/-- **Invariant.** The prepared cache is kept, the anchors hold their values, and every fresh
parsed input whose incoming coordinate is still unexposed carries its guess record. -/
structure Inv (s : St) : Prop where
  prepared : Prepared K.initial s
  anchored : ∀ c, K.Anchor c → s.known c = some (K.F c)
  guessed : ∀ x u q, K.Fr s x u → HiddenGraph.parse K.p (candidateActive K.p) x = some q →
    s.known q.1.inputCoordinate = none → (q.1.inputCoordinate, q.2) ∈ s.guesses

variable {K} in
theorem Inv.expose {s : St} (h : K.Inv s) (c : Coordinate) (v : Digest) (hc : s.known c = none) :
    K.Inv (s.expose c v) where
  prepared := h.prepared
  anchored c' hc' := by
    have hne : c' ≠ c := by
      rintro rfl
      rw [h.anchored c' hc'] at hc
      cases hc
    have hk : (s.expose c v).known c' = s.known c' := by simp [DebtState.expose, hne]
    rw [hk]
    exact h.anchored c' hc'
  guessed x u q hfr hp hk := by
    refine h.guessed x u q hfr hp ?_
    by_cases hne : q.1.inputCoordinate = c
    · rw [hne]
      exact hc
    · have hk' : (s.expose c v).known q.1.inputCoordinate = s.known q.1.inputCoordinate := by
        simp [DebtState.expose, hne]
      rw [← hk']
      exact hk

variable {K} in
theorem Inv.record {s : St} (h : K.Inv s) (g : Coordinate × Digest) : K.Inv (s.record g) where
  prepared := h.prepared
  anchored := h.anchored
  guessed x u q hfr hp hk := List.mem_cons_of_mem _ (h.guessed x u q hfr hp hk)

variable {K} in
theorem Inv.store {s : St} (h : K.Inv s) (x : HashInput) (u : HashOutput) (hx : s.cache x = none)
    (hguess : ∀ q, HiddenGraph.parse K.p (candidateActive K.p) x = some q →
      s.known q.1.inputCoordinate = none → (q.1.inputCoordinate, q.2) ∈ s.guesses) :
    K.Inv (s.store x u) where
  prepared := prepared_store K.initial s h.prepared x u hx
  anchored := h.anchored
  guessed y w q hfr hp hk := by
    have hi := initial_none_of_fresh K.initial s h.prepared x hx
    rcases (K.fr_store u hx hi).1 hfr with hfr | ⟨rfl, -⟩
    · exact h.guessed y w q hfr hp hk
    · exact hguess q hp hk

/-! ### Steps without a fresh answer -/

theorem pot_succ (y : ℕ) (s : St) : K.pot (y + 1) s = K.pot y s + ν * K.rate s := by
  unfold pot
  push_cast
  ring

theorem pot_mono {y y' : ℕ} (h : y ≤ y') (s : St) : K.pot y s ≤ K.pot y' s := by
  unfold pot
  gcongr

theorem vrate_ge (hρ : K.ρ ≤ 2) (s : St) : ENNReal.ofReal K.ρ ≤ K.vrate s := by
  unfold vrate
  split_ifs
  · exact ofReal_le_two hρ
  · exact le_rfl

theorem vrate_le_rate (s : St) : K.vrate s ≤ K.rate s := by
  unfold rate
  rw [add_assoc]
  exact le_self_add

/-- A cached read: the step pays the digest baseline from the rate. -/
theorem pot_same (hρ : K.ρ ≤ 2) (hρ1 : 1 ≤ K.ρ) (y : ℕ) (s : St) (d : ℝ≥0∞) (hd : d ≤ 1) :
    K.pot y s + ν * (d * ENNReal.ofReal K.ρ) ≤ K.pot (y + 1) s := by
  rw [K.pot_succ]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ bot_le)
  calc d * ENNReal.ofReal K.ρ ≤ 1 * ENNReal.ofReal K.ρ := mul_le_mul_of_nonneg_right hd bot_le
    _ = ENNReal.ofReal K.ρ := one_mul _
    _ ≤ _ := (K.vrate_ge hρ s).trans (K.vrate_le_rate s)

theorem bad_expose (s : St) (c : Coordinate) (v : Digest) (hc : s.known c = none) :
    K.Bad (s.expose c v) → K.Bad s ∨ v ∈ debts K.tg K.initial s c := by
  rintro (hr | hw | hrev | htwo)
  · rcases (realized_expose K.tg K.initial s c v hc).1 hr with hr | hv
    · exact Or.inl (Or.inl hr)
    · exact Or.inr hv
  · exact Or.inl (Or.inr (Or.inl hw))
  · exact Or.inl (Or.inr (Or.inr (Or.inl hrev)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr htwo)))

/-- **Reveal.** Sampling an unexposed coordinate settles its debts with exactly their share. -/
theorem pot_expose_mean (y : ℕ) (s : St) (c : Coordinate) (hc : s.known c = none) :
    ∑' v, Pr[= v | ($ᵗ Digest : ProbComp Digest)] * K.pot y (s.expose c v) ≤ K.pot y s := by
  set E := ((debts K.tg K.initial s c).encard : ℝ≥0∞) * ν with hE
  have hEtop : E ≠ ⊤ := by
    refine ENNReal.mul_ne_top ?_ ν_ne_top
    rw [Ne, ENat.toENNReal_eq_top]
    exact (Set.toFinite _).encard_lt_top.ne
  have hpoint : ∀ v, K.pot y (s.expose c v) + E ≤
      K.pot y s + (if v ∈ debts K.tg K.initial s c then 1 else 0) := by
    intro v
    have hD := K.done_le (s := s) (s' := s.expose c v) (v ∈ debts K.tg K.initial s c) (K.bad_expose s c v hc)
    have hP := K.pend_expose s c v hc
    unfold pot
    have hUA : K.UAset (s.expose c v) = K.UAset s := rfl
    have hR : K.rate (s.expose c v) = K.rate s := rfl
    rw [hUA, hR, hP]
    calc K.done (s.expose c v) + K.pend (s.expose c v) + ν / 2 * ((K.UAset s).encard : ℝ≥0∞) +
          (y : ℝ≥0∞) * ν * K.rate s + E
        ≤ (K.done s + if v ∈ debts K.tg K.initial s c then 1 else 0) + K.pend (s.expose c v) +
          ν / 2 * ((K.UAset s).encard : ℝ≥0∞) + (y : ℝ≥0∞) * ν * K.rate s + E := by
          gcongr
          refine hD.trans (add_le_add le_rfl ?_)
          split_ifs <;> simp_all
      _ = _ := by ring
  have hmean : ∑' v, Pr[= v | ($ᵗ Digest : ProbComp Digest)] * (K.pot y (s.expose c v) + E) ≤
      ∑' v, Pr[= v | ($ᵗ Digest : ProbComp Digest)] *
        (K.pot y s + if v ∈ debts K.tg K.initial s c then 1 else 0) :=
    ENNReal.tsum_le_tsum fun v => mul_le_mul_of_nonneg_left (hpoint v) bot_le
  simp only [mul_add, probOutput_digest] at hmean
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, ENNReal.tsum_mul_right] at hmean
  have hsum : ∑' _v : Digest, ν = 1 := by
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_digest_ennreal, mul_comm,
      ν_mul_space]
  have hind : ∑' v : Digest, ν * (if v ∈ debts K.tg K.initial s c then (1 : ℝ≥0∞) else 0) = E := by
    rw [tsum_fintype, ← Finset.mul_sum]
    have := meanD_ite (fun v => v ∈ debts K.tg K.initial s c) (1 : ℝ≥0∞)
    rw [meanD] at this
    rw [this, mul_one, hE, mul_comm]
    rfl
  rw [hsum, one_mul, one_mul, hind] at hmean
  have hlhs : ∑' v, Pr[= v | ($ᵗ Digest : ProbComp Digest)] * K.pot y (s.expose c v) =
      ∑' v : Digest, ν * K.pot y (s.expose c v) := tsum_congr fun v => by rw [probOutput_digest]
  rw [hlhs]
  exact (ENNReal.add_le_add_iff_right hEtop).1 hmean

/-- A guess record whose FORS contact, if any, is already recorded keeps the recorded contacts. -/
theorem kfSet_record (s : St) (g : Coordinate × Digest)
    (h : ∀ index tree leaf secret, g = (Coordinate.ftsSecret index tree leaf, secret) →
      K.FContact s index tree leaf secret → g ∈ s.guesses) :
    K.KFset (s.record g) = K.KFset s := by
  ext ⟨index, tree, leaf, secret⟩
  simp only [KFset, Set.mem_setOf_eq, DebtState.record, List.mem_cons]
  constructor
  · rintro ⟨hc, rfl | hg⟩
    · exact ⟨hc, h _ _ _ _ rfl hc⟩
    · exact ⟨hc, hg⟩
  · rintro ⟨hc, hg⟩
    exact ⟨hc, Or.inr hg⟩

/-- **Guess record.** Recording a guess at an unexposed coordinate adds at most one debt. -/
theorem pot_record (y : ℕ) (s : St) (g : Coordinate × Digest) (hg : s.known g.1 = none)
    (hK : K.KFset (s.record g) = K.KFset s) : K.pot y (s.record g) ≤ K.pot y s + ν := by
  have hD : K.done (s.record g) ≤ K.done s := by
    have := K.done_le (s := s) (s' := s.record g) False (by
      rintro (hr | hw | ⟨index, tree, leaf, secret, hc, hng⟩ | htwo)
      · exact Or.inl (Or.inl ((realized_record K.tg K.initial s g hg).1 hr))
      · exact Or.inl (Or.inr (Or.inl hw))
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨index, tree, leaf, secret, hc,
          fun h => hng (List.mem_cons_of_mem _ h)⟩)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr htwo))))
    simpa using this
  have hR : K.rate (s.record g) = K.rate s := by
    unfold rate
    rw [hK]
    rfl
  have hUA : K.UAset (s.record g) = K.UAset s := rfl
  unfold pot
  rw [hR, hUA]
  calc K.done (s.record g) + K.pend (s.record g) + ν / 2 * ((K.UAset s).encard : ℝ≥0∞) +
        (y : ℝ≥0∞) * ν * K.rate s
      ≤ K.done s + (K.pend s + ν) + ν / 2 * ((K.UAset s).encard : ℝ≥0∞) + (y : ℝ≥0∞) * ν * K.rate s := by
        gcongr
        exact K.pend_record s g
    _ = _ := by ring

end Ctx

end LeanSphincs.Security.PotentialA
