import FORS.SWRoute.ForecastTail
import FORS.SWRoute.ForecastLight

/-! **The kernel-checkable certificate of `ForecastTail`.** A certificate (`TailCert`) gives the
cap `n0`, the Chernoff parameters `θ_D` (`D < n0`) and the precision of the exponential bounds; with
a Poisson table `t` of rate `μ̄` (`checkPT`, `checkRate`) it is checked by `checkTail`:

* `v_D = θ_D (m - fresh_D - 2^-10) - q lam1Q_D ≥ 0`, where `lam1Q_D ≥ Γ_D - 1` replaces every
  `e^u - 1` by `excessUp u` (`u / (1 - u)` below `1/2`, the squaring bound `expUp u - 1` above);
* `(1 - m)⁺ (2^b lightTail(t, n0 - 1) + Σ_{D < n0} k 2^a 2^b μ̄^D / D! / expLow(v_D) + 2^-99) ≤ Pb`.

**Soundness** (`forecastTail_of_check`): `Γ_D^q ≤ e^{q (Γ_D - 1)}`, `e^{-v} ≤ 1 / expLow v`, and the
light tail bounds the Poisson mean of `(n - (n0 - 1))⁺` (`poisMean_leaf_le`). The closed forms
(Touchard polynomials, `freshK`, `phiK`) are generic in the field, so their rational values cast to
the real ones (`touchard_cast`, `freshK_cast`, `phiK_cast`). -/

open ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Security FORS.Security.H0 FORS.Base.H0 ForsPrice
open FORS.Base.H0 (expUp expLow exp_le_expUp expLow_le one_le_expLow)

set_option linter.unusedSectionVars false

/-! ### Casts of the closed forms -/

theorem chooseK_cast (n j : ℕ) : ((chooseK n j : ℚ) : ℝ) = (chooseK n j : ℝ) := by
  unfold chooseK; push_cast; rfl

theorem chooseK_nonneg (n j : ℕ) : (0 : ℝ) ≤ chooseK n j := by unfold chooseK; positivity

theorem chooseK_nonnegQ (n j : ℕ) : (0 : ℚ) ≤ chooseK n j := by unfold chooseK; positivity

theorem getD_map_cast (L : List ℚ) (i : ℕ) :
    (L.map (fun x : ℚ => (x : ℝ))).getD i 0 = ((L.getD i 0 : ℚ) : ℝ) := by
  have h := List.getD_map (fun x : ℚ => (x : ℝ)) (l := L) (n := i) (d := 0)
  simp only [Rat.cast_zero] at h
  exact h

theorem touchardGo_cast (μ : ℚ) : ∀ (s n : ℕ) (L : List ℚ),
    (touchardGo μ s n L).map (fun x : ℚ => (x : ℝ)) = touchardGo (μ : ℝ) s n (L.map fun x : ℚ => (x : ℝ))
  | 0, _, _ => rfl
  | s + 1, n, L => by
      simp only [touchardGo]
      rw [touchardGo_cast μ s (n + 1)]
      congr 1
      rw [List.map_append, List.map_singleton]
      congr 2
      rw [Rat.cast_mul, Rat.cast_list_sum, List.map_map]
      congr 2
      refine List.map_congr_left fun i _ => ?_
      simp only [Function.comp_apply]
      rw [Rat.cast_mul, chooseK_cast, getD_map_cast]

theorem touchard_cast (μ : ℚ) (r : ℕ) : ((touchard μ r : ℚ) : ℝ) = touchard (μ : ℝ) r := by
  unfold touchard
  rw [← getD_map_cast, touchardGo_cast]
  simp

theorem phiK_cast (a : ℕ) (μ : ℚ) (r : ℕ) : ((phiK a μ r : ℚ) : ℝ) = phiK a (μ : ℝ) r := by
  unfold phiK; push_cast; rw [touchard_cast]

theorem freshK_cast (b k a : ℕ) (μ : ℚ) (q D : ℕ) :
    ((freshK b k a μ q D : ℚ) : ℝ) = freshK b k a (μ : ℝ) q D := by
  unfold freshK
  rw [Rat.cast_mul, Rat.cast_div, Rat.cast_div, Rat.cast_list_sum, List.map_map]
  push_cast
  congr 3
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  rw [Rat.cast_mul, Rat.cast_mul, chooseK_cast, touchard_cast]
  push_cast
  rfl

/-! ### The certificate -/

/-- An upper bound for `e^u - 1`: `u / (1 - u)` below `1/2`, `expUp u s P - 1` above. -/
def excessUp (u : ℚ) (s P : ℕ) : ℚ := if u < 1 / 2 then u / (1 - u) else expUp u s P - 1

/-- A tail certificate: the cap `n0`, `θ_D` for `D < n0`, and the precision (`s` squarings, `P`
bits, `J` series terms). -/
structure TailCert where
  n0 : ℕ
  th : List ℚ
  s : ℕ
  P : ℕ
  J : ℕ

/-- `Γ_D - 1 ≤ lam1Q`. -/
def lam1Q (b k a : ℕ) (mu : ℚ) (D : ℕ) (th : ℚ) (s P : ℕ) : ℚ :=
  ((List.range k).map fun j => if 1 ≤ j then
    chooseK (k - 1) j * ((D : ℚ) / 2 ^ a) ^ (k - 1 - j) * excessUp (th * phiK a mu j) s P else 0).sum / 2 ^ (b + a)

/-- The Chernoff exponent of `D`. -/
def vQ (b k a : ℕ) (mu : ℚ) (q : ℕ) (m : ℚ) (c : TailCert) (D : ℕ) : ℚ :=
  c.th.getD D 0 * (m - freshK b k a mu q D - 1 / 2 ^ 10) - q * lam1Q b k a mu D (c.th.getD D 0) c.s c.P

/-- The term of `D`. -/
def termQ (b k a : ℕ) (mu : ℚ) (q : ℕ) (m : ℚ) (c : TailCert) (D : ℕ) : ℚ :=
  k * 2 ^ a * 2 ^ b * (mu ^ D / D.factorial) / expLow (vQ b k a mu q m c D) c.J c.P

/-- The tail sum, before the excess factor. -/
def tailQ (b k a : ℕ) (t : PoisT) (q : ℕ) (m : ℚ) (c : TailCert) : ℚ :=
  2 ^ b * lightTail t (c.n0 - 1) + ((List.range c.n0).map (termQ b k a t.mu q m c)).sum + 1 / 2 ^ 99

/-! ### The coin condition -/

/-- The cap floor at heights `b`, `a` and `k` trees (`capFloor` of the parameters). -/
def capFloorN (b k a : ℕ) : ℕ := 2 * (b + (a + 1) * k + 101)

/-- **The check of the coin condition** at budget `q` and cap `n0`. -/
def checkCoin (b k a : ℕ) (t : PoisT) (q n0 : ℕ) : Bool :=
  decide (0 < t.mu) &&
    decide (∀ r < k, 1 ≤ r → 4 * ((patCapN b a (capFloorN b k a) q 1 : ℕ) : ℚ) * coinR b a (capFloorN b k a) q t.mu r ≤
      (1 / 2 ^ 10) * (1 + ((patCapN b a (capFloorN b k a) q 1 : ℕ) : ℚ) * phiK a t.mu r)) &&
    decide (((1 + coinRateK b a (capFloorN b k a) q / t.mu) ^ (k - 1) - 1) * (1 + freshK b k a t.mu q n0) ≤
      (1 / 2 ^ 10) / 2)

theorem checkCoin_parts {b k a : ℕ} {t : PoisT} {q n0 : ℕ} (h : checkCoin b k a t q n0 = true) :
    0 < t.mu ∧
      (∀ r < k, 1 ≤ r → 4 * ((patCapN b a (capFloorN b k a) q 1 : ℕ) : ℚ) * coinR b a (capFloorN b k a) q t.mu r ≤
        (1 / 2 ^ 10) * (1 + ((patCapN b a (capFloorN b k a) q 1 : ℕ) : ℚ) * phiK a t.mu r)) ∧
      ((1 + coinRateK b a (capFloorN b k a) q / t.mu) ^ (k - 1) - 1) * (1 + freshK b k a t.mu q n0) ≤
        (1 / 2 ^ 10) / 2 := by
  simp only [checkCoin, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩


/-- **The check of a tail certificate.** -/
def checkTail (b k a : ℕ) (t : PoisT) (q : ℕ) (m : ℚ) (c : TailCert) (Pb : ℚ) : Bool :=
  decide (1 ≤ c.n0) && decide (c.th.length = c.n0) && decide (1 ≤ t.n1) &&
    decide (∀ D < c.n0, 0 ≤ c.th.getD D 0 ∧ (∀ j < k, c.th.getD D 0 * phiK a t.mu j < 2 ^ c.s) ∧
      0 ≤ vQ b k a t.mu q m c D) &&
    decide (max 0 (1 - m) * tailQ b k a t q m c ≤ Pb) && checkCoin b k a t q c.n0

theorem checkTail_parts {b k a : ℕ} {t : PoisT} {q : ℕ} {m : ℚ} {c : TailCert} {Pb : ℚ}
    (h : checkTail b k a t q m c Pb = true) :
    1 ≤ c.n0 ∧ c.th.length = c.n0 ∧ 1 ≤ t.n1 ∧
      (∀ D < c.n0, 0 ≤ c.th.getD D 0 ∧ (∀ j < k, c.th.getD D 0 * phiK a t.mu j < 2 ^ c.s) ∧
        0 ≤ vQ b k a t.mu q m c D) ∧
      max 0 (1 - m) * tailQ b k a t q m c ≤ Pb ∧ checkCoin b k a t q c.n0 = true := by
  simp only [checkTail, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-! ### Real bounds -/

theorem exp_sub_one_le_excessUp (u : ℚ) (s P : ℕ) (hu : 0 ≤ u) (hus : u < 2 ^ s) :
    Real.exp u - 1 ≤ (excessUp u s P : ℝ) := by
  unfold excessUp
  split_ifs with h
  · have hu1 : (u : ℝ) < 1 / 2 := by
      have h' := (Rat.cast_lt (K := ℝ)).mpr h
      push_cast at h'
      linarith
    have hu0 : (0 : ℝ) ≤ u := by exact_mod_cast hu
    have h1u : (0 : ℝ) < 1 - u := by linarith
    have hneg : 1 - (u : ℝ) ≤ Real.exp (-(u : ℝ)) := by
      have := Real.add_one_le_exp (-(u : ℝ)); linarith
    have hexp : Real.exp (u : ℝ) ≤ 1 / (1 - u) := by
      rw [le_div_iff₀ h1u]
      calc Real.exp (u : ℝ) * (1 - u) ≤ Real.exp (u : ℝ) * Real.exp (-(u : ℝ)) :=
            mul_le_mul_of_nonneg_left hneg (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hval : (((u / (1 - u)) : ℚ) : ℝ) = (u : ℝ) / (1 - u) := by push_cast; ring
    rw [hval]
    have : 1 / (1 - (u : ℝ)) - 1 = (u : ℝ) / (1 - u) := by field_simp; ring
    linarith
  · have := exp_le_expUp u s P hu hus
    push_cast
    linarith

theorem touchard_nonneg {μ : ℝ} (hμ : 0 ≤ μ) (r : ℕ) : 0 ≤ touchard μ r := by
  have hgo : ∀ (s n : ℕ) (L : List ℝ), (∀ x ∈ L, 0 ≤ x) → ∀ x ∈ touchardGo μ s n L, 0 ≤ x := by
    intro s
    induction s with
    | zero => intro n L hL; exact hL
    | succ s ih =>
        intro n L hL
        simp only [touchardGo]
        refine ih (n + 1) _ fun x hx => ?_
        rcases List.mem_append.1 hx with hx | hx
        · exact hL x hx
        · rw [List.mem_singleton.1 hx]
          refine mul_nonneg hμ (List.sum_nonneg fun y hy => ?_)
          obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
          refine mul_nonneg (chooseK_nonneg n i) ?_
          by_cases hi : i < L.length
          · rw [List.getD_eq_getElem _ _ hi]; exact hL _ (List.getElem_mem hi)
          · rw [List.getD_eq_default _ _ (by omega)]
  unfold touchard
  by_cases hr : r < (touchardGo μ r 0 [1]).length
  · rw [List.getD_eq_getElem _ _ hr]
    exact hgo r 0 [1] (by simp) _ (List.getElem_mem hr)
  · rw [List.getD_eq_default _ _ (by omega)]

theorem phiK_nonneg (a : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) (r : ℕ) : 0 ≤ phiK a μ r := by
  unfold phiK; have := touchard_nonneg hμ r; positivity

theorem gammaR_term_nonneg (k a : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) {φ : ℕ → ℝ} (hφ : ∀ j, 0 ≤ φ j) (D j : ℕ) :
    0 ≤ (if 1 ≤ j then chooseK (k - 1) j * ((D : ℝ) / 2 ^ a) ^ (k - 1 - j) * (Real.exp (θ * φ j) - 1) else 0) := by
  split_ifs
  · have : 1 ≤ Real.exp (θ * φ j) := Real.one_le_exp (mul_nonneg hθ (hφ j))
    have h2 : 0 ≤ Real.exp (θ * φ j) - 1 := by linarith
    have := chooseK_nonneg (k - 1) j
    positivity
  · exact le_rfl

theorem gammaR_nonneg (b k a : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) {φ : ℕ → ℝ} (hφ : ∀ j, 0 ≤ φ j) (D : ℕ) :
    0 ≤ gammaR b k a θ φ D := by
  unfold gammaR
  rw [list_sum_range]
  have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range k) => gammaR_term_nonneg k a hθ hφ D j)
  positivity

/-- `Γ_D ≤ 1 + lam1Q`. -/
theorem gammaR_le (b k a : ℕ) {mu : ℚ} (hmu : 0 ≤ mu) (D : ℕ) {th : ℚ} {s P : ℕ} (hth : 0 ≤ th)
    (hs : ∀ j < k, th * phiK a mu j < 2 ^ s) :
    gammaR b k a th (phiK a (mu : ℝ)) D ≤ 1 + (lam1Q b k a mu D th s P : ℝ) := by
  unfold gammaR lam1Q
  refine add_le_add le_rfl ?_
  rw [Rat.cast_div, Rat.cast_list_sum, List.map_map, list_sum_range, list_sum_range, Rat.cast_pow,
    Rat.cast_ofNat]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine Finset.sum_le_sum fun j hj => ?_
  simp only [Function.comp_apply]
  split_ifs with h1
  · have hmu' : (0 : ℚ) ≤ phiK a mu j := by
      have := phiK_nonneg a (μ := (mu : ℝ)) (by exact_mod_cast hmu) j
      rw [← phiK_cast] at this; exact_mod_cast this
    have hu0 : 0 ≤ th * phiK a mu j := mul_nonneg hth hmu'
    have hex := exp_sub_one_le_excessUp _ s P hu0 (hs j (Finset.mem_range.1 hj))
    rw [Rat.cast_mul, phiK_cast] at hex
    rw [Rat.cast_mul, Rat.cast_mul, chooseK_cast, Rat.cast_pow, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow,
      Rat.cast_ofNat]
    have hpos : (0 : ℝ) ≤ chooseK (k - 1) j * ((D : ℝ) / 2 ^ a) ^ (k - 1 - j) := by
      have := chooseK_nonneg (k - 1) j; positivity
    exact mul_le_mul_of_nonneg_left hex hpos
  · simp

/-- The light majorant: `(n - n*)⁺ ≤ leafQ (lightTab n1 n*) 1 n`. -/
theorem natSub_le_leafQ (n1 nstar n : ℕ) :
    (((n - nstar : ℕ) : ℝ≥0∞)) ≤ ENNReal.ofReal (leafQ (lightTab n1 nstar) 1 n : ℝ) := by
  rw [← ENNReal.ofReal_natCast]
  apply ENNReal.ofReal_le_ofReal
  have hq : ((n - nstar : ℕ) : ℚ) ≤ leafQ (lightTab n1 nstar) 1 n := by
    unfold leafQ
    rw [lightTab_length]
    split_ifs with hlt
    · rw [lightTab_getD hlt]
    · rw [lightTab_getD (by omega)]
      have h : n - nstar ≤ (n1 + 1 - 1 - nstar) + (n - (n1 + 1 - 1)) := by omega
      have h' : ((n - nstar : ℕ) : ℚ) ≤ ((n1 + 1 - 1 - nstar : ℕ) : ℚ) + ((n - (n1 + 1 - 1) : ℕ) : ℚ) := by
        exact_mod_cast h
      linarith
  exact_mod_cast hq

theorem gammaR_one_le (b k a : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) {φ : ℕ → ℝ} (hφ : ∀ j, 0 ≤ φ j) (D : ℕ) :
    1 ≤ gammaR b k a θ φ D := by
  unfold gammaR
  rw [list_sum_range]
  have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range k) => gammaR_term_nonneg k a hθ hφ D j)
  have : 0 ≤ (∑ j ∈ Finset.range k, (if 1 ≤ j then chooseK (k - 1) j * ((D : ℝ) / 2 ^ a) ^ (k - 1 - j) *
      (Real.exp (θ * φ j) - 1) else 0)) / 2 ^ (b + a) := by positivity
  linarith

theorem freshK_mono (b k a : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) {q q' : ℕ} (hq : q ≤ q') (D : ℕ) :
    freshK b k a μ q D ≤ freshK b k a μ q' D := by
  unfold freshK
  have hS : 0 ≤ ((List.range k).map fun i => chooseK (k - 1) i * (D : ℝ) ^ (k - 1 - i) * touchard μ i).sum := by
    refine List.sum_nonneg fun y hy => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    have := chooseK_nonneg (k - 1) i
    have := touchard_nonneg hμ i
    positivity
  have hq' : (q : ℝ) ≤ q' := by exact_mod_cast hq
  gcongr

theorem coinGo_cast (b a cf q : ℕ) : ∀ (t n : ℕ) (L : List ℚ),
    (coinGo b a cf q t n L).map (fun x : ℚ => (x : ℝ)) = coinGo b a cf q t n (L.map fun x : ℚ => (x : ℝ))
  | 0, _, _ => rfl
  | t + 1, n, L => by
      simp only [coinGo]
      rw [coinGo_cast b a cf q t (n + 1)]
      congr 1
      rw [List.map_append, List.map_singleton]
      congr 2
      rw [Rat.cast_list_sum, List.map_map]
      congr 1
      refine List.map_congr_left fun j _ => ?_
      simp only [Function.comp_apply]
      rw [Rat.cast_mul, Rat.cast_div, Rat.cast_mul, chooseK_cast, getD_map_cast, Rat.cast_natCast, Rat.cast_pow,
        Rat.cast_ofNat]

theorem coinV_cast (b a cf q s : ℕ) : ((coinV b a cf q s : ℚ) : ℝ) = coinV b a cf q s := by
  unfold coinV
  rw [← getD_map_cast, coinGo_cast]
  simp

theorem coinR_cast (b a cf q : ℕ) (μ : ℚ) (r : ℕ) : ((coinR b a cf q μ r : ℚ) : ℝ) = coinR b a cf q (μ : ℝ) r := by
  unfold coinR
  rw [Rat.cast_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun s _ => ?_
  simp only [Function.comp_apply]
  split_ifs
  · rw [Rat.cast_mul, Rat.cast_mul, chooseK_cast, coinV_cast, phiK_cast]
  · simp

theorem coinRateK_cast (b a cf q : ℕ) : ((coinRateK b a cf q : ℚ) : ℝ) = coinRateK b a cf q := by
  unfold coinRateK; push_cast; rfl

theorem patCapN_mono (b a cf s : ℕ) {q q' : ℕ} (hq : q ≤ q') : patCapN b a cf q s ≤ patCapN b a cf q' s := by
  unfold patCapN
  exact max_le_max (Nat.add_le_add_right (Nat.div_le_div_right (Nat.mul_le_mul_left 6 hq)) 1) le_rfl

theorem one_le_patCapN (b a cf q s : ℕ) : 1 ≤ patCapN b a cf q s := by
  unfold patCapN; exact le_trans (Nat.le_add_left 1 _) (le_max_left _ _)

theorem getD_append_single (L : List ℝ) (x : ℝ) (i : ℕ) :
    (L ++ [x]).getD i 0 = if i < L.length then L.getD i 0 else if i = L.length then x else 0 := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · rw [List.getD_append_right _ _ _ _ (by omega), h2, Nat.sub_self]; rfl
  · rw [List.getD_append_right _ _ _ _ (by omega)]
    rw [List.getD_eq_default _ _ (by simp; omega)]

theorem coinGo_mono {b a cf q q' : ℕ} (hq : q ≤ q') : ∀ (t n : ℕ) (L L' : List ℝ), L.length = L'.length →
    (∀ i, 0 ≤ L.getD i 0 ∧ L.getD i 0 ≤ L'.getD i 0) →
    ∀ i, 0 ≤ (coinGo b a cf q t n L).getD i 0 ∧ (coinGo b a cf q t n L).getD i 0 ≤ (coinGo b a cf q' t n L').getD i 0
  | 0, _, _, _, _, hL, i => hL i
  | t + 1, n, L, L', hlen, hL, i => by
      simp only [coinGo]
      refine coinGo_mono hq t (n + 1) _ _ (by simp [hlen]) (fun i => ?_) i
      rw [getD_append_single, getD_append_single, hlen]
      split_ifs
      · exact hL i
      · rw [list_sum_range, list_sum_range]
        constructor
        · refine Finset.sum_nonneg fun j _ => ?_
          have := chooseK_nonneg n j
          have := (hL (n - j)).1
          positivity
        · refine Finset.sum_le_sum fun j _ => ?_
          have h1 : ((patCapN b a cf q (j + 1) : ℕ) : ℝ) ≤ ((patCapN b a cf q' (j + 1) : ℕ) : ℝ) := by
            exact_mod_cast patCapN_mono b a cf (j + 1) hq
          have hc := chooseK_nonneg n j
          have h0 := (hL (n - j)).1
          have h2 := (hL (n - j)).2
          have : chooseK n j * ((patCapN b a cf q (j + 1) : ℕ) : ℝ) / 2 ^ 128 ≤
              chooseK n j * ((patCapN b a cf q' (j + 1) : ℕ) : ℝ) / 2 ^ 128 := by gcongr
          exact mul_le_mul this h2 h0 (by positivity)
      · exact ⟨le_rfl, le_rfl⟩

theorem coinV_mono (b a cf s : ℕ) {q q' : ℕ} (hq : q ≤ q') :
    0 ≤ (coinV b a cf q s : ℝ) ∧ (coinV b a cf q s : ℝ) ≤ coinV b a cf q' s := by
  unfold coinV
  exact coinGo_mono hq s 0 [1] [1] rfl (fun i => ⟨by rcases i with _ | i <;> simp, le_rfl⟩) s

theorem coinR_mono (b a cf : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) (r : ℕ) {q q' : ℕ} (hq : q ≤ q') :
    0 ≤ coinR b a cf q μ r ∧ coinR b a cf q μ r ≤ coinR b a cf q' μ r := by
  unfold coinR
  rw [list_sum_range, list_sum_range]
  constructor
  · refine Finset.sum_nonneg fun s _ => ?_
    split_ifs
    · have := chooseK_nonneg r s
      have := (coinV_mono b a cf s hq).1
      have := phiK_nonneg a hμ (r - s)
      positivity
    · exact le_rfl
  · refine Finset.sum_le_sum fun s _ => ?_
    split_ifs
    · have := chooseK_nonneg r s
      have h1 := coinV_mono b a cf s hq
      have := phiK_nonneg a hμ (r - s)
      gcongr
      exact h1.2
    · exact le_rfl

/-- **The coin condition at every budget below the checked one.** -/
theorem coinCond_of_check {b k a : ℕ} {t : PoisT} {qb n0 : ℕ} (h : checkCoin b k a t qb n0 = true)
    {q : ℕ} (hq : q ≤ qb) : CoinCond b k a (capFloorN b k a) q (t.mu : ℝ) n0 := by
  obtain ⟨hmu, h1, h2⟩ := checkCoin_parts h
  have hmuR : (0 : ℝ) < (t.mu : ℝ) := by exact_mod_cast hmu
  set cf := capFloorN b k a
  refine ⟨fun r hr1 hrk => ?_, ?_, hmuR⟩
  · have hc := h1 r hrk hr1
    have hcR : 4 * ((patCapN b a cf qb 1 : ℕ) : ℝ) * coinR b a cf qb (t.mu : ℝ) r ≤
        coinSlack * (1 + ((patCapN b a cf qb 1 : ℕ) : ℝ) * phiK a (t.mu : ℝ) r) := by
      have := (Rat.cast_le (K := ℝ)).mpr hc
      push_cast at this
      rw [coinR_cast, phiK_cast] at this
      unfold coinSlack
      linarith
    have hA : (1 : ℝ) ≤ ((patCapN b a cf qb 1 : ℕ) : ℝ) := by exact_mod_cast one_le_patCapN b a cf qb 1
    have ha1 : (1 : ℝ) ≤ ((patCapN b a cf q 1 : ℕ) : ℝ) := by exact_mod_cast one_le_patCapN b a cf q 1
    have haA : ((patCapN b a cf q 1 : ℕ) : ℝ) ≤ ((patCapN b a cf qb 1 : ℕ) : ℝ) := by
      exact_mod_cast patCapN_mono b a cf 1 hq
    obtain ⟨hR0, hRle⟩ := coinR_mono b a cf hmuR.le r hq
    have hφ := phiK_nonneg a hmuR.le r
    have hs : (0 : ℝ) < coinSlack := by unfold coinSlack; norm_num
    -- coinR(qb) ≤ s / (4 A) + s φ / 4, so 4 a coinR(q) ≤ s a / A + s a φ ≤ s + s a φ
    set A := ((patCapN b a cf qb 1 : ℕ) : ℝ)
    set a' := ((patCapN b a cf q 1 : ℕ) : ℝ)
    set φr := phiK a (t.mu : ℝ) r
    have key : 4 * a' * coinR b a cf q (t.mu : ℝ) r * A ≤ coinSlack * (1 + a' * φr) * A := by
      have ha0 : (0 : ℝ) ≤ 4 * a' * A := mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
      have e1 : 4 * a' * coinR b a cf q (t.mu : ℝ) r * A ≤ a' * (4 * A * coinR b a cf qb (t.mu : ℝ) r) := by
        calc 4 * a' * coinR b a cf q (t.mu : ℝ) r * A = (4 * a' * A) * coinR b a cf q (t.mu : ℝ) r := by ring
          _ ≤ (4 * a' * A) * coinR b a cf qb (t.mu : ℝ) r := mul_le_mul_of_nonneg_left hRle ha0
          _ = a' * (4 * A * coinR b a cf qb (t.mu : ℝ) r) := by ring
      have e2 : a' * (4 * A * coinR b a cf qb (t.mu : ℝ) r) ≤ a' * (coinSlack * (1 + A * φr)) :=
        mul_le_mul_of_nonneg_left hcR (by linarith)
      have e3 : a' * (coinSlack * (1 + A * φr)) ≤ coinSlack * (1 + a' * φr) * A := by
        have h' : a' * coinSlack ≤ A * coinSlack := mul_le_mul_of_nonneg_right haA hs.le
        have eq1 : a' * (coinSlack * (1 + A * φr)) = a' * coinSlack + coinSlack * a' * A * φr := by ring
        have eq2 : coinSlack * (1 + a' * φr) * A = A * coinSlack + coinSlack * a' * A * φr := by ring
        rw [eq1, eq2]
        linarith
      linarith
    exact le_of_mul_le_mul_right key (by linarith)
  · have h2R : ((1 + coinRateK b a cf qb / (t.mu : ℝ)) ^ (k - 1) - 1) * (1 + freshK b k a (t.mu : ℝ) qb n0) ≤
        coinSlack / 2 := by
      have := (Rat.cast_le (K := ℝ)).mpr h2
      push_cast at this
      rw [coinRateK_cast, freshK_cast] at this
      unfold coinSlack
      linarith
    have hr : (coinRateK b a cf q : ℝ) ≤ coinRateK b a cf qb := by
      unfold coinRateK
      have : ((patCapN b a cf q 1 : ℕ) : ℝ) ≤ ((patCapN b a cf qb 1 : ℕ) : ℝ) := by
        exact_mod_cast patCapN_mono b a cf 1 hq
      gcongr
    have hr0 : (0 : ℝ) ≤ coinRateK b a cf q := by unfold coinRateK; positivity
    have hf := freshK_mono b k a hmuR.le hq n0
    have hf0 : 0 ≤ freshK b k a (t.mu : ℝ) q n0 := by
      unfold freshK
      refine mul_nonneg (by positivity) (div_nonneg (List.sum_nonneg fun y hy => ?_) (by positivity))
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
      have := chooseK_nonneg (k - 1) i
      have := touchard_nonneg hmuR.le i
      positivity
    have hp : (1 + coinRateK b a cf q / (t.mu : ℝ)) ^ (k - 1) ≤ (1 + coinRateK b a cf qb / (t.mu : ℝ)) ^ (k - 1) := by
      gcongr
    have hp1 : 1 ≤ (1 + coinRateK b a cf q / (t.mu : ℝ)) ^ (k - 1) :=
      one_le_pow₀ (by have : 0 ≤ coinRateK b a cf q / (t.mu : ℝ) := div_nonneg hr0 hmuR.le; linarith)
    calc ((1 + coinRateK b a cf q / (t.mu : ℝ)) ^ (k - 1) - 1) * (1 + freshK b k a (t.mu : ℝ) q n0)
        ≤ ((1 + coinRateK b a cf qb / (t.mu : ℝ)) ^ (k - 1) - 1) * (1 + freshK b k a (t.mu : ℝ) qb n0) :=
          mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
      _ ≤ _ := h2R

/-! ### Soundness -/

/-- **A checked tail certificate proves `ForecastTail` at every budget `q ≤ qb`.** -/
theorem forecastTail_of_check (H b k a N qtop : ℕ) (hH : totalHeight = H) (hb : subtreeHeight = b)
    (hk : forsTrees = k) (ha : forsHeight = a) (hN : signatureLimit = N) (t : PoisT)
    (hr : checkRate H b N qtop t = true) (ht : checkPT t = true) (qb : ℕ) (hqb : qb ≤ qtop)
    (m : ℚ) (c : TailCert) (Pb : ℚ) (h : checkTail b k a t qb m c Pb = true) (q : ℕ) (hq : q ≤ qb) :
    ForecastTail (m : ℝ) q (Pb : ℝ) := by
  obtain ⟨hn0, hlen, h1, hD, hfin, hcoin⟩ := checkTail_parts h
  have hmu0 : (0 : ℚ) ≤ t.mu := t.mu_nonneg
  have hmuR : (0 : ℝ) ≤ (t.mu : ℝ) := by exact_mod_cast hmu0
  set μ : ℝ≥0 := ⟨(t.mu : ℝ), hmuR⟩ with hμ
  refine ⟨c.n0, μ, fun D => (c.th.getD D 0 : ℝ), hn0, ?_, fun D => ?_, ?_, ?_⟩
  · have := rate_le_tableF H b N qtop t hr hH hb hN q (le_trans hq hqb)
    rw [hb]
    exact this
  · show (0 : ℝ) ≤ ((c.th.getD D 0 : ℚ) : ℝ)
    by_cases hDn : D < c.n0
    · exact_mod_cast (hD D hDn).1
    · rw [List.getD_eq_default _ _ (by omega)]; simp
  · have hcf : capFloor = capFloorN b k a := by unfold capFloor capFloorN; rw [hb, hk, ha]
    rw [hb, hk, ha, hcf]
    exact coinCond_of_check hcoin hq
  · rw [hb, hk, ha]
    unfold tailSum
    -- the light term
    have hleaf := checkLeaf_lightTab h1 (c.n0 - 1)
    have hlight : (2 : ℝ≥0∞) ^ b * poisMean μ (fun n => ((n - (c.n0 - 1) : ℕ) : ℝ≥0∞)) ≤
        ENNReal.ofReal ((2 ^ b * lightTail t (c.n0 - 1) : ℚ) : ℝ) := by
      have hpm := poisMean_leaf_le ht hleaf (lightTab_length t.n1 (c.n0 - 1))
      have hsum : (((List.range (t.n1 + 1)).map fun n => t.pb n * (lightTab t.n1 (c.n0 - 1)).getD n 0).sum +
          t.pb (t.n1 + 1) * ((lightTab t.n1 (c.n0 - 1)).getD t.n1 0 / (1 - t.r) + 1 / (1 - t.r) ^ 2)) =
          lightTail t (c.n0 - 1) := by
        unfold lightTail
        rw [lightTab_getD (by omega)]
        congr 2
        refine List.map_congr_left fun n hn => ?_
        rw [lightTab_getD (List.mem_range.1 hn)]
      rw [hsum] at hpm
      have hmono : poisMean μ (fun n => ((n - (c.n0 - 1) : ℕ) : ℝ≥0∞)) ≤
          poisMean μ (fun n => ENNReal.ofReal (leafQ (lightTab t.n1 (c.n0 - 1)) 1 n : ℝ)) := by
        unfold poisMean
        exact ENNReal.tsum_le_tsum fun n => mul_le_mul_right (natSub_le_leafQ t.n1 (c.n0 - 1) n) _
      calc (2 : ℝ≥0∞) ^ b * poisMean μ (fun n => ((n - (c.n0 - 1) : ℕ) : ℝ≥0∞))
          ≤ (2 : ℝ≥0∞) ^ b * ENNReal.ofReal ((lightTail t (c.n0 - 1) : ℚ) : ℝ) :=
            mul_le_mul_right (le_trans hmono hpm) _
        _ = _ := by
            have h0 : (0 : ℝ) ≤ ((lightTail t (c.n0 - 1) : ℚ) : ℝ) := by exact_mod_cast lightTail_nonneg ht _
            rw [show ((2 ^ b * lightTail t (c.n0 - 1) : ℚ) : ℝ) = (2 : ℝ) ^ b * ((lightTail t (c.n0 - 1) : ℚ) : ℝ) by
              push_cast; ring, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
              ENNReal.ofReal_ofNat]
    -- the D-terms
    have hterm : ∀ D ∈ Finset.range c.n0, (k : ℝ≥0∞) * 2 ^ a * 2 ^ b * ENNReal.ofReal ((μ : ℝ) ^ D / D.factorial) *
        ENNReal.ofReal (Real.exp (-((c.th.getD D 0 : ℝ) * ((m : ℝ) - freshK b k a (μ : ℝ) q D - coinSlack)))) *
        ENNReal.ofReal (gammaR b k a (c.th.getD D 0 : ℝ) (phiK a (μ : ℝ)) D) ^ q ≤
        ENNReal.ofReal ((termQ b k a t.mu qb m c D : ℚ) : ℝ) := by
      intro D hDm
      obtain ⟨hth0, hths, hv⟩ := hD D (Finset.mem_range.1 hDm)
      set th := c.th.getD D 0 with hthdef
      have hth0' : (0 : ℝ) ≤ (th : ℝ) := by exact_mod_cast hth0
      have hφ : ∀ j, 0 ≤ phiK a (μ : ℝ) j := fun j => phiK_nonneg a hmuR j
      set l1 := lam1Q b k a t.mu D th c.s c.P with hl1
      have hg : gammaR b k a (th : ℝ) (phiK a (μ : ℝ)) D ≤ 1 + (l1 : ℝ) := gammaR_le b k a hmu0 D hth0 hths
      have hg1 := gammaR_one_le b k a hth0' hφ D
      have hg0 : 0 ≤ gammaR b k a (th : ℝ) (phiK a (μ : ℝ)) D := by linarith
      have hl10 : (0 : ℝ) ≤ (l1 : ℝ) := by linarith
      set v := vQ b k a t.mu qb m c D with hvdef
      have hpow : ENNReal.ofReal (gammaR b k a (th : ℝ) (phiK a (μ : ℝ)) D) ^ q ≤
          ENNReal.ofReal (Real.exp ((q : ℝ) * (l1 : ℝ))) := by
        rw [← ENNReal.ofReal_pow hg0]
        apply ENNReal.ofReal_le_ofReal
        have h1' : 0 ≤ 1 + (l1 : ℝ) := by linarith
        calc gammaR b k a (th : ℝ) (phiK a (μ : ℝ)) D ^ q ≤ (1 + (l1 : ℝ)) ^ q := pow_le_pow_left₀ hg0 hg q
          _ ≤ Real.exp (l1 : ℝ) ^ q := pow_le_pow_left₀ h1' (by have := Real.add_one_le_exp (l1 : ℝ); linarith) q
          _ = Real.exp ((q : ℝ) * (l1 : ℝ)) := by rw [← Real.exp_nat_mul]
      have hEL := expLow_le v c.J c.P hv
      have hEL1 : (1 : ℝ) ≤ (expLow v c.J c.P : ℝ) := by exact_mod_cast one_le_expLow _ c.J c.P hv
      have hvR : (v : ℝ) = (th : ℝ) * ((m : ℝ) - freshK b k a (μ : ℝ) qb D - coinSlack) - (qb : ℝ) * (l1 : ℝ) := by
        rw [hvdef]
        unfold vQ coinSlack
        push_cast
        rw [← hthdef, ← hl1, freshK_cast]
        rfl
      have hfr : freshK b k a (μ : ℝ) q D ≤ freshK b k a (μ : ℝ) qb D := freshK_mono b k a μ.2 hq D
      have hqR : (q : ℝ) ≤ qb := by exact_mod_cast hq
      have hle : -((th : ℝ) * ((m : ℝ) - freshK b k a (μ : ℝ) q D - coinSlack)) + (q : ℝ) * (l1 : ℝ) ≤ -(v : ℝ) := by
        rw [hvR]
        have := mul_le_mul_of_nonneg_left hfr hth0'
        have := mul_le_mul_of_nonneg_right hqR hl10
        nlinarith
      have hexp : Real.exp (-((th : ℝ) * ((m : ℝ) - freshK b k a (μ : ℝ) q D - coinSlack))) *
          Real.exp ((q : ℝ) * (l1 : ℝ)) ≤ 1 / (expLow v c.J c.P : ℝ) := by
        rw [← Real.exp_add, le_div_iff₀ (by linarith)]
        calc Real.exp (-((th : ℝ) * ((m : ℝ) - freshK b k a (μ : ℝ) q D - coinSlack)) + (q : ℝ) * (l1 : ℝ)) *
              (expLow v c.J c.P : ℝ)
            ≤ Real.exp (-(v : ℝ)) * Real.exp (v : ℝ) :=
              mul_le_mul (Real.exp_le_exp.2 hle) hEL (by linarith) (Real.exp_pos _).le
          _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have hA0 : (0 : ℝ) ≤ (μ : ℝ) ^ D / D.factorial := by positivity
      calc (k : ℝ≥0∞) * 2 ^ a * 2 ^ b * ENNReal.ofReal ((μ : ℝ) ^ D / D.factorial) *
            ENNReal.ofReal (Real.exp (-((th : ℝ) * ((m : ℝ) - freshK b k a (μ : ℝ) q D - coinSlack)))) *
            ENNReal.ofReal (gammaR b k a (th : ℝ) (phiK a (μ : ℝ)) D) ^ q
          ≤ (k : ℝ≥0∞) * 2 ^ a * 2 ^ b * ENNReal.ofReal ((μ : ℝ) ^ D / D.factorial) *
            ENNReal.ofReal (Real.exp (-((th : ℝ) * ((m : ℝ) - freshK b k a (μ : ℝ) q D - coinSlack)))) *
            ENNReal.ofReal (Real.exp ((q : ℝ) * (l1 : ℝ))) := by gcongr
        _ = ENNReal.ofReal ((k : ℝ) * 2 ^ a * 2 ^ b * ((μ : ℝ) ^ D / D.factorial) *
              (Real.exp (-((th : ℝ) * ((m : ℝ) - freshK b k a (μ : ℝ) q D - coinSlack))) *
                Real.exp ((q : ℝ) * (l1 : ℝ)))) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num),
              ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, mul_assoc _ (ENNReal.ofReal (Real.exp _))]
        _ ≤ ENNReal.ofReal ((k : ℝ) * 2 ^ a * 2 ^ b * ((μ : ℝ) ^ D / D.factorial) *
              (1 / (expLow v c.J c.P : ℝ))) := by
            apply ENNReal.ofReal_le_ofReal
            exact mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = ENNReal.ofReal ((termQ b k a t.mu qb m c D : ℚ) : ℝ) := by
            congr 1
            unfold termQ
            rw [← hvdef]
            push_cast
            rw [show ((μ : ℝ≥0) : ℝ) = (t.mu : ℝ) from rfl]
            ring
    have htnn : ∀ D ∈ Finset.range c.n0, (0 : ℝ) ≤ ((termQ b k a t.mu qb m c D : ℚ) : ℝ) := by
      intro D hDm
      have hv := (hD D (Finset.mem_range.1 hDm)).2.2
      have := one_le_expLow _ c.J c.P hv
      have : (0 : ℚ) ≤ termQ b k a t.mu qb m c D := by unfold termQ; positivity
      exact_mod_cast this
    have hsumT : ∑ D ∈ Finset.range c.n0, ENNReal.ofReal ((termQ b k a t.mu qb m c D : ℚ) : ℝ) =
        ENNReal.ofReal ((((List.range c.n0).map (termQ b k a t.mu qb m c)).sum : ℚ) : ℝ) := by
      rw [← ENNReal.ofReal_sum_of_nonneg htnn, list_sum_range]
      push_cast
      rfl
    have hT0 : (0 : ℝ) ≤ ((((List.range c.n0).map (termQ b k a t.mu qb m c)).sum : ℚ) : ℝ) := by
      rw [list_sum_range]
      push_cast
      exact Finset.sum_nonneg htnn
    have hL0 : (0 : ℝ) ≤ ((2 ^ b * lightTail t (c.n0 - 1) : ℚ) : ℝ) := by
      have := lightTail_nonneg ht (c.n0 - 1)
      have : (0 : ℚ) ≤ 2 ^ b * lightTail t (c.n0 - 1) := by positivity
      exact_mod_cast this
    have htq : ((tailQ b k a t qb m c : ℚ) : ℝ) = ((2 ^ b * lightTail t (c.n0 - 1) : ℚ) : ℝ) +
        ((((List.range c.n0).map (termQ b k a t.mu qb m c)).sum : ℚ) : ℝ) + 1 / 2 ^ 99 := by
      unfold tailQ
      push_cast
      ring
    have htot : (2 : ℝ≥0∞) ^ b * poisMean μ (fun n => ((n - (c.n0 - 1) : ℕ) : ℝ≥0∞)) +
        ∑ D ∈ Finset.range c.n0, (k : ℝ≥0∞) * 2 ^ a * 2 ^ b * ENNReal.ofReal ((μ : ℝ) ^ D / D.factorial) *
          ENNReal.ofReal (Real.exp (-((c.th.getD D 0 : ℝ) * ((m : ℝ) - freshK b k a (μ : ℝ) q D - coinSlack)))) *
          ENNReal.ofReal (gammaR b k a (c.th.getD D 0 : ℝ) (phiK a (μ : ℝ)) D) ^ q +
        ENNReal.ofReal (1 / 2 ^ 99) ≤ ENNReal.ofReal ((tailQ b k a t qb m c : ℚ) : ℝ) := by
      calc _ ≤ ENNReal.ofReal ((2 ^ b * lightTail t (c.n0 - 1) : ℚ) : ℝ) +
            ENNReal.ofReal ((((List.range c.n0).map (termQ b k a t.mu qb m c)).sum : ℚ) : ℝ) +
            ENNReal.ofReal (1 / 2 ^ 99) := by
            rw [← hsumT]
            exact add_le_add (add_le_add hlight (Finset.sum_le_sum hterm)) le_rfl
        _ = _ := by
            rw [← ENNReal.ofReal_add hL0 hT0, ← ENNReal.ofReal_add (by positivity) (by positivity), htq]
    refine le_trans (mul_le_mul_right htot _) ?_
    by_cases hm : (1 : ℝ) - m ≤ 0
    · rw [ENNReal.ofReal_of_nonpos hm, zero_mul]
      exact zero_le
    · push Not at hm
      rw [← ENNReal.ofReal_mul hm.le]
      apply ENNReal.ofReal_le_ofReal
      have hmq : (0 : ℚ) < 1 - m := by exact_mod_cast hm
      rw [max_eq_right hmq.le] at hfin
      exact_mod_cast hfin

/-- **The per-entry form**: a checked certificate at the right end `qb ≤ qtop` of an entry proves
`ForecastTail m q Pb` for every budget of the entry. -/
theorem tailOK_of_check (H b k a N qtop : ℕ) (hH : totalHeight = H) (hb : subtreeHeight = b)
    (hk : forsTrees = k) (ha : forsHeight = a) (hN : signatureLimit = N) (t : PoisT)
    (hr : checkRate H b N qtop t = true) (ht : checkPT t = true) (qa qb : ℕ) (hqb : qb ≤ qtop)
    (m Pb : ℚ) (c : TailCert) (h : checkTail b k a t qb m c Pb = true) :
    ∀ q, qa ≤ q → q ≤ qb → ForecastTail (m : ℝ) q (Pb : ℝ) :=
  fun q _ hq => forecastTail_of_check H b k a N qtop hH hb hk ha hN t hr ht qb hqb m c Pb h q hq

end FORS.Security.SWRoute
