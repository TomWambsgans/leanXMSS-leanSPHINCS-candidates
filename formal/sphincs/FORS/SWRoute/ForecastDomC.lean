import FORS.SWRoute.ForecastDomB

/-! **The domination of the own-cell forecast, part C: the future at one index.**

* `hTermO_fst_le`: the one-coin H-term (future pairs and fresh slots) of a one-index count function
  `H(n_I)` is at most `E_μ[H]` at any rate `μ ≥ N / 2^b + q (landing w) / 2^b`;
* the cover indicator `covI I ℓ T` (every tree of `T` is covered at index `I` for the leaves `ℓ`) is
  dominated by `(n_I / 2^a)^|T|` after averaging the marks (`covI_dominated`), so its H-term is at
  most `φ(|T|)` (`hTermO_covI_le`);
* one-index Poisson means on `ℕ` (`pois1`): semigroup, chord and rate monotonicity. -/

open ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base.Domination FORS.Base.H0 FORS.Security.H0 FORS.Security.H0Avg ForsPrice Concrete

set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### The rate of the future -/

theorem rate_ag (w : ℝ≥0∞) (hw : w ≤ 1) {n k N q : ℕ} (hn : n ≤ N) (hk : k ≤ q) (μ : ℝ≥0)
    (hμ : (N : ℝ) / 2 ^ subtreeHeight + (q : ℝ) * (landing * w).toReal / 2 ^ subtreeHeight ≤ μ) :
    ∃ α γ : ℝ≥0, (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * α = 1 ∧
      (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) * γ = landing * w ∧
        (n : ℝ≥0) * α + (k : ℝ≥0) * γ ≤ μ := by
  have hlw : landing * w ≠ ⊤ := ne_top_of_le_ne_top one_ne_top (mul_le_one' landing_le_one hw)
  have h2b0 : ((2 : ℝ≥0) ^ subtreeHeight) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hL : (Fintype.card (Fin (2 ^ subtreeHeight)) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ subtreeHeight := by
    rw [Fintype.card_fin]; push_cast; rfl
  refine ⟨((2 : ℝ≥0) ^ subtreeHeight)⁻¹, (landing * w).toNNReal / (2 : ℝ≥0) ^ subtreeHeight, ?_, ?_, ?_⟩
  · rw [hL, ENNReal.coe_inv h2b0]
    push_cast
    exact ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (pow_ne_top ofNat_ne_top)
  · rw [hL, ENNReal.coe_div h2b0, ENNReal.coe_toNNReal hlw]
    push_cast
    exact ENNReal.mul_div_cancel (pow_ne_zero _ two_ne_zero) (pow_ne_top ofNat_ne_top)
  · rw [← NNReal.coe_le_coe]
    push_cast
    have hn' : (n : ℝ) ≤ N := by exact_mod_cast hn
    have hk' : (k : ℝ) ≤ q := by exact_mod_cast hk
    have h0 : 0 ≤ (landing * w).toReal := ENNReal.toReal_nonneg
    calc (n : ℝ) * ((2 : ℝ) ^ subtreeHeight)⁻¹ + (k : ℝ) * ((landing * w).toReal / 2 ^ subtreeHeight)
        ≤ (N : ℝ) * ((2 : ℝ) ^ subtreeHeight)⁻¹ + (q : ℝ) * ((landing * w).toReal / 2 ^ subtreeHeight) := by
          gcongr
      _ = (N : ℝ) / 2 ^ subtreeHeight + (q : ℝ) * (landing * w).toReal / 2 ^ subtreeHeight := by ring
      _ ≤ μ := hμ

theorem uniformIndex_fst :
    UniformIndex (Prod.fst : View → Fin (2 ^ subtreeHeight)) (Finset.univ : Finset View) := by
  intro g
  calc freshAvg (Finset.univ : Finset View) (fun u => g u.1)
      = freshAvg Finset.univ (fun l : Fin (2 ^ subtreeHeight) =>
          freshAvg (Finset.univ : Finset (FTree → FLeaf)) fun m => g ((l, m) : View).1) := freshAvg_prod _
    _ = freshAvg Finset.univ (fun l : Fin (2 ^ subtreeHeight) => g l) := by
        congr 1; funext l; exact freshAvg_const' (g l)
    _ = _ := by unfold freshAvg; rw [Finset.card_univ]

theorem hTermO_const_mulD {V : Type} (U : Finset V) (w lam : ℝ≥0∞) (N q : ℕ) (c : ℝ≥0∞)
    (f : Multiset V → ℝ≥0∞) :
    hTermO U w lam N q (fun X => c * f X) = c * hTermO U w lam N q f := by
  unfold hTermO
  rw [← creations_const_mul]
  congr 1
  funext J
  exact virtualOnce_const_mul c f N J 0

/-- **The H-term of a one-index count function.** -/
theorem hTermO_fst_le {H : ℕ → ℝ≥0∞} (hH : Good1 H) (I : Fin (2 ^ subtreeHeight)) (w : ℝ≥0∞) (hw : w ≤ 1)
    {n k N q : ℕ} (hn : n ≤ N) (hk : k ≤ q) (μ : ℝ≥0)
    (hμ : (N : ℝ) / 2 ^ subtreeHeight + (q : ℝ) * (landing * w).toReal / 2 ^ subtreeHeight ≤ μ) :
    hTermO (Finset.univ : Finset View) w landing n k (fun X => H (countAt X I)) ≤ poisMean μ H := by
  obtain ⟨α, γ, hα, hγ, hr⟩ := rate_ag w hw hn hk μ hμ
  have h := hTermO_le_poisIID_of_le (Prod.fst : View → Fin (2 ^ subtreeHeight)) Finset.univ uniformIndex_fst
    (countGood_single hH I) w landing hw landing_le_one α γ hα hγ n k μ hr
  rw [poisIID_single] at h
  exact h

/-- **The H-term of a mark-dominated function.** -/
theorem hTermO_dom_le {f : Multiset View → ℝ≥0∞} {H : ℕ → ℝ≥0∞} (hH : Good1 H) (I : Fin (2 ^ subtreeHeight))
    (hd : Dominated f (fun e : Multiset (Fin (2 ^ subtreeHeight)) => H (e.count I))) (w : ℝ≥0∞) (hw : w ≤ 1)
    {n k N q : ℕ} (hn : n ≤ N) (hk : k ≤ q) (μ : ℝ≥0)
    (hμ : (N : ℝ) / 2 ^ subtreeHeight + (q : ℝ) * (landing * w).toReal / 2 ^ subtreeHeight ≤ μ) :
    hTermO (Finset.univ : Finset View) w landing n k f ≤ poisMean μ H := by
  obtain ⟨α, γ, hα, hγ, hr⟩ := rate_ag w hw hn hk μ hμ
  refine le_trans (hTermO_le_of_dominated w landing n k hd) ?_
  have h := hTermO_le_poisIID_of_le (id : Fin (2 ^ subtreeHeight) → Fin (2 ^ subtreeHeight)) Finset.univ
    uniformIndex_id (countGood_single hH I) w landing hw landing_le_one α γ hα hγ n k μ hr
  rw [poisIID_single] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  funext e
  rw [cnt_id]

/-! ### The cover indicator -/

/-- The trees whose leaf `ℓ` is disclosed at index `I` by a view of `e`. -/
noncomputable def covT (I : Fin (2 ^ subtreeHeight)) (ℓ : FTree → FLeaf) (e : Multiset View) : Finset FTree :=
  Finset.univ.filter fun κ' => ∃ x ∈ e, x.1 = I ∧ x.2 κ' = ℓ κ'

/-- The indicator that every tree of `T` is covered. -/
noncomputable def covI (I : Fin (2 ^ subtreeHeight)) (ℓ : FTree → FLeaf) (T : Finset FTree)
    (e : Multiset View) : ℝ≥0∞ :=
  if T ⊆ covT I ℓ e then 1 else 0

variable (I : Fin (2 ^ subtreeHeight)) (ℓ : FTree → FLeaf)

theorem mem_covT {e : Multiset View} {κ' : FTree} :
    κ' ∈ covT I ℓ e ↔ ∃ x ∈ e, x.1 = I ∧ x.2 κ' = ℓ κ' := by
  unfold covT; simp

theorem covT_mono {e e' : Multiset View} (h : e ≤ e') : covT I ℓ e ⊆ covT I ℓ e' := by
  intro κ' hκ
  obtain ⟨x, hx, h1, h2⟩ := (mem_covT I ℓ).1 hκ
  exact (mem_covT I ℓ).2 ⟨x, Multiset.mem_of_le h hx, h1, h2⟩

theorem covI_mono (T : Finset FTree) : Monotone' (covI I ℓ T) := by
  intro e e' h
  unfold covI
  by_cases hT : T ⊆ covT I ℓ e
  · rw [if_pos hT, if_pos (hT.trans (covT_mono I ℓ h))]
  · rw [if_neg hT]; exact zero_le

theorem covI_le_one (T : Finset FTree) (e : Multiset View) : covI I ℓ T e ≤ 1 := by
  unfold covI; split_ifs <;> simp

theorem covI_empty (e : Multiset View) : covI I ℓ ∅ e = 1 := by
  unfold covI; rw [if_pos (Finset.empty_subset _)]

theorem covT_add_single (e : Multiset View) (x : View) :
    covT I ℓ (e + {x}) = covT I ℓ e ∪ Finset.univ.filter (fun κ' => x.1 = I ∧ x.2 κ' = ℓ κ') := by
  ext κ'
  simp only [Finset.mem_union, mem_covT, Finset.mem_filter, Finset.mem_univ, true_and, Multiset.mem_add,
    Multiset.mem_singleton]
  constructor
  · rintro ⟨y, hy | rfl, h1, h2⟩
    · exact Or.inl ⟨y, hy, h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  · rintro (⟨y, hy, h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨y, Or.inl hy, h1, h2⟩
    · exact ⟨x, Or.inr rfl, h1, h2⟩

theorem covI_add_single (T : Finset FTree) (e : Multiset View) (x : View) :
    covI I ℓ T (e + {x}) = covI I ℓ (T.filter fun κ' => ¬(x.1 = I ∧ x.2 κ' = ℓ κ')) e := by
  unfold covI
  rw [covT_add_single]
  congr 1
  apply propext
  constructor
  · intro h κ' hκ
    have hκT := (Finset.mem_filter.1 hκ).1
    rcases Finset.mem_union.1 (h hκT) with h1 | h1
    · exact h1
    · exact absurd (Finset.mem_filter.1 h1).2 (Finset.mem_filter.1 hκ).2
  · intro h κ' hκ
    by_cases hx : x.1 = I ∧ x.2 κ' = ℓ κ'
    · exact Finset.mem_union.2 (Or.inr (Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩))
    · exact Finset.mem_union.2 (Or.inl (h (Finset.mem_filter.2 ⟨hκ, hx⟩)))

theorem covT_zero : covT I ℓ 0 = ∅ := by
  ext κ'; simp [mem_covT]

theorem card_fleafE' : ((Fintype.card FLeaf : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ forsHeight := by
  rw [Fintype.card_fin]; push_cast; rfl

/-- One more view at the index raises the cover bound by `1 / 2^a` per tree. -/
theorem avg_cover_step (T : Finset FTree) (β : ℝ≥0∞) :
    freshAvg (Finset.univ : Finset (FTree → FLeaf))
        (fun m => β ^ (T.filter fun κ' => ¬(m κ' = ℓ κ')).card) ≤
      (β + ((2 : ℝ≥0∞) ^ forsHeight)⁻¹) ^ T.card := by
  set G : FTree → FLeaf → ℝ≥0∞ := fun κ' x => if κ' ∈ T ∧ ¬x = ℓ κ' then β else 1 with hG
  have hprod : (fun m : FTree → FLeaf => β ^ (T.filter fun κ' => ¬(m κ' = ℓ κ')).card) =
      fun m => ∏ κ', G κ' (m κ') := by
    funext m
    rw [← Finset.prod_const, Finset.prod_filter]
    have e : ∀ κ', G κ' (m κ') = if κ' ∈ T then (if ¬(m κ' = ℓ κ') then β else 1) else 1 := by
      intro κ'
      by_cases hκ : κ' ∈ T <;> by_cases hx : m κ' = ℓ κ' <;> simp [hG, hκ, hx]
    simp only [e]
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [hprod, freshAvg_pi_prod G]
  calc ∏ κ', freshAvg (Finset.univ : Finset FLeaf) (G κ')
      ≤ ∏ κ', (if κ' ∈ T then β + ((2 : ℝ≥0∞) ^ forsHeight)⁻¹ else 1) := by
        refine Finset.prod_le_prod' fun κ' _ => ?_
        by_cases hκ : κ' ∈ T
        · rw [if_pos hκ]
          calc freshAvg (Finset.univ : Finset FLeaf) (fun x => if κ' ∈ T ∧ ¬x = ℓ κ' then β else 1)
              ≤ freshAvg (Finset.univ : Finset FLeaf) (fun x => β + if x = ℓ κ' then 1 else 0) :=
                freshAvg_mono _ fun x _ => by
                  by_cases hx : x = ℓ κ'
                  · simp [hκ, hx]
                  · simp [hκ, hx]
            _ = β + ((2 : ℝ≥0∞) ^ forsHeight)⁻¹ := by
                rw [freshAvg_add, freshAvg_const', freshAvg_indicator_eq, card_fleafE']
        · rw [if_neg hκ]
          simp [hG, hκ, freshAvg_const']
    _ = _ := by
        rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

theorem covI_avgL : ∀ (L : List (Fin (2 ^ subtreeHeight))) (T : Finset FTree),
    avgL (covI I ℓ T) L 0 ≤ (((L.count I : ℕ) : ℝ≥0∞) / 2 ^ forsHeight) ^ T.card
  | [], T => by
      simp only [avgL, List.count_nil, Nat.cast_zero, ENNReal.zero_div]
      unfold covI
      rw [covT_zero]
      by_cases hT : T = ∅
      · subst hT; simp
      · rw [if_neg (fun h => hT (Finset.subset_empty.1 h))]; exact zero_le
  | l :: L, T => by
      simp only [avgL]
      have hs : ∀ m : FTree → FLeaf, avgL (covI I ℓ T) L (0 + {(l, m)}) =
          avgL (covI I ℓ (T.filter fun κ' => ¬(((l, m) : View).1 = I ∧ ((l, m) : View).2 κ' = ℓ κ'))) L 0 := by
        intro m
        rw [← avgL_shift]
        congr 1
        funext e
        exact covI_add_single I ℓ T e (l, m)
      simp only [hs]
      by_cases hl : l = I
      · have hf : ∀ m : FTree → FLeaf,
            (T.filter fun κ' => ¬(((l, m) : View).1 = I ∧ ((l, m) : View).2 κ' = ℓ κ')) =
              T.filter fun κ' => ¬(m κ' = ℓ κ') := fun m =>
          Finset.filter_congr (fun κ' _ => ⟨fun h h' => h ⟨hl, h'⟩, fun h h' => h h'.2⟩)
        simp only [hf]
        have hc : (l :: L).count I = L.count I + 1 := by rw [hl, List.count_cons_self]
        rw [hc]
        refine le_trans (freshAvg_mono _ fun m _ => covI_avgL L _) ?_
        refine le_trans (avg_cover_step ℓ T _) (le_of_eq ?_)
        congr 1
        rw [Nat.cast_succ, ENNReal.add_div, one_div]
      · rw [List.count_cons_of_ne hl]
        have hT : ∀ m : FTree → FLeaf,
            (T.filter fun κ' => ¬(((l, m) : View).1 = I ∧ ((l, m) : View).2 κ' = ℓ κ')) = T := fun m =>
          Finset.filter_true_of_mem fun κ' _ h => hl h.1
        simp only [hT]
        rw [freshAvg_const']
        exact covI_avgL L T

/-- **The cover indicator is mark-dominated** by `(n_I / 2^a)^|T|`. -/
theorem covI_dominated (T : Finset FTree) :
    Dominated (covI I ℓ T) (fun e : Multiset (Fin (2 ^ subtreeHeight)) =>
      (((e.count I : ℕ) : ℝ≥0∞) / 2 ^ forsHeight) ^ T.card) := fun L => by
  have h := covI_avgL I ℓ L T
  show _ ≤ (((Multiset.count I (L : Multiset (Fin (2 ^ subtreeHeight))) : ℕ) : ℝ≥0∞) / 2 ^ forsHeight) ^ T.card
  rw [Multiset.coe_count]
  exact h

theorem good1_phi (t : ℕ) : Good1 (fun j : ℕ => ((j : ℝ≥0∞) / 2 ^ forsHeight) ^ t) := by
  have e : (fun j : ℕ => ((j : ℝ≥0∞) / 2 ^ forsHeight) ^ t) =
      fun j : ℕ => ((2 : ℝ≥0∞) ^ forsHeight)⁻¹ ^ t * (j : ℝ≥0∞) ^ t := by
    funext j
    rw [div_eq_mul_inv, mul_pow, mul_comm]
  rw [e]
  exact (good1_pow t).const_mul
    (pow_ne_top (ENNReal.inv_ne_top.2 (pow_ne_zero _ two_ne_zero)))

/-- **The future covers `T` with mean at most `φ(|T|)`.** -/
theorem hTermO_covI_le (T : Finset FTree) (w : ℝ≥0∞) (hw : w ≤ 1) {n k N q : ℕ} (hn : n ≤ N) (hk : k ≤ q)
    (μ : ℝ≥0)
    (hμ : (N : ℝ) / 2 ^ subtreeHeight + (q : ℝ) * (landing * w).toReal / 2 ^ subtreeHeight ≤ μ) :
    hTermO (Finset.univ : Finset View) w landing n k (covI I ℓ T) ≤
      ENNReal.ofReal (phiK forsHeight (μ : ℝ) T.card) := by
  rw [← poisMean_phi]
  exact hTermO_dom_le (good1_phi T.card) I (covI_dominated I ℓ T) w hw hn hk μ hμ

/-! ### One-index Poisson means -/

/-- A function of one count as a count function over `Unit`. -/
def liftU (G : ℕ → ℝ≥0∞) : (Unit → ℕ) → ℝ≥0∞ := fun k => G (k ())

theorem pois_liftU (a : ℝ≥0) (G : ℕ → ℝ≥0∞) (k : Unit → ℕ) : pois a () (liftU G) k = pois1 a G (k ()) := by
  unfold pois pois1 liftU
  simp

theorem pois_liftU_fun (a : ℝ≥0) (G : ℕ → ℝ≥0∞) : pois a () (liftU G) = liftU (pois1 a G) := by
  funext k
  rw [pois_liftU]
  rfl

theorem pois1_pois1 (a b : ℝ≥0) (G : ℕ → ℝ≥0∞) (x : ℕ) : pois1 a (pois1 b G) x = pois1 (a + b) G x := by
  have h := pois_pois a b () (liftU G) (fun _ => x)
  rw [pois_liftU_fun, pois_liftU, pois_liftU] at h
  exact h

theorem Good1.pois1 {G : ℕ → ℝ≥0∞} (hG : Good1 G) (a : ℝ≥0) : Good1 (pois1 a G) where
  mono := fun x y hxy => ENNReal.tsum_le_tsum fun n =>
    mul_le_mul_right (hG.mono (Nat.add_le_add_right hxy n)) _
  convex := fun x => by
    unfold FORS.Base.H0.pois1
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun n => ?_
    rw [← mul_add, ← mul_add]
    refine mul_le_mul_right ?_ _
    have := hG.convex (x + n)
    rw [show x + 1 + n = x + n + 1 by omega, show x + 2 + n = x + n + 2 by omega]
    exact this
  growth := by
    have hc := (countGood_single hG ()).pois a ()
    obtain ⟨C, r, h⟩ := hc.growth
    refine ⟨C, r, fun n => ?_⟩
    have h2 := pois_liftU a G (fun _ => n)
    unfold liftU at h2
    have := h (fun _ => n)
    rw [h2] at this
    simpa using this

theorem chord1 {G : ℕ → ℝ≥0∞} (hG : Good1 G) (a : ℝ≥0) (x : ℕ) :
    G x + (a : ℝ≥0∞) * G (x + 1) ≤ pois1 a G x + (a : ℝ≥0∞) * G x := by
  have h := good_chord (countGood_single hG ()) a () (fun _ => x)
  have e : ((fun _ => x) + Pi.single () 1 : Unit → ℕ) () = x + 1 := by simp
  simp only [e] at h
  have h2 := pois_liftU a G (fun _ => x)
  unfold liftU at h2
  rw [h2] at h
  exact h

/-- A Bernoulli count is below a Poisson count of the same mean. -/
theorem bern_le_pois1 {G : ℕ → ℝ≥0∞} (hG : Good1 G) (a : ℝ≥0) (ha : a ≤ 1) (x : ℕ) :
    (1 - (a : ℝ≥0∞)) * G x + (a : ℝ≥0∞) * G (x + 1) ≤ pois1 a G x := by
  have h := chord1 hG a x
  have hfin : (a : ℝ≥0∞) * G x ≠ ⊤ := mul_ne_top coe_ne_top (hG.ne_top x)
  refine (ENNReal.add_le_add_iff_right hfin).1 ?_
  have ha' : (a : ℝ≥0∞) ≤ 1 := by exact_mod_cast ha
  calc (1 - (a : ℝ≥0∞)) * G x + (a : ℝ≥0∞) * G (x + 1) + (a : ℝ≥0∞) * G x
      = ((1 - (a : ℝ≥0∞)) + a) * G x + (a : ℝ≥0∞) * G (x + 1) := by ring
    _ = G x + (a : ℝ≥0∞) * G (x + 1) := by rw [tsub_add_cancel_of_le ha', one_mul]
    _ ≤ _ := h

theorem le_pois1 {G : ℕ → ℝ≥0∞} (hG : Monotone G) (a : ℝ≥0) (x : ℕ) : G x ≤ pois1 a G x := by
  calc G x = ∑' n, poisW a n * G x := by rw [ENNReal.tsum_mul_right, poisW_tsum, one_mul]
    _ ≤ _ := ENNReal.tsum_le_tsum fun n => mul_le_mul_right (hG (Nat.le_add_right x n)) _

theorem pois1_mono_rate {G : ℕ → ℝ≥0∞} (hG : Good1 G) {a b : ℝ≥0} (hab : a ≤ b) (x : ℕ) :
    pois1 a G x ≤ pois1 b G x := by
  obtain ⟨c, rfl⟩ := le_iff_exists_add.1 hab
  rw [← pois1_pois1]
  exact ENNReal.tsum_le_tsum fun n => mul_le_mul_right (le_pois1 hG.mono c _) _

theorem pois1_zero_eq (a : ℝ≥0) (G : ℕ → ℝ≥0∞) : pois1 a G 0 = poisMean a G := pois1_zero a G

end FORS.Security.SWRoute
