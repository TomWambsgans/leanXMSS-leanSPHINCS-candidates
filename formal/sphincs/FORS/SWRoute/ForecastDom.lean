import FORS.SWRoute.ForecastDomG

/-! **The excess payment is paid by the tail potential** (`excPay_le_psi`, WP-F-A).

At an ordinary query `x` whose FORS leaf contact would survive (cell `c = (I, κ, L)`, `Q` the
views disclosed at `I`, `D = |Q|`), the excess payment `weight · (min(1, PiC) - m)⁺` is at most
`(1 - m)⁺ · psi`:

* if `psi ≥ 1` the excess is at most `(1 - m)⁺`;
* otherwise no failure happened: fewer than `n0` views are disclosed at `I` (else `psiL ≥ 1`), no
  pattern is selected by more unsigned cached pairs than its cap (else `psiP ≥ 1`), and the sum `X`
  of the pair weights `φ(r)` of the unsigned cached pairs at `c` is at most `t_D` (else the cell
  term `(c, D, Q)` of `psiC` is at least `e^{θ (X - t_D)} ≥ 1`). Then the **domination**
  `PiC ≤ X + fresh_D + coinSlack ≤ m` holds (`PiC_le_m`): every unsigned cached pair at `c` misses
  `r ≥ 1` trees (a near cell otherwise, `missing_pos`) and contributes at most `φ(r) + coinR(r)`
  (`candValueG_le`), the coin-assisted parts add at most `coinSlack / 2` (`CoinCond`), and the
  fresh part is at most `freshK` at the rate `μ + δ`, at most `fresh_D + coinSlack / 2`. -/

open OracleComp OracleSpec ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base FORS.Base.Domination FORS.Base.H0 FORS.Security.H0Avg ForsPrice Concrete GraphView
  ForsPotential FORS.LoopWalk HiddenGraph PotentialA

set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-! ### Small facts -/

theorem termO_zero_fun (parameter : PublicParameter) (data : PublicData) {w : ℝ≥0∞} (hw : w ≤ 1) (s : State)
    (Ms : List Message) (L : QueryLog SigningSpec) (excl : Pair → Prop) (d : Multiset View) (n k : ℕ) :
    termO parameter data w s Ms L excl (fun _ => 0) d n k = 0 := by
  have h : termBase parameter data w s Ms L excl (fun _ => 0) d n = fun _ => 0 := by
    funext J
    unfold termBase
    rw [show virtualOnce Finset.univ w (fun _ : Multiset View => (0 : ℝ≥0∞)) n J = fun _ => 0 from
      funext fun e => virtualOnce_const Finset.univ_nonempty hw 0 n J e]
    exact grpAll_const s excl 0 _ d
  unfold termO
  rw [h, creations_zero_fun]

theorem discAt_card_le (d : Multiset View) (I : Fin (2 ^ subtreeHeight)) : (discAt d I).card ≤ countAt d I := by
  unfold discAt countAt
  rw [← Multiset.toFinset_filter]
  exact Multiset.toFinset_card_le _

theorem missT_card_eq (I : Fin (2 ^ subtreeHeight)) (κ : FTree) (L0 : FLeaf) (d : Multiset View) (u : View) :
    (missT I u.2 κ d).card = missing (I, κ, L0) (discAt d I) u := by
  unfold missT missing
  congr 1
  refine Finset.filter_congr fun κ' _ => ?_
  rw [mem_covT, show (I, κ, L0).1 = I from rfl, mem_leavesAt_discAt]

theorem freshSum_mono_D (μ : ℝ≥0) {D D' : ℕ} (h : D ≤ D') : freshSum (μ : ℝ) D ≤ freshSum (μ : ℝ) D' := by
  unfold freshSum
  rw [lsum_range, lsum_range]
  refine Finset.sum_le_sum fun i _ => ?_
  have := chooseK_nonneg' (forsTrees - 1) i
  have := touchard_nonneg' μ i
  have hD : (D : ℝ) ^ (forsTrees - 1 - i) ≤ (D' : ℝ) ^ (forsTrees - 1 - i) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast h) _
  gcongr

theorem freshK_mono_D (μ : ℝ≥0) (q : ℕ) {D D' : ℕ} (h : D ≤ D') :
    freshK subtreeHeight forsTrees forsHeight (μ : ℝ) q D ≤ freshK subtreeHeight forsTrees forsHeight (μ : ℝ) q D' := by
  rw [freshK_eq, freshK_eq]
  have := freshSum_mono_D μ h
  gcongr

theorem freshK_nonneg (μ : ℝ≥0) (q D : ℕ) : 0 ≤ freshK subtreeHeight forsTrees forsHeight (μ : ℝ) q D := by
  rw [freshK_eq]
  have := freshSum_nonneg μ D
  positivity

theorem coinSlack_pos : 0 < coinSlack := by unfold coinSlack; positivity

theorem wQφ_nonnegD (c : FCell) (Q : Finset View) {φ : ℕ → ℝ} (hφ : ∀ r, 0 ≤ φ r) (u : View) : 0 ≤ wQφ c Q φ u := by
  unfold wQφ; split_ifs <;> simp [hφ]

/-! ### The potential at a failure -/

section Lower

variable (K : Ctx) (data : PublicData) (wbar : ℝ≥0∞) (tp : TailPar)

theorem one_le_psi_light (hw : wbar ≤ 1) (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (k : ℕ) (I : Fin (2 ^ subtreeHeight)) (hn0 : 1 ≤ tp.n0) (h : tp.n0 ≤ countAt d I) :
    1 ≤ psi K.p data wbar tp s P Ms L d k := by
  have h1 : 1 ≤ lightFail (tp.n0 - 1) d := one_le_lightFail (l := I) (by omega)
  have h2 : lightFail (tp.n0 - 1) d ≤ psiL K.p data wbar tp s Ms L d k :=
    base_le_termO hw (lightFail_props _) s Ms L _ d _ k
  unfold psi
  exact le_trans (le_trans h1 h2) (le_trans le_self_add le_self_add)

theorem one_le_psi_pat (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (k : ℕ) (I : Fin (2 ^ subtreeHeight)) (S : Pat) (hS : 1 ≤ patSize S)
    (hgt : patCap tp.q (patSize S) < ((P.filter fun p => decide (Unsigned L p)).filter
      fun p => decide (PatCovers I S (pview K.p data s p))).length) :
    1 ≤ psi K.p data wbar tp s P Ms L d k := by
  set cnt := ((P.filter fun p => decide (Unsigned L p)).filter
      fun p => decide (PatCovers I S (pview K.p data s p))).length with hcnt
  have hprod : prodU L P (fun p => if PatCovers I S (pview K.p data s p) then 2 else 1) = 2 ^ cnt := by
    unfold prodU
    rw [hcnt]
    convert list_prod_two (P.filter fun p => decide (Unsigned L p)) (fun p => PatCovers I S (pview K.p data s p))
      using 3
  have hterm : 1 ≤ (2 : ℝ≥0∞)⁻¹ ^ patCap tp.q (patSize S) *
      prodU L P (fun p => if PatCovers I S (pview K.p data s p) then 2 else 1) *
      (1 + ((2 : ℝ≥0∞) ^ (subtreeHeight + forsHeight * patSize S))⁻¹) ^ k := by
    rw [hprod]
    have h1 : 1 ≤ (2 : ℝ≥0∞)⁻¹ ^ patCap tp.q (patSize S) * 2 ^ cnt := by
      obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hgt.le
      rw [he, pow_add, ← mul_assoc, ← ENNReal.inv_pow,
        ENNReal.inv_mul_cancel (pow_ne_zero _ two_ne_zero) (pow_ne_top ofNat_ne_top), one_mul]
      exact one_le_pow₀ (by norm_num)
    exact le_trans h1 (le_mul_of_one_le_right' (one_le_pow₀ le_self_add))
  unfold psi psiP
  refine le_trans ?_ le_add_self
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ I))
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (a := S) ?_)
  · exact hterm
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hS

theorem inDisc_monoFin (Q : Finset View) : MonoFin (inDisc Q) := by
  refine ⟨fun a b hab => ?_, fun D => ?_⟩
  · unfold inDisc
    by_cases h : Q ⊆ a.toFinset
    · rw [if_pos h, if_pos (h.trans (Multiset.toFinset_subset.2 (Multiset.subset_of_le hab)))]
    · rw [if_neg h]; exact zero_le
  · unfold inDisc; split_ifs <;> simp

theorem one_le_psi_cell (hw : wbar ≤ 1) (hθ : ∀ D, 0 ≤ tp.θ D) (s : State) (P : List Pair) (Ms : List Message)
    (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ) (c : FCell) (D : ℕ) (hD : D < tp.n0)
    (Q : Finset View) (hQ : Q ∈ subsetsAt c.1 D) (hQd : Q ⊆ d.toFinset)
    (hX : tp.thr D < ((P.filter fun p => decide (Unsigned L p)).map
      fun p => wQφ c Q tp.φ (pview K.p data s p)).sum) :
    1 ≤ psi K.p data wbar tp s P Ms L d k := by
  set X := ((P.filter fun p => decide (Unsigned L p)).map fun p => wQφ c Q tp.φ (pview K.p data s p)).sum
  have hprod : prodU L P (fun p => pairFφ c Q (tp.θ D) tp.φ (pview K.p data s p)) =
      ENNReal.ofReal (Real.exp (tp.θ D * X)) := by
    unfold prodU
    convert list_prod_pairF c Q (tp.θ D) tp.φ (P.filter fun p => decide (Unsigned L p)) (pview K.p data s) using 4
  have hφ : ∀ j, 0 ≤ tp.φ j := fun j => phiK_nonneg forsHeight (NNReal.coe_nonneg _) j
  have hΓ : 1 ≤ ENNReal.ofReal (gammaR subtreeHeight forsTrees forsHeight (tp.θ D) tp.φ D) ^ k := by
    refine one_le_pow₀ ?_
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (gammaR_one_le _ _ _ (hθ D) hφ D)
  have hdisc : 1 ≤ termO K.p data wbar s Ms L (fun _ => False) (inDisc Q) d (signatureLimit - L.length) k := by
    refine le_trans (le_of_eq ?_) (base_le_termO hw (inDisc_monoFin Q) s Ms L _ d _ k)
    unfold inDisc; rw [if_pos hQd]
  have hexp : 1 ≤ ENNReal.ofReal (Real.exp (-(tp.θ D * tp.thr D))) * ENNReal.ofReal (Real.exp (tp.θ D * X)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    refine Real.one_le_exp ?_
    have := hθ D
    nlinarith
  have hterm : 1 ≤ ENNReal.ofReal (Real.exp (-(tp.θ D * tp.thr D))) *
      prodU L P (fun p => pairFφ c Q (tp.θ D) tp.φ (pview K.p data s p)) *
      ENNReal.ofReal (gammaR subtreeHeight forsTrees forsHeight (tp.θ D) tp.φ D) ^ k *
      termO K.p data wbar s Ms L (fun _ => False) (inDisc Q) d (signatureLimit - L.length) k := by
    rw [hprod]
    calc (1 : ℝ≥0∞) = 1 * 1 * 1 := by simp
      _ ≤ _ := by gcongr
  unfold psi psiC
  refine le_trans ?_ (le_trans le_add_self le_self_add)
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ c))
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_range.2 hD))
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => zero_le) hQ)
  exact hterm

end Lower

/-! ### The domination -/

section Dom

variable (K : Ctx) (root : Digest) (data : PublicData) (wbar : ℝ≥0∞) (tp : TailPar)

theorem coinR_nonneg (q : ℕ) (μ : ℝ≥0) (r : ℕ) : 0 ≤ coinR subtreeHeight forsHeight capFloor q (μ : ℝ) r := by
  unfold coinR
  rw [lsum_range]
  refine Finset.sum_nonneg fun j _ => ?_
  split_ifs
  · have := chooseK_nonneg' r j
    have := coinV_nonneg subtreeHeight forsHeight capFloor q j
    have := phiK_nonneg forsHeight (NNReal.coe_nonneg μ) (r - j)
    positivity
  · exact le_rfl

theorem PiC_eq (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View)
    (k : ℕ) (hL : L.length ≤ signatureLimit) (c : Index × FTree × FLeaf) :
    PiC K data wbar ∅ c s P Ms L d k =
      ((P.filter fun p => decide (Unsigned L p)).map
          fun p => candValueG K.p data (ownW c) wbar s Ms L d (signatureLimit - L.length) k p).sum +
        k * hValueG K.p data (ownW c) wbar 0 s Ms L d (signatureLimit - L.length) k := by
  unfold PiC potG
  rw [if_neg (by simp only [false_or, not_lt]; exact hL)]
  unfold coreG
  have hf : failMass (∅ : Finset (Fin (2 ^ subtreeHeight))) = 0 := by
    unfold failMass
    simp only [Finset.notMem_empty, if_false]
    unfold freshAvg
    simp
  rw [hf, add_zero, mul_zero, add_zero, ← list_sum_ite_filter]
  congr 1

/-- **The domination**: with no failure, the near forecast at a surviving cell is at most `m`. -/
theorem PiC_le_m (hH : totalHeight = subtreeHeight) (hw : wbar ≤ 1) (s : State) (P : List Pair)
    (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ)
    (hP : PInv K.p data s P) (hM : MInv K.p data s Ms) (hL : L.length ≤ signatureLimit) (hk : k ≤ tp.q)
    (hrate : (signatureLimit : ℝ) / 2 ^ subtreeHeight +
      (tp.q : ℝ) * (landing * wbar).toReal / 2 ^ subtreeHeight ≤ tp.μ)
    (hcoin : CoinCond subtreeHeight forsTrees forsHeight capFloor tp.q (tp.μ : ℝ) tp.n0)
    (hknown : KnownInv s d) (f : FIn) (hsurv : SurvivesAt K root s f) (hok : PatOK K.p data s tp.q L P)
    (hD : (discAt d (localIdx f.index)).card < tp.n0) (hm1 : tp.m < 1)
    (hX : ((P.filter fun p => decide (Unsigned L p)).map
      fun p => wQφ (cellOfF f) (discAt d (localIdx f.index)) tp.φ (pview K.p data s p)).sum ≤
        tp.thr (discAt d (localIdx f.index)).card) :
    PiC K data wbar ∅ (CellOf f) s P Ms L d k ≤ ENNReal.ofReal tp.m := by
  set I := localIdx f.index with hI
  set c' := cellOfF f with hc'
  set Q := discAt d I with hQ
  set D := Q.card with hDdef
  set LU := P.filter fun p => decide (Unsigned L p) with hLU
  have hφ0 : ∀ r, 0 ≤ tp.φ r := fun r => phiK_nonneg forsHeight (NNReal.coe_nonneg _) r
  set w : Pair → ℝ := fun p => wQφ c' Q tp.φ (pview K.p data s p) with hwdef
  set cr : Pair → ℝ := fun p => if Opens c' (pview K.p data s p) then
    coinR subtreeHeight forsHeight capFloor tp.q (tp.μ : ℝ) (missing c' Q (pview K.p data s p)) else 0 with hcrdef
  set X := (LU.map w).sum with hXdef
  have hw0 : ∀ p, 0 ≤ w p := fun p => wQφ_nonnegD c' Q hφ0 _
  have hcr0 : ∀ p, 0 ≤ cr p := fun p => by
    simp only [hcrdef]; split_ifs
    · exact coinR_nonneg tp.q tp.μ _
    · exact le_rfl
  -- one cached pair
  have hB : ∀ p ∈ LU, candValueG K.p data (ownW (CellOf f)) wbar s Ms L d (signatureLimit - L.length) k p ≤
      ENNReal.ofReal (w p + cr p) := by
    intro p hp
    have hpP : p ∈ P := (List.mem_filter.1 hp).1
    by_cases hop : Opens c' (pview K.p data s p)
    · have hr : 1 ≤ missing c' Q (pview K.p data s p) := missing_pos K root data hH hP hknown hsurv hpP hop
      have hnotQ : pview K.p data s p ∉ Q := fun h => by
        have h0 : missing c' Q (pview K.p data s p) = 0 := missing_zero_of_mem h
        omega
      have hw_eq : w p = tp.φ (missing c' Q (pview K.p data s p)) := by
        simp only [hwdef]; unfold wQφ; rw [if_pos ⟨hop, hnotQ, hr⟩]
      have hcr_eq : cr p = coinR subtreeHeight forsHeight capFloor tp.q (tp.μ : ℝ)
          (missing c' Q (pview K.p data s p)) := by
        simp only [hcrdef]; rw [if_pos hop]
      rw [hw_eq, hcr_eq]
      have h := candValueG_le K.p data wbar hH tp.q hw s Ms hM.nodup L d (Nat.sub_le signatureLimit L.length) hk tp.μ hrate
        (CellOf f) p (fun B hB => matchSet_card_le K.p data s hP hok Ms (· = p) _ _ B hB)
      have e := missT_card_eq I f.κ f.leaf d (pview K.p data s p)
      simp only [CellOf] at h
      rw [e] at h
      exact h
    · have hzero : ownW (CellOf f) (pview K.p data s p) = fun _ => 0 := by
        funext D'
        unfold ownW
        rw [if_neg]
        rintro ⟨h1, h2, _⟩
        exact hop ⟨h1, h2⟩
      unfold candValueG
      rw [hzero, termO_zero_fun K.p data hw]
      exact zero_le
  -- the fresh part
  have hrK : coinRateK subtreeHeight forsHeight capFloor tp.q =
      (2 : ℝ) ^ forsHeight * (patCapN subtreeHeight forsHeight capFloor tp.q 1 : ℝ) / 2 ^ 128 := rfl
  have hrK0 : (0 : ℝ) ≤ coinRateK subtreeHeight forsHeight capFloor tp.q := by rw [hrK]; positivity
  set δ : ℝ≥0 := ⟨coinRateK subtreeHeight forsHeight capFloor tp.q, hrK0⟩ with hδdef
  have hδ : ((hitsAt K.p data s (fun _ => False) (localIdx (CellOf f).1) (live L Ms)).card : ℝ≥0) / 2 ^ 128 ≤ δ := by
    have h : (hitsAt K.p data s (fun _ => False) (localIdx (CellOf f).1) (live L Ms)).card ≤
        2 ^ forsHeight * patCapN subtreeHeight forsHeight capFloor tp.q 1 :=
      hitsAt_card_le K.p data s hP hok Ms (fun _ => False) _ f.κ
    rw [← NNReal.coe_le_coe, hδdef]
    show ((((hitsAt K.p data s (fun _ => False) (localIdx (CellOf f).1) (live L Ms)).card : ℝ≥0) / 2 ^ 128 :
      ℝ≥0) : ℝ) ≤ coinRateK subtreeHeight forsHeight capFloor tp.q
    rw [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_ofNat, hrK]
    gcongr
    exact_mod_cast h
  have hfr := khValueG_le K.p data wbar hH hw s Ms hM.nodup L d (Nat.sub_le signatureLimit L.length) hk tp.μ δ hrate (CellOf f) hδ
  -- the real inequality
  have hμpos : (0 : ℝ) < tp.μ := hcoin.2.2
  have hcap1 : (1 : ℝ) ≤ (patCapN subtreeHeight forsHeight capFloor tp.q 1 : ℝ) := by
    have : 1 ≤ patCapN subtreeHeight forsHeight capFloor tp.q 1 := by
      unfold patCapN; exact le_trans (Nat.le_add_left 1 _) (le_max_left _ _)
    exact_mod_cast this
  set cap1 : ℝ := (patCapN subtreeHeight forsHeight capFloor tp.q 1 : ℝ) with hcap1def
  have hfresh0 := freshK_nonneg tp.μ tp.q D
  have hslack := coinSlack_pos
  have hthr : tp.thr D = tp.m - freshK subtreeHeight forsTrees forsHeight (tp.μ : ℝ) tp.q D - coinSlack := rfl
  have hX1 : X ≤ 1 := by
    have : X ≤ tp.thr D := hX
    rw [hthr] at this
    linarith
  -- the number of pairs at the cell
  have hopens : ((LU.filter fun p => decide (Opens c' (pview K.p data s p))).length : ℝ) ≤ cap1 := by
    have h := hok I (patOf (fun _ => f.leaf) {f.κ}) (by rw [patSize_patOf, Finset.card_singleton])
    rw [patSize_patOf, Finset.card_singleton] at h
    have hfil : (LU.filter fun p => decide (Opens c' (pview K.p data s p))) =
        LU.filter fun p => decide (PatCovers I (patOf (fun _ => f.leaf) {f.κ}) (pview K.p data s p)) := by
      refine List.filter_congr fun p _ => ?_
      rw [decide_eq_decide]
      constructor
      · intro hop
        exact patCovers_patOf hop.1 fun κ' hκ' => by rw [Finset.mem_singleton.1 hκ']; exact hop.2
      · intro hpc
        refine ⟨hpc.1, hpc.2 f.κ f.leaf ?_⟩
        unfold patOf
        rw [if_pos (Finset.mem_singleton_self _)]
    rw [hfil, hcap1def]
    exact_mod_cast h
  -- the coin parts
  have hcr_le : ∀ p ∈ LU, cr p ≤ (if Opens c' (pview K.p data s p) then coinSlack / (4 * cap1) else 0) +
      coinSlack / 4 * w p := by
    intro p hp
    by_cases hop : Opens c' (pview K.p data s p)
    · have hr : 1 ≤ missing c' Q (pview K.p data s p) :=
        missing_pos K root data hH hP hknown hsurv (List.mem_filter.1 hp).1 hop
      have hnotQ : pview K.p data s p ∉ Q := fun h => by
        have h0 : missing c' Q (pview K.p data s p) = 0 := missing_zero_of_mem h
        omega
      have hrk := missing_lt c' Q (pview K.p data s p)
      have hc := hcoin.1 _ hr hrk
      simp only [hcrdef, hwdef, if_pos hop]
      unfold wQφ
      rw [if_pos ⟨hop, hnotQ, hr⟩]
      rw [← hcap1def] at hc
      have h4 : 0 < 4 * cap1 := by linarith
      rw [div_add' _ _ _ h4.ne', le_div_iff₀ h4]
      have : tp.φ = phiK forsHeight (tp.μ : ℝ) := rfl
      rw [this]
      nlinarith [hφ0 (missing c' Q (pview K.p data s p))]
    · simp only [hcrdef, if_neg hop, zero_add]
      have := hw0 p
      positivity
  have hcrsum : (LU.map cr).sum ≤ coinSlack / 2 := by
    calc (LU.map cr).sum
        ≤ (LU.map fun p => (if Opens c' (pview K.p data s p) then coinSlack / (4 * cap1) else 0) +
            coinSlack / 4 * w p).sum := List.sum_le_sum hcr_le
      _ = coinSlack / (4 * cap1) * ((LU.filter fun p => decide (Opens c' (pview K.p data s p))).length : ℝ) +
            coinSlack / 4 * X := by
          rw [List.sum_map_add, list_sum_const_filter, List.sum_map_mul_left]
      _ ≤ coinSlack / (4 * cap1) * cap1 + coinSlack / 4 * 1 := by
          have h1 : 0 ≤ coinSlack / (4 * cap1) := div_nonneg hslack.le (by linarith)
          have h2 : 0 ≤ coinSlack / 4 := div_nonneg hslack.le (by norm_num)
          exact add_le_add (mul_le_mul_of_nonneg_left hopens h1) (mul_le_mul_of_nonneg_left hX1 h2)
      _ = coinSlack / 2 := by
          have hc0 : cap1 ≠ 0 := by linarith
          rw [show coinSlack / (4 * cap1) * cap1 = coinSlack / 4 by field_simp]
          ring
  -- the fresh rate
  have hfresh : freshK subtreeHeight forsTrees forsHeight ((tp.μ + δ : ℝ≥0) : ℝ) tp.q D ≤
      freshK subtreeHeight forsTrees forsHeight (tp.μ : ℝ) tp.q D + coinSlack / 2 := by
    have hle : tp.μ ≤ tp.μ + δ := le_self_add
    have h1 := freshK_scale (q := tp.q) (D := D) (by exact_mod_cast hμpos : (0 : ℝ≥0) < tp.μ) hle
    have hc : ((tp.μ + δ : ℝ≥0) : ℝ) / tp.μ = 1 + coinRateK subtreeHeight forsHeight capFloor tp.q / (tp.μ : ℝ) := by
      have hδc : ((δ : ℝ≥0) : ℝ) = coinRateK subtreeHeight forsHeight capFloor tp.q := rfl
      rw [NNReal.coe_add, hδc, add_div, div_self hμpos.ne']
    rw [hc] at h1
    have h2 := hcoin.2.1
    have hpow : 1 ≤ (1 + coinRateK subtreeHeight forsHeight capFloor tp.q / (tp.μ : ℝ)) ^ (forsTrees - 1) := by
      refine one_le_pow₀ ?_
      have : 0 ≤ coinRateK subtreeHeight forsHeight capFloor tp.q / (tp.μ : ℝ) := div_nonneg hrK0 hμpos.le
      linarith
    have hmono := freshK_mono_D tp.μ tp.q (le_of_lt hD)
    set cc := (1 + coinRateK subtreeHeight forsHeight capFloor tp.q / (tp.μ : ℝ)) ^ (forsTrees - 1)
    have hprod := mul_nonneg (sub_nonneg.2 hpow)
      (by linarith : (0 : ℝ) ≤ 1 + freshK subtreeHeight forsTrees forsHeight (tp.μ : ℝ) tp.q tp.n0 -
        freshK subtreeHeight forsTrees forsHeight (tp.μ : ℝ) tp.q D)
    nlinarith
  -- assemble
  rw [PiC_eq K data wbar s P Ms L d k hL]
  have hsum0 : ∀ p ∈ LU, 0 ≤ w p + cr p := fun p _ => add_nonneg (hw0 p) (hcr0 p)
  calc (LU.map fun p => candValueG K.p data (ownW (CellOf f)) wbar s Ms L d (signatureLimit - L.length) k p).sum +
        (k : ℝ≥0∞) * hValueG K.p data (ownW (CellOf f)) wbar 0 s Ms L d (signatureLimit - L.length) k
      ≤ (LU.map fun p => ENNReal.ofReal (w p + cr p)).sum +
          ENNReal.ofReal (freshK subtreeHeight forsTrees forsHeight ((tp.μ + δ : ℝ≥0) : ℝ) tp.q D) :=
        add_le_add (List.sum_le_sum hB) hfr
    _ = ENNReal.ofReal ((LU.map fun p => w p + cr p).sum +
          freshK subtreeHeight forsTrees forsHeight ((tp.μ + δ : ℝ≥0) : ℝ) tp.q D) := by
        rw [list_sum_ofReal LU (fun p => w p + cr p) hsum0, ← ENNReal.ofReal_add
          (List.sum_nonneg fun y hy => by
            obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
            exact hsum0 p hp)
          (freshK_nonneg _ _ _)]
    _ ≤ ENNReal.ofReal tp.m := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [List.sum_map_add]
        have : X ≤ tp.thr D := hX
        rw [hthr] at this
        have hXeq : (LU.map w).sum = X := rfl
        linarith

/-- **The excess payment is paid by the tail potential.** -/
theorem excPay_le_psi (s : State) (P : List Pair) (Ms : List Message) (L : QueryLog SigningSpec)
    (d : Multiset View) (k : ℕ) (x : HashInput)
    (hH : totalHeight = subtreeHeight) (hw : wbar ≤ 1)
    (hP : PInv K.p data s P) (hM : MInv K.p data s Ms)
    (hL : L.length ≤ signatureLimit) (hk : k ≤ tp.q)
    (hθ : ∀ D, 0 ≤ tp.θ D) (hn0 : 1 ≤ tp.n0)
    (hrate : (signatureLimit : ℝ) / 2 ^ subtreeHeight +
      (tp.q : ℝ) * (landing * wbar).toReal / 2 ^ subtreeHeight ≤ tp.μ)
    (hcoin : CoinCond subtreeHeight forsTrees forsHeight capFloor tp.q (tp.μ : ℝ) tp.n0)
    (hknown : KnownInv s d) :
    excPay K root data wbar ∅ (ENNReal.ofReal tp.m) s P Ms L d k x ≤
      ENNReal.ofReal (1 - tp.m) * psi K.p data wbar tp s P Ms L d k := by
  unfold excPay
  split_ifs with hx
  · set f := Classical.choose hx with hf
    have hsurv : SurvivesAt K root s f := (Classical.choose_spec hx).2
    have hw1 : weightA K root s ≤ 1 := weightA_le_one K root s
    have hex : min 1 (PiC K data wbar ∅ (CellOf f) s P Ms L d k) - ENNReal.ofReal tp.m ≤
        ENNReal.ofReal (1 - tp.m) := by
      refine le_trans (tsub_le_tsub_right (min_le_left _ _) _) ?_
      by_cases hm0 : 0 ≤ tp.m
      · rw [ENNReal.ofReal_sub 1 hm0, ENNReal.ofReal_one]
      · rw [ENNReal.ofReal_of_nonpos (le_of_lt (not_le.1 hm0)), tsub_zero, ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (by linarith [not_le.1 hm0])
    by_cases hpsi : 1 ≤ psi K.p data wbar tp s P Ms L d k
    · calc weightA K root s * (min 1 (PiC K data wbar ∅ (CellOf f) s P Ms L d k) - ENNReal.ofReal tp.m)
          ≤ 1 * ENNReal.ofReal (1 - tp.m) := mul_le_mul' hw1 hex
        _ = ENNReal.ofReal (1 - tp.m) * 1 := by rw [one_mul, mul_one]
        _ ≤ _ := mul_le_mul_right hpsi _
    · have hmin : min 1 (PiC K data wbar ∅ (CellOf f) s P Ms L d k) ≤ ENNReal.ofReal tp.m := by
        by_cases hm1 : 1 ≤ tp.m
        · refine le_trans (min_le_left _ _) ?_
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hm1
        refine le_trans (min_le_right _ _) ?_
        have hm1' : tp.m < 1 := not_le.1 hm1
        set I := localIdx f.index
        by_cases hDn : tp.n0 ≤ (discAt d I).card
        · exact absurd (one_le_psi_light K data wbar tp hw s P Ms L d k I hn0
            (le_trans hDn (discAt_card_le d I))) hpsi
        have hDlt : (discAt d I).card < tp.n0 := not_le.1 hDn
        by_cases hok : PatOK K.p data s tp.q L P
        · by_cases hXle : ((P.filter fun p => decide (Unsigned L p)).map
              fun p => wQφ (cellOfF f) (discAt d I) tp.φ (pview K.p data s p)).sum ≤ tp.thr (discAt d I).card
          · exact PiC_le_m K root data wbar tp hH hw s P Ms L d k hP hM hL hk hrate hcoin hknown f hsurv hok
              hDlt hm1' hXle
          · have hQ : discAt d I ∈ subsetsAt (cellOfF f).1 (discAt d I).card := by
              unfold subsetsAt
              exact Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, fun v hv => (Finset.mem_filter.1 hv).2⟩
            exact absurd (one_le_psi_cell K data wbar tp hw hθ s P Ms L d k (cellOfF f) _ hDlt (discAt d I) hQ
              (Finset.filter_subset _ _) (not_le.1 hXle)) hpsi
        · unfold PatOK at hok
          push Not at hok
          obtain ⟨I', S, hS, hgt⟩ := hok
          exact absurd (one_le_psi_pat K data wbar tp s P Ms L d k I' S hS hgt) hpsi
      rw [tsub_eq_zero_of_le hmin, mul_zero]
      exact zero_le
  · exact zero_le

end Dom

end FORS.Security.SWRoute
