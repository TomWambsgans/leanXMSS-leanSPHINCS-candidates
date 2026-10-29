import FORS.SWRoute.ForecastStepBase

/-! **The tail potential is a supermartingale** (WP-F-B, toward `xs_bound`).

* `psi_newPair`: a new pair (an ordinary query on the first block of a fresh pair) keeps the mean of
  `psi` below its value with one more budget unit. The light part is a one-coin forecast
  (`termO_newPair`). For a cell term, the new pair's factor `e^{θ wQφ}` multiplies a forecast that
  also depends on the new pair: `E_u[a(u) T(u)] ≤ E_u[T(u)] + E_u[e(u)] T ≤ Γ_D T` since the excess
  `e(u)` is zero inside `Q`, and outside `Q` the new pair's view is irrelevant for `1[Q ⊆ ·]`, so its
  forecast is at most the old one (`termO_newPair_inv`). A pattern term gains the mean factor
  `1 + landing 2^-(b + a|S|)`.
* `psi_grow`: an ordinary query that touches no new pair does not raise `psi`.
* `psi_sign`: a signing call on a fresh message does not raise `psi` in the mean: the products over
  the unsigned pairs only lose factors (the pair a completed call creates is signed when no index
  fails), and the forecasts are the existing signing supermartingales (`post_term_leO`,
  `term_expectO`). -/

open OracleComp OracleSpec ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.LoopWalk ForsPotential PotentialA
open FORS.Security FORS.Security.H0 FORS.Security.H0Avg FORS.Base.H0

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-! ### Small facts -/

theorem inDisc_propsB (Q : Finset View) : MonoFin (inDisc Q) := by
  classical
  refine ⟨fun small large hle => ?_, fun D => ?_⟩
  · unfold inDisc
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (h1.trans (Multiset.toFinset_subset.2 (Multiset.subset_of_le hle))) h2
    · exact zero_le
    · exact le_rfl
  · unfold inDisc; split_ifs <;> simp

theorem pairE_finset_sumB {ι : Type} [DecidableEq ι] (S : Finset ι) (F : (DigestCall → HashOutput) → ι → ℝ≥0∞) :
    pairE (fun u => ∑ i ∈ S, F u i) = ∑ i ∈ S, pairE (fun u => F u i) := by
  induction S using Finset.induction_on with
  | empty => simpa using pairE_const 0
  | insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      rw [pairE_add, ih]

theorem leavesAt_le_of_subsetsAt {c : FCell} {D : ℕ} {Q : Finset View} (hQ : Q ∈ subsetsAt c.1 D) (κ' : FTree) :
    (leavesAt Q c.1 κ').card ≤ D := by
  have h := (Finset.mem_filter.1 hQ).2.1
  rw [← h]
  exact leavesAt_card_le Q c.1 κ'

/-- The unsigned-pair product after a new pair: one more factor if it lands. -/
theorem prodU_addPair_le (parameter : PublicParameter) (data : PublicData) {s : State} {P : List Pair}
    (hP : PInv parameter data s P) {p : Pair} (hp0 : s.cache (pblk parameter data p firstCall) = none)
    (L : QueryLog SigningSpec) (g : View → ℝ≥0∞) (hg : ∀ v, 1 ≤ g v) (u : DigestCall → HashOutput) :
    prodU L (addPair parameter P p u) (fun q => g (pview parameter data (withPair parameter data s p u) q)) ≤
      (if Landed parameter (blockIndex (u firstCall)) then g (viewOf u) else 1) *
        prodU L P (fun q => g (pview parameter data s q)) := by
  classical
  have hpP := not_mem_of_fresh hP hp0
  have hcongr : prodU L P (fun q => g (pview parameter data (withPair parameter data s p u) q)) =
      prodU L P (fun q => g (pview parameter data s q)) :=
    prodU_congrB L fun q hq => by
      rw [pview_withPair_other s p q (fun h => hpP (h ▸ hq)) u]
  unfold addPair
  split_ifs with hl
  · rw [prodU_consB, hcongr, pview_withPair_self]
    refine mul_le_mul_left ?_ _
    split_ifs
    · exact le_rfl
    · exact hg _
  · rw [hcongr, one_mul]

/-! ### A new pair -/

section NewPair

variable (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (tp : TailPar)

/-- **A cell term through a new pair.** -/
theorem cell_newPair (hw : wbar ≤ 1) {s : State} {Ms : List Message} (hM : MInv parameter data s Ms) (p : Pair)
    (hp0 : s.cache (pblk parameter data p firstCall) = none) (L : QueryLog SigningSpec)
    (hrate : MsgLive L p.1 → Rate parameter data wbar s p.1) (c : FCell) (D : ℕ) (Q : Finset View)
    (hQ : Q ∈ subsetsAt c.1 D) {θ : ℝ} (hθ : 0 ≤ θ) {φ : ℕ → ℝ} (hφ : ∀ r, 0 ≤ φ r) (d : Multiset View) (n k : ℕ) :
    pairE (fun u => (if Landed parameter (blockIndex (u firstCall)) then pairFφ c Q θ φ (viewOf u) else 1) *
        termO parameter data wbar (withPair parameter data s p u) (addMsg Ms p.1) L (fun _ => False) (inDisc Q) d n k) ≤
      ENNReal.ofReal (gammaR subtreeHeight forsTrees forsHeight θ φ D) *
        termO parameter data wbar s Ms L (fun _ => False) (inDisc Q) d n (k + 1) := by
  set T0 := termO parameter data wbar s Ms L (fun _ => False) (inDisc Q) d n k with hT0
  set T1 := termO parameter data wbar s Ms L (fun _ => False) (inDisc Q) d n (k + 1) with hT1
  set X := ((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ * ((2 : ℝ≥0∞) ^ forsHeight)⁻¹ *
        ∑ j ∈ Finset.range forsTrees,
          (((forsTrees - 1).choose j : ℕ) : ℝ≥0∞) * ((D : ℝ≥0∞) / 2 ^ forsHeight) ^ (forsTrees - 1 - j) *
            excφ θ φ j with hX
  have hT01 : T0 ≤ T1 := termO_mono hw (inDisc_propsB Q) s Ms L _ d n (Nat.le_succ k)
  have hpoint : ∀ u : DigestCall → HashOutput,
      (if Landed parameter (blockIndex (u firstCall)) then pairFφ c Q θ φ (viewOf u) else 1) *
        termO parameter data wbar (withPair parameter data s p u) (addMsg Ms p.1) L (fun _ => False) (inDisc Q) d n k ≤
      termO parameter data wbar (withPair parameter data s p u) (addMsg Ms p.1) L (fun _ => False) (inDisc Q) d n k +
        (if Landed parameter (blockIndex (u firstCall)) then eφ c Q θ φ (viewOf u) else 0) * T0 := by
    intro u
    split_ifs with hl
    · set Tu := termO parameter data wbar (withPair parameter data s p u) (addMsg Ms p.1) L (fun _ => False)
        (inDisc Q) d n k
      calc pairFφ c Q θ φ (viewOf u) * Tu ≤ (1 + eφ c Q θ φ (viewOf u)) * Tu :=
            mul_le_mul_left (pairFφ_le c Q θ φ _) _
        _ = Tu + eφ c Q θ φ (viewOf u) * Tu := by ring
        _ ≤ _ := by
            refine add_le_add le_rfl ?_
            by_cases hv : viewOf u ∈ Q
            · have h0 : eφ c Q θ φ (viewOf u) = 0 := by
                unfold eφ; rw [if_neg (fun h => h.2 hv)]
              rw [h0, zero_mul, zero_mul]
            · exact mul_le_mul_right (termO_newPair_inv (inDisc_propsB Q) hM p hp0 L u hl
                (inDisc_add_of_not_mem hv) d n k) _
    · rw [one_mul, zero_mul, add_zero]
  have hland : pairE (fun u => if Landed parameter (blockIndex (u firstCall)) then eφ c Q θ φ (viewOf u) else 0) ≤ X := by
    rw [pairE_landed parameter (eφ c Q θ φ) 0, mul_zero, add_zero]
    calc landing * freshAvg Finset.univ (eφ c Q θ φ) ≤ 1 * freshAvg Finset.univ (eφ c Q θ φ) :=
          mul_le_mul_left ForsPrice.landing_le_one _
      _ ≤ X := by rw [one_mul]; exact avg_eφ_le c Q D (leavesAt_le_of_subsetsAt hQ) θ φ
  calc _ ≤ pairE (fun u =>
        termO parameter data wbar (withPair parameter data s p u) (addMsg Ms p.1) L (fun _ => False) (inDisc Q) d n k +
          (if Landed parameter (blockIndex (u firstCall)) then eφ c Q θ φ (viewOf u) else 0) * T0) :=
        pairE_mono hpoint
    _ = pairE (fun u =>
          termO parameter data wbar (withPair parameter data s p u) (addMsg Ms p.1) L (fun _ => False) (inDisc Q) d n k) +
        pairE (fun u => if Landed parameter (blockIndex (u firstCall)) then eφ c Q θ φ (viewOf u) else 0) * T0 := by
        rw [pairE_add]
        congr 1
        simp only [mul_comm _ T0, pairE_const_mul]
    _ ≤ T1 + X * T1 :=
        add_le_add (termO_newPair hw (inDisc_propsB Q) hM p hp0 L _ hrate d n k) (mul_le_mul' hland hT01)
    _ = (1 + X) * T1 := by ring
    _ ≤ _ := mul_le_mul_left (gamma_le hθ hφ D) _

/-- **A pattern factor through a new pair.** -/
theorem pat_newPair (I : Fin (2 ^ subtreeHeight)) (S : Pat) :
    pairE (fun u => if Landed parameter (blockIndex (u firstCall)) then
        (haveI := Classical.propDecidable (PatCovers I S (viewOf u));
          if PatCovers I S (viewOf u) then (2 : ℝ≥0∞) else 1) else 1) ≤
      1 + ((2 : ℝ≥0∞) ^ (subtreeHeight + forsHeight * patSize S))⁻¹ := by
  classical
  rw [pairE_landed parameter (fun v => if PatCovers I S v then (2 : ℝ≥0∞) else 1) 1]
  have h2 : (fun v => if PatCovers I S v then (2 : ℝ≥0∞) else 1) =
      fun v => 1 + (if PatCovers I S v then (1 : ℝ≥0∞) else 0) := by
    funext v; split_ifs
    · norm_num
    · simp
  rw [h2, freshAvg_add, freshAvg_const _ Finset.univ_nonempty, avg_patCovers, mul_one, mul_add, mul_one,
    add_right_comm, add_tsub_cancel_of_le ForsPrice.landing_le_one]
  exact add_le_add le_rfl (mul_le_of_le_one_left' ForsPrice.landing_le_one)

/-- **`psi` through a new pair.** -/
theorem psi_newPair (hw : wbar ≤ 1) (hθ : ∀ D, 0 ≤ tp.θ D) {s : State} {P : List Pair} {Ms : List Message}
    (hP : PInv parameter data s P) (hM : MInv parameter data s Ms) (p : Pair)
    (hp0 : s.cache (pblk parameter data p firstCall) = none) (L : QueryLog SigningSpec)
    (hrate : MsgLive L p.1 → Rate parameter data wbar s p.1) (d : Multiset View) (k : ℕ) :
    pairE (fun u => psi parameter data wbar tp (withPair parameter data s p u) (addPair parameter P p u)
        (addMsg Ms p.1) L d k) ≤ psi parameter data wbar tp s P Ms L d (k + 1) := by
  classical
  unfold psi
  rw [pairE_add, pairE_add]
  refine add_le_add (add_le_add ?_ ?_) ?_
  · -- the light part
    unfold psiL
    exact termO_newPair hw (lightFail_props _) hM p hp0 L _ hrate d _ k
  · -- the cell part
    unfold psiC
    rw [pairE_finset_sumB]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [pairE_finset_sumB]
    refine Finset.sum_le_sum fun D _ => ?_
    rw [pairE_finset_sumB]
    refine Finset.sum_le_sum fun Q hQ => ?_
    set E := ENNReal.ofReal (Real.exp (-(tp.θ D * tp.thr D)))
    set G := ENNReal.ofReal (gammaR subtreeHeight forsTrees forsHeight (tp.θ D) tp.φ D)
    set g : View → ℝ≥0∞ := pairFφ c Q (tp.θ D) tp.φ
    have hg1 : ∀ v, 1 ≤ g v := one_le_pairFφ c Q (hθ D) tp.φ_nonneg
    set Pi0 := prodU L P (fun q => g (pview parameter data s q))
    calc pairE (fun u => E * prodU L (addPair parameter P p u)
            (fun q => g (pview parameter data (withPair parameter data s p u) q)) * G ^ k *
            termO parameter data wbar (withPair parameter data s p u) (addMsg Ms p.1) L (fun _ => False) (inDisc Q) d
              (signatureLimit - L.length) k)
        ≤ pairE (fun u => (E * Pi0 * G ^ k) *
            ((if Landed parameter (blockIndex (u firstCall)) then g (viewOf u) else 1) *
              termO parameter data wbar (withPair parameter data s p u) (addMsg Ms p.1) L (fun _ => False) (inDisc Q) d
                (signatureLimit - L.length) k)) := by
          refine pairE_mono fun u => ?_
          have h := prodU_addPair_le parameter data hP hp0 L g hg1 u
          calc E * prodU L (addPair parameter P p u)
                (fun q => g (pview parameter data (withPair parameter data s p u) q)) * G ^ k * _
              ≤ E * ((if Landed parameter (blockIndex (u firstCall)) then g (viewOf u) else 1) * Pi0) * G ^ k * _ := by
                gcongr
            _ = _ := by ring
      _ = (E * Pi0 * G ^ k) * pairE (fun u => (if Landed parameter (blockIndex (u firstCall)) then g (viewOf u) else 1) *
              termO parameter data wbar (withPair parameter data s p u) (addMsg Ms p.1) L (fun _ => False) (inDisc Q) d
                (signatureLimit - L.length) k) := pairE_const_mul _ _
      _ ≤ (E * Pi0 * G ^ k) * (G * termO parameter data wbar s Ms L (fun _ => False) (inDisc Q) d
              (signatureLimit - L.length) (k + 1)) :=
          mul_le_mul_right (cell_newPair parameter data wbar hw hM p hp0 L hrate c D Q hQ (hθ D) tp.φ_nonneg d _ k) _
      _ = _ := by rw [pow_succ]; ring
  · -- the pattern part
    unfold psiP
    rw [pairE_finset_sumB]
    refine Finset.sum_le_sum fun I _ => ?_
    rw [pairE_finset_sumB]
    refine Finset.sum_le_sum fun S _ => ?_
    set h : View → ℝ≥0∞ := fun v => if PatCovers I S v then 2 else 1
    have hh1 : ∀ v, 1 ≤ h v := fun v => by simp only [h]; split_ifs <;> norm_num
    set Y := ((2 : ℝ≥0∞) ^ (subtreeHeight + forsHeight * patSize S))⁻¹
    set Pi0 := prodU L P (fun q => h (pview parameter data s q))
    calc pairE (fun u => (2 : ℝ≥0∞)⁻¹ ^ patCap tp.q (patSize S) *
            prodU L (addPair parameter P p u) (fun q => h (pview parameter data (withPair parameter data s p u) q)) *
            (1 + Y) ^ k)
        ≤ pairE (fun u => ((2 : ℝ≥0∞)⁻¹ ^ patCap tp.q (patSize S) * Pi0 * (1 + Y) ^ k) *
            (if Landed parameter (blockIndex (u firstCall)) then h (viewOf u) else 1)) := by
          refine pairE_mono fun u => ?_
          have h' := prodU_addPair_le parameter data hP hp0 L h hh1 u
          calc (2 : ℝ≥0∞)⁻¹ ^ patCap tp.q (patSize S) *
                prodU L (addPair parameter P p u) (fun q => h (pview parameter data (withPair parameter data s p u) q)) *
                (1 + Y) ^ k
              ≤ (2 : ℝ≥0∞)⁻¹ ^ patCap tp.q (patSize S) *
                ((if Landed parameter (blockIndex (u firstCall)) then h (viewOf u) else 1) * Pi0) * (1 + Y) ^ k := by
                gcongr
            _ = _ := by ring
      _ = ((2 : ℝ≥0∞)⁻¹ ^ patCap tp.q (patSize S) * Pi0 * (1 + Y) ^ k) *
            pairE (fun u => if Landed parameter (blockIndex (u firstCall)) then h (viewOf u) else 1) :=
          pairE_const_mul _ _
      _ ≤ ((2 : ℝ≥0∞)⁻¹ ^ patCap tp.q (patSize S) * Pi0 * (1 + Y) ^ k) * (1 + Y) :=
          mul_le_mul_right (pat_newPair parameter I S) _
      _ = _ := by rw [pow_succ]; ring

end NewPair

/-! ### Other ordinary queries -/

section Grow

variable {parameter : PublicParameter} {data : PublicData} {wbar : ℝ≥0∞} {tp : TailPar}

/-- **A grown state with the same digest blocks** has no larger `psi`. -/
theorem psi_grow (hw : wbar ≤ 1) (hθ : ∀ D, 0 ≤ tp.θ D) {s s' : State}
    (h : ∀ q, s'.cache (pblk parameter data q firstCall) = s.cache (pblk parameter data q firstCall))
    (hv : ∀ q, LandedIn parameter data s q → ∀ call,
      s'.cache (pblk parameter data q call) = s.cache (pblk parameter data q call))
    {P : List Pair} (hPl : ∀ q ∈ P, LandedIn parameter data s q)
    (Ms : List Message) (L : QueryLog SigningSpec) (d : Multiset View) {k k' : ℕ} (hk : k' ≤ k) :
    psi parameter data wbar tp s' P Ms L d k' ≤ psi parameter data wbar tp s P Ms L d k := by
  have hpv : ∀ q ∈ P, pview parameter data s' q = pview parameter data s q :=
    fun q hq => pview_congr parameter data (hv q (hPl q hq))
  unfold psi
  refine add_le_add (add_le_add ?_ ?_) ?_
  · unfold psiL
    rw [termO_blocks wbar h hv]
    exact termO_mono hw (lightFail_props _) s Ms L _ d _ hk
  · unfold psiC
    refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun D _ => Finset.sum_le_sum fun Q _ => ?_
    rw [termO_blocks wbar h hv, prodU_congrB L (g' := fun q => pairFφ c Q (tp.θ D) tp.φ (pview parameter data s q))
      fun q hq => by rw [hpv q hq]]
    gcongr
    · exact one_le_gamma (hθ D) tp.φ_nonneg D
    · exact termO_mono hw (inDisc_propsB Q) s Ms L _ d _ hk
  · unfold psiP
    refine Finset.sum_le_sum fun I _ => Finset.sum_le_sum fun S _ => ?_
    rw [prodU_congrB L (g' := fun q => haveI := Classical.propDecidable;
      if PatCovers I S (pview parameter data s q) then (2 : ℝ≥0∞) else 1) fun q hq => by rw [hpv q hq]]
    gcongr
    exact le_self_add

end Grow

/-! ### A signing call -/

section Sign

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (tp : TailPar) (Qtot : ℕ) (m : Message)

/-- The pairs a completed signing call creates are signed, when no index fails. -/
theorem newPairs_signed (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hfail : ∀ ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ (∅ : Finset (Fin (2 ^ subtreeHeight))))
    (budget : ℕ) (s : State) (hprep : Prepared initial s) (L : QueryLog SigningSpec)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSource parameter data m) budget s))
    (r : Option Signature) (hr : out.1.1 = some r) :
    ∀ q ∈ newPairs parameter data m s out.2, ¬Unsigned (L ++ [⟨m, r⟩]) q := by
  have hpost := source_post tg initial model parameter data m (fun ρ call => hparse (m, ρ) call) ∅ hfail
    budget s hprep out hout r hr
  have hshape := sign_shape parameter data ∅ m hpost out rfl hr
  intro q hq
  rcases hshape with ⟨hnew, _⟩ | ⟨ρ, u, hnew, _, _, _, _, _, hfl, hsig⟩ | ⟨_, _, _, hnew, _⟩
  · unfold newPairs at hq; rw [hnew] at hq; simp at hq
  · have hlist : newPairs parameter data m s out.2 = [(m, ρ)] := by
      unfold newPairs; rw [hnew, Finset.toList_singleton]; rfl
    rw [hlist, List.mem_singleton] at hq
    subst hq
    rcases r with _ | sig
    · exact absurd (hfl rfl) (Finset.notMem_empty _)
    · rw [← hsig sig rfl]
      exact not_unsigned_signed
  · unfold newPairs at hq; rw [hnew] at hq; simp at hq

/-- **`psi` through a signing call** on a message that was never signed, while fewer than `N`
signatures were asked. -/
theorem psi_sign (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hfail : ∀ ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ (∅ : Finset (Fin (2 ^ subtreeHeight))))
    (hw : wbar ≤ 1) (hθ : ∀ D, 0 ≤ tp.θ D) (budget : ℕ) (s : State) (P : List Pair) (Ms : List Message)
    (L : QueryLog SigningSpec) (d : Multiset View) (R : List Coordinate) (hprep : Prepared initial s)
    (hP : PInv parameter data s P) (hM : MInv parameter data s Ms) (hD : DInv R d)
    (hC : CountInv parameter data Qtot s budget) (hm : MsgLive L m) (hlt : L.length < signatureLimit) :
    ∑' o1, Pr[= o1 | interp tg initial model (signCostSource parameter data m) budget s] *
        o1.1.1.elim 0 (fun r => psi parameter data wbar tp o1.2 (newPairs parameter data m s o1.2 ++ P)
          (addMsg Ms m) (L ++ [⟨m, r⟩]) (discAfter parameter data m s d o1) (budget - traceCost o1.1.2.2.1)) ≤
      psi parameter data wbar tp s P Ms L d budget := by
  classical
  set sign := signCostSource parameter data m with hsign
  set n := signatureLimit - (L.length + 1) with hn
  have hn1 : signatureLimit - L.length = n + 1 := by omega
  have hparse' : ∀ ρ call, model.parse (GraphView.pblk parameter data m ρ call) = none :=
    fun ρ call => hparse (m, ρ) call
  have hkind' : ∀ ρ call, tg.kind (GraphView.pblk parameter data m ρ call) = .none :=
    fun ρ call => hkind (m, ρ) call
  have hinv : PairInv parameter data m s := pairInv_of_pinv hP m
  set rest := restMsgs m L Ms with hrest
  -- the upper values of the forecasts
  set UL : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    creations Finset.univ landing (fun J => upperO parameter data wbar m s n d (lightFail (tp.n0 - 1)) rest
      (fun _ => False) o1 J) budget [] with hUL
  set UC : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    ∑ c : FCell, ∑ D ∈ Finset.range tp.n0, ∑ Q ∈ subsetsAt c.1 D,
      ENNReal.ofReal (Real.exp (-(tp.θ D * tp.thr D))) *
        prodU L P (fun q => pairFφ c Q (tp.θ D) tp.φ (pview parameter data s q)) *
        ENNReal.ofReal (gammaR subtreeHeight forsTrees forsHeight (tp.θ D) tp.φ D) ^ budget *
        creations Finset.univ landing (fun J => upperO parameter data wbar m s n d (inDisc Q) rest
          (fun _ => False) o1 J) budget [] with hUC
  have hpoint : ∀ o1 ∈ support (interp tg initial model sign budget s),
      o1.1.1.elim 0 (fun r => psi parameter data wbar tp o1.2 (newPairs parameter data m s o1.2 ++ P)
          (addMsg Ms m) (L ++ [⟨m, r⟩]) (discAfter parameter data m s d o1) (budget - traceCost o1.1.2.2.1)) ≤
        UL o1 + UC o1 + psiP parameter data tp s P L budget := by
    intro o1 ho1
    cases hres : o1.1.1 with
    | none => simp only [Option.elim]; exact zero_le
    | some r =>
        simp only [Option.elim]
        obtain ⟨-, -, -, -, -, hview⟩ := sign_paramsS tg initial model ∅ Qtot hparse hfail budget s P Ms d R
          hprep hP hM hD hC o1 ho1 r hres
        have hsigned := newPairs_signed tg initial model parameter data m hparse hfail budget s hprep L o1 ho1 r hres
        have hlen : signatureLimit - (L ++ [(⟨m, r⟩ : (_ : Message) × Option Signature)]).length = n := by
          simp only [List.length_append, List.length_singleton]
          exact hn.symm
        have hk : budget - traceCost o1.1.2.2.1 ≤ budget := Nat.sub_le _ _
        have hprod : ∀ g : View → ℝ≥0∞, (∀ v, 1 ≤ g v) →
            prodU (L ++ [⟨m, r⟩]) (newPairs parameter data m s o1.2 ++ P) (fun q => g (pview parameter data o1.2 q)) ≤
              prodU L P (fun q => g (pview parameter data s q)) := fun g hg =>
          prodU_le_ofB L _ _ P _ _ (fun q => hg _) hsigned (fun q hq => unsigned_of_append hq)
            (fun q hq => by rw [hview q hq])
        unfold psi
        refine add_le_add (add_le_add ?_ ?_) ?_
        · unfold psiL
          rw [hlen]
          exact post_term_leO tg initial model parameter data wbar ∅ m hw (lightFail_props _) hparse hfail budget s Ms L d
            hprep o1 ho1 r hres (fun _ => False) (fun _ _ _ h => h) n hk
        · unfold psiC
          refine Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun D _ => Finset.sum_le_sum fun Q _ => ?_
          rw [hlen]
          exact mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl (hprod _ (one_le_pairFφ c Q (hθ D) tp.φ_nonneg)))
            (pow_le_pow_right₀ (one_le_gamma (hθ D) tp.φ_nonneg D) hk))
            (post_term_leO tg initial model parameter data wbar ∅ m hw (inDisc_propsB Q) hparse hfail budget s Ms L
              d hprep o1 ho1 r hres (fun _ => False) (fun _ _ _ h => h) n hk)
        · unfold psiP
          refine Finset.sum_le_sum fun I _ => Finset.sum_le_sum fun S _ => ?_
          exact mul_le_mul' (mul_le_mul' le_rfl (hprod (fun v => haveI := Classical.propDecidable (PatCovers I S v);
            if PatCovers I S v then (2 : ℝ≥0∞) else 1) (fun v => by split_ifs <;> norm_num)))
            (pow_le_pow_right₀ le_self_add hk)
  have hmass : ∑' o1, Pr[= o1 | interp tg initial model sign budget s] ≤ 1 := tsum_probOutput_le_one
  have hEL : ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * UL o1 ≤
      psiL parameter data wbar tp s Ms L d budget := by
    unfold psiL
    rw [hn1, termO_eq_cons hm hM]
    exact term_expectO tg initial model hparse' hkind' hinv (lightFail_props _) _ _ budget budget
  have hEC : ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * UC o1 ≤
      psiC parameter data wbar tp s P Ms L d budget := by
    simp only [hUC, Finset.mul_sum]
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    unfold psiC
    refine Finset.sum_le_sum fun c _ => ?_
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine Finset.sum_le_sum fun D _ => ?_
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    refine Finset.sum_le_sum fun Q _ => ?_
    rw [hn1]
    calc _ = (ENNReal.ofReal (Real.exp (-(tp.θ D * tp.thr D))) *
            prodU L P (fun q => pairFφ c Q (tp.θ D) tp.φ (pview parameter data s q)) *
            ENNReal.ofReal (gammaR subtreeHeight forsTrees forsHeight (tp.θ D) tp.φ D) ^ budget) *
          ∑' o1, Pr[= o1 | interp tg initial model sign budget s] *
            creations Finset.univ landing (fun J => upperO parameter data wbar m s n d (inDisc Q) rest
              (fun _ => False) o1 J) budget [] := by
          rw [← ENNReal.tsum_mul_left]
          exact tsum_congr fun o1 => by ring
      _ ≤ _ := by
          refine mul_le_mul_right ?_ _
          rw [termO_eq_cons hm hM]
          exact term_expectO tg initial model hparse' hkind' hinv (inDisc_propsB Q) _ _ budget budget
  calc _ ≤ ∑' o1, Pr[= o1 | interp tg initial model sign budget s] *
        (UL o1 + UC o1 + psiP parameter data tp s P L budget) := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support (interp tg initial model sign budget s)
        · exact mul_le_mul_right (hpoint o1 ho1) _
        · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
    _ = ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * UL o1 +
          ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * UC o1 +
          (∑' o1, Pr[= o1 | interp tg initial model sign budget s]) * psiP parameter data tp s P L budget := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ _ := by
        unfold psi
        exact add_le_add (add_le_add hEL hEC) (mul_le_of_le_one_left' hmass)

end Sign

end FORS.Security.SWRoute
