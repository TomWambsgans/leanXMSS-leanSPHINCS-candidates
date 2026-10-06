import LeanForest.BridgeWsum

/-! **The contact potential of the forest (A4).** A recorded forest step is a contact with weight
`cw` (one if decided, `2^-128` while its written coordinate is unexposed). Its chain is *settled*
once a reveal opens it at or below the step: the contact then pays one. An unsettled contact pays
its coefficient: the reveal rate of the remaining signatures, the coin part of cached landed pairs
and of the remaining budget, and the capped near potential. The potential

  `Ψ = Σ_{recorded} cw · (settled ? 1 : sig + coin + min(1, potN(y))) + y 2^-128 coin +
      κ 2^-128 Σ_{j < y} potN(j)`

pays, at the end, a recorded contact at a chain opened at or below its step, or a near cover with a
recorded contact; a forest step query costs `2^-128 (N rate + 1 - κ)`. -/

open OracleComp OracleSpec ENNReal

namespace LeanForest.Security.ForsPotential

open LeanSphincs.Security
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner HiddenBridge
open PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### Capped expectations -/

omit [Params] in
theorem tsum_min_leF {α : Type} (mx : ProbComp α) (X : α → ℝ≥0∞) :
    ∑' a, Pr[= a | mx] * min 1 (X a) ≤ min 1 (∑' a, Pr[= a | mx] * X a) := by
  refine le_min ?_ (ENNReal.tsum_le_tsum fun a => mul_le_mul_right (min_le_right _ _) _)
  calc ∑' a, Pr[= a | mx] * min 1 (X a) ≤ ∑' a, Pr[= a | mx] * 1 :=
        ENNReal.tsum_le_tsum fun a => mul_le_mul_right (min_le_left _ _) _
    _ = ∑' a, Pr[= a | mx] := by simp only [mul_one]
    _ ≤ 1 := tsum_probOutput_le_one

omit [Params] in
theorem pairE_min_leF (F : HashOutput → ℝ≥0∞) : pairE (fun a => min 1 (F a)) ≤ min 1 (pairE F) :=
  tsum_min_leF _ F

omit [Params] in
/-- **The split of one contact.** A contact with capped value is paid by `pay` and `κ` times its
uncapped value. -/
theorem capped_splitF {pay κ : ℝ≥0∞} (hκ : ν ≤ pay + κ * ν) (Q : ℝ≥0∞) :
    ν * min 1 Q ≤ pay + κ * ν * Q :=
  calc ν * min 1 Q ≤ (pay + κ * ν) * min 1 Q := mul_le_mul_left hκ _
    _ = pay * min 1 Q + κ * ν * min 1 Q := add_mul _ _ _
    _ ≤ pay * 1 + κ * ν * Q :=
        add_le_add (mul_le_mul_right (min_le_left _ _) _) (mul_le_mul_right (min_le_right _ _) _)
    _ = pay + κ * ν * Q := by rw [mul_one]

omit [Params] in
theorem pairE_sum_range (n : ℕ) (F : HashOutput → ℕ → ℝ≥0∞) :
    pairE (fun a => ∑ j ∈ Finset.range n, F a j) = ∑ j ∈ Finset.range n, pairE fun a => F a j := by
  unfold pairE
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]

/-! ### The potential -/

section DefsA4

variable (K : Ctx) (data : PublicData) (wbar κ : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- The chain of a step is opened by a reveal at or below the step. -/
def Settled (R : List Coordinate) (f : FIn) : Prop :=
  ∃ q : FPos, q.val ≤ f.t.val ∧ Coordinate.fchain f.index f.c f.s f.j f.a f.i q ∈ R

/-- Coefficient of a contact: one once settled, `C` otherwise. -/
noncomputable def gA (R : List Coordinate) (C : ℝ≥0∞) (f : FIn) : ℝ≥0∞ := if Settled R f then 1 else C

/-- The reveal rate of the remaining signatures. -/
noncomputable def sigRiskF (L : QueryLog SigningSpec) : ℝ≥0∞ := ((signatureLimit - L.length : ℕ) : ℝ≥0∞) * revRate

/-- Cached landed pairs of messages not yet signed. -/
noncomputable def coinCountF (P : List Pair) (L : QueryLog SigningSpec) : ℕ :=
  (P.filter fun q => decide (MsgFresh L q)).length

/-- The coin part of the reveal rate: the cached landed pairs of messages not yet signed and those
of the remaining budget. -/
noncomputable def coinRiskF (P : List Pair) (L : QueryLog SigningSpec) (budget : ℕ) : ℝ≥0∞ :=
  wbar * coinCountF P L + budget * (wbar * landing)

/-- **The near potential**: one coin, subtree-free near witness, baseline zero, no gate. -/
noncomputable def potNF (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ) :
    ℝ≥0∞ :=
  potG K.p data witnessNear wbar 0 Fail (fun _ => False) s P L d k

/-- The coefficient of an unsettled contact. -/
noncomputable def coefU (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (budget : ℕ) :
    ℝ≥0∞ :=
  sigRiskF L + coinRiskF wbar P L budget + min 1 (potNF K data wbar Fail s P L d budget)

/-- **The contact potential.** -/
noncomputable def psiF : PotF := fun s P L d R budget =>
  if signatureLimit < L.length then 0
  else K.wsum (gA R (coefU K data wbar Fail s P L d budget)) s + (budget : ℝ≥0∞) * ν * coinRiskF wbar P L budget +
    κ * ν * ∑ j ∈ Finset.range budget, potNF K data wbar Fail s P L d j

/-- The near forecast of a new pair at the start of the run. -/
noncomputable def startNearF (k : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtualOnce Finset.univ wbar (excessW witnessNear 0) signatureLimit I 0) k []

end DefsA4

/-! ### Basic facts -/

section Basic

variable (K : Ctx)

omit [Params] in
theorem gA_mono (R : List Coordinate) {C C' : ℝ≥0∞} (h : C ≤ C') (f : FIn) : gA R C f ≤ gA R C' f := by
  unfold gA
  split_ifs
  · exact le_rfl
  · exact h

theorem wsum_mono_g {g g' : FIn → ℝ≥0∞} (h : ∀ f, g f ≤ g' f) (s : State) : K.wsum g s ≤ K.wsum g' s := by
  unfold Ctx.wsum
  refine Finset.sum_le_sum fun f _ => ?_
  split_ifs
  · exact mul_le_mul_left (h f) _
  · exact le_rfl

/-- The weights split into the settled part and the unsettled part times the coefficient. -/
theorem wsum_gA (R : List Coordinate) (C : ℝ≥0∞) (s : State) :
    K.wsum (gA R C) s = K.wsum (gA R 0) s + K.wsum (fun f => if Settled R f then 0 else 1) s * C := by
  unfold Ctx.wsum gA
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases hr : Ctx.Recd s f <;> by_cases hS : Settled R f <;> simp [hr, hS, mul_comm]

theorem coinRiskF_mono (wbar : ℝ≥0∞) (P : List Pair) (L : QueryLog SigningSpec) {k k' : ℕ} (h : k ≤ k') :
    coinRiskF wbar P L k ≤ coinRiskF wbar P L k' := by
  unfold coinRiskF
  gcongr

theorem potNF_mono (data : PublicData) (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (hw : wbar ≤ 1)
    (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) {k k' : ℕ} (h : k ≤ k') :
    potNF K data wbar Fail s P L d k ≤ potNF K data wbar Fail s P L d k' :=
  potG_grow wbar 0 Fail witnessNear_props (fun _ _ _ h => h) hw ENNReal.zero_ne_top (Extends.refl s)
    (fun _ _ => rfl) L d h

/-- An unexposed read coordinate is not settled. -/
theorem not_settled_of_unknown {s : State} {R : List Coordinate} (hrinv : ∀ c ∈ R, s.known c ≠ none)
    (hclosed : UpClosed R) {f : FIn} (hk : s.known f.inC = none) : ¬Settled R f := by
  rintro ⟨q, hq, hmem⟩
  have hmem' := hclosed _ _ _ _ _ _ q ⟨f.t.val, by omega⟩ hmem hq
  exact hrinv _ hmem' hk

theorem coinCountF_addPair (parameter : PublicParameter) (P : List Pair) (L : QueryLog SigningSpec) (p : Pair)
    (u0 : HashOutput) :
    (coinCountF (addPair parameter P p u0) L : ℝ≥0∞) =
      coinCountF P L + if Landed parameter (blockIndex u0) then (if MsgFresh L p then 1 else 0) else 0 := by
  unfold coinCountF addPair
  split_ifs with hl hf
  · rw [List.filter_cons_of_pos (by simpa using hf)]
    simp
  · rw [List.filter_cons_of_neg (by simpa using hf)]
    simp
  · simp

end Basic

/-! ### A new pair -/

section NewPair

variable (K : Ctx) (data : PublicData) (wbar κ : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ)
  (model : HiddenRows.Model HashInput HashOutput Address Coordinate)

/-- A new pair moves the near potential down by one level. -/
theorem potNF_newPair (hw : wbar ≤ 1) {s : State} {P : List Pair} (hP : PInv K.p data s P) {p : Pair}
    (hp0 : s.cache (pblk K.p data p) = none) (L : QueryLog SigningSpec) (d : Multiset View) (j : ℕ) :
    pairE (fun u => potNF K data wbar Fail (withPair K.p data s p u) (addPair K.p P p u) L d j) ≤
      potNF K data wbar Fail s P L d (j + 1) := by
  unfold potNF potG
  by_cases hL : False ∨ signatureLimit < L.length
  · simp only [if_pos hL, pairE_const, le_refl]
  · simp only [if_neg hL]
    have h := coreG_newPair wbar 0 Fail witnessNear_props hw ENNReal.zero_ne_top hP hp0 L d
      (signatureLimit - L.length) j
    rwa [add_zero] at h

/-- A new pair adds a landed fresh pair with chance `landing`. -/
theorem coinRiskF_newPair (P : List Pair) (L : QueryLog SigningSpec) (p : Pair) (y : ℕ) :
    pairE (fun u => coinRiskF wbar (addPair K.p P p u) L y) ≤ coinRiskF wbar P L (y + 1) := by
  unfold coinRiskF
  simp only [coinCountF_addPair, mul_add]
  rw [pairE_add, pairE_add, pairE_const, pairE_const, pairE_const_mul]
  have hland : pairE (fun u => if Landed K.p (blockIndex u) then (if MsgFresh L p then (1 : ℝ≥0∞) else 0)
      else 0) ≤ landing := by
    have h := pairE_landed K.p (fun _ => if MsgFresh L p then (1 : ℝ≥0∞) else 0) 0
    simp only [mul_zero, add_zero] at h
    have h' : pairE (fun u => if Landed K.p (blockIndex u) then
        (fun _ : View => if MsgFresh L p then (1 : ℝ≥0∞) else 0) (viewOf u) else 0) ≤ landing := by
      rw [h, freshAvg_const _ Finset.univ_nonempty]
      split_ifs <;> simp
    simpa using h'
  calc wbar * (coinCountF P L : ℝ≥0∞) + wbar * pairE (fun u => if Landed K.p (blockIndex u) then
        (if MsgFresh L p then (1 : ℝ≥0∞) else 0) else 0) + (y : ℝ≥0∞) * (wbar * landing)
      ≤ wbar * (coinCountF P L : ℝ≥0∞) + wbar * landing + (y : ℝ≥0∞) * (wbar * landing) := by gcongr
    _ = _ := by push_cast; ring

/-- **A new pair.** -/
theorem psiF_newPair (hw : wbar ≤ 1) :
    NewPairPaysF K data Qtot model (psiF K data wbar κ Fail) := by
  intro budget s P L d R hb hB p hp0
  obtain ⟨y, rfl⟩ : ∃ y, budget = y + 1 := ⟨budget - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  unfold psiF
  by_cases hL : signatureLimit < L.length
  · simp only [if_pos hL, pairE_const, le_refl]
  simp only [if_neg hL]
  have hi := initial_none_of_fresh K.initial s hB.inv.prepared _ hp0
  have hnf : ∀ f : FIn, pblk K.p data p ≠ f.input K.p := fun f =>
    msg_ne_fchain (msgInput_digestInput K.p data.root p.1 p.2)
  have hw' : ∀ (g : FIn → ℝ≥0∞) u, K.wsum g (withPair K.p data s p u) = K.wsum g s := fun g u =>
    K.wsum_store_other g u hp0 hi hnf
  set wS := K.wsum (gA R 0) s with hwS
  set wU := K.wsum (fun f => if Settled R f then 0 else 1) s with hwU
  have hpt : ∀ u, K.wsum (gA R (coefU K data wbar Fail (withPair K.p data s p u) (addPair K.p P p u) L d y))
      (withPair K.p data s p u) = wS + wU * (sigRiskF L + coinRiskF wbar (addPair K.p P p u) L y +
        min 1 (potNF K data wbar Fail (withPair K.p data s p u) (addPair K.p P p u) L d y)) := by
    intro u
    rw [hw', wsum_gA]
    rfl
  simp only [hpt]
  rw [pairE_add, pairE_add, pairE_add, pairE_const, pairE_const_mul, pairE_add, pairE_add, pairE_const,
    pairE_const_mul, pairE_const_mul, pairE_sum_range]
  have h1 := coinRiskF_newPair K wbar P L p y
  have h2 : pairE (fun u => min 1 (potNF K data wbar Fail (withPair K.p data s p u) (addPair K.p P p u) L d y)) ≤
      min 1 (potNF K data wbar Fail s P L d (y + 1)) :=
    le_trans (pairE_min_leF _) (min_le_min le_rfl (potNF_newPair K data wbar Fail hw hB.pinv hp0 L d y))
  have h3 : ∑ j ∈ Finset.range y, pairE (fun u =>
      potNF K data wbar Fail (withPair K.p data s p u) (addPair K.p P p u) L d j) ≤
      ∑ j ∈ Finset.range (y + 1), potNF K data wbar Fail s P L d j := by
    rw [Finset.sum_range_succ']
    exact le_trans (Finset.sum_le_sum fun j _ => potNF_newPair K data wbar Fail hw hB.pinv hp0 L d j) le_self_add
  have hy : ((y : ℝ≥0∞)) ≤ ((y + 1 : ℕ) : ℝ≥0∞) := by exact_mod_cast Nat.le_succ y
  rw [wsum_gA K R (coefU K data wbar Fail s P L d (y + 1)) s, ← hwS, ← hwU]
  unfold coefU
  gcongr

end NewPair

/-! ### Any other ordinary query -/

section Ordinary

variable (K : Ctx) (data : PublicData) (wbar κ : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ)
  (model : HiddenRows.Model HashInput HashOutput Address Coordinate)

/-- **Any other ordinary query**, paying `2^-128 (N rate) + payB` at a forest step input, once
`2^-128 ≤ payB + κ 2^-128`. -/
theorem psiF_ordinary (hMp : model.parse = HiddenGraph.parse K.p (candidateActive K.p))
    (hMi : model.incoming = Address.inputCoordinate) (hw : wbar ≤ 1) {payB : ℝ≥0∞}
    (hκ : ν ≤ payB + κ * ν) :
    OrdinaryPaysF K data Qtot model (IsFchainIn K.p) (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB)
      (psiF K data wbar κ Fail) := by
  intro budget s P L d R hb hB x hnew
  obtain ⟨y, rfl⟩ : ∃ y, budget = y + 1 := ⟨budget - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  unfold psiF
  by_cases hL : signatureLimit < L.length
  · simp only [if_pos hL, mul_zero, tsum_zero, zero_le]
  simp only [if_neg hL]
  set C0 := coefU K data wbar Fail s P L d y with hC0
  set Q := potNF K data wbar Fail s P L d y with hQ
  set S := ∑ j ∈ Finset.range y, potNF K data wbar Fail s P L d j with hS
  set f1 : ℝ≥0∞ := if IsFchainIn K.p x then 1 else 0 with hf1
  have hpt : ∀ r ∈ support (ordinaryStep model x s.known s),
      K.wsum (gA R (coefU K data wbar Fail r.2 P L d y)) r.2 + (y : ℝ≥0∞) * ν * coinRiskF wbar P L y +
          κ * ν * ∑ j ∈ Finset.range y, potNF K data wbar Fail r.2 P L d j ≤
        K.wsum (gA R C0) r.2 + (y : ℝ≥0∞) * ν * coinRiskF wbar P L y + κ * ν * S := by
    intro r hr
    have hext := ordinaryStep_extends model x s r hr
    obtain ⟨_, hview⟩ := same_items K.p data hext (ordinaryStep_cache_ne model x s r hr) hnew hB.pinv
    have hgrow : ∀ j, potNF K data wbar Fail r.2 P L d j ≤ potNF K data wbar Fail s P L d j := fun j =>
      potG_grow wbar 0 Fail witnessNear_props (fun _ _ _ h => h) hw ENNReal.zero_ne_top hext hview L d le_rfl
    refine add_le_add (add_le_add (wsum_mono_g K (fun f => gA_mono R ?_ f) r.2) le_rfl)
      (mul_le_mul_right (Finset.sum_le_sum fun j _ => hgrow j) _)
    rw [hC0]; unfold coefU
    gcongr
    exact hgrow y
  have hC : ∀ f : FIn, x = f.input K.p → s.known f.inC = none → gA R C0 f ≤ C0 := by
    intro f _ hk
    unfold gA
    rw [if_neg (not_settled_of_unknown hB.rinv hB.rclosed hk)]
  have hmean := K.wsum_ordinary model hMp hMi hB.inv hB.gc x (gA R C0) C0 hC
  have hmass : ∑' r, Pr[= r | ordinaryStep model x s.known s] = 1 := by simp
  have hf1le : f1 ≤ 1 := by rw [hf1]; split_ifs <;> simp
  have hC0le : ν * C0 * f1 ≤ (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) * f1 + ν * coinRiskF wbar P L y +
      κ * ν * Q := by
    have hsig : sigRiskF L ≤ (signatureLimit : ℝ≥0∞) * revRate := by
      unfold sigRiskF
      gcongr
      exact_mod_cast Nat.sub_le _ _
    calc ν * C0 * f1 = (ν * sigRiskF L + ν * min 1 Q) * f1 + ν * coinRiskF wbar P L y * f1 := by
          rw [hC0]; unfold coefU; ring
      _ ≤ (ν * ((signatureLimit : ℝ≥0∞) * revRate) + (payB + κ * ν * Q)) * f1 + ν * coinRiskF wbar P L y * 1 := by
          gcongr
          exact capped_splitF hκ Q
      _ = (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) * f1 + ν * coinRiskF wbar P L y +
            κ * ν * Q * f1 := by ring
      _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_right' hf1le)
  calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        (K.wsum (gA R C0) r.2 + (y : ℝ≥0∞) * ν * coinRiskF wbar P L y + κ * ν * S) := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support (ordinaryStep model x s.known s)
        · exact mul_le_mul_right (hpt r hr) _
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = ∑' r, Pr[= r | ordinaryStep model x s.known s] * K.wsum (gA R C0) r.2 +
          ((y : ℝ≥0∞) * ν * coinRiskF wbar P L y + κ * ν * S) := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
        ring
    _ ≤ (K.wsum (gA R C0) s + ν * C0 * f1) + ((y : ℝ≥0∞) * ν * coinRiskF wbar P L y + κ * ν * S) :=
        add_le_add hmean le_rfl
    _ ≤ K.wsum (gA R C0) s + ((ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) * f1 +
          ν * coinRiskF wbar P L y + κ * ν * Q) + ((y : ℝ≥0∞) * ν * coinRiskF wbar P L y + κ * ν * S) := by
        gcongr
    _ = K.wsum (gA R C0) s + ((y : ℝ≥0∞) + 1) * ν * coinRiskF wbar P L y + κ * ν * (S + Q) +
          (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) * f1 := by ring
    _ ≤ K.wsum (gA R (coefU K data wbar Fail s P L d (y + 1))) s +
          ((y + 1 : ℕ) : ℝ≥0∞) * ν * coinRiskF wbar P L (y + 1) +
          κ * ν * ∑ j ∈ Finset.range (y + 1), potNF K data wbar Fail s P L d j +
          (ν * ((signatureLimit : ℝ≥0∞) * revRate) + payB) * f1 := by
        rw [Finset.sum_range_succ]
        gcongr
        · refine wsum_mono_g K (fun f => gA_mono R ?_ f) s
          rw [hC0]; unfold coefU
          gcongr
          · exact coinRiskF_mono wbar P L (Nat.le_succ y)
          · exact potNF_mono K data wbar Fail hw s P L d (Nat.le_succ y)
        · push_cast
          exact le_rfl
        · exact coinRiskF_mono wbar P L (Nat.le_succ y)

end Ordinary

/-! ### The start -/

section Start

variable (K : Ctx) (data : PublicData) (wbar κ : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

theorem potNF_start (known : HiddenReveal.Knowledge Coordinate) (total : ℕ) :
    potNF K data wbar Fail (DebtState.start K.initial known) [] [] 0 total =
      total * (startNearF wbar total + failMass Fail) + signatureLimit * failMass Fail := by
  unfold potNF potG
  rw [if_neg (by simp)]
  unfold coreG hValueG startNearF
  simp [coinItems, items]

/-- **The start of the contact potential.** -/
theorem psiF_start (known : HiddenReveal.Knowledge Coordinate) (total : ℕ) :
    psiF K data wbar κ Fail (DebtState.start K.initial known) [] [] 0 [] total =
      (total : ℝ≥0∞) * ν * (total * (wbar * landing)) +
        κ * ν * ∑ j ∈ Finset.range total, ((j : ℝ≥0∞) * (startNearF wbar j + failMass Fail) +
          signatureLimit * failMass Fail) := by
  unfold psiF
  rw [if_neg (by simp)]
  have hw0 : ∀ g, K.wsum g (DebtState.start K.initial known) = 0 := fun g => by
    unfold Ctx.wsum
    refine Finset.sum_eq_zero fun f _ => ?_
    rw [if_neg]
    intro h
    cases h
  rw [hw0, zero_add]
  simp only [potNF_start]
  unfold coinRiskF coinCountF
  simp

end Start

end LeanForest.Security.ForsPotential
