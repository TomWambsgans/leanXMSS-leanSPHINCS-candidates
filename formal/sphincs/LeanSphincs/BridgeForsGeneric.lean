import LeanSphincs.BridgeForsPotentialOnce

/-! The one-coin FORS potential with a generic witness. A witness `W` assigns to a target view and
a multiset of disclosed views a monotone, supermodular, finite value; the fresh-digest price is
`landing` times its average over a uniform target. The potential and its new-pair, order and growth
lemmas are those of `BridgeForsPotentialOnce` with the cover witness replaced by `W` and an
arbitrary monotone gate in place of the decided-hit test; `canonG` bounds one outcome of a signing
call, as used by the signing lemmas of `BridgeContactHalf`. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] digestAttemptLimit

variable [Params]

/-! ### Witnesses and their prices -/

/-- A witness is monotone, supermodular and finite in the disclosures, for every target. -/
def WitnessProps (W : View → Multiset View → ℝ≥0∞) : Prop :=
  ∀ v, Monotone' (W v) ∧ Supermodular (W v) ∧ ∀ D, W v D ≠ ⊤

/-- The price of a fresh digest for a witness. -/
noncomputable def priceW (W : View → Multiset View → ℝ≥0∞) (D : Multiset View) : ℝ≥0∞ :=
  landing * freshAvg Finset.univ fun v => W v D

/-- The excess of the price over a baseline. -/
noncomputable def excessW (W : View → Multiset View → ℝ≥0∞) (b0 : ℝ≥0∞) (D : Multiset View) : ℝ≥0∞ :=
  priceW W D - b0

theorem priceW_props {W : View → Multiset View → ℝ≥0∞} (hW : WitnessProps W) :
    Monotone' (priceW W) ∧ Supermodular (priceW W) ∧ ∀ D, priceW W D ≠ ⊤ := by
  refine ⟨mono_const_mul (mono_freshAvg _ fun v => (hW v).1) _,
    super_const_mul (super_freshAvg _ fun v => (hW v).2.1) _, fun D => ?_⟩
  refine ENNReal.mul_ne_top ?_ (freshAvg_ne_top Finset.univ_nonempty fun v => (hW v).2.2 D)
  simp [landing]

theorem excessW_props {W : View → Multiset View → ℝ≥0∞} (hW : WitnessProps W) {b0 : ℝ≥0∞} (hb0 : b0 ≠ ⊤) :
    Monotone' (excessW W b0) ∧ Supermodular (excessW W b0) ∧ ∀ D, excessW W b0 D ≠ ⊤ :=
  ⟨excess_mono (priceW_props hW).1 b0, excess_super (priceW_props hW).1 (priceW_props hW).2.1
    (priceW_props hW).2.2 b0 hb0, fun D => ne_top_of_le_ne_top ((priceW_props hW).2.2 D) tsub_le_self⟩

/-! ### The potential -/

section DefsG

variable (parameter : PublicParameter) (data : PublicData) (W : View → Multiset View → ℝ≥0∞)
  (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (gate : State → Prop)

/-- The forecast of a candidate: its own item is excluded from the group of its message. -/
noncomputable def candValueG (s : State) (_P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View)
    (n k : ℕ) (p : Pair) : ℝ≥0∞ :=
  fut parameter data wbar s L (· = p) (W (pview parameter data s p)) n k d

/-- The excess forecast of a new pair. -/
noncomputable def hValueG (s : State) (_P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    ℝ≥0∞ :=
  fut parameter data wbar s L (fun _ => False) (excessW W b0) n k d

/-- The value of a candidate: one at a failing index, its forecast otherwise; zero once signed. -/
noncomputable def candG (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (p : Pair) : ℝ≥0∞ :=
  if Unsigned L p then
    (if (pview parameter data s p).1 ∈ Fail then 1 else candValueG parameter data W wbar s P L d n k p)
  else 0

/-- The potential without the gate. -/
noncomputable def coreG (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    ℝ≥0∞ :=
  (P.map (candG parameter data W wbar Fail s P L d n k)).sum +
    k * (hValueG parameter data W wbar b0 s P L d n k + failMass Fail) + n * failMass Fail

/-- **The generic potential.** -/
noncomputable def potG (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ) :
    ℝ≥0∞ :=
  if gate s ∨ signatureLimit < L.length then 0
  else coreG parameter data W wbar b0 Fail s P L d (signatureLimit - L.length) k

end DefsG

/-! ### A new pair -/

section NewPairG

variable (parameter : PublicParameter) (data : PublicData) (W : View → Multiset View → ℝ≥0∞)
  (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

variable {parameter data}

/-- A new candidate's forecast is at most the baseline plus one excess. -/
theorem fresh_forecastG (hw : wbar ≤ 1) (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop)
    (d : Multiset View) (n k : ℕ) :
    landing * freshAvg Finset.univ (fun v => fut parameter data wbar s L excl (W v) n k d) ≤
      b0 + fut parameter data wbar s L excl (excessW W b0) n k d := by
  rw [← fut_freshAvg hw, ← fut_const_mul hw]
  calc fut parameter data wbar s L excl (fun D => landing * freshAvg Finset.univ fun v => W v D) n k d
      ≤ fut parameter data wbar s L excl (fun D => (fun _ => b0) D + excessW W b0 D) n k d :=
        fut_mono_base hw s L excl (fun D => show priceW W D ≤ b0 + (priceW W D - b0) from le_add_tsub) n k d
    _ = _ := by rw [fut_add hw, fut_const hw]

/-- Old candidates after a new pair: the same views, the groups of the new state. -/
theorem candG_withPair {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (q : Pair) (hq : q ∈ P) (u0 u1 : HashOutput) (P' : List Pair) :
    candG parameter data W wbar Fail (withPair parameter data s p u0 u1) P' L d n k q =
      if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
        fut parameter data wbar (withPair parameter data s p u0 u1) L (· = q)
          (W (pview parameter data s q)) n k d) else 0 := by
  have hpP := not_mem_of_fresh hP hp0
  have hqp : q ≠ p := fun h => hpP (h ▸ hq)
  unfold candG candValueG
  rw [pview_withPair_other (parameter := parameter) (data := data) s p q hqp u0 u1]

variable {W}

/-- The new candidate itself. -/
theorem candG_withPair_self (hW : WitnessProps W) (hw : wbar ≤ 1) {s : State} {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (u0 u1 : HashOutput) (hl : Landed parameter (blockIndex u0)) (P' : List Pair) :
    candG parameter data W wbar Fail (withPair parameter data s p u0 u1) P' L d n k p ≤
      (if (viewOf u0 u1).1 ∈ Fail then 1 else 0) +
        fut parameter data wbar s L (fun _ => False) (W (viewOf u0 u1)) n k d := by
  unfold candG candValueG
  rw [pview_withPair_self]
  split_ifs
  · exact le_self_add
  · rw [zero_add]
    exact fut_newPair_self hw (hW _) s L p hp0 u0 u1 hl n k d
  · exact bot_le
  · exact bot_le

variable (W) in
/-- The excess forecast after a new pair is the forecast of the new state. -/
theorem hValueG_withPair (s : State) (p : Pair) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (u0 u1 : HashOutput) (P' : List Pair) :
    hValueG parameter data W wbar b0 (withPair parameter data s p u0 u1) P' L d n k =
      fut parameter data wbar (withPair parameter data s p u0 u1) L (fun _ => False) (excessW W b0) n k d := rfl

theorem candValueG_mono (hW : WitnessProps W) (hw : wbar ≤ 1) (s : State) (P : List Pair)
    (L : QueryLog SigningSpec) (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') (p : Pair) :
    candValueG parameter data W wbar s P L d n k p ≤ candValueG parameter data W wbar s P L d n k' p :=
  fut_mono_count hw (hW _) s L _ n hk d

theorem hValueG_mono (hW : WitnessProps W) (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (s : State) (P : List Pair)
    (L : QueryLog SigningSpec) (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    hValueG parameter data W wbar b0 s P L d n k ≤ hValueG parameter data W wbar b0 s P L d n k' :=
  fut_mono_count hw (excessW_props hW hb0) s L _ n hk d

theorem candG_mono (hW : WitnessProps W) (hw : wbar ≤ 1) (s : State) (P : List Pair) (L : QueryLog SigningSpec)
    (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') (q : Pair) :
    candG parameter data W wbar Fail s P L d n k q ≤ candG parameter data W wbar Fail s P L d n k' q := by
  unfold candG
  split_ifs
  · exact le_rfl
  · exact candValueG_mono wbar hW hw s P L d n hk q
  · exact le_rfl

theorem coreG_mono (hW : WitnessProps W) (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (s : State) (P : List Pair)
    (L : QueryLog SigningSpec) (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    coreG parameter data W wbar b0 Fail s P L d n k ≤ coreG parameter data W wbar b0 Fail s P L d n k' := by
  unfold coreG
  refine add_le_add (add_le_add (List.sum_le_sum fun q _ => candG_mono wbar Fail hW hw s P L d n hk q) ?_) le_rfl
  exact mul_le_mul' (by exact_mod_cast hk) (add_le_add (hValueG_mono wbar b0 hW hw hb0 s P L d n hk) le_rfl)

/-- **A new pair.** Touching a new pair costs one future pair and at most the baseline. -/
theorem coreG_newPair (hW : WitnessProps W) (hfair : Fair5 wbar) (hb0 : b0 ≠ ⊤) {s : State} {P : List Pair}
    (hP : PInv parameter data s P) {p : Pair} (hp0 : s.cache (pblk parameter data p 0) = none)
    (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    pairE (fun u0 u1 => coreG parameter data W wbar b0 Fail (withPair parameter data s p u0 u1)
      (addPair parameter P p u0) L d n k) ≤ coreG parameter data W wbar b0 Fail s P L d n (k + 1) + b0 := by
  have hw := hfair.le_one
  have hpP := not_mem_of_fresh hP hp0
  set Wv : View → ℝ≥0∞ := fun v => fut parameter data wbar s L (fun _ => False) (W v) n k d with hWv
  set φ := failMass Fail with hφ
  set A : Pair → HashOutput → HashOutput → ℝ≥0∞ := fun q u0 u1 => if Unsigned L q then
    (if (pview parameter data s q).1 ∈ Fail then 1 else
      fut parameter data wbar (withPair parameter data s p u0 u1) L (· = q)
        (W (pview parameter data s q)) n k d) else 0 with hA
  set Hs : HashOutput → HashOutput → ℝ≥0∞ := fun u0 u1 =>
    fut parameter data wbar (withPair parameter data s p u0 u1) L (fun _ => False) (excessW W b0) n k d with hHs
  have hpoint : ∀ u0 u1, coreG parameter data W wbar b0 Fail (withPair parameter data s p u0 u1)
      (addPair parameter P p u0) L d n k ≤
      ((if Landed parameter (blockIndex u0) then
          (if (viewOf u0 u1).1 ∈ Fail then 1 else 0) + Wv (viewOf u0 u1) else 0) +
        (P.map fun q => A q u0 u1).sum) + k * (Hs u0 u1 + φ) + n * φ := by
    intro u0 u1
    unfold coreG
    have hH : hValueG parameter data W wbar b0 (withPair parameter data s p u0 u1) (addPair parameter P p u0) L d n k =
        Hs u0 u1 := rfl
    rw [hH]
    have hmap : ∀ P' : List Pair, P.map (candG parameter data W wbar Fail (withPair parameter data s p u0 u1) P' L d n k) =
        P.map fun q => A q u0 u1 := fun P' => List.map_congr_left fun q hq =>
      candG_withPair W wbar Fail hP hp0 L d n k q hq u0 u1 P'
    have hlist : ((addPair parameter P p u0).map (candG parameter data W wbar Fail (withPair parameter data s p u0 u1)
        (addPair parameter P p u0) L d n k)).sum ≤
        (if Landed parameter (blockIndex u0) then
          (if (viewOf u0 u1).1 ∈ Fail then 1 else 0) + Wv (viewOf u0 u1) else 0) +
        (P.map fun q => A q u0 u1).sum := by
      by_cases hl : Landed parameter (blockIndex u0)
      · unfold addPair
        simp only [if_pos hl, List.map_cons, List.sum_cons]
        rw [hmap]
        exact add_le_add (candG_withPair_self wbar Fail hW hw hp0 L d n k u0 u1 hl _) le_rfl
      · unfold addPair
        simp only [if_neg hl, zero_add]
        rw [hmap]
    gcongr
  refine le_trans (pairE_mono hpoint) ?_
  simp only [pairE_add, pairE_const_mul, pairE_const, pairE_list_sum]
  have h1 : pairE (fun u0 u1 => if Landed parameter (blockIndex u0) then
      (if (viewOf u0 u1).1 ∈ Fail then 1 else 0) + Wv (viewOf u0 u1) else 0) = landing * (φ + freshAvg Finset.univ Wv) := by
    rw [pairE_landed parameter (fun v => (if v.1 ∈ Fail then 1 else 0) + Wv v) 0, mul_zero, add_zero, freshAvg_add]
    rfl
  have h2 : ∀ q ∈ P, pairE (fun u0 u1 => A q u0 u1) ≤ candG parameter data W wbar Fail s P L d n (k + 1) q := by
    intro q hq
    have hqp : ¬p = q := fun h => hpP (h ▸ hq)
    simp only [hA]
    unfold candG candValueG
    split_ifs
    · simp only [pairE_const, le_refl]
    · exact fut_newPair hfair (hW _) s L (· = q) p hp0 hqp n k d
    · simp only [pairE_const, le_refl]
  have h3 : pairE (fun u0 u1 => Hs u0 u1) ≤ hValueG parameter data W wbar b0 s P L d n (k + 1) :=
    fut_newPair hfair (excessW_props hW hb0) s L (fun _ => False) p hp0 (fun h => h) n k d
  have hfresh : landing * freshAvg Finset.univ Wv ≤ b0 + hValueG parameter data W wbar b0 s P L d n (k + 1) := by
    refine le_trans (fresh_forecastG W wbar b0 hw s L (fun _ => False) d n k) (add_le_add le_rfl ?_)
    exact hValueG_mono wbar b0 hW hw hb0 s P L d n (Nat.le_succ k)
  have hφ1 : landing * φ ≤ φ := mul_le_of_le_one_left' landing_le_one
  rw [h1]
  unfold coreG
  set S := (P.map (candG parameter data W wbar Fail s P L d n (k + 1))).sum
  set H := hValueG parameter data W wbar b0 s P L d n (k + 1)
  have hS : (P.map fun q => pairE fun u0 u1 => A q u0 u1).sum ≤ S :=
    List.sum_le_sum fun q hq => h2 q hq
  calc landing * (φ + freshAvg Finset.univ Wv) + (P.map fun q => pairE fun u0 u1 => A q u0 u1).sum +
        k * (pairE (fun u0 u1 => Hs u0 u1) + φ) + n * φ
      ≤ φ + (b0 + H) + S + k * (H + φ) + n * φ := by
        rw [mul_add]
        gcongr
    _ = S + ((k : ℝ≥0∞) + 1) * (H + φ) + n * φ + b0 := by ring
    _ = _ := by push_cast; ring

end NewPairG

/-! ### Order and congruence -/

section OrderG

variable (parameter : PublicParameter) (data : PublicData) {W : View → Multiset View → ℝ≥0∞}
  (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

variable {parameter data}

/-- The potential sees the state only through the views of its items and the statuses. -/
theorem coreG_congr {s s' : State} {P : List Pair}
    (h : ∀ q ∈ P, pview parameter data s' q = pview parameter data s q)
    (hstat : ∀ m, stat parameter data m s' = stat parameter data m s)
    (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    coreG parameter data W wbar b0 Fail s' P L d n k = coreG parameter data W wbar b0 Fail s P L d n k := by
  have hcand : ∀ q ∈ P, candG parameter data W wbar Fail s' P L d n k q =
      candG parameter data W wbar Fail s P L d n k q := by
    intro q hq
    unfold candG candValueG
    rw [h q hq, fut_congr L _ _ (fun m _ => hstat m)]
  unfold coreG hValueG
  rw [List.map_congr_left hcand, fut_congr L _ _ (fun m _ => hstat m)]

theorem potG_mono (hW : WitnessProps W) (gate : State → Prop) (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (s : State)
    (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) {k k' : ℕ} (hk : k ≤ k') :
    potG parameter data W wbar b0 Fail gate s P L d k ≤ potG parameter data W wbar b0 Fail gate s P L d k' := by
  unfold potG
  split_ifs
  · exact le_rfl
  · exact coreG_mono wbar b0 Fail hW hw hb0 s P L d _ hk

/-- A grown state with the same item views and statuses has no larger potential. -/
theorem potG_grow (hW : WitnessProps W) {gate : State → Prop}
    (hgate : ∀ s s' : State, Extends s s' → gate s → gate s') (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤)
    {s s' : State} (hext : Extends s s') {P : List Pair}
    (hview : ∀ q ∈ P, pview parameter data s' q = pview parameter data s q)
    (hstat : ∀ m, stat parameter data m s' = stat parameter data m s) (L : QueryLog SigningSpec)
    (d : Multiset View) {k k' : ℕ} (hk : k ≤ k') :
    potG parameter data W wbar b0 Fail gate s' P L d k ≤ potG parameter data W wbar b0 Fail gate s P L d k' := by
  unfold potG
  by_cases hr : gate s' ∨ signatureLimit < L.length
  · rw [if_pos hr]; exact bot_le
  · have hr' : ¬(gate s ∨ signatureLimit < L.length) := fun h => hr (h.imp (hgate s s' hext) id)
    rw [if_neg hr, if_neg hr', coreG_congr wbar b0 Fail hview hstat]
    exact coreG_mono wbar b0 Fail hW hw hb0 s P L d _ hk

end OrderG

/-! ### The bound for one signing outcome -/

section SignPointG

variable (parameter : PublicParameter) (data : PublicData) (W : View → Multiset View → ℝ≥0∞)
  (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (m : Message) (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View)

/-- Bound for one outcome of a signing call. -/
noncomputable def canonG (n k : ℕ) (out : Run HashInput Coordinate (Option Signature) × State) : ℝ≥0∞ :=
  freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out +
  (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
      creations Finset.univ landing (fun J => upperO parameter data wbar m s n d
        (stateFn parameter data s (L ++ [⟨m, none⟩]) (· = q) (W (pview parameter data s q)))
        (· = q) out J) k []) else 0).sum +
  k * (creations Finset.univ landing (fun J => upperO parameter data wbar m s n d
      (stateFn parameter data s (L ++ [⟨m, none⟩]) (fun _ => False) (excessW W b0)) (fun _ => False) out J) k [] +
    failMass Fail) +
  n * failMass Fail

end SignPointG

end LeanSphincs.Security.ForsPotential
