import LeanForest.BridgeForsPotentialOnce

/-! The one-coin forest potential with a generic monotone witness. A witness `W` assigns to a target
view and a multiset of disclosed views a monotone, finite value; the fresh-digest price is `landing`
times its average over a uniform target. The potential and its new-pair, order and signing lemmas
are those of `BridgeForsPotentialOnce` with the cover witness replaced by `W` and an arbitrary monotone
gate in place of the decided-hit test; the forecast level of the signing lemmas is free of the
run's budget. -/

open OracleComp OracleSpec ENNReal

namespace LeanForest.Security.ForsPotential

open LeanSphincs.Security
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner LeanSphincs.Security.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### Witnesses and their prices -/

/-- Monotone finite witnesses. -/
def WitnessProps (W : View → Multiset View → ℝ≥0∞) : Prop := ∀ v, MonoFin (W v)

/-- The fresh-digest price of a witness. -/
noncomputable def priceW (W : View → Multiset View → ℝ≥0∞) (D : Multiset View) : ℝ≥0∞ :=
  landing * freshAvg Finset.univ fun v => W v D

/-- The excess of the price over a baseline. -/
noncomputable def excessW (W : View → Multiset View → ℝ≥0∞) (b0 : ℝ≥0∞) (D : Multiset View) : ℝ≥0∞ :=
  priceW W D - b0

theorem priceW_props {W : View → Multiset View → ℝ≥0∞} (hW : WitnessProps W) : MonoFin (priceW W) := by
  refine ⟨fun a b hab => ?_, fun D => ?_⟩
  · unfold priceW
    exact mul_le_mul_left' (freshAvg_mono _ fun v _ => (hW v).1 a b hab) _
  · unfold priceW
    refine ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top landing_le_one) ?_
    exact freshAvg_ne_top Finset.univ_nonempty fun v => (hW v).2 D

theorem excessW_props {W : View → Multiset View → ℝ≥0∞} (hW : WitnessProps W) {b0 : ℝ≥0∞} (_hb0 : b0 ≠ ⊤) :
    MonoFin (excessW W b0) := by
  refine ⟨fun a b hab => tsub_le_tsub_right ((priceW_props hW).1 a b hab) b0, fun D => ?_⟩
  unfold excessW
  exact ne_top_of_le_ne_top ((priceW_props hW).2 D) tsub_le_self


/-! ### The potential -/

section DefsG

variable (parameter : PublicParameter) (data : PublicData) (W : View → Multiset View → ℝ≥0∞)
  (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- The forecast of a candidate. -/
noncomputable def candValueG (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View)
    (n k : ℕ) (p : Pair) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtualOnce Finset.univ wbar (W (pview parameter data s p)) n I d)
    k (coinItems parameter data s L (P.erase p))

/-- The excess forecast of a new pair. -/
noncomputable def hValueG (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtualOnce Finset.univ wbar (excessW W b0) n I d) k
    (coinItems parameter data s L P)

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

variable (gate : State → Prop)

/-- **The generic potential.** -/
noncomputable def potG (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ) :
    ℝ≥0∞ :=
  if gate s ∨ signatureLimit < L.length then 0
  else coreG parameter data W wbar b0 Fail s P L d (signatureLimit - L.length) k

end DefsG

section Basic

variable {W : View → Multiset View → ℝ≥0∞} (wbar b0 : ℝ≥0∞)

/-- A new candidate's forecast is at most the baseline plus one excess. -/
theorem fresh_forecastG (hw : wbar ≤ 1) (I : List View) (d : Multiset View) (n k : ℕ) :
    landing * freshAvg Finset.univ (fun v => creations Finset.univ landing
      (fun J => virtualOnce Finset.univ wbar (W v) n J d) k I) ≤
    b0 + creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar (excessW W b0) n J d) k I := by
  have hU : (Finset.univ : Finset View).Nonempty := Finset.univ_nonempty
  rw [← creations_freshAvg, ← creations_const_mul]
  have hpt : ∀ J, landing * freshAvg Finset.univ (fun v => virtualOnce Finset.univ wbar (W v) n J d) ≤
      b0 + virtualOnce Finset.univ wbar (excessW W b0) n J d := by
    intro J
    rw [← virtualOnce_freshAvg hU, ← virtualOnce_const_mul]
    calc virtualOnce Finset.univ wbar (fun D => landing * freshAvg Finset.univ fun v => W v D) n J d
        ≤ virtualOnce Finset.univ wbar (fun D => b0 + excessW W b0 D) n J d :=
          virtualOnce_mono_base (fun D => show priceW W D ≤ b0 + (priceW W D - b0) from le_add_tsub) n J d
      _ = b0 + virtualOnce Finset.univ wbar (excessW W b0) n J d := by
          rw [virtualOnce_add hU (fun _ => b0) (excessW W b0), virtualOnce_const hU hw]
  calc creations Finset.univ landing (fun J => landing * freshAvg Finset.univ fun v =>
        virtualOnce Finset.univ wbar (W v) n J d) k I
      ≤ creations Finset.univ landing (fun J => b0 + virtualOnce Finset.univ wbar (excessW W b0) n J d) k I :=
        creations_mono hpt k I
    _ = _ := by rw [creations_add (fun _ => b0), creations_const Finset.univ_nonempty landing_le_one]

end Basic

/-! ### A new pair -/

section NewPairG

variable (parameter : PublicParameter) (data : PublicData) {W : View → Multiset View → ℝ≥0∞} (wbar b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight)))

variable {parameter data}

/-- Old candidates after a new pair. -/
theorem candG_withPair {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p) = none) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (q : Pair) (hq : q ∈ P) (u0 : HashOutput) :
    candG parameter data W wbar Fail (withPair parameter data s p u0) (addPair parameter P p u0) L d n k q =
      if Landed parameter (blockIndex u0) then
        (if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
          creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar (W (pview parameter data s q))
            n J d) k (newCoin L p u0 (coinItems parameter data s L (P.erase q)))) else 0)
      else candG parameter data W wbar Fail s P L d n k q := by
  have hpP := not_mem_of_fresh hP hp0
  have hqp : q ≠ p := fun h => hpP (h ▸ hq)
  have hv := pview_withPair_other (parameter := parameter) (data := data) s p q hqp u0
  have hsub : ∀ r ∈ P.erase q, r ∈ P := fun r hr => List.mem_of_mem_erase hr
  by_cases hl : Landed parameter (blockIndex u0)
  · rw [if_pos hl]
    unfold candG candValueG addPair
    rw [if_pos hl, hv]
    have herase : (p :: P).erase q = p :: P.erase q := List.erase_cons_tail (by simpa using hqp.symm)
    rw [herase, coinItems_cons_withPair hP hp0 L u0 _ hsub]
  · rw [if_neg hl]
    unfold candG candValueG addPair
    rw [if_neg hl, hv, coinItems_withPair hP hp0 L u0 _ hsub]

/-- The new candidate itself. -/
theorem candG_withPair_self {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p) = none) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (u0 : HashOutput) :
    candG parameter data W wbar Fail (withPair parameter data s p u0) (p :: P) L d n k p ≤
      (if (viewOf u0).1 ∈ Fail then 1 else 0) +
        creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar (W (viewOf u0)) n J d) k
          (coinItems parameter data s L P) := by
  unfold candG candValueG
  rw [pview_withPair_self, List.erase_cons_head, coinItems_withPair hP hp0 L u0 _ fun r hr => hr]
  split_ifs <;> simp

theorem hValueG_withPair {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p) = none) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (u0 : HashOutput) :
    hValueG parameter data W wbar b0 (withPair parameter data s p u0) (addPair parameter P p u0) L d n k =
      if Landed parameter (blockIndex u0) then
        creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar (excessW W b0) n J d) k
          (newCoin L p u0 (coinItems parameter data s L P))
      else hValueG parameter data W wbar b0 s P L d n k := by
  unfold hValueG addPair
  split_ifs
  · rw [coinItems_cons_withPair hP hp0 L u0 _ fun r hr => hr]
  · rw [coinItems_withPair hP hp0 L u0 _ fun r hr => hr]

theorem candValueG_mono (hW : WitnessProps W) (hw : wbar ≤ 1) (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View)
    (n : ℕ) {k k' : ℕ} (hk : k ≤ k') (p : Pair) :
    candValueG parameter data W wbar s P L d n k p ≤ candValueG parameter data W wbar s P L d n k' p :=
  creations_mono_count Finset.univ_nonempty landing_le_one
    (virtualOnce_cons_le' wbar hw (hW _) n d) (virtualOnce_perm' wbar n d) hk _

theorem hValueG_mono (hW : WitnessProps W) (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (s : State) (P : List Pair) (L : QueryLog SigningSpec)
    (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    hValueG parameter data W wbar b0 s P L d n k ≤ hValueG parameter data W wbar b0 s P L d n k' :=
  creations_mono_count Finset.univ_nonempty landing_le_one
    (virtualOnce_cons_le' wbar hw (excessW_props hW hb0) n d) (virtualOnce_perm' wbar n d) hk _

theorem candG_mono (hW : WitnessProps W) (hw : wbar ≤ 1) (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View)
    (n : ℕ) {k k' : ℕ} (hk : k ≤ k') (q : Pair) :
    candG parameter data W wbar Fail s P L d n k q ≤ candG parameter data W wbar Fail s P L d n k' q := by
  unfold candG
  split_ifs
  · exact le_rfl
  · exact candValueG_mono wbar hW hw s P L d n hk q
  · exact le_rfl

theorem coreG_mono (hW : WitnessProps W) (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (s : State) (P : List Pair) (L : QueryLog SigningSpec)
    (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    coreG parameter data W wbar b0 Fail s P L d n k ≤ coreG parameter data W wbar b0 Fail s P L d n k' := by
  unfold coreG
  refine add_le_add (add_le_add (List.sum_le_sum fun q _ => candG_mono wbar Fail hW hw s P L d n hk q) ?_) le_rfl
  exact mul_le_mul' (by exact_mod_cast hk) (add_le_add (hValueG_mono wbar b0 hW hw hb0 s P L d n hk) le_rfl)

/-- **A new pair.** Touching a new pair costs one future pair and at most the baseline. -/
theorem coreG_newPair (hW : WitnessProps W) (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) {s : State} {P : List Pair}
    (hP : PInv parameter data s P) {p : Pair} (hp0 : s.cache (pblk parameter data p) = none)
    (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    pairE (fun u0 => coreG parameter data W wbar b0 Fail (withPair parameter data s p u0)
      (addPair parameter P p u0) L d n k) ≤ coreG parameter data W wbar b0 Fail s P L d n (k + 1) + b0 := by
  set I := coinItems parameter data s L P with hI
  set Wv : View → ℝ≥0∞ := fun v =>
    creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar (W v) n J d) k I with hWv
  set GH : List View → ℝ≥0∞ := fun J => virtualOnce Finset.univ wbar (excessW W b0) n J d with hGH
  set φ := failMass Fail with hφ
  set A : Pair → HashOutput → ℝ≥0∞ := fun q u0 => if Unsigned L q then
    (if (pview parameter data s q).1 ∈ Fail then 1 else
      creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar (W (pview parameter data s q)) n J d)
        k (newCoin L p u0 (coinItems parameter data s L (P.erase q)))) else 0 with hA
  have hpoint : ∀ u0, coreG parameter data W wbar b0 Fail (withPair parameter data s p u0)
      (addPair parameter P p u0) L d n k ≤
      ((if Landed parameter (blockIndex u0) then
          (if (viewOf u0).1 ∈ Fail then 1 else 0) + Wv (viewOf u0) else 0) +
        (P.map fun q => if Landed parameter (blockIndex u0) then A q u0
          else candG parameter data W wbar Fail s P L d n k q).sum) +
      k * ((if Landed parameter (blockIndex u0) then creations Finset.univ landing GH k (newCoin L p u0 I)
          else hValueG parameter data W wbar b0 s P L d n k) + φ) + n * φ := by
    intro u0
    unfold coreG
    rw [hValueG_withPair wbar b0 hP hp0 L d n k u0]
    have hlist : ((addPair parameter P p u0).map (candG parameter data W wbar Fail (withPair parameter data s p u0)
        (addPair parameter P p u0) L d n k)).sum =
        (if Landed parameter (blockIndex u0) then
          candG parameter data W wbar Fail (withPair parameter data s p u0) (p :: P) L d n k p else 0) +
        (P.map fun q => if Landed parameter (blockIndex u0) then A q u0
          else candG parameter data W wbar Fail s P L d n k q).sum := by
      by_cases hl : Landed parameter (blockIndex u0)
      · have hmap : P.map (candG parameter data W wbar Fail (withPair parameter data s p u0) (p :: P) L d n k) =
            P.map fun q => A q u0 := List.map_congr_left fun q hq => by
          have h := candG_withPair (W := W) wbar Fail hP hp0 L d n k q hq u0
          unfold addPair at h
          simp only [if_pos hl] at h
          exact h
        unfold addPair
        simp only [if_pos hl, List.map_cons, List.sum_cons, hmap]
      · have hmap : P.map (candG parameter data W wbar Fail (withPair parameter data s p u0) P L d n k) =
            P.map fun q => candG parameter data W wbar Fail s P L d n k q := List.map_congr_left fun q hq => by
          have h := candG_withPair (W := W) wbar Fail hP hp0 L d n k q hq u0
          unfold addPair at h
          simp only [if_neg hl] at h
          exact h
        unfold addPair
        simp only [if_neg hl, zero_add, hmap]
    rw [hlist]
    gcongr
    by_cases hl : Landed parameter (blockIndex u0)
    · simp only [if_pos hl]
      exact candG_withPair_self wbar Fail hP hp0 L d n k u0
    · simp only [if_neg hl, le_refl]
  refine le_trans (pairE_mono hpoint) ?_
  simp only [pairE_add, pairE_const_mul, pairE_const, pairE_list_sum]
  have h1 : pairE (fun u0 => if Landed parameter (blockIndex u0) then
      (if (viewOf u0).1 ∈ Fail then 1 else 0) + Wv (viewOf u0) else 0) = landing * (φ + freshAvg Finset.univ Wv) := by
    rw [pairE_landed parameter (fun v => (if v.1 ∈ Fail then 1 else 0) + Wv v) 0, mul_zero, add_zero, freshAvg_add]
    rfl
  have h2 : ∀ q, pairE (fun u0 => if Landed parameter (blockIndex u0) then A q u0
      else candG parameter data W wbar Fail s P L d n k q) ≤ candG parameter data W wbar Fail s P L d n (k + 1) q := by
    intro q
    simp only [hA]
    unfold candG candValueG
    split_ifs
    · simp only [ite_self, pairE_const, le_refl]
    · exact creations_newCoin_le wbar hw (hW _) n d k _ L p
    · simp only [ite_self, pairE_const, le_refl]
  have h3 : pairE (fun u0 => if Landed parameter (blockIndex u0) then
      creations Finset.univ landing GH k (newCoin L p u0 I) else hValueG parameter data W wbar b0 s P L d n k) ≤
      hValueG parameter data W wbar b0 s P L d n (k + 1) :=
    creations_newCoin_le wbar hw (excessW_props hW hb0) n d k I L p
  have hfresh : landing * freshAvg Finset.univ Wv ≤ b0 + hValueG parameter data W wbar b0 s P L d n (k + 1) := by
    refine le_trans (fresh_forecastG wbar b0 hw I d n k) (add_le_add le_rfl ?_)
    unfold hValueG
    exact creations_le_succ Finset.univ_nonempty landing_le_one
      (virtualOnce_cons_le' wbar hw (excessW_props hW hb0) n d) (virtualOnce_perm' wbar n d) k I
  have hφ1 : landing * φ ≤ φ := mul_le_of_le_one_left' landing_le_one
  rw [h1]
  unfold coreG
  set S := (P.map (candG parameter data W wbar Fail s P L d n (k + 1))).sum
  set H := hValueG parameter data W wbar b0 s P L d n (k + 1)
  have hS : (P.map fun q => pairE fun u0 => if Landed parameter (blockIndex u0) then A q u0
      else candG parameter data W wbar Fail s P L d n k q).sum ≤ S :=
    List.sum_le_sum fun q _ => h2 q
  calc landing * (φ + freshAvg Finset.univ Wv) +
        (P.map fun q => pairE fun u0 => if Landed parameter (blockIndex u0) then A q u0
          else candG parameter data W wbar Fail s P L d n k q).sum +
        k * (pairE (fun u0 => if Landed parameter (blockIndex u0) then
          creations Finset.univ landing GH k (newCoin L p u0 I) else hValueG parameter data W wbar b0 s P L d n k) + φ) +
        n * φ
      ≤ φ + (b0 + H) + S + k * (H + φ) + n * φ := by
        rw [mul_add]
        gcongr
    _ = S + ((k : ℝ≥0∞) + 1) * (H + φ) + n * φ + b0 := by ring
    _ = _ := by push_cast; ring

end NewPairG

/-! ### Order and congruence -/

section OrderG

variable (parameter : PublicParameter) (data : PublicData) {W : View → Multiset View → ℝ≥0∞} (wbar b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight)))

variable {parameter data}

/-- The potential sees the state only through the views of its items. -/
theorem coreG_congr {s s' : State} {P : List Pair} (h : ∀ q ∈ P, pview parameter data s' q = pview parameter data s q)
    (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    coreG parameter data W wbar b0 Fail s' P L d n k = coreG parameter data W wbar b0 Fail s P L d n k := by
  have hcand : ∀ q ∈ P, candG parameter data W wbar Fail s' P L d n k q = candG parameter data W wbar Fail s P L d n k q := by
    intro q hq
    unfold candG candValueG
    rw [h q hq, coinItems_congr (fun r hr => h r (List.mem_of_mem_erase hr)) L]
  unfold coreG hValueG
  rw [List.map_congr_left hcand, coinItems_congr h L]

theorem potG_le_coreG (gate : State → Prop) (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ) :
    potG parameter data W wbar b0 Fail gate s P L d k ≤
      coreG parameter data W wbar b0 Fail s P L d (signatureLimit - L.length) k := by
  unfold potG
  split_ifs
  · exact bot_le
  · exact le_rfl

/-- A grown state with the same item views has no larger potential. -/
theorem potG_grow (hW : WitnessProps W) {gate : State → Prop}
    (hgate : ∀ s s' : State, Extends s s' → gate s → gate s') (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) {s s' : State}
    (hext : Extends s s') {P : List Pair}
    (hview : ∀ q ∈ P, pview parameter data s' q = pview parameter data s q) (L : QueryLog SigningSpec)
    (d : Multiset View) {k k' : ℕ} (hk : k ≤ k') :
    potG parameter data W wbar b0 Fail gate s' P L d k ≤ potG parameter data W wbar b0 Fail gate s P L d k' := by
  unfold potG
  by_cases hr : gate s' ∨ signatureLimit < L.length
  · rw [if_pos hr]; exact bot_le
  · have hr' : ¬(gate s ∨ signatureLimit < L.length) := fun h =>
      hr (h.imp (hgate s s' hext) id)
    rw [if_neg hr, if_neg hr', coreG_congr wbar b0 Fail hview]
    exact coreG_mono wbar b0 Fail hW hw hb0 s P L d _ hk

end OrderG

/-! ### The potential after signing a message for the first time -/

section SignPointG

variable (parameter : PublicParameter) (data : PublicData) (W : View → Multiset View → ℝ≥0∞) (wbar b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight))) (m : Message) (s : State) (P : List Pair) (L : QueryLog SigningSpec)
  (d : Multiset View)

/-- Bound for one outcome of a signing call. -/
noncomputable def canonG (n k : ℕ) (out : Run HashInput Coordinate (Option Signature) × State) : ℝ≥0∞ :=
  freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out +
  (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
      creations Finset.univ landing (fun J => upperO parameter data wbar m s n d (W (pview parameter data s q))
        (· = q) out J) k (restItems parameter data m s L (P.erase q))) else 0).sum +
  k * (creations Finset.univ landing (fun J => upperO parameter data wbar m s n d (excessW W b0) (fun _ => False) out J) k
      (restItems parameter data m s L P) + failMass Fail) +
  n * failMass Fail

/-- The bound for one signing outcome with the gate and the signature limit: zero once the gate is
on or no signature is left. -/
noncomputable def canonL (gate : State → Prop) (K : ℕ) (out : Run HashInput Coordinate (Option Signature) × State) :
    ℝ≥0∞ :=
  if gate s ∨ signatureLimit ≤ L.length then 0
  else canonG parameter data W wbar b0 Fail m s P L d (signatureLimit - (L.length + 1)) K out

end SignPointG

section SignPointMainG

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) {W : View → Multiset View → ℝ≥0∞} (wbar b0 : ℝ≥0∞)
  (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ) (m : Message)

/-- **The potential after one signing outcome.** -/
theorem sign_pointG_level (hW : WitnessProps W) {gate : State → Prop}
    (hgate : ∀ s s' : State, Extends s s' → gate s → gate s')
    (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    (hfail : ∀ ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (attempts budget : ℕ) (s : State) (P : List Pair) (L : QueryLog SigningSpec)
    (d : Multiset View) (R : List Coordinate) (hprep : Prepared initial s) (hP : PInv parameter data s P)
    (hD : DInv R d) (hC : CountInv parameter data Qtot s budget)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSourceLoop parameter data m attempts) budget s))
    (r : Option Signature) (hr : out.1.1 = some r) {k' K : ℕ} (hk : k' ≤ K) :
    potG parameter data W wbar b0 Fail gate out.2 (newPairs parameter data m s out.2 ++ P) (L ++ [⟨m, r⟩])
        (discAfter parameter data m s d out) k' ≤
      canonL parameter data W wbar b0 Fail m s P L d gate K out := by
  unfold canonL
  obtain ⟨_, hP', _, _, hview⟩ := sign_params tg initial model Fail Qtot hparse hfail attempts budget
    s P d R hprep hP hD hC out hout r hr
  have hext := interp_extends tg initial model _ budget s out hout
  have hpost := loop_post tg initial model parameter data m (fun ρ => hparse (m, ρ)) Fail hfail
    attempts budget s hprep out hout r hr
  have hshape := sign_shape parameter data Fail m hpost out rfl hr
  unfold potG
  by_cases hcase : gate out.2 ∨ signatureLimit < (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length
  · rw [if_pos hcase]; exact bot_le
  rw [if_neg hcase]
  have hreal : ¬gate s := fun h => hcase (Or.inl (hgate s out.2 hext h))
  have hlen : L.length < signatureLimit := by
    have := hcase
    simp only [List.length_append, List.length_singleton, not_or, not_lt] at this
    omega
  rw [if_neg (by push Not; exact ⟨hreal, hlen⟩)]
  have hn : signatureLimit - (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length = signatureLimit - (L.length + 1) := by simp
  rw [hn]
  set n := signatureLimit - (L.length + 1) with hndef
  have hnotnew : ∀ q ∈ P, q ∉ newPairs parameter data m s out.2 := by
    intro q hq hnew
    obtain ⟨_, h0, _⟩ := (mem_newPairs parameter data m s).1 hnew
    obtain ⟨u, hu, _⟩ := (hP.mem q).1 hq
    rw [h0] at hu; cases hu
  unfold coreG canonG
  rw [List.map_append, List.sum_append]
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) le_rfl
  · -- new pairs: only a failed fresh pair stays a candidate
    rcases hshape with ⟨hnew, _⟩ | ⟨ρ, u0, hnew, _, h0, hl, hs0, _, hfl, hsig⟩ | ⟨_, _, _, hnew, _⟩
    · unfold newPairs; rw [hnew]; simp
    · have hv : pview parameter data out.2 (m, ρ) = viewOf u0 := pview_of_cached h0
      have hlist : newPairs parameter data m s out.2 = [(m, ρ)] := by
        unfold newPairs; rw [hnew, Finset.toList_singleton]; rfl
      rw [hlist]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      refine le_trans ?_ (freshNewWeight_ge hr hs0 h0 hl (fun v => if v.1 ∈ Fail then 1 else 0))
      unfold candG
      rw [hv]
      split_ifs with hu hF hF'
      · exact le_rfl
      · exfalso
        rcases r with _ | sig
        · exact hF (hfl rfl)
        · exact not_unsigned_signed (m := m) (L := L) (sig := sig) (by rw [hsig sig rfl]; exact hu)
      · exact bot_le
      · exact le_rfl
    · unfold newPairs; rw [hnew]; simp
  · -- old candidates
    refine List.sum_le_sum fun q hq => ?_
    unfold candG
    by_cases hU' : Unsigned (L ++ [⟨m, r⟩] : QueryLog SigningSpec) q
    · have hU := unsigned_of_append hU'
      rw [if_pos hU', if_pos hU, hview q hq]
      split_ifs with hF
      · exact le_rfl
      · unfold candValueG
        rw [hview q hq, List.erase_append_right _ (hnotnew q hq),
          coinItems_after (P.erase q) fun q' hq' => hview q' (List.mem_of_mem_erase hq')]
        refine post_term_leO hw (hW _) _ n _ hk _ fun J => ?_
        refine upper_pointO hw (hW _) hP (· = q) out r hr Fail hshape (fun sig hsig _ heq => ?_) J
        subst hsig
        exact not_unsigned_signed (m := m) (L := L) (by rw [heq]; exact hU')
    · rw [if_neg hU']
      exact bot_le
  · -- the excess forecast
    refine mul_le_mul' (by exact_mod_cast hk) (add_le_add ?_ le_rfl)
    unfold hValueG
    rw [coinItems_after P hview]
    refine post_term_leO hw (excessW_props hW hb0) _ n _ hk _ fun J => ?_
    exact upper_pointO hw (excessW_props hW hb0) hP (fun _ => False) out r hr Fail hshape (fun _ _ _ h => h) J

/-- **The signing step in expectation**, for a message signed for the first time. -/
theorem sign_expectG_level (hW : WitnessProps W) (gate : State → Prop)
    (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    {Cmax : ℕ} (hfair : Fair wbar Cmax) (hb0 : b0 ≠ ⊤) (attempts budget K : ℕ) (s : State) (P : List Pair)
    (L : QueryLog SigningSpec) (hm : ∀ entry ∈ L, entry.1 ≠ m) (d : Multiset View) (hP : PInv parameter data s P)
    (hcount : cachedCount parameter data m s + attempts ≤ Cmax) :
    ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
        canonL parameter data W wbar b0 Fail m s P L d gate K out ≤
      potG parameter data W wbar b0 Fail gate s P L d K := by
  unfold canonL
  by_cases hcase : gate s ∨ signatureLimit ≤ L.length
  · simp only [if_pos hcase, mul_zero, tsum_zero]
    exact bot_le
  simp only [if_neg hcase]
  have hcase' : ¬gate s ∧ L.length < signatureLimit := by push Not at hcase; exact hcase
  have hlen := hcase'.2
  unfold potG
  rw [if_neg (by rintro (h | h); exact hcase'.1 h; omega)]
  set n := signatureLimit - (L.length + 1) with hn
  have hn1 : signatureLimit - L.length = n + 1 := by omega
  rw [hn1]
  have hparse' : ∀ ρ, model.parse (blk parameter data m ρ) = none := fun ρ => hparse (m, ρ)
  have hmass : ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] ≤ 1 :=
    tsum_probOutput_le_one
  have hFN : ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
      freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out ≤ failMass Fail := by
    have h := loop_bound_comb tg initial model parameter data m hparse' s (fun v => if v.1 ∈ Fail then 1 else 0)
      (fun _ _ => 0) 1 ENNReal.one_ne_top (fun v => by split_ifs <;> simp) (fun _ _ => zero_le)
      (shareOf wbar (landedCount parameter data m s)) (shareOf_ne_top hfair _) Cmax hfair.cmax (hfair.share_le _)
      attempts budget s (related_self s) hcount
    have hz : ∀ ρ, poolValue parameter data m s (fun _ _ => 0) ρ = 0 := by
      intro ρ
      unfold poolValue
      cases s.cache (blk parameter data m ρ) <;> simp
    simp only [hz, Finset.sum_const_zero, zero_tsub, mul_zero, add_zero] at h
    refine le_trans (ENNReal.tsum_le_tsum fun out => mul_le_mul_right le_self_add _) h
  have hT : ∀ q ∈ P, ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
      (if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
        creations Finset.univ landing (fun J => upperO parameter data wbar m s n d (W (pview parameter data s q))
          (· = q) out J) K (restItems parameter data m s L (P.erase q))) else 0) ≤
      candG parameter data W wbar Fail s P L d (n + 1) K q := by
    intro q _
    unfold candG
    split_ifs
    · rw [ENNReal.tsum_mul_right, mul_one]; exact hmass
    · unfold candValueG
      rw [creations_perm (virtualOnce_perm' wbar (n + 1) d) K _ _ (coinItems_perm parameter data m s L hm _)]
      have h := term_expectO tg initial model hparse' hfair (hW (pview parameter data s q)) hP (· = q)
        attempts budget K hcount (restItems parameter data m s L (P.erase q)) (n := n) (d := d)
      rwa [← erase_eq_filter' hP.nodup q] at h
    · simp
  have hH := term_expectO tg initial model (n := n) (d := d) hparse' hfair (excessW_props hW hb0) hP (fun _ => False)
    attempts budget K hcount (restItems parameter data m s L P)
  rw [filter_false'] at hH
  have hHv : hValueG parameter data W wbar b0 s P L d (n + 1) K =
      creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar (excessW W b0) (n + 1) J d) K
        (msgItems parameter data m s P ++ restItems parameter data m s L P) := by
    unfold hValueG
    exact creations_perm (virtualOnce_perm' wbar (n + 1) d) K _ _ (coinItems_perm parameter data m s L hm _)
  unfold canonG coreG
  simp only [mul_add, ENNReal.tsum_add]
  rw [tsum_list_sum]
  calc _ ≤ failMass Fail + (P.map (candG parameter data W wbar Fail s P L d (n + 1) K)).sum +
        (K * hValueG parameter data W wbar b0 s P L d (n + 1) K + K * failMass Fail) +
          n * failMass Fail := by
        refine add_le_add (add_le_add (add_le_add hFN (List.sum_le_sum hT)) (add_le_add ?_ ?_)) ?_
        · simp only [mul_left_comm _ (K : ℝ≥0∞), ENNReal.tsum_mul_left]
          rw [hHv]
          exact mul_le_mul_right hH _
        · rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' hmass
        · rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' hmass
    _ = _ := by push_cast; ring


end SignPointMainG

end LeanForest.Security.ForsPotential
