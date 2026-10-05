import LeanSphincs.BridgeForsPotential
import LeanSphincs.BridgeVirtualOnce

/-! The FORS potential for adversaries that never request a signature on the same message twice.
The virtual future gives every remaining signature a fresh uniform view and every item whose
message has not been signed one coin: only the single signing call of that message can select
it. The future loads are then those of the signatures alone, without the share of the cached
pairs that the per-slot coins of `BridgeForsPotential` add. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

section DefsO

variable (parameter : PublicParameter) (data : PublicData)

/-- No signing request so far was for the pair's message. -/
def MsgFresh (L : QueryLog SigningSpec) (p : Pair) : Prop := ∀ entry ∈ L, entry.1 ≠ p.1

/-- Views of the items whose message has not been signed: the items that keep a coin. -/
noncomputable def coinItems (s : State) (L : QueryLog SigningSpec) (P : List Pair) : List View :=
  items parameter data s (P.filter fun q => decide (MsgFresh L q))

variable (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- The forecast of a candidate. -/
noncomputable def candValueO (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View)
    (n k : ℕ) (p : Pair) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtualOnce Finset.univ wbar (witnessFn (pview parameter data s p)) n I d)
    k (coinItems parameter data s L (P.erase p))

/-- The excess forecast of a new pair. -/
noncomputable def hValueO (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtualOnce Finset.univ wbar (excess b0) n I d) k
    (coinItems parameter data s L P)

/-- The value of a candidate: one at a failing index, its forecast otherwise; zero once signed. -/
noncomputable def candO (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (p : Pair) : ℝ≥0∞ :=
  if Unsigned L p then
    (if (pview parameter data s p).1 ∈ Fail then 1 else candValueO parameter data wbar s P L d n k p)
  else 0

/-- The potential without the hit and transcript tests. -/
noncomputable def coreO (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    ℝ≥0∞ :=
  (P.map (candO parameter data wbar Fail s P L d n k)).sum +
    k * (hValueO parameter data wbar b0 s P L d n k + failMass Fail) + n * failMass Fail

variable (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)

/-- **The potential.** -/
noncomputable def potO (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ) :
    ℝ≥0∞ :=
  if Realized tg initial s ∨ signatureLimit < L.length then 0
  else coreO parameter data wbar b0 Fail s P L d (signatureLimit - L.length) k

end DefsO

/-! ### The virtual future of a list of items -/

section Basic

variable (wbar b0 : ℝ≥0∞)

theorem virtualOnce_cons_le' (hw : wbar ≤ 1) {f : Multiset View → ℝ≥0∞}
    (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤) (n : ℕ) (d : Multiset View) :
    ∀ v I, virtualOnce Finset.univ wbar f n I d ≤ virtualOnce Finset.univ wbar f n (v :: I) d :=
  fun v I => virtualOnce_le_cons Finset.univ_nonempty hw hf.1 hf.2.1 hf.2.2 n I v d

theorem virtualOnce_perm' {f : Multiset View → ℝ≥0∞} (n : ℕ) (d : Multiset View) :
    ∀ I I' : List View, I.Perm I' →
      virtualOnce Finset.univ wbar f n I d = virtualOnce Finset.univ wbar f n I' d :=
  fun _ _ h => virtualOnce_perm n h d

/-- A new candidate's forecast is at most the baseline plus one excess. -/
theorem fresh_forecastO (hw : wbar ≤ 1) (I : List View) (d : Multiset View) (n k : ℕ) :
    landing * freshAvg Finset.univ (fun v => creations Finset.univ landing
      (fun J => virtualOnce Finset.univ wbar (witnessFn v) n J d) k I) ≤
    b0 + creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar (excess b0) n J d) k I := by
  have hU : (Finset.univ : Finset View).Nonempty := Finset.univ_nonempty
  rw [← creations_freshAvg, ← creations_const_mul]
  have hpt : ∀ J, landing * freshAvg Finset.univ (fun v => virtualOnce Finset.univ wbar (witnessFn v) n J d) ≤
      b0 + virtualOnce Finset.univ wbar (excess b0) n J d := by
    intro J
    rw [← virtualOnce_freshAvg hU, ← virtualOnce_const_mul]
    calc virtualOnce Finset.univ wbar (fun D => landing * freshAvg Finset.univ fun v => witnessFn v D) n J d
        ≤ virtualOnce Finset.univ wbar (fun D => b0 + excess b0 D) n J d :=
          virtualOnce_mono_base (fun D => show price D ≤ b0 + (price D - b0) from le_add_tsub) n J d
      _ = b0 + virtualOnce Finset.univ wbar (excess b0) n J d := by
          rw [virtualOnce_add hU (fun _ => b0) (excess b0), virtualOnce_const hU hw]
  calc creations Finset.univ landing (fun J => landing * freshAvg Finset.univ fun v =>
        virtualOnce Finset.univ wbar (witnessFn v) n J d) k I
      ≤ creations Finset.univ landing (fun J => b0 + virtualOnce Finset.univ wbar (excess b0) n J d) k I :=
        creations_mono hpt k I
    _ = _ := by rw [creations_add (fun _ => b0), creations_const Finset.univ_nonempty landing_le_one]

end Basic

/-! ### A new pair -/

section NewPairO

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- The coin items gained by a new landed pair. -/
noncomputable def newCoin (L : QueryLog SigningSpec) (p : Pair) (u0 u1 : HashOutput) (I : List View) : List View :=
  if MsgFresh L p then viewOf u0 u1 :: I else I

variable {parameter data}

theorem coinItems_withPair {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) (L : QueryLog SigningSpec) (u0 u1 : HashOutput)
    (l : List Pair) (hl : ∀ q ∈ l, q ∈ P) :
    coinItems parameter data (withPair parameter data s p u0 u1) L l = coinItems parameter data s L l := by
  have hpP := not_mem_of_fresh hP hp0
  unfold coinItems
  exact items_withPair s p u0 u1 _ fun h => hpP (hl p (List.mem_of_mem_filter h))

theorem coinItems_cons_withPair {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) (L : QueryLog SigningSpec) (u0 u1 : HashOutput)
    (l : List Pair) (hl : ∀ q ∈ l, q ∈ P) :
    coinItems parameter data (withPair parameter data s p u0 u1) L (p :: l) =
      newCoin L p u0 u1 (coinItems parameter data s L l) := by
  have hpP := not_mem_of_fresh hP hp0
  have hpl : p ∉ l := fun h => hpP (hl p h)
  unfold coinItems newCoin items
  by_cases hf : MsgFresh L p
  · rw [List.filter_cons_of_pos (by simpa using hf), List.map_cons, pview_withPair_self, if_pos hf]
    exact congrArg _ (items_withPair s p u0 u1 _ fun h => hpl (List.mem_of_mem_filter h))
  · rw [List.filter_cons_of_neg (by simpa using hf), if_neg hf]
    exact items_withPair s p u0 u1 _ fun h => hpl (List.mem_of_mem_filter h)

/-- Old candidates after a new pair. -/
theorem candO_withPair {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (q : Pair) (hq : q ∈ P) (u0 u1 : HashOutput) :
    candO parameter data wbar Fail (withPair parameter data s p u0 u1) (addPair parameter P p u0) L d n k q =
      if Landed parameter (blockIndex u0) then
        (if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
          creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar (witnessFn (pview parameter data s q))
            n J d) k (newCoin L p u0 u1 (coinItems parameter data s L (P.erase q)))) else 0)
      else candO parameter data wbar Fail s P L d n k q := by
  have hpP := not_mem_of_fresh hP hp0
  have hqp : q ≠ p := fun h => hpP (h ▸ hq)
  have hv := pview_withPair_other (parameter := parameter) (data := data) s p q hqp u0 u1
  have hsub : ∀ r ∈ P.erase q, r ∈ P := fun r hr => List.mem_of_mem_erase hr
  by_cases hl : Landed parameter (blockIndex u0)
  · rw [if_pos hl]
    unfold candO candValueO addPair
    rw [if_pos hl, hv]
    have herase : (p :: P).erase q = p :: P.erase q := List.erase_cons_tail (by simpa using hqp.symm)
    rw [herase, coinItems_cons_withPair hP hp0 L u0 u1 _ hsub]
  · rw [if_neg hl]
    unfold candO candValueO addPair
    rw [if_neg hl, hv, coinItems_withPair hP hp0 L u0 u1 _ hsub]

/-- The new candidate itself. -/
theorem candO_withPair_self {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (u0 u1 : HashOutput) :
    candO parameter data wbar Fail (withPair parameter data s p u0 u1) (p :: P) L d n k p ≤
      (if (viewOf u0 u1).1 ∈ Fail then 1 else 0) +
        creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar (witnessFn (viewOf u0 u1)) n J d) k
          (coinItems parameter data s L P) := by
  unfold candO candValueO
  rw [pview_withPair_self, List.erase_cons_head, coinItems_withPair hP hp0 L u0 u1 _ fun r hr => hr]
  split_ifs <;> simp

theorem hValueO_withPair {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (u0 u1 : HashOutput) :
    hValueO parameter data wbar b0 (withPair parameter data s p u0 u1) (addPair parameter P p u0) L d n k =
      if Landed parameter (blockIndex u0) then
        creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar (excess b0) n J d) k
          (newCoin L p u0 u1 (coinItems parameter data s L P))
      else hValueO parameter data wbar b0 s P L d n k := by
  unfold hValueO addPair
  split_ifs
  · rw [coinItems_cons_withPair hP hp0 L u0 u1 _ fun r hr => hr]
  · rw [coinItems_withPair hP hp0 L u0 u1 _ fun r hr => hr]

theorem candValueO_mono (hw : wbar ≤ 1) (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View)
    (n : ℕ) {k k' : ℕ} (hk : k ≤ k') (p : Pair) :
    candValueO parameter data wbar s P L d n k p ≤ candValueO parameter data wbar s P L d n k' p :=
  creations_mono_count Finset.univ_nonempty landing_le_one
    (virtualOnce_cons_le' wbar hw (witness_props _) n d) (virtualOnce_perm' wbar n d) hk _

theorem hValueO_mono (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (s : State) (P : List Pair) (L : QueryLog SigningSpec)
    (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    hValueO parameter data wbar b0 s P L d n k ≤ hValueO parameter data wbar b0 s P L d n k' :=
  creations_mono_count Finset.univ_nonempty landing_le_one
    (virtualOnce_cons_le' wbar hw (excess_props b0 hb0) n d) (virtualOnce_perm' wbar n d) hk _

theorem candO_mono (hw : wbar ≤ 1) (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View)
    (n : ℕ) {k k' : ℕ} (hk : k ≤ k') (q : Pair) :
    candO parameter data wbar Fail s P L d n k q ≤ candO parameter data wbar Fail s P L d n k' q := by
  unfold candO
  split_ifs
  · exact le_rfl
  · exact candValueO_mono wbar hw s P L d n hk q
  · exact le_rfl

theorem coreO_mono (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (s : State) (P : List Pair) (L : QueryLog SigningSpec)
    (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    coreO parameter data wbar b0 Fail s P L d n k ≤ coreO parameter data wbar b0 Fail s P L d n k' := by
  unfold coreO
  refine add_le_add (add_le_add (List.sum_le_sum fun q _ => candO_mono wbar Fail hw s P L d n hk q) ?_) le_rfl
  exact mul_le_mul' (by exact_mod_cast hk) (add_le_add (hValueO_mono wbar b0 hw hb0 s P L d n hk) le_rfl)

/-- Creations with one more future pair dominate an extra coin item. -/
theorem creations_newCoin_le (hw : wbar ≤ 1) {f : Multiset View → ℝ≥0∞}
    (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤) (n : ℕ) (d : Multiset View) (k : ℕ) (I : List View)
    (L : QueryLog SigningSpec) (p : Pair) :
    pairE (fun u0 u1 => if Landed parameter (blockIndex u0) then
        creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar f n J d) k (newCoin L p u0 u1 I)
      else creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar f n J d) k I) ≤
      creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar f n J d) (k + 1) I := by
  set G : List View → ℝ≥0∞ := fun J => virtualOnce Finset.univ wbar f n J d with hG
  by_cases hfr : MsgFresh L p
  · have h : (fun u0 u1 => if Landed parameter (blockIndex u0) then creations Finset.univ landing G k
          (newCoin L p u0 u1 I) else creations Finset.univ landing G k I) =
        fun u0 u1 => if Landed parameter (blockIndex u0) then
          (fun v => creations Finset.univ landing G k (v :: I)) (viewOf u0 u1)
          else creations Finset.univ landing G k I := by
      funext u0 u1
      simp only [newCoin, if_pos hfr]
    rw [h, pairE_landed parameter (fun v => creations Finset.univ landing G k (v :: I))
      (creations Finset.univ landing G k I)]
    simp only [creations]
    exact le_of_eq (add_comm _ _)
  · have h : (fun u0 u1 => if Landed parameter (blockIndex u0) then creations Finset.univ landing G k
          (newCoin L p u0 u1 I) else creations Finset.univ landing G k I) =
        fun _ _ => creations Finset.univ landing G k I := by
      funext u0 u1
      simp only [newCoin, if_neg hfr, ite_self]
    rw [h, pairE_const]
    exact creations_le_succ Finset.univ_nonempty landing_le_one
      (virtualOnce_cons_le' wbar hw hf n d) (virtualOnce_perm' wbar n d) k I

/-- **A new pair.** Touching a new pair costs one future pair and at most the baseline. -/
theorem coreO_newPair (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) {s : State} {P : List Pair}
    (hP : PInv parameter data s P) {p : Pair} (hp0 : s.cache (pblk parameter data p 0) = none)
    (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    pairE (fun u0 u1 => coreO parameter data wbar b0 Fail (withPair parameter data s p u0 u1)
      (addPair parameter P p u0) L d n k) ≤ coreO parameter data wbar b0 Fail s P L d n (k + 1) + b0 := by
  set I := coinItems parameter data s L P with hI
  set W : View → ℝ≥0∞ := fun v =>
    creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar (witnessFn v) n J d) k I with hW
  set GH : List View → ℝ≥0∞ := fun J => virtualOnce Finset.univ wbar (excess b0) n J d with hGH
  set φ := failMass Fail with hφ
  set A : Pair → HashOutput → HashOutput → ℝ≥0∞ := fun q u0 u1 => if Unsigned L q then
    (if (pview parameter data s q).1 ∈ Fail then 1 else
      creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar (witnessFn (pview parameter data s q)) n J d)
        k (newCoin L p u0 u1 (coinItems parameter data s L (P.erase q)))) else 0 with hA
  -- pointwise upper bound
  have hpoint : ∀ u0 u1, coreO parameter data wbar b0 Fail (withPair parameter data s p u0 u1)
      (addPair parameter P p u0) L d n k ≤
      ((if Landed parameter (blockIndex u0) then
          (if (viewOf u0 u1).1 ∈ Fail then 1 else 0) + W (viewOf u0 u1) else 0) +
        (P.map fun q => if Landed parameter (blockIndex u0) then A q u0 u1
          else candO parameter data wbar Fail s P L d n k q).sum) +
      k * ((if Landed parameter (blockIndex u0) then creations Finset.univ landing GH k (newCoin L p u0 u1 I)
          else hValueO parameter data wbar b0 s P L d n k) + φ) + n * φ := by
    intro u0 u1
    unfold coreO
    rw [hValueO_withPair wbar b0 hP hp0 L d n k u0 u1]
    have hlist : ((addPair parameter P p u0).map (candO parameter data wbar Fail (withPair parameter data s p u0 u1)
        (addPair parameter P p u0) L d n k)).sum =
        (if Landed parameter (blockIndex u0) then
          candO parameter data wbar Fail (withPair parameter data s p u0 u1) (p :: P) L d n k p else 0) +
        (P.map fun q => if Landed parameter (blockIndex u0) then A q u0 u1
          else candO parameter data wbar Fail s P L d n k q).sum := by
      by_cases hl : Landed parameter (blockIndex u0)
      · have hmap : P.map (candO parameter data wbar Fail (withPair parameter data s p u0 u1) (p :: P) L d n k) =
            P.map fun q => A q u0 u1 := List.map_congr_left fun q hq => by
          have h := candO_withPair wbar Fail hP hp0 L d n k q hq u0 u1
          unfold addPair at h
          simp only [if_pos hl] at h
          exact h
        unfold addPair
        simp only [if_pos hl, List.map_cons, List.sum_cons, hmap]
      · have hmap : P.map (candO parameter data wbar Fail (withPair parameter data s p u0 u1) P L d n k) =
            P.map fun q => candO parameter data wbar Fail s P L d n k q := List.map_congr_left fun q hq => by
          have h := candO_withPair wbar Fail hP hp0 L d n k q hq u0 u1
          unfold addPair at h
          simp only [if_neg hl] at h
          exact h
        unfold addPair
        simp only [if_neg hl, zero_add, hmap]
    rw [hlist]
    gcongr
    by_cases hl : Landed parameter (blockIndex u0)
    · simp only [if_pos hl]
      exact candO_withPair_self wbar Fail hP hp0 L d n k u0 u1
    · simp only [if_neg hl, le_refl]
  refine le_trans (pairE_mono hpoint) ?_
  -- expectations
  simp only [pairE_add, pairE_const_mul, pairE_const, pairE_list_sum]
  have h1 : pairE (fun u0 u1 => if Landed parameter (blockIndex u0) then
      (if (viewOf u0 u1).1 ∈ Fail then 1 else 0) + W (viewOf u0 u1) else 0) = landing * (φ + freshAvg Finset.univ W) := by
    rw [pairE_landed parameter (fun v => (if v.1 ∈ Fail then 1 else 0) + W v) 0, mul_zero, add_zero, freshAvg_add]
    rfl
  have h2 : ∀ q, pairE (fun u0 u1 => if Landed parameter (blockIndex u0) then A q u0 u1
      else candO parameter data wbar Fail s P L d n k q) ≤ candO parameter data wbar Fail s P L d n (k + 1) q := by
    intro q
    simp only [hA]
    unfold candO candValueO
    split_ifs
    · simp only [ite_self, pairE_const, le_refl]
    · exact creations_newCoin_le wbar hw (witness_props _) n d k _ L p
    · simp only [ite_self, pairE_const, le_refl]
  have h3 : pairE (fun u0 u1 => if Landed parameter (blockIndex u0) then
      creations Finset.univ landing GH k (newCoin L p u0 u1 I) else hValueO parameter data wbar b0 s P L d n k) ≤
      hValueO parameter data wbar b0 s P L d n (k + 1) :=
    creations_newCoin_le wbar hw (excess_props b0 hb0) n d k I L p
  -- the new candidate is paid by the baseline and one excess
  have hfresh : landing * freshAvg Finset.univ W ≤ b0 + hValueO parameter data wbar b0 s P L d n (k + 1) := by
    refine le_trans (fresh_forecastO wbar b0 hw I d n k) (add_le_add le_rfl ?_)
    unfold hValueO
    exact creations_le_succ Finset.univ_nonempty landing_le_one
      (virtualOnce_cons_le' wbar hw (excess_props b0 hb0) n d) (virtualOnce_perm' wbar n d) k I
  have hφ1 : landing * φ ≤ φ := mul_le_of_le_one_left' landing_le_one
  rw [h1]
  unfold coreO
  set S := (P.map (candO parameter data wbar Fail s P L d n (k + 1))).sum
  set H := hValueO parameter data wbar b0 s P L d n (k + 1)
  have hS : (P.map fun q => pairE fun u0 u1 => if Landed parameter (blockIndex u0) then A q u0 u1
      else candO parameter data wbar Fail s P L d n k q).sum ≤ S :=
    List.sum_le_sum fun q _ => h2 q
  calc landing * (φ + freshAvg Finset.univ W) +
        (P.map fun q => pairE fun u0 u1 => if Landed parameter (blockIndex u0) then A q u0 u1
          else candO parameter data wbar Fail s P L d n k q).sum +
        k * (pairE (fun u0 u1 => if Landed parameter (blockIndex u0) then
          creations Finset.univ landing GH k (newCoin L p u0 u1 I) else hValueO parameter data wbar b0 s P L d n k) + φ) +
        n * φ
      ≤ φ + (b0 + H) + S + k * (H + φ) + n * φ := by
        rw [mul_add]
        gcongr
    _ = S + ((k : ℝ≥0∞) + 1) * (H + φ) + n * φ + b0 := by ring
    _ = _ := by push_cast; ring

end NewPairO

/-! ### Order and congruence -/

section OrderO

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

variable {parameter data}

theorem coinItems_congr {s s' : State} {l : List Pair} (h : ∀ q ∈ l, pview parameter data s' q = pview parameter data s q)
    (L : QueryLog SigningSpec) : coinItems parameter data s' L l = coinItems parameter data s L l :=
  items_congr fun q hq => h q (List.mem_of_mem_filter hq)

/-- The potential sees the state only through the views of its items. -/
theorem coreO_congr {s s' : State} {P : List Pair} (h : ∀ q ∈ P, pview parameter data s' q = pview parameter data s q)
    (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    coreO parameter data wbar b0 Fail s' P L d n k = coreO parameter data wbar b0 Fail s P L d n k := by
  have hcand : ∀ q ∈ P, candO parameter data wbar Fail s' P L d n k q = candO parameter data wbar Fail s P L d n k q := by
    intro q hq
    unfold candO candValueO
    rw [h q hq, coinItems_congr (fun r hr => h r (List.mem_of_mem_erase hr)) L]
  unfold coreO hValueO
  rw [List.map_congr_left hcand, coinItems_congr h L]

theorem potO_le_coreO (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
    (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ) :
    potO parameter data wbar b0 Fail tg initial s P L d k ≤
      coreO parameter data wbar b0 Fail s P L d (signatureLimit - L.length) k := by
  unfold potO
  split_ifs
  · exact bot_le
  · exact le_rfl

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)

/-- A grown state with the same item views has no larger potential. -/
theorem potO_grow (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) {s s' : State} (hext : Extends s s') {P : List Pair}
    (hview : ∀ q ∈ P, pview parameter data s' q = pview parameter data s q) (L : QueryLog SigningSpec)
    (d : Multiset View) {k k' : ℕ} (hk : k ≤ k') :
    potO parameter data wbar b0 Fail tg initial s' P L d k ≤ potO parameter data wbar b0 Fail tg initial s P L d k' := by
  unfold potO
  by_cases hr : Realized tg initial s' ∨ signatureLimit < L.length
  · rw [if_pos hr]; exact bot_le
  · have hr' : ¬(Realized tg initial s ∨ signatureLimit < L.length) := fun h =>
      hr (h.imp (realized_of_extends tg initial hext) id)
    rw [if_neg hr, if_neg hr', coreO_congr wbar b0 Fail hview]
    exact coreO_mono wbar b0 Fail hw hb0 s P L d _ hk

end OrderO

/-! ### Paid programs -/

section GoodO

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A program whose final value is paid by the potential and the baseline payments. -/
def GoodO (L : QueryLog SigningSpec) (prog : OracleComp CostSpec HiddenBridge.Outcome) : Prop :=
  ∀ budget (s : State) (P : List Pair) (d : Multiset View) (R : List Coordinate),
    Prepared initial s → PInv parameter data s P → DInv R d → CountInv parameter data Qtot s budget →
      ∑' out, Pr[= out | interp tg initial model prog budget s] * finalValue parameter data tg initial R out ≤
        potO parameter data wbar b0 Fail tg initial s P L d budget + b0 * expectedFlagged tg initial model prog budget s

theorem goodO_draw (L : QueryLog SigningSpec) (draw : ℕ)
    (next : Fin (draw + 1) → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodO parameter data wbar b0 Fail Qtot tg initial model L (next v)) :
    GoodO parameter data wbar b0 Fail Qtot tg initial model L
      (liftM (CostSpec.query (.inl (.inl draw))) >>= next) := by
  intro budget s P d R hprep hP hD hC
  unfold expectedFlagged
  rw [interp_draw, tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
  calc _ ≤ ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
        (potO parameter data wbar b0 Fail tg initial s P L d budget +
          b0 * expectedFlagged tg initial model (next v) budget s) :=
        ENNReal.tsum_le_tsum fun v => mul_le_mul_right (h v budget s P d R hprep hP hD hC) _
    _ ≤ _ := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
        refine add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) (le_of_eq ?_)
        unfold expectedFlagged
        simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

/-- The sibling of a new pair, presampled after the first read. -/
theorem new_pair_boundO (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (L : QueryLog SigningSpec)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodO parameter data wbar b0 Fail Qtot tg initial model L (next v))
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) (P : List Pair) (d : Multiset View) (R : List Coordinate)
    (hprep : Prepared initial s) (hP : PInv parameter data s P) (hD : DInv R d)
    (hC : CountInv parameter data Qtot s budget) (p : Pair)
    (hp0 : s.cache (pblk parameter data p 0) = none) (hp1 : s.cache (pblk parameter data p 1) = none)
    (call : Fin 2) :
    ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        ∑' out, Pr[= out | interp tg initial model (next u) (budget - 1)
          (s.store (pblk parameter data p call) u)] * finalValue parameter data tg initial R out ≤
      potO parameter data wbar b0 Fail tg initial s P L d budget +
        b0 * ((if Realized tg initial s then 0 else 1) +
          ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
            expectedFlagged tg initial model (next u) (budget - 1) (s.store (pblk parameter data p call) u)) := by
  set y := pblk parameter data p (if call = 0 then 1 else 0) with hy
  have hstate : ∀ u u', (s.store (pblk parameter data p call) u).store y u' =
      if call = 0 then withPair parameter data s p u u' else withPair parameter data s p u' u := by
    intro u u'
    fin_cases call
    · rfl
    · simp only [hy, Fin.mk_one, one_ne_zero, if_false, withPair]
      exact store_comm s _ _ (Ne.symm (pblk_ne_call parameter data p)) u u'
  have hsib : ∀ u, (s.store (pblk parameter data p call) u).cache y = none := by
    intro u
    have hne : y ≠ pblk parameter data p call := by
      fin_cases call
      · exact Ne.symm (pblk_ne_call parameter data p)
      · exact pblk_ne_call parameter data p
    rw [store_cache_ne s _ _ hne]
    fin_cases call
    · exact hp1
    · exact hp0
  have hxfresh : s.cache (pblk parameter data p call) = none := by
    fin_cases call
    · exact hp0
    · exact hp1
  have hone : ∀ u, ∑' out, Pr[= out | interp tg initial model (next u) (budget - 1)
        (s.store (pblk parameter data p call) u)] * finalValue parameter data tg initial R out ≤
      ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (potO parameter data wbar b0 Fail tg initial ((s.store (pblk parameter data p call) u).store y u')
          (addPair parameter P p (if call = 0 then u else u')) L d (budget - 1) +
        b0 * expectedFlagged tg initial model (next u) (budget - 1)
          ((s.store (pblk parameter data p call) u).store y u')) := by
    intro u
    refine le_trans (interp_presample_le tg initial model y (hkind _ _) (next u) (budget - 1) _ _
      (fun out s' hs' => finalValue_presample tg initial parameter data y (hkind _ _) R out s' hs')) ?_
    rw [presample_fresh y _ (hsib u), tsum_probOutput_map_mul]
    refine ENNReal.tsum_le_tsum fun u' => mul_le_mul_right ?_ _
    rw [hstate u u']
    have hprep2 : ∀ a b, Prepared initial (withPair parameter data s p a b) := by
      intro a b
      unfold withPair
      exact prepared_store initial _ (prepared_store initial s hprep _ a hp0) _ b
        (by rw [store_cache_ne s _ _ (Ne.symm (pblk_ne_call parameter data p))]; exact hp1)
    have hC2 : ∀ a b, CountInv parameter data Qtot (withPair parameter data s p a b) (budget - 1) := by
      intro a b m
      have h1 := count_withPair (parameter := parameter) (data := data) m s p a b
      have h2 := hC m
      omega
    split_ifs with hc
    · exact h u (budget - 1) _ _ d R (hprep2 u u') (pinv_withPair hP hp0 u u') hD (hC2 u u')
    · exact h u (budget - 1) _ _ d R (hprep2 u' u) (pinv_withPair hP hp0 u' u) hD (hC2 u' u)
  refine le_trans (ENNReal.tsum_le_tsum fun u => mul_le_mul_right (hone u) _) ?_
  simp only [mul_add, ENNReal.tsum_add]
  rw [← add_assoc]
  refine add_le_add ?_ ?_
  swap
  · refine le_of_eq ?_
    have hu : ∀ u, ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] *
        expectedFlagged tg initial model (next u) (budget - 1)
          ((s.store (pblk parameter data p call) u).store y u') =
        expectedFlagged tg initial model (next u) (budget - 1) (s.store (pblk parameter data p call) u) := by
      intro u
      have hmap := tsum_probOutput_map_mul ($ᵗ HashOutput : ProbComp HashOutput)
        (fun u' => (s.store (pblk parameter data p call) u).store y u')
        (fun s2 => expectedFlagged tg initial model (next u) (budget - 1) s2)
      rw [← hmap, ← presample_fresh y _ (hsib u)]
      unfold expectedFlagged
      exact interp_presample_eq tg initial model y (hkind _ _) (next u) (budget - 1) _
        (fun run => (flaggedCount tg run.2.2.2 : ℝ≥0∞))
    simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left, hu]
  · by_cases hr : Realized tg initial s ∨ signatureLimit < L.length
    · refine le_of_eq_of_le (ENNReal.tsum_eq_zero.2 fun u => ?_) bot_le
      rw [ENNReal.tsum_eq_zero.2 fun u' => ?_, mul_zero]
      unfold potO
      rw [if_pos (hr.imp (realized_of_extends tg initial ((extends_store s _ u hxfresh).trans
        (extends_store _ y u' (hsib u)))) id), mul_zero]
    · have hreal : ¬Realized tg initial s := fun h' => hr (Or.inl h')
      rw [if_neg hreal, mul_one]
      have hpot : potO parameter data wbar b0 Fail tg initial s P L d budget =
          coreO parameter data wbar b0 Fail s P L d (signatureLimit - L.length) (budget - 1 + 1) := by
        unfold potO; rw [if_neg hr, Nat.sub_add_cancel hb]
      rw [hpot]
      refine le_trans ?_ (coreO_newPair wbar b0 Fail hw hb0 hP hp0 L d _ (budget - 1))
      unfold pairE
      have hle : ∀ u u', potO parameter data wbar b0 Fail tg initial ((s.store (pblk parameter data p call) u).store y u')
          (addPair parameter P p (if call = 0 then u else u')) L d (budget - 1) ≤
          if call = 0 then coreO parameter data wbar b0 Fail (withPair parameter data s p u u') (addPair parameter P p u)
            L d (signatureLimit - L.length) (budget - 1)
          else coreO parameter data wbar b0 Fail (withPair parameter data s p u' u) (addPair parameter P p u') L d
            (signatureLimit - L.length) (budget - 1) := by
        intro u u'
        rw [hstate u u']
        split_ifs
        · exact potO_le_coreO wbar b0 Fail tg initial _ _ L d _
        · exact potO_le_coreO wbar b0 Fail tg initial _ _ L d _
      refine le_trans (ENNReal.tsum_le_tsum fun u => mul_le_mul_right
        (ENNReal.tsum_le_tsum fun u' => mul_le_mul_right (hle u u') _) _) (le_of_eq ?_)
      split_ifs with hc
      · rfl
      · exact tsum_swap2 _ (fun a b => coreO parameter data wbar b0 Fail (withPair parameter data s p a b)
          (addPair parameter P p a) L d (signatureLimit - L.length) (budget - 1))

/-- **One ordinary query.** -/
theorem goodO_ordinary (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (L : QueryLog SigningSpec) (x : HashInput)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, GoodO parameter data wbar b0 Fail Qtot tg initial model L (next v)) :
    GoodO parameter data wbar b0 Fail Qtot tg initial model L
      (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) := by
  intro budget s P d R hprep hP hD hC
  by_cases hb : 1 ≤ budget
  swap
  · rw [interp_ordinary, if_neg hb, tsum_probOutput_pure_mul, finalValue_abort]
    exact bot_le
  rw [finalValue_ordinary tg initial model parameter data R x next budget hb s,
    flagged_ordinary tg initial model x next budget hb s]
  by_cases hnew : ∃ p call, x = pblk parameter data p call ∧ s.cache (pblk parameter data p 0) = none
  · obtain ⟨p, call, rfl, hp0⟩ := hnew
    have hp1 := hP.first p hp0
    have hfresh : s.cache (pblk parameter data p call) = none := by
      fin_cases call
      · exact hp0
      · exact hp1
    rw [ordinaryStep, hparse p call]
    simp only
    rw [readOutside_fresh _ s hfresh, tsum_probOutput_map_mul, tsum_probOutput_map_mul]
    have hpay : (pays tg initial s (.inl (.inr (.inl (pblk parameter data p call)))) : ℝ≥0∞) =
        if Realized tg initial s then 0 else 1 := by
      by_cases hr : Realized tg initial s <;> simp [pays, hdigest p call, hr]
    rw [hpay]
    exact new_pair_boundO parameter data wbar b0 Fail Qtot tg initial model hkind hw hb0 L next h budget hb s P d R
      hprep hP hD hC p hp0 hp1 call
  · calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] *
          (potO parameter data wbar b0 Fail tg initial s P L d budget +
            b0 * expectedFlagged tg initial model (next r.1) (budget - 1) r.2) := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support (ordinaryStep model x s.known s)
          · refine mul_le_mul_right ?_ _
            have hext := ordinaryStep_extends model x s r hr
            obtain ⟨hP', hview⟩ := same_items parameter data hext
              (ordinaryStep_cache_ne model x s r hr) hnew hP
            have hcnt : CountInv parameter data Qtot r.2 (budget - 1) := by
              intro m
              have h1 : cachedCount parameter data m r.2 ≤ cachedCount parameter data m s + 1 := by
                rw [cachedCount_eq, cachedCount_eq]
                exact costStep_card_le model _ (.inl (.inr (.inl x))) s r (by rw [costStep_ordinary]; exact hr)
              have h2 := hC m
              omega
            refine le_trans (h r.1 (budget - 1) r.2 P d R
              (fun i o hi => hext.1 i o (hprep i o hi)) hP' hD hcnt) (add_le_add ?_ le_rfl)
            exact potO_grow wbar b0 Fail tg initial hw hb0 hext hview L d (Nat.sub_le _ _)
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ ≤ _ := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
          refine add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) ?_
          refine le_add_left (le_of_eq ?_)
          simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

/-- **Leaf.** A FORS cover with no decided hit is paid by the potential. -/
theorem goodO_pure (hw : wbar ≤ 1) (L : QueryLog SigningSpec) (forgery : Forgery) (verified : Bool) :
    GoodO parameter data wbar b0 Fail Qtot tg initial model L (pure (forgery, L, verified)) := by
  intro budget s P d R hprep hP hD hC
  rw [interp_pure, tsum_probOutput_pure_mul]
  refine le_trans ?_ le_self_add
  unfold finalValue
  simp only [Option.elim, List.append_nil]
  split_ifs with hcov
  swap
  · exact bot_le
  obtain ⟨⟨hvalid, digest, hdig, hland, hunsigned, hcovered⟩, hreal⟩ := hcov
  set q : Pair := (forgery.message, forgery.signature.randomness) with hq
  unfold HiddenBridge.cachedDigest at hdig
  cases h0 : s.cache (pblk parameter data q 0) with
  | none =>
      have h0' : s.cache (tweakableHashInput parameter (.message 0)
          (messageDigestPayload data.root forgery.message forgery.signature.randomness)) = none := h0
      rw [h0'] at hdig; cases hdig
  | some a =>
      cases h1 : s.cache (pblk parameter data q 1) with
      | none =>
          have h0' : s.cache (tweakableHashInput parameter (.message 0)
              (messageDigestPayload data.root forgery.message forgery.signature.randomness)) = some a := h0
          have h1' : s.cache (tweakableHashInput parameter (.message 1)
              (messageDigestPayload data.root forgery.message forgery.signature.randomness)) = none := h1
          rw [h0', h1'] at hdig; cases hdig
      | some b =>
          have h0' : s.cache (tweakableHashInput parameter (.message 0)
              (messageDigestPayload data.root forgery.message forgery.signature.randomness)) = some a := h0
          have h1' : s.cache (tweakableHashInput parameter (.message 1)
              (messageDigestPayload data.root forgery.message forgery.signature.randomness)) = some b := h1
          rw [h0', h1'] at hdig
          have hdig' : truncateMessageDigest a b = digest := by
            simpa using hdig
          subst hdig'
          have hlanded : LandedIn parameter data s q := ⟨a, h0, by rwa [Completeness.digestIndex_truncate] at hland⟩
          have hqP := (hP.mem q).2 hlanded
          have hv : pview parameter data s q = Lifetime.localDigestView (truncateMessageDigest a b) := by
            simp only [pview, h0, h1, Option.elim, viewOf]
          unfold potO
          rw [if_neg (by
            rintro (h | h)
            · exact hreal h
            · exact absurd hvalid (by simp [SigningTranscript.Valid]; omega))]
          unfold coreO
          refine le_trans ?_ (le_trans (List.le_sum_of_mem (List.mem_map_of_mem hqP)) (le_self_add.trans le_self_add))
          unfold candO
          rw [if_pos (show Unsigned L q from hunsigned)]
          split_ifs
          · exact le_rfl
          · unfold candValueO
            calc (1 : ℝ≥0∞) ≤ witnessFn (pview parameter data s q) d := by
                  unfold witnessFn
                  rw [hv]
                  exact_mod_cast witness_pos_of_covered hD _ hcovered
              _ ≤ virtualOnce Finset.univ wbar (witnessFn (pview parameter data s q))
                    (signatureLimit - L.length) (coinItems parameter data s L (P.erase q)) d :=
                  base_le_virtualOnce Finset.univ_nonempty hw (witness_props _).1 (witness_props _).2.1
                    (witness_props _).2.2 _ _ d
              _ ≤ _ := creations_mono_count (k := 0) Finset.univ_nonempty landing_le_one
                    (virtualOnce_cons_le' wbar hw (witness_props _) _ d) (virtualOnce_perm' wbar _ d)
                    (Nat.zero_le _) _

/-- Lifted hash computations are sequences of ordinary queries. -/
theorem goodO_liftHash (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (L : QueryLog SigningSpec) {α : Type} (computation : OracleComp HashSpec α)
    (next : α → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ a, GoodO parameter data wbar b0 Fail Qtot tg initial model L (next a)) :
    GoodO parameter data wbar b0 Fail Qtot tg initial model L
      ((liftM computation : OracleComp CostSpec α) >>= next) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [liftM_pure, pure_bind] using h value
  | query_bind query rest ih =>
      rw [liftM_bind, bind_assoc]
      exact goodO_ordinary parameter data wbar b0 Fail Qtot tg initial model hparse hkind hdigest hw hb0 L query _ ih

end GoodO

/-! ### Signing a message for the first time -/

section SignDefsO

variable (parameter : PublicParameter) (data : PublicData) (m : Message) (s : State)

/-- A pool sum over the randomizers of a message is at most the sum over the items of that
message. -/
theorem pool_sum_le_msg {P : List Pair} (hP : PInv parameter data s P) (excl : Pair → Prop) (g : View → ℝ≥0∞) :
    ∑ ρ, poolValue parameter data m s (fun ρ v => if excl (m, ρ) then 0 else g v) ρ ≤
      (((others excl P).filter fun q => decide (q.1 = m)).map fun q => g (pview parameter data s q)).sum := by
  classical
  set P' := (others excl P).filter fun q => decide (q.1 = m) with hP'
  have hmem : ∀ ρ, (m, ρ) ∈ P' ↔ (m, ρ) ∈ others excl P := by
    intro ρ
    simp [hP', List.mem_filter]
  have hpoint : ∀ ρ, poolValue parameter data m s (fun ρ v => if excl (m, ρ) then 0 else g v) ρ =
      if (m, ρ) ∈ P' then g (pview parameter data s (m, ρ)) else 0 := by
    intro ρ
    simp only [hmem ρ]
    unfold poolValue
    cases h0 : s.cache (blk parameter data m ρ 0) with
    | none =>
        have : (m, ρ) ∉ P := fun hmem => by
          obtain ⟨u, hu, _⟩ := (hP.mem _).1 hmem
          change s.cache (blk parameter data m ρ 0) = some u at hu
          rw [h0] at hu; cases hu
        simp [mem_others, this]
    | some u0 =>
        simp only [Option.elim]
        by_cases hl : Landed parameter (blockIndex u0)
        · have hland : LandedIn parameter data s (m, ρ) := ⟨u0, h0, hl⟩
          have hmemP := (hP.mem _).2 hland
          obtain ⟨u1, h1⟩ := Option.ne_none_iff_exists'.1 (hP.second _ hland)
          rw [if_pos hl]
          change (s.cache (blk parameter data m ρ 1)).elim _ _ = _
          rw [h1]
          simp only [Option.elim]
          have hv : pview parameter data s (m, ρ) = viewOf u0 u1 := by
            simp only [pview]
            change ((s.cache (blk parameter data m ρ 0)).elim _ fun u0 =>
              (s.cache (blk parameter data m ρ 1)).elim _ fun u1 => viewOf u0 u1) = _
            rw [h0, h1]
            rfl
          by_cases hx : excl (m, ρ)
          · simp [hx, mem_others]
          · simp [hx, mem_others, hmemP, hv]
        · have : (m, ρ) ∉ P := fun hmem => by
            obtain ⟨u, hu, hlu⟩ := (hP.mem _).1 hmem
            change s.cache (blk parameter data m ρ 0) = some u at hu
            rw [h0] at hu; cases hu; exact hl hlu
          rw [if_neg hl]
          simp [mem_others, this]
  simp only [hpoint]
  rw [← Finset.sum_filter]
  have hnodup : P'.Nodup := (others_nodup hP.nodup).filter _
  rw [← List.sum_toFinset _ hnodup]
  calc ∑ ρ ∈ Finset.univ.filter (fun ρ => (m, ρ) ∈ P'), g (pview parameter data s (m, ρ))
      = ∑ q ∈ (Finset.univ.filter (fun ρ => (m, ρ) ∈ P')).image (fun ρ => (m, ρ)),
          g (pview parameter data s q) := by
        rw [Finset.sum_image fun _ _ _ _ h => (Prod.ext_iff.1 h).2]
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset fun q hq => ?_
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hq
        rw [Finset.mem_filter] at hρ
        exact List.mem_toFinset.2 hρ.2

/-- Views of the items of other messages that keep their coin. -/
noncomputable def restItems (L : QueryLog SigningSpec) (l : List Pair) : List View :=
  items parameter data s (l.filter fun q => decide (MsgFresh L q ∧ q.1 ≠ m))

/-- Views of the items of the message. -/
noncomputable def msgItems (l : List Pair) : List View :=
  items parameter data s (l.filter fun q => decide (q.1 = m))

/-- Before signing a fresh message, the coin items are its items and the rest. -/
theorem coinItems_perm (L : QueryLog SigningSpec) (hm : ∀ entry ∈ L, entry.1 ≠ m) (l : List Pair) :
    (coinItems parameter data s L l).Perm (msgItems parameter data m s l ++ restItems parameter data m s L l) := by
  unfold coinItems msgItems restItems items
  rw [← List.map_append]
  refine List.Perm.map _ ?_
  have h1 : (l.filter fun q => decide (MsgFresh L q)).filter (fun q => decide (q.1 = m)) =
      l.filter fun q => decide (q.1 = m) := by
    rw [List.filter_filter]
    congr 1
    funext q
    by_cases hq : q.1 = m
    · have hf : MsgFresh L q := fun entry he => by rw [hq]; exact hm entry he
      simp [hq, hf]
    · simp [hq]
  have h2 : (l.filter fun q => decide (MsgFresh L q)).filter (fun q => !decide (q.1 = m)) =
      l.filter fun q => decide (MsgFresh L q ∧ q.1 ≠ m) := by
    rw [List.filter_filter]
    congr 1
    funext q
    by_cases hq : q.1 = m <;> by_cases hf : MsgFresh L q <;> simp [hq, hf]
  have hperm := List.filter_append_perm (fun q => decide (q.1 = m)) (l.filter fun q => decide (MsgFresh L q))
  rw [h1, h2] at hperm
  exact hperm.symm

end SignDefsO

section SignUpperO

variable (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (m : Message) (s : State) (n : ℕ)
  (d : Multiset View) (f : Multiset View → ℝ≥0∞)

/-- The value without disclosure. -/
noncomputable def baseVO (J : List View) : ℝ≥0∞ := virtualOnce Finset.univ wbar f n J d

/-- Gain of a fresh view that is disclosed (it gets no coin: its message is now signed). -/
noncomputable def gainFO (J : List View) (u : View) : ℝ≥0∞ :=
  virtualOnce Finset.univ wbar f n J (d + {u}) - baseVO wbar n d f J

/-- Gain of disclosing an existing item. -/
noncomputable def gainPO (J : List View) (v : View) : ℝ≥0∞ :=
  virtualOnce Finset.univ wbar f n J (d + {v}) - baseVO wbar n d f J

/-- Upper value of one signing outcome, for the coin items `J` that remain. -/
noncomputable def upperO (excl : Pair → Prop) (out : Run HashInput Coordinate (Option Signature) × State)
    (J : List View) : ℝ≥0∞ :=
  baseVO wbar n d f J + freshNewWeight parameter data m s (gainFO wbar n d f J) out +
    outWeight parameter data m s 0 (fun ρ v => if excl (m, ρ) then 0 else gainPO wbar n d f J v) out

variable {parameter data wbar m s n d f}

/-- **Pointwise upper value.** -/
theorem upper_pointO (hw : wbar ≤ 1) (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤) {P : List Pair}
    (hP : PInv parameter data s P) (excl : Pair → Prop) (out : Run HashInput Coordinate (Option Signature) × State)
    (r : Option Signature) (hres : out.1.1 = some r) (Fail : Finset (Fin (2 ^ subtreeHeight)))
    (shape : (newRand parameter data m s out.2 = ∅ ∧ poolDisc parameter data m s out = 0) ∨
      (∃ ρ u0 u1, newRand parameter data m s out.2 = {ρ} ∧ poolDisc parameter data m s out = 0 ∧
        out.2.cache (blk parameter data m ρ 0) = some u0 ∧ Landed parameter (blockIndex u0) ∧
        out.2.cache (blk parameter data m ρ 1) = some u1 ∧ s.cache (blk parameter data m ρ 0) = none ∧
        (∀ ρ', ρ' ≠ ρ → RelatedAt parameter data m s out.2 ρ') ∧
        (r = none → (viewOf u0 u1).1 ∈ Fail) ∧ (∀ sig, r = some sig → sig.randomness = ρ)) ∨
      (∃ ρ u0 u1 sig, newRand parameter data m s out.2 = ∅ ∧ poolDisc parameter data m s out = {viewOf u0 u1} ∧
        r = some sig ∧ sig.randomness = ρ ∧ s.cache (blk parameter data m ρ 0) = some u0 ∧
        out.2.cache (blk parameter data m ρ 0) = some u0 ∧ out.2.cache (blk parameter data m ρ 1) = some u1))
    (hex : ∀ sig, r = some sig → s.cache (blk parameter data m sig.randomness 0) ≠ none → ¬excl (m, sig.randomness))
    (J : List View) :
    virtualOnce Finset.univ wbar f n J (discAfter parameter data m s d out) ≤
      upperO parameter data wbar m s n d f excl out J := by
  have hprops := virtualOnce_props Finset.univ_nonempty hw hf.1 hf.2.1 hf.2.2 n J
  unfold upperO discAfter newPairs
  rcases shape with ⟨hnew, hpool⟩ | ⟨ρ, u0, u1, hnew, hpool, h0, hl, h1, hs0, _, _, _⟩ |
      ⟨ρ, u0, u1, sig, hnew, hpool, hr, hsig, hs0, h0, h1⟩
  · rw [hnew, hpool]
    simp only [Finset.toList_empty, List.map_nil, Multiset.coe_nil, add_zero]
    exact le_trans le_self_add le_self_add
  · rw [hnew, hpool, Finset.toList_singleton]
    have hv : pview parameter data out.2 (m, ρ) = viewOf u0 u1 := pview_of_cached h0 h1
    simp only [List.map_cons, List.map_nil, hv, add_zero]
    rw [show ((([viewOf u0 u1] : List View)) : Multiset View) = {viewOf u0 u1} from rfl]
    have hbase : baseVO wbar n d f J ≤ virtualOnce Finset.univ wbar f n J (d + {viewOf u0 u1}) :=
      hprops.1 _ _ (Multiset.le_add_right _ _)
    rw [← add_tsub_cancel_of_le hbase]
    refine le_trans (add_le_add le_rfl ?_) le_self_add
    unfold freshNewWeight
    rw [if_pos (by rw [hres]; rfl)]
    have hs1 : s.cache (blk parameter data m ρ 1) = none := hP.first (m, ρ) hs0
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun ρ' => if s.cache (blk parameter data m ρ' 1) = none then
      (out.2.cache (blk parameter data m ρ' 0)).elim 0 (fun u0 =>
        (out.2.cache (blk parameter data m ρ' 1)).elim 0 fun u1 =>
          if Landed parameter (blockIndex u0) then gainFO wbar n d f J (viewOf u0 u1) else 0) else 0)
      (fun _ _ => bot_le) (Finset.mem_univ ρ))
    simp only [hs1, h0, h1, Option.elim, if_true, if_pos hl]
    rfl
  · rw [hnew, hpool]
    simp only [Finset.toList_empty, List.map_nil, Multiset.coe_nil, add_zero]
    have hbase : baseVO wbar n d f J ≤ virtualOnce Finset.univ wbar f n J (d + {viewOf u0 u1}) :=
      hprops.1 _ _ (Multiset.le_add_right _ _)
    rw [← add_tsub_cancel_of_le hbase]
    refine le_trans (add_le_add le_rfl ?_) (add_le_add le_self_add le_rfl)
    unfold outWeight
    rw [hres, hr]
    simp only
    rw [hsig, h0, h1]
    simp only [Option.elim, pairWeight, hs0, reduceCtorEq, if_false]
    have hne : s.cache (blk parameter data m sig.randomness 0) ≠ none := by
      rw [hsig, hs0]; exact Option.some_ne_none _
    have hx := hex sig hr hne
    rw [hsig] at hx
    rw [if_neg hx]
    rfl

end SignUpperO

section SignExpectO

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (m : Message) (s : State) (n : ℕ)
  (d : Multiset View) (f : Multiset View → ℝ≥0∞)

variable {parameter data wbar m s n d f}

theorem upper_expectO (hparse : ∀ ρ call, model.parse (blk parameter data m ρ call) = none)
    {Cmax : ℕ} (hfair : Fair wbar Cmax) (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤)
    {P : List Pair} (hP : PInv parameter data s P) (excl : Pair → Prop) (attempts budget : ℕ)
    (hcount : cachedCount parameter data m s + attempts ≤ Cmax) (J : List View) :
    ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
        upperO parameter data wbar m s n d f excl out J ≤
      baseVO wbar n d f J + freshAvg Finset.univ (gainFO wbar n d f J) +
        wbar * ∑ ρ, poolValue parameter data m s (fun ρ v => if excl (m, ρ) then 0 else gainPO wbar n d f J v) ρ := by
  have hprops := virtualOnce_props Finset.univ_nonempty hfair.le_one hf.1 hf.2.1 hf.2.2 n J
  have hnob1 : ∀ ρ, s.cache (blk parameter data m ρ 0) = none → s.cache (blk parameter data m ρ 1) = none :=
    fun ρ h => hP.first (m, ρ) h
  have hlandb1 : ∀ ρ u0, s.cache (blk parameter data m ρ 0) = some u0 → Landed parameter (blockIndex u0) →
      s.cache (blk parameter data m ρ 1) ≠ none := fun ρ u0 h0 hl => hP.second (m, ρ) ⟨u0, h0, hl⟩
  set B : ℝ≥0∞ := ∑ v : View, virtualOnce Finset.univ wbar f n J (d + {v}) with hB
  have hBfin : B ≠ ⊤ := ENNReal.sum_ne_top.2 fun v _ => hprops.2.2 _
  have hgp : ∀ ρ v, (fun ρ v => if excl (m, ρ) then 0 else gainPO wbar n d f J v) ρ v ≤ B := by
    intro ρ v
    simp only
    split_ifs
    · exact bot_le
    · exact le_trans tsub_le_self (Finset.single_le_sum (f := fun v => virtualOnce Finset.univ wbar f n J (d + {v}))
        (fun _ _ => bot_le) (Finset.mem_univ v))
  have hpool := loop_bound tg initial model parameter data m hparse s hnob1 (fun _ => 0)
    (fun ρ v => if excl (m, ρ) then 0 else gainPO wbar n d f J v) B hBfin (fun _ => bot_le) hgp wbar hfair.ne_top
    Cmax hfair.cmax hfair.share attempts budget s (related_self parameter data m s) hcount
  have hfresh := loop_bound_fresh tg initial model parameter data m hparse s hnob1 hlandb1 (gainFO wbar n d f J)
    attempts budget s (related_self parameter data m s)
  unfold upperO
  simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
  refine add_le_add (add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) hfresh) (le_trans hpool ?_)
  simp [freshAvg]

/-- The pool sum fits in the coins of the items of the message. -/
theorem slot_combineO (hw : wbar ≤ 1) (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤)
    {P : List Pair} (hP : PInv parameter data s P) (excl : Pair → Prop) (J : List View) :
    baseVO wbar n d f J + freshAvg Finset.univ (gainFO wbar n d f J) +
        wbar * ∑ ρ, poolValue parameter data m s (fun ρ v => if excl (m, ρ) then 0 else gainPO wbar n d f J v) ρ ≤
      virtualOnce Finset.univ wbar f (n + 1) (msgItems parameter data m s (others excl P) ++ J) d := by
  refine le_trans (add_le_add le_rfl (mul_le_mul_right (pool_sum_le_msg parameter data m s hP excl _) wbar))
    (le_trans (le_of_eq ?_) (once_slot_ge Finset.univ_nonempty hw hf.1 hf.2.1 hf.2.2 n
      (msgItems parameter data m s (others excl P)) J d))
  rw [← List.sum_map_mul_left]
  unfold msgItems items
  rw [List.map_map]
  rfl

/-- **A dominated term.** Averaged over a signing call, the upper value of a term is at most its
value with one more fresh slot and the coins of the message's items. -/
theorem term_expectO (hparse : ∀ ρ call, model.parse (blk parameter data m ρ call) = none)
    {Cmax : ℕ} (hfair : Fair wbar Cmax) (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤)
    {P : List Pair} (hP : PInv parameter data s P) (excl : Pair → Prop) (attempts budget k : ℕ)
    (hcount : cachedCount parameter data m s + attempts ≤ Cmax) (rest : List View) :
    ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
        creations Finset.univ landing (fun J => upperO parameter data wbar m s n d f excl out J) k rest ≤
      creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar f (n + 1) J d) k
        (msgItems parameter data m s (others excl P) ++ rest) := by
  rw [creations_tsum, creations_prepend (virtualOnce_perm' wbar (n + 1) d)]
  refine creations_mono_suffix k _ fun news => ?_
  exact le_trans (upper_expectO tg initial model hparse hfair hf hP excl attempts budget hcount _)
    (slot_combineO hfair.le_one hf hP excl (news ++ rest))

end SignExpectO

/-! ### The potential after signing a message for the first time -/

section SignPointO

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (m : Message) (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View)

/-- Bound for one outcome of a signing call. -/
noncomputable def canonO (n k : ℕ) (out : Run HashInput Coordinate (Option Signature) × State) : ℝ≥0∞ :=
  freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out +
  (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
      creations Finset.univ landing (fun J => upperO parameter data wbar m s n d (witnessFn (pview parameter data s q))
        (· = q) out J) k (restItems parameter data m s L (P.erase q))) else 0).sum +
  k * (creations Finset.univ landing (fun J => upperO parameter data wbar m s n d (excess b0) (fun _ => False) out J) k
      (restItems parameter data m s L P) + failMass Fail) +
  n * failMass Fail

variable {parameter data wbar b0 Fail m s P L d}

omit [Params] in
theorem msgFresh_append {L : QueryLog SigningSpec} {r : Option Signature} {q : Pair} :
    MsgFresh (L ++ [⟨m, r⟩]) q ↔ MsgFresh L q ∧ q.1 ≠ m := by
  unfold MsgFresh
  constructor
  · intro h
    exact ⟨fun e he => h e (List.mem_append_left _ he),
      fun hq => h ⟨m, r⟩ (List.mem_append_right _ (List.mem_singleton_self _)) hq.symm⟩
  · rintro ⟨h, hq⟩ e he
    rcases List.mem_append.1 he with he | he
    · exact h e he
    · rw [List.mem_singleton] at he
      subst he
      exact fun h' => hq h'.symm

/-- After signing, the coin items are the items of the other fresh messages. -/
theorem coinItems_after {s' : State} {r : Option Signature} (l : List Pair)
    (hview : ∀ q ∈ l, pview parameter data s' q = pview parameter data s q) :
    coinItems parameter data s' (L ++ [⟨m, r⟩]) (newPairs parameter data m s s' ++ l) =
      restItems parameter data m s L l := by
  unfold coinItems restItems items
  rw [List.filter_append]
  have hnew : (newPairs parameter data m s s').filter (fun q => decide (MsgFresh (L ++ [⟨m, r⟩]) q)) = [] := by
    refine List.filter_eq_nil_iff.2 fun q hq => ?_
    obtain ⟨hm, _, _⟩ := (mem_newPairs parameter data m s).1 hq
    simp only [decide_eq_true_eq, msgFresh_append, not_and, not_not]
    exact fun _ => hm
  have hold : l.filter (fun q => decide (MsgFresh (L ++ [⟨m, r⟩]) q)) =
      l.filter fun q => decide (MsgFresh L q ∧ q.1 ≠ m) := by
    congr 1
    funext q
    simp only [msgFresh_append]
  rw [hnew, hold, List.nil_append]
  exact List.map_congr_left fun q hq => hview q (List.mem_of_mem_filter hq)

end SignPointO

/-- Fewer future pairs, then a pointwise bound. -/
theorem post_term_leO {wbar : ℝ≥0∞} (hw : wbar ≤ 1) {f : Multiset View → ℝ≥0∞}
    (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤) (I : List View) (n : ℕ) (d' : Multiset View)
    {k' k : ℕ} (hk : k' ≤ k) (U : List View → ℝ≥0∞) (hU : ∀ J, virtualOnce Finset.univ wbar f n J d' ≤ U J) :
    creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar f n J d') k' I ≤
      creations Finset.univ landing U k I :=
  le_trans (creations_mono_count Finset.univ_nonempty landing_le_one (virtualOnce_cons_le' wbar hw hf n d')
    (virtualOnce_perm' wbar n d') hk I) (creations_mono hU k I)

section SignPointMainO

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ) (m : Message)

/-- **The potential after one signing outcome.** -/
theorem sign_pointO (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hfail : ∀ ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (attempts budget : ℕ) (s : State) (P : List Pair) (L : QueryLog SigningSpec)
    (d : Multiset View) (R : List Coordinate) (hprep : Prepared initial s) (hP : PInv parameter data s P)
    (hD : DInv R d) (hC : CountInv parameter data Qtot s budget)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSourceLoop parameter data m attempts) budget s))
    (r : Option Signature) (hr : out.1.1 = some r) {k' : ℕ} (hk : k' ≤ budget) :
    potO parameter data wbar b0 Fail tg initial out.2 (newPairs parameter data m s out.2 ++ P) (L ++ [⟨m, r⟩])
        (discAfter parameter data m s d out) k' ≤
      if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
      else canonO parameter data wbar b0 Fail m s P L d (signatureLimit - (L.length + 1)) budget out := by
  obtain ⟨_, hP', _, _, hview⟩ := sign_params tg initial model Fail Qtot hparse hfail attempts budget
    s P d R hprep hP hD hC out hout r hr
  have hext := interp_extends tg initial model _ budget s out hout
  have hpost := loop_post tg initial model parameter data m (fun ρ call => hparse (m, ρ) call) Fail hfail
    attempts budget s hprep out hout r hr
  have hshape := sign_shape parameter data Fail m hpost out rfl hr
  unfold potO
  by_cases hcase : Realized tg initial out.2 ∨ signatureLimit < (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length
  · rw [if_pos hcase]; exact bot_le
  rw [if_neg hcase]
  have hreal : ¬Realized tg initial s := fun h => hcase (Or.inl (realized_of_extends tg initial hext h))
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
  unfold coreO canonO
  rw [List.map_append, List.sum_append]
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) le_rfl
  · -- new pairs: only a failed fresh pair stays a candidate
    rcases hshape with ⟨hnew, _⟩ | ⟨ρ, u0, u1, hnew, _, h0, hl, h1, hs0, _, hfl, hsig⟩ |
        ⟨_, _, _, _, hnew, _⟩
    · unfold newPairs; rw [hnew]; simp
    · have hs1 : s.cache (blk parameter data m ρ 1) = none := hP.first (m, ρ) hs0
      have hv : pview parameter data out.2 (m, ρ) = viewOf u0 u1 := pview_of_cached h0 h1
      have hlist : newPairs parameter data m s out.2 = [(m, ρ)] := by
        unfold newPairs; rw [hnew, Finset.toList_singleton]; rfl
      rw [hlist]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      refine le_trans ?_ (freshNewWeight_ge hr hs1 h0 hl h1 (fun v => if v.1 ∈ Fail then 1 else 0))
      unfold candO
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
    unfold candO
    by_cases hU' : Unsigned (L ++ [⟨m, r⟩] : QueryLog SigningSpec) q
    · have hU := unsigned_of_append hU'
      rw [if_pos hU', if_pos hU, hview q hq]
      split_ifs with hF
      · exact le_rfl
      · unfold candValueO
        rw [hview q hq, List.erase_append_right _ (hnotnew q hq),
          coinItems_after (P.erase q) fun q' hq' => hview q' (List.mem_of_mem_erase hq')]
        refine post_term_leO hw (witness_props _) _ n _ hk _ fun J => ?_
        refine upper_pointO hw (witness_props _) hP (· = q) out r hr Fail hshape (fun sig hsig _ heq => ?_) J
        subst hsig
        exact not_unsigned_signed (m := m) (L := L) (by rw [heq]; exact hU')
    · rw [if_neg hU']
      exact bot_le
  · -- the excess forecast
    refine mul_le_mul' (by exact_mod_cast hk) (add_le_add ?_ le_rfl)
    unfold hValueO
    rw [coinItems_after P hview]
    refine post_term_leO hw (excess_props b0 hb0) _ n _ hk _ fun J => ?_
    exact upper_pointO hw (excess_props b0 hb0) hP (fun _ => False) out r hr Fail hshape (fun _ _ _ h => h) J

/-- **The signing step in expectation**, for a message signed for the first time. -/
theorem sign_expectO (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    {Cmax : ℕ} (hfair : Fair wbar Cmax) (hb0 : b0 ≠ ⊤) (attempts budget : ℕ) (s : State) (P : List Pair)
    (L : QueryLog SigningSpec) (hm : ∀ entry ∈ L, entry.1 ≠ m) (d : Multiset View) (hP : PInv parameter data s P)
    (hcount : cachedCount parameter data m s + attempts ≤ Cmax) :
    ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
        (if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
          else canonO parameter data wbar b0 Fail m s P L d (signatureLimit - (L.length + 1)) budget out) ≤
      potO parameter data wbar b0 Fail tg initial s P L d budget := by
  by_cases hcase : Realized tg initial s ∨ signatureLimit ≤ L.length
  · simp only [if_pos hcase, mul_zero, tsum_zero]
    exact bot_le
  simp only [if_neg hcase]
  have hcase' : ¬Realized tg initial s ∧ L.length < signatureLimit := by push Not at hcase; exact hcase
  have hlen := hcase'.2
  unfold potO
  rw [if_neg (by rintro (h | h); exact hcase'.1 h; omega)]
  set n := signatureLimit - (L.length + 1) with hn
  have hn1 : signatureLimit - L.length = n + 1 := by omega
  rw [hn1]
  have hparse' : ∀ ρ call, model.parse (blk parameter data m ρ call) = none := fun ρ call => hparse (m, ρ) call
  have hnob1 : ∀ ρ, s.cache (blk parameter data m ρ 0) = none → s.cache (blk parameter data m ρ 1) = none :=
    fun ρ h => hP.first (m, ρ) h
  have hlandb1 : ∀ ρ u0, s.cache (blk parameter data m ρ 0) = some u0 → Landed parameter (blockIndex u0) →
      s.cache (blk parameter data m ρ 1) ≠ none := fun ρ u0 h0 hl => hP.second (m, ρ) ⟨u0, h0, hl⟩
  have hmass : ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] ≤ 1 :=
    tsum_probOutput_le_one
  have hFN := loop_bound_fresh tg initial model parameter data m hparse' s hnob1 hlandb1
    (fun v => if v.1 ∈ Fail then 1 else 0) attempts budget s (related_self parameter data m s)
  have hT : ∀ q ∈ P, ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
      (if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
        creations Finset.univ landing (fun J => upperO parameter data wbar m s n d (witnessFn (pview parameter data s q))
          (· = q) out J) budget (restItems parameter data m s L (P.erase q))) else 0) ≤
      candO parameter data wbar Fail s P L d (n + 1) budget q := by
    intro q _
    unfold candO
    split_ifs
    · rw [ENNReal.tsum_mul_right, mul_one]; exact hmass
    · unfold candValueO
      rw [creations_perm (virtualOnce_perm' wbar (n + 1) d) budget _ _ (coinItems_perm parameter data m s L hm _)]
      have h := term_expectO tg initial model hparse' hfair (witness_props (pview parameter data s q)) hP (· = q)
        attempts budget budget hcount (restItems parameter data m s L (P.erase q)) (n := n) (d := d)
      rwa [← erase_eq_filter' hP.nodup q] at h
    · simp
  have hH := term_expectO tg initial model (n := n) (d := d) hparse' hfair (excess_props b0 hb0) hP (fun _ => False)
    attempts budget budget hcount (restItems parameter data m s L P)
  rw [filter_false'] at hH
  have hHv : hValueO parameter data wbar b0 s P L d (n + 1) budget =
      creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar (excess b0) (n + 1) J d) budget
        (msgItems parameter data m s P ++ restItems parameter data m s L P) := by
    unfold hValueO
    exact creations_perm (virtualOnce_perm' wbar (n + 1) d) budget _ _ (coinItems_perm parameter data m s L hm _)
  unfold canonO coreO
  simp only [mul_add, ENNReal.tsum_add]
  rw [tsum_list_sum]
  have hφ : freshAvg Finset.univ (fun v : View => if v.1 ∈ Fail then (1 : ℝ≥0∞) else 0) = failMass Fail := rfl
  rw [hφ] at hFN
  calc _ ≤ failMass Fail + (P.map (candO parameter data wbar Fail s P L d (n + 1) budget)).sum +
        (budget * hValueO parameter data wbar b0 s P L d (n + 1) budget + budget * failMass Fail) +
          n * failMass Fail := by
        refine add_le_add (add_le_add (add_le_add hFN (List.sum_le_sum hT)) (add_le_add ?_ ?_)) ?_
        · simp only [mul_left_comm _ (budget : ℝ≥0∞), ENNReal.tsum_mul_left]
          rw [hHv]
          exact mul_le_mul_right hH _
        · rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' hmass
        · rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' hmass
    _ = _ := by push_cast; ring

/-- **One signing call** on a message that was never signed before. -/
theorem goodO_sign (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    {Cmax : ℕ} (hfair : Fair wbar Cmax) (hb0 : b0 ≠ ⊤) (hQ : Qtot + digestAttemptLimit ≤ Cmax)
    (L : QueryLog SigningSpec) (hm : ∀ entry ∈ L, entry.1 ≠ m)
    (next : Option Signature → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ r, GoodO parameter data wbar b0 Fail Qtot tg initial model (L ++ [⟨m, r⟩]) (next r)) :
    GoodO parameter data wbar b0 Fail Qtot tg initial model L (signCostSource parameter data m >>= next) := by
  intro budget s P d R hprep hP hD hC
  have hcount : cachedCount parameter data m s + digestAttemptLimit ≤ Cmax := by
    have := hC m; omega
  unfold signCostSource
  set sign := signCostSourceLoop parameter data m digestAttemptLimit with hsign
  set cont : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    o1.1.1.elim 0 fun r => expectedFlagged tg initial model (next r) (budget - traceCost o1.1.2.2.1) o1.2 with hcont
  set canonR : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
    else canonO parameter data wbar b0 Fail m s P L d (signatureLimit - (L.length + 1)) budget o1 with hcanonR
  have hpoint : ∀ o1 ∈ support (interp tg initial model sign budget s),
      ∑' out, Pr[= out | interpThen tg initial model next budget o1] * finalValue parameter data tg initial R out ≤
        canonR o1 + b0 * cont o1 := by
    intro o1 ho1
    cases hres : o1.1.1 with
    | none =>
        rw [interpThen_none tg initial model next budget o1 hres, tsum_probOutput_pure_mul]
        exact bot_le
    | some r =>
        rw [interpThen_some tg initial model next budget o1 r hres, tsum_probOutput_map_mul]
        obtain ⟨hprep', hP', hD', hC', _⟩ := sign_params tg initial model Fail Qtot hparse (hfail m)
          digestAttemptLimit budget s P d R hprep hP hD hC o1 ho1 r hres
        have hIH := h r (budget - traceCost o1.1.2.2.1) o1.2 _ _ _ hprep' hP' hD' hC'
        have hpot := sign_pointO tg initial model parameter data wbar b0 Fail Qtot m hparse (hfail m) hfair.le_one hb0
          digestAttemptLimit budget s P L d R hprep hP hD hC o1 ho1 r hres (Nat.sub_le budget (traceCost o1.1.2.2.1))
        have heq : ∀ o2 : Run HashInput Coordinate HiddenBridge.Outcome × State,
            finalValue parameter data tg initial R
              ((o2.1.1, o1.1.2.1 ++ o2.1.2.1, o1.1.2.2.1 ++ o2.1.2.2.1, o1.1.2.2.2 ++ o2.1.2.2.2), o2.2) =
            finalValue parameter data tg initial (R ++ o1.1.2.1) o2 := by
          intro o2
          unfold finalValue
          simp only [List.append_assoc]
        simp only [heq]
        refine le_trans hIH (add_le_add hpot ?_)
        simp only [hcont, hres, Option.elim, le_refl]
  have hflag : ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * cont o1 ≤
      expectedFlagged tg initial model (sign >>= next) budget s := by
    unfold expectedFlagged
    rw [interp_bind, tsum_probOutput_bind_mul]
    refine ENNReal.tsum_le_tsum fun o1 => mul_le_mul_right ?_ _
    cases hres : o1.1.1 with
    | none => simp only [hcont, hres, Option.elim]; exact bot_le
    | some r =>
        simp only [hcont, hres, Option.elim]
        rw [interpThen_some tg initial model next budget o1 r hres, tsum_probOutput_map_mul]
        unfold expectedFlagged
        refine ENNReal.tsum_le_tsum fun o2 => mul_le_mul_right ?_ _
        simp only [flaggedCount_append, Nat.cast_add]
        exact le_add_self
  rw [interp_bind, tsum_probOutput_bind_mul]
  calc _ ≤ ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * (canonR o1 + b0 * cont o1) := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support (interp tg initial model sign budget s)
        · exact mul_le_mul_right (hpoint o1 ho1) _
        · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
    _ = ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * canonR o1 +
          b0 * ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * cont o1 := by
        simp only [mul_add, ENNReal.tsum_add, mul_left_comm _ b0, ENNReal.tsum_mul_left]
    _ ≤ _ := add_le_add (sign_expectO tg initial model parameter data wbar b0 Fail m hparse hfair hb0
          digestAttemptLimit budget s P L hm d hP hcount) (mul_le_mul_right hflag _)

end SignPointMainO

end LeanSphincs.Security.ForsPotential
