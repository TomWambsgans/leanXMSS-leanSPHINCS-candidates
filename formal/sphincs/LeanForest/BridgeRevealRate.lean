import LeanForest.BridgeRunFacts
import LeanForest.BridgeForestNear
import LeanForest.H0Mark
import LeanForest.BridgeRevealAll

/-! **One signing call opens a given forest chain rarely.** A fresh landed digest opens chain `i` of
the WOTS key `a` of subtree `j` under the leaf `sp` of tree `c` at the index of a given step, at or
below a position `k ≤ 3`, with probability at most `2^-b · 2^-4 · 2^-3 · 134/256`: the digest picks
the index, the leaf and the WOTS key uniformly, and at most 134 of the 256 codewords have digit `i`
at least one. A cached landed pair of the signed message adds `wbar` each. -/

open OracleComp OracleSpec ENNReal

namespace LeanForest.Security.ForsPotential

open LeanSphincs.Security
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForestPrice ForestSigner HiddenBridge
open LeanSphincs.Security.Domination

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### Counting codewords -/

/-- The codewords whose digit `i` is at least one. -/
def litCount (i : FChain) : ℕ := (Finset.univ.filter fun w : LutIdx => 1 ≤ (lut w i).val).card

omit [Params] in
theorem litCount_le_all : ∀ i : FChain, litCount i ≤ 134 := by
  unfold litCount
  decide +kernel

omit [Params] in
theorem sub_eq_or_other (j j' : SubIdx) : j' = j ∨ j' = otherSub j := by
  fin_cases j <;> fin_cases j' <;> decide

omit [Params] in
/-- The fields opening a given chain at or below position `k < 4`. -/
theorem card_opens_le (sp : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (k : ℕ) (hk : k < chainTop) :
    (Finset.univ.filter fun x : FieldVal => (decodeMark x).super = sp ∧ (decodeMark x).child j = a ∧
      chainTop - (lut ((decodeMark x).word j) i).val ≤ k).card ≤ 2048 * 134 := by
  set S := Finset.univ.filter fun x : FieldVal => (decodeMark x).super = sp ∧ (decodeMark x).child j = a ∧
    chainTop - (lut ((decodeMark x).word j) i).val ≤ k with hS
  set T := (Finset.univ : Finset (ChildIdx × LutIdx)) ×ˢ (Finset.univ.filter fun w : LutIdx => 1 ≤ (lut w i).val)
    with hT
  set g : FieldVal → (ChildIdx × LutIdx) × LutIdx := fun x =>
    (((decodeMark x).child (otherSub j), (decodeMark x).word (otherSub j)), (decodeMark x).word j) with hg
  have hmaps : Set.MapsTo g (S : Set FieldVal) (T : Set ((ChildIdx × LutIdx) × LutIdx)) := by
    intro x hx
    simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
    rw [Finset.mem_coe]
    simp only [hT, hg, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_filter]
    have := hx.2.2
    simp only [chainTop] at this
    omega
  have hinj : Set.InjOn g S := by
    intro x hx y hy hxy
    simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx hy
    simp only [hg, Prod.mk.injEq] at hxy
    obtain ⟨⟨hc, hw⟩, hwj⟩ := hxy
    have hm : decodeMark x = decodeMark y := by
      have hsup : (decodeMark x).super = (decodeMark y).super := hx.1.trans hy.1.symm
      have hch : (decodeMark x).child = (decodeMark y).child := by
        funext j'
        rcases sub_eq_or_other j j' with rfl | rfl
        · exact hx.2.1.trans hy.2.1.symm
        · exact hc
      have hwd : (decodeMark x).word = (decodeMark y).word := by
        funext j'
        rcases sub_eq_or_other j j' with rfl | rfl
        · exact hwj
        · exact hw
      cases hX : decodeMark x
      cases hY : decodeMark y
      rw [hX, hY] at hsup hch hwd
      simp only at hsup hch hwd
      rw [hsup, hch, hwd]
    exact markEquiv.injective hm
  calc S.card ≤ T.card := Finset.card_le_card_of_injOn g hmaps hinj
    _ = 2048 * litCount i := by
        rw [hT, Finset.card_product, Finset.card_univ, Fintype.card_prod]
        rfl
    _ ≤ 2048 * 134 := Nat.mul_le_mul_left _ (litCount_le_all i)

/-! ### Hitting one chain -/

/-- A kept view opens a forest chain at or below position `k`. -/
noncomputable def opensAt (index : Index) (c : Coord) (sp : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain)
    (k : ℕ) (v : View) : ℝ≥0∞ :=
  if v.1 = localIdx index ∧ (decodeMark (v.2 c)).super = sp ∧ (decodeMark (v.2 c)).child j = a ∧
    chainTop - (lut ((decodeMark (v.2 c)).word j) i).val ≤ k then 1 else 0

/-- The reveal rate `134 · 2^-b · 2^-15`. -/
noncomputable def revRate : ℝ≥0∞ := 134 * ((2 ^ subtreeHeight * 2 ^ 15 : ℕ) : ℝ≥0∞)⁻¹

theorem opensAt_le_one (index : Index) (c : Coord) (sp : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain)
    (k : ℕ) (v : View) : opensAt index c sp j a i k v ≤ 1 := by
  unfold opensAt
  split_ifs <;> simp

/-- **A uniform kept view opens a given chain with probability at most the reveal rate.** -/
theorem freshAvg_opensAt (index : Index) (c : Coord) (sp : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain)
    (k : ℕ) (hk : k < chainTop) : freshAvg Finset.univ (opensAt index c sp j a i k) ≤ revRate := by
  set P : FieldVal → Prop := fun x => (decodeMark x).super = sp ∧ (decodeMark x).child j = a ∧
    chainTop - (lut ((decodeMark x).word j) i).val ≤ k with hP
  have hsplit : ∀ v : View, opensAt index c sp j a i k v =
      (if v.1 = localIdx index then 1 else 0) *
        ∏ c', (fun c' (t : FieldVal) => if c' = c then (if P t then (1 : ℝ≥0∞) else 0) else 1) c' (v.2 c') := by
    intro v
    rw [Finset.prod_eq_single c (fun c' _ hc' => by simp only [if_neg hc']) (fun h => absurd (Finset.mem_univ c) h)]
    simp only [if_true, opensAt, hP]
    split_ifs <;> simp_all
  have hfield : freshAvg (Finset.univ : Finset FieldVal) (fun t => if P t then (1 : ℝ≥0∞) else 0) ≤
      ((2 ^ 26 : ℕ) : ℝ≥0∞)⁻¹ * (2048 * 134 : ℕ) := by
    unfold freshAvg
    rw [Finset.card_univ]
    have hc : Fintype.card FieldVal = 2 ^ 26 := by simp [FieldVal, coordBits]
    rw [hc]
    refine mul_le_mul_right ?_ _
    rw [Finset.sum_boole]
    exact_mod_cast card_opens_le sp j a i k hk
  rw [show (Finset.univ : Finset View) = (Finset.univ : Finset (Fin (2 ^ subtreeHeight) × (Coord → FieldVal)))
    from rfl, H0Avg.freshAvg_prod]
  simp only [hsplit]
  have hinner : ∀ l : Fin (2 ^ subtreeHeight), (freshAvg (Finset.univ : Finset (Coord → FieldVal)) fun τ =>
      (if (l, τ).1 = localIdx index then (1 : ℝ≥0∞) else 0) *
        ∏ c', (fun c' (t : FieldVal) => if c' = c then (if P t then (1 : ℝ≥0∞) else 0) else 1) c' ((l, τ).2 c')) =
      (if l = localIdx index then 1 else 0) *
        freshAvg (Finset.univ : Finset FieldVal) (fun t => if P t then (1 : ℝ≥0∞) else 0) := by
    intro l
    have hmul : ∀ (C : ℝ≥0∞) (G : (Coord → FieldVal) → ℝ≥0∞),
        freshAvg (Finset.univ : Finset (Coord → FieldVal)) (fun τ => C * G τ) =
          C * freshAvg (Finset.univ : Finset (Coord → FieldVal)) G := by
      intro C G
      unfold freshAvg
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    refine (hmul (if l = localIdx index then 1 else 0) (fun τ => ∏ c', (fun c' (t : FieldVal) =>
      if c' = c then (if P t then (1 : ℝ≥0∞) else 0) else 1) c' (τ c'))).trans ?_
    rw [H0Avg.freshAvg_pi_prod (fun c' (t : FieldVal) => if c' = c then (if P t then (1 : ℝ≥0∞) else 0) else 1)]
    congr 1
    rw [Finset.prod_eq_single c (fun c' _ hc' => by simp only [if_neg hc']; exact H0Avg.freshAvg_const' 1)
      (fun h => absurd (Finset.mem_univ c) h)]
    simp only [if_true]
  simp only [hinner]
  have hidx : freshAvg (Finset.univ : Finset (Fin (2 ^ subtreeHeight))) (fun l =>
      (if l = localIdx index then (1 : ℝ≥0∞) else 0) *
        freshAvg (Finset.univ : Finset FieldVal) (fun t => if P t then (1 : ℝ≥0∞) else 0)) =
      ((2 ^ subtreeHeight : ℕ) : ℝ≥0∞)⁻¹ *
        freshAvg (Finset.univ : Finset FieldVal) (fun t => if P t then (1 : ℝ≥0∞) else 0) := by
    unfold freshAvg
    rw [Finset.card_univ, Fintype.card_fin]
    congr 1
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ (localIdx index), if_pos (Finset.mem_univ _)]
  rw [hidx]
  calc ((2 ^ subtreeHeight : ℕ) : ℝ≥0∞)⁻¹ *
        freshAvg (Finset.univ : Finset FieldVal) (fun t => if P t then (1 : ℝ≥0∞) else 0)
      ≤ ((2 ^ subtreeHeight : ℕ) : ℝ≥0∞)⁻¹ * (((2 ^ 26 : ℕ) : ℝ≥0∞)⁻¹ * (2048 * 134 : ℕ)) :=
        mul_le_mul_right hfield _
    _ = revRate := by
        unfold revRate
        have h26 : ((2 ^ 26 : ℕ) : ℝ≥0∞) = ((2 ^ 15 : ℕ) : ℝ≥0∞) * 2048 := by norm_num
        rw [h26, ENNReal.mul_inv (Or.inr (by norm_num)) (Or.inr (by norm_num)), Nat.cast_mul, Nat.cast_mul,
          Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat]
        have h2048 : (2048 : ℝ≥0∞)⁻¹ * 2048 = 1 := ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
        rw [ENNReal.mul_inv (Or.inr (by norm_num)) (Or.inr (by norm_num))]
        calc ((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ * (((2 : ℝ≥0∞) ^ 15)⁻¹ * (2048 : ℝ≥0∞)⁻¹ * (2048 * 134))
            = 134 * (((2 : ℝ≥0∞) ^ subtreeHeight)⁻¹ * ((2 : ℝ≥0∞) ^ 15)⁻¹) * ((2048 : ℝ≥0∞)⁻¹ * 2048) := by ring
          _ = _ := by rw [h2048, mul_one]

/-! ### One signing call -/

section Reveal

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate) (parameter : PublicParameter) (data : PublicData)
  (m : Message)

/-- A completed signing call that opens a chain selected a pair whose view opens it, fresh or cached. -/
theorem reveal_point (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    {s : State} (hprep : Prepared initial s)
    (attempts budget : ℕ) (o1 : Run HashInput Coordinate (Option Signature) × State)
    (ho1 : o1 ∈ support (interp tg initial model (signCostSourceLoop parameter data m attempts) budget s))
    (r : Option Signature) (hr : o1.1.1 = some r)
    (index : Index) (c : Coord) (sp : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (k : ℕ) (q : FPos)
    (hq : q.val ≤ k) (hrev : Coordinate.fchain index c sp j a i q ∈ o1.1.2.1) :
    1 ≤ freshNewWeight parameter data m s (opensAt index c sp j a i k) o1 +
      outWeight parameter data m s (fun _ => 0) (fun _ v => opensAt index c sp j a i k v) o1 := by
  have hpost := loop_post tg initial model parameter data m (fun ρ => hparse (m, ρ)) Finset.univ
    (fun _ _ _ _ _ _ _ _ => Finset.mem_univ _) attempts budget s hprep o1 ho1 r hr
  rcases hpost with ⟨_, hnil, _⟩ | ⟨ρ, u0, hsel, hfts, hsig, hfl⟩
  · rw [hnil] at hrev
    cases hrev
  · obtain ⟨hi, hs, ha, hpos⟩ := hfts _ hrev index c sp j a i q rfl
    have hmarks := digestMarks_eq (truncateMessageDigest u0) c
    have hhit : opensAt index c sp j a i k (viewOf u0) = 1 := by
      unfold opensAt viewOf
      rw [if_pos]
      refine ⟨by rw [localDigestView_fst, hi], ?_, ?_, ?_⟩
      · rw [localDigestView_snd, ← hmarks, hs]
      · rw [localDigestView_snd, ← hmarks, ha]
      · rw [localDigestView_snd, ← hmarks]
        exact le_trans hpos hq
    rcases hsel.2.2.1 with hs0 | hs0
    · have h := freshNewWeight_ge hr hs0 hsel.1 hsel.2.1 (opensAt index c sp j a i k)
      rw [hhit] at h
      exact le_trans h le_self_add
    · rcases r with _ | sig
      · rw [(hfl rfl).1] at hrev
        cases hrev
      · have hρ := hsig sig rfl
        refine le_trans (le_of_eq ?_) le_add_self
        unfold outWeight
        rw [hr]
        simp only
        rw [hρ, hsel.1]
        simp only [Option.elim, pairWeight, hs0, reduceCtorEq, if_false]
        exact hhit.symm

omit [Params] in
theorem list_sum_le_length {γ : Type} (l : List γ) (f : γ → ℝ≥0∞) (hf : ∀ x, f x ≤ 1) :
    (l.map f).sum ≤ l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [add_comm (l.length : ℝ≥0∞)]
      exact add_le_add (hf x) ih

/-- **One signing call** opens a given chain at or below `k < 4` with probability at most the reveal
rate plus `wbar` per cached pair of the signed message. -/
theorem reveal_le (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    {s : State} {P : List Pair} (hP : PInv parameter data s P) (hprep : Prepared initial s)
    {wbar : ℝ≥0∞} {Cmax : ℕ} (hfair : Fair wbar Cmax) (attempts budget : ℕ)
    (hcount : cachedCount parameter data m s + attempts ≤ Cmax)
    (index : Index) (c : Coord) (sp : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (k : ℕ) (hk : k < chainTop) :
    ∑' o1, Pr[= o1 | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
        (if o1.1.1.isSome ∧ ∃ q : FPos, q.val ≤ k ∧ Coordinate.fchain index c sp j a i q ∈ o1.1.2.1 then 1 else 0) ≤
      revRate + wbar * ((P.filter fun q => decide (q.1 = m)).length : ℝ≥0∞) := by
  have hparse' : ∀ ρ, model.parse (blk parameter data m ρ) = none := fun ρ => hparse (m, ρ)
  set g : View → ℝ≥0∞ := opensAt index c sp j a i k with hgdef
  set gp : Randomness → View → ℝ≥0∞ := fun _ v => g v with hgp
  have hcomb := loop_bound_comb tg initial model parameter data m hparse' s g gp 1 ENNReal.one_ne_top
    (fun v => opensAt_le_one index c sp j a i k v) (fun _ v => opensAt_le_one index c sp j a i k v)
    (shareOf wbar (landedCount parameter data m s)) (shareOf_ne_top hfair _) Cmax hfair.cmax (hfair.share_le _)
    attempts budget s (related_self s) hcount
  have hsum := pool_sum_le_msg parameter data m s hP (fun _ => False) g
  rw [filter_false'] at hsum
  simp only [if_neg not_false] at hsum
  have hlen : ((P.filter fun q => decide (q.1 = m)).map fun q => g (pview parameter data s q)).sum ≤
      ((P.filter fun q => decide (q.1 = m)).length : ℝ≥0∞) :=
    list_sum_le_length _ _ fun q => opensAt_le_one index c sp j a i k _
  have he : shareOf wbar (landedCount parameter data m s) ≤ wbar := by
    have := shareOf_coef hfair (landedCount parameter data m s) 0 (Nat.zero_le _)
    simpa using this
  calc _ ≤ ∑' o1, Pr[= o1 | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
        (freshNewWeight parameter data m s g o1 + outWeight parameter data m s 0 gp o1) := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support (interp tg initial model (signCostSourceLoop parameter data m attempts) budget s)
        · refine mul_le_mul_right ?_ _
          split_ifs with hc
          · obtain ⟨hsome, q, hq, hrev⟩ := hc
            obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hsome
            exact reveal_point tg initial model parameter data m hparse hprep attempts budget o1 ho1 r hr
              index c sp j a i k q hq hrev
          · exact bot_le
        · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
    _ ≤ freshAvg Finset.univ g + shareOf wbar (landedCount parameter data m s) *
          (∑ ρ, poolValue parameter data m s gp ρ -
            (landedCount parameter data m s : ℝ≥0∞) * freshAvg Finset.univ g) := hcomb
    _ ≤ revRate + wbar * ((P.filter fun q => decide (q.1 = m)).length : ℝ≥0∞) := by
        refine add_le_add (freshAvg_opensAt index c sp j a i k hk) ?_
        calc _ ≤ wbar * ∑ ρ, poolValue parameter data m s gp ρ := mul_le_mul' he tsub_le_self
          _ ≤ _ := mul_le_mul_right (le_trans hsum hlen) _

/-- Every reveal of a run of the final assembly from a cached digest block is opened by its digest. -/
theorem finish_reveals_ok (ρ : Randomness) (b : ℕ) (s' : State) (u0 : HashOutput)
    (hparse : model.parse (blk parameter data m ρ) = none)
    (hc0 : s'.cache (blk parameter data m ρ) = some u0)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data m ρ) b s')) :
    ∀ c ∈ out.1.2.1, ForestOk (truncateMessageDigest u0) c := by
  rw [finishCostSource_eq, interp_ordinary] at hout
  split_ifs at hout with h1
  · rw [ordinaryStep, hparse] at hout
    simp only at hout
    rw [readOutside_cached _ s' u0 hc0, pure_bind, support_map] at hout
    obtain ⟨o, ho, rfl⟩ := hout
    exact interp_reveals tg initial model _ (revealsIn_finishRest parameter data m ρ _) _ _ o ho
  · rw [support_pure, Set.mem_singleton_iff] at hout
    subst hout
    intro c hc
    cases hc

/-- **One signing call, every run.** A signing call, completed or not, reveals a given chain at or
below `k < 4` with probability at most the reveal rate plus `wbar` per cached pair of the message. -/
theorem reveal_le_all (hparse : ∀ p, model.parse (pblk parameter data p) = none)
    {s : State} {P : List Pair} (hP : PInv parameter data s P)
    {wbar : ℝ≥0∞} {Cmax : ℕ} (hfair : Fair wbar Cmax) (attempts budget : ℕ)
    (hcount : cachedCount parameter data m s + attempts ≤ Cmax)
    (index : Index) (c : Coord) (sp : SuperIdx) (j : SubIdx) (a : ChildIdx) (i : FChain) (k : ℕ) (hk : k < chainTop) :
    ∑' o1, Pr[= o1 | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
        (if ∃ q : FPos, q.val ≤ k ∧ Coordinate.fchain index c sp j a i q ∈ o1.1.2.1 then 1 else 0) ≤
      revRate + wbar * ((P.filter fun q => decide (q.1 = m)).length : ℝ≥0∞) := by
  have hparse' : ∀ ρ, model.parse (blk parameter data m ρ) = none := fun ρ => hparse (m, ρ)
  set g : View → ℝ≥0∞ := opensAt index c sp j a i k with hgdef
  set gp : Randomness → View → ℝ≥0∞ := fun _ v => g v with hgp
  set V : List Coordinate → ℝ≥0∞ := fun L =>
    if ∃ q : FPos, q.val ≤ k ∧ Coordinate.fchain index c sp j a i q ∈ L then 1 else 0 with hV
  have hV0 : V [] = 0 := by
    simp only [hV]
    rw [if_neg]
    rintro ⟨q, _, h⟩
    cases h
  have hVfin : ∀ (ρ : Randomness) (s' : State) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data m s s' ρ → s'.cache (blk parameter data m ρ) = some u0 →
      Landed parameter (blockIndex u0) →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data m ρ) b s'),
        V out.1.2.1 ≤ pairWeight parameter data m s g gp ρ u0 := by
    intro ρ s' u0 b _ hc0 hl out hout
    simp only [hV]
    split_ifs with hrev
    swap
    · exact bot_le
    obtain ⟨q, hq, hmem⟩ := hrev
    obtain ⟨hi, hs, ha, hpos⟩ := finish_reveals_ok tg initial model parameter data m ρ b s' u0 (hparse' ρ) hc0 out
      hout _ hmem index c sp j a i q rfl
    have hmarks := digestMarks_eq (truncateMessageDigest u0) c
    have hhit : opensAt index c sp j a i k (viewOf u0) = 1 := by
      unfold opensAt viewOf
      rw [if_pos]
      refine ⟨by rw [localDigestView_fst, hi], ?_, ?_, ?_⟩
      · rw [localDigestView_snd, ← hmarks, hs]
      · rw [localDigestView_snd, ← hmarks, ha]
      · rw [localDigestView_snd, ← hmarks]
        exact le_trans hpos hq
    unfold pairWeight
    split_ifs
    · rw [hgdef, hhit]
    · simp only [hgp, hgdef, hhit, le_refl]
  have hbound := loop_boundV tg initial model parameter data m hparse' s g gp V hV0 hVfin 1 ENNReal.one_ne_top
    (fun v => opensAt_le_one index c sp j a i k v) (fun _ v => opensAt_le_one index c sp j a i k v)
    (shareOf wbar (landedCount parameter data m s)) (shareOf_ne_top hfair _) Cmax hfair.cmax (hfair.share_le _)
    attempts budget s (related_self s) hcount
  have hsum := pool_sum_le_msg parameter data m s hP (fun _ => False) g
  rw [filter_false'] at hsum
  simp only [if_neg not_false] at hsum
  have hlen : ((P.filter fun q => decide (q.1 = m)).map fun q => g (pview parameter data s q)).sum ≤
      ((P.filter fun q => decide (q.1 = m)).length : ℝ≥0∞) :=
    list_sum_le_length _ _ fun q => opensAt_le_one index c sp j a i k _
  have he : shareOf wbar (landedCount parameter data m s) ≤ wbar := by
    have := shareOf_coef hfair (landedCount parameter data m s) 0 (Nat.zero_le _)
    simpa using this
  refine le_trans hbound (add_le_add (freshAvg_opensAt index c sp j a i k hk) ?_)
  calc _ ≤ wbar * ∑ ρ, poolValue parameter data m s gp ρ := mul_le_mul' he tsub_le_self
    _ ≤ _ := mul_le_mul_right (le_trans hsum hlen) _

end Reveal

end LeanForest.Security.ForsPotential
