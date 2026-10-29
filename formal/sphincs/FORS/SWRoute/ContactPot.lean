import FORS.SWRoute.ContactAcct

/-! **The contact potential A4': cell counts and the coin cap.** With one digest call per pair and
`M = 1`, a signing call uses a cached landed pair of its message only when its uniform start is that
pair's randomizer, with chance `cinv = 1 / |Randomness|` per pair. So the cached-pair part of the
risk that a signature opens a contact's cell is `cinv` times the number of live landed pairs at the
cell (`ncell`). A fresh view opens a given cell with chance `revRate`, so each new pair raises a
cell's count by `revRate` in the mean, and the exponential functional `capC` (an exact martingale,
like `lam`) is at least one as soon as some cell holds `T` live pairs. -/

open OracleComp OracleSpec ENNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.LoopWalk ForsPotential PotentialA

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

/-- A cell of the FORS instances. -/
abbrev Cell := Index × FTree × FLeaf

/-- A view opens a cell: it selects the cell's leaf in the cell's tree at the cell's index. -/
def OpensC (c : Cell) (v : View) : Prop := v.1 = localIdx c.1 ∧ v.2 c.2.1 = c.2.2

/-- The share of one randomizer. -/
noncomputable def cinv : ℝ≥0∞ := (Fintype.card Randomness : ℝ≥0∞)⁻¹

section Counts

variable (parameter : PublicParameter) (data : PublicData)

/-- **The live landed pairs at a cell.** -/
noncomputable def ncell (c : Cell) (s : State) (P : List Pair) (L : QueryLog SigningSpec) : ℕ :=
  ((livePairs L P).filter fun q => decide (OpensC c (pview parameter data s q))).length

/-- A uniform kept view opens a given cell with chance at most `revRate`. -/
theorem freshAvg_opensC (c : Cell) :
    freshAvg Finset.univ (fun v : View => if OpensC c v then (1 : ℝ≥0∞) else 0) ≤ revRate := by
  refine le_trans (le_of_eq ?_) (freshAvg_opensAt c.1 c.2.1 c.2.2)
  congr 1
  funext v
  unfold opensAt OpensC
  by_cases h : v.1 = localIdx c.1 ∧ v.2 c.2.1 = c.2.2 <;> simp [h]

/-- The count after a new pair: the old pairs keep their views; the new one counts if it lands, its
message is live, and its view opens the cell. -/
theorem ncell_withPair {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p firstCall) = none) (L : QueryLog SigningSpec)
    (u : DigestCall → HashOutput) (c : Cell) :
    ncell parameter data c (withPair parameter data s p u) (addPair parameter P p u) L =
      ncell parameter data c s P L +
        (if Landed parameter (blockIndex (u firstCall)) ∧ MsgLive L p.1 ∧ OpensC c (viewOf u) then 1 else 0) := by
  have hpP := not_mem_of_fresh hP hp0
  have hold : (livePairs L P).filter (fun q => decide (OpensC c (pview parameter data (withPair parameter data s p u) q))) =
      (livePairs L P).filter (fun q => decide (OpensC c (pview parameter data s q))) := by
    refine List.filter_congr fun q hq => ?_
    have hqP : q ∈ P := (List.mem_filter.1 hq).1
    have hqp : q ≠ p := fun h => hpP (h ▸ hqP)
    rw [pview_withPair_other s p q hqp u]
  unfold ncell addPair
  by_cases hl : Landed parameter (blockIndex (u firstCall))
  · rw [if_pos hl]
    unfold livePairs
    rw [List.filter_cons]
    by_cases hlive : MsgLive L p.1
    · rw [if_pos (by simpa using hlive), List.filter_cons, pview_withPair_self]
      have hold' := hold
      unfold livePairs at hold'
      by_cases ho : OpensC c (viewOf u)
      · rw [if_pos (by simpa using ho), List.length_cons, hold', if_pos ⟨hl, hlive, ho⟩]
      · rw [if_neg (by simpa using ho), hold', if_neg (fun h => ho h.2.2), add_zero]
    · rw [if_neg (by simpa using hlive)]
      have hold' := hold
      unfold livePairs at hold'
      rw [hold', if_neg (fun h => hlive h.2.1), add_zero]
  · rw [if_neg hl, hold, if_neg (fun h => hl h.1), add_zero]

/-- **A new pair raises a cell's count by at most `revRate` in the mean.** -/
theorem ncell_newPair {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p firstCall) = none) (L : QueryLog SigningSpec) (c : Cell) :
    pairE (fun u => (ncell parameter data c (withPair parameter data s p u) (addPair parameter P p u) L : ℝ≥0∞)) ≤
      ncell parameter data c s P L + revRate := by
  simp only [ncell_withPair parameter data hP hp0 L _ c, Nat.cast_add]
  rw [pairE_add, pairE_const]
  refine add_le_add le_rfl ?_
  have hpt : ∀ u : DigestCall → HashOutput,
      (((if Landed parameter (blockIndex (u firstCall)) ∧ MsgLive L p.1 ∧ OpensC c (viewOf u) then 1 else 0 : ℕ)
        : ℝ≥0∞)) ≤
      if Landed parameter (blockIndex (u firstCall)) then (fun v : View => if OpensC c v then (1 : ℝ≥0∞) else 0)
        (viewOf u) else 0 := by
    intro u
    split_ifs with h1 h2 h3 <;> simp_all
  refine le_trans (pairE_mono hpt) ?_
  rw [pairE_landed parameter (fun v : View => if OpensC c v then (1 : ℝ≥0∞) else 0) 0, mul_zero, add_zero]
  exact le_trans (mul_le_of_le_one_left' ForsPrice.landing_le_one) (freshAvg_opensC c)

end Counts

/-! ### The coin cap -/

section Cap

variable (parameter : PublicParameter) (data : PublicData) (T : ℕ)

/-- **The coin cap**: an exponential martingale over the cells, at least one once some cell holds
`T` live landed pairs. -/
noncomputable def capC (k : ℕ) (s : State) (P : List Pair) (L : QueryLog SigningSpec) : ℝ≥0∞ :=
  ∑ c : Cell, ((3 : ℝ≥0∞) / 2) ^ ncell parameter data c s P L * (1 + revRate / 2) ^ k * ((2 : ℝ≥0∞) / 3) ^ T

theorem three_two_mul : ((3 : ℝ≥0∞) / 2) * ((2 : ℝ≥0∞) / 3) = 1 := by
  rw [← mul_div_assoc, ENNReal.div_mul_cancel (by norm_num) (by norm_num),
    ENNReal.div_self (by norm_num) (by norm_num)]

theorem one_le_three_two : (1 : ℝ≥0∞) ≤ (3 : ℝ≥0∞) / 2 := by
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  norm_num

/-- A full cell makes the cap at least one. -/
theorem one_le_capC {k : ℕ} {s : State} {P : List Pair} {L : QueryLog SigningSpec} (c : Cell)
    (hc : T ≤ ncell parameter data c s P L) : 1 ≤ capC parameter data T k s P L := by
  refine le_trans ?_ (Finset.single_le_sum (f := fun c : Cell => ((3 : ℝ≥0∞) / 2) ^ ncell parameter data c s P L *
    (1 + revRate / 2) ^ k * ((2 : ℝ≥0∞) / 3) ^ T) (fun _ _ => zero_le) (Finset.mem_univ c))
  obtain ⟨e, he⟩ : ∃ e, ncell parameter data c s P L = T + e := ⟨_, (Nat.add_sub_cancel' hc).symm⟩
  rw [he, pow_add]
  have h1 : (1 : ℝ≥0∞) ≤ (1 + revRate / 2) ^ k := one_le_pow₀ le_self_add
  calc (1 : ℝ≥0∞) = 1 * 1 * 1 := by simp
    _ ≤ ((3 : ℝ≥0∞) / 2) ^ e * (1 + revRate / 2) ^ k * (((3 : ℝ≥0∞) / 2) ^ T * ((2 : ℝ≥0∞) / 3) ^ T) := by
        rw [← mul_pow, three_two_mul, one_pow]
        gcongr
        exact one_le_pow₀ one_le_three_two
    _ = _ := by ring

/-- The cap does not grow when no cell count grows and the budget does not grow. -/
theorem capC_mono {k k' : ℕ} {s s' : State} {P P' : List Pair} {L L' : QueryLog SigningSpec} (hk : k' ≤ k)
    (hc : ∀ c, ncell parameter data c s' P' L' ≤ ncell parameter data c s P L) :
    capC parameter data T k' s' P' L' ≤ capC parameter data T k s P L := by
  unfold capC
  refine Finset.sum_le_sum fun c _ => ?_
  gcongr
  · exact one_le_three_two
  · exact hc c
  · exact le_self_add

/-- **The cap under a new pair** keeps its mean (it may only decrease). -/
theorem capC_newPair {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p firstCall) = none) (L : QueryLog SigningSpec) (k : ℕ) :
    pairE (fun u => capC parameter data T k (withPair parameter data s p u) (addPair parameter P p u) L) ≤
      capC parameter data T (k + 1) s P L := by
  unfold capC
  rw [pairE]
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine Finset.sum_le_sum fun c _ => ?_
  have hpt : ∀ u : DigestCall → HashOutput,
      ((3 : ℝ≥0∞) / 2) ^ ncell parameter data c (withPair parameter data s p u) (addPair parameter P p u) L =
        ((3 : ℝ≥0∞) / 2) ^ ncell parameter data c s P L *
          (1 + (if Landed parameter (blockIndex (u firstCall)) ∧ MsgLive L p.1 ∧ OpensC c (viewOf u)
            then 1 / 2 else 0)) := by
    intro u
    rw [ncell_withPair parameter data hP hp0 L u c, pow_add]
    congr 1
    split_ifs
    · rw [pow_one, show (3 : ℝ≥0∞) = 2 + 1 by norm_num, ENNReal.add_div,
        ENNReal.div_self (by norm_num) (by norm_num)]
    · simp
  have hmean : pairE (fun u : DigestCall → HashOutput =>
      (if Landed parameter (blockIndex (u firstCall)) ∧ MsgLive L p.1 ∧ OpensC c (viewOf u) then (1 : ℝ≥0∞) / 2
        else 0)) ≤ revRate / 2 := by
    have hpt2 : ∀ u : DigestCall → HashOutput,
        (if Landed parameter (blockIndex (u firstCall)) ∧ MsgLive L p.1 ∧ OpensC c (viewOf u) then (1 : ℝ≥0∞) / 2
          else 0) ≤
        if Landed parameter (blockIndex (u firstCall)) then
          (fun v : View => (1 / 2 : ℝ≥0∞) * (if OpensC c v then 1 else 0)) (viewOf u) else 0 := by
      intro u
      split_ifs with h1 h2 h3 <;> simp_all
    refine le_trans (pairE_mono hpt2) ?_
    rw [pairE_landed parameter (fun v : View => (1 / 2 : ℝ≥0∞) * (if OpensC c v then 1 else 0)) 0, mul_zero, add_zero]
    have hfa : freshAvg Finset.univ (fun v : View => (1 / 2 : ℝ≥0∞) * (if OpensC c v then 1 else 0)) =
        (1 / 2) * freshAvg Finset.univ (fun v : View => if OpensC c v then (1 : ℝ≥0∞) else 0) := by
      unfold freshAvg
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hfa]
    calc landing * (1 / 2 * freshAvg Finset.univ fun v : View => if OpensC c v then (1 : ℝ≥0∞) else 0)
        ≤ 1 * (1 / 2 * revRate) := by
          gcongr
          · exact ForsPrice.landing_le_one
          · exact freshAvg_opensC c
      _ = revRate / 2 := by rw [one_mul, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul, mul_one]
  calc ∑' u, Pr[= u | ($ᵗ (DigestCall → HashOutput) : ProbComp (DigestCall → HashOutput))] *
        (((3 : ℝ≥0∞) / 2) ^ ncell parameter data c (withPair parameter data s p u) (addPair parameter P p u) L *
          (1 + revRate / 2) ^ k * ((2 : ℝ≥0∞) / 3) ^ T)
      = ((3 : ℝ≥0∞) / 2) ^ ncell parameter data c s P L * (1 + revRate / 2) ^ k * ((2 : ℝ≥0∞) / 3) ^ T *
          pairE (fun u : DigestCall → HashOutput => 1 + (if Landed parameter (blockIndex (u firstCall)) ∧
            MsgLive L p.1 ∧ OpensC c (viewOf u) then (1 : ℝ≥0∞) / 2 else 0)) := by
        unfold pairE
        rw [← ENNReal.tsum_mul_left]
        refine tsum_congr fun u => ?_
        rw [hpt u]
        ring
    _ ≤ ((3 : ℝ≥0∞) / 2) ^ ncell parameter data c s P L * (1 + revRate / 2) ^ k * ((2 : ℝ≥0∞) / 3) ^ T *
          (1 + revRate / 2) := by
        refine mul_le_mul' le_rfl ?_
        rw [pairE_add, pairE_const]
        exact add_le_add le_rfl hmean
    _ = _ := by rw [pow_succ]; ring

end Cap

end FORS.Security.SWRoute
