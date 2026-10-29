import FORS.CoverPotential.GenericWitness
import FORS.Base.Poisson

/-! **The domination of the own-cell forecast, part A: the algebra of the forecast operators.**
A one-coin forecast `termO f d` is the mean of `f` over `d` plus the virtual future: the group
selections of the cached pairs of the live messages, the coins of the future pairs and the fresh
slots. This file proves

* `termO_le_sum`: if `f (e + X) ≤ Σ_i a_i(e) b_i(X)`, then the forecast is at most
  `Σ_i grpAll(a_i)(d) · hTermO(b_i)`: the groups act on the first factor, the future pairs and the
  fresh slots on the second;
* `termO_le_shift`: a base below `h` of the new disclosures has a forecast below the forecast of `h`
  from the empty multiset;
* for a full key (`totalHeight = subtreeHeight`, every digest lands): the group of a message is the
  plain average over its randomizers of the translates by the selected pair's view (`grpM_eq`), and
  the groups commute with the future pairs (`creations_grpAll`). -/

open OracleComp OracleSpec ENNReal NNReal

namespace FORS.Security.SWRoute

variable [Params]

open FORS.Base
open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner
  FORS.Base.Domination FORS.Base.H0 FORS.LoopWalk ForsPotential

set_option linter.unusedSectionVars false

/-! ### Translations and finite sums in the virtual future -/

section Algebra

variable {V : Type}

theorem fresh_shift (U : Finset V) (f : Multiset V → ℝ≥0∞) (e : Multiset V) :
    ∀ m x, fresh U (fun X => f (X + e)) m x = fresh U f m (x + e)
  | 0, _ => rfl
  | m + 1, x => by
      simp only [fresh]
      congr 1
      funext u
      rw [fresh_shift U f e m, add_right_comm]

theorem virtualOnce_shift (U : Finset V) (w : ℝ≥0∞) (f : Multiset V → ℝ≥0∞) (m : ℕ) (coins : List V)
    (e : Multiset V) :
    virtualOnce U w (fun X => f (X + e)) m coins 0 = virtualOnce U w f m coins e := by
  unfold virtualOnce
  calc slotValue (fresh U (fun X => f (X + e)) m) 0 (itemCoins w coins)
      = slotValue (fun x => fresh U f m (x + e)) 0 (itemCoins w coins) :=
        slotValue_congr (fun x => fresh_shift U f e m x) _ _
    _ = _ := by rw [slotValue_translate (fresh U f m) e, zero_add]

theorem virtualOnce_finset_sum {U : Finset V} (hU : U.Nonempty) (w : ℝ≥0∞) {ι : Type} [DecidableEq ι]
    (S : Finset ι) (g : ι → Multiset V → ℝ≥0∞) (m : ℕ) (coins : List V) (d : Multiset V) :
    virtualOnce U w (fun D => ∑ i ∈ S, g i D) m coins d = ∑ i ∈ S, virtualOnce U w (g i) m coins d := by
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      have h := virtualOnce_const_mul (U := U) (w := w) 0 (fun _ => (1 : ℝ≥0∞)) m coins d
      simpa using h
  | insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      rw [virtualOnce_add hU (g a) (fun D => ∑ i ∈ S, g i D), ih]

end Algebra

section Groups

variable {parameter : PublicParameter} {data : PublicData}

theorem grpAll_finset_sum (s : State) (excl : Pair → Prop) {ι : Type} [DecidableEq ι] (S : Finset ι)
    (g : ι → Multiset View → ℝ≥0∞) (Ms : List Message) (d : Multiset View) :
    grpAll parameter data s excl Ms (fun e => ∑ i ∈ S, g i e) d = ∑ i ∈ S, grpAll parameter data s excl Ms (g i) d := by
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact grpAll_const s excl 0 Ms d
  | insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      rw [grpAll_add s excl (g a) (fun e => ∑ i ∈ S, g i e), ih]

theorem grpAll_le_one (s : State) (excl : Pair → Prop) {F : Multiset View → ℝ≥0∞} (hF : ∀ e, F e ≤ 1)
    (Ms : List Message) (d : Multiset View) : grpAll parameter data s excl Ms F d ≤ 1 :=
  le_trans (grpAll_le_of_le s excl hF Ms d) (le_of_eq (grpAll_const s excl 1 Ms d))

end Groups

/-! ### The forecast through a product split -/

section Split

variable (parameter : PublicParameter) (data : PublicData) (w : ℝ≥0∞) (s : State) (Ms : List Message)
  (L : QueryLog SigningSpec) (excl : Pair → Prop)

/-- **The forecast through a product split.** -/
theorem termO_le_sum {f : Multiset View → ℝ≥0∞} {ι : Type} [DecidableEq ι] (S : Finset ι)
    (a b : ι → Multiset View → ℝ≥0∞) (hf : ∀ e X, f (e + X) ≤ ∑ i ∈ S, a i e * b i X)
    (d : Multiset View) (n k : ℕ) :
    termO parameter data w s Ms L excl f d n k ≤
      ∑ i ∈ S, grpAll parameter data s excl (live L Ms) (a i) d * hTermO Finset.univ w landing n k (b i) := by
  have hU : (Finset.univ : Finset View).Nonempty := Finset.univ_nonempty
  have hJ : ∀ J : List View, termBase parameter data w s Ms L excl f d n J ≤
      ∑ i ∈ S, grpAll parameter data s excl (live L Ms) (a i) d * virtualOnce Finset.univ w (b i) n J 0 := by
    intro J
    unfold termBase
    have hpt : ∀ e, virtualOnce Finset.univ w f n J e ≤
        ∑ i ∈ S, virtualOnce Finset.univ w (b i) n J 0 * a i e := by
      intro e
      rw [← virtualOnce_shift]
      calc virtualOnce Finset.univ w (fun X => f (X + e)) n J 0
          ≤ virtualOnce Finset.univ w (fun X => ∑ i ∈ S, a i e * b i X) n J 0 :=
            virtualOnce_mono_base (fun X => by rw [add_comm]; exact hf e X) n J 0
        _ = ∑ i ∈ S, a i e * virtualOnce Finset.univ w (b i) n J 0 := by
            rw [virtualOnce_finset_sum hU w S (fun i X => a i e * b i X)]
            exact Finset.sum_congr rfl fun i _ => virtualOnce_const_mul (a i e) (b i) n J 0
        _ = _ := Finset.sum_congr rfl fun i _ => mul_comm _ _
    calc grpAll parameter data s excl (live L Ms) (virtualOnce Finset.univ w f n J) d
        ≤ grpAll parameter data s excl (live L Ms)
            (fun e => ∑ i ∈ S, virtualOnce Finset.univ w (b i) n J 0 * a i e) d :=
          grpAll_le_of_le s excl hpt _ d
      _ = ∑ i ∈ S, virtualOnce Finset.univ w (b i) n J 0 * grpAll parameter data s excl (live L Ms) (a i) d := by
          rw [grpAll_finset_sum s excl S]
          exact Finset.sum_congr rfl fun i _ => grpAll_const_mul s excl _ (a i) _ d
      _ = _ := Finset.sum_congr rfl fun i _ => mul_comm _ _
  unfold termO hTermO
  calc creations Finset.univ landing (termBase parameter data w s Ms L excl f d n) k []
      ≤ creations Finset.univ landing (fun J => ∑ i ∈ S, grpAll parameter data s excl (live L Ms) (a i) d *
          virtualOnce Finset.univ w (b i) n J 0) k [] := creations_mono hJ k []
    _ = _ := by
        rw [creations_finset_sum]
        exact Finset.sum_congr rfl fun i _ => creations_const_mul _ _ k []

/-- **A base below a function of the new disclosures.** -/
theorem termO_le_shift {F h : Multiset View → ℝ≥0∞} (d : Multiset View) (hF : ∀ Y, F (d + Y) ≤ h Y)
    (n k : ℕ) :
    termO parameter data w s Ms L excl F d n k ≤ termO parameter data w s Ms L excl h 0 n k := by
  unfold termO termBase
  refine creations_mono (fun J => ?_) k []
  have e1 := grpAll_shift (parameter := parameter) (data := data) s excl
    (virtualOnce Finset.univ w F n J) d (live L Ms) 0
  rw [zero_add] at e1
  rw [← e1]
  refine grpAll_le_of_le s excl (fun e => ?_) _ 0
  rw [← virtualOnce_shift Finset.univ w F n J (e + d), ← virtualOnce_shift Finset.univ w h n J e]
  refine virtualOnce_mono_base (fun X => ?_) n J 0
  calc F (X + (e + d)) = F (d + (X + e)) := by congr 1; abel
    _ ≤ h (X + e) := hF _

end Split

/-! ### Full keys: every digest lands -/

section Full

theorem landed_all (hH : totalHeight = subtreeHeight) (parameter : PublicParameter) (i : Index) :
    Landed parameter i := by
  unfold Landed subtreePosition
  have hi : i.val < 2 ^ subtreeHeight := lt_of_lt_of_eq i.isLt (by rw [hH])
  rw [Nat.div_eq_of_lt hi, hH, Nat.sub_self, pow_zero, Nat.mod_one]

theorem landing_one (hH : totalHeight = subtreeHeight) : landing = 1 := by
  unfold landing
  rw [hH, Nat.sub_self]
  simp

theorem stOf_ne_miss (hH : totalHeight = subtreeHeight) (parameter : PublicParameter) (data : PublicData)
    (m : Message) (s : State) (ρ : Randomness) : stOf parameter data m s ρ ≠ .miss := by
  unfold stOf
  cases s.cache (blk parameter data m ρ) with
  | none => simp
  | some u0 => simp [landed_all hH]

theorem walk_one {α : Type} (σ : Equiv.Perm α) (st : α → St) (hst : ∀ r, st r ≠ .miss)
    (item : α → ℝ≥0∞) (fr ex : ℝ≥0∞) (A : ℕ) (r : α) :
    walk σ 1 st item fr ex (A + 1) r = if st r = .hit then item r else fr := by
  cases h : st r with
  | hit => rw [walk_succ_hit item fr ex A h]; rfl
  | miss => exact absurd h (hst r)
  | fresh => rw [walk_succ_fresh item fr ex A h]; simp

theorem gv_one {α : Type} [Fintype α] (σ : Equiv.Perm α) (st : α → St) (hst : ∀ r, st r ≠ .miss)
    (item : α → ℝ≥0∞) (base favg : ℝ≥0∞) (A : ℕ) :
    gv σ 1 st item base favg (A + 1) = ∑ r, if st r = .hit then item r else base := by
  unfold gv
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [walk_one σ st hst]
  by_cases h : st r = .hit
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    have hf : st r = .fresh := by
      cases h' : st r
      · rfl
      · exact absurd h' (hst r)
      · exact absurd h' h
    rw [if_pos hf]

theorem grp_one {α V : Type} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) (A : ℕ) (U : Finset V)
    (st : α → St) (hst : ∀ r, st r ≠ .miss) (ext : α → Multiset V) (F : Multiset V → ℝ≥0∞)
    (d : Multiset V) :
    grp σ 1 (A + 1) U st ext F d = freshAvg Finset.univ (fun r => F (d + if st r = .hit then ext r else 0)) := by
  unfold grp freshAvg
  rw [gv_one σ st hst, Finset.card_univ]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases h : st r = .hit <;> simp [h]

variable (parameter : PublicParameter) (data : PublicData)

/-- What the group of a message adds for a randomizer: the view of a cached pair (unless excluded). -/
noncomputable def gx (s : State) (excl : Pair → Prop) (m : Message) (ρ : Randomness) : Multiset View :=
  if stOf parameter data m s ρ = .hit then extOf parameter data s excl m ρ else 0

theorem digestAttemptLimit_succ : digestAttemptLimit = (digestAttemptLimit - 1) + 1 :=
  (Nat.succ_pred_eq_of_pos (by unfold digestAttemptLimit; positivity)).symm

/-- **The group of a message on a full key**: the average over the randomizers of the translates. -/
theorem grpM_eq (hH : totalHeight = subtreeHeight) (s : State) (excl : Pair → Prop) (m : Message)
    (F : Multiset View → ℝ≥0∞) (d : Multiset View) :
    grpM parameter data s excl m F d = freshAvg Finset.univ (fun ρ => F (d + gx parameter data s excl m ρ)) := by
  unfold grpM gx
  rw [landing_one hH, digestAttemptLimit_succ]
  exact grp_one _ _ _ _ (stOf_ne_miss hH parameter data m s) _ F d

/-- **The groups commute with the future pairs** (full key). -/
theorem creations_grpAll (hH : totalHeight = subtreeHeight) (s : State) (excl : Pair → Prop) {W : Type}
    (U : Finset W) (lam : ℝ≥0∞) (G : List W → Multiset View → ℝ≥0∞) :
    ∀ (Ms : List Message) (d : Multiset View) (k : ℕ) (items : List W),
      creations U lam (fun J => grpAll parameter data s excl Ms (G J) d) k items =
        grpAll parameter data s excl Ms (fun e => creations U lam (fun J => G J e) k items) d
  | [], _, _, _ => rfl
  | m :: Ms, d, k, items => by
      simp only [grpAll, grpM_eq parameter data hH]
      rw [creations_freshAvg Finset.univ
        (fun ρ J => grpAll parameter data s excl Ms (G J) (d + gx parameter data s excl m ρ)) k items]
      congr 1
      funext ρ
      exact creations_grpAll hH s excl U lam G Ms _ k items

end Full

end FORS.Security.SWRoute
