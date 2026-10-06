import LeanSphincs.BridgeForsPotential
import LeanSphincs.BridgeVirtualOnce

/-! The cached digest pairs of a state, seen through the signer `R0, R0 + 1, ...`. Every message
that was not signed yet has one exclusive group (`Walk.grp`) over the statuses of its randomizers;
`stateFn s L excl f` is a base function `f` averaged over the selections of all these groups. The
potentials forecast `stateFn s L excl f` instead of `f`: one more digest query costs one future
pair of coin `w` with `landing · w ≥ (2 - landing) / 2^128`, and a signing call resolves the group
of its message with the exact selection probabilities of the walk. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] digestAttemptLimit

/-- The next randomizer of the walk. -/
def succR : Randomness ≃ Randomness where
  toFun x := x + 1
  invFun x := x - 1
  left_inv x := by simp
  right_inv x := by simp

theorem succR_free (y : Randomness) (j : ℕ) (hj : j < 2 ^ 128 - 1) : succR^[j] (succR y) ≠ y :=
  succ_iterate_ne y j (by omega)

variable [Params]

theorem landing_ne_zero : landing ≠ 0 := by
  unfold landing
  exact ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _)

/-- The rate of the walk: a digest query adds at most this much selection mass. -/
noncomputable def rate5 : ℝ≥0∞ := (1 + (1 - landing)) * ((Fintype.card Randomness : ℕ) : ℝ≥0∞)⁻¹

theorem rate5_le_one : rate5 ≤ 1 := by
  unfold rate5
  rw [card_randomness]
  calc (1 + (1 - landing)) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ ≤ (1 + 1) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ := by
        gcongr; exact tsub_le_self
    _ ≤ ((2 ^ 128 : ℕ) : ℝ≥0∞) * (((2 ^ 128 : ℕ) : ℝ≥0∞))⁻¹ := by
        gcongr
        exact_mod_cast (by norm_num : (1 + 1 : ℕ) ≤ 2 ^ 128)
    _ = 1 := ENNReal.mul_inv_cancel (by exact_mod_cast (by norm_num : (2 : ℕ) ^ 128 ≠ 0)) (ENNReal.natCast_ne_top _)

/-- The coin of a future pair pays the rate of the walk. -/
structure Fair5 (wbar : ℝ≥0∞) : Prop where
  ne_top : wbar ≠ ⊤
  le_one : wbar ≤ 1
  rate : rate5 ≤ landing * wbar

section Defs

variable (parameter : PublicParameter) (data : PublicData)

/-- The excluded randomizers of a message. -/
noncomputable def exB (excl : Pair → Prop) (m : Message) (ρ : Randomness) : Bool :=
  @decide (excl (m, ρ)) (Classical.propDecidable _)

omit [Params] in
theorem exB_iff {excl : Pair → Prop} {m : Message} {ρ : Randomness} : exB excl m ρ = true ↔ excl (m, ρ) := by
  unfold exB
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

omit [Params] in
theorem exB_false (m : Message) : exB (fun _ => False) m = fun _ => false := by
  funext ρ
  exact Bool.eq_false_iff.2 fun h => exB_iff.1 h

/-- The group of one message in a state. -/
noncomputable def grpM (m : Message) (s : State) (excl : Pair → Prop) (h : Multiset View → ℝ≥0∞)
    (d : Multiset View) : ℝ≥0∞ :=
  Walk.grp succR landing digestAttemptLimit (stat parameter data m s) (exB excl m) h d

/-- The messages that were not signed. -/
noncomputable def freshMsgs (L : QueryLog SigningSpec) : List Message :=
  (Finset.univ.filter fun m : Message => ∀ entry ∈ L, entry.1 ≠ m).toList

/-- The groups of a list of messages, nested. -/
noncomputable def foldG (s : State) (excl : Pair → Prop) (l : List Message) (f : Multiset View → ℝ≥0∞) :
    Multiset View → ℝ≥0∞ :=
  l.foldr (fun m h => grpM parameter data m s excl h) f

/-- **The base function seen through the cached pairs of the unsigned messages.** -/
noncomputable def stateFn (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop) (f : Multiset View → ℝ≥0∞) :
    Multiset View → ℝ≥0∞ :=
  foldG parameter data s excl (freshMsgs L) f

/-- The forecast of a base function: future pairs with one coin each, fresh slots, and the groups
of the state. -/
noncomputable def fut (wbar : ℝ≥0∞) (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop)
    (f : Multiset View → ℝ≥0∞) (n k : ℕ) (d : Multiset View) : ℝ≥0∞ :=
  creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar (stateFn parameter data s L excl f) n J d) k []

end Defs

section Basic

variable {parameter : PublicParameter} {data : PublicData}

theorem rep_grpM (m : Message) (s : State) (excl : Pair → Prop) :
    Rep (fun h d => grpM parameter data m s excl h d) :=
  Walk.rep_grp landing_le_one _ _

theorem foldG_nil (s : State) (excl : Pair → Prop) (f : Multiset View → ℝ≥0∞) :
    foldG parameter data s excl [] f = f := rfl

theorem foldG_cons (s : State) (excl : Pair → Prop) (m : Message) (l : List Message) (f : Multiset View → ℝ≥0∞) :
    foldG parameter data s excl (m :: l) f = grpM parameter data m s excl (foldG parameter data s excl l f) := rfl

theorem rep_foldG (s : State) (excl : Pair → Prop) (l : List Message) :
    Rep (fun f d => foldG parameter data s excl l f d) := by
  induction l with
  | nil => exact Rep.id
  | cons m l ih =>
      obtain ⟨K, hfin, hK⟩ := (rep_grpM (parameter := parameter) (data := data) m s excl).comp ih
      exact ⟨K, hfin, fun f d => by beta_reduce; rw [foldG_cons]; exact hK f d⟩

theorem rep_stateFn (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop) :
    Rep (fun f d => stateFn parameter data s L excl f d) := rep_foldG s excl _

theorem stateFn_props (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop) {f : Multiset View → ℝ≥0∞}
    (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤) :
    Monotone' (stateFn parameter data s L excl f) ∧ Supermodular (stateFn parameter data s L excl f) ∧
      ∀ D, stateFn parameter data s L excl f D ≠ ⊤ :=
  (rep_stateFn s L excl).props hf

theorem foldG_const (s : State) (excl : Pair → Prop) (K : ℝ≥0∞) (l : List Message) :
    foldG parameter data s excl l (fun _ => K) = fun _ => K := by
  induction l with
  | nil => exact foldG_nil s excl _
  | cons m l ih =>
      funext d
      rw [foldG_cons, ih]
      unfold grpM
      exact Walk.grp_const landing_le_one _ _ K d

theorem le_foldG (s : State) (excl : Pair → Prop) {f : Multiset View → ℝ≥0∞} (hf : Monotone' f)
    (l : List Message) (d : Multiset View) : f d ≤ foldG parameter data s excl l f d := by
  induction l with
  | nil => rw [foldG_nil]
  | cons m l ih =>
      rw [foldG_cons]
      unfold grpM
      exact le_trans ih (Walk.le_grp landing_le_one ((rep_foldG s excl l).monotone' hf) _ _ d)

theorem le_stateFn (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop) {f : Multiset View → ℝ≥0∞}
    (hf : Monotone' f) (d : Multiset View) : f d ≤ stateFn parameter data s L excl f d :=
  le_foldG s excl hf _ d

/-- The nested groups do not depend on the order of the messages. -/
theorem foldG_perm (s : State) (excl : Pair → Prop) {l l' : List Message} (h : l.Perm l')
    (f : Multiset View → ℝ≥0∞) : foldG parameter data s excl l f = foldG parameter data s excl l' f := by
  unfold foldG
  refine h.foldr_eq' (fun x _ y _ z => ?_) f
  funext d
  exact (rep_grpM y s excl).comm (rep_grpM x s excl) z d

/-- Groups only read the digest blocks of their message. -/
theorem stat_congr {m : Message} {s s' : State}
    (h : ∀ ρ call, s'.cache (blk parameter data m ρ call) = s.cache (blk parameter data m ρ call)) :
    stat parameter data m s' = stat parameter data m s := by
  funext ρ
  unfold stat
  rw [h ρ 0, h ρ 1]

theorem foldG_congr {s s' : State} (excl : Pair → Prop) (f : Multiset View → ℝ≥0∞) (l : List Message)
    (h : ∀ m ∈ l, stat parameter data m s' = stat parameter data m s) :
    foldG parameter data s' excl l f = foldG parameter data s excl l f := by
  induction l with
  | nil => rw [foldG_nil, foldG_nil]
  | cons m l ih =>
      rw [foldG_cons, foldG_cons, ih fun m' hm' => h m' (List.mem_cons_of_mem _ hm')]
      unfold grpM
      rw [h m (List.mem_cons_self ..)]

theorem mem_freshMsgs {L : QueryLog SigningSpec} {m : Message} : m ∈ freshMsgs L ↔ ∀ entry ∈ L, entry.1 ≠ m := by
  simp [freshMsgs]

/-- The state function only reads the statuses of the unsigned messages. -/
theorem stateFn_congr {s s' : State} (L : QueryLog SigningSpec) (excl : Pair → Prop) (f : Multiset View → ℝ≥0∞)
    (h : ∀ m, (∀ entry ∈ L, entry.1 ≠ m) → stat parameter data m s' = stat parameter data m s) :
    stateFn parameter data s' L excl f = stateFn parameter data s L excl f :=
  foldG_congr excl f _ fun m hm => h m (mem_freshMsgs.1 hm)

omit [Params] in
theorem fresh_append {L : QueryLog SigningSpec} {m m' : Message} {r : Option Signature} :
    (∀ entry ∈ (L ++ [⟨m, r⟩] : QueryLog SigningSpec), entry.1 ≠ m') ↔ (∀ entry ∈ L, entry.1 ≠ m') ∧ m ≠ m' := by
  constructor
  · intro h
    exact ⟨fun e he => h e (List.mem_append_left _ he),
      h ⟨m, r⟩ (List.mem_append_right _ (List.mem_singleton_self _))⟩
  · rintro ⟨h, hne⟩ e he
    rcases List.mem_append.1 he with he | he
    · exact h e he
    · rw [List.mem_singleton] at he
      subst he
      exact hne

/-- The signature returned for a message does not matter. -/
theorem stateFn_log (s : State) (L : QueryLog SigningSpec) (m : Message) (r r' : Option Signature)
    (excl : Pair → Prop) (f : Multiset View → ℝ≥0∞) :
    stateFn parameter data s (L ++ [⟨m, r⟩]) excl f = stateFn parameter data s (L ++ [⟨m, r'⟩]) excl f := by
  unfold stateFn freshMsgs
  rw [Finset.filter_congr (fun m' _ => (fresh_append (L := L) (m := m) (r := r)).trans
    (fresh_append (L := L) (m := m) (r := r')).symm)]

/-- After the message is signed, the state function is that of the other messages. -/
theorem stateFn_after {s s' : State} (L : QueryLog SigningSpec) (m : Message) (r : Option Signature)
    (excl : Pair → Prop) (f : Multiset View → ℝ≥0∞)
    (hother : ∀ q : Pair, q.1 ≠ m → ∀ call, s'.cache (pblk parameter data q call) = s.cache (pblk parameter data q call)) :
    stateFn parameter data s' (L ++ [⟨m, r⟩]) excl f = stateFn parameter data s (L ++ [⟨m, none⟩]) excl f := by
  rw [stateFn_log s' L m r none]
  refine stateFn_congr _ excl f fun m' hm' => stat_congr fun ρ call => ?_
  exact hother (m', ρ) (fun h => (fresh_append.1 hm').2 h.symm) call

/-- Without a new pair, an ordinary query keeps the statuses. -/
theorem stat_same {x : HashInput} {s s' : State} (hext : Extends s s') (hother : ∀ y, y ≠ x → s'.cache y = s.cache y)
    (hnot : ¬∃ p call, x = pblk parameter data p call ∧ s.cache (pblk parameter data p 0) = none)
    {P : List Pair} (hP : PInv parameter data s P) (m : Message) :
    stat parameter data m s' = stat parameter data m s := by
  have hkeep : ∀ y, s.cache y ≠ none → s'.cache y = s.cache y := by
    intro y hy
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hy
    rw [hv]; exact hext.1 y v hv
  funext ρ
  have hzero : s'.cache (blk parameter data m ρ 0) = s.cache (blk parameter data m ρ 0) := by
    by_cases hx : x = pblk parameter data (m, ρ) 0
    · by_cases hn : s.cache (pblk parameter data (m, ρ) 0) = none
      · exact absurd ⟨(m, ρ), 0, hx, hn⟩ hnot
      · exact hkeep _ hn
    · exact hother _ (Ne.symm hx)
  unfold stat
  rw [hzero]
  cases h0 : s.cache (blk parameter data m ρ 0) with
  | none => rfl
  | some u0 =>
      simp only [Option.map_some]
      by_cases hl : Landed parameter (blockIndex u0)
      · rw [if_pos hl, if_pos hl, hkeep _ (hP.second (m, ρ) ⟨u0, h0, hl⟩)]
      · rw [if_neg hl, if_neg hl]

/-- **The group of an unsigned message, taken out.** -/
theorem stateFn_split (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop) (f : Multiset View → ℝ≥0∞)
    (m : Message) (hm : ∀ entry ∈ L, entry.1 ≠ m) (r : Option Signature) :
    stateFn parameter data s L excl f =
      grpM parameter data m s excl (stateFn parameter data s (L ++ [⟨m, r⟩]) excl f) := by
  unfold stateFn
  have hset : (Finset.univ.filter fun m' : Message => ∀ entry ∈ L, entry.1 ≠ m') =
      insert m (Finset.univ.filter fun m' : Message => ∀ entry ∈ (L ++ [⟨m, r⟩] : QueryLog SigningSpec), entry.1 ≠ m') := by
    ext m'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, List.mem_append,
      List.mem_singleton]
    constructor
    · intro h
      by_cases h' : m' = m
      · exact Or.inl h'
      · refine Or.inr fun entry he => ?_
        rcases he with he | he
        · exact h entry he
        · subst he; exact fun h'' => h' h''.symm
    · rintro (h | h)
      · subst h; exact hm
      · exact fun entry he => h entry (Or.inl he)
  have hnot : m ∉ (Finset.univ.filter fun m' : Message =>
      ∀ entry ∈ (L ++ [⟨m, r⟩] : QueryLog SigningSpec), entry.1 ≠ m') := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall]
    exact ⟨⟨m, r⟩, by simp, by simp⟩
  have hperm : (freshMsgs L).Perm (m :: freshMsgs (L ++ [⟨m, r⟩])) := by
    unfold freshMsgs
    rw [hset]
    exact Finset.toList_insert hnot
  rw [foldG_perm s excl hperm f, foldG_cons]

/-- Without cached digest blocks the state function is the base function. -/
theorem grpM_clean (m : Message) (s : State) (excl : Pair → Prop)
    (hclean : ∀ ρ, s.cache (blk parameter data m ρ 0) = none) {f : Multiset View → ℝ≥0∞} (d : Multiset View) :
    grpM parameter data m s excl f d = f d := by
  have hσ : stat parameter data m s = fun _ => none := by
    funext ρ
    simp [stat, hclean ρ]
  unfold grpM Walk.grp
  rw [hσ]
  have hat : ∀ x0 : Randomness, Walk.grpAt succR landing digestAttemptLimit (fun _ => none)
      (exB excl m) f d x0 = f d := by
    intro x0
    unfold Walk.grpAt
    have hb : Walk.baseOf (fun _ : Randomness => (none : Option (Option View))) f d x0 = f d := by simp [Walk.baseOf]
    have hpay : Walk.pay (fun _ : Randomness => (none : Option (Option View))) (exB excl m) f d (f d) =
        fun _ => f d := by
      funext x; simp [Walk.pay]
    rw [hb, hpay]
    exact Walk.val_const _ _ _ (Walk.sOf_add_tOf landing_le_one _) (f d) _ x0
  simp only [hat, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, Walk.card_inv_mul_card, one_mul]

theorem foldG_clean (s : State) (excl : Pair → Prop) (hclean : ∀ m ρ, s.cache (blk parameter data m ρ 0) = none)
    (f : Multiset View → ℝ≥0∞) (l : List Message) : foldG parameter data s excl l f = f := by
  induction l with
  | nil => exact foldG_nil s excl f
  | cons m l ih =>
      funext d
      rw [foldG_cons, grpM_clean m s excl (hclean m), ih]

theorem stateFn_clean (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop)
    (hclean : ∀ m ρ, s.cache (blk parameter data m ρ 0) = none) (f : Multiset View → ℝ≥0∞) :
    stateFn parameter data s L excl f = f := foldG_clean s excl hclean f _

end Basic

/-! ### A new pair -/

section NewPair5

variable {parameter : PublicParameter} {data : PublicData}

theorem stat_withPair (s : State) (m : Message) (y : Randomness) (u0 u1 : HashOutput) :
    stat parameter data m (withPair parameter data s (m, y) u0 u1) =
      Function.update (stat parameter data m s) y
        (if Landed parameter (blockIndex u0) then some (some (viewOf u0 u1)) else some none) := by
  funext ρ
  by_cases hρ : ρ = y
  · subst hρ
    have h0 := withPair_zero (parameter := parameter) (data := data) s (m, ρ) u0 u1
    have h1 := withPair_one (parameter := parameter) (data := data) s (m, ρ) u0 u1
    simp only [stat, Function.update_self]
    change ((withPair parameter data s (m, ρ) u0 u1).cache (pblk parameter data (m, ρ) 0)).map _ = _
    rw [h0]
    change (Option.some u0).map (fun u0 => if Landed parameter (blockIndex u0) then
      some (((withPair parameter data s (m, ρ) u0 u1).cache (pblk parameter data (m, ρ) 1)).elim (viewOf u0 u0) (viewOf u0))
      else none) = _
    rw [Option.map_some]
    split_ifs
    · rw [h1]; rfl
    · rfl
  · rw [Function.update_of_ne hρ]
    have hne : ((m, ρ) : Pair) ≠ (m, y) := fun h => hρ (Prod.ext_iff.1 h).2
    have h0 := withPair_other_pair (parameter := parameter) (data := data) s (m, y) (m, ρ) hne u0 u1 0
    have h1 := withPair_other_pair (parameter := parameter) (data := data) s (m, y) (m, ρ) hne u0 u1 1
    unfold stat
    change ((withPair parameter data s (m, y) u0 u1).cache (pblk parameter data (m, ρ) 0)).map
      (fun u0' => if Landed parameter (blockIndex u0') then
        some (((withPair parameter data s (m, y) u0 u1).cache (pblk parameter data (m, ρ) 1)).elim
          (viewOf u0' u0') (viewOf u0')) else none) = _
    rw [h0, h1]

/-- The groups of the other messages do not see a new pair. -/
theorem stateFn_withPair_other (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop)
    (f : Multiset View → ℝ≥0∞) (p : Pair) (u0 u1 : HashOutput) (hsigned : ¬∀ entry ∈ L, entry.1 ≠ p.1) :
    stateFn parameter data (withPair parameter data s p u0 u1) L excl f = stateFn parameter data s L excl f := by
  refine stateFn_congr L excl f fun m hm => stat_congr fun ρ call => ?_
  have hne : ((m, ρ) : Pair) ≠ p := fun h => hsigned (by rw [← h]; exact hm)
  exact withPair_other_pair s p (m, ρ) hne u0 u1 call

/-- **One more digest pair, on the state function.** -/
theorem stateFn_newPair {f : Multiset View → ℝ≥0∞} (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤)
    (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop) (p : Pair)
    (hp0 : s.cache (pblk parameter data p 0) = none) (hex : ¬excl p) (d : Multiset View) :
    pairE (fun u0 u1 => stateFn parameter data (withPair parameter data s p u0 u1) L excl f d) ≤
      (1 - rate5) * stateFn parameter data s L excl f d + rate5 * avgT (stateFn parameter data s L excl f) d := by
  set S := stateFn parameter data s L excl f with hS
  have hSp := stateFn_props (parameter := parameter) (data := data) s L excl hf
  by_cases hm : ∀ entry ∈ L, entry.1 ≠ p.1
  · obtain ⟨m, y⟩ := p
    set h := stateFn parameter data s (L ++ [⟨m, none⟩]) excl f with hh
    have hhp := stateFn_props (parameter := parameter) (data := data) s (L ++ [⟨m, none⟩]) excl hf
    have hsplit : S = grpM parameter data m s excl h := stateFn_split s L excl f m hm none
    have hrest : ∀ u0 u1, stateFn parameter data (withPair parameter data s (m, y) u0 u1) (L ++ [⟨m, none⟩]) excl f = h := by
      intro u0 u1
      refine stateFn_withPair_other s _ excl f (m, y) u0 u1 fun hall => ?_
      exact hall ⟨m, none⟩ (List.mem_append_right _ (List.mem_singleton_self _)) rfl
    set F : View → ℝ≥0∞ := fun v => Walk.grp succR landing digestAttemptLimit
      (Function.update (stat parameter data m s) y (some (some v))) (exB excl m) h d with hF
    set C : ℝ≥0∞ := Walk.grp succR landing digestAttemptLimit
      (Function.update (stat parameter data m s) y (some none)) (exB excl m) h d with hC
    have hpoint : (fun u0 u1 => stateFn parameter data (withPair parameter data s (m, y) u0 u1) L excl f d) =
        fun u0 u1 => if Landed parameter (blockIndex u0) then F (viewOf u0 u1) else C := by
      funext u0 u1
      rw [stateFn_split _ L excl f m hm none, hrest u0 u1]
      unfold grpM
      rw [stat_withPair]
      by_cases hl : Landed parameter (blockIndex u0)
      · rw [if_pos hl, if_pos hl]
      · rw [if_neg hl, if_neg hl]
    rw [hpoint, pairE_landed parameter F C]
    have hσy : stat parameter data m s y = none := by
      have : s.cache (blk parameter data m y 0) = none := hp0
      simp [stat, this]
    have := Walk.grp_avg_step (e := succR) (p := landing) (L := digestAttemptLimit) landing_le_one landing_ne_zero
      (2 ^ 128 - 1) (by unfold digestAttemptLimit; norm_num) (by unfold digestAttemptLimit; norm_num)
      succR_free hhp (stat parameter data m s) y hσy (exB excl m) (Bool.eq_false_iff.2 fun h => hex (exB_iff.1 h))
      rate5 rfl rate5_le_one d
    rw [hsplit]
    exact this
  · have hconst : ∀ u0 u1, stateFn parameter data (withPair parameter data s p u0 u1) L excl f d = S d :=
      fun u0 u1 => by rw [stateFn_withPair_other s L excl f p u0 u1 hm]
    simp only [hconst, pairE_const]
    calc S d = (1 - rate5) * S d + rate5 * S d := by
          rw [← add_mul, tsub_add_cancel_of_le rate5_le_one, one_mul]
      _ ≤ _ := by gcongr; exact le_avgT hSp.1 d

/-- **A new landed pair, seen by itself.** -/
theorem stateFn_newPair_self {f : Multiset View → ℝ≥0∞} (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤)
    (s : State) (L : QueryLog SigningSpec) (p : Pair) (hp0 : s.cache (pblk parameter data p 0) = none)
    (u0 u1 : HashOutput) (hl : Landed parameter (blockIndex u0)) (d : Multiset View) :
    stateFn parameter data (withPair parameter data s p u0 u1) L (· = p) f d ≤
      stateFn parameter data s L (fun _ => False) f d := by
  -- the groups of the other messages never exclude anything
  have hother : ∀ (s' : State) (l : List Message), p.1 ∉ l →
      foldG parameter data s' (· = p) l f = foldG parameter data s' (fun _ => False) l f := by
    intro s' l
    induction l with
    | nil => intro _; rw [foldG_nil, foldG_nil]
    | cons m l ih =>
        intro hnot
        have hm : m ≠ p.1 := fun h => hnot (h ▸ List.mem_cons_self ..)
        rw [foldG_cons, foldG_cons, ih fun h => hnot (List.mem_cons_of_mem _ h)]
        unfold grpM
        have hex : exB (· = p) m = exB (fun _ => False) m := by
          rw [exB_false]
          funext ρ
          have : ((m, ρ) : Pair) ≠ p := fun h => hm (congrArg Prod.fst h)
          exact Bool.eq_false_iff.2 fun h => this (exB_iff.1 h)
        rw [hex]
  by_cases hm : ∀ entry ∈ L, entry.1 ≠ p.1
  · obtain ⟨m, y⟩ := p
    have hnot : m ∉ freshMsgs (L ++ [⟨m, none⟩]) := by
      rw [mem_freshMsgs]
      intro hall
      exact hall ⟨m, none⟩ (List.mem_append_right _ (List.mem_singleton_self _)) rfl
    set h := stateFn parameter data s (L ++ [⟨m, none⟩]) (fun _ => False) f with hh
    have hhp := stateFn_props (parameter := parameter) (data := data) s (L ++ [⟨m, none⟩]) (fun _ => False) hf
    have hrest : stateFn parameter data (withPair parameter data s (m, y) u0 u1) (L ++ [⟨m, none⟩]) (· = (m, y)) f = h := by
      unfold stateFn
      rw [hother _ _ hnot]
      exact stateFn_withPair_other s _ _ f (m, y) u0 u1 fun hall => hall ⟨m, none⟩ (List.mem_append_right _ (List.mem_singleton_self _)) rfl
    rw [stateFn_split _ L _ f m hm none, hrest, stateFn_split s L _ f m hm none]
    unfold grpM
    rw [stat_withPair, if_pos hl]
    have hσy : stat parameter data m s y = none := by
      have : s.cache (blk parameter data m y 0) = none := hp0
      simp [stat, this]
    have := Walk.grp_landed_excl_le (e := succR) (L := digestAttemptLimit) landing_le_one hhp.1
      (stat parameter data m s) y hσy (viewOf u0 u1) (fun _ => false) d
    have hex1 : exB (· = ((m, y) : Pair)) m = fun x => decide (x = y) || false := by
      funext ρ
      refine Bool.eq_iff_iff.2 ?_
      rw [exB_iff, Bool.or_false, decide_eq_true_eq]
      exact ⟨fun h => (Prod.ext_iff.1 h).2, fun h => by rw [h]⟩
    rw [hex1, exB_false]
    exact this
  · have hnot : p.1 ∉ freshMsgs L := fun h => hm (mem_freshMsgs.1 h)
    unfold stateFn
    rw [hother _ _ hnot]
    exact le_of_eq (congrFun (stateFn_withPair_other s L _ f p u0 u1 hm) d)

end NewPair5

/-! ### Forecasts -/

section Fut

variable {parameter : PublicParameter} {data : PublicData} {wbar : ℝ≥0∞}

theorem rep_fut (hw : wbar ≤ 1) (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop) (n k : ℕ) :
    Rep (fun f d => fut parameter data wbar s L excl f n k d) := by
  have h1 := rep_creations (Finset.univ : Finset View) landing_le_one
    (fun J f d => virtualOnce Finset.univ wbar f n J d) (fun J => rep_virtualOnce Finset.univ hw n J) k []
  exact h1.comp (rep_stateFn s L excl)

theorem fut_mono_count (hw : wbar ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤)
    (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') (d : Multiset View) :
    fut parameter data wbar s L excl f n k d ≤ fut parameter data wbar s L excl f n k' d :=
  creations_mono_count Finset.univ_nonempty landing_le_one
    (fun v I => virtualOnce_le_cons Finset.univ_nonempty hw (stateFn_props s L excl hf).1
      (stateFn_props s L excl hf).2.1 (stateFn_props s L excl hf).2.2 n I v d)
    (fun _ _ h => virtualOnce_perm n h d) hk _

/-- The forecast only adds disclosures. -/
theorem le_fut (hw : wbar ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤)
    (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop) (n k : ℕ) (d : Multiset View) :
    f d ≤ fut parameter data wbar s L excl f n k d := by
  have hS := stateFn_props (parameter := parameter) (data := data) s L excl hf
  calc f d ≤ stateFn parameter data s L excl f d := le_stateFn s L excl hf.1 d
    _ ≤ virtualOnce Finset.univ wbar (stateFn parameter data s L excl f) n [] d :=
        base_le_virtualOnce Finset.univ_nonempty hw hS.1 hS.2.1 hS.2.2 n [] d
    _ ≤ _ := fut_mono_count (k := 0) hw hf s L excl n (Nat.zero_le k) d

theorem fut_congr {s s' : State} (L : QueryLog SigningSpec) (excl : Pair → Prop) (f : Multiset View → ℝ≥0∞)
    (h : ∀ m, (∀ entry ∈ L, entry.1 ≠ m) → stat parameter data m s' = stat parameter data m s)
    (n k : ℕ) (d : Multiset View) :
    fut parameter data wbar s' L excl f n k d = fut parameter data wbar s L excl f n k d := by
  unfold fut
  rw [stateFn_congr L excl f h]

theorem fut_clean (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop)
    (hclean : ∀ m ρ, s.cache (blk parameter data m ρ 0) = none) (f : Multiset View → ℝ≥0∞) (n k : ℕ)
    (d : Multiset View) :
    fut parameter data wbar s L excl f n k d =
      creations Finset.univ landing (fun J => virtualOnce Finset.univ wbar f n J d) k [] := by
  unfold fut
  rw [stateFn_clean s L excl hclean f]

theorem grpM_excl_le (m : Message) (s : State) (excl : Pair → Prop) {h : Multiset View → ℝ≥0∞}
    (hmono : Monotone' h) (D : Multiset View) :
    grpM parameter data m s excl h D ≤ grpM parameter data m s (fun _ => False) h D := by
  unfold grpM
  exact Walk.grp_ex_mono hmono _ (fun x hx => (exB_iff.1 hx).elim) D

/-- Excluding a pair lowers the forecast. -/
theorem fut_excl_le (hw : wbar ≤ 1) {f : Multiset View → ℝ≥0∞} (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤)
    (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop) (n k : ℕ) (d : Multiset View) :
    fut parameter data wbar s L excl f n k d ≤ fut parameter data wbar s L (fun _ => False) f n k d := by
  have hR := rep_creations (Finset.univ : Finset View) landing_le_one
    (fun J f d => virtualOnce Finset.univ wbar f n J d) (fun J => rep_virtualOnce Finset.univ hw n J) k []
  refine hR.map_mono (fun D => ?_) d
  unfold stateFn
  generalize freshMsgs L = l
  induction l generalizing D with
  | nil => rw [foldG_nil, foldG_nil]
  | cons m l ih =>
      rw [foldG_cons, foldG_cons]
      calc grpM parameter data m s excl (foldG parameter data s excl l f) D
          ≤ grpM parameter data m s excl (foldG parameter data s (fun _ => False) l f) D :=
            (rep_grpM m s excl).map_mono (fun D' => ih D') D
        _ ≤ _ := grpM_excl_le m s excl ((rep_foldG s (fun _ => False) l).monotone' hf.1) D

/-- Forecasts are linear in the base function. -/
theorem fut_add (hw : wbar ≤ 1) (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop)
    (f g : Multiset View → ℝ≥0∞) (n k : ℕ) (d : Multiset View) :
    fut parameter data wbar s L excl (fun D => f D + g D) n k d =
      fut parameter data wbar s L excl f n k d + fut parameter data wbar s L excl g n k d :=
  (rep_fut hw s L excl n k).map_add f g d

theorem fut_const_mul (hw : wbar ≤ 1) (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop) (c : ℝ≥0∞)
    (f : Multiset View → ℝ≥0∞) (n k : ℕ) (d : Multiset View) :
    fut parameter data wbar s L excl (fun D => c * f D) n k d = c * fut parameter data wbar s L excl f n k d :=
  (rep_fut hw s L excl n k).map_const_mul c f d

theorem fut_mono_base (hw : wbar ≤ 1) (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop)
    {f g : Multiset View → ℝ≥0∞} (hfg : ∀ D, f D ≤ g D) (n k : ℕ) (d : Multiset View) :
    fut parameter data wbar s L excl f n k d ≤ fut parameter data wbar s L excl g n k d :=
  (rep_fut hw s L excl n k).map_mono hfg d

theorem fut_freshAvg (hw : wbar ≤ 1) (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop)
    {W : Type} (T : Finset W) (g : W → Multiset View → ℝ≥0∞) (n k : ℕ) (d : Multiset View) :
    fut parameter data wbar s L excl (fun D => freshAvg T fun i => g i D) n k d =
      freshAvg T fun i => fut parameter data wbar s L excl (g i) n k d :=
  (rep_fut hw s L excl n k).map_freshAvg T g d

theorem fut_const (hw : wbar ≤ 1) (s : State) (L : QueryLog SigningSpec) (excl : Pair → Prop) (c : ℝ≥0∞)
    (n k : ℕ) (d : Multiset View) : fut parameter data wbar s L excl (fun _ => c) n k d = c := by
  unfold fut stateFn
  rw [foldG_const]
  simp only [virtualOnce_const Finset.univ_nonempty hw]
  exact creations_const Finset.univ_nonempty landing_le_one c k []

/-- Expectation over a fresh pair commutes with operators that are combinations of translates. -/
theorem pairE_rep {T : (Multiset View → ℝ≥0∞) → Multiset View → ℝ≥0∞} (hT : Rep T)
    (G : HashOutput → HashOutput → Multiset View → ℝ≥0∞) (d : Multiset View) :
    pairE (fun u0 u1 => T (G u0 u1) d) = T (fun D => pairE (fun u0 u1 => G u0 u1 D)) d := by
  unfold pairE
  rw [hT.map_tsum]
  refine tsum_congr fun u0 => ?_
  rw [hT.map_tsum]

/-- **One more digest pair costs one future pair.** -/
theorem fut_newPair (hfair : Fair5 wbar) {f : Multiset View → ℝ≥0∞}
    (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤) (s : State) (L : QueryLog SigningSpec)
    (excl : Pair → Prop) (p : Pair) (hp0 : s.cache (pblk parameter data p 0) = none) (hex : ¬excl p)
    (n k : ℕ) (d : Multiset View) :
    pairE (fun u0 u1 => fut parameter data wbar (withPair parameter data s p u0 u1) L excl f n k d) ≤
      fut parameter data wbar s L excl f n (k + 1) d := by
  have hR := rep_creations (Finset.univ : Finset View) landing_le_one
    (fun J f d => virtualOnce Finset.univ wbar f n J d) (fun J => rep_virtualOnce Finset.univ hfair.le_one n J) k []
  have h1 := pairE_rep hR (fun u0 u1 => stateFn parameter data (withPair parameter data s p u0 u1) L excl f) d
  have h2 := hR.map_mono (fun D => stateFn_newPair hf s L excl p hp0 hex D) d
  have h3 := creations_avg_step landing_le_one hfair.le_one hfair.rate
    (stateFn_props (parameter := parameter) (data := data) s L excl hf) n d k []
  unfold fut
  exact le_trans (le_of_eq h1) (le_trans h2 h3)

/-- **A new landed candidate** forecasts with the groups it found, its own item excluded. -/
theorem fut_newPair_self (hw : wbar ≤ 1) {f : Multiset View → ℝ≥0∞}
    (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤) (s : State) (L : QueryLog SigningSpec) (p : Pair)
    (hp0 : s.cache (pblk parameter data p 0) = none) (u0 u1 : HashOutput) (hl : Landed parameter (blockIndex u0))
    (n k : ℕ) (d : Multiset View) :
    fut parameter data wbar (withPair parameter data s p u0 u1) L (· = p) f n k d ≤
      fut parameter data wbar s L (fun _ => False) f n k d := by
  have hR := rep_creations (Finset.univ : Finset View) landing_le_one
    (fun J f d => virtualOnce Finset.univ wbar f n J d) (fun J => rep_virtualOnce Finset.univ hw n J) k []
  exact hR.map_mono (fun D => stateFn_newPair_self hf s L p hp0 u0 u1 hl D) d

end Fut

/-! ### Signing -/

section Sign5

variable {parameter : PublicParameter} {data : PublicData} {wbar : ℝ≥0∞}

/-- **The group of the signed message pays the signing call.** The value before the disclosure,
the gain of a fresh uniform view, and the gains of the known landed values weighted by the exact
selection probabilities of the walk are at most the value with one more slot and the group. -/
theorem sign_combine (hw : wbar ≤ 1) {h : Multiset View → ℝ≥0∞} (hh : Monotone' h ∧ Supermodular h ∧ ∀ D, h D ≠ ⊤)
    (m : Message) (s : State) (excl : Pair → Prop) (n : ℕ) (J : List View) (d : Multiset View) :
    virtualOnce Finset.univ wbar h n J d +
        freshAvg Finset.univ (fun u => virtualOnce Finset.univ wbar h n J (d + {u}) - virtualOnce Finset.univ wbar h n J d) +
        ((Fintype.card Randomness : ℕ) : ℝ≥0∞)⁻¹ * ∑ ρ, Walk.val (fun x : Randomness => x + 1)
          (Walk.sOf landing (stat parameter data m s)) (Walk.tOf landing (stat parameter data m s))
          (walkPay parameter data m s (fun _ => 0) (fun ρ v => if excl (m, ρ) then 0 else
            virtualOnce Finset.univ wbar h n J (d + {v}) - virtualOnce Finset.univ wbar h n J d)) 0
          digestAttemptLimit ρ ≤
      virtualOnce Finset.univ wbar (grpM parameter data m s excl h) (n + 1) J d := by
  set G := virtualOnce Finset.univ wbar h n J with hG
  set Hf := virtualOnce Finset.univ wbar h (n + 1) J with hHf
  have hGp := virtualOnce_props (U := (Finset.univ : Finset View)) Finset.univ_nonempty hw hh.1 hh.2.1 hh.2.2 n J
  have hHp := virtualOnce_props (U := (Finset.univ : Finset View)) Finset.univ_nonempty hw hh.1 hh.2.1 hh.2.2 (n + 1) J
  have hHeq : ∀ e, Hf e = freshAvg Finset.univ fun u => G (e + {u}) := by
    intro e
    have := virtualOnce_succ (U := (Finset.univ : Finset View)) (w := wbar) (f := h) n [] J e
    simpa [itemCoins, slotValue] using this
  have h1 : G d + freshAvg Finset.univ (fun u => G (d + {u}) - G d) ≤ Hf d := by
    have := once_slot_ge (U := (Finset.univ : Finset View)) Finset.univ_nonempty hw hh.1 hh.2.1 hh.2.2 n [] J d
    simp only [List.map_nil, List.sum_nil, add_zero, List.nil_append] at this
    exact this
  have hgain : ∀ v, G (d + {v}) - G d ≤ gain Hf d v := by
    intro v
    unfold gain
    refine ENNReal.le_sub_of_add_le_left (hHp.2.2 d) ?_
    rw [hHeq d, hHeq (d + {v})]
    calc (freshAvg Finset.univ fun u => G (d + {u})) + (G (d + {v}) - G d)
        = freshAvg Finset.univ (fun u => G (d + {u}) + (G (d + {v}) - G d)) := by
          rw [freshAvg_add, freshAvg_const _ Finset.univ_nonempty]
      _ ≤ _ := freshAvg_mono _ fun u _ => by
          have := gain_le_of_le G hGp.1 hGp.2.1 hGp.2.2 d (d + {u}) (Multiset.le_add_right _ _) v
          unfold gain at this
          rw [add_right_comm]
          exact this
  have hpool := Walk.grp_ge_pool (e := succR) (p := landing) (L := digestAttemptLimit) landing_le_one hHp.1
    (stat parameter data m s) (exB excl m) d
  have hcomm : Walk.grp succR landing digestAttemptLimit (stat parameter data m s) (exB excl m) Hf d =
      virtualOnce Finset.univ wbar (grpM parameter data m s excl h) (n + 1) J d :=
    (rep_grpM (parameter := parameter) (data := data) m s excl).comm (rep_virtualOnce Finset.univ hw (n + 1) J) h d
  rw [← hcomm]
  refine le_trans ?_ hpool
  refine le_trans (add_le_add h1 le_rfl) (add_le_add le_rfl (mul_le_mul_right (Finset.sum_le_sum fun ρ _ => ?_) _))
  refine Walk.val_mono _ _ _ (fun x => ?_) le_rfl _ ρ
  unfold walkPay
  rcases stat parameter data m s x with _ | _ | v
  · simp [freshAvg]
  · exact le_rfl
  · simp only
    by_cases hx : excl (m, x)
    · rw [if_pos hx]; exact bot_le
    · rw [if_neg hx, if_neg (fun hb => hx (exB_iff.1 hb))]
      exact hgain v

end Sign5

end LeanSphincs.Security.ForsPotential
