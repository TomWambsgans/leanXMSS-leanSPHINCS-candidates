import LeanSphincs.BridgeContactB
import LeanSphincs.BridgeContact5

/-! **A4a.** A contact made at an unknown FORS secret whose leaf is revealed by the run. Contacts are
made at unexposed secrets, so a contact is revealed only by a later signature. One signing call
reveals a given leaf only through the pair it signs: a fresh landed view, which hits the leaf with
probability `2^-b 2^-10`, or a cached landed pair of the signed message; under the signer that
tries `R0, R0 + 1, ...` the cached pairs are selected with total probability at most the group of
the message on the card function, `grpM m s (fun _ => False) cardFn 0` (`BridgeContact5`). This file
proves that reveal bound and defines the event, its final value, and the counts of revealed and
unrevealed contacts and of cached landed pairs of messages not yet signed (`coinCount`: a count of
items only; their selection probabilities are not a common constant). -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] digestAttemptLimit

variable [Params]

/-! ### Hitting one leaf -/

/-- A kept view hits a FORS leaf position. -/
noncomputable def hitsAt (i : Index) (t : FtsTree) (l : FtsLeaf) (v : View) : ℝ≥0∞ :=
  if v.1 = localIdx i ∧ v.2 t = l then 1 else 0

/-- The probability that a uniform kept view hits a given leaf, `2^-b 2^-10`. -/
noncomputable def matchRate : ℝ≥0∞ := ((2 ^ subtreeHeight * 2 ^ 10 : ℕ) : ℝ≥0∞)⁻¹

theorem card_leafMatch (t : FtsTree) (l : FtsLeaf) :
    (Finset.univ.filter fun r : IndexGroup → FtsLeaf => r t = l).card = 2 ^ 230 := by
  set h : IndexGroup → FtsLeaf → ℕ := fun t' x => if t' = t then (if x = l then 1 else 0) else 1 with hh
  have hpt : ∀ r : IndexGroup → FtsLeaf, (if r t = l then 1 else 0) = ∏ t', h t' (r t') := by
    intro r
    rw [← Finset.mul_prod_erase Finset.univ (fun t' => h t' (r t')) (Finset.mem_univ t)]
    rw [Finset.prod_eq_one (fun t' ht' => by simp only [hh, if_neg (Finset.ne_of_mem_erase ht')])]
    simp [hh]
  rw [Finset.card_filter]
  simp only [hpt]
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  rw [← Finset.mul_prod_erase Finset.univ (fun t' => ∑ x, h t' x) (Finset.mem_univ t)]
  have h1 : ∑ x, h t x = 1 := by simp [hh]
  have h2 : ∀ t' ∈ Finset.univ.erase t, ∑ x, h t' x = 2 ^ 10 := by
    intro t' ht'
    simp only [hh, if_neg (Finset.ne_of_mem_erase ht'), Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
    exact H0.card_ftsLeaf
  rw [h1, one_mul, Finset.prod_congr rfl h2, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]
  simp only [Fintype.card_fin, ftsTrees]
  norm_num

theorem freshAvg_hitsAt (i : Index) (t : FtsTree) (l : FtsLeaf) :
    freshAvg Finset.univ (hitsAt i t l) = matchRate := by
  unfold freshAvg hitsAt
  have hsum : ∑ v ∈ (Finset.univ : Finset View), (if v.1 = localIdx i ∧ v.2 t = l then (1 : ℝ≥0∞) else 0) =
      ((2 ^ 230 : ℕ) : ℝ≥0∞) := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (localIdx i) (fun a _ ha => by simp [ha]) (fun h => absurd (Finset.mem_univ _) h)]
    simp only [true_and]
    rw [← card_leafMatch t l, Finset.card_filter]
    push_cast
    exact Finset.sum_congr rfl fun r _ => by split_ifs <;> simp
  rw [hsum, Finset.card_univ, H0.card_view]
  unfold matchRate
  have hsplit : ((2 ^ subtreeHeight * 2 ^ 240 : ℕ) : ℝ≥0∞) =
      ((2 ^ subtreeHeight * 2 ^ 10 : ℕ) : ℝ≥0∞) * ((2 ^ 230 : ℕ) : ℝ≥0∞) := by
    rw [← Nat.cast_mul, show (240 : ℕ) = 10 + 230 from rfl, pow_add, ← mul_assoc]
  rw [hsplit, ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inr (by positivity)), mul_assoc,
    ENNReal.inv_mul_cancel (by positivity) (ENNReal.natCast_ne_top _), mul_one]

/-! ### One signing call reveals a leaf rarely -/

section Reveal

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate) (parameter : PublicParameter) (data : PublicData)
  (m : Message)

/-- A completed signing call that reveals a leaf selected a pair hitting it, fresh or cached. -/
theorem reveal_point (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    {s : State} {P : List Pair} (hP : PInv parameter data s P) (hprep : Prepared initial s)
    (attempts budget : ℕ) (o1 : Run HashInput Coordinate (Option Signature) × State)
    (ho1 : o1 ∈ support (interp tg initial model (signCostSourceLoop parameter data m attempts) budget s))
    (r : Option Signature) (hr : o1.1.1 = some r) (i : Index) (t : FtsTree) (l : FtsLeaf)
    (hrev : Coordinate.ftsSecret i t l ∈ o1.1.2.1) :
    1 ≤ freshNewWeight parameter data m s (hitsAt i t l) o1 +
      outWeight parameter data m s (fun _ => 0) (fun _ v => hitsAt i t l v) o1 := by
  have hpost := loop_post tg initial model parameter data m (fun ρ call => hparse (m, ρ) call) Finset.univ
    (fun _ _ _ _ _ _ _ _ => Finset.mem_univ _) attempts budget s hprep o1 ho1 r hr
  rcases hpost with ⟨_, hnil, _⟩ | ⟨ρ, u0, u1, hsel, hfts, hsig, hfl⟩
  · rw [hnil] at hrev; cases hrev
  · obtain ⟨hi, hl⟩ := hfts _ hrev i t l rfl
    have hhit : hitsAt i t l (viewOf u0 u1) = 1 := by
      unfold hitsAt
      rw [if_pos ⟨by rw [hi]; rfl, by rw [hl]; rfl⟩]
    rcases hsel.2.2.2.1 with hs0 | hs0
    · have hs1 : s.cache (blk parameter data m ρ 1) = none := hP.first (m, ρ) hs0
      have h := freshNewWeight_ge hr hs1 hsel.1 hsel.2.1 hsel.2.2.1 (hitsAt i t l)
      rw [hhit] at h
      exact le_trans h le_self_add
    · rcases r with _ | sig
      · rw [(hfl rfl).1] at hrev; cases hrev
      · have hρ := hsig sig rfl
        refine le_trans (le_of_eq ?_) le_add_self
        unfold outWeight
        rw [hr]
        simp only
        rw [hρ, hsel.1, hsel.2.2.1]
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

/-- **One signing call** reveals a given leaf with probability at most `2^-b 2^-10` plus the
selection mass of the known landed randomizers of the signed message. -/
theorem reveal_le (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    {s : State} {P : List Pair} (hP : PInv parameter data s P) (hprep : Prepared initial s)
    (budget : ℕ) (i : Index) (t : FtsTree) (l : FtsLeaf) :
    ∑' o1, Pr[= o1 | interp tg initial model (signCostSourceLoop parameter data m digestAttemptLimit) budget s] *
        (if o1.1.1.isSome ∧ Coordinate.ftsSecret i t l ∈ o1.1.2.1 then 1 else 0) ≤
      matchRate + grpM parameter data m s (fun _ => False) cardFn 0 := by
  have hparse' : ∀ ρ call, model.parse (blk parameter data m ρ call) = none := fun ρ call => hparse (m, ρ) call
  have hnob1 : ∀ ρ, s.cache (blk parameter data m ρ 0) = none → s.cache (blk parameter data m ρ 1) = none :=
    fun ρ h => hP.first (m, ρ) h
  have hlandb1 : ∀ ρ u0, s.cache (blk parameter data m ρ 0) = some u0 → Landed parameter (blockIndex u0) →
      s.cache (blk parameter data m ρ 1) ≠ none := fun ρ u0 h0 hl => hP.second (m, ρ) ⟨u0, h0, hl⟩
  set gp : Randomness → View → ℝ≥0∞ := fun _ v => hitsAt i t l v with hgp
  have hgp1 : ∀ ρ v, gp ρ v ≤ 1 := by
    intro ρ v
    simp only [hgp, hitsAt]
    split_ifs <;> simp
  have hfresh := loop_bound_fresh tg initial model parameter data m hparse' s hnob1 hlandb1 (hitsAt i t l)
    digestAttemptLimit budget s (related_self parameter data m s)
  have hpool := le_trans (loop_bound tg initial model parameter data m hparse' s hnob1 hlandb1 (fun _ => 0) gp
    digestAttemptLimit attemptLimit_le budget) (pool_walk_le_grpM parameter data m s gp hgp1)
  calc _ ≤ ∑' o1, Pr[= o1 | interp tg initial model (signCostSourceLoop parameter data m digestAttemptLimit) budget s] *
        (freshNewWeight parameter data m s (hitsAt i t l) o1 + outWeight parameter data m s (fun _ => 0) gp o1) := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support (interp tg initial model (signCostSourceLoop parameter data m digestAttemptLimit) budget s)
        · refine mul_le_mul_right ?_ _
          split_ifs with hc
          · obtain ⟨hsome, hrev⟩ := hc
            obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hsome
            exact reveal_point tg initial model parameter data m hparse hP hprep digestAttemptLimit budget o1 ho1 r hr
              i t l hrev
          · exact bot_le
        · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
    _ = ∑' o1, Pr[= o1 | interp tg initial model (signCostSourceLoop parameter data m digestAttemptLimit) budget s] *
          freshNewWeight parameter data m s (hitsAt i t l) o1 +
        ∑' o1, Pr[= o1 | interp tg initial model (signCostSourceLoop parameter data m digestAttemptLimit) budget s] *
          outWeight parameter data m s (fun _ => 0) gp o1 := by
        simp only [mul_add, ENNReal.tsum_add]
    _ ≤ freshAvg Finset.univ (hitsAt i t l) + grpM parameter data m s (fun _ => False) cardFn 0 :=
        add_le_add hfresh hpool
    _ = _ := by rw [freshAvg_hitsAt]

end Reveal

/-! ### The event and its counts -/

section Defs

variable (parameter : PublicParameter) (K : HiddenReveal.Knowledge Coordinate) (wbar : ℝ≥0∞)

/-- **The spec's A4a**: a contact at a revealed leaf. -/
def A4a (s : State) (reveals : List Coordinate) : Prop :=
  ∃ index tree leaf, GRContact parameter K s index tree leaf ∧ Coordinate.ftsSecret index tree leaf ∈ reveals

/-- The final value of A4a: a finished game with a valid transcript. -/
noncomputable def finalA : FinalFn := fun o R s =>
  o.elim 0 fun outcome => if SigningTranscript.Valid outcome.2.1 ∧ A4a parameter K s R then 1 else 0

/-- Cached landed pairs of messages not yet signed (a count of items, not a bound on their
selection probabilities). -/
noncomputable def coinCount (P : List Pair) (L : QueryLog SigningSpec) : ℕ := (P.filter fun q => decide (MsgFresh L q)).length

/-- Revealed contacts. -/
noncomputable def revealedContacts (s : State) (R : List Coordinate) : Finset (Coordinate × Digest) :=
  (contacts parameter K s).filter fun g => g.1 ∈ R

/-- Unrevealed contacts. -/
noncomputable def openContacts (s : State) (R : List Coordinate) : Finset (Coordinate × Digest) :=
  (contacts parameter K s).filter fun g => g.1 ∉ R

end Defs

/-! ### Stores and coin counts -/

section Steps

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  (wbar : ℝ≥0∞) (Qtot : ℕ) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

omit [Params] in
theorem a4a_mono {s s' : State} (hext : Extends s s') {R : List Coordinate} (h : A4a parameter K s R) :
    A4a parameter K s' R := by
  obtain ⟨i, t, l, ⟨secret, ans, hc, hg, hK⟩, hR⟩ := h
  exact ⟨i, t, l, ⟨secret, ans, hext.1 _ _ hc, hext.2.2 _ hg, hK⟩, hR⟩

theorem finalA_store (o : Option HiddenBridge.Outcome) (R : List Coordinate) (s : State) (x : HashInput)
    (u : HashOutput) (hx : s.cache x = none) :
    finalA parameter K o R s ≤ finalA parameter K o R (s.store x u) := by
  unfold finalA
  cases o with
  | none => exact le_rfl
  | some outcome =>
      simp only [Option.elim]
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd ⟨h1.1, a4a_mono parameter K (extends_store s x u hx) h1.2⟩ h2
      · exact bot_le
      · exact le_rfl

theorem coinCount_addPair (P : List Pair) (L : QueryLog SigningSpec) (p : Pair) (u0 : HashOutput) :
    (coinCount (addPair parameter P p u0) L : ℝ≥0∞) =
      coinCount P L + if Landed parameter (blockIndex u0) then (if MsgFresh L p then 1 else 0) else 0 := by
  unfold coinCount addPair
  split_ifs with hl hf
  · rw [List.filter_cons_of_pos (by simpa using hf)]
    simp
  · rw [List.filter_cons_of_neg (by simpa using hf)]
    simp
  · simp

omit [Params] in
theorem coinCount_split (P : List Pair) (L : QueryLog SigningSpec) (m : Message) (hm : ∀ entry ∈ L, entry.1 ≠ m) :
    coinCount P L = (P.filter fun q => decide (MsgFresh L q ∧ q.1 ≠ m)).length +
      (P.filter fun q => decide (q.1 = m)).length := by
  unfold coinCount
  have h1 : (P.filter fun q => decide (MsgFresh L q)).filter (fun q => !decide (q.1 = m)) =
      P.filter fun q => decide (MsgFresh L q ∧ q.1 ≠ m) := by
    rw [List.filter_filter]
    congr 1
    funext q
    by_cases hq : q.1 = m <;> by_cases hf : MsgFresh L q <;> simp [hq, hf]
  have h2 : (P.filter fun q => decide (MsgFresh L q)).filter (fun q => decide (q.1 = m)) =
      P.filter fun q => decide (q.1 = m) := by
    rw [List.filter_filter]
    congr 1
    funext q
    by_cases hq : q.1 = m
    · have hf : MsgFresh L q := fun entry he => by rw [hq]; exact hm entry he
      simp [hq, hf]
    · simp [hq]
  have h := List.length_eq_length_filter_add (l := P.filter fun q => decide (MsgFresh L q))
    (fun q => decide (q.1 = m))
  rw [h2, h1] at h
  omega

theorem coinCount_after (P : List Pair) (L : QueryLog SigningSpec) (m : Message) (s s' : State)
    (r : Option Signature) :
    coinCount (newPairs parameter data m s s' ++ P) (L ++ [⟨m, r⟩]) =
      (P.filter fun q => decide (MsgFresh L q ∧ q.1 ≠ m)).length := by
  unfold coinCount
  rw [List.filter_append]
  have hnew : (newPairs parameter data m s s').filter (fun q => decide (MsgFresh (L ++ [⟨m, r⟩]) q)) = [] := by
    refine List.filter_eq_nil_iff.2 fun q hq => ?_
    obtain ⟨hm, _, _⟩ := (mem_newPairs parameter data m s).1 hq
    simp only [decide_eq_true_eq, msgFresh_append, not_and, not_not]
    exact fun _ => hm
  rw [hnew, List.nil_append]
  congr 1
  congr 1
  funext q
  simp only [msgFresh_append]

end Steps

/-! ### The event of a run -/

section Bound

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  (wbar : ℝ≥0∞) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- The event A4a of a finished run with a valid transcript. -/
def A4aRun (out : Run HashInput Coordinate HiddenBridge.Outcome × State) : Prop :=
  ∃ outcome, out.1.1 = some outcome ∧ SigningTranscript.Valid outcome.2.1 ∧ A4a parameter K out.2 out.1.2.1

end Bound

end LeanSphincs.Security.ForsPotential
