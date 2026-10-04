import LeanSphincs.BridgeSignerPost
import LeanSphincs.BridgeVirtual
import LeanSphincs.BridgeImplication

/-! The FORS potential of the lazy run. Every cached landed message-randomizer pair is an item;
the unsigned ones are candidates whose value is the virtual-future forecast of their witness
count; the remaining budget may create future pairs, each paying the excess forecast of a new
pair. A new pair touched by a query is paid by the saturation baseline plus one excess. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-- A message and a randomizer. -/
abbrev Pair := Message × Randomness

abbrev State := DebtState HashInput HashOutput Coordinate

instance : Inhabited View := ⟨(⟨0, Nat.two_pow_pos _⟩, fun _ => ⟨0, Nat.two_pow_pos _⟩)⟩

theorem payload_pair_injective (root : Digest) {m m' : Message} {ρ ρ' : Randomness}
    (h : messageDigestPayload root m ρ = messageDigestPayload root m' ρ') : m = m' ∧ ρ = ρ' := by
  have hparts := List.append_inj h (by simp [messageDigestPayload, bytesLE_length])
  have hfirst := List.append_inj hparts.1 (by simp [bytesLE_length])
  exact ⟨bytesLE_injective hparts.2, bytesLE_injective hfirst.1⟩

section Defs

variable (parameter : PublicParameter) (data : PublicData)

/-- Block `call` of a pair. -/
abbrev pblk (p : Pair) (call : Fin 2) : HashInput := blk parameter data p.1 p.2 call

theorem pblk_injective {p q : Pair} {call call' : Fin 2}
    (h : pblk parameter data p call = pblk parameter data q call') : p = q ∧ call = call' := by
  obtain ⟨hfields, -, hpayload⟩ := tweakableInput_injective h
  obtain ⟨hm, hρ⟩ := payload_pair_injective data.root hpayload
  refine ⟨Prod.ext hm hρ, ?_⟩
  have := congrArg TweakFields.position hfields
  simp only [hashDomainFields, tweakFields] at this
  exact Fin.ext (by
    have h1 := call.isLt
    have h2 := call'.isLt
    have := congrArg BitVec.toNat this
    simp at this
    omega)

theorem pblk_ne_of_ne {p q : Pair} (h : p ≠ q) (call call' : Fin 2) :
    pblk parameter data p call ≠ pblk parameter data q call' := fun heq =>
  h (pblk_injective parameter data heq).1

theorem pblk_ne_call (p : Pair) : pblk parameter data p 0 ≠ pblk parameter data p 1 := fun heq =>
  absurd (pblk_injective parameter data heq).2 (by decide)

/-- The kept view of a pair whose two blocks are cached. -/
noncomputable def pview (s : State) (p : Pair) : View :=
  (s.cache (pblk parameter data p 0)).elim default fun u0 =>
    (s.cache (pblk parameter data p 1)).elim default fun u1 => viewOf u0 u1

/-- Block 0 of the pair is cached and lands. -/
def LandedIn (s : State) (p : Pair) : Prop :=
  ∃ u0, s.cache (pblk parameter data p 0) = some u0 ∧ Landed parameter (blockIndex u0)

/-- The items are exactly the landed pairs; landed pairs have both blocks; no pair has only
its second block. -/
structure PInv (s : State) (P : List Pair) : Prop where
  nodup : P.Nodup
  mem : ∀ p, p ∈ P ↔ LandedIn parameter data s p
  second : ∀ p, LandedIn parameter data s p → s.cache (pblk parameter data p 1) ≠ none
  first : ∀ p, s.cache (pblk parameter data p 0) = none → s.cache (pblk parameter data p 1) = none

/-- The local index of a leaf index. -/
def localIdx (i : Index) : Fin (2 ^ subtreeHeight) := ⟨i.val % 2 ^ subtreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

theorem localDigestView_fst (digest : MessageDigest) :
    (Lifetime.localDigestView digest).1 = localIdx (digestIndex digest) := rfl

theorem localDigestView_snd (digest : MessageDigest) :
    (Lifetime.localDigestView digest).2 = digestLeaves digest := rfl

/-- The disclosed views account for every revealed FORS secret. -/
def DInv (R : List Coordinate) (d : Multiset View) : Prop :=
  ∀ i t l, Coordinate.ftsSecret i t l ∈ R → ∃ v ∈ d, v.1 = localIdx i ∧ v.2 t = l

/-- The pair was never signed in the log. -/
def Unsigned (L : QueryLog SigningSpec) (p : Pair) : Prop :=
  ∀ entry ∈ L, ∀ sig, entry.2 = some sig → ¬(entry.1 = p.1 ∧ sig.randomness = p.2)

variable (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- The excess of the price over the baseline. -/
noncomputable def excess (D : Multiset View) : ℝ≥0∞ := price D - b0

/-- Share of kept views at failing indices. -/
noncomputable def failMass : ℝ≥0∞ :=
  freshAvg Finset.univ fun v : View => if v.1 ∈ Fail then 1 else 0

/-- Witness count of a target as a value. -/
noncomputable def witnessFn (v : View) (D : Multiset View) : ℝ≥0∞ := (witness v D : ℝ≥0∞)

/-- Views of a list of pairs. -/
noncomputable def items (s : State) (P : List Pair) : List View := P.map (pview parameter data s)

/-- The forecast of a candidate. -/
noncomputable def candValue (s : State) (P : List Pair) (d : Multiset View) (n k : ℕ) (p : Pair) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtual Finset.univ wbar (witnessFn (pview parameter data s p)) n I d) k
    (items parameter data s (P.erase p))

/-- The excess forecast of a new pair. -/
noncomputable def hValue (s : State) (P : List Pair) (d : Multiset View) (n k : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtual Finset.univ wbar (excess b0) n I d) k (items parameter data s P)

/-- The value of a candidate: one at a failing index, its forecast otherwise; zero once signed. -/
noncomputable def cand (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (p : Pair) : ℝ≥0∞ :=
  if Unsigned L p then (if (pview parameter data s p).1 ∈ Fail then 1 else candValue parameter data wbar s P d n k p)
  else 0

/-- The potential without the hit and transcript tests. -/
noncomputable def core (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    ℝ≥0∞ :=
  (P.map (cand parameter data wbar Fail s P L d n k)).sum +
    k * (hValue parameter data wbar b0 s P d n k + failMass Fail) + n * failMass Fail

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)

/-- **The potential.** -/
noncomputable def pot (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ) : ℝ≥0∞ :=
  if Realized tg initial s ∨ signatureLimit < L.length then 0
  else core parameter data wbar b0 Fail s P L d (signatureLimit - L.length) k

end Defs

/-! ### The law of a fresh pair -/

section Mean

theorem landing_le_one : landing ≤ 1 := by
  unfold landing
  exact ENNReal.inv_le_one.2 (by exact_mod_cast Nat.one_le_two_pow)

theorem unlanded_mass (parameter : PublicParameter) :
    ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Landed parameter (blockIndex u0) then (0 : ℝ≥0∞) else 1) = 1 - landing := by
  have htot : (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Landed parameter (blockIndex u0) then (1 : ℝ≥0∞) else 0)) +
    ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Landed parameter (blockIndex u0) then (0 : ℝ≥0∞) else 1) = 1 := by
    rw [← ENNReal.tsum_add]
    calc _ = ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] := by
          refine tsum_congr fun u0 => ?_
          split_ifs <;> simp
      _ = 1 := tsum_probOutput_eq_one' probFailure_eq_zero
  rw [landed_mass parameter] at htot
  exact ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top (by rw [add_comm]; exact htot)

/-- **Mean over a fresh pair.** -/
theorem pair_mean (parameter : PublicParameter) (F : View → ℝ≥0∞) (C : ℝ≥0∞) :
    ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
      ∑' u1, Pr[= u1 | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if Landed parameter (blockIndex u0) then F (viewOf u0 u1) else C) =
      landing * freshAvg Finset.univ F + (1 - landing) * C := by
  have hsplit : ∀ u0, ∑' u1, Pr[= u1 | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Landed parameter (blockIndex u0) then F (viewOf u0 u1) else C) =
      (∑' u1, Pr[= u1 | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if Landed parameter (blockIndex u0) then F (Lifetime.localDigestView (truncateMessageDigest u0 u1)) else 0)) +
      C * (if Landed parameter (blockIndex u0) then 0 else 1) := by
    intro u0
    split_ifs
    · simp [viewOf]
    · simp only [mul_zero, tsum_zero, zero_add, mul_one]
      rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' probFailure_eq_zero, one_mul]
  simp only [hsplit, mul_add, ENNReal.tsum_add]
  rw [fresh_view_mean parameter F]
  congr 1
  simp only [mul_left_comm _ C, ENNReal.tsum_mul_left]
  rw [unlanded_mass parameter, mul_comm]

/-- Expectations distribute over a list sum. -/
theorem tsum_list_sum {β γ : Type} (w : β → ℝ≥0∞) (l : List γ) (f : β → γ → ℝ≥0∞) :
    ∑' x, w x * (l.map (f x)).sum = (l.map fun c => ∑' x, w x * f x c).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, mul_add, ENNReal.tsum_add, ih]

end Mean

/-! ### Expectation over the two blocks of a fresh pair -/

section PairE

/-- Expectation over two fresh blocks. -/
noncomputable def pairE (F : HashOutput → HashOutput → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
    ∑' u1, Pr[= u1 | ($ᵗ HashOutput : ProbComp HashOutput)] * F u0 u1

omit [Params] in
theorem pairE_add (F G : HashOutput → HashOutput → ℝ≥0∞) :
    pairE (fun a b => F a b + G a b) = pairE F + pairE G := by
  simp only [pairE, mul_add, ENNReal.tsum_add]

omit [Params] in
theorem pairE_mono {F G : HashOutput → HashOutput → ℝ≥0∞} (h : ∀ a b, F a b ≤ G a b) : pairE F ≤ pairE G :=
  ENNReal.tsum_le_tsum fun a => mul_le_mul_right (ENNReal.tsum_le_tsum fun b => mul_le_mul_right (h a b) _) _

omit [Params] in
theorem pairE_const (c : ℝ≥0∞) : pairE (fun _ _ => c) = c := by
  simp only [pairE, ENNReal.tsum_mul_right, tsum_probOutput_eq_one' probFailure_eq_zero, one_mul]

omit [Params] in
theorem pairE_const_mul (c : ℝ≥0∞) (F : HashOutput → HashOutput → ℝ≥0∞) :
    pairE (fun a b => c * F a b) = c * pairE F := by
  simp only [pairE, mul_left_comm _ c, ENNReal.tsum_mul_left]

omit [Params] in
theorem pairE_list_sum {γ : Type} (l : List γ) (F : HashOutput → HashOutput → γ → ℝ≥0∞) :
    pairE (fun a b => (l.map (F a b)).sum) = (l.map fun c => pairE fun a b => F a b c).sum := by
  induction l with
  | nil => simpa using pairE_const 0
  | cons c l ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [pairE_add, ih]

theorem pairE_landed (parameter : PublicParameter) (F : View → ℝ≥0∞) (C : ℝ≥0∞) :
    pairE (fun u0 u1 => if Landed parameter (blockIndex u0) then F (viewOf u0 u1) else C) =
      landing * freshAvg Finset.univ F + (1 - landing) * C :=
  pair_mean parameter F C

end PairE

/-! ### A new pair -/

section NewPair

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- Both blocks of a new pair stored. -/
noncomputable def withPair (s : State) (p : Pair) (u0 u1 : HashOutput) : State :=
  (s.store (pblk parameter data p 0) u0).store (pblk parameter data p 1) u1

/-- The items after a new pair. -/
noncomputable def addPair (P : List Pair) (p : Pair) (u0 : HashOutput) : List Pair :=
  if Landed parameter (blockIndex u0) then p :: P else P

variable {parameter data}

theorem withPair_other (s : State) (p : Pair) (u0 u1 : HashOutput) (x : HashInput)
    (h0 : x ≠ pblk parameter data p 0) (h1 : x ≠ pblk parameter data p 1) :
    (withPair parameter data s p u0 u1).cache x = s.cache x := by
  unfold withPair
  rw [store_cache_ne _ _ _ h1, store_cache_ne _ _ _ h0]

theorem withPair_zero (s : State) (p : Pair) (u0 u1 : HashOutput) :
    (withPair parameter data s p u0 u1).cache (pblk parameter data p 0) = some u0 := by
  unfold withPair
  rw [store_cache_ne _ _ _ (pblk_ne_call parameter data p)]
  simp [DebtState.store]

theorem withPair_one (s : State) (p : Pair) (u0 u1 : HashOutput) :
    (withPair parameter data s p u0 u1).cache (pblk parameter data p 1) = some u1 := by
  unfold withPair
  simp [DebtState.store]

theorem withPair_other_pair (s : State) (p q : Pair) (hq : q ≠ p) (u0 u1 : HashOutput) (call : Fin 2) :
    (withPair parameter data s p u0 u1).cache (pblk parameter data q call) = s.cache (pblk parameter data q call) :=
  withPair_other s p u0 u1 _ (pblk_ne_of_ne parameter data hq _ _) (pblk_ne_of_ne parameter data hq _ _)

theorem pview_withPair_self (s : State) (p : Pair) (u0 u1 : HashOutput) :
    pview parameter data (withPair parameter data s p u0 u1) p = viewOf u0 u1 := by
  simp only [pview, withPair_zero, withPair_one, Option.elim]

theorem pview_withPair_other (s : State) (p q : Pair) (hq : q ≠ p) (u0 u1 : HashOutput) :
    pview parameter data (withPair parameter data s p u0 u1) q = pview parameter data s q := by
  simp only [pview, withPair_other_pair s p q hq]

theorem items_withPair (s : State) (p : Pair) (u0 u1 : HashOutput) (l : List Pair) (hl : p ∉ l) :
    items parameter data (withPair parameter data s p u0 u1) l = items parameter data s l := by
  unfold items
  refine List.map_congr_left fun q hq => ?_
  exact pview_withPair_other s p q (fun h => hl (h ▸ hq)) u0 u1

theorem not_mem_of_fresh {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) : p ∉ P := by
  intro hp
  obtain ⟨u, hu, _⟩ := (hP.mem p).1 hp
  rw [hp0] at hu
  cases hu

theorem pinv_withPair {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) (u0 u1 : HashOutput) :
    PInv parameter data (withPair parameter data s p u0 u1) (addPair parameter P p u0) := by
  have hpP := not_mem_of_fresh hP hp0
  have hland : ∀ q, q ≠ p → (LandedIn parameter data (withPair parameter data s p u0 u1) q ↔
      LandedIn parameter data s q) := by
    intro q hq
    simp only [LandedIn, withPair_other_pair s p q hq]
  refine ⟨?_, fun q => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · unfold addPair
    split_ifs
    · exact List.nodup_cons.2 ⟨hpP, hP.nodup⟩
    · exact hP.nodup
  · by_cases hqp : q = p
    · subst hqp
      unfold addPair
      constructor
      · intro hmem
        split_ifs at hmem with hl
        · exact ⟨u0, withPair_zero s q u0 u1, hl⟩
        · exact absurd hmem hpP
      · rintro ⟨u, hu, hl⟩
        rw [withPair_zero] at hu
        cases hu
        rw [if_pos hl]
        exact List.mem_cons_self ..
    · rw [hland q hqp, ← hP.mem q]
      unfold addPair
      split_ifs
      · simp [hqp]
      · rfl
  · by_cases hqp : q = p
    · subst hqp
      rw [withPair_one]
      simp
    · rw [withPair_other_pair s p q hqp]
      exact hP.second q ((hland q hqp).1 hq)
  · by_cases hqp : q = p
    · subst hqp
      rw [withPair_zero] at hq
      cases hq
    · rw [withPair_other_pair s p q hqp] at hq ⊢
      exact hP.first q hq

end NewPair

/-! ### The new-pair inequality -/

section NewPairCore

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

theorem excess_props (hb0 : b0 ≠ ⊤) :
    Monotone' (excess b0) ∧ Supermodular (excess b0) ∧ ∀ D, excess b0 D ≠ ⊤ :=
  ⟨excess_mono price_mono b0, excess_super price_mono price_super price_ne_top b0 hb0,
    fun D => ne_top_of_le_ne_top (price_ne_top D) tsub_le_self⟩

theorem witness_props (v : View) :
    Monotone' (witnessFn v) ∧ Supermodular (witnessFn v) ∧ ∀ D, witnessFn v D ≠ ⊤ :=
  ⟨witness_mono v, witness_super v, fun _ => ENNReal.natCast_ne_top _⟩

theorem virtual_cons_le (hw : wbar ≤ 1) {f : Multiset View → ℝ≥0∞}
    (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤) (n : ℕ) (d : Multiset View) :
    ∀ v I, virtual Finset.univ wbar f n I d ≤ virtual Finset.univ wbar f n (v :: I) d :=
  fun v I => virtual_le_cons Finset.univ_nonempty hw hf.1 hf.2.1 hf.2.2 n I v d

theorem virtual_perm' {f : Multiset View → ℝ≥0∞} (n : ℕ) (d : Multiset View) :
    ∀ I I' : List View, I.Perm I' → virtual Finset.univ wbar f n I d = virtual Finset.univ wbar f n I' d :=
  fun _ _ h => virtual_perm n h d

/-- A new candidate's forecast is at most the baseline plus one excess. -/
theorem fresh_forecast (hw : wbar ≤ 1) (I : List View) (d : Multiset View) (n k : ℕ) :
    landing * freshAvg Finset.univ (fun v => creations Finset.univ landing
      (fun J => virtual Finset.univ wbar (witnessFn v) n J d) k I) ≤
    b0 + creations Finset.univ landing (fun J => virtual Finset.univ wbar (excess b0) n J d) k I := by
  have hU : (Finset.univ : Finset View).Nonempty := Finset.univ_nonempty
  rw [← creations_freshAvg, ← creations_const_mul]
  have hpt : ∀ J, landing * freshAvg Finset.univ (fun v => virtual Finset.univ wbar (witnessFn v) n J d) ≤
      b0 + virtual Finset.univ wbar (excess b0) n J d := by
    intro J
    rw [← virtual_freshAvg hU, ← virtual_const_mul]
    calc virtual Finset.univ wbar (fun D => landing * freshAvg Finset.univ fun v => witnessFn v D) n J d
        ≤ virtual Finset.univ wbar (fun D => b0 + excess b0 D) n J d :=
          virtual_mono_base (fun D => show price D ≤ b0 + (price D - b0) from le_add_tsub) n J d
      _ = b0 + virtual Finset.univ wbar (excess b0) n J d := by
          rw [virtual_add hU (fun _ => b0) (excess b0), virtual_const hU hw]
  calc creations Finset.univ landing (fun J => landing * freshAvg Finset.univ fun v =>
        virtual Finset.univ wbar (witnessFn v) n J d) k I
      ≤ creations Finset.univ landing (fun J => b0 + virtual Finset.univ wbar (excess b0) n J d) k I :=
        creations_mono hpt k I
    _ = _ := by rw [creations_add (fun _ => b0), creations_const Finset.univ_nonempty landing_le_one]

variable {parameter data}

/-- Old candidates after a new pair. -/
theorem cand_withPair {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (q : Pair) (hq : q ∈ P) (u0 u1 : HashOutput) :
    cand parameter data wbar Fail (withPair parameter data s p u0 u1) (addPair parameter P p u0) L d n k q =
      if Landed parameter (blockIndex u0) then
        (if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
          creations Finset.univ landing (fun J => virtual Finset.univ wbar (witnessFn (pview parameter data s q)) n J d) k
            (viewOf u0 u1 :: items parameter data s (P.erase q))) else 0)
      else cand parameter data wbar Fail s P L d n k q := by
  have hpP := not_mem_of_fresh hP hp0
  have hqp : q ≠ p := fun h => hpP (h ▸ hq)
  have hpe : p ∉ P.erase q := fun h => hpP (List.mem_of_mem_erase h)
  have hv := pview_withPair_other (parameter := parameter) (data := data) s p q hqp u0 u1
  by_cases hl : Landed parameter (blockIndex u0)
  · rw [if_pos hl]
    unfold cand candValue addPair
    rw [if_pos hl, hv]
    have herase : (p :: P).erase q = p :: P.erase q := List.erase_cons_tail (by simpa using hqp.symm)
    have hitems : items parameter data (withPair parameter data s p u0 u1) ((p :: P).erase q) =
        viewOf u0 u1 :: items parameter data s (P.erase q) := by
      rw [herase]
      show (p :: P.erase q).map (pview parameter data (withPair parameter data s p u0 u1)) = _
      rw [List.map_cons, pview_withPair_self]
      exact congrArg _ (items_withPair s p u0 u1 _ hpe)
    rw [hitems]
  · rw [if_neg hl]
    unfold cand candValue addPair
    rw [if_neg hl, hv, items_withPair s p u0 u1 _ hpe]

/-- The new candidate itself. -/
theorem cand_withPair_self {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ)
    (u0 u1 : HashOutput) :
    cand parameter data wbar Fail (withPair parameter data s p u0 u1) (p :: P) L d n k p ≤
      (if (viewOf u0 u1).1 ∈ Fail then 1 else 0) +
        creations Finset.univ landing (fun J => virtual Finset.univ wbar (witnessFn (viewOf u0 u1)) n J d) k
          (items parameter data s P) := by
  have hpP := not_mem_of_fresh hP hp0
  unfold cand candValue
  rw [pview_withPair_self, List.erase_cons_head, items_withPair s p u0 u1 _ hpP]
  split_ifs <;> simp

theorem hValue_withPair {s : State} {P : List Pair} (hP : PInv parameter data s P) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) (d : Multiset View) (n k : ℕ) (u0 u1 : HashOutput) :
    hValue parameter data wbar b0 (withPair parameter data s p u0 u1) (addPair parameter P p u0) d n k =
      if Landed parameter (blockIndex u0) then
        creations Finset.univ landing (fun J => virtual Finset.univ wbar (excess b0) n J d) k
          (viewOf u0 u1 :: items parameter data s P)
      else hValue parameter data wbar b0 s P d n k := by
  have hpP := not_mem_of_fresh hP hp0
  unfold hValue addPair
  split_ifs
  · show creations _ _ _ k ((p :: P).map (pview parameter data (withPair parameter data s p u0 u1))) = _
    rw [List.map_cons, pview_withPair_self]
    exact congrArg _ (congrArg _ (items_withPair s p u0 u1 _ hpP))
  · rw [items_withPair s p u0 u1 _ hpP]

/-- **A new pair.** Touching a new pair costs one future pair and at most the baseline. -/
theorem core_newPair (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) {s : State} {P : List Pair}
    (hP : PInv parameter data s P) {p : Pair} (hp0 : s.cache (pblk parameter data p 0) = none)
    (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    pairE (fun u0 u1 => core parameter data wbar b0 Fail (withPair parameter data s p u0 u1)
      (addPair parameter P p u0) L d n k) ≤ core parameter data wbar b0 Fail s P L d n (k + 1) + b0 := by
  set I := items parameter data s P with hI
  set W : View → ℝ≥0∞ := fun v =>
    creations Finset.univ landing (fun J => virtual Finset.univ wbar (witnessFn v) n J d) k I with hW
  set GH : List View → ℝ≥0∞ := fun J => virtual Finset.univ wbar (excess b0) n J d with hGH
  set φ := failMass Fail with hφ
  set A : Pair → View → ℝ≥0∞ := fun q v => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
    creations Finset.univ landing (fun J => virtual Finset.univ wbar (witnessFn (pview parameter data s q)) n J d) k
      (v :: items parameter data s (P.erase q))) else 0 with hA
  -- pointwise upper bound
  have hpoint : ∀ u0 u1, core parameter data wbar b0 Fail (withPair parameter data s p u0 u1)
      (addPair parameter P p u0) L d n k ≤
      ((if Landed parameter (blockIndex u0) then
          (if (viewOf u0 u1).1 ∈ Fail then 1 else 0) + W (viewOf u0 u1) else 0) +
        (P.map fun q => if Landed parameter (blockIndex u0) then A q (viewOf u0 u1)
          else cand parameter data wbar Fail s P L d n k q).sum) +
      k * ((if Landed parameter (blockIndex u0) then creations Finset.univ landing GH k (viewOf u0 u1 :: I)
          else hValue parameter data wbar b0 s P d n k) + φ) + n * φ := by
    intro u0 u1
    unfold core
    rw [hValue_withPair wbar b0 hP hp0 d n k u0 u1]
    have hlist : ((addPair parameter P p u0).map (cand parameter data wbar Fail (withPair parameter data s p u0 u1)
        (addPair parameter P p u0) L d n k)).sum =
        (if Landed parameter (blockIndex u0) then
          cand parameter data wbar Fail (withPair parameter data s p u0 u1) (p :: P) L d n k p else 0) +
        (P.map fun q => if Landed parameter (blockIndex u0) then A q (viewOf u0 u1)
          else cand parameter data wbar Fail s P L d n k q).sum := by
      by_cases hl : Landed parameter (blockIndex u0)
      · have hmap : P.map (cand parameter data wbar Fail (withPair parameter data s p u0 u1) (p :: P) L d n k) =
            P.map fun q => A q (viewOf u0 u1) := List.map_congr_left fun q hq => by
          have h := cand_withPair wbar Fail hP hp0 L d n k q hq u0 u1
          unfold addPair at h
          simp only [if_pos hl] at h
          exact h
        unfold addPair
        simp only [if_pos hl, List.map_cons, List.sum_cons, hmap]
      · have hmap : P.map (cand parameter data wbar Fail (withPair parameter data s p u0 u1) P L d n k) =
            P.map fun q => cand parameter data wbar Fail s P L d n k q := List.map_congr_left fun q hq => by
          have h := cand_withPair wbar Fail hP hp0 L d n k q hq u0 u1
          unfold addPair at h
          simp only [if_neg hl] at h
          exact h
        unfold addPair
        simp only [if_neg hl, zero_add, hmap]
    rw [hlist]
    gcongr
    by_cases hl : Landed parameter (blockIndex u0)
    · simp only [if_pos hl]
      exact cand_withPair_self wbar Fail hP hp0 L d n k u0 u1
    · simp only [if_neg hl, le_refl]
  refine le_trans (pairE_mono hpoint) ?_
  -- expectations
  simp only [pairE_add, pairE_const_mul, pairE_const, pairE_list_sum]
  have h1 : pairE (fun u0 u1 => if Landed parameter (blockIndex u0) then
      (if (viewOf u0 u1).1 ∈ Fail then 1 else 0) + W (viewOf u0 u1) else 0) = landing * (φ + freshAvg Finset.univ W) := by
    rw [pairE_landed parameter (fun v => (if v.1 ∈ Fail then 1 else 0) + W v) 0, mul_zero, add_zero, freshAvg_add]
    rfl
  have h2 : ∀ q, pairE (fun u0 u1 => if Landed parameter (blockIndex u0) then A q (viewOf u0 u1)
      else cand parameter data wbar Fail s P L d n k q) = cand parameter data wbar Fail s P L d n (k + 1) q := by
    intro q
    rw [pairE_landed parameter (A q)]
    simp only [hA]
    unfold cand candValue
    split_ifs
    · rw [freshAvg_const _ Finset.univ_nonempty, mul_one, mul_one, add_tsub_cancel_of_le landing_le_one]
    · simp only [creations]
      ring
    · simp [freshAvg]
  have h3 : pairE (fun u0 u1 => if Landed parameter (blockIndex u0) then
      creations Finset.univ landing GH k (viewOf u0 u1 :: I) else hValue parameter data wbar b0 s P d n k) =
      hValue parameter data wbar b0 s P d n (k + 1) := by
    rw [pairE_landed parameter (fun v => creations Finset.univ landing GH k (v :: I))]
    unfold hValue
    simp only [creations]
    ring
  rw [h1, h3, List.map_congr_left fun q _ => h2 q]
  -- the new candidate is paid by the baseline and one excess
  have hfresh : landing * freshAvg Finset.univ W ≤ b0 + hValue parameter data wbar b0 s P d n (k + 1) := by
    refine le_trans (fresh_forecast wbar b0 hw I d n k) (add_le_add le_rfl ?_)
    unfold hValue
    exact creations_le_succ Finset.univ_nonempty landing_le_one
      (virtual_cons_le wbar hw (excess_props b0 hb0) n d) (virtual_perm' wbar n d) k I
  have hφ1 : landing * φ ≤ φ := mul_le_of_le_one_left' landing_le_one
  unfold core
  set S := (P.map (cand parameter data wbar Fail s P L d n (k + 1))).sum
  set H := hValue parameter data wbar b0 s P d n (k + 1)
  calc landing * (φ + freshAvg Finset.univ W) + S + k * (H + φ) + n * φ
      ≤ φ + (b0 + H) + S + k * (H + φ) + n * φ := by
        rw [mul_add]
        gcongr
    _ = S + ((k : ℝ≥0∞) + 1) * (H + φ) + n * φ + b0 := by ring
    _ = _ := by push_cast; ring

end NewPairCore

/-! ### Order and congruence of the potential -/

section Order

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

variable {parameter data}

theorem items_congr {s s' : State} {l : List Pair} (h : ∀ q ∈ l, pview parameter data s' q = pview parameter data s q) :
    items parameter data s' l = items parameter data s l :=
  List.map_congr_left h

/-- The potential sees the state only through the views of its items. -/
theorem core_congr {s s' : State} {P : List Pair} (h : ∀ q ∈ P, pview parameter data s' q = pview parameter data s q)
    (L : QueryLog SigningSpec) (d : Multiset View) (n k : ℕ) :
    core parameter data wbar b0 Fail s' P L d n k = core parameter data wbar b0 Fail s P L d n k := by
  have hcand : ∀ q ∈ P, cand parameter data wbar Fail s' P L d n k q = cand parameter data wbar Fail s P L d n k q := by
    intro q hq
    unfold cand candValue
    rw [h q hq, items_congr fun r hr => h r (List.mem_of_mem_erase hr)]
  unfold core hValue
  rw [List.map_congr_left hcand, items_congr h]

theorem candValue_mono (hw : wbar ≤ 1) (s : State) (P : List Pair) (d : Multiset View) (n : ℕ) {k k' : ℕ}
    (hk : k ≤ k') (p : Pair) :
    candValue parameter data wbar s P d n k p ≤ candValue parameter data wbar s P d n k' p :=
  creations_mono_count Finset.univ_nonempty landing_le_one
    (virtual_cons_le wbar hw (witness_props _) n d) (virtual_perm' wbar n d) hk _

theorem hValue_mono (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (s : State) (P : List Pair) (d : Multiset View) (n : ℕ)
    {k k' : ℕ} (hk : k ≤ k') :
    hValue parameter data wbar b0 s P d n k ≤ hValue parameter data wbar b0 s P d n k' :=
  creations_mono_count Finset.univ_nonempty landing_le_one
    (virtual_cons_le wbar hw (excess_props b0 hb0) n d) (virtual_perm' wbar n d) hk _

theorem core_mono (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (s : State) (P : List Pair) (L : QueryLog SigningSpec)
    (d : Multiset View) (n : ℕ) {k k' : ℕ} (hk : k ≤ k') :
    core parameter data wbar b0 Fail s P L d n k ≤ core parameter data wbar b0 Fail s P L d n k' := by
  unfold core
  refine add_le_add (add_le_add (List.sum_le_sum fun q _ => ?_) ?_) le_rfl
  · unfold cand
    split_ifs
    · exact le_rfl
    · exact candValue_mono wbar hw s P d n hk q
    · exact le_rfl
  · exact mul_le_mul' (by exact_mod_cast hk) (add_le_add (hValue_mono wbar b0 hw hb0 s P d n hk) le_rfl)

theorem pot_le_core (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
    (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ) :
    pot parameter data wbar b0 Fail tg initial s P L d k ≤
      core parameter data wbar b0 Fail s P L d (signatureLimit - L.length) k := by
  unfold pot
  split_ifs
  · exact bot_le
  · exact le_rfl

end Order

/-! ### Paid programs -/

section Good

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- The final value: a FORS cover with no decided hit. -/
noncomputable def finalValue (R : List Coordinate) (out : Run HashInput Coordinate HiddenBridge.Outcome × State) :
    ℝ≥0∞ :=
  out.1.1.elim 0 fun outcome =>
    if HiddenBridge.ForsCover parameter data.root outcome (R ++ out.1.2.1) out.2.cache ∧ ¬Realized tg initial out.2
    then 1 else 0

/-- A program whose final value is paid by the potential and the baseline payments. -/
def Good (L : QueryLog SigningSpec) (prog : OracleComp CostSpec HiddenBridge.Outcome) : Prop :=
  ∀ budget (s : State) (P : List Pair) (d : Multiset View) (R : List Coordinate),
    Prepared initial s → PInv parameter data s P → DInv R d →
      ∑' out, Pr[= out | interp tg initial model prog budget s] * finalValue parameter data tg initial R out ≤
        pot parameter data wbar b0 Fail tg initial s P L d budget + b0 * expectedFlagged tg initial model prog budget s

theorem pot_mono (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (s : State) (P : List Pair) (L : QueryLog SigningSpec)
    (d : Multiset View) {k k' : ℕ} (hk : k ≤ k') :
    pot parameter data wbar b0 Fail tg initial s P L d k ≤ pot parameter data wbar b0 Fail tg initial s P L d k' := by
  unfold pot
  split_ifs
  · exact le_rfl
  · exact core_mono wbar b0 Fail hw hb0 s P L d _ hk

/-- A grown state with the same item views has no larger potential. -/
theorem pot_grow (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) {s s' : State} (hext : Extends s s') {P : List Pair}
    (hview : ∀ q ∈ P, pview parameter data s' q = pview parameter data s q) (L : QueryLog SigningSpec)
    (d : Multiset View) {k k' : ℕ} (hk : k ≤ k') :
    pot parameter data wbar b0 Fail tg initial s' P L d k ≤ pot parameter data wbar b0 Fail tg initial s P L d k' := by
  unfold pot
  by_cases hr : Realized tg initial s' ∨ signatureLimit < L.length
  · rw [if_pos hr]; exact bot_le
  · have hr' : ¬(Realized tg initial s ∨ signatureLimit < L.length) := fun h =>
      hr (h.imp (realized_of_extends tg initial hext) id)
    rw [if_neg hr, if_neg hr', core_congr wbar b0 Fail hview]
    exact core_mono wbar b0 Fail hw hb0 s P L d _ hk

/-! #### Draws -/

theorem good_draw (L : QueryLog SigningSpec) (draw : ℕ)
    (next : Fin (draw + 1) → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, Good parameter data wbar b0 Fail tg initial model L (next v)) :
    Good parameter data wbar b0 Fail tg initial model L
      (liftM (CostSpec.query (.inl (.inl draw))) >>= next) := by
  intro budget s P d R hprep hP hD
  unfold expectedFlagged
  rw [interp_draw, tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
  calc _ ≤ ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
        (pot parameter data wbar b0 Fail tg initial s P L d budget +
          b0 * expectedFlagged tg initial model (next v) budget s) :=
        ENNReal.tsum_le_tsum fun v => mul_le_mul_right (h v budget s P d R hprep hP hD) _
    _ ≤ _ := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
        refine add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) (le_of_eq ?_)
        unfold expectedFlagged
        simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

end Good

/-! ### One ordinary query -/

section Ordinary

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

theorem readOutside_cache_ne (x : HashInput) (s : State) :
    ∀ r ∈ support (readOutside x s), ∀ y, y ≠ x → r.2.cache y = s.cache y := by
  intro r hr y hy
  rcases readOutside_support x s r hr with h | ⟨_, h⟩
  · rw [h]
  · rw [h]; exact store_cache_ne s x y hy r.1

/-- An ordinary query changes the cache at most at its input. -/
theorem ordinaryStep_cache_ne (x : HashInput) (s : State) :
    ∀ r ∈ support (ordinaryStep model x s.known s), ∀ y, y ≠ x → r.2.cache y = s.cache y := by
  intro r hr y hy
  unfold ordinaryStep at hr
  split at hr
  · exact readOutside_cache_ne x s r hr y hy
  · split at hr
    · exact readOutside_cache_ne x _ r hr y hy
    · split at hr
      · rw [support_map] at hr
        obtain ⟨r', hr', rfl⟩ := hr
        rw [sampleCoordinate_expose _ s r' hr']
        rfl
      · exact readOutside_cache_ne x s r hr y hy

theorem ordinaryStep_extends (x : HashInput) (s : State) :
    ∀ r ∈ support (ordinaryStep model x s.known s), Extends s r.2 := by
  intro r hr
  exact extends_costStep model (.inl (.inr (.inl x))) s r (by rw [costStep_ordinary]; exact hr)

theorem forsCover_mono (parameter : PublicParameter) (root : Digest) (outcome : HiddenBridge.Outcome)
    (reveals : List Coordinate) {c c' : QueryCache HashSpec} (h : ∀ x v, c x = some v → c' x = some v)
    (hc : HiddenBridge.ForsCover parameter root outcome reveals c) :
    HiddenBridge.ForsCover parameter root outcome reveals c' := by
  obtain ⟨hvalid, digest, hdig, hrest⟩ := hc
  refine ⟨hvalid, digest, ?_, hrest⟩
  unfold HiddenBridge.cachedDigest at hdig ⊢
  cases h0 : c (tweakableHashInput parameter (.message 0)
      (messageDigestPayload root outcome.1.message outcome.1.signature.randomness)) with
  | none => rw [h0] at hdig; cases hdig
  | some a =>
      cases h1 : c (tweakableHashInput parameter (.message 1)
          (messageDigestPayload root outcome.1.message outcome.1.signature.randomness)) with
      | none => rw [h0, h1] at hdig; cases hdig
      | some b =>
          rw [h0, h1] at hdig
          rw [h _ _ h0, h _ _ h1]
          exact hdig

variable (parameter : PublicParameter) (data : PublicData)

theorem finalValue_presample (y : HashInput) (hk : tg.kind y = .none) (R : List Coordinate)
    (out : Run HashInput Coordinate HiddenBridge.Outcome × State) (s' : State)
    (hs' : s' ∈ support (presample y out.2)) :
    finalValue parameter data tg initial R out ≤ finalValue parameter data tg initial R (out.1, s') := by
  have hreal := realized_presample tg initial y hk out.2 s' hs'
  have hgrow : ∀ x v, out.2.cache x = some v → s'.cache x = some v := by
    cases hc : out.2.cache y with
    | some v =>
        rw [presample_cached y out.2 v hc, support_pure, Set.mem_singleton_iff] at hs'
        rw [hs']
        exact fun _ _ h => h
    | none =>
        rw [presample_fresh y out.2 hc, support_map] at hs'
        obtain ⟨u, _, rfl⟩ := hs'
        exact (extends_store out.2 y u hc).1
  unfold finalValue
  cases out.1.1 with
  | none => exact le_rfl
  | some outcome =>
      simp only [Option.elim]
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd ⟨forsCover_mono parameter data.root outcome _ hgrow h1.1, fun h => h1.2 (hreal.1 h)⟩ h2
      · exact bot_le
      · exact le_rfl

theorem finalValue_abort (R : List Coordinate) (s : State) :
    finalValue parameter data tg initial R ((none, [], [], []), s) = 0 := rfl

theorem interp_mass {α : Type} (computation : OracleComp CostSpec α) (budget : ℕ) (s : State) :
    ∑' out, Pr[= out | interp tg initial model computation budget s] = 1 :=
  tsum_probOutput_eq_one' probFailure_eq_zero

theorem finalValue_ordinary (R : List Coordinate) (x : HashInput)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome) (budget : ℕ) (hb : 1 ≤ budget) (s : State) :
    ∑' out, Pr[= out | interp tg initial model (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) budget s] *
        finalValue parameter data tg initial R out =
      ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        ∑' out, Pr[= out | interp tg initial model (next r.1) (budget - 1) r.2] *
          finalValue parameter data tg initial R out := by
  rw [interp_ordinary, if_pos hb, tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_map_mul]
  rfl

theorem flagged_ordinary (x : HashInput) (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) :
    expectedFlagged tg initial model (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) budget s =
      (pays tg initial s (.inl (.inr (.inl x))) : ℝ≥0∞) +
        ∑' r, Pr[= r | ordinaryStep model x s.known s] *
          expectedFlagged tg initial model (next r.1) (budget - 1) r.2 := by
  unfold expectedFlagged
  rw [interp_ordinary, if_pos hb, tsum_probOutput_bind_mul]
  simp only [tsum_probOutput_map_mul, flaggedCount_append, flaggedCount_touch, Nat.cast_add, mul_add,
    ENNReal.tsum_add, ENNReal.tsum_mul_right, interp_mass]
  rw [one_mul, tsum_probOutput_eq_one' probFailure_eq_zero, one_mul]

/-- Without a new pair, an ordinary query keeps the items and their views. -/
theorem same_items {x : HashInput} {s s' : State} (hext : Extends s s') (hother : ∀ y, y ≠ x → s'.cache y = s.cache y)
    (hnot : ¬∃ p call, x = pblk parameter data p call ∧ s.cache (pblk parameter data p 0) = none)
    {P : List Pair} (hP : PInv parameter data s P) :
    PInv parameter data s' P ∧ ∀ q ∈ P, pview parameter data s' q = pview parameter data s q := by
  have hkeep : ∀ y, s.cache y ≠ none → s'.cache y = s.cache y := by
    intro y hy
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hy
    rw [hv]; exact hext.1 y v hv
  have hzero : ∀ q, s'.cache (pblk parameter data q 0) = s.cache (pblk parameter data q 0) := by
    intro q
    by_cases hx : x = pblk parameter data q 0
    · by_cases hn : s.cache (pblk parameter data q 0) = none
      · exact absurd ⟨q, 0, hx, hn⟩ hnot
      · exact hkeep _ hn
    · exact hother _ (Ne.symm hx)
  have hland : ∀ q, LandedIn parameter data s' q ↔ LandedIn parameter data s q := by
    intro q; simp only [LandedIn, hzero q]
  refine ⟨⟨hP.nodup, fun q => (hP.mem q).trans (hland q).symm, fun q hq => ?_, fun q hq => ?_⟩, fun q hq => ?_⟩
  · have := hP.second q ((hland q).1 hq)
    rw [hkeep _ this]; exact this
  · rw [hzero q] at hq
    have h1 := hP.first q hq
    by_cases hx : x = pblk parameter data q 1
    · exact absurd ⟨q, 1, hx, hq⟩ hnot
    · rw [hother _ (Ne.symm hx)]; exact h1
  · have hl := (hP.mem q).1 hq
    have h1 := hP.second q hl
    unfold pview
    rw [hzero q, hkeep _ h1]

end Ordinary

omit [Params] in
theorem tsum_swap2 {α : Type} (w : α → ℝ≥0∞) (C : α → α → ℝ≥0∞) :
    ∑' u, w u * ∑' u', w u' * C u' u = ∑' a, w a * ∑' b, w b * C a b := by
  calc ∑' u, w u * ∑' u', w u' * C u' u = ∑' u, ∑' u', w u' * (w u * C u' u) :=
        tsum_congr fun u => by rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun u' => mul_left_comm _ _ _
    _ = ∑' u', ∑' u, w u' * (w u * C u' u) := ENNReal.tsum_comm
    _ = _ := tsum_congr fun u' => ENNReal.tsum_mul_left

section OrdinaryGood

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- The sibling of a new pair, presampled after the first read. -/
theorem new_pair_bound (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (L : QueryLog SigningSpec)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, Good parameter data wbar b0 Fail tg initial model L (next v))
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) (P : List Pair) (d : Multiset View) (R : List Coordinate)
    (hprep : Prepared initial s) (hP : PInv parameter data s P) (hD : DInv R d) (p : Pair)
    (hp0 : s.cache (pblk parameter data p 0) = none) (hp1 : s.cache (pblk parameter data p 1) = none)
    (call : Fin 2) :
    ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
        ∑' out, Pr[= out | interp tg initial model (next u) (budget - 1)
          (s.store (pblk parameter data p call) u)] * finalValue parameter data tg initial R out ≤
      pot parameter data wbar b0 Fail tg initial s P L d budget +
        b0 * ((if Realized tg initial s then 0 else 1) +
          ∑' u, Pr[= u | ($ᵗ HashOutput : ProbComp HashOutput)] *
            expectedFlagged tg initial model (next u) (budget - 1) (s.store (pblk parameter data p call) u)) := by
  -- the sibling, and the two orders of the blocks
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
  -- the bound for one answer, after presampling the sibling
  have hone : ∀ u, ∑' out, Pr[= out | interp tg initial model (next u) (budget - 1)
        (s.store (pblk parameter data p call) u)] * finalValue parameter data tg initial R out ≤
      ∑' u', Pr[= u' | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (pot parameter data wbar b0 Fail tg initial ((s.store (pblk parameter data p call) u).store y u')
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
    split_ifs with hc
    · exact h u (budget - 1) _ _ d R (hprep2 u u') (pinv_withPair hP hp0 u u') hD
    · exact h u (budget - 1) _ _ d R (hprep2 u' u) (pinv_withPair hP hp0 u' u) hD
  refine le_trans (ENNReal.tsum_le_tsum fun u => mul_le_mul_right (hone u) _) ?_
  simp only [mul_add, ENNReal.tsum_add]
  rw [← add_assoc]
  refine add_le_add ?_ ?_
  swap
  · -- the payments
    refine le_of_eq ?_
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
  · -- the potential
    by_cases hr : Realized tg initial s ∨ signatureLimit < L.length
    · refine le_of_eq_of_le (ENNReal.tsum_eq_zero.2 fun u => ?_) bot_le
      rw [ENNReal.tsum_eq_zero.2 fun u' => ?_, mul_zero]
      unfold pot
      rw [if_pos (hr.imp (realized_of_extends tg initial ((extends_store s _ u hxfresh).trans
        (extends_store _ y u' (hsib u)))) id), mul_zero]
    · have hreal : ¬Realized tg initial s := fun h' => hr (Or.inl h')
      rw [if_neg hreal, mul_one]
      have hpot : pot parameter data wbar b0 Fail tg initial s P L d budget =
          core parameter data wbar b0 Fail s P L d (signatureLimit - L.length) (budget - 1 + 1) := by
        unfold pot; rw [if_neg hr, Nat.sub_add_cancel hb]
      rw [hpot]
      refine le_trans ?_ (core_newPair wbar b0 Fail hw hb0 hP hp0 L d _ (budget - 1))
      unfold pairE
      have hle : ∀ u u', pot parameter data wbar b0 Fail tg initial ((s.store (pblk parameter data p call) u).store y u')
          (addPair parameter P p (if call = 0 then u else u')) L d (budget - 1) ≤
          if call = 0 then core parameter data wbar b0 Fail (withPair parameter data s p u u') (addPair parameter P p u) L d
            (signatureLimit - L.length) (budget - 1)
          else core parameter data wbar b0 Fail (withPair parameter data s p u' u) (addPair parameter P p u') L d
            (signatureLimit - L.length) (budget - 1) := by
        intro u u'
        rw [hstate u u']
        split_ifs
        · exact pot_le_core wbar b0 Fail tg initial _ _ L d _
        · exact pot_le_core wbar b0 Fail tg initial _ _ L d _
      refine le_trans (ENNReal.tsum_le_tsum fun u => mul_le_mul_right
        (ENNReal.tsum_le_tsum fun u' => mul_le_mul_right (hle u u') _) _) (le_of_eq ?_)
      split_ifs with hc
      · rfl
      · exact tsum_swap2 _ (fun a b => core parameter data wbar b0 Fail (withPair parameter data s p a b)
          (addPair parameter P p a) L d (signatureLimit - L.length) (budget - 1))

/-- **One ordinary query.** -/
theorem good_ordinary (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (L : QueryLog SigningSpec) (x : HashInput)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, Good parameter data wbar b0 Fail tg initial model L (next v)) :
    Good parameter data wbar b0 Fail tg initial model L
      (liftM (CostSpec.query (.inl (.inr (.inl x)))) >>= next) := by
  intro budget s P d R hprep hP hD
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
    exact new_pair_bound parameter data wbar b0 Fail tg initial model hkind hw hb0 L next h budget hb s P d R
      hprep hP hD p hp0 hp1 call
  · -- the items are kept
    calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] *
          (pot parameter data wbar b0 Fail tg initial s P L d budget +
            b0 * expectedFlagged tg initial model (next r.1) (budget - 1) r.2) := by
          refine ENNReal.tsum_le_tsum fun r => ?_
          by_cases hr : r ∈ support (ordinaryStep model x s.known s)
          · refine mul_le_mul_right ?_ _
            have hext := ordinaryStep_extends model x s r hr
            obtain ⟨hP', hview⟩ := same_items parameter data hext
              (ordinaryStep_cache_ne model x s r hr) hnew hP
            refine le_trans (h r.1 (budget - 1) r.2 P d R
              (fun i o hi => hext.1 i o (hprep i o hi)) hP' hD) (add_le_add ?_ le_rfl)
            exact pot_grow parameter data wbar b0 Fail tg initial hw hb0 hext hview L d (Nat.sub_le _ _)
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ ≤ _ := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
          refine add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) ?_
          refine le_add_left (le_of_eq ?_)
          simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

end OrdinaryGood

end LeanSphincs.Security.ForsPotential
