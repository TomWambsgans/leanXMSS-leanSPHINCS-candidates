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

/-! ### Counting cached randomizers -/

section Count

variable {parameter : PublicParameter} {data : PublicData}

theorem blk_zero_injective (m : Message) : Function.Injective fun ρ : Randomness => blk parameter data m ρ 0 := by
  intro ρ ρ' h
  by_contra hne
  exact blk_ne_of_ne parameter data m ρ ρ' 0 0 (Or.inl hne) h

variable (parameter data) in
/-- Block-0 inputs of a message. -/
noncomputable def zeroInputs (m : Message) : Finset HashInput :=
  Finset.univ.image fun ρ => blk parameter data m ρ 0

theorem cachedCount_eq (m : Message) (s : State) :
    cachedCount parameter data m s = ((zeroInputs parameter data m).filter fun x => s.cache x ≠ none).card := by
  unfold cachedCount zeroInputs
  rw [Finset.filter_image, Finset.card_image_of_injective _ (blk_zero_injective m)]

theorem card_filter_store_of_not_mem (T : Finset HashInput) (s : State) (x : HashInput) (hx : x ∉ T)
    (u : HashOutput) :
    (T.filter fun y => (s.store x u).cache y ≠ none).card = (T.filter fun y => s.cache y ≠ none).card := by
  congr 1
  refine Finset.filter_congr fun y hy => ?_
  rw [store_cache_ne s x y (fun h => hx (h ▸ hy)) u]

theorem count_withPair (m : Message) (s : State) (p : Pair) (u0 u1 : HashOutput) :
    cachedCount parameter data m (withPair parameter data s p u0 u1) ≤ cachedCount parameter data m s + 1 := by
  rw [cachedCount_eq, cachedCount_eq]
  unfold withPair
  rw [card_filter_store_of_not_mem _ _ _ ?_ u1]
  · exact card_filter_store_le _ _ _ _
  · intro hmem
    obtain ⟨ρ, _, hρ⟩ := Finset.mem_image.1 hmem
    exact absurd (pblk_injective parameter data (show pblk parameter data (m, ρ) 0 = pblk parameter data p 1 from hρ)).2
      (by decide)

end Count

/-! ### Paid programs -/

section Good

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- The final value: a FORS cover with no decided hit. -/
noncomputable def finalValue (R : List Coordinate) (out : Run HashInput Coordinate HiddenBridge.Outcome × State) :
    ℝ≥0∞ :=
  out.1.1.elim 0 fun outcome =>
    if HiddenBridge.ForsCover parameter data.root outcome (R ++ out.1.2.1) out.2.cache ∧ ¬Realized tg initial out.2
    then 1 else 0

/-- Cached block-0 entries of every message, plus the remaining budget, stay bounded. -/
def CountInv (s : State) (budget : ℕ) : Prop :=
  ∀ m : Message, cachedCount parameter data m s + budget ≤ Qtot

/-- A program whose final value is paid by the potential and the baseline payments. -/
def Good (L : QueryLog SigningSpec) (prog : OracleComp CostSpec HiddenBridge.Outcome) : Prop :=
  ∀ budget (s : State) (P : List Pair) (d : Multiset View) (R : List Coordinate),
    Prepared initial s → PInv parameter data s P → DInv R d → CountInv parameter data Qtot s budget →
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
    (h : ∀ v, Good parameter data wbar b0 Fail Qtot tg initial model L (next v)) :
    Good parameter data wbar b0 Fail Qtot tg initial model L
      (liftM (CostSpec.query (.inl (.inl draw))) >>= next) := by
  intro budget s P d R hprep hP hD hC
  unfold expectedFlagged
  rw [interp_draw, tsum_probOutput_bind_mul, tsum_probOutput_bind_mul]
  calc _ ≤ ∑' v, Pr[= v | (liftM (unifSpec.query draw) : ProbComp (Fin (draw + 1)))] *
        (pot parameter data wbar b0 Fail tg initial s P L d budget +
          b0 * expectedFlagged tg initial model (next v) budget s) :=
        ENNReal.tsum_le_tsum fun v => mul_le_mul_right (h v budget s P d R hprep hP hD hC) _
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
  (Qtot : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- The sibling of a new pair, presampled after the first read. -/
theorem new_pair_bound (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (L : QueryLog SigningSpec)
    (next : HashOutput → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ v, Good parameter data wbar b0 Fail Qtot tg initial model L (next v))
    (budget : ℕ) (hb : 1 ≤ budget) (s : State) (P : List Pair) (d : Multiset View) (R : List Coordinate)
    (hprep : Prepared initial s) (hP : PInv parameter data s P) (hD : DInv R d)
    (hC : CountInv parameter data Qtot s budget) (p : Pair)
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
    (h : ∀ v, Good parameter data wbar b0 Fail Qtot tg initial model L (next v)) :
    Good parameter data wbar b0 Fail Qtot tg initial model L
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
    exact new_pair_bound parameter data wbar b0 Fail Qtot tg initial model hkind hw hb0 L next h budget hb s P d R
      hprep hP hD hC p hp0 hp1 call
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
            have hcnt : CountInv parameter data Qtot r.2 (budget - 1) := by
              intro m
              have h1 : cachedCount parameter data m r.2 ≤ cachedCount parameter data m s + 1 := by
                rw [cachedCount_eq, cachedCount_eq]
                exact costStep_card_le model _ (.inl (.inr (.inl x))) s r (by rw [costStep_ordinary]; exact hr)
              have h2 := hC m
              omega
            refine le_trans (h r.1 (budget - 1) r.2 P d R
              (fun i o hi => hext.1 i o (hprep i o hi)) hP' hD hcnt) (add_le_add ?_ le_rfl)
            exact pot_grow parameter data wbar b0 Fail tg initial hw hb0 hext hview L d (Nat.sub_le _ _)
          · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
      _ ≤ _ := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
          refine add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) ?_
          refine le_add_left (le_of_eq ?_)
          simp only [mul_left_comm _ b0, ENNReal.tsum_mul_left]

end OrdinaryGood

/-! ### Leaves and verification -/

section Leaf

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ) {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- A covered view has a positive witness count. -/
theorem witness_pos_of_covered {R : List Coordinate} {d : Multiset View} (hD : DInv R d) (digest : MessageDigest)
    (hcov : Covered (HiddenBridge.revealedSet R) (fullDigestView digest)) :
    1 ≤ witness (Lifetime.localDigestView digest) d := by
  unfold witness
  refine Finset.one_le_prod' fun t _ => ?_
  have hmem := hcov t
  simp only [fullDigestView, HiddenBridge.revealedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  obtain ⟨w, hw, h1, h2⟩ := hD _ _ _ hmem
  unfold matchCount
  refine Multiset.card_pos.2 fun hzero => ?_
  have : w ∈ d.filter fun view => view.1 = (Lifetime.localDigestView digest).1 ∧
      view.2 t = (Lifetime.localDigestView digest).2 t :=
    Multiset.mem_filter.2 ⟨hw, by rw [localDigestView_fst, localDigestView_snd]; exact ⟨h1, h2⟩⟩
  rw [hzero] at this
  exact absurd this (Multiset.notMem_zero _)

/-- **Leaf.** A FORS cover with no decided hit is paid by the potential. -/
theorem good_pure (hw : wbar ≤ 1) (L : QueryLog SigningSpec) (forgery : Forgery) (verified : Bool) :
    Good parameter data wbar b0 Fail Qtot tg initial model L (pure (forgery, L, verified)) := by
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
  -- the pair's two blocks are cached
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
          unfold pot
          rw [if_neg (by
            rintro (h | h)
            · exact hreal h
            · exact absurd hvalid (by simp [SigningTranscript.Valid]; omega))]
          unfold core
          refine le_trans ?_ (le_trans (List.le_sum_of_mem (List.mem_map_of_mem hqP)) (le_self_add.trans le_self_add))
          unfold cand
          rw [if_pos (show Unsigned L q from hunsigned)]
          split_ifs
          · exact le_rfl
          · unfold candValue
            calc (1 : ℝ≥0∞) ≤ witnessFn (pview parameter data s q) d := by
                  unfold witnessFn
                  rw [hv]
                  exact_mod_cast witness_pos_of_covered hD _ hcovered
              _ ≤ virtual Finset.univ wbar (witnessFn (pview parameter data s q))
                    (signatureLimit - L.length) (items parameter data s (P.erase q)) d :=
                  base_le_virtual Finset.univ_nonempty hw (witness_props _).1 (witness_props _).2.1
                    (witness_props _).2.2 _ _ d
              _ ≤ _ := creations_mono_count (k := 0) Finset.univ_nonempty landing_le_one
                    (virtual_cons_le wbar hw (witness_props _) _ d) (virtual_perm' wbar _ d) (Nat.zero_le _) _

/-- Lifted hash computations are sequences of ordinary queries. -/
theorem good_liftHash (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hdigest : ∀ p call, tg.digest (pblk parameter data p call))
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (L : QueryLog SigningSpec) {α : Type} (computation : OracleComp HashSpec α)
    (next : α → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ a, Good parameter data wbar b0 Fail Qtot tg initial model L (next a)) :
    Good parameter data wbar b0 Fail Qtot tg initial model L
      ((liftM computation : OracleComp CostSpec α) >>= next) := by
  induction computation using OracleComp.inductionOn with
  | pure value => simpa only [liftM_pure, pure_bind] using h value
  | query_bind query rest ih =>
      rw [liftM_bind, bind_assoc]
      exact good_ordinary parameter data wbar b0 Fail Qtot tg initial model hparse hkind hdigest hw hb0 L query _ ih

end Leaf

/-! ### What a signing call adds -/

/-- The pairs that are not excluded. -/
noncomputable def others (excl : Pair → Prop) (P : List Pair) : List Pair := P.filter fun q => ¬excl q

theorem mem_others {excl : Pair → Prop} {P : List Pair} {q : Pair} : q ∈ others excl P ↔ q ∈ P ∧ ¬excl q := by
  unfold others; simp

theorem others_nodup {excl : Pair → Prop} {P : List Pair} (h : P.Nodup) : (others excl P).Nodup := h.filter _

section SignDefs

variable (parameter : PublicParameter) (data : PublicData) (m : Message) (s : State)

/-- Randomizers of the message whose block 0 is new and lands. -/
noncomputable def newRand (s' : State) : Finset Randomness :=
  Finset.univ.filter fun ρ => s.cache (blk parameter data m ρ 0) = none ∧ LandedIn parameter data s' (m, ρ)

/-- Pairs created by a signing call. -/
noncomputable def newPairs (s' : State) : List Pair := (newRand parameter data m s s').toList.map fun ρ => (m, ρ)

/-- Disclosure of an existing pair signed by the call. -/
noncomputable def poolDisc (out : Run HashInput Coordinate (Option Signature) × State) : Multiset View :=
  out.1.1.elim 0 fun r => r.elim 0 fun sig =>
    if s.cache (blk parameter data m sig.randomness 0) = none then 0
    else {pview parameter data out.2 (m, sig.randomness)}

/-- Disclosures after a signing call. -/
noncomputable def discAfter (d : Multiset View) (out : Run HashInput Coordinate (Option Signature) × State) :
    Multiset View :=
  d + ((newPairs parameter data m s out.2).map (pview parameter data out.2) : Multiset View) +
    poolDisc parameter data m s out

theorem newPairs_nodup (s' : State) : (newPairs parameter data m s s').Nodup :=
  (Finset.nodup_toList _).map fun _ _ h => (Prod.ext_iff.1 h).2

theorem mem_newPairs {s' : State} {q : Pair} :
    q ∈ newPairs parameter data m s s' ↔ q.1 = m ∧ s.cache (pblk parameter data q 0) = none ∧
      LandedIn parameter data s' q := by
  unfold newPairs newRand
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ρ, ⟨h0, hl⟩, rfl⟩
    exact ⟨rfl, h0, hl⟩
  · rintro ⟨hm, h0, hl⟩
    exact ⟨q.2, ⟨by rw [← hm]; exact h0, by rw [← hm]; exact hl⟩, by rw [← hm]⟩

/-- A pool sum over the randomizers of a message is at most the sum over the other items. -/
theorem pool_sum_le {P : List Pair} (hP : PInv parameter data s P) (excl : Pair → Prop) (g : View → ℝ≥0∞) :
    ∑ ρ, poolValue parameter data m s (fun ρ v => if excl (m, ρ) then 0 else g v) ρ ≤
      ((others excl P).map fun q => g (pview parameter data s q)).sum := by
  classical
  have hpoint : ∀ ρ, poolValue parameter data m s (fun ρ v => if excl (m, ρ) then 0 else g v) ρ =
      if (m, ρ) ∈ others excl P then g (pview parameter data s (m, ρ)) else 0 := by
    intro ρ
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
          have hmem := (hP.mem _).2 hland
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
          · simp [hx, mem_others, hmem, hv]
        · have : (m, ρ) ∉ P := fun hmem => by
            obtain ⟨u, hu, hlu⟩ := (hP.mem _).1 hmem
            change s.cache (blk parameter data m ρ 0) = some u at hu
            rw [h0] at hu; cases hu; exact hl hlu
          rw [if_neg hl]
          simp [mem_others, this]
  simp only [hpoint]
  rw [← Finset.sum_filter]
  have hnodup : (others excl P).Nodup := others_nodup hP.nodup
  rw [← List.sum_toFinset _ hnodup]
  calc ∑ ρ ∈ Finset.univ.filter (fun ρ => (m, ρ) ∈ others excl P), g (pview parameter data s (m, ρ))
      = ∑ q ∈ (Finset.univ.filter (fun ρ => (m, ρ) ∈ others excl P)).image (fun ρ => (m, ρ)),
          g (pview parameter data s q) := by
        rw [Finset.sum_image fun _ _ _ _ h => (Prod.ext_iff.1 h).2]
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset fun q hq => ?_
        obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.1 hq
        rw [Finset.mem_filter] at hρ
        exact List.mem_toFinset.2 hρ.2

end SignDefs

/-! ### The three shapes of a completed signing call -/

section SignShape

variable (parameter : PublicParameter) (data : PublicData) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (m : Message) {s : State}

theorem newRand_eq_empty {s' : State} (h : ∀ ρ, RelatedAt parameter data m s s' ρ) :
    newRand parameter data m s s' = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun ρ hρ => ?_
  simp only [newRand, Finset.mem_filter, Finset.mem_univ, true_and] at hρ
  obtain ⟨h0, u, hu, hl⟩ := hρ
  rcases (h ρ).2 with he | ⟨_, u', hu', hnl⟩
  · change s'.cache (blk parameter data m ρ 0) = some u at hu
    rw [he, h0] at hu; cases hu
  · change s'.cache (blk parameter data m ρ 0) = some u at hu
    rw [hu'] at hu; cases hu; exact hnl hl

theorem newRand_eq_single {s' : State} {ρ : Randomness} (h : ∀ ρ', ρ' ≠ ρ → RelatedAt parameter data m s s' ρ')
    (h0 : s.cache (blk parameter data m ρ 0) = none) (hl : LandedIn parameter data s' (m, ρ)) :
    newRand parameter data m s s' = {ρ} := by
  ext ρ'
  simp only [newRand, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨h0', u, hu, hl'⟩
    by_contra hne
    rcases (h ρ' hne).2 with he | ⟨_, u', hu', hnl⟩
    · change s'.cache (blk parameter data m ρ' 0) = some u at hu
      rw [he, h0'] at hu; cases hu
    · change s'.cache (blk parameter data m ρ' 0) = some u at hu
      rw [hu'] at hu; cases hu; exact hnl hl'
  · rintro rfl
    exact ⟨h0, hl⟩

theorem newRand_eq_empty_of_pool {s' : State} {ρ : Randomness} (h : ∀ ρ', ρ' ≠ ρ → RelatedAt parameter data m s s' ρ')
    (h0 : s.cache (blk parameter data m ρ 0) ≠ none) : newRand parameter data m s s' = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun ρ' hρ' => ?_
  simp only [newRand, Finset.mem_filter, Finset.mem_univ, true_and] at hρ'
  obtain ⟨h0', u, hu, hl'⟩ := hρ'
  by_cases hne : ρ' = ρ
  · subst hne; exact h0 h0'
  · rcases (h ρ' hne).2 with he | ⟨_, u', hu', hnl⟩
    · change s'.cache (blk parameter data m ρ' 0) = some u at hu
      rw [he, h0'] at hu; cases hu
    · change s'.cache (blk parameter data m ρ' 0) = some u at hu
      rw [hu'] at hu; cases hu; exact hnl hl'

/-- **Shapes.** A completed signing call adds nothing, one fresh landed pair, or signs a cached
landed pair. -/
theorem sign_shape {reveals : List Coordinate} {r : Option Signature} {s' : State}
    (post : SignPost parameter data m Fail s s' reveals r)
    (out : Run HashInput Coordinate (Option Signature) × State) (hout2 : out.2 = s') (hres : out.1.1 = some r) :
    (newRand parameter data m s s' = ∅ ∧ poolDisc parameter data m s out = 0) ∨
    (∃ ρ u0 u1, newRand parameter data m s s' = {ρ} ∧ poolDisc parameter data m s out = 0 ∧
      s'.cache (blk parameter data m ρ 0) = some u0 ∧ Landed parameter (blockIndex u0) ∧
      s'.cache (blk parameter data m ρ 1) = some u1 ∧ s.cache (blk parameter data m ρ 0) = none ∧
      (∀ ρ', ρ' ≠ ρ → RelatedAt parameter data m s s' ρ') ∧
      (r = none → (viewOf u0 u1).1 ∈ Fail) ∧ (∀ sig, r = some sig → sig.randomness = ρ)) ∨
    (∃ ρ u0 u1 sig, newRand parameter data m s s' = ∅ ∧ poolDisc parameter data m s out = {viewOf u0 u1} ∧
      r = some sig ∧ sig.randomness = ρ ∧ s.cache (blk parameter data m ρ 0) = some u0 ∧
      s'.cache (blk parameter data m ρ 0) = some u0 ∧ s'.cache (blk parameter data m ρ 1) = some u1) := by
  subst hout2
  rcases post with ⟨hrn, _, hrel⟩ | ⟨ρ, u0, u1, ⟨hs0, hl, hs1, hs0r, _, hothers⟩, _, hsig, hfl⟩
  · left
    refine ⟨newRand_eq_empty parameter data m hrel, ?_⟩
    unfold poolDisc; rw [hres, hrn]; rfl
  · rcases hs0r with hn | he
    · -- fresh
      right; left
      refine ⟨ρ, u0, u1, newRand_eq_single parameter data m hothers hn ⟨u0, hs0, hl⟩, ?_, hs0, hl, hs1, hn,
        hothers, fun hrn => (hfl hrn).2 hn, hsig⟩
      unfold poolDisc
      rw [hres]
      rcases r with _ | sig
      · rfl
      · simp only [Option.elim]
        rw [hsig sig rfl, if_pos hn]
    · rcases r with _ | sig
      · left
        refine ⟨newRand_eq_empty_of_pool parameter data m hothers (by rw [he]; exact Option.some_ne_none _), ?_⟩
        unfold poolDisc; rw [hres]; rfl
      · right; right
        refine ⟨ρ, u0, u1, sig, newRand_eq_empty_of_pool parameter data m hothers (by rw [he]; exact Option.some_ne_none _),
          ?_, rfl, hsig sig rfl, he, hs0, hs1⟩
        unfold poolDisc
        rw [hres]
        simp only [Option.elim]
        rw [hsig sig rfl, if_neg (by rw [he]; exact Option.some_ne_none _)]
        congr 1
        simp only [pview]
        change ((out.2.cache (blk parameter data m ρ 0)).elim _ fun u0 =>
          (out.2.cache (blk parameter data m ρ 1)).elim _ fun u1 => viewOf u0 u1) = _
        rw [hs0, hs1]
        rfl

end SignShape

/-! ### Upper values of a signing outcome -/

section SignUpper

variable (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (m : Message) (s : State) (n : ℕ)
  (d : Multiset View) (f : Multiset View → ℝ≥0∞)

/-- The value without disclosure. -/
noncomputable def baseV (J : List View) : ℝ≥0∞ := virtual Finset.univ wbar f n J d

/-- Gain of a fresh view that is disclosed and becomes an item. -/
noncomputable def gainF (J : List View) (u : View) : ℝ≥0∞ :=
  virtual Finset.univ wbar f n (u :: J) (d + {u}) - baseV wbar n d f J

/-- Gain of disclosing an existing item. -/
noncomputable def gainP (J : List View) (v : View) : ℝ≥0∞ :=
  virtual Finset.univ wbar f n J (d + {v}) - baseV wbar n d f J

/-- Upper value of one signing outcome, for future items `J`. -/
noncomputable def upper (excl : Pair → Prop) (out : Run HashInput Coordinate (Option Signature) × State)
    (J : List View) : ℝ≥0∞ :=
  baseV wbar n d f J + freshNewWeight parameter data m s (gainF wbar n d f J) out +
    outWeight parameter data m s 0 (fun ρ v => if excl (m, ρ) then 0 else gainP wbar n d f J v) out

theorem related_self : Related parameter data m s s := ⟨fun _ => rfl, fun _ => Or.inl rfl⟩

variable {parameter data wbar m s n d f}

theorem pview_of_cached {s' : State} {q : Pair} {u0 u1 : HashOutput} (h0 : s'.cache (pblk parameter data q 0) = some u0)
    (h1 : s'.cache (pblk parameter data q 1) = some u1) : pview parameter data s' q = viewOf u0 u1 := by
  simp only [pview, h0, h1, Option.elim]

/-- **Pointwise upper value.** -/
theorem upper_point (Fail : Finset (Fin (2 ^ subtreeHeight))) (hw : wbar ≤ 1)
    (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤) {P : List Pair} (hP : PInv parameter data s P)
    (excl : Pair → Prop) (out : Run HashInput Coordinate (Option Signature) × State) (r : Option Signature)
    (hres : out.1.1 = some r)
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
    virtual Finset.univ wbar f n (((newPairs parameter data m s out.2).map (pview parameter data out.2)) ++ J)
        (discAfter parameter data m s d out) ≤ upper parameter data wbar m s n d f excl out J := by
  have hprops := fun I => virtual_props Finset.univ_nonempty hw hf.1 hf.2.1 hf.2.2 n I
  unfold upper discAfter newPairs
  rcases shape with ⟨hnew, hpool⟩ | ⟨ρ, u0, u1, hnew, hpool, h0, hl, h1, hs0, _, _, _⟩ |
      ⟨ρ, u0, u1, sig, hnew, hpool, hr, hsig, hs0, h0, h1⟩
  · rw [hnew, hpool]
    simp only [Finset.toList_empty, List.map_nil, List.nil_append, Multiset.coe_nil, add_zero]
    exact le_trans le_self_add le_self_add
  · rw [hnew, hpool, Finset.toList_singleton]
    have hv : pview parameter data out.2 (m, ρ) = viewOf u0 u1 := pview_of_cached h0 h1
    simp only [List.map_cons, List.map_nil, hv, List.cons_append, List.nil_append, add_zero]
    rw [show ((([viewOf u0 u1] : List View)) : Multiset View) = {viewOf u0 u1} from rfl]
    have hbase : baseV wbar n d f J ≤ virtual Finset.univ wbar f n (viewOf u0 u1 :: J) (d + {viewOf u0 u1}) :=
      le_trans (virtual_le_cons Finset.univ_nonempty hw hf.1 hf.2.1 hf.2.2 n J _ d)
        ((hprops _).1 _ _ (Multiset.le_add_right _ _))
    rw [← add_tsub_cancel_of_le hbase]
    refine le_trans (add_le_add le_rfl ?_) le_self_add
    -- the fresh pair is counted in the fresh weight
    unfold freshNewWeight
    rw [if_pos (by rw [hres]; rfl)]
    have hs1 : s.cache (blk parameter data m ρ 1) = none := hP.first (m, ρ) hs0
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun ρ' => if s.cache (blk parameter data m ρ' 1) = none then
      (out.2.cache (blk parameter data m ρ' 0)).elim 0 (fun u0 =>
        (out.2.cache (blk parameter data m ρ' 1)).elim 0 fun u1 =>
          if Landed parameter (blockIndex u0) then gainF wbar n d f J (viewOf u0 u1) else 0) else 0)
      (fun _ _ => bot_le) (Finset.mem_univ ρ))
    simp only [hs1, h0, h1, Option.elim, if_true, if_pos hl]
    rfl
  · rw [hnew, hpool]
    simp only [Finset.toList_empty, List.map_nil, List.nil_append, Multiset.coe_nil, add_zero]
    have hbase : baseV wbar n d f J ≤ virtual Finset.univ wbar f n J (d + {viewOf u0 u1}) :=
      (hprops _).1 _ _ (Multiset.le_add_right _ _)
    rw [← add_tsub_cancel_of_le hbase]
    refine le_trans (add_le_add le_rfl ?_) (add_le_add le_self_add le_rfl)
    -- the pool pair is counted in the pool weight
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

end SignUpper

/-! ### Expected upper values -/

section SignExpect

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (wbar : ℝ≥0∞) (m : Message) (s : State) (n : ℕ)
  (d : Multiset View) (f : Multiset View → ℝ≥0∞)

/-- The fair-share hypotheses of the grinding signer. -/
structure Fair (Cmax : ℕ) : Prop where
  ne_top : wbar ≠ ⊤
  le_one : wbar ≤ 1
  cmax : Cmax ≤ 2 ^ 128
  share : ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ ≤ wbar * (((2 ^ 128 - Cmax : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞)) * landing

variable {parameter data wbar m s n d f}

theorem upper_expect (hparse : ∀ ρ call, model.parse (blk parameter data m ρ call) = none)
    {Cmax : ℕ} (hfair : Fair wbar Cmax) (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤)
    {P : List Pair} (hP : PInv parameter data s P) (excl : Pair → Prop) (attempts budget : ℕ)
    (hcount : cachedCount parameter data m s + attempts ≤ Cmax) (J : List View) :
    ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
        upper parameter data wbar m s n d f excl out J ≤
      baseV wbar n d f J + freshAvg Finset.univ (gainF wbar n d f J) +
        wbar * ∑ ρ, poolValue parameter data m s (fun ρ v => if excl (m, ρ) then 0 else gainP wbar n d f J v) ρ := by
  have hprops := virtual_props Finset.univ_nonempty hfair.le_one hf.1 hf.2.1 hf.2.2 n J
  have hnob1 : ∀ ρ, s.cache (blk parameter data m ρ 0) = none → s.cache (blk parameter data m ρ 1) = none :=
    fun ρ h => hP.first (m, ρ) h
  have hlandb1 : ∀ ρ u0, s.cache (blk parameter data m ρ 0) = some u0 → Landed parameter (blockIndex u0) →
      s.cache (blk parameter data m ρ 1) ≠ none := fun ρ u0 h0 hl => hP.second (m, ρ) ⟨u0, h0, hl⟩
  set B : ℝ≥0∞ := ∑ v : View, virtual Finset.univ wbar f n J (d + {v}) with hB
  have hBfin : B ≠ ⊤ := ENNReal.sum_ne_top.2 fun v _ => hprops.2.2 _
  have hgp : ∀ ρ v, (fun ρ v => if excl (m, ρ) then 0 else gainP wbar n d f J v) ρ v ≤ B := by
    intro ρ v
    simp only
    split_ifs
    · exact bot_le
    · exact le_trans tsub_le_self (Finset.single_le_sum (f := fun v => virtual Finset.univ wbar f n J (d + {v}))
        (fun _ _ => bot_le) (Finset.mem_univ v))
  have hpool := loop_bound tg initial model parameter data m hparse s hnob1 (fun _ => 0)
    (fun ρ v => if excl (m, ρ) then 0 else gainP wbar n d f J v) B hBfin (fun _ => bot_le) hgp wbar hfair.ne_top
    Cmax hfair.cmax hfair.share attempts budget s (related_self parameter data m s) hcount
  have hfresh := loop_bound_fresh tg initial model parameter data m hparse s hnob1 hlandb1 (gainF wbar n d f J)
    attempts budget s (related_self parameter data m s)
  unfold upper
  simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
  refine add_le_add (add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) hfresh) (le_trans hpool ?_)
  simp [freshAvg]

/-- The pool sum fits in the coins of the items. -/
theorem slot_combine (Fail : Finset (Fin (2 ^ subtreeHeight))) (hw : wbar ≤ 1)
    (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤)
    {P : List Pair} (hP : PInv parameter data s P) (excl : Pair → Prop) (news : List View) :
    baseV wbar n d f (news ++ items parameter data s (others excl P)) +
        freshAvg Finset.univ (gainF wbar n d f (news ++ items parameter data s (others excl P))) +
        wbar * ∑ ρ, poolValue parameter data m s (fun ρ v => if excl (m, ρ) then 0 else
          gainP wbar n d f (news ++ items parameter data s (others excl P)) v) ρ ≤
      virtual Finset.univ wbar f (n + 1) (news ++ items parameter data s (others excl P)) d := by
  set J := news ++ items parameter data s (others excl P) with hJ
  refine le_trans (add_le_add le_rfl ?_) (slot_ge Finset.univ_nonempty hw hf.1 hf.2.1 hf.2.2 n J d)
  refine le_trans (mul_le_mul_right (pool_sum_le parameter data m s hP excl (gainP wbar n d f J)) wbar) ?_
  rw [← List.sum_map_mul_left]
  have hsplit : (J.map fun w => wbar * (virtual Finset.univ wbar f n J (d + {w}) - virtual Finset.univ wbar f n J d)).sum =
      (news.map fun w => wbar * gainP wbar n d f J w).sum +
        ((items parameter data s (others excl P)).map fun w => wbar * gainP wbar n d f J w).sum := by
    rw [hJ, List.map_append, List.sum_append]
    rfl
  rw [hsplit]
  refine le_trans (le_of_eq ?_) le_add_self
  unfold items
  rw [List.map_map]
  rfl

/-- **A dominated term.** Averaged over a signing call, the upper value of a term is at most its
value with one more virtual slot. -/
theorem term_expect (hparse : ∀ ρ call, model.parse (blk parameter data m ρ call) = none)
    (Fail : Finset (Fin (2 ^ subtreeHeight))) {Cmax : ℕ} (hfair : Fair wbar Cmax)
    (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤)
    {P : List Pair} (hP : PInv parameter data s P) (excl : Pair → Prop) (attempts budget k : ℕ)
    (hcount : cachedCount parameter data m s + attempts ≤ Cmax) :
    ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
        creations Finset.univ landing (fun J => upper parameter data wbar m s n d f excl out J) k
          (items parameter data s (others excl P)) ≤
      creations Finset.univ landing (fun J => virtual Finset.univ wbar f (n + 1) J d) k
        (items parameter data s (others excl P)) := by
  rw [creations_tsum]
  refine creations_mono_suffix k _ fun news => ?_
  exact le_trans (upper_expect tg initial model hparse hfair hf hP excl attempts budget hcount _)
    (slot_combine Fail hfair.le_one hf hP excl news)

end SignExpect

/-! ### The state after a signing call -/

section SignParams

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ)
  (m : Message)

variable {parameter data m}

theorem other_message_kept (attempts budget : ℕ) (s : State)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSourceLoop parameter data m attempts) budget s))
    (q : Pair) (hq : q.1 ≠ m) (call : Fin 2) :
    out.2.cache (pblk parameter data q call) = s.cache (pblk parameter data q call) := by
  refine interp_avoids_cache tg initial model _ _ (avoids_loop parameter data m attempts) budget s out hout _ ⟨?_, ?_⟩
  · exact msgInput_digestInput parameter data.root q.1 q.2 call
  · intro ρ c h
    exact hq (congrArg Prod.fst
      (pblk_injective parameter data (show pblk parameter data q call = pblk parameter data (m, ρ) c from h)).1)

theorem landed_of_cached {s : State} {P : List Pair} (hP : PInv parameter data s P) {q : Pair}
    (hq : q ∈ P) : ∃ u0 u1, s.cache (pblk parameter data q 0) = some u0 ∧ Landed parameter (blockIndex u0) ∧
      s.cache (pblk parameter data q 1) = some u1 := by
  obtain ⟨u0, h0, hl⟩ := (hP.mem q).1 hq
  obtain ⟨u1, h1⟩ := Option.ne_none_iff_exists'.1 (hP.second q ⟨u0, h0, hl⟩)
  exact ⟨u0, u1, h0, hl, h1⟩

/-- **The state after a signing call.** -/
theorem sign_params (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hfail : ∀ ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (attempts budget : ℕ) (s : State) (P : List Pair) (d : Multiset View) (R : List Coordinate)
    (hprep : Prepared initial s) (hP : PInv parameter data s P) (hD : DInv R d)
    (hC : CountInv parameter data Qtot s budget)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSourceLoop parameter data m attempts) budget s))
    (r : Option Signature) (hr : out.1.1 = some r) :
    Prepared initial out.2 ∧ PInv parameter data out.2 (newPairs parameter data m s out.2 ++ P) ∧
      DInv (R ++ out.1.2.1) (discAfter parameter data m s d out) ∧
      CountInv parameter data Qtot out.2 (budget - traceCost out.1.2.2.1) ∧
      (∀ q ∈ P, pview parameter data out.2 q = pview parameter data s q) := by
  have hext := interp_extends tg initial model _ budget s out hout
  have hpost := loop_post tg initial model parameter data m (fun ρ call => hparse (m, ρ) call) Fail hfail
    attempts budget s hprep out hout r hr
  have hother := other_message_kept tg initial model attempts budget s out hout
  -- every randomizer of the message is related, or the selected one
  have hrelOr : ∀ ρ, RelatedAt parameter data m s out.2 ρ ∨
      ∃ u0 u1, Selected parameter data m s out.2 ρ u0 u1 := by
    intro ρ
    rcases hpost with ⟨_, _, hrel⟩ | ⟨ρs, u0, u1, hsel, _⟩
    · exact Or.inl (hrel ρ)
    · by_cases h : ρ = ρs
      · subst h; exact Or.inr ⟨u0, u1, hsel⟩
      · exact Or.inl (hsel.2.2.2.2.2 ρ h)
  have hgrow : ∀ q call u, s.cache (pblk parameter data q call) = some u →
      out.2.cache (pblk parameter data q call) = some u := fun q call u h => hext.1 _ u h
  refine ⟨fun x v hx => hext.1 x v (hprep x v hx), ⟨?_, fun q => ?_, fun q hq => ?_, fun q hq => ?_⟩, ?_, ?_, ?_⟩
  · -- no duplicate items
    refine List.nodup_append.2 ⟨newPairs_nodup parameter data m s out.2, hP.nodup, fun a ha b hb hab => ?_⟩
    subst hab
    obtain ⟨_, h0, _⟩ := (mem_newPairs parameter data m s).1 ha
    obtain ⟨u, hu, _⟩ := (hP.mem a).1 hb
    rw [h0] at hu; cases hu
  · -- the items are the landed pairs
    rw [List.mem_append, mem_newPairs]
    constructor
    · rintro (⟨_, _, hl⟩ | hq)
      · exact hl
      · obtain ⟨u0, h0, hl⟩ := (hP.mem q).1 hq
        exact ⟨u0, hgrow q 0 u0 h0, hl⟩
    · rintro ⟨u0, h0, hl⟩
      cases hs0 : s.cache (pblk parameter data q 0) with
      | none =>
          left
          refine ⟨?_, rfl, ⟨u0, h0, hl⟩⟩
          by_contra hm
          rw [hother q hm 0, hs0] at h0
          cases h0
      | some u =>
          right
          have := hgrow q 0 u hs0
          rw [h0] at this
          cases this
          exact (hP.mem q).2 ⟨u0, hs0, hl⟩
  · -- landed pairs have both blocks
    obtain ⟨u0, h0, hl⟩ := hq
    cases hs0 : s.cache (pblk parameter data q 0) with
    | some u =>
        have := hgrow q 0 u hs0
        rw [h0] at this
        cases this
        obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hP.second q ⟨u0, hs0, hl⟩)
        rw [hgrow q 1 v hv]
        exact Option.some_ne_none _
    | none =>
        have hm : q.1 = m := by
          by_contra hm
          rw [hother q hm 0, hs0] at h0
          cases h0
        obtain ⟨msg, ρ⟩ := q
        simp only at hm
        subst hm
        rcases hrelOr ρ with hrel | ⟨u0', u1', hsel⟩
        · rcases hrel.2 with he | ⟨_, u, hu, hnl⟩
          · change out.2.cache (blk parameter data msg ρ 0) = some u0 at h0
            rw [he] at h0
            change s.cache (blk parameter data msg ρ 0) = none at hs0
            rw [hs0] at h0; cases h0
          · change out.2.cache (blk parameter data msg ρ 0) = some u0 at h0
            rw [hu] at h0; cases h0; exact absurd hl hnl
        · change out.2.cache (blk parameter data msg ρ 1) ≠ none
          rw [hsel.2.2.1]
          exact Option.some_ne_none _
  · -- no pair has only its second block
    have hs0 : s.cache (pblk parameter data q 0) = none := by
      cases hc : s.cache (pblk parameter data q 0) with
      | none => rfl
      | some u => rw [hgrow q 0 u hc] at hq; cases hq
    have hs1 := hP.first q hs0
    by_cases hm : q.1 = m
    · obtain ⟨msg, ρ⟩ := q
      simp only at hm
      subst hm
      rcases hrelOr ρ with hrel | ⟨u0', u1', hsel⟩
      · change out.2.cache (blk parameter data msg ρ 1) = none
        rw [hrel.1]; exact hs1
      · change out.2.cache (blk parameter data msg ρ 0) = none at hq
        rw [hsel.1] at hq; cases hq
    · rw [hother q hm 1]; exact hs1
  · -- every revealed secret has a disclosed view
    intro i t l hmem
    rcases List.mem_append.1 hmem with hR | hrev
    · obtain ⟨v, hv, h1, h2⟩ := hD i t l hR
      exact ⟨v, Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inl hv))), h1, h2⟩
    · rcases hpost with ⟨_, hnil, _⟩ | ⟨ρs, u0, u1, hsel, hfts, hsig, hfl⟩
      · rw [hnil] at hrev; cases hrev
      · obtain ⟨hi, hl⟩ := hfts _ hrev i t l rfl
        refine ⟨viewOf u0 u1, ?_, by rw [hi]; rfl, by rw [hl]; rfl⟩
        have hv : pview parameter data out.2 (m, ρs) = viewOf u0 u1 := pview_of_cached hsel.1 hsel.2.2.1
        rcases r with _ | sig
        · rw [(hfl rfl).1] at hrev; cases hrev
        · unfold discAfter
          rcases hsel.2.2.2.1 with hn | he
          · have hnew : (m, ρs) ∈ newPairs parameter data m s out.2 :=
              (mem_newPairs parameter data m s).2 ⟨rfl, hn, ⟨u0, hsel.1, hsel.2.1⟩⟩
            refine Multiset.mem_add.2 (Or.inl (Multiset.mem_add.2 (Or.inr ?_)))
            rw [Multiset.mem_coe, ← hv]
            exact List.mem_map_of_mem hnew
          · refine Multiset.mem_add.2 (Or.inr ?_)
            unfold poolDisc
            rw [hr]
            simp only [Option.elim]
            rw [hsig sig rfl, he, if_neg (Option.some_ne_none _), hv]
            exact Multiset.mem_singleton_self _
  · -- the count of cached randomizers
    intro m'
    have h1 : cachedCount parameter data m' out.2 ≤ cachedCount parameter data m' s + traceCost out.1.2.2.1 := by
      rw [cachedCount_eq, cachedCount_eq]
      exact interp_card_le tg initial model _ _ budget s out hout
    have h2 := interp_traceCost_le tg initial model _ budget s out hout
    have h3 := hC m'
    omega
  · -- items keep their views
    intro q hq
    obtain ⟨u0, u1, h0, _, h1⟩ := landed_of_cached hP hq
    rw [pview_of_cached h0 h1, pview_of_cached (hgrow q 0 u0 h0) (hgrow q 1 u1 h1)]

end SignParams

/-! ### The potential after a signing call -/

section SignPoint

variable (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (m : Message) (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View)

omit [Params] in
theorem erase_eq_filter' {P : List Pair} (hP : P.Nodup) (q : Pair) : P.erase q = others (· = q) P := by
  rw [hP.erase_eq_filter]
  unfold others
  congr 1
  funext q'
  rw [Bool.eq_iff_iff]
  simp [bne_iff_ne]

omit [Params] in
theorem filter_false' (P : List Pair) : others (fun _ => False) P = P := by unfold others; simp

/-- Bound for one outcome of a signing call. -/
noncomputable def canon (n k : ℕ) (out : Run HashInput Coordinate (Option Signature) × State) : ℝ≥0∞ :=
  freshNewWeight parameter data m s (fun v => if v.1 ∈ Fail then 1 else 0) out +
  (P.map fun q => if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
      creations Finset.univ landing (fun J => upper parameter data wbar m s n d (witnessFn (pview parameter data s q))
        (· = q) out J) k (items parameter data s (others (· = q) P))) else 0).sum +
  k * (creations Finset.univ landing (fun J => upper parameter data wbar m s n d (excess b0) (fun _ => False) out J) k
      (items parameter data s (others (fun _ => False) P)) + failMass Fail) +
  n * failMass Fail

variable {parameter data wbar b0 Fail m s P L d}

theorem freshNewWeight_ge {out : Run HashInput Coordinate (Option Signature) × State} {r : Option Signature}
    (hres : out.1.1 = some r) {ρ : Randomness} {u0 u1 : HashOutput}
    (hs1 : s.cache (blk parameter data m ρ 1) = none) (h0 : out.2.cache (blk parameter data m ρ 0) = some u0)
    (hl : Landed parameter (blockIndex u0)) (h1 : out.2.cache (blk parameter data m ρ 1) = some u1)
    (g : View → ℝ≥0∞) : g (viewOf u0 u1) ≤ freshNewWeight parameter data m s g out := by
  unfold freshNewWeight
  rw [if_pos (by rw [hres]; rfl)]
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun ρ' => if s.cache (blk parameter data m ρ' 1) = none then
    (out.2.cache (blk parameter data m ρ' 0)).elim 0 (fun u0 =>
      (out.2.cache (blk parameter data m ρ' 1)).elim 0 fun u1 =>
        if Landed parameter (blockIndex u0) then g (viewOf u0 u1) else 0) else 0)
    (fun _ _ => bot_le) (Finset.mem_univ ρ))
  simp only [hs1, h0, h1, Option.elim, if_true, if_pos hl]

theorem unsigned_of_append {L : QueryLog SigningSpec} {e : (t : Message) × Option Signature} {q : Pair}
    (h : Unsigned (L ++ [e]) q) : Unsigned L q :=
  fun entry he sig hs => h entry (List.mem_append_left _ he) sig hs

theorem not_unsigned_signed {L : QueryLog SigningSpec} {sig : Signature} :
    ¬Unsigned (L ++ [⟨m, some sig⟩]) (m, sig.randomness) := fun h =>
  h ⟨m, some sig⟩ (List.mem_append_right _ (List.mem_singleton_self _)) sig rfl ⟨rfl, rfl⟩

end SignPoint

/-- New items in front, fewer future pairs, then a pointwise bound. -/
theorem post_term_le {wbar : ℝ≥0∞} (hw : wbar ≤ 1) {f : Multiset View → ℝ≥0∞}
    (hf : Monotone' f ∧ Supermodular f ∧ ∀ D, f D ≠ ⊤) (pre I : List View) (n : ℕ) (d' : Multiset View)
    {k' k : ℕ} (hk : k' ≤ k) (U : List View → ℝ≥0∞) (hU : ∀ J, virtual Finset.univ wbar f n (pre ++ J) d' ≤ U J) :
    creations Finset.univ landing (fun J => virtual Finset.univ wbar f n J d') k' (pre ++ I) ≤
      creations Finset.univ landing U k I := by
  rw [creations_prepend (virtual_perm' wbar n d') pre]
  refine le_trans (creations_mono_count Finset.univ_nonempty landing_le_one ?_ ?_ hk I) (creations_mono hU k I)
  · intro v J
    rw [virtual_perm n (List.perm_middle (a := v) (l₁ := pre) (l₂ := J)) d']
    exact virtual_cons_le wbar hw hf n d' v _
  · intro J J' hJ
    exact virtual_perm n (hJ.append_left pre) d'

section SignPointMain

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ) (m : Message)

/-- **The potential after one signing outcome.** -/
theorem sign_point (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hfail : ∀ ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (hw : wbar ≤ 1) (hb0 : b0 ≠ ⊤) (attempts budget : ℕ) (s : State) (P : List Pair) (L : QueryLog SigningSpec)
    (d : Multiset View) (R : List Coordinate) (hprep : Prepared initial s) (hP : PInv parameter data s P)
    (hD : DInv R d) (hC : CountInv parameter data Qtot s budget)
    (out : Run HashInput Coordinate (Option Signature) × State)
    (hout : out ∈ support (interp tg initial model (signCostSourceLoop parameter data m attempts) budget s))
    (r : Option Signature) (hr : out.1.1 = some r) {k' : ℕ} (hk : k' ≤ budget) :
    pot parameter data wbar b0 Fail tg initial out.2 (newPairs parameter data m s out.2 ++ P) (L ++ [⟨m, r⟩])
        (discAfter parameter data m s d out) k' ≤
      if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
      else canon parameter data wbar b0 Fail m s P L d (signatureLimit - (L.length + 1)) budget out := by
  obtain ⟨_, hP', _, _, hview⟩ := sign_params tg initial model Fail Qtot hparse hfail attempts budget
    s P d R hprep hP hD hC out hout r hr
  have hext := interp_extends tg initial model _ budget s out hout
  have hpost := loop_post tg initial model parameter data m (fun ρ call => hparse (m, ρ) call) Fail hfail
    attempts budget s hprep out hout r hr
  have hshape := sign_shape parameter data Fail m hpost out rfl hr
  unfold pot
  by_cases hcase : Realized tg initial out.2 ∨ signatureLimit < (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length
  · rw [if_pos hcase]; exact bot_le
  rw [if_neg hcase]
  have hreal : ¬Realized tg initial s := fun h => hcase (Or.inl (realized_of_extends tg initial hext h))
  have hlen : L.length < signatureLimit := by
    have := hcase
    simp only [List.length_append, List.length_singleton, not_or, not_lt] at this
    omega
  rw [if_neg (by push_neg; exact ⟨hreal, hlen⟩)]
  have hn : signatureLimit - (L ++ [⟨m, r⟩] : QueryLog SigningSpec).length = signatureLimit - (L.length + 1) := by simp
  rw [hn]
  set n := signatureLimit - (L.length + 1) with hndef
  set pre := (newPairs parameter data m s out.2).map (pview parameter data out.2) with hpre
  have hnotnew : ∀ q ∈ P, q ∉ newPairs parameter data m s out.2 := by
    intro q hq hnew
    obtain ⟨_, h0, _⟩ := (mem_newPairs parameter data m s).1 hnew
    obtain ⟨u, hu, _⟩ := (hP.mem q).1 hq
    rw [h0] at hu; cases hu
  have hitemsP : ∀ (l : List Pair), (∀ q ∈ l, q ∈ P) →
      items parameter data out.2 (newPairs parameter data m s out.2 ++ l) = pre ++ items parameter data s l := by
    intro l hl
    unfold items
    rw [List.map_append]
    congr 1
    exact List.map_congr_left fun q hq => hview q (hl q hq)
  unfold core canon
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
      unfold cand
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
    unfold cand
    by_cases hU' : Unsigned (L ++ [⟨m, r⟩] : QueryLog SigningSpec) q
    · have hU := unsigned_of_append hU'
      rw [if_pos hU', if_pos hU, hview q hq]
      split_ifs with hF
      · exact le_rfl
      · unfold candValue
        rw [hview q hq, List.erase_append_right _ (hnotnew q hq), erase_eq_filter' hP.nodup q,
          hitemsP _ fun q' hq' => (mem_others.1 hq').1]
        refine post_term_le hw (witness_props _) pre _ n _ hk _ fun J => ?_
        refine upper_point Fail hw (witness_props _) hP (· = q) out r hr hshape (fun sig hsig _ heq => ?_) J
        subst hsig
        exact not_unsigned_signed (m := m) (L := L) (by rw [heq]; exact hU')
    · rw [if_neg hU']
      exact bot_le
  · -- the excess forecast
    refine mul_le_mul' (by exact_mod_cast hk) (add_le_add ?_ le_rfl)
    unfold hValue
    rw [hitemsP P fun q hq => hq, filter_false']
    refine post_term_le hw (excess_props b0 hb0) pre _ n _ hk _ fun J => ?_
    exact upper_point Fail hw (excess_props b0 hb0) hP (fun _ => False) out r hr hshape (fun _ _ _ h => h) J

/-- **The signing step in expectation.** -/
theorem sign_expect (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    {Cmax : ℕ} (hfair : Fair wbar Cmax) (hb0 : b0 ≠ ⊤) (attempts budget : ℕ) (s : State) (P : List Pair)
    (L : QueryLog SigningSpec) (d : Multiset View) (hP : PInv parameter data s P)
    (hcount : cachedCount parameter data m s + attempts ≤ Cmax) :
    ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
        (if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
          else canon parameter data wbar b0 Fail m s P L d (signatureLimit - (L.length + 1)) budget out) ≤
      pot parameter data wbar b0 Fail tg initial s P L d budget := by
  by_cases hcase : Realized tg initial s ∨ signatureLimit ≤ L.length
  · simp only [if_pos hcase, mul_zero, tsum_zero]
    exact bot_le
  simp only [if_neg hcase]
  have hcase' : ¬Realized tg initial s ∧ L.length < signatureLimit := by push_neg at hcase; exact hcase
  have hlen := hcase'.2
  unfold pot
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
  -- the four parts
  have hFN := loop_bound_fresh tg initial model parameter data m hparse' s hnob1 hlandb1
    (fun v => if v.1 ∈ Fail then 1 else 0) attempts budget s (related_self parameter data m s)
  have hT : ∀ q ∈ P, ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data m attempts) budget s] *
      (if Unsigned L q then (if (pview parameter data s q).1 ∈ Fail then 1 else
        creations Finset.univ landing (fun J => upper parameter data wbar m s n d (witnessFn (pview parameter data s q))
          (· = q) out J) budget (items parameter data s (others (· = q) P))) else 0) ≤
      cand parameter data wbar Fail s P L d (n + 1) budget q := by
    intro q _
    unfold cand
    split_ifs
    · rw [ENNReal.tsum_mul_right, mul_one]; exact hmass
    · unfold candValue
      rw [erase_eq_filter' hP.nodup q]
      exact term_expect tg initial model hparse' Fail hfair (witness_props _) hP (· = q) attempts budget budget hcount
    · simp
  have hH := term_expect tg initial model (n := n) (d := d) hparse' Fail hfair (excess_props b0 hb0) hP (fun _ => False)
    attempts budget budget hcount
  rw [filter_false'] at hH
  unfold canon core
  simp only [mul_add, ENNReal.tsum_add, filter_false']
  rw [tsum_list_sum]
  have hφ : freshAvg Finset.univ (fun v : View => if v.1 ∈ Fail then (1 : ℝ≥0∞) else 0) = failMass Fail := rfl
  rw [hφ] at hFN
  calc _ ≤ failMass Fail + (P.map (cand parameter data wbar Fail s P L d (n + 1) budget)).sum +
        (budget * hValue parameter data wbar b0 s P d (n + 1) budget + budget * failMass Fail) + n * failMass Fail := by
        refine add_le_add (add_le_add (add_le_add hFN (List.sum_le_sum hT)) (add_le_add ?_ ?_)) ?_
        · simp only [mul_left_comm _ (budget : ℝ≥0∞), ENNReal.tsum_mul_left]
          exact mul_le_mul_left' hH _
        · rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' hmass
        · rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' hmass
    _ = _ := by push_cast; ring

end SignPointMain

/-! ### The signing step -/

section SignGood

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (wbar b0 : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))
  (Qtot : ℕ)

theorem interpThen_some {α β : Type} (next : α → OracleComp CostSpec β) (budget : ℕ)
    (o1 : Run HashInput Coordinate α × State) (v : α) (hv : o1.1.1 = some v) :
    interpThen tg initial model next budget o1 =
      (fun o2 => ((o2.1.1, o1.1.2.1 ++ o2.1.2.1, o1.1.2.2.1 ++ o2.1.2.2.1, o1.1.2.2.2 ++ o2.1.2.2.2), o2.2)) <$>
        interp tg initial model (next v) (budget - traceCost o1.1.2.2.1) o1.2 := by
  unfold interpThen
  rw [hv]

theorem interpThen_none {α β : Type} (next : α → OracleComp CostSpec β) (budget : ℕ)
    (o1 : Run HashInput Coordinate α × State) (hv : o1.1.1 = none) :
    interpThen tg initial model next budget o1 = pure ((none, o1.1.2.1, o1.1.2.2.1, o1.1.2.2.2), o1.2) := by
  unfold interpThen
  rw [hv]

/-- **One signing call.** -/
theorem good_sign (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    {Cmax : ℕ} (hfair : Fair wbar Cmax) (hb0 : b0 ≠ ⊤) (hQ : Qtot + digestAttemptLimit ≤ Cmax)
    (L : QueryLog SigningSpec) (m : Message) (next : Option Signature → OracleComp CostSpec HiddenBridge.Outcome)
    (h : ∀ r, Good parameter data wbar b0 Fail Qtot tg initial model (L ++ [⟨m, r⟩]) (next r)) :
    Good parameter data wbar b0 Fail Qtot tg initial model L (signCostSource parameter data m >>= next) := by
  intro budget s P d R hprep hP hD hC
  have hcount : cachedCount parameter data m s + digestAttemptLimit ≤ Cmax := by
    have := hC m; omega
  unfold signCostSource
  set sign := signCostSourceLoop parameter data m digestAttemptLimit with hsign
  -- the continuation's flagged count
  set cont : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    o1.1.1.elim 0 fun r => expectedFlagged tg initial model (next r) (budget - traceCost o1.1.2.2.1) o1.2 with hcont
  set canonR : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    if Realized tg initial s ∨ signatureLimit ≤ L.length then 0
    else canon parameter data wbar b0 Fail m s P L d (signatureLimit - (L.length + 1)) budget o1 with hcanonR
  -- each outcome of the signing call
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
        have hpot := sign_point tg initial model parameter data wbar b0 Fail Qtot m hparse (hfail m) hfair.le_one hb0
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
  -- the payments of the whole run cover the continuations
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
    _ ≤ _ := add_le_add (sign_expect tg initial model parameter data wbar b0 Fail m hparse hfair hb0
          digestAttemptLimit budget s P L d hP hcount) (mul_le_mul_left' hflag _)

end SignGood

end LeanSphincs.Security.ForsPotential
