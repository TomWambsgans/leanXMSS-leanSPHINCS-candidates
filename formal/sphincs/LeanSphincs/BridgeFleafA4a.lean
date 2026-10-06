import LeanSphincs.BridgeFleafGame
import LeanSphincs.BridgeFleafA3
import LeanSphincs.BridgeContactBound

/-! **A4a paid per FORS leaf query.** A contact (a FORS leaf query that hits an unknown secret,
probability `2^-128`) is revealed later by a signature with a fresh view (rate `n 2^-b 2^-10`, `n`
the remaining signatures, paid by `2^-128 N 2^-b 2^-10` at every FORS leaf query), or by a
signature that selects a cached landed digest pair. The second part is a budget term. With `A` the
selection mass of the known landed pairs of the unsigned messages (`poolMass`, the state function
on the card function) and `r = rate5 = (2 - landing) / 2^128` the mass one more digest query adds,

`Ψ = #revealed + #open · n 2^-b 2^-10 + #open · (A + y r) + 2^-128 · (y A + C(y, 2) r)`

is a supermartingale up to the payment: a unit of budget is spent either on a contact attempt
(worth `2^-128` times the mass still to come, `A + (y - 1) r`) or on a digest query (worth `r` per
open contact and per future contact attempt), not on both. It starts at `2^-128 · C(q, 2) · r`,
half of the product `(q 2^-128)(q r)`. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
open HiddenBridge

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### The potential -/

section Defs

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)

/-- The signature part of the reveal rate of one unrevealed contact. -/
noncomputable def sigRisk (L : QueryLog SigningSpec) : ℝ≥0∞ :=
  ((signatureLimit - L.length : ℕ) : ℝ≥0∞) * matchRate

/-- The selection mass of the known landed pairs of the messages not yet signed. -/
noncomputable def poolMass (s : State) (L : QueryLog SigningSpec) : ℝ≥0∞ :=
  stateFn parameter data s L (fun _ => False) cardFn 0

/-- The coin part of the reveal rate of one unrevealed contact: the mass of the known landed pairs
and the mass the remaining budget can add. -/
noncomputable def coinRisk (s : State) (L : QueryLog SigningSpec) (budget : ℕ) : ℝ≥0∞ :=
  poolMass parameter data s L + budget * rate5

/-- **The potential of A4a with a payment per FORS leaf query.** -/
noncomputable def psiAF : Potential := fun s _ L _ R budget =>
  if signatureLimit < L.length then 0
  else (revealedContacts parameter K s R).card + (openContacts parameter K s R).card * sigRisk L +
    (openContacts parameter K s R).card * coinRisk parameter data s L budget +
    contactRate * (budget * poolMass parameter data s L + (budget.choose 2 : ℕ) * rate5)

end Defs

/-! ### The pool mass -/

section Mass

variable {parameter : PublicParameter} {data : PublicData}

theorem stateFn_card (s : State) (L : QueryLog SigningSpec) (D : Multiset View) :
    stateFn parameter data s L (fun _ => False) cardFn D =
      stateFn parameter data s L (fun _ => False) cardFn 0 + cardFn D := by
  have hR := rep_stateFn (parameter := parameter) (data := data) s L (fun _ => False)
  have h1 := hR.map_translate cardFn D 0
  rw [zero_add] at h1
  have h2 : (fun D' : Multiset View => cardFn (D' + D)) = fun D' => cardFn D' + (fun _ => cardFn D) D' := by
    funext D'
    unfold cardFn
    rw [Multiset.card_add]
    push_cast
    rfl
  rw [← h1, h2, hR.map_add]
  congr 1
  have h3 := foldG_const (parameter := parameter) (data := data) s (fun _ => False) (cardFn D) (freshMsgs L)
  exact congrFun h3 0

theorem poolMass_newPair (s : State) (L : QueryLog SigningSpec) (p : Pair)
    (hp0 : s.cache (pblk parameter data p 0) = none) :
    pairE (fun u0 u1 => poolMass parameter data (withPair parameter data s p u0 u1) L) ≤
      poolMass parameter data s L + rate5 := by
  have h := stateFn_newPair cardFn_props s L (fun _ => False) p hp0 (fun h => h) (0 : Multiset View)
  have havg : avgT (stateFn parameter data s L (fun _ => False) cardFn) 0 =
      stateFn parameter data s L (fun _ => False) cardFn 0 + 1 := by
    unfold avgT
    have : (fun v : View => stateFn parameter data s L (fun _ => False) cardFn (0 + {v})) =
        fun _ => stateFn parameter data s L (fun _ => False) cardFn 0 + 1 := by
      funext v
      rw [stateFn_card s L (0 + {v})]
      congr 1
      simp [cardFn]
    rw [this, freshAvg_const _ Finset.univ_nonempty]
  rw [havg] at h
  refine le_trans h (le_of_eq ?_)
  unfold poolMass
  rw [mul_add, ← add_assoc, ← add_mul, tsub_add_cancel_of_le rate5_le_one, one_mul, mul_one]

theorem poolMass_split (s : State) (L : QueryLog SigningSpec) (m : Message) (hm : ∀ entry ∈ L, entry.1 ≠ m) :
    poolMass parameter data s L =
      grpM parameter data m s (fun _ => False) cardFn 0 + poolMass parameter data s (L ++ [⟨m, none⟩]) := by
  unfold poolMass
  rw [stateFn_split s L (fun _ => False) cardFn m hm none]
  set c0 := stateFn parameter data s (L ++ [⟨m, none⟩]) (fun _ => False) cardFn 0 with hc0
  have hfun : stateFn parameter data s (L ++ [⟨m, none⟩]) (fun _ => False) cardFn = fun D => cardFn D + c0 := by
    funext D
    rw [stateFn_card s _ D, add_comm]
  have hadd := (rep_grpM (parameter := parameter) (data := data) m s (fun _ => False)).map_add cardFn (fun _ => c0) 0
  beta_reduce at hadd
  have hc : grpM parameter data m s (fun _ => False) (fun _ => c0) 0 = c0 := by
    unfold grpM
    exact Walk.grp_const (e := succR) (L := digestAttemptLimit) landing_le_one (stat parameter data m s)
      (exB (fun _ => False) m) c0 0
  rw [hfun, hadd, hc]

theorem poolMass_congr {s s' : State} (L : QueryLog SigningSpec)
    (h : ∀ m, stat parameter data m s' = stat parameter data m s) :
    poolMass parameter data s' L = poolMass parameter data s L := by
  unfold poolMass
  rw [stateFn_congr L _ _ fun m _ => h m]

theorem poolMass_clean (s : State) (L : QueryLog SigningSpec)
    (hclean : ∀ m ρ, s.cache (blk parameter data m ρ 0) = none) : poolMass parameter data s L = 0 := by
  unfold poolMass
  rw [stateFn_clean s L _ hclean]
  exact cardFn_zero

theorem choose_two_succ (j : ℕ) : ((j + 1).choose 2 : ℝ≥0∞) = j + (j.choose 2 : ℕ) := by
  have : (j + 1).choose 2 = j + j.choose 2 := by
    rw [Nat.choose_succ_succ j 1, Nat.choose_one_right]
  rw [this]
  push_cast
  rfl

end Mass

/-! ### The four steps -/

section Steps

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  (Qtot : ℕ) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- **A new pair.** -/
theorem psiAF_newPair (hparse : ∀ p call, model.parse (pblk parameter data p call) = none) :
    NewPairPays parameter data Qtot initial model (psiAF parameter data K) := by
  intro budget s P L d R hb hB p hp0
  have hp1 := hB.pinv.first p hp0
  have hc : ∀ a b, contacts parameter K (withPair parameter data s p a b) = contacts parameter K s :=
    fun a b => contacts_withPair parameter data K model hB.cinv hparse hp0 hp1 a b
  simp only [psiAF, revealedContacts, openContacts, hc]
  by_cases hL : signatureLimit < L.length
  · simp only [if_pos hL, pairE_const, le_refl]
  simp only [if_neg hL]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hb
  simp only [Nat.add_sub_cancel]
  set Rv : ℝ≥0∞ := (((contacts parameter K s).filter fun g => g.1 ∈ R).card : ℝ≥0∞)
  set U : ℝ≥0∞ := (((contacts parameter K s).filter fun g => g.1 ∉ R).card : ℝ≥0∞)
  set S0 : ℝ≥0∞ := Rv + U * sigRisk L with hS0
  set A0 : ℝ≥0∞ := poolMass parameter data s L with hA0
  set c2 : ℝ≥0∞ := ((j.choose 2 : ℕ) : ℝ≥0∞) with hc2
  have hpt : ∀ u0 u1 : HashOutput, S0 + U * coinRisk parameter data (withPair parameter data s p u0 u1) L j +
      contactRate * ((j : ℝ≥0∞) * poolMass parameter data (withPair parameter data s p u0 u1) L + c2 * rate5) =
      (S0 + U * ((j : ℝ≥0∞) * rate5) + contactRate * (c2 * rate5)) +
        (U + contactRate * j) * poolMass parameter data (withPair parameter data s p u0 u1) L := by
    intro u0 u1
    simp only [coinRisk]
    ring
  refine le_trans (le_of_eq (congrArg pairE (funext fun u0 => funext fun u1 => hpt u0 u1))) ?_
  rw [pairE_add, pairE_const, pairE_const_mul]
  have hmass := poolMass_newPair (parameter := parameter) (data := data) s L p hp0
  rw [choose_two_succ]
  simp only [coinRisk]
  push_cast
  calc (S0 + U * ((j : ℝ≥0∞) * rate5) + contactRate * (c2 * rate5)) +
        (U + contactRate * j) * pairE (fun u0 u1 => poolMass parameter data (withPair parameter data s p u0 u1) L)
      ≤ (S0 + U * ((j : ℝ≥0∞) * rate5) + contactRate * (c2 * rate5)) + (U + contactRate * j) * (A0 + rate5) := by
        gcongr
    _ = S0 + U * (A0 + ((j : ℝ≥0∞) + 1) * rate5) + contactRate * ((j : ℝ≥0∞) * A0 + ((j : ℝ≥0∞) + c2) * rate5) := by
        ring
    _ ≤ S0 + U * (A0 + ((j : ℝ≥0∞) + 1) * rate5) +
          contactRate * (((j : ℝ≥0∞) + 1) * A0 + ((j : ℝ≥0∞) + c2) * rate5) := by
        gcongr
        exact le_self_add

/-- New contacts appear only at FORS leaf queries, `2^-128` of them on average. -/
theorem newContacts_mean (hrows : FtsRows parameter model) (x : HashInput) (s : State)
    (hinv : CInv parameter model s) :
    ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        ((contacts parameter K r.2 \ contacts parameter K s).card : ℝ≥0∞) ≤
      contactRate * (if IsFleafIn parameter x then 1 else 0) := by
  by_cases hF : IsFleafIn parameter x
  · rw [if_pos hF, mul_one]
    exact ordinary_contacts_mean (K := K) hrows x s hinv
  · rw [if_neg hF, mul_zero]
    refine le_of_eq (ENNReal.tsum_eq_zero.2 fun r => ?_)
    by_cases hr : r ∈ support (ordinaryStep model x s.known s)
    · have hnew := (ordinary_contacts (K := K) hrows x s hinv r hr).2.2
      have hempty : contacts parameter K r.2 \ contacts parameter K s = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun g hg => ?_
        obtain ⟨hg1, hg2⟩ := Finset.mem_sdiff.1 hg
        obtain ⟨a, i, t, l, hp, hi, hg', -⟩ := hnew g hg1 hg2
        exact hF ⟨i, t, l, g.2, hrows x a g.2 i t l hp (hi.trans hg')⟩
      rw [hempty]
      simp
    · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul]

/-- **Any other ordinary query**, paying `2^-128 N 2^-b 2^-10` at a FORS leaf input. -/
theorem psiAF_ordinary (hrows : FtsRows parameter model) :
    OrdinaryPaysP parameter data Qtot initial model (IsFleafIn parameter)
      (contactRate * (signatureLimit * matchRate)) (psiAF parameter data K) := by
  intro budget s P L d R hb hB x hnew
  simp only [psiAF]
  by_cases hL : signatureLimit < L.length
  · simp only [if_pos hL, mul_zero, tsum_zero, zero_le]
  simp only [if_neg hL]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hb
  simp only [Nat.add_sub_cancel]
  set Rv : ℝ≥0∞ := ((revealedContacts parameter K s R).card : ℝ≥0∞) with hRv
  set U : ℝ≥0∞ := ((openContacts parameter K s R).card : ℝ≥0∞) with hU
  set σ := sigRisk L with hσ
  set A0 : ℝ≥0∞ := poolMass parameter data s L with hA0
  set c2 : ℝ≥0∞ := ((j.choose 2 : ℕ) : ℝ≥0∞) with hc2
  set f : ℝ≥0∞ := if IsFleafIn parameter x then 1 else 0 with hf
  set Nw : HashOutput × State → ℝ≥0∞ := fun r =>
    ((contacts parameter K r.2 \ contacts parameter K s).card : ℝ≥0∞) with hNw
  have hpt : ∀ r ∈ support (ordinaryStep model x s.known s),
      ((revealedContacts parameter K r.2 R).card : ℝ≥0∞) + ((openContacts parameter K r.2 R).card : ℝ≥0∞) * σ +
          ((openContacts parameter K r.2 R).card : ℝ≥0∞) * coinRisk parameter data r.2 L j +
          contactRate * ((j : ℝ≥0∞) * poolMass parameter data r.2 L + c2 * rate5) ≤
        Rv + (U + Nw r) * σ + (U + Nw r) * (A0 + (j : ℝ≥0∞) * rate5) +
          contactRate * ((j : ℝ≥0∞) * A0 + c2 * rate5) := by
    intro r hr
    obtain ⟨_, hsub, hnew'⟩ := ordinary_contacts (K := K) hrows x s hB.cinv r hr
    have hmass : poolMass parameter data r.2 L = A0 :=
      poolMass_congr L (stat_same (ordinaryStep_extends model x s r hr) (ordinaryStep_cache_ne model x s r hr)
        hnew hB.pinv)
    have hRv' : revealedContacts parameter K r.2 R = revealedContacts parameter K s R := by
      unfold revealedContacts
      ext g
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hg, hgR⟩
        refine ⟨?_, hgR⟩
        by_contra hn
        obtain ⟨_, _, _, _, _, _, _, hk, _, _⟩ := hnew' g hg hn
        exact hB.rinv g.1 hgR hk
      · rintro ⟨hg, hgR⟩
        exact ⟨hsub hg, hgR⟩
    have hU' : ((openContacts parameter K r.2 R).card : ℝ≥0∞) ≤ U + Nw r := by
      have hsub' : openContacts parameter K r.2 R ⊆
          openContacts parameter K s R ∪ (contacts parameter K r.2 \ contacts parameter K s) := by
        intro g hg
        obtain ⟨hg1, hg2⟩ := Finset.mem_filter.1 hg
        by_cases hgs : g ∈ contacts parameter K s
        · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hgs, hg2⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hg1, hgs⟩)
      have hnat := le_trans (Finset.card_le_card hsub') (Finset.card_union_le _ _)
      rw [hU]
      simp only [hNw]
      exact_mod_cast hnat
    rw [hRv']
    simp only [coinRisk, hmass]
    gcongr
  have hmean := newContacts_mean parameter K model hrows x s hB.cinv
  have hmass : ∑' r, Pr[= r | ordinaryStep model x s.known s] = 1 := by simp
  have hf1 : f ≤ 1 := by rw [hf]; split_ifs <;> simp
  have hσN : σ ≤ (signatureLimit : ℝ≥0∞) * matchRate := by
    rw [hσ, sigRisk]
    gcongr
    exact_mod_cast Nat.sub_le _ _
  rw [choose_two_succ]
  simp only [coinRisk]
  push_cast
  calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        (Rv + (U + Nw r) * σ + (U + Nw r) * (A0 + (j : ℝ≥0∞) * rate5) +
          contactRate * ((j : ℝ≥0∞) * A0 + c2 * rate5)) := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support (ordinaryStep model x s.known s)
        · exact mul_le_mul_right (hpt r hr) _
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = (∑' r, Pr[= r | ordinaryStep model x s.known s]) *
          (Rv + U * σ + U * (A0 + (j : ℝ≥0∞) * rate5) + contactRate * ((j : ℝ≥0∞) * A0 + c2 * rate5)) +
          (∑' r, Pr[= r | ordinaryStep model x s.known s] * Nw r) * (σ + (A0 + (j : ℝ≥0∞) * rate5)) := by
        rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
        refine tsum_congr fun r => ?_
        ring
    _ ≤ 1 * (Rv + U * σ + U * (A0 + (j : ℝ≥0∞) * rate5) + contactRate * ((j : ℝ≥0∞) * A0 + c2 * rate5)) +
          (contactRate * f) * (σ + (A0 + (j : ℝ≥0∞) * rate5)) := by
        rw [hmass]
        gcongr
    _ ≤ (Rv + U * σ + U * (A0 + (j : ℝ≥0∞) * rate5) + contactRate * ((j : ℝ≥0∞) * A0 + c2 * rate5)) +
          (contactRate * f * σ + contactRate * (A0 + (j : ℝ≥0∞) * rate5)) := by
        refine add_le_add (le_of_eq (one_mul _)) ?_
        calc contactRate * f * (σ + (A0 + (j : ℝ≥0∞) * rate5))
            = contactRate * f * σ + contactRate * f * (A0 + (j : ℝ≥0∞) * rate5) := mul_add _ _ _
          _ ≤ contactRate * f * σ + contactRate * 1 * (A0 + (j : ℝ≥0∞) * rate5) := by gcongr
          _ = _ := by rw [mul_one]
    _ = Rv + U * σ + U * (A0 + (j : ℝ≥0∞) * rate5) +
          contactRate * (((j : ℝ≥0∞) + 1) * A0 + ((j : ℝ≥0∞) + c2) * rate5) + contactRate * σ * f := by ring
    _ ≤ Rv + U * σ + U * (A0 + ((j : ℝ≥0∞) + 1) * rate5) +
          contactRate * (((j : ℝ≥0∞) + 1) * A0 + ((j : ℝ≥0∞) + c2) * rate5) +
          contactRate * ((signatureLimit : ℝ≥0∞) * matchRate) * f := by
        gcongr
        exact le_self_add

/-- **A signing call** on a fresh message. -/
theorem psiAF_sign (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hrows : FtsRows parameter model) :
    SignPays parameter data Qtot tg initial model (psiAF parameter data K) := by
  intro budget s P L d R hB m hm
  set sign := signCostSourceLoop parameter data m digestAttemptLimit with hsign
  by_cases hL : signatureLimit ≤ L.length
  · refine le_of_eq_of_le (ENNReal.tsum_eq_zero.2 fun o1 => ?_) bot_le
    cases hres : o1.1.1 with
    | none => simp
    | some r =>
        simp only [Option.elim, psiAF]
        rw [if_pos (by simp only [List.length_append, List.length_singleton]; omega), mul_zero]
  have hL' : ¬signatureLimit < L.length := by omega
  set C := contacts parameter K s with hC
  set Rv : ℝ≥0∞ := ((revealedContacts parameter K s R).card : ℝ≥0∞) with hRv
  set U : ℝ≥0∞ := ((openContacts parameter K s R).card : ℝ≥0∞) with hU
  set G : ℝ≥0∞ := grpM parameter data m s (fun _ => False) cardFn 0 with hG
  set A1 : ℝ≥0∞ := poolMass parameter data s (L ++ [⟨m, none⟩]) with hA1
  set c2 : ℝ≥0∞ := ((budget.choose 2 : ℕ) : ℝ≥0∞) with hc2
  set n := signatureLimit - (L.length + 1) with hn
  have hn1 : signatureLimit - L.length = n + 1 := by omega
  have hsplit : poolMass parameter data s L = G + A1 := poolMass_split s L m hm
  have hsig : sigRisk L = (n : ℝ≥0∞) * matchRate + matchRate := by
    simp only [sigRisk, hn1]
    push_cast
    ring
  -- the reveal indicator of the open contacts
  set X : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    ∑ g ∈ openContacts parameter K s R, (if o1.1.1.isSome ∧ g.1 ∈ o1.1.2.1 then 1 else 0) with hX
  have hpt : ∀ o1 ∈ support (interp tg initial model sign budget s),
      o1.1.1.elim 0 (fun r => psiAF parameter data K o1.2 (newPairs parameter data m s o1.2 ++ P) (L ++ [⟨m, r⟩])
        (discAfter parameter data m s d o1) (R ++ o1.1.2.1) (budget - traceCost o1.1.2.2.1)) ≤
      Rv + X o1 + (U * ((n : ℝ≥0∞) * matchRate) + U * (A1 + (budget : ℝ≥0∞) * rate5) +
        contactRate * ((budget : ℝ≥0∞) * A1 + c2 * rate5)) := by
    intro o1 ho1
    cases hres : o1.1.1 with
    | none => exact bot_le
    | some r =>
        simp only [Option.elim, psiAF]
        split_ifs with hgate
        · exact bot_le
        have hother := other_message_kept tg initial model digestAttemptLimit budget s o1 ho1
        have hmassA : poolMass parameter data o1.2 (L ++ [⟨m, r⟩]) = A1 := by
          rw [hA1]
          unfold poolMass
          rw [stateFn_after L m r _ _ hother]
        have hcon := (interp_contacts_avoid (K := K) tg initial hrows _ (avoids_loopF parameter data m _)
          budget s hB.cinv o1 ho1).2
        simp only [revealedContacts, openContacts, hcon]
        have hRv' : (((C.filter fun g => g.1 ∈ R ++ o1.1.2.1).card : ℕ) : ℝ≥0∞) ≤ Rv + X o1 := by
          have hsub : C.filter (fun g => g.1 ∈ R ++ o1.1.2.1) ⊆
              C.filter (fun g => g.1 ∈ R) ∪ (openContacts parameter K s R).filter (fun g => g.1 ∈ o1.1.2.1) := by
            intro g hg
            obtain ⟨hgC, hgR⟩ := Finset.mem_filter.1 hg
            rcases List.mem_append.1 hgR with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hgC, h⟩)
            · by_cases hR : g.1 ∈ R
              · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hgC, hR⟩)
              · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hgC, hR⟩, h⟩)
          have hX' : (((openContacts parameter K s R).filter (fun g => g.1 ∈ o1.1.2.1)).card : ℝ≥0∞) = X o1 := by
            simp only [hX, hres, Option.isSome_some, true_and]
            rw [Finset.card_filter]
            push_cast
            rfl
          calc (((C.filter fun g => g.1 ∈ R ++ o1.1.2.1).card : ℕ) : ℝ≥0∞)
              ≤ (((C.filter fun g => g.1 ∈ R) ∪
                  (openContacts parameter K s R).filter (fun g => g.1 ∈ o1.1.2.1)).card : ℝ≥0∞) := by
                exact_mod_cast Finset.card_le_card hsub
            _ ≤ _ := by
                rw [← hX', hRv]
                exact_mod_cast Finset.card_union_le _ _
        have hU' : (((C.filter fun g => g.1 ∉ R ++ o1.1.2.1).card : ℕ) : ℝ≥0∞) ≤ U := by
          refine Nat.cast_le.mpr (Finset.card_le_card fun g hg => ?_)
          obtain ⟨hgC, hgR⟩ := Finset.mem_filter.1 hg
          exact Finset.mem_filter.2 ⟨hgC, fun h => hgR (List.mem_append_left _ h)⟩
        have hσ' : sigRisk (L ++ [⟨m, r⟩]) = (n : ℝ≥0∞) * matchRate := by
          simp only [sigRisk, List.length_append, List.length_singleton, hn]
        have hbud : ((budget - traceCost o1.1.2.2.1 : ℕ) : ℝ≥0∞) ≤ budget := by
          exact_mod_cast Nat.sub_le budget _
        have hch : (((budget - traceCost o1.1.2.2.1).choose 2 : ℕ) : ℝ≥0∞) ≤ c2 := by
          rw [hc2]
          exact_mod_cast Nat.choose_le_choose 2 (Nat.sub_le budget (traceCost o1.1.2.2.1))
        rw [hσ']
        simp only [coinRisk, hmassA]
        calc _ ≤ (Rv + X o1) + U * ((n : ℝ≥0∞) * matchRate) + U * (A1 + (budget : ℝ≥0∞) * rate5) +
              contactRate * ((budget : ℝ≥0∞) * A1 + c2 * rate5) := by
              gcongr
          _ = _ := by ring
  -- the expected reveals of the open contacts
  have hXe : ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * X o1 ≤ U * (matchRate + G) := by
    simp only [hX, Finset.mul_sum]
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    calc ∑ g ∈ openContacts parameter K s R, ∑' o1, Pr[= o1 | interp tg initial model sign budget s] *
          (if o1.1.1.isSome ∧ g.1 ∈ o1.1.2.1 then 1 else 0)
        ≤ ∑ _g ∈ openContacts parameter K s R, (matchRate + G) := by
          refine Finset.sum_le_sum fun g hg => ?_
          obtain ⟨i, t, l, ans, hgi, _, _⟩ := (Finset.mem_filter.1 (Finset.mem_filter.1 hg).1).2
          rw [hgi]
          exact reveal_le tg initial model parameter data m hparse hB.pinv hB.prep budget i t l
      _ = U * (matchRate + G) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hmass : ∑' o1, Pr[= o1 | interp tg initial model sign budget s] ≤ 1 := tsum_probOutput_le_one
  simp only [psiAF, if_neg hL', revealedContacts, openContacts]
  set Z : ℝ≥0∞ := U * ((n : ℝ≥0∞) * matchRate) + U * (A1 + (budget : ℝ≥0∞) * rate5) +
    contactRate * ((budget : ℝ≥0∞) * A1 + c2 * rate5) with hZ
  calc _ ≤ ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * (Rv + X o1 + Z) := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support (interp tg initial model sign budget s)
        · exact mul_le_mul_right (hpt o1 ho1) _
        · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
    _ = (∑' o1, Pr[= o1 | interp tg initial model sign budget s]) * Rv +
          ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * X o1 +
          (∑' o1, Pr[= o1 | interp tg initial model sign budget s]) * Z := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ 1 * Rv + U * (matchRate + G) + 1 * Z := by
        gcongr
    _ = Rv + U * ((n : ℝ≥0∞) * matchRate + matchRate) + U * (G + A1 + (budget : ℝ≥0∞) * rate5) +
          contactRate * ((budget : ℝ≥0∞) * A1 + c2 * rate5) := by
        rw [hZ]; ring
    _ ≤ Rv + U * ((n : ℝ≥0∞) * matchRate + matchRate) + U * (G + A1 + (budget : ℝ≥0∞) * rate5) +
          contactRate * ((budget : ℝ≥0∞) * (G + A1) + c2 * rate5) := by
        gcongr
        exact le_add_self
    _ = _ := by
        rw [hsig, hsplit]
        simp only [coinRisk, hsplit]
        rfl

/-- **The end of the game.** -/
theorem psiAF_final : FinalPays parameter data Qtot initial model (psiAF parameter data K) (finalA parameter K) := by
  intro budget s P L d R hB forgery verified
  simp only [finalA, Option.elim, psiAF]
  split_ifs with hcase hL
  · exact absurd hcase.1 (by simp [SigningTranscript.Valid]; omega)
  · obtain ⟨_, i, t, l, hgr, hR⟩ := hcase
    obtain ⟨secret, hmem⟩ := mem_contacts_of_GR parameter K hgr
    have h1 : (1 : ℝ≥0∞) ≤ (revealedContacts parameter K s R).card := by
      exact_mod_cast Finset.card_pos.2 ⟨_, Finset.mem_filter.2 ⟨hmem, hR⟩⟩
    exact le_trans h1 (le_trans le_self_add (le_trans le_self_add le_self_add))
  · exact bot_le
  · exact bot_le

end Steps

/-! ### The bound -/

section Bound

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- **Theorem (a), paid per FORS leaf query.** In the lazy run of the rest of the game of an
adversary that never repeats a message, the game finishes with a valid transcript and a contact
made at an unknown secret is revealed with probability at most
`2^-128 C(total, 2) rate5 + 2^-128 N 2^-b 2^-10 E[#FORS leaf queries]`. -/
theorem a4a_boundF (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hclean : ∀ p call, initial (pblk parameter data p call) = none)
    (hrows : FtsRows parameter model)
    (hcleanF : ∀ x a v i t l, model.parse x = some (a, v) → model.incoming a = .ftsSecret i t l → initial x = none)
    (total : ℕ)
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M []) (known : Knowledge Coordinate) :
    Pr[A4aRun parameter K | interp tg initial model (advProg parameter data M []) total
        (DebtState.start initial known)] ≤
      contactRate * ((total.choose 2 : ℕ) * rate5) +
        (contactRate * (signatureLimit * matchRate)) *
          expectedF tg initial model (IsFleafIn parameter) (advProg parameter data M []) total
            (DebtState.start initial known) := by
  have hFp : ∀ p call, ¬IsFleafIn parameter (pblk parameter data p call) := by
    rintro p call ⟨i, t, l, secret, h⟩
    exact PotentialA.msg_ne_fors (msgInput_digestInput parameter data.root p.1 p.2 call) h
  have h := final_le_startP parameter data tg initial model (IsFleafIn parameter)
    (contactRate * (signatureLimit * matchRate)) hparse hkind hrows hFp hclean hcleanF Finset.univ
    (fun _ _ _ _ _ _ _ _ _ => Finset.mem_univ _) total
    (G := finalA parameter K) (fun _ _ => rfl) (fun o R s x u hx => finalA_store parameter K o R s x u hx)
    (psiAF_newPair parameter data K total initial model hparse)
    (psiAF_ordinary parameter data K total initial model hrows)
    (psiAF_sign parameter data K total tg initial model hparse hrows)
    (psiAF_final parameter data K total initial model) M hnr known
  have hstart : psiAF parameter data K (DebtState.start initial known) [] [] 0 [] total =
      contactRate * ((total.choose 2 : ℕ) * rate5) := by
    have hc : contacts parameter K (DebtState.start initial known) = ∅ := by
      unfold contacts
      rfl
    have hm : poolMass parameter data (DebtState.start initial known) [] = 0 :=
      poolMass_clean _ _ fun m ρ => hclean (m, ρ) 0
    simp only [psiAF, revealedContacts, openContacts, hc, coinRisk, hm]
    simp
  rw [hstart] at h
  rw [probEvent_eq_tsum_ite]
  refine le_trans (ENNReal.tsum_le_tsum fun out => ?_) h
  split_ifs with hE
  · obtain ⟨outcome, hres, hvalid, ha⟩ := hE
    simp only [finalA, hres, Option.elim, if_pos (And.intro hvalid ha), mul_one, le_refl]
  · exact bot_le

end Bound

/-! ### One sample -/

section Sample

open Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- **Theorem (a) paid per FORS leaf query, one sample.** On the interpreted run of `costGameX` of an
adversary that never repeats a message, with `y = q - keygenCost`. The expected number of FORS leaf
queries is taken over the same run. -/
theorem a4a_bound_gameF (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) (hmsg : ∀ x, IsMsgInput x → tg.kind x = .none)
    (K : HiddenReveal.Knowledge Coordinate) (known : Knowledge Coordinate) :
    Pr[A4aRun (truncateHash parameterOutput) K | interp tg prepared.2 (sampleModel parameterOutput highs)
        (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
          (internalize adversary)) q (DebtState.start prepared.2 known)] ≤
      contactRate * (((q - keygenCost).choose 2 : ℕ) * rate5) +
        (contactRate * (signatureLimit * matchRate)) *
          ∑' out, Pr[= out | interp tg prepared.2 (sampleModel parameterOutput highs)
              (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
                (internalize adversary)) q (DebtState.start prepared.2 known)] *
            (fleafCount (IsFleafIn (truncateHash parameterOutput)) out.1.2.2.1 : ℝ≥0∞) := by
  set param := truncateHash parameterOutput with hparam
  set data := sampleData parameterOutput fixed highs remaining with hdata
  set model := sampleModel parameterOutput highs with hmodel
  set start : State := DebtState.start prepared.2 known with hstart
  by_cases hK : keygenCost ≤ q
  · have hrunEq : interp tg prepared.2 model (costGameX param data (internalize adversary)) q start =
        (fun out => ((out.1.1, out.1.2.1, Sum.inr keygenCost :: out.1.2.2.1, out.1.2.2.2), out.2)) <$>
          interp tg prepared.2 model (advProg param data ((internalize adversary).main ⟨data.root, param⟩) [])
            (q - keygenCost) start := by
      unfold costGameX
      rw [interp_tick_bind tg prepared.2 model _ _ q start hK, costRestX_eq]
    rw [hrunEq, probEvent_map, tsum_probOutput_map_mul]
    have h := a4a_boundF param data K tg prepared.2 model
      (sampleModel_parse_blk parameterOutput highs data)
      (fun p call => hmsg _ (msgInput_digestInput param data.root p.1 p.2 call))
      (fun p call => prepared_clean parameterOutput fixed highs remaining prepared hprepared _
        (msgInput_digestInput param data.root p.1 p.2 call))
      (ftsRows_sampleModel parameterOutput highs)
      (prepared_cleanRows parameterOutput fixed highs remaining prepared hprepared) (q - keygenCost)
      ((internalize adversary).main ⟨data.root, param⟩)
      (noRepeat_internalize_adversary adversary hnr ⟨data.root, param⟩) known
    refine le_trans (le_of_eq ?_) (le_trans h (le_of_eq ?_))
    · rfl
    · unfold expectedF
      congr 2
  · have hrunEq : interp tg prepared.2 model (costGameX param data (internalize adversary)) q start =
        pure ((none, [], [], []), start) := by
      unfold costGameX
      exact interp_tick_bind_abort tg prepared.2 model _ _ q start hK
    rw [hrunEq, probEvent_pure, if_neg (fun ⟨_, h, _⟩ => by cases h)]
    exact zero_le

end Sample

end LeanSphincs.Security.ForsPotential
