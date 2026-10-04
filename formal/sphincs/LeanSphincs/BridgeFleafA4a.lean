import LeanSphincs.BridgeFleafGame
import LeanSphincs.BridgeFleafA3
import LeanSphincs.BridgeContactBound

/-! **A4a paid per FORS leaf query.** The potential of `BridgeContactA` charges, on every unit of
budget, `2^-128` times the whole reveal rate of a future contact. Contacts arise only at FORS leaf
queries, so the signature part of that rate, `n 2^-b 2^-10` (`n` the remaining signatures), is
paid instead by `2^-128 N 2^-b 2^-10` at every FORS leaf query of the trace. The coin part
`wbar (#coins + y landing)` of a future contact cannot be paid that way: the number of cached
landed pairs at the time of a FORS leaf query is not bounded by `y landing` along a run, only in
expectation, so it stays a budget term. The potential

`Ψ = #revealed contacts + #unrevealed contacts · n 2^-b 2^-10 +
  (#unrevealed contacts + y 2^-128) · wbar (#coins + y landing)`

pays the event up to `2^-128 N 2^-b 2^-10` per FORS leaf query, and starts at
`(q 2^-128) (q wbar landing)`. -/

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

variable (parameter : PublicParameter) (K : HiddenReveal.Knowledge Coordinate) (wbar : ℝ≥0∞)

/-- The signature part of the reveal rate of one unrevealed contact. -/
noncomputable def sigRisk (L : QueryLog SigningSpec) : ℝ≥0∞ :=
  ((signatureLimit - L.length : ℕ) : ℝ≥0∞) * matchRate

/-- The coin part of the reveal rate of one unrevealed contact: the cached landed pairs of messages
not yet signed, and the ones of the remaining budget. -/
noncomputable def coinRisk (P : List Pair) (L : QueryLog SigningSpec) (budget : ℕ) : ℝ≥0∞ :=
  wbar * coinCount P L + budget * (wbar * landing)

/-- **The potential of A4a with a payment per FORS leaf query.** -/
noncomputable def psiAF : Potential := fun s P L _ R budget =>
  if signatureLimit < L.length then 0
  else (revealedContacts parameter K s R).card + (openContacts parameter K s R).card * sigRisk L +
    ((openContacts parameter K s R).card + budget * contactRate) * coinRisk wbar P L budget

end Defs

/-! ### The four steps -/

section Steps

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  (wbar : ℝ≥0∞) (Qtot : ℕ) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- **A new pair.** -/
theorem psiAF_newPair (hparse : ∀ p call, model.parse (pblk parameter data p call) = none) :
    NewPairPays parameter data Qtot initial model (psiAF parameter K wbar) := by
  intro budget s P L d R hb hB p hp0
  have hp1 := hB.pinv.first p hp0
  have hc : ∀ a b, contacts parameter K (withPair parameter data s p a b) = contacts parameter K s :=
    fun a b => contacts_withPair parameter data K model hB.cinv hparse hp0 hp1 a b
  simp only [psiAF, revealedContacts, openContacts, hc]
  by_cases hL : signatureLimit < L.length
  · simp only [if_pos hL, pairE_const, le_refl]
  simp only [if_neg hL]
  set Rv : ℝ≥0∞ := (((contacts parameter K s).filter fun g => g.1 ∈ R).card : ℝ≥0∞)
  set U : ℝ≥0∞ := (((contacts parameter K s).filter fun g => g.1 ∉ R).card : ℝ≥0∞)
  set S0 : ℝ≥0∞ := Rv + U * sigRisk L with hS0
  set A0 : ℝ≥0∞ := wbar * coinCount P L with hA0
  have hpt : ∀ u0 u1 : HashOutput, S0 + (U + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) *
      coinRisk wbar (addPair parameter P p u0) L (budget - 1) =
      S0 + (U + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) * (A0 + ((budget - 1 : ℕ) : ℝ≥0∞) * (wbar * landing)) +
        (U + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) * wbar *
          (if Landed parameter (blockIndex u0) then (if MsgFresh L p then 1 else 0) else 0) := by
    intro u0 u1
    simp only [coinRisk, coinCount_addPair, A0]
    ring
  refine le_trans (le_of_eq (congrArg pairE (funext fun u0 => funext fun u1 => hpt u0 u1))) ?_
  rw [pairE_add, pairE_add, pairE_const, pairE_const, pairE_const_mul]
  have hland : pairE (fun u0 _ => if Landed parameter (blockIndex u0) then (if MsgFresh L p then (1 : ℝ≥0∞) else 0)
      else 0) ≤ landing := by
    have h := pairE_landed parameter (fun _ => if MsgFresh L p then (1 : ℝ≥0∞) else 0) 0
    simp only [mul_zero, add_zero] at h
    have h' : pairE (fun u0 u1 => if Landed parameter (blockIndex u0) then
        (fun _ : View => if MsgFresh L p then (1 : ℝ≥0∞) else 0) (viewOf u0 u1) else 0) ≤ landing := by
      rw [h, freshAvg_const _ Finset.univ_nonempty]
      split_ifs <;> simp
    simpa using h'
  have hbud : ((budget - 1 : ℕ) : ℝ≥0∞) + 1 = budget := by exact_mod_cast Nat.sub_add_cancel hb
  calc S0 + (U + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) * (A0 + ((budget - 1 : ℕ) : ℝ≥0∞) * (wbar * landing)) +
        (U + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) * wbar *
          pairE (fun u0 _ => if Landed parameter (blockIndex u0) then (if MsgFresh L p then 1 else 0) else 0)
      ≤ S0 + (U + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) * (A0 + ((budget - 1 : ℕ) : ℝ≥0∞) * (wbar * landing)) +
        (U + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) * wbar * landing := by gcongr
    _ = S0 + (U + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) *
          (A0 + (((budget - 1 : ℕ) : ℝ≥0∞) + 1) * (wbar * landing)) := by ring
    _ ≤ S0 + (U + (budget : ℝ≥0∞) * contactRate) * (A0 + (budget : ℝ≥0∞) * (wbar * landing)) := by
        rw [hbud]
        gcongr
        exact Nat.sub_le budget 1
    _ = _ := by simp only [coinRisk, A0, S0]

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
      (contactRate * (signatureLimit * matchRate)) (psiAF parameter K wbar) := by
  intro budget s P L d R hb hB x hnew
  simp only [psiAF]
  by_cases hL : signatureLimit < L.length
  · simp only [if_pos hL, mul_zero, tsum_zero, zero_le]
  simp only [if_neg hL]
  set Rv : ℝ≥0∞ := ((revealedContacts parameter K s R).card : ℝ≥0∞) with hRv
  set U : ℝ≥0∞ := ((openContacts parameter K s R).card : ℝ≥0∞) with hU
  set σ := sigRisk L with hσ
  set ρc := coinRisk wbar P L budget with hρc
  set f : ℝ≥0∞ := if IsFleafIn parameter x then 1 else 0 with hf
  set Nw : HashOutput × State → ℝ≥0∞ := fun r =>
    ((contacts parameter K r.2 \ contacts parameter K s).card : ℝ≥0∞) with hNw
  have hpt : ∀ r ∈ support (ordinaryStep model x s.known s),
      ((revealedContacts parameter K r.2 R).card : ℝ≥0∞) + ((openContacts parameter K r.2 R).card : ℝ≥0∞) * σ +
          (((openContacts parameter K r.2 R).card : ℝ≥0∞) + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) *
            coinRisk wbar P L (budget - 1) ≤
        Rv + (U + Nw r) * σ + (U + Nw r + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) * ρc := by
    intro r hr
    obtain ⟨_, hsub, hnew'⟩ := ordinary_contacts (K := K) hrows x s hB.cinv r hr
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
    have hρ' : coinRisk wbar P L (budget - 1) ≤ ρc := by
      simp only [hρc, coinRisk]
      gcongr
      exact_mod_cast Nat.sub_le budget 1
    rw [hRv']
    gcongr
  have hmean := newContacts_mean parameter K model hrows x s hB.cinv
  have hmass : ∑' r, Pr[= r | ordinaryStep model x s.known s] = 1 := by simp
  have hf1 : f ≤ 1 := by rw [hf]; split_ifs <;> simp
  have hσN : σ ≤ (signatureLimit : ℝ≥0∞) * matchRate := by
    rw [hσ, sigRisk]
    gcongr
    exact_mod_cast Nat.sub_le _ _
  have hbud : ((budget - 1 : ℕ) : ℝ≥0∞) + 1 = budget := by exact_mod_cast Nat.sub_add_cancel hb
  calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        (Rv + (U + Nw r) * σ + (U + Nw r + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) * ρc) := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support (ordinaryStep model x s.known s)
        · exact mul_le_mul_right (hpt r hr) _
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = (∑' r, Pr[= r | ordinaryStep model x s.known s]) * Rv +
          ((∑' r, Pr[= r | ordinaryStep model x s.known s]) * U +
            ∑' r, Pr[= r | ordinaryStep model x s.known s] * Nw r) * σ +
          ((∑' r, Pr[= r | ordinaryStep model x s.known s]) * U +
            ∑' r, Pr[= r | ordinaryStep model x s.known s] * Nw r +
            (∑' r, Pr[= r | ordinaryStep model x s.known s]) * (((budget - 1 : ℕ) : ℝ≥0∞) * contactRate)) * ρc := by
        simp only [add_mul, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, ← mul_assoc]
    _ ≤ 1 * Rv + (1 * U + contactRate * f) * σ +
          (1 * U + contactRate * f + 1 * (((budget - 1 : ℕ) : ℝ≥0∞) * contactRate)) * ρc := by
        rw [hmass]
        gcongr
    _ = Rv + U * σ + (U + (contactRate * f + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate)) * ρc +
          contactRate * f * σ := by ring
    _ ≤ Rv + U * σ + (U + (budget : ℝ≥0∞) * contactRate) * ρc +
          contactRate * ((signatureLimit : ℝ≥0∞) * matchRate) * f := by
        gcongr ?_ + ?_
        · gcongr
          calc contactRate * f + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate
              ≤ contactRate * 1 + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate := by gcongr
            _ = (((budget - 1 : ℕ) : ℝ≥0∞) + 1) * contactRate := by ring
            _ = _ := by rw [hbud]
        · calc contactRate * f * σ = contactRate * σ * f := by ring
            _ ≤ _ := by gcongr

/-- **A signing call** on a fresh message. -/
theorem psiAF_sign (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hrows : FtsRows parameter model) {Cmax : ℕ} (hfair : Fair wbar Cmax) (hQ : Qtot + digestAttemptLimit ≤ Cmax) :
    SignPays parameter data Qtot tg initial model (psiAF parameter K wbar) := by
  intro budget s P L d R hB m hm
  have hcount : cachedCount parameter data m s + digestAttemptLimit ≤ Cmax := by
    have := hB.count m; omega
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
  set Pm : ℝ≥0∞ := ((P.filter fun q => decide (q.1 = m)).length : ℝ≥0∞) with hPm
  set cc' : ℝ≥0∞ := ((P.filter fun q => decide (MsgFresh L q ∧ q.1 ≠ m)).length : ℝ≥0∞) with hcc'
  set n := signatureLimit - (L.length + 1) with hn
  have hn1 : signatureLimit - L.length = n + 1 := by omega
  set ρ'' : ℝ≥0∞ := wbar * cc' + budget * (wbar * landing) with hρ''
  have hcoin : coinRisk wbar P L budget = wbar * Pm + ρ'' := by
    simp only [coinRisk, hρ'', coinCount_split P L m hm, hPm, hcc']
    push_cast
    ring
  have hsig : sigRisk L = (n : ℝ≥0∞) * matchRate + matchRate := by
    simp only [sigRisk, hn1]
    push_cast
    ring
  -- the reveal indicator of the open contacts
  set X : Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun o1 =>
    ∑ g ∈ openContacts parameter K s R, (if o1.1.1.isSome ∧ g.1 ∈ o1.1.2.1 then 1 else 0) with hX
  have hpt : ∀ o1 ∈ support (interp tg initial model sign budget s),
      o1.1.1.elim 0 (fun r => psiAF parameter K wbar o1.2 (newPairs parameter data m s o1.2 ++ P) (L ++ [⟨m, r⟩])
        (discAfter parameter data m s d o1) (R ++ o1.1.2.1) (budget - traceCost o1.1.2.2.1)) ≤
      Rv + X o1 + (U * ((n : ℝ≥0∞) * matchRate) + (U + (budget : ℝ≥0∞) * contactRate) * ρ'') := by
    intro o1 ho1
    cases hres : o1.1.1 with
    | none => exact bot_le
    | some r =>
        simp only [Option.elim, psiAF]
        split_ifs with hgate
        · exact bot_le
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
        have hρ' : coinRisk wbar (newPairs parameter data m s o1.2 ++ P) (L ++ [⟨m, r⟩])
            (budget - traceCost o1.1.2.2.1) ≤ ρ'' := by
          simp only [coinRisk, coinCount_after, hρ'', hcc']
          gcongr
          exact_mod_cast Nat.sub_le budget _
        have hbud : ((budget - traceCost o1.1.2.2.1 : ℕ) : ℝ≥0∞) ≤ budget := by
          exact_mod_cast Nat.sub_le budget _
        rw [hσ']
        calc _ ≤ (Rv + X o1) + U * ((n : ℝ≥0∞) * matchRate) + (U + (budget : ℝ≥0∞) * contactRate) * ρ'' := by
              gcongr
          _ = _ := by ring
  -- the expected reveals of the open contacts
  have hXe : ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * X o1 ≤ U * (matchRate + wbar * Pm) := by
    simp only [hX, Finset.mul_sum]
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    calc ∑ g ∈ openContacts parameter K s R, ∑' o1, Pr[= o1 | interp tg initial model sign budget s] *
          (if o1.1.1.isSome ∧ g.1 ∈ o1.1.2.1 then 1 else 0)
        ≤ ∑ _g ∈ openContacts parameter K s R, (matchRate + wbar * Pm) := by
          refine Finset.sum_le_sum fun g hg => ?_
          obtain ⟨i, t, l, ans, hgi, _, _⟩ := (Finset.mem_filter.1 (Finset.mem_filter.1 hg).1).2
          rw [hgi]
          exact reveal_le tg initial model parameter data m hparse hB.pinv hB.prep hfair digestAttemptLimit budget
            hcount i t l
      _ = U * (matchRate + wbar * Pm) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hmass : ∑' o1, Pr[= o1 | interp tg initial model sign budget s] ≤ 1 := tsum_probOutput_le_one
  simp only [psiAF, if_neg hL', revealedContacts, openContacts]
  calc _ ≤ ∑' o1, Pr[= o1 | interp tg initial model sign budget s] *
        (Rv + X o1 + (U * ((n : ℝ≥0∞) * matchRate) + (U + (budget : ℝ≥0∞) * contactRate) * ρ'')) := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support (interp tg initial model sign budget s)
        · exact mul_le_mul_right (hpt o1 ho1) _
        · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
    _ = (∑' o1, Pr[= o1 | interp tg initial model sign budget s]) * Rv +
          ∑' o1, Pr[= o1 | interp tg initial model sign budget s] * X o1 +
          (∑' o1, Pr[= o1 | interp tg initial model sign budget s]) *
            (U * ((n : ℝ≥0∞) * matchRate) + (U + (budget : ℝ≥0∞) * contactRate) * ρ'') := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ 1 * Rv + U * (matchRate + wbar * Pm) +
          1 * (U * ((n : ℝ≥0∞) * matchRate) + (U + (budget : ℝ≥0∞) * contactRate) * ρ'') := by
        gcongr
    _ = Rv + U * ((n : ℝ≥0∞) * matchRate + matchRate) + (U * (wbar * Pm) +
          (U + (budget : ℝ≥0∞) * contactRate) * ρ'') := by ring
    _ ≤ Rv + U * ((n : ℝ≥0∞) * matchRate + matchRate) + ((U + (budget : ℝ≥0∞) * contactRate) * (wbar * Pm) +
          (U + (budget : ℝ≥0∞) * contactRate) * ρ'') := by
        gcongr
        exact le_self_add
    _ = Rv + U * sigRisk L + (U + (budget : ℝ≥0∞) * contactRate) * coinRisk wbar P L budget := by
        rw [hsig, hcoin]
        ring

/-- **The end of the game.** -/
theorem psiAF_final : FinalPays parameter data Qtot initial model (psiAF parameter K wbar) (finalA parameter K) := by
  intro budget s P L d R hB forgery verified
  simp only [finalA, Option.elim, psiAF]
  split_ifs with hcase hL
  · exact absurd hcase.1 (by simp [SigningTranscript.Valid]; omega)
  · obtain ⟨_, i, t, l, hgr, hR⟩ := hcase
    obtain ⟨secret, hmem⟩ := mem_contacts_of_GR parameter K hgr
    have h1 : (1 : ℝ≥0∞) ≤ (revealedContacts parameter K s R).card := by
      exact_mod_cast Finset.card_pos.2 ⟨_, Finset.mem_filter.2 ⟨hmem, hR⟩⟩
    exact le_trans h1 (le_trans le_self_add le_self_add)
  · exact bot_le
  · exact bot_le

end Steps

/-! ### The bound -/

section Bound

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  (wbar : ℝ≥0∞) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- **Theorem (a), paid per FORS leaf query.** In the lazy run of the rest of the game of an
adversary that never repeats a message, the game finishes with a valid transcript and a contact
made at an unknown secret is revealed with probability at most
`x (total wbar landing) + 2^-128 N 2^-b 2^-10 E[#FORS leaf queries]`, `x = total 2^-128`. -/
theorem a4a_boundF (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hclean : ∀ p call, initial (pblk parameter data p call) = none)
    (hrows : FtsRows parameter model)
    (hcleanF : ∀ x a v i t l, model.parse x = some (a, v) → model.incoming a = .ftsSecret i t l → initial x = none)
    (total : ℕ) (hfair : Fair wbar (total + digestAttemptLimit))
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M []) (known : Knowledge Coordinate) :
    Pr[A4aRun parameter K | interp tg initial model (advProg parameter data M []) total
        (DebtState.start initial known)] ≤
      ((total : ℝ≥0∞) * contactRate) * (total * (wbar * landing)) +
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
    (psiAF_newPair parameter data K wbar total initial model hparse)
    (psiAF_ordinary parameter data K wbar total initial model hrows)
    (psiAF_sign parameter data K wbar total tg initial model hparse hrows hfair le_rfl)
    (psiAF_final parameter data K wbar total initial model) M hnr known
  have hstart : psiAF parameter K wbar (DebtState.start initial known) [] [] 0 [] total =
      ((total : ℝ≥0∞) * contactRate) * (total * (wbar * landing)) := by
    have hc : contacts parameter K (DebtState.start initial known) = ∅ := by
      unfold contacts
      rfl
    simp only [psiAF, revealedContacts, openContacts, hc, coinRisk, coinCount]
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
    (K : HiddenReveal.Knowledge Coordinate) (wbar : ℝ≥0∞) (hfair : Fair wbar (q - keygenCost + digestAttemptLimit))
    (known : Knowledge Coordinate) :
    Pr[A4aRun (truncateHash parameterOutput) K | interp tg prepared.2 (sampleModel parameterOutput highs)
        (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
          (internalize adversary)) q (DebtState.start prepared.2 known)] ≤
      (((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) * ((q - keygenCost : ℕ) * (wbar * landing)) +
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
    have h := a4a_boundF param data K wbar tg prepared.2 model
      (sampleModel_parse_blk parameterOutput highs data)
      (fun p call => hmsg _ (msgInput_digestInput param data.root p.1 p.2 call))
      (fun p call => prepared_clean parameterOutput fixed highs remaining prepared hprepared _
        (msgInput_digestInput param data.root p.1 p.2 call))
      (ftsRows_sampleModel parameterOutput highs)
      (prepared_cleanRows parameterOutput fixed highs remaining prepared hprepared) (q - keygenCost) hfair
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

/-- **Theorem (a) paid per FORS leaf query, at the fair share.** -/
theorem a4a_bound_fairF (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (hq : 2 * (q - keygenCost) ≤ 2 ^ 128)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) (hmsg : ∀ x, IsMsgInput x → tg.kind x = .none)
    (K : HiddenReveal.Knowledge Coordinate) (known : Knowledge Coordinate) :
    Pr[A4aRun (truncateHash parameterOutput) K | interp tg prepared.2 (sampleModel parameterOutput highs)
        (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
          (internalize adversary)) q (DebtState.start prepared.2 known)] ≤
      (((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) *
          ((q - keygenCost : ℕ) * (((2 ^ 128 - ((q - keygenCost) + 2 ^ 32) : ℕ) : ℝ≥0∞))⁻¹) +
        (contactRate * (signatureLimit * matchRate)) *
          ∑' out, Pr[= out | interp tg prepared.2 (sampleModel parameterOutput highs)
              (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
                (internalize adversary)) q (DebtState.start prepared.2 known)] *
            (fleafCount (IsFleafIn (truncateHash parameterOutput)) out.1.2.2.1 : ℝ≥0∞) := by
  have h := a4a_bound_gameF adversary hnr q parameterOutput fixed highs remaining prepared hprepared tg hmsg K
    (H0.wbarOf (q - keygenCost)) (fair_wbarOf _ hq) known
  rwa [wbarOf_mul_landing] at h

end Sample

end LeanSphincs.Security.ForsPotential
