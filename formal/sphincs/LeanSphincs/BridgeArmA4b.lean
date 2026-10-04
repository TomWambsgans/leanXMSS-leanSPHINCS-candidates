import LeanSphincs.BridgeFleafA4a
import LeanSphincs.BridgeContactHalf

/-! **A4b armed by the near potential, paid per FORS leaf query.** The refined potential of
`BridgeContactHalf` charges a new contact `2^-128 · potNear`, all of it to the near forecast. A
contact only matters once, so its near potential can be capped at one: the potential

  `ψ(y) = C_F · min(1, potNear(y)) + κ 2^-128 · Σ_{j < y} potNear(j)`

still pays A4b at the end (a contact and a near-covered candidate make both factors at least one),
and `min(1, ·)` of a supermartingale is a supermartingale. A FORS leaf query now raises the first
term by at most `2^-128 min(1, potNear(y - 1))`, and for every `Q`

  `2^-128 min(1, Q) ≤ pay + κ 2^-128 Q`   once   `2^-128 ≤ pay + κ 2^-128`.

The top level of the sum pays `κ 2^-128 Q`, and `pay` is paid per FORS leaf query of the trace: on
the small-budget route it is the part `(ρ - 1 - x - N 2^-b 2^-10) 2^-128` of the linear
potential's slack that A4a leaves unused. With `κ = 2 - ρ + x + N 2^-b 2^-10` the near term of A4b
shrinks by the factor `κ`, and no further term is needed for contacts whose leaf becomes near
covered only later: their risk is carried by the capped factor. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal
open HiddenBridge

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false
attribute [local instance] Classical.propDecidable

variable [Params]

/-! ### Capped expectations -/

omit [Params] in
theorem pairE_min_le (F : HashOutput → HashOutput → ℝ≥0∞) :
    pairE (fun a b => min 1 (F a b)) ≤ min 1 (pairE F) :=
  le_min (le_trans (pairE_mono fun _ _ => min_le_left _ _) (le_of_eq (pairE_const 1)))
    (pairE_mono fun _ _ => min_le_right _ _)

omit [Params] in
theorem tsum_min_le {α : Type} (mx : ProbComp α) (X : α → ℝ≥0∞) :
    ∑' a, Pr[= a | mx] * min 1 (X a) ≤ min 1 (∑' a, Pr[= a | mx] * X a) := by
  refine le_min ?_ (ENNReal.tsum_le_tsum fun a => mul_le_mul_left' (min_le_right _ _) _)
  calc ∑' a, Pr[= a | mx] * min 1 (X a) ≤ ∑' a, Pr[= a | mx] * 1 :=
        ENNReal.tsum_le_tsum fun a => mul_le_mul_left' (min_le_left _ _) _
    _ = ∑' a, Pr[= a | mx] := by simp only [mul_one]
    _ ≤ 1 := tsum_probOutput_le_one

omit [Params] in
/-- **The split of one contact.** A contact with capped value is paid by `pay` and `κ` times its
uncapped value. -/
theorem capped_split {pay κ : ℝ≥0∞} (hκ : contactRate ≤ pay + κ * contactRate) (Q : ℝ≥0∞) :
    contactRate * min 1 Q ≤ pay + κ * contactRate * Q :=
  calc contactRate * min 1 Q ≤ (pay + κ * contactRate) * min 1 Q := mul_le_mul_right' hκ _
    _ = pay * min 1 Q + κ * contactRate * min 1 Q := add_mul _ _ _
    _ ≤ pay * 1 + κ * contactRate * Q :=
        add_le_add (mul_le_mul_left' (min_le_left _ _) _) (mul_le_mul_left' (min_le_right _ _) _)
    _ = pay + κ * contactRate * Q := by rw [mul_one]

/-! ### The armed potential -/

section DefsArm

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (κ : ℝ≥0∞)

/-- **The armed potential** of A4b: the contacts times the capped near potential, plus `κ` times
the contact rate times the near potentials at every lower level. -/
noncomputable def psiArm : Potential := fun s P L d _ budget =>
  (contacts parameter K s).card * min 1 (potN parameter data wbar Fail s P L d budget) +
    κ * contactRate * ∑ j ∈ Finset.range budget, potN parameter data wbar Fail s P L d j

end DefsArm

/-! ### The four steps -/

section StepsArm

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (κ : ℝ≥0∞) (Qtot : ℕ) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- **A new pair.** -/
theorem psiArm_newPair (hw : wbar ≤ 1) (hparse : ∀ p call, model.parse (pblk parameter data p call) = none) :
    NewPairPays parameter data Qtot initial model (psiArm parameter data K wbar Fail κ) := by
  intro budget s P L d R hb hB p hp0
  have hp1 := hB.pinv.first p hp0
  simp only [psiArm]
  have hc : ∀ a b, ((contacts parameter K (withPair parameter data s p a b)).card : ℝ≥0∞) =
      (contacts parameter K s).card := fun a b => by
    rw [contacts_withPair parameter data K model hB.cinv hparse hp0 hp1]
  simp only [hc]
  rw [pairE_add, pairE_const_mul, pairE_const_mul, pairE_range_sum]
  obtain ⟨y, rfl⟩ : ∃ y, budget = y + 1 := ⟨budget - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  refine add_le_add (mul_le_mul_left' ?_ _) (mul_le_mul_left' ?_ _)
  · exact le_trans (pairE_min_le _)
      (min_le_min le_rfl (potN_newPair parameter data wbar Fail hw hB.pinv hp0 L d y))
  · rw [Finset.sum_range_succ']
    exact le_trans (Finset.sum_le_sum fun j _ => potN_newPair parameter data wbar Fail hw hB.pinv hp0 L d j)
      le_self_add

/-- **Any other ordinary query**, paying `pay` at a FORS leaf input. -/
theorem psiArm_ordinary (hw : wbar ≤ 1) (hrows : FtsRows parameter model) {pay : ℝ≥0∞}
    (hκ : contactRate ≤ pay + κ * contactRate) :
    OrdinaryPaysP parameter data Qtot initial model (IsFleafIn parameter) pay
      (psiArm parameter data K wbar Fail κ) := by
  intro budget s P L d R hb hB x hnew
  simp only [psiArm]
  obtain ⟨y, rfl⟩ : ∃ y, budget = y + 1 := ⟨budget - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set Q := potN parameter data wbar Fail s P L d y with hQ
  set S := ∑ j ∈ Finset.range y, potN parameter data wbar Fail s P L d j with hS
  set c : ℝ≥0∞ := ((contacts parameter K s).card : ℝ≥0∞) with hcdef
  set f : ℝ≥0∞ := if IsFleafIn parameter x then 1 else 0 with hf
  set Nw : HashOutput × State → ℝ≥0∞ := fun r =>
    ((contacts parameter K r.2 \ contacts parameter K s).card : ℝ≥0∞) with hNw
  have hpt : ∀ r ∈ support (ordinaryStep model x s.known s),
      ((contacts parameter K r.2).card : ℝ≥0∞) * min 1 (potN parameter data wbar Fail r.2 P L d y) +
          κ * contactRate * ∑ j ∈ Finset.range y, potN parameter data wbar Fail r.2 P L d j ≤
        (c + Nw r) * min 1 Q + κ * contactRate * S := by
    intro r hr
    have hext := ordinaryStep_extends model x s r hr
    obtain ⟨_, hview⟩ := same_items parameter data hext (ordinaryStep_cache_ne model x s r hr) hnew hB.pinv
    have hgrow : ∀ j, potN parameter data wbar Fail r.2 P L d j ≤ potN parameter data wbar Fail s P L d j :=
      fun j => potG_grow wbar 0 Fail witnessNear_props gate_false_mono hw ENNReal.zero_ne_top hext hview L d le_rfl
    refine add_le_add (mul_le_mul' ?_ (min_le_min le_rfl (hgrow y)))
      (mul_le_mul_left' (Finset.sum_le_sum fun j _ => hgrow j) _)
    simp only [hcdef, hNw]
    rw [add_comm]
    exact_mod_cast Finset.card_le_card_sdiff_add_card
  have hmean : ∑' r, Pr[= r | ordinaryStep model x s.known s] * Nw r ≤ contactRate * f :=
    newContacts_mean parameter K model hrows x s hB.cinv
  have hmass : ∑' r, Pr[= r | ordinaryStep model x s.known s] = 1 := by simp
  have hf1 : f ≤ 1 := by rw [hf]; split_ifs <;> simp
  have hmono : min 1 Q ≤ min 1 (potN parameter data wbar Fail s P L d (y + 1)) :=
    min_le_min le_rfl (potG_mono wbar 0 Fail witnessNear_props _ hw ENNReal.zero_ne_top s P L d (Nat.le_succ y))
  calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] * ((c + Nw r) * min 1 Q + κ * contactRate * S) := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support (ordinaryStep model x s.known s)
        · exact mul_le_mul_left' (hpt r hr) _
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = ((∑' r, Pr[= r | ordinaryStep model x s.known s]) * c +
          ∑' r, Pr[= r | ordinaryStep model x s.known s] * Nw r) * min 1 Q +
          (∑' r, Pr[= r | ordinaryStep model x s.known s]) * (κ * contactRate * S) := by
        simp only [add_mul, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, ← mul_assoc]
    _ ≤ (1 * c + contactRate * f) * min 1 Q + 1 * (κ * contactRate * S) := by
        rw [hmass]
        gcongr
    _ = c * min 1 Q + f * (contactRate * min 1 Q) + κ * contactRate * S := by ring
    _ ≤ c * min 1 Q + f * (pay + κ * contactRate * Q) + κ * contactRate * S := by
        gcongr
        exact capped_split hκ Q
    _ = c * min 1 Q + pay * f + f * (κ * contactRate * Q) + κ * contactRate * S := by ring
    _ ≤ c * min 1 Q + pay * f + 1 * (κ * contactRate * Q) + κ * contactRate * S := by gcongr
    _ = c * min 1 Q + κ * contactRate * (S + Q) + pay * f := by ring
    _ ≤ c * min 1 (potN parameter data wbar Fail s P L d (y + 1)) +
          κ * contactRate * ∑ j ∈ Finset.range (y + 1), potN parameter data wbar Fail s P L d j + pay * f := by
        rw [Finset.sum_range_succ]
        gcongr

/-- **A signing call** on a fresh message. Every level of the near potential is kept in
expectation, and so is its cap. -/
theorem psiArm_sign (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hrows : FtsRows parameter model)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    {Cmax : ℕ} (hfair : Fair wbar Cmax) (hQ : Qtot + digestAttemptLimit ≤ Cmax) :
    SignPays parameter data Qtot tg initial model (psiArm parameter data K wbar Fail κ) := by
  intro budget s P L d R hB m hm
  have hcount : cachedCount parameter data m s + digestAttemptLimit ≤ Cmax := by
    have := hB.count m; omega
  set c : ℝ≥0∞ := ((contacts parameter K s).card : ℝ≥0∞) with hcdef
  set canon : ℕ → Run HashInput Coordinate (Option Signature) × State → ℝ≥0∞ := fun k o1 =>
    canonL parameter data witnessNear wbar 0 Fail (fun _ => False) m s P L d k o1 with hcanon
  set run := interp tg initial model (signCostSourceLoop parameter data m digestAttemptLimit) budget s with hrun
  have hse : ∀ k, ∑' o1, Pr[= o1 | run] * canon k o1 ≤ potN parameter data wbar Fail s P L d k := fun k =>
    sign_expectG_level tg initial model parameter data wbar 0 Fail m witnessNear_props (fun _ => False) hparse hfair
      ENNReal.zero_ne_top digestAttemptLimit budget k s P L hm d hB.pinv hcount
  have hpt : ∀ o1 ∈ support run,
      o1.1.1.elim 0 (fun r => psiArm parameter data K wbar Fail κ o1.2 (newPairs parameter data m s o1.2 ++ P)
        (L ++ [⟨m, r⟩]) (discAfter parameter data m s d o1) (R ++ o1.1.2.1) (budget - traceCost o1.1.2.2.1)) ≤
        c * min 1 (canon budget o1) + κ * contactRate * ∑ j ∈ Finset.range budget, canon j o1 := by
    intro o1 ho1
    cases hres : o1.1.1 with
    | none => exact bot_le
    | some r =>
        simp only [Option.elim, psiArm]
        have hcon := (interp_contacts_avoid (K := K) tg initial hrows _ (avoids_loopF parameter data m _)
          budget s hB.cinv o1 ho1).2
        rw [hcon]
        have hpoint : ∀ k' K', k' ≤ K' → potN parameter data wbar Fail o1.2 (newPairs parameter data m s o1.2 ++ P)
            (L ++ [⟨m, r⟩]) (discAfter parameter data m s d o1) k' ≤ canon K' o1 := fun k' K' hk =>
          sign_pointG_level tg initial model parameter data wbar 0 Fail Qtot m witnessNear_props gate_false_mono
            hparse (hfail m) hfair.le_one ENNReal.zero_ne_top digestAttemptLimit budget s P L d R hB.prep hB.pinv
            hB.dinv hB.count o1 ho1 r hres hk
        refine add_le_add (mul_le_mul_left' (min_le_min le_rfl (hpoint _ _ (Nat.sub_le _ _))) _)
          (mul_le_mul_left' ?_ _)
        calc _ ≤ ∑ j ∈ Finset.range (budget - traceCost o1.1.2.2.1), canon j o1 :=
              Finset.sum_le_sum fun j _ => hpoint j j le_rfl
          _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.sub_le _ _))
  calc _ ≤ ∑' o1, Pr[= o1 | run] *
        (c * min 1 (canon budget o1) + κ * contactRate * ∑ j ∈ Finset.range budget, canon j o1) := by
        refine ENNReal.tsum_le_tsum fun o1 => ?_
        by_cases ho1 : o1 ∈ support run
        · exact mul_le_mul_left' (hpt o1 ho1) _
        · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul]
    _ = c * ∑' o1, Pr[= o1 | run] * min 1 (canon budget o1) +
        κ * contactRate * ∑ j ∈ Finset.range budget, ∑' o1, Pr[= o1 | run] * canon j o1 := by
        rw [← tsum_range_sum, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        refine tsum_congr fun o1 => ?_
        ring
    _ ≤ _ := add_le_add (mul_le_mul_left' (le_trans (tsum_min_le _ _) (min_le_min le_rfl (hse budget))) _)
        (mul_le_mul_left' (Finset.sum_le_sum fun j _ => hse j) _)

/-- **The end of the game.** A valid finished game with A4b has a contact and a near-covered
candidate, so the capped first term is at least one. -/
theorem psiArm_final (hw : wbar ≤ 1) :
    FinalPays parameter data Qtot initial model (psiArm parameter data K wbar Fail κ) (finalB parameter data K) := by
  intro budget s P L d R hB forgery verified
  simp only [finalB, Option.elim, psiArm]
  split_ifs with hcase
  swap
  · exact bot_le
  obtain ⟨hvalid, i, t, l, hgr, m, ρ, digest, hdig, hland, hunsigned, hidx, -, hnear⟩ := hcase
  -- a contact
  have hc1 : (1 : ℝ≥0∞) ≤ (contacts parameter K s).card := by
    obtain ⟨secret, hmem⟩ := mem_contacts_of_GR parameter K hgr
    exact_mod_cast Finset.card_pos.2 ⟨_, hmem⟩
  -- the near-covered candidate
  set q : Pair := (m, ρ) with hq
  unfold HiddenBridge.cachedDigest at hdig
  have hpot : (1 : ℝ≥0∞) ≤ potN parameter data wbar Fail s P L d budget := by
    cases h0 : s.cache (pblk parameter data q 0) with
    | none =>
        have h0' : s.cache (tweakableHashInput parameter (.message 0) (messageDigestPayload data.root m ρ)) = none := h0
        rw [h0'] at hdig; cases hdig
    | some a =>
        cases h1 : s.cache (pblk parameter data q 1) with
        | none =>
            have h0' : s.cache (tweakableHashInput parameter (.message 0)
                (messageDigestPayload data.root m ρ)) = some a := h0
            have h1' : s.cache (tweakableHashInput parameter (.message 1)
                (messageDigestPayload data.root m ρ)) = none := h1
            rw [h0', h1'] at hdig; cases hdig
        | some b =>
            have h0' : s.cache (tweakableHashInput parameter (.message 0)
                (messageDigestPayload data.root m ρ)) = some a := h0
            have h1' : s.cache (tweakableHashInput parameter (.message 1)
                (messageDigestPayload data.root m ρ)) = some b := h1
            rw [h0', h1'] at hdig
            have hdig' : truncateMessageDigest a b = digest := by simpa using hdig
            subst hdig'
            have hlanded : LandedIn parameter data s q :=
              ⟨a, h0, by rwa [Completeness.digestIndex_truncate] at hland⟩
            have hqP := (hB.pinv.mem q).2 hlanded
            have hv : pview parameter data s q = Lifetime.localDigestView (truncateMessageDigest a b) := by
              simp only [pview, h0, h1, Option.elim, viewOf]
            unfold potN potG
            rw [if_neg (by
              rintro (h | h)
              · exact h
              · exact absurd hvalid (by simp [SigningTranscript.Valid]; omega))]
            unfold coreG
            refine le_trans ?_ (le_trans (List.le_sum_of_mem (List.mem_map_of_mem hqP))
              (le_self_add.trans le_self_add))
            unfold candG
            rw [if_pos (show Unsigned L q from hunsigned)]
            split_ifs
            · exact le_rfl
            · unfold candValueG
              calc (1 : ℝ≥0∞) ≤ witnessNear (pview parameter data s q) d := by
                    unfold witnessNear
                    rw [hv]
                    exact_mod_cast nearCount_pos hB.dinv _ t (fun other hother => by
                      rw [hidx]; exact hnear other hother)
                _ ≤ virtualOnce Finset.univ wbar (witnessNear (pview parameter data s q))
                      (signatureLimit - L.length) (coinItems parameter data s L (P.erase q)) d :=
                    base_le_virtualOnce Finset.univ_nonempty hw (witnessNear_props _).1 (witnessNear_props _).2.1
                      (witnessNear_props _).2.2 _ _ d
                _ ≤ _ := creations_mono_count (k := 0) Finset.univ_nonempty landing_le_one
                      (virtualOnce_cons_le' wbar hw (witnessNear_props _) _ d) (virtualOnce_perm' wbar _ d)
                      (Nat.zero_le _) _
  calc (1 : ℝ≥0∞) = 1 * min 1 (potN parameter data wbar Fail s P L d budget) := by
        rw [one_mul, min_eq_left hpot]
    _ ≤ ((contacts parameter K s).card : ℝ≥0∞) * min 1 (potN parameter data wbar Fail s P L d budget) :=
        mul_le_mul_right' hc1 _
    _ ≤ _ := le_self_add

end StepsArm

/-! ### The bound -/

section BoundArm

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- The start of the armed potential: no contacts, and `κ` times the refined sum. -/
theorem psiArm_start (κ : ℝ≥0∞) (known : Knowledge Coordinate) (total : ℕ) :
    psiArm parameter data K wbar Fail κ (DebtState.start initial known) [] [] 0 [] total =
      κ * contactRate * ∑ j ∈ Finset.range total,
        ((j : ℝ≥0∞) * (startNear wbar j + failMass Fail) + signatureLimit * failMass Fail) := by
  simp only [psiArm, potN_start]
  have : contacts parameter K (DebtState.start initial known) = ∅ := by
    unfold contacts
    rfl
  rw [this, Finset.card_empty, Nat.cast_zero, zero_mul, zero_add]

/-- **Theorem (b), armed.** In the lazy run of the rest of the game of an adversary that never
repeats a message, the game finishes with a valid transcript and A4b holds with probability at most
`κ 2^-128 Σ_{j < total} potNear_j(start)` plus `pay` per expected FORS leaf query, whenever
`2^-128 ≤ pay + κ 2^-128`. -/
theorem a4b_boundArm (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hclean : ∀ p call, initial (pblk parameter data p call) = none)
    (hrows : FtsRows parameter model)
    (hcleanF : ∀ x a v i t l, model.parse x = some (a, v) → model.incoming a = .ftsSecret i t l → initial x = none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (total : ℕ) (hfair : Fair wbar (total + digestAttemptLimit)) {pay κ : ℝ≥0∞}
    (hκ : contactRate ≤ pay + κ * contactRate)
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M []) (known : Knowledge Coordinate) :
    Pr[A4bRun parameter data K | interp tg initial model (advProg parameter data M []) total
        (DebtState.start initial known)] ≤
      κ * contactRate * ∑ j ∈ Finset.range total,
          ((j : ℝ≥0∞) * (startNear wbar j + failMass Fail) + signatureLimit * failMass Fail) +
        pay * expectedF tg initial model (IsFleafIn parameter) (advProg parameter data M []) total
          (DebtState.start initial known) := by
  have hFp : ∀ p call, ¬IsFleafIn parameter (pblk parameter data p call) := by
    rintro p call ⟨i, t, l, secret, h⟩
    exact PotentialA.msg_ne_fors (msgInput_digestInput parameter data.root p.1 p.2 call) h
  have h := final_le_startP parameter data tg initial model (IsFleafIn parameter) pay hparse hkind hrows hFp
    hclean hcleanF Fail hfail total
    (G := finalB parameter data K) (fun _ _ => rfl) (fun o R s x u hx => finalB_store o R s x u hx)
    (psiArm_newPair parameter data K wbar Fail κ total initial model hfair.le_one hparse)
    (psiArm_ordinary parameter data K wbar Fail κ total initial model hfair.le_one hrows hκ)
    (psiArm_sign parameter data K wbar Fail κ total tg initial model hparse hrows hfail hfair le_rfl)
    (psiArm_final parameter data K wbar Fail κ total initial model hfair.le_one) M hnr known
  rw [psiArm_start] at h
  rw [probEvent_eq_tsum_ite]
  refine le_trans (ENNReal.tsum_le_tsum fun out => ?_) h
  split_ifs with hE
  · obtain ⟨outcome, hres, hvalid, ha⟩ := hE
    simp only [finalB, hres, Option.elim, if_pos (And.intro hvalid ha), mul_one, le_refl]
  · exact bot_le

end BoundArm

/-! ### One sample, and the fair share -/

section GameArm

open Completeness SeedModel Graph Assembly Reduce Internalize

attribute [local instance] sampleCellFintypeInst sampleCellDecEq hiddenTableSampleable highsSampleable
  remainingSampleable

/-- **Theorem (b) armed, one sample.** On the interpreted run of `costGameX` of an adversary that
never repeats a message, with `y = q - keygenCost`. The expected number of FORS leaf queries is
taken over the same run. -/
theorem a4b_bound_gameArm (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) (hmsg : ∀ x, IsMsgInput x → tg.kind x = .none)
    (K : HiddenReveal.Knowledge Coordinate) (wbar : ℝ≥0∞) (hfair : Fair wbar (q - keygenCost + digestAttemptLimit))
    {pay κ : ℝ≥0∞} (hκ : contactRate ≤ pay + κ * contactRate) (known : Knowledge Coordinate) :
    Pr[A4bRun (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining) K |
        interp tg prepared.2 (sampleModel parameterOutput highs)
          (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
            (internalize adversary)) q (DebtState.start prepared.2 known)] ≤
      κ * contactRate * ∑ j ∈ Finset.range (q - keygenCost),
          ((j : ℝ≥0∞) * (startNear wbar j + failMass (failSet prepared.1)) +
            signatureLimit * failMass (failSet prepared.1)) +
        pay * ∑' out, Pr[= out | interp tg prepared.2 (sampleModel parameterOutput highs)
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
    have h := a4b_boundArm param data K wbar (failSet prepared.1) tg prepared.2 model
      (sampleModel_parse_blk parameterOutput highs data)
      (fun p call => hmsg _ (msgInput_digestInput param data.root p.1 p.2 call))
      (fun p call => prepared_clean parameterOutput fixed highs remaining prepared hprepared _
        (msgInput_digestInput param data.root p.1 p.2 call))
      (ftsRows_sampleModel parameterOutput highs)
      (prepared_cleanRows parameterOutput fixed highs remaining prepared hprepared)
      (fun m ρ digest budget s1 hprep out hout hnone => finishRest_fail parameterOutput fixed highs remaining prepared
        hprepared tg m ρ digest budget s1 hprep out hout hnone) (q - keygenCost) hfair hκ
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

/-- **Theorem (b) armed, at the fair share, with a certified near H-term.** The near term of
`a4b_bound_check_half` enters multiplied by `κ`, and `pay` is paid per expected FORS leaf query. -/
theorem a4b_bound_checkArm (adversary : Adversary) (hnr : adversary.NoRepeat) (q : ℕ)
    (b N qb m : ℕ) (c : ℚ) (hb : subtreeHeight = b) (hN : signatureLimit = N)
    (hc : H0.checkNear b N qb m c = true) (hq : q - keygenCost ≤ qb)
    (parameterOutput : HashOutput) (fixed : HiddenGraph.Table) (highs : CoordinateHighs)
    (remaining : RemainingOutputs) (prepared : (Index → Option (Counter × Encoding)) × QueryCache HashSpec)
    (hprepared : prepared ∈ support (preparation parameterOutput fixed highs remaining))
    (tg : Targeting HashInput HashOutput Coordinate) (hmsg : ∀ x, IsMsgInput x → tg.kind x = .none)
    (K : HiddenReveal.Knowledge Coordinate) {pay κ : ℝ≥0∞} (hκ : contactRate ≤ pay + κ * contactRate)
    (known : Knowledge Coordinate) :
    Pr[A4bRun (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining) K |
        interp tg prepared.2 (sampleModel parameterOutput highs)
          (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
            (internalize adversary)) q (DebtState.start prepared.2 known)] ≤
      κ * ((((q - keygenCost : ℕ) : ℝ≥0∞) * contactRate) *
        ((q - keygenCost : ℕ) * (ENNReal.ofReal ((c / 2 : ℚ) : ℝ) + failMass (failSet prepared.1)) +
          signatureLimit * failMass (failSet prepared.1))) +
        pay * ∑' out, Pr[= out | interp tg prepared.2 (sampleModel parameterOutput highs)
              (costGameX (truncateHash parameterOutput) (sampleData parameterOutput fixed highs remaining)
                (internalize adversary)) q (DebtState.start prepared.2 known)] *
            (fleafCount (IsFleafIn (truncateHash parameterOutput)) out.1.2.2.1 : ℝ≥0∞) := by
  have hqb : 2 * qb ≤ 2 ^ 128 := by
    simp only [H0.checkNear, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact hc.1.1.2
  have hfair := fair_wbarOf (q - keygenCost) (by omega)
  have h := a4b_bound_gameArm adversary hnr q parameterOutput fixed highs remaining prepared hprepared tg hmsg K
    (H0.wbarOf (q - keygenCost)) hfair hκ known
  refine le_trans h (add_le_add ?_ le_rfl)
  rw [mul_assoc κ, mul_comm ((q - keygenCost : ℕ) : ℝ≥0∞) contactRate, mul_assoc contactRate]
  refine mul_le_mul_left' (mul_le_mul_left' (start_sum_le hfair.le_one _ _ _ ?_) _) _
  rw [startNear_wbarOf, ← ofReal_half]
  exact H0.hNearOf_le_of_check b N qb m c hb hN hc _ hq

end GameArm

end LeanSphincs.Security.ForsPotential
