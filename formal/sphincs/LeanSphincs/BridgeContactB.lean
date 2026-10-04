import LeanSphincs.BridgeContactGame

/-! **A4b.** A contact made at an unknown FORS secret together with an unsigned cached landed pair
whose digest is covered by the reveals at every tree but one. The product potential
`(C_F + y 2^-128) · potNear`, with `C_F` the number of contacts, `y` the remaining budget and
`potNear` the one-coin FORS potential of the near witness with baseline zero and no gate, pays the
event: contacts change only at FORS leaf queries, which keep `potNear` and create a contact with
probability at most `2^-128`, and `potNear` is paid by every other step. At the end, a near cover
makes `potNear` at least one. -/

open OracleComp OracleSpec ENNReal

namespace LeanSphincs.Security.ForsPotential

open Concrete HiddenGraph HiddenCost HiddenDebt GraphView Domination ForsPrice ForsSigner HiddenReveal

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

variable [Params]

/-- The contact rate `2^-128`. -/
noncomputable def contactRate : ℝ≥0∞ := ((2 : ℝ≥0∞) ^ 128)⁻¹

section Defs

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight)))

/-- **The spec's A4b** on a final state, log and reveals. -/
def A4b (s : State) (L : QueryLog SigningSpec) (reveals : List Coordinate) : Prop :=
  ∃ index tree leaf, GRContact parameter K s index tree leaf ∧
    ∃ (m : Message) (ρ : Randomness) (digest : MessageDigest),
      HiddenBridge.cachedDigest s.cache parameter data.root m ρ = some digest ∧
      Landed parameter (digestIndex digest) ∧
      (∀ entry ∈ L, ∀ signature, entry.2 = some signature → ¬(entry.1 = m ∧ signature.randomness = ρ)) ∧
      digestIndex digest = index ∧ digestLeaves digest tree = leaf ∧
      ∀ other, other ≠ tree → digestLeaves digest other ∈ HiddenBridge.revealedSet reveals index other

/-- The final value of A4b: a finished game with a valid transcript. -/
noncomputable def finalB : FinalFn := fun o R s =>
  o.elim 0 fun outcome =>
    if SigningTranscript.Valid outcome.2.1 ∧ A4b parameter data K s outcome.2.1 R then 1 else 0

/-- **The near potential**: one coin, near witness, baseline zero, no gate. -/
noncomputable def potN (s : State) (P : List Pair) (L : QueryLog SigningSpec) (d : Multiset View) (k : ℕ) : ℝ≥0∞ :=
  potG parameter data witnessNear wbar 0 Fail (fun _ => False) s P L d k

/-- **The product potential** of A4b. -/
noncomputable def psiB : Potential := fun s P L d _ budget =>
  ((contacts parameter K s).card + budget * contactRate) * potN parameter data wbar Fail s P L d budget

/-- The near forecast of a new pair at the start of the run. -/
noncomputable def startNear (k : ℕ) : ℝ≥0∞ :=
  creations Finset.univ landing (fun I => virtualOnce Finset.univ wbar (excessW witnessNear 0) signatureLimit I 0) k []

end Defs

/-! ### The final value -/

section Final

variable {parameter : PublicParameter} {data : PublicData} {K : HiddenReveal.Knowledge Coordinate}

theorem a4b_mono {s s' : State} (hext : Extends s s') {L : QueryLog SigningSpec} {R : List Coordinate}
    (h : A4b parameter data K s L R) : A4b parameter data K s' L R := by
  obtain ⟨i, t, l, ⟨secret, ans, hc, hg, hK⟩, m, ρ, digest, hdig, hrest⟩ := h
  refine ⟨i, t, l, ⟨secret, ans, hext.1 _ _ hc, hext.2.2 _ hg, hK⟩, m, ρ, digest, ?_, hrest⟩
  unfold HiddenBridge.cachedDigest at hdig ⊢
  cases h0 : s.cache (tweakableHashInput parameter (.message 0) (messageDigestPayload data.root m ρ)) with
  | none => rw [h0] at hdig; cases hdig
  | some a =>
      cases h1 : s.cache (tweakableHashInput parameter (.message 1) (messageDigestPayload data.root m ρ)) with
      | none => rw [h0, h1] at hdig; cases hdig
      | some b =>
          rw [h0, h1] at hdig
          rw [hext.1 _ _ h0, hext.1 _ _ h1]
          exact hdig

theorem finalB_store (o : Option HiddenBridge.Outcome) (R : List Coordinate) (s : State) (x : HashInput)
    (u : HashOutput) (hx : s.cache x = none) :
    finalB parameter data K o R s ≤ finalB parameter data K o R (s.store x u) := by
  unfold finalB
  cases o with
  | none => exact le_rfl
  | some outcome =>
      simp only [Option.elim]
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd ⟨h1.1, a4b_mono (extends_store s x u hx) h1.2⟩ h2
      · exact bot_le
      · exact le_rfl

end Final

/-! ### The four steps -/

section Steps

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

omit [Params] in
theorem gate_false_mono : ∀ s s' : State, Extends s s' → (fun _ : State => False) s → (fun _ : State => False) s' :=
  fun _ _ _ h => h

theorem contacts_withPair {s : State} (hinv : CInv parameter model s)
    (hparse : ∀ p call, model.parse (pblk parameter data p call) = none) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) (hp1 : s.cache (pblk parameter data p 1) = none)
    (a b : HashOutput) : contacts parameter K (withPair parameter data s p a b) = contacts parameter K s := by
  have hp1' : (s.store (pblk parameter data p 0) a).cache (pblk parameter data p 1) = none := by
    rw [store_cache_ne s _ _ (Ne.symm (pblk_ne_call parameter data p))]; exact hp1
  unfold withPair
  rw [contacts_store (cinv_store hinv hp0 (hparse p 0) a).guessed hp1' b, contacts_store hinv.guessed hp0 a]

/-- **A new pair.** -/
theorem psiB_newPair (hw : wbar ≤ 1) (hparse : ∀ p call, model.parse (pblk parameter data p call) = none) :
    NewPairPays parameter data Qtot initial model (psiB parameter data K wbar Fail) := by
  intro budget s P L d R hb hB p hp0
  have hp1 := hB.pinv.first p hp0
  simp only [psiB]
  have hc : ∀ a b, ((contacts parameter K (withPair parameter data s p a b)).card : ℝ≥0∞) =
      (contacts parameter K s).card := fun a b => by rw [contacts_withPair parameter data K model hB.cinv hparse hp0 hp1]
  simp only [hc]
  rw [pairE_const_mul]
  have hbud : ((budget - 1 : ℕ) : ℝ≥0∞) ≤ budget := by exact_mod_cast Nat.sub_le budget 1
  refine mul_le_mul' (add_le_add le_rfl (mul_le_mul_right' hbud _)) ?_
  unfold potN potG
  by_cases hL : False ∨ signatureLimit < L.length
  · simp only [if_pos hL, pairE_const, le_refl]
  · simp only [if_neg hL]
    have h := coreG_newPair wbar 0 Fail witnessNear_props hw ENNReal.zero_ne_top hB.pinv hp0 L d
      (signatureLimit - L.length) (budget - 1)
    rwa [Nat.sub_add_cancel hb, add_zero] at h

/-- **Any other ordinary query.** -/
theorem psiB_ordinary (hw : wbar ≤ 1) (hrows : FtsRows parameter model) :
    OrdinaryPays parameter data Qtot initial model (psiB parameter data K wbar Fail) := by
  intro budget s P L d R hb hB x hnew
  simp only [psiB]
  set Q := potN parameter data wbar Fail s P L d budget with hQ
  set c : ℝ≥0∞ := ((contacts parameter K s).card : ℝ≥0∞) with hcdef
  have hpt : ∀ r ∈ support (ordinaryStep model x s.known s),
      ((contacts parameter K r.2).card + ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) *
          potN parameter data wbar Fail r.2 P L d (budget - 1) ≤
        (c + ((contacts parameter K r.2 \ contacts parameter K s).card : ℝ≥0∞) +
          ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) * Q := by
    intro r hr
    have hext := ordinaryStep_extends model x s r hr
    obtain ⟨_, hview⟩ := same_items parameter data hext (ordinaryStep_cache_ne model x s r hr) hnew hB.pinv
    refine mul_le_mul' (add_le_add ?_ le_rfl) ?_
    · rw [hcdef, add_comm]
      exact_mod_cast Finset.card_le_card_sdiff_add_card
    · exact potG_grow wbar 0 Fail witnessNear_props gate_false_mono hw ENNReal.zero_ne_top hext hview L d
        (Nat.sub_le budget 1)
  have hmean := ordinary_contacts_mean (K := K) hrows x s hB.cinv
  calc _ ≤ ∑' r, Pr[= r | ordinaryStep model x s.known s] *
        ((c + ((contacts parameter K r.2 \ contacts parameter K s).card : ℝ≥0∞) +
          ((budget - 1 : ℕ) : ℝ≥0∞) * contactRate) * Q) := by
        refine ENNReal.tsum_le_tsum fun r => ?_
        by_cases hr : r ∈ support (ordinaryStep model x s.known s)
        · exact mul_le_mul_left' (hpt r hr) _
        · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ = ((∑' r, Pr[= r | ordinaryStep model x s.known s]) * c +
          ∑' r, Pr[= r | ordinaryStep model x s.known s] *
            ((contacts parameter K r.2 \ contacts parameter K s).card : ℝ≥0∞) +
          (∑' r, Pr[= r | ordinaryStep model x s.known s]) * (((budget - 1 : ℕ) : ℝ≥0∞) * contactRate)) * Q := by
        simp only [add_mul, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, ← mul_assoc]
    _ ≤ (1 * c + contactRate + 1 * (((budget - 1 : ℕ) : ℝ≥0∞) * contactRate)) * Q := by
        gcongr
        · exact tsum_probOutput_le_one
        · exact hmean
        · exact tsum_probOutput_le_one
    _ = (c + (budget : ℝ≥0∞) * contactRate) * Q := by
        have hcast : ((budget - 1 : ℕ) : ℝ≥0∞) + 1 = budget := by exact_mod_cast Nat.sub_add_cancel hb
        rw [one_mul, one_mul, ← hcast]
        ring

/-- **A signing call** on a fresh message. -/
theorem psiB_sign (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hrows : FtsRows parameter model)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    {Cmax : ℕ} (hfair : Fair wbar Cmax) (hQ : Qtot + digestAttemptLimit ≤ Cmax) :
    SignPays parameter data Qtot tg initial model (psiB parameter data K wbar Fail) := by
  intro budget s P L d R hB m hm
  have hcount : cachedCount parameter data m s + digestAttemptLimit ≤ Cmax := by
    have := hB.count m; omega
  set c : ℝ≥0∞ := ((contacts parameter K s).card : ℝ≥0∞) with hcdef
  have hse := sign_expectG tg initial model parameter data wbar 0 Fail m witnessNear_props
    (fun _ => False) hparse hfair ENNReal.zero_ne_top digestAttemptLimit budget s P L hm d hB.pinv hcount
  refine le_trans ?_ (mul_le_mul_left' hse (c + (budget : ℝ≥0∞) * contactRate))
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun o1 => ?_
  by_cases ho1 : o1 ∈ support (interp tg initial model (signCostSourceLoop parameter data m digestAttemptLimit) budget s)
  · rw [mul_left_comm]
    refine mul_le_mul_left' ?_ _
    cases hres : o1.1.1 with
    | none => exact bot_le
    | some r =>
        simp only [Option.elim, psiB]
        have hcon := (interp_contacts_avoid (K := K) tg initial hrows _ (avoids_loopF parameter data m _)
          budget s hB.cinv o1 ho1).2
        rw [hcon]
        have hbud : ((budget - traceCost o1.1.2.2.1 : ℕ) : ℝ≥0∞) ≤ budget := by
          exact_mod_cast Nat.sub_le budget _
        refine mul_le_mul' (add_le_add le_rfl (mul_le_mul_right' hbud _)) ?_
        exact sign_pointG tg initial model parameter data wbar 0 Fail Qtot m witnessNear_props gate_false_mono
          hparse (hfail m) hfair.le_one ENNReal.zero_ne_top digestAttemptLimit budget s P L d R hB.prep hB.pinv
          hB.dinv hB.count o1 ho1 r hres (Nat.sub_le budget (traceCost o1.1.2.2.1))
  · rw [probOutput_eq_zero_of_not_mem_support ho1, zero_mul, zero_mul, mul_zero]

/-- **The end of the game.** A valid finished game with A4b has a contact and a near-covered
candidate. -/
theorem psiB_final (hw : wbar ≤ 1) : FinalPays parameter data Qtot initial model (psiB parameter data K wbar Fail)
    (finalB parameter data K) := by
  intro budget s P L d R hB forgery verified
  simp only [finalB, Option.elim, psiB]
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
  calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
    _ ≤ ((contacts parameter K s).card : ℝ≥0∞) * potN parameter data wbar Fail s P L d budget :=
        mul_le_mul' hc1 hpot
    _ ≤ _ := mul_le_mul_right' le_self_add _

end Steps

/-! ### The bound -/

section Bound

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- The event A4b of a finished run with a valid transcript. -/
def A4bRun (out : Run HashInput Coordinate HiddenBridge.Outcome × State) : Prop :=
  ∃ outcome, out.1.1 = some outcome ∧ SigningTranscript.Valid outcome.2.1 ∧
    A4b parameter data K out.2 outcome.2.1 out.1.2.1

theorem potN_start (known : Knowledge Coordinate) (total : ℕ) :
    potN parameter data wbar Fail (DebtState.start initial known) [] [] 0 total =
      total * (startNear wbar total + failMass Fail) + signatureLimit * failMass Fail := by
  unfold potN potG
  rw [if_neg (by simp)]
  unfold coreG hValueG startNear
  simp [coinItems, items]

/-- **Theorem (b).** In the lazy run of the rest of the game of an adversary that never repeats a
message, the probability that the game finishes with a valid transcript and A4b holds is at most
`x · potNear(start)`, `x = total · 2^-128`. -/
theorem a4b_bound (hparse : ∀ p call, model.parse (pblk parameter data p call) = none)
    (hkind : ∀ p call, tg.kind (pblk parameter data p call) = .none)
    (hclean : ∀ p call, initial (pblk parameter data p call) = none)
    (hrows : FtsRows parameter model)
    (hcleanF : ∀ x a v i t l, model.parse x = some (a, v) → model.incoming a = .ftsSecret i t l → initial x = none)
    (hfail : ∀ m ρ digest budget (s1 : State), Prepared initial s1 →
      ∀ out ∈ support (interp tg initial model (finishRest parameter data m ρ digest) budget s1),
        out.1.1 = some none → (Lifetime.localDigestView digest).1 ∈ Fail)
    (total : ℕ) (hfair : Fair wbar (total + digestAttemptLimit))
    (M : OracleComp (OracleWorld + SigningSpec) Forgery) (hnr : NoRepeat M []) (known : Knowledge Coordinate) :
    Pr[A4bRun parameter data K | interp tg initial model (advProg parameter data M []) total
        (DebtState.start initial known)] ≤
      ((total : ℝ≥0∞) * contactRate) *
        (total * (startNear wbar total + failMass Fail) + signatureLimit * failMass Fail) := by
  have h := final_le_start parameter data tg initial model hparse hkind hrows hclean hcleanF Fail hfail total
    (G := finalB parameter data K) (fun _ _ => rfl) (fun o R s x u hx => finalB_store o R s x u hx)
    (psiB_newPair parameter data K wbar Fail total initial model hfair.le_one hparse)
    (psiB_ordinary parameter data K wbar Fail total initial model hfair.le_one hrows)
    (psiB_sign parameter data K wbar Fail total tg initial model hparse hrows hfail hfair le_rfl)
    (psiB_final parameter data K wbar Fail total initial model hfair.le_one) M hnr known
  have hstart : psiB parameter data K wbar Fail (DebtState.start initial known) [] [] 0 [] total =
      ((total : ℝ≥0∞) * contactRate) *
        (total * (startNear wbar total + failMass Fail) + signatureLimit * failMass Fail) := by
    simp only [psiB]
    rw [potN_start]
    have : contacts parameter K (DebtState.start initial known) = ∅ := by
      unfold contacts
      rfl
    rw [this, Finset.card_empty, Nat.cast_zero, zero_add]
  rw [hstart] at h
  rw [probEvent_eq_tsum_ite]
  refine le_trans (ENNReal.tsum_le_tsum fun out => ?_) h
  split_ifs with hE
  · obtain ⟨outcome, hres, hvalid, ha⟩ := hE
    simp only [finalB, hres, Option.elim, if_pos (And.intro hvalid ha), mul_one, le_refl]
  · exact bot_le

end Bound

end LeanSphincs.Security.ForsPotential
