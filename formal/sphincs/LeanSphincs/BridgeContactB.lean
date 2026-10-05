import LeanSphincs.BridgeContactGame

/-! **A4b.** A contact made at an unknown FORS secret together with an unsigned cached landed pair
whose digest is covered by the reveals at every tree but one. This file defines the event, its
final value, the contact rate `2^-128`, and the near potential `potN` (`potNear` in the formulas of
`BridgeArmA4b`): the one-coin FORS potential of the near witness with baseline zero and no gate,
with its start value. The A4b potential of `BridgeArmA4b` is built from them. -/

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

/-! ### Helpers for the steps -/

section Steps

variable (parameter : PublicParameter) (data : PublicData) (K : HiddenReveal.Knowledge Coordinate)
  (wbar : ℝ≥0∞) (Fail : Finset (Fin (2 ^ subtreeHeight))) (Qtot : ℕ) {A : Type}
  (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

omit [Params] in
theorem gate_false_mono : ∀ s s' : State, Extends s s' → (fun _ : State => False) s → (fun _ : State => False) s' :=
  fun _ _ _ h => h

omit [Params] in
theorem contacts_withPair {s : State} (hinv : CInv parameter model s)
    (hparse : ∀ p call, model.parse (pblk parameter data p call) = none) {p : Pair}
    (hp0 : s.cache (pblk parameter data p 0) = none) (hp1 : s.cache (pblk parameter data p 1) = none)
    (a b : HashOutput) : contacts parameter K (withPair parameter data s p a b) = contacts parameter K s := by
  have hp1' : (s.store (pblk parameter data p 0) a).cache (pblk parameter data p 1) = none := by
    rw [store_cache_ne s _ _ (Ne.symm (pblk_ne_call parameter data p))]; exact hp1
  unfold withPair
  rw [contacts_store (cinv_store hinv hp0 (hparse p 0) a).guessed hp1' b, contacts_store hinv.guessed hp0 a]

end Steps

/-! ### The event of a run, and the start value -/

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

end Bound

end LeanSphincs.Security.ForsPotential
