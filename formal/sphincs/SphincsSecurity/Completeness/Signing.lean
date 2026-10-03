import SphincsSecurity.Completeness.Digest
import SphincsSecurity.Completeness.Counter
import SphincsSecurity.Completeness.Encoding

/-!
# When signing fails

`sign` runs the randomizer search, derives and opens the few-time forest, and signs three layers,
returning `none` as soon as a search runs out. A union bound through that structure charges the
failure to the four searches. Each counter search needs its own inputs uncached when it starts;
`EncodingFresh` carries that from the start of signing, past the digest loop and the forest, and
past each earlier layer, whose own searches use a different layer field.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Completeness

open Concrete

attribute [local irreducible] Seeded.signDigestLoop Seeded.ftsOpen Seeded.treeRoot Seeded.treePath
  Seeded.layerMessage Seeded.otsSign sequenceFin digestAttemptLimit encodingAttemptLimit
  SphincsSecurity.deriveKey

/-- One counter search's failure bound. -/
noncomputable def encodingBound : ℝ≥0∞ :=
  failMass (fun out => TargetSum.decodeDigest (truncateHash out)) ^ encodingAttemptLimit

theorem EncodingFresh.mono {parameter : PublicParameter} {pending pending' : Layer → Prop}
    {cache : QueryCache HashSpec} (h : EncodingFresh parameter pending cache)
    (hsub : ∀ lay, pending' lay → pending lay) : EncodingFresh parameter pending' cache :=
  fun lay hlay => h lay (hsub lay hlay)

/-- A layer fails only if its counter search does, and that search starts on uncached inputs. -/
theorem probEvent_signLayer_none (sk : Seeded.SecretKey) (index : Index) (lay : Layer)
    (cache : QueryCache HashSpec) (hfresh : EncodingFresh sk.parameter (fun l => l = lay) cache) :
    Pr[fun r => r.1 = none | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (Seeded.signLayer sk index lay : OracleComp HashSpec (Option (LayerSignature lay)))).run cache]
      ≤ encodingBound := by
  rw [Seeded.signLayer]
  refine probEvent_bind_le _ _ _ cache _ (fun r hr => ?_)
  have hfresh' := hfresh.step _ r hr (fun f l hl tree leaf payload => by
    subst hl
    exact Avoids.layerMessage_of_structural f _ sk index l
      (structural_encoding sk.parameter sk.seed l tree leaf payload))
  refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ r.2 0 ?_) ?_
  · rintro ⟨result, cache'⟩ hr' hsome
    obtain ⟨⟨counter, values⟩, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    dsimp only
    refine probEvent_bind_le _ _ _ cache' _ (fun r'' _ => ?_)
    simp
  · rw [add_zero]
    exact probEvent_otsSign sk.parameter lay _ _ sk.seed r.1 r.2
      (fun c _ => hfresh' lay rfl _ _ _)

/-- The three layers run in turn; each passes the invariant on to the layers after it. -/
theorem probEvent_sequenceLayers_none (sk : Seeded.SecretKey) (index : Index)
    (cache : QueryCache HashSpec) (hfresh : EncodingFresh sk.parameter (fun _ => True) cache) :
    Pr[fun r => r.1 = none | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (sequenceLayers (m := OracleComp HashSpec) (α := fun lay => LayerSignature lay)
        (fun lay => Seeded.signLayer sk index lay))).run cache] ≤ 3 * encodingBound := by
  rw [sequenceLayers]
  refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ cache (2 * encodingBound) ?_) ?_
  · rintro ⟨result, c1⟩ hr hsome
    obtain ⟨bottom, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    dsimp only
    have h1 : EncodingFresh sk.parameter (fun l => l = middleLayer ∨ l = topLayer) c1 :=
      (hfresh.mono (fun _ _ => trivial)).step _ ⟨some bottom, c1⟩ hr
        (fun f l hl tree leaf payload => Avoids.signLayer_of_layer_ne f sk index bottomLayer
          (by rcases hl with rfl | rfl <;> decide) tree leaf payload)
    refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ c1 encodingBound ?_) ?_
    · rintro ⟨result2, c2⟩ hr2 hsome2
      obtain ⟨middle, rfl⟩ := Option.ne_none_iff_exists'.mp hsome2
      dsimp only
      have h2 : EncodingFresh sk.parameter (fun l => l = topLayer) c2 :=
        (h1.mono (fun l hl => Or.inr hl)).step _ ⟨some middle, c2⟩ hr2
          (fun f l hl tree leaf payload => Avoids.signLayer_of_layer_ne f sk index middleLayer
            (by subst hl; decide) tree leaf payload)
      refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ c2 0 ?_) ?_
      · rintro ⟨result3, c3⟩ _ hsome3
        obtain ⟨top, rfl⟩ := Option.ne_none_iff_exists'.mp hsome3
        simp
      · rw [add_zero]
        exact probEvent_signLayer_none sk index topLayer c2 h2
    · exact (add_le_add (probEvent_signLayer_none sk index middleLayer c1
        (h1.mono (fun l hl => Or.inl hl))) le_rfl).trans_eq (two_mul _).symm
  · calc _ ≤ encodingBound + 2 * encodingBound :=
          add_le_add (probEvent_signLayer_none sk index bottomLayer cache
            (hfresh.mono (fun _ _ => trivial))) le_rfl
      _ = 3 * encodingBound := by ring

/-- Signing fails only if the randomizer search or one of the three counter searches does. -/
theorem probEvent_sign_none (sk : Seeded.SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (hrand : ∀ s, cache (randInput sk message s) = none)
    (hmsg : ∀ ρ, cache (msgInput sk message ρ) = none)
    (henc : EncodingFresh sk.parameter (fun _ => True) cache) :
    Pr[fun r => r.1 = none | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (Seeded.sign sk message : OracleComp HashSpec (Option Signature))).run cache]
      ≤ digestFactor ^ digestAttemptLimit + 3 * encodingBound := by
  rw [Seeded.sign]
  refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ cache (3 * encodingBound) ?_) ?_
  · rintro ⟨result, c1⟩ hr hsome
    obtain ⟨⟨randomness, index, leaves⟩, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    dsimp only
    have h1 : EncodingFresh sk.parameter (fun _ => True) c1 :=
      henc.step _ ⟨_, c1⟩ hr (fun f l _ tree leaf payload =>
        Avoids.signDigestLoop_of_structural f _ sk message
          (structural_encoding sk.parameter sk.seed l tree leaf payload) _ _)
    refine probEvent_bind_le _ _ _ c1 _ (fun r2 hr2 => ?_)
    have h2 := h1.step _ r2 hr2 (fun f l _ tree leaf payload =>
      Avoids.sequenceFin f _ _ (fun _ => Avoids.deriveKey f _ _ _ _
        ((structural_encoding sk.parameter sk.seed l tree leaf payload).derive _)))
    refine probEvent_bind_le _ _ _ r2.2 _ (fun r3 hr3 => ?_)
    have h3 := h2.step _ r3 hr3 (fun f l _ tree leaf payload =>
      Avoids.ftsOpen_of_structural f _ _ _ _ _
        (structural_encoding sk.parameter sk.seed l tree leaf payload))
    refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ r3.2 0 ?_) ?_
    · rintro ⟨result4, c4⟩ _ hsome4
      obtain ⟨layers, rfl⟩ := Option.ne_none_iff_exists'.mp hsome4
      dsimp only
      refine probEvent_bind_le _ _ _ c4 _ (fun r5 _ => ?_)
      simp
    · rw [add_zero]
      exact probEvent_sequenceLayers_none sk index r3.2 h3
  · exact add_le_add (probEvent_signDigestLoop sk message digestAttemptLimit 0 cache ∅
      (by rw [digestAttemptLimit]; omega) (by simp) (fun s _ _ => hrand s) (fun ρ _ => hmsg ρ)) le_rfl

end SphincsSecurity.Completeness
