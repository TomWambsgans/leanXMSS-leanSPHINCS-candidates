import LeanForest.BridgeSigner

/-! The grinding signer's view of message-digest blocks, and its fair share. Its encoding search
and its reveals never query a message-digest input, so after the digest call of the final assembly
the selected pair's block is what the signature discloses. A cached landed pair of the signed
message is selected with probability at most `1 / (n + R)` when the message has `n` cached landed
pairs: every trial picks each of them with probability `2^-128` and a fresh landed pair with
probability at least `R · 2^-128`. -/

open OracleComp OracleSpec ENNReal

namespace LeanForest.Security.ForestSigner

open Concrete HiddenCost HiddenDebt GraphView

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- A message-digest input, for any public parameter and payload. -/
def IsMsgInput (input : HashInput) : Prop :=
  ∃ parameter payload, input = tweakableHashInput parameter .message payload

/-- No query of a hash computation is a message-digest input. -/
def NoMsg {α : Type} (computation : OracleComp HashSpec α) : Prop :=
  computation.IsQueryBoundP IsMsgInput 0

theorem NoMsg.pure' {α : Type} (value : α) : NoMsg (pure value : OracleComp HashSpec α) := trivial

theorem NoMsg.bind {α β : Type} {oa : OracleComp HashSpec α} {next : α → OracleComp HashSpec β}
    (h : NoMsg oa) (hnext : ∀ value, NoMsg (next value)) : NoMsg (oa >>= next) := by
  have := isQueryBoundP_bind (n := 0) (m := 0) h (fun value _ => hnext value)
  simpa [NoMsg] using this

theorem NoMsg.query {input : HashInput} (h : ¬IsMsgInput input) :
    NoMsg (oracleHash input : OracleComp HashSpec HashOutput) := by
  simp only [NoMsg, oracleHash, HasQuery.query]
  rw [isQueryBoundP_query_iff]
  exact fun hm => absurd hm h

theorem not_msg_tweakable (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (hdomain : (hashDomainFields domain).tag ≠ 12) : ¬IsMsgInput (tweakableHashInput parameter domain payload) := by
  rintro ⟨parameter', payload', heq⟩
  have h := (tweakableInput_injective heq).1
  apply hdomain
  rw [h]
  rfl

theorem NoMsg.tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (hdomain : (hashDomainFields domain).tag ≠ 12) :
    NoMsg (Concrete.tweakableHash parameter domain payload : OracleComp HashSpec Digest) := by
  unfold Concrete.tweakableHash
  exact NoMsg.bind (NoMsg.query (not_msg_tweakable parameter domain payload hdomain)) fun _ => NoMsg.pure' _

theorem NoMsg.encode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) :
    NoMsg (Concrete.encode parameter lay tree leaf message counter : OracleComp HashSpec (Option Encoding)) := by
  unfold Concrete.encode
  exact NoMsg.bind (NoMsg.tweakableHash _ _ _ (by simp [hashDomainFields, tweakFields])) fun _ => NoMsg.pure' _

theorem NoMsg.search (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) : ∀ attempts start,
    NoMsg (ReferenceChoice.search parameter lay tree leaf message attempts start)
  | 0, _ => NoMsg.pure' _
  | attempts + 1, start => by
      rw [ReferenceChoice.search]
      refine NoMsg.bind (NoMsg.encode _ _ _ _ _ _) fun found => ?_
      cases found with
      | none => exact NoMsg.search parameter lay tree leaf message attempts (start + 1)
      | some _ => exact NoMsg.pure' _

end LeanForest.Security.ForestSigner

namespace LeanForest.Security.HiddenDebt

open HiddenCost HiddenBridge HiddenOutside HiddenReveal

variable {D R A ι : Type} [Fintype ι] [SampleableType R]
attribute [local instance] saturationDecEqInput saturationDecEqCoordinate
variable (tg : Targeting D R ι) (initial : Cache D R) (model : HiddenRows.Model D R A ι)

omit [Fintype ι] in
/-- **One read of a cached entry, kept.** -/
theorem one_read_bound {β : Type} (x0 : D) (hp0 : model.parse x0 = none)
    (state : DebtState D R ι) (u0 : R) (hc0 : state.cache x0 = some u0)
    (rest : R → OracleComp (SourceCostSpec D R ι) β)
    (havoid : ∀ a, Avoids (fun x => x = x0) (rest a)) (g : R → ℝ≥0∞) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model
        (liftM ((SourceCostSpec D R ι).query (.inl (.inr (.inl x0)))) >>= fun a => rest a) budget state] *
        (if out.1.1.isSome then (out.2.cache x0).elim 0 g else 0) ≤ g u0 := by
  rw [interp_ordinary]
  split_ifs with h0
  · rw [ordinaryStep, hp0]
    simp only
    rw [readOutside_cached x0 state u0 hc0, pure_bind, tsum_probOutput_map_mul]
    simp only
    calc _ ≤ ∑' out, Pr[= out | interp tg initial model (rest u0) (budget - 1) state] * g u0 := by
          refine ENNReal.tsum_le_tsum fun out => ?_
          by_cases hout : out ∈ support (interp tg initial model (rest u0) (budget - 1) state)
          · have hk0 := interp_avoids_cache tg initial model _ (rest u0) (havoid u0) _ state out hout x0 rfl
            gcongr
            split_ifs
            · rw [hk0, hc0]; rfl
            · exact bot_le
          · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
      _ ≤ g u0 := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' tsum_probOutput_le_one
  · rw [tsum_probOutput_pure_mul]
    simp

end LeanForest.Security.HiddenDebt

namespace LeanForest.Security.GraphView

open LeanSphincs.Security
open Concrete Completeness Prefix HiddenGraph HiddenCost HiddenDebt ForestSigner

attribute [local instance] Classical.propDecidable

variable [Params]

/-- The final assembly after its digest call. -/
noncomputable def finishRest (parameter : PublicParameter) (data : PublicData) (_message : Message)
    (randomness : Randomness) (digest : MessageDigest) : OracleComp CostSpec (Option Signature) := do
  HiddenCost.tick 130873
  let index := digestIndex digest
  let some (counter, word) ← liftM (ReferenceChoice.search parameter topLayer rootTree index
    (data.forestKey index) encodingAttemptLimit 0) | return none
  let values ← sequenceFin fun chain => HiddenCost.reveal
    (.chain topLayer rootTree index chain (word chain))
  let opening ← sequenceFin fun c => coordCostSource data index c (digestMarks digest c)
  HiddenCost.tick (184 + treePathCost)
  let top : LayerSignature topLayer := ⟨counter, values, data.treePath index⟩
  return some ⟨randomness, opening, Fin.cases top (fun i => Fin.elim0 i)⟩

theorem finishCostSource_eq (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) :
    finishCostSource parameter data message randomness =
      liftM (CostSpec.query (.inl (.inr (.inl (Security.digestInput parameter data.root message randomness))))) >>=
        fun first => finishRest parameter data message randomness (truncateMessageDigest first) := by
  unfold finishCostSource finishRest messageDigest messageDigestCall
  simp only [liftM_bind, bind_assoc, liftM_pure, pure_bind]
  rfl

omit [Params] in
theorem msgInput_digestInput (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) :
    IsMsgInput (Security.digestInput parameter root message randomness) :=
  ⟨parameter, _, rfl⟩

omit [Params] in
theorem avoids_coordCostSource (avoid : HashInput → Prop) (data : PublicData) (index : Index) (c : Coord)
    (mark : CoordMark) : Avoids avoid (coordCostSource data index c mark) := by
  unfold coordCostSource
  refine avoids_bind _ (avoids_sequenceFin _ _ fun j => ?_) fun _ => avoids_pure _ _
  refine avoids_bind _ (avoids_sequenceFin _ _ fun i => ?_) fun _ => avoids_pure _ _
  unfold revealChainCost
  refine avoids_sequenceFin _ _ fun k => ?_
  split
  · exact avoids_reveal _ _
  · exact avoids_pure _ _

/-- The rest of the final assembly never queries a message-digest input. -/
theorem avoids_finishRest (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) (digest : MessageDigest) :
    Avoids IsMsgInput (finishRest parameter data message randomness digest) := by
  unfold finishRest
  refine avoids_bind _ (avoids_tick _ _) fun _ => ?_
  refine avoids_bind _ (avoids_liftHash _ _ (NoMsg.search _ _ _ _ _ _ _)) fun found => ?_
  rcases found with _ | ⟨counter, word⟩
  · exact avoids_pure _ _
  · refine avoids_bind _ (avoids_sequenceFin _ _ fun _ => avoids_reveal _ _) fun _ => ?_
    refine avoids_bind _ (avoids_sequenceFin _ _ fun _ => avoids_coordCostSource _ _ _ _ _) fun _ => ?_
    exact avoids_bind _ (avoids_tick _ _) fun _ => avoids_pure _ _

omit [Params] in
theorem post_bind {spec : OracleSpec ι} {α β : Type} (P : β → Prop) (first : OracleComp spec α)
    {next : α → OracleComp spec β} (h : ∀ a, ∀ v ∈ support (next a), P v) :
    ∀ v ∈ support (first >>= next), P v := by
  intro v hv
  rw [support_bind] at hv
  obtain ⟨a, _, hva⟩ := Set.mem_iUnion₂.1 hv
  exact h a v hva

/-- A completed assembly signs with the trial's randomizer. -/
theorem finish_randomness (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness) :
    ∀ v ∈ support (finishCostSource parameter data message randomness), ∀ sig, v = some sig →
      sig.randomness = randomness := by
  rw [finishCostSource_eq]
  refine post_bind _ _ fun a => ?_
  unfold finishRest
  refine post_bind _ _ fun _ => post_bind _ _ fun found => ?_
  rcases found with _ | ⟨counter, word⟩
  · intro v hv sig hsig
    rw [support_pure, Set.mem_singleton_iff] at hv
    rw [hv] at hsig
    cases hsig
  · refine post_bind _ _ fun _ => post_bind _ _ fun _ => post_bind _ _ fun _ => ?_
    intro v hv sig hsig
    rw [support_pure, Set.mem_singleton_iff] at hv
    rw [hv] at hsig
    cases hsig
    rfl

section FinishOne

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate) (initial : HiddenOutside.Cache HashInput HashOutput)
  (model : HiddenRows.Model HashInput HashOutput A Coordinate)

/-- **Final assembly, one cached block.** -/
theorem finish_bound₁ (parameter : PublicParameter) (data : PublicData) (message : Message)
    (randomness : Randomness)
    (hparse : model.parse (Security.digestInput parameter data.root message randomness) = none)
    (state : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput)
    (hc0 : state.cache (Security.digestInput parameter data.root message randomness) = some u0)
    (g : HashOutput → ℝ≥0∞) (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message randomness) budget state] *
        (if out.1.1.isSome then
          (out.2.cache (Security.digestInput parameter data.root message randomness)).elim 0 g else 0) ≤ g u0 := by
  rw [finishCostSource_eq]
  exact one_read_bound tg initial model _ hparse state u0 hc0
    (fun a => finishRest parameter data message randomness (truncateMessageDigest a))
    (fun a => avoids_mono (fun x hx => by
        rw [hx]; exact msgInput_digestInput parameter data.root message randomness)
      (avoids_finishRest parameter data message randomness _)) g budget

end FinishOne

theorem signCostSourceLoop_succ (parameter : PublicParameter) (data : PublicData) (message : Message)
    (attempts : ℕ) :
    signCostSourceLoop parameter data message (attempts + 1) =
      (liftM ($ᵗ Randomness : ProbComp Randomness) : OracleComp CostSpec Randomness) >>= fun randomness =>
        liftM (CostSpec.query (.inl (.inr (.inl
          (Security.digestInput parameter data.root message randomness))))) >>= fun first =>
            if Landed parameter (blockIndex first) then finishCostSource parameter data message randomness
            else signCostSourceLoop parameter data message attempts := by
  rw [signCostSourceLoop]
  rfl

/-- The view of a digest block. -/
def viewOf (u0 : HashOutput) : Lifetime.KeptDigestView :=
  Lifetime.localDigestView (truncateMessageDigest u0)

/-- The fresh landed view law: weighting a fresh block by a landed view weight gives the landing
probability times the uniform average of the weight. -/
theorem fresh_view_mean (parameter : PublicParameter) (gf : Lifetime.KeptDigestView → ℝ≥0∞) :
    (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Landed parameter (blockIndex u0) then gf (viewOf u0) else 0)) =
      ForestPrice.landing * Domination.freshAvg Finset.univ gf := by
  classical
  set φ : MessageDigest → ℝ≥0∞ := fun digest =>
    if Landed parameter (digestIndex digest) then gf (Lifetime.localDigestView digest) else 0
  have hsplit : (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Landed parameter (blockIndex u0) then gf (viewOf u0) else 0)) =
      ∑' digest, Pr[= digest | truncateMessageDigest <$> ($ᵗ HashOutput : ProbComp HashOutput)] * φ digest := by
    rw [tsum_probOutput_map_mul]
    refine tsum_congr fun u0 => ?_
    simp only [φ, viewOf, digestIndex_truncate]
  rw [hsplit]
  have huni : ∀ digest, Pr[= digest | truncateMessageDigest <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
      Pr[= digest | ($ᵗ MessageDigest : ProbComp MessageDigest)] := by
    intro digest
    rw [probOutput_def, probOutput_def, Security.evalDist_digestBlock_uniform]
  simp only [huni]
  have hview : ∀ digest, φ digest = ∑ view, gf view *
      (if Landed parameter (digestIndex digest) ∧ Lifetime.localDigestView digest = view then 1 else 0) := by
    intro digest
    simp only [φ]
    split_ifs with hl
    · rw [Finset.sum_eq_single (Lifetime.localDigestView digest)]
      · simp [hl]
      · intro b _ hb
        simp [hl, Ne.symm hb]
      · simp
    · simp [hl]
  simp only [hview, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  have hterm : ∀ view : Lifetime.KeptDigestView,
      (∑' digest, Pr[= digest | ($ᵗ MessageDigest : ProbComp MessageDigest)] *
        (gf view * if Landed parameter (digestIndex digest) ∧ Lifetime.localDigestView digest = view then 1 else 0)) =
      gf view * (ForestPrice.landing * (Fintype.card Lifetime.KeptDigestView : ℝ≥0∞)⁻¹) := by
    intro view
    have hp := Lifetime.probEvent_landed_localDigest parameter (fun v => v = view)
    rw [probEvent_eq_tsum_ite] at hp
    rw [probEvent_eq_eq_probOutput, probOutput_uniformSample] at hp
    calc _ = gf view * ∑' digest, (if Landed parameter (digestIndex digest) ∧
            Lifetime.localDigestView digest = view then Pr[= digest | ($ᵗ MessageDigest : ProbComp MessageDigest)]
            else 0) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun digest => ?_
          split_ifs <;> ring
      _ = _ := by rw [hp]; rfl
  simp only [hterm]
  rw [← Finset.sum_mul, Domination.freshAvg, Finset.card_univ]
  ring


omit [Params] in
theorem loop_arith_real (a e u n N F l d : ℝ) (ha : 0 ≤ a) (he : 0 ≤ e) (hd : 0 ≤ d)
    (hnNF : n * u + N + F ≤ 1) (hu : u ≤ e * (n * u + F * l)) :
    u * (n * a + d) + N * (a + e * d) + F * (l * a + (1 - l) * (a + e * d)) ≤ a + e * d := by
  nlinarith [mul_nonneg ha (by linarith : (0:ℝ) ≤ 1 - n * u - N - F),
    mul_nonneg hd (by linarith : (0:ℝ) ≤ e * (n * u + F * l) - u),
    mul_nonneg hd (mul_nonneg he (by linarith : (0:ℝ) ≤ 1 - n * u - N - F))]

omit [Params] in
/-- The fixed point of one grinding trial with a fair share: landed pool pairs (`n` of them, each
picked with probability `u`), cached rejections (`N`), and fresh trials (`F`, landing with
probability `l`). The pool's share is at most `e` per pair of its excess over the fresh value. -/
theorem loop_arith (a S e u n N F l : ℝ≥0∞) (ha : a ≠ ⊤) (hS : S ≠ ⊤) (he : e ≠ ⊤) (hn : n ≠ ⊤)
    (hut : u ≠ ⊤) (hnNF : n * u + N + F ≤ 1) (hl : l ≤ 1) (hu : u ≤ e * (n * u + F * l)) :
    u * S + N * (a + e * (S - n * a)) + F * (l * a + (1 - l) * (a + e * (S - n * a))) ≤
      a + e * (S - n * a) := by
  set D := S - n * a with hD
  have hDt : D ≠ ⊤ := ne_top_of_le_ne_top hS tsub_le_self
  have hNt : N ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans (le_trans le_add_self le_self_add) hnNF)
  have hFt : F ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_trans le_add_self hnNF)
  have hlt : l ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hl
  have hSle : S ≤ n * a + D := le_add_tsub
  calc _ ≤ u * (n * a + D) + N * (a + e * D) + F * (l * a + (1 - l) * (a + e * D)) := by gcongr
    _ ≤ _ := ?_
  have hl1 : (1 - l).toReal = 1 - l.toReal := by
    rw [ENNReal.toReal_sub_of_le hl ENNReal.one_ne_top, ENNReal.toReal_one]
  have hl1t : (1 - l) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness)]
  rw [← ENNReal.toReal_le_toReal (by finiteness) ENNReal.one_ne_top] at hnNF
  rw [← ENNReal.toReal_le_toReal hut (by finiteness)] at hu
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, hl1,
    ENNReal.toReal_one] at hnNF hu ⊢
  exact loop_arith_real _ _ _ _ _ _ _ _ ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    hnNF hu

section Loop

variable {A : Type} (tg : Targeting HashInput HashOutput Coordinate)
  (initial : HiddenOutside.Cache HashInput HashOutput) (model : HiddenRows.Model HashInput HashOutput A Coordinate)
  (parameter : PublicParameter) (data : PublicData) (message : Message)

/-- The digest block of the signed message with a randomizer. -/
abbrev blk (randomness : Randomness) : HashInput :=
  Security.digestInput parameter data.root message randomness

/-- Weight of a selected pair with a known block: fresh pairs (relative to the reference state)
use `gf` (landed only), pool pairs use `gp`. -/
noncomputable def pairWeight (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (randomness : Randomness) (u0 : HashOutput) : ℝ≥0∞ :=
  if reference.cache (blk parameter data message randomness) = none then
    (if Landed parameter (blockIndex u0) then gf (viewOf u0) else 0)
  else gp randomness (viewOf u0)

/-- Weight of a signing outcome: the weight of the pair it signed. -/
noncomputable def outWeight (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate) : ℝ≥0∞ :=
  match out.1.1 with
  | some (some sig) => (out.2.cache (blk parameter data message sig.randomness)).elim 0
      (pairWeight parameter data message reference gf gp sig.randomness)
  | _ => 0

/-- Forecast weight of a cached landed pair of the reference state. -/
noncomputable def poolValue (reference : DebtState HashInput HashOutput Coordinate)
    (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞) (randomness : Randomness) : ℝ≥0∞ :=
  (reference.cache (blk parameter data message randomness)).elim 0 fun u0 =>
    if Landed parameter (blockIndex u0) then gp randomness (viewOf u0) else 0

/-- The state differs from the reference only by rejected trial blocks. -/
def Related (reference state : DebtState HashInput HashOutput Coordinate) : Prop :=
  ∀ ρ, state.cache (blk parameter data message ρ) = reference.cache (blk parameter data message ρ) ∨
    (reference.cache (blk parameter data message ρ) = none ∧ ∃ u,
      state.cache (blk parameter data message ρ) = some u ∧ ¬Landed parameter (blockIndex u))

/-- The state differs from the reference only by rejected trial blocks, except at one randomizer. -/
def RelatedOff (reference state : DebtState HashInput HashOutput Coordinate) (ρ : Randomness) : Prop :=
  ∀ ρ', ρ' ≠ ρ → (state.cache (blk parameter data message ρ') = reference.cache (blk parameter data message ρ') ∨
    (reference.cache (blk parameter data message ρ') = none ∧ ∃ u,
      state.cache (blk parameter data message ρ') = some u ∧ ¬Landed parameter (blockIndex u)))

/-- Randomizers whose block is cached. -/
noncomputable def cachedCount (state : DebtState HashInput HashOutput Coordinate) : ℕ :=
  (Finset.univ.filter fun ρ : Randomness => state.cache (blk parameter data message ρ) ≠ none).card

/-- Randomizers whose block is cached and lands: the pool of the message. -/
noncomputable def landedCount (state : DebtState HashInput HashOutput Coordinate) : ℕ :=
  (Finset.univ.filter fun ρ : Randomness => ∃ u0, state.cache (blk parameter data message ρ) = some u0 ∧
    Landed parameter (blockIndex u0)).card

omit [Params] in
theorem payload_randomness_injective (root : Digest) (message : Message) {ρ ρ' : Randomness}
    (h : messageDigestPayload root message ρ = messageDigestPayload root message ρ') : ρ = ρ' := by
  have hparts := List.append_inj h (by simp [bytesLE_length])
  have hfirst := List.append_inj hparts.1 (by simp [bytesLE_length])
  exact bytesLE_injective hfirst.1

omit [Params] in
theorem blk_ne_of_ne {ρ ρ' : Randomness} (h : ρ ≠ ρ') :
    blk parameter data message ρ ≠ blk parameter data message ρ' := fun heq =>
  h (payload_randomness_injective data.root message (tweakableInput_injective heq).2.2)

theorem related_store (reference state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state) (ρ : Randomness)
    (hs : state.cache (blk parameter data message ρ) = none) (u : HashOutput)
    (hu : ¬Landed parameter (blockIndex u)) :
    Related parameter data message reference (state.store (blk parameter data message ρ) u) := by
  have href : reference.cache (blk parameter data message ρ) = none := by
    rcases hrel ρ with h | ⟨h, _⟩
    · rw [← h]; exact hs
    · exact h
  intro ρ'
  by_cases hρ : ρ' = ρ
  · subst hρ
    exact Or.inr ⟨href, u, by simp [DebtState.store], hu⟩
  · rw [store_cache_ne state _ _ (blk_ne_of_ne parameter data message hρ) u]
    exact hrel ρ'

omit [Params] in
theorem cachedCount_store (state : DebtState HashInput HashOutput Coordinate) (ρ : Randomness) (u : HashOutput) :
    cachedCount parameter data message (state.store (blk parameter data message ρ) u) ≤
      cachedCount parameter data message state + 1 := by
  unfold cachedCount
  calc (Finset.univ.filter fun ρ' : Randomness =>
          (state.store (blk parameter data message ρ) u).cache (blk parameter data message ρ') ≠ none).card
      ≤ (insert ρ (Finset.univ.filter fun ρ' : Randomness =>
          state.cache (blk parameter data message ρ') ≠ none)).card := by
        refine Finset.card_le_card fun ρ' hρ' => ?_
        rw [Finset.mem_filter] at hρ'
        rw [Finset.mem_insert, Finset.mem_filter]
        by_cases h : ρ' = ρ
        · exact Or.inl h
        · refine Or.inr ⟨Finset.mem_univ _, ?_⟩
          rw [store_cache_ne state _ _ (blk_ne_of_ne parameter data message h) u] at hρ'
          exact hρ'.2
    _ ≤ _ := Finset.card_insert_le _ _

/-- The weight of a completed assembly is the weight of its own pair. -/
theorem outWeight_finish_le (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (ρ : Randomness) (budget : ℕ) (state : DebtState HashInput HashOutput Coordinate)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) budget state)) :
    outWeight parameter data message reference gf gp out ≤
      (if out.1.1.isSome then (out.2.cache (blk parameter data message ρ)).elim 0
        (pairWeight parameter data message reference gf gp ρ) else 0) := by
  unfold outWeight
  rcases hres : out.1.1 with _ | (_ | sig)
  · exact le_rfl
  · exact bot_le
  · have hmem := interp_result_mem tg initial model _ budget state out hout _ hres
    have hrand := finish_randomness parameter data message ρ _ hmem sig rfl
    simp only [Option.isSome_some, if_true]
    subst hrand
    exact le_rfl

/-- **One grinding trial.** -/
theorem trial_boundW
    (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (reference : DebtState HashInput HashOutput Coordinate) (ρ : Randomness)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (W : Option (Option Signature) → DebtState HashInput HashOutput Coordinate → ℝ≥0∞)
    (hWabort : ∀ s', W none s' = 0)
    (hWfin : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ → s'.cache (blk parameter data message ρ) = some u0 →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        W out.1.1 out.2 ≤ (if out.1.1.isSome then (out.2.cache (blk parameter data message ρ)).elim 0
          (pairWeight parameter data message reference gf gp ρ) else 0))
    (bound : ℝ≥0∞) (state : DebtState HashInput HashOutput Coordinate)
    (hrel : Related parameter data message reference state) (attempts : ℕ)
    (hih : ∀ s', Related parameter data message reference s' →
      cachedCount parameter data message s' ≤ cachedCount parameter data message state + 1 → ∀ b,
        ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts) b s'] *
          W out.1.1 out.2 ≤ bound)
    (budget : ℕ) :
    ∑' out, Pr[= out | interp tg initial model
        (liftM (CostSpec.query (.inl (.inr (.inl (blk parameter data message ρ))))) >>= fun first =>
          if Landed parameter (blockIndex first) then finishCostSource parameter data message ρ
          else signCostSourceLoop parameter data message attempts) budget state] *
        W out.1.1 out.2 ≤
      (state.cache (blk parameter data message ρ)).elim
        (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
          (if Landed parameter (blockIndex u0) then gf (viewOf u0) else bound))
        (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
          else bound) := by
  have hfinish : ∀ (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ → s'.cache (blk parameter data message ρ) = some u0 →
      ∑' out, Pr[= out | interp tg initial model (finishCostSource parameter data message ρ) b s'] *
          W out.1.1 out.2 ≤
        pairWeight parameter data message reference gf gp ρ u0 := by
    intro s' u0 b hrel' hs'
    refine le_trans (ENNReal.tsum_le_tsum fun out => ?_) (finish_bound₁ tg initial model parameter data message ρ
      (hparse ρ) s' u0 hs' _ b)
    by_cases hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s')
    · exact mul_le_mul_right (hWfin s' u0 b hrel' hs' out hout) _
    · rw [probOutput_eq_zero_of_not_mem_support hout, zero_mul, zero_mul]
  rw [interp_ordinary]
  split_ifs with h1
  · rw [ordinaryStep, hparse ρ]
    simp only
    rw [tsum_probOutput_bind_mul]
    simp only [tsum_probOutput_map_mul]
    cases hc : state.cache (blk parameter data message ρ) with
    | some u0 =>
        rw [readOutside_cached _ state u0 hc, tsum_probOutput_pure_mul]
        simp only [Option.elim]
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          have href : reference.cache (blk parameter data message ρ) = some u0 := by
            rcases hrel ρ with h | ⟨_, u, hu, hnl⟩
            · rw [← h]; exact hc
            · rw [hc] at hu; cases hu; exact absurd hl hnl
          refine le_trans (hfinish state u0 _ (fun ρ' _ => hrel ρ') hc) (le_of_eq ?_)
          simp [pairWeight, poolValue, href, hl]
        · rw [if_neg hl, if_neg hl]
          exact hih state hrel (Nat.le_succ _) _
    | none =>
        rw [readOutside_fresh _ state hc, tsum_probOutput_map_mul]
        simp only [Option.elim]
        have href : reference.cache (blk parameter data message ρ) = none := by
          rcases hrel ρ with h | ⟨h, _⟩
          · rw [← h]; exact hc
          · exact h
        refine ENNReal.tsum_le_tsum fun u0 => mul_le_mul_right ?_ _
        by_cases hl : Landed parameter (blockIndex u0)
        · rw [if_pos hl, if_pos hl]
          refine le_trans (hfinish _ u0 _ (fun ρ' hρ' => by
              rw [show (state.store (blk parameter data message ρ) u0).cache (blk parameter data message ρ') =
                state.cache (blk parameter data message ρ') from
                store_cache_ne state _ _ (blk_ne_of_ne parameter data message hρ') u0]
              exact hrel ρ')
            (by simp [DebtState.store])) (le_of_eq ?_)
          simp only [pairWeight, href, if_true, if_pos hl]
        · rw [if_neg hl, if_neg hl]
          exact hih _ (related_store parameter data message reference state hrel ρ hc u0 hl)
            (cachedCount_store parameter data message state ρ u0) _
  · rw [tsum_probOutput_pure_mul]
    rw [hWabort]
    exact zero_le

omit [Params] in
theorem card_randomness : Fintype.card Randomness = 2 ^ 128 := HiddenDebt.card_digest

theorem landed_mass (parameter : PublicParameter) :
    ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Landed parameter (blockIndex u0) then (1 : ℝ≥0∞) else 0) = ForestPrice.landing := by
  have h := fresh_view_mean parameter (fun _ => 1)
  rw [Domination.freshAvg_const _ Finset.univ_nonempty, mul_one] at h
  exact h

theorem unlanded_mass (parameter : PublicParameter) :
    ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Landed parameter (blockIndex u0) then (0 : ℝ≥0∞) else 1) = 1 - ForestPrice.landing := by
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

/-- **Fair share of the grinding signer.** With `n` cached landed pairs of the message in the
reference state, the signed pair's weight is at most the fresh average `a` plus `e` times the pool's
excess `S - n a`, whenever `2^-128 ≤ e (n 2^-128 + (2^128 - Cmax) 2^-128 landing)`. -/
theorem loop_boundW
    (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (W : Option (Option Signature) → DebtState HashInput HashOutput Coordinate → ℝ≥0∞)
    (hWabort : ∀ s', W none s' = 0)
    (hWnone : ∀ s' : DebtState HashInput HashOutput Coordinate, Related parameter data message reference s' →
      W (some none) s' = 0)
    (hWfin : ∀ (ρ : Randomness) (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput) (b : ℕ),
      RelatedOff parameter data message reference s' ρ → s'.cache (blk parameter data message ρ) = some u0 →
      ∀ out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s'),
        W out.1.1 out.2 ≤ (if out.1.1.isSome then (out.2.cache (blk parameter data message ρ)).elim 0
          (pairWeight parameter data message reference gf gp ρ) else 0))
    (B : ℝ≥0∞) (hB : B ≠ ⊤) (hgf : ∀ v, gf v ≤ B) (hgp : ∀ ρ v, gp ρ v ≤ B)
    (e : ℝ≥0∞) (he : e ≠ ⊤) (Cmax : ℕ) (hC : Cmax ≤ 2 ^ 128)
    (hu : ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ ≤
      e * ((landedCount parameter data message reference : ℝ≥0∞) * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ +
        (((2 ^ 128 - Cmax : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞)) * ForestPrice.landing)) :
    ∀ attempts budget state, Related parameter data message reference state →
      cachedCount parameter data message state + attempts ≤ Cmax →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts) budget state] *
          W out.1.1 out.2 ≤
        Domination.freshAvg Finset.univ gf + e * (∑ ρ, poolValue parameter data message reference gp ρ -
          (landedCount parameter data message reference : ℝ≥0∞) * Domination.freshAvg Finset.univ gf) := by
  set S := ∑ ρ, poolValue parameter data message reference gp ρ with hS
  set a := Domination.freshAvg Finset.univ gf with ha
  set n : ℝ≥0∞ := (landedCount parameter data message reference : ℝ≥0∞) with hn
  set Bnd := a + e * (S - n * a) with hBnd
  intro attempts
  induction attempts with
  | zero =>
      intro budget state hrel _
      change ∑' out, Pr[= out | interp tg initial model (pure none) budget state] *
        W out.1.1 out.2 ≤ _
      rw [interp_pure, tsum_probOutput_pure_mul]
      change W (some none) state ≤ _
      rw [hWnone state hrel]
      exact bot_le
  | succ attempts ih =>
      intro budget state hrel hcount
      rw [signCostSourceLoop_succ, interp_liftProb_bind, tsum_probOutput_bind_mul]
      have htrial := fun ρ => trial_boundW tg initial model parameter data message hparse reference ρ gf gp W
        hWabort (hWfin ρ) Bnd state hrel attempts (fun s' hs' hcs b => ih b s' hs' (by omega)) budget
      refine le_trans (ENNReal.tsum_le_tsum fun ρ => mul_le_mul_right (htrial ρ) _) ?_
      set u : ℝ≥0∞ := ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ with hudef
      have hpr : ∀ ρ, Pr[= ρ | ($ᵗ Randomness : ProbComp Randomness)] = u := by
        intro ρ
        rw [probOutput_uniformSample, card_randomness]
      simp only [hpr, ENNReal.tsum_mul_left]
      rw [tsum_fintype]
      set Fr := Finset.univ.filter fun ρ : Randomness => state.cache (blk parameter data message ρ) = none
      set NL := Finset.univ.filter fun ρ : Randomness => ∃ u0,
        state.cache (blk parameter data message ρ) = some u0 ∧ ¬Landed parameter (blockIndex u0)
      set LP := Finset.univ.filter fun ρ : Randomness => ∃ u0,
        reference.cache (blk parameter data message ρ) = some u0 ∧ Landed parameter (blockIndex u0)
      set fresh := ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
        (if Landed parameter (blockIndex u0) then gf (viewOf u0) else Bnd)
      have hpoint : ∀ ρ, (state.cache (blk parameter data message ρ)).elim fresh
          (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
            else Bnd) ≤
          poolValue parameter data message reference gp ρ + (if ρ ∈ NL then Bnd else 0) +
            (if ρ ∈ Fr then fresh else 0) := by
        intro ρ
        cases hc : state.cache (blk parameter data message ρ) with
        | none =>
            have hFr : ρ ∈ Fr := by simp [Fr, hc]
            simp only [Option.elim, if_pos hFr]
            exact le_add_self
        | some u0 =>
            have hFr : ρ ∉ Fr := by simp [Fr, hc]
            simp only [Option.elim, if_neg hFr, add_zero]
            split_ifs with hl hNL
            · exact le_self_add
            · exact le_self_add
            · exact le_add_self
            · rename_i hnot
              exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, u0, hc, hl⟩) hnot
      have hsum : ∑ ρ, (state.cache (blk parameter data message ρ)).elim fresh
          (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
            else Bnd) ≤ S + (NL.card : ℝ≥0∞) * Bnd + (Fr.card : ℝ≥0∞) * fresh := by
        refine le_trans (Finset.sum_le_sum fun ρ _ => hpoint ρ) (le_of_eq ?_)
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
          Finset.univ_inter, Finset.univ_inter, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      have hfreshEq : fresh = ForestPrice.landing * a + (1 - ForestPrice.landing) * Bnd := by
        have hsplit : fresh = (∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (if Landed parameter (blockIndex u0) then gf (viewOf u0) else 0)) +
            Bnd * ∑' u0, Pr[= u0 | ($ᵗ HashOutput : ProbComp HashOutput)] *
              (if Landed parameter (blockIndex u0) then 0 else 1) := by
          rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
          refine tsum_congr fun u0 => ?_
          split_ifs
          · simp
          · simp [mul_comm]
        rw [hsplit, unlanded_mass parameter, fresh_view_mean parameter gf]
        ring
      have hpool : ∀ ρ, poolValue parameter data message reference gp ρ ≤ B := by
        intro ρ
        unfold poolValue
        cases reference.cache (blk parameter data message ρ) with
        | none => exact bot_le
        | some u0 =>
            simp only [Option.elim]
            split_ifs
            · exact hgp _ _
            · exact bot_le
      have hSfin : S ≠ ⊤ := ENNReal.sum_ne_top.2 fun ρ _ => ne_top_of_le_ne_top hB (hpool ρ)
      have hafin : a ≠ ⊤ := Domination.freshAvg_ne_top Finset.univ_nonempty fun v => ne_top_of_le_ne_top hB (hgf v)
      have hcard : Fr.card + cachedCount parameter data message state = 2 ^ 128 := by
        rw [← card_randomness]
        exact Finset.card_filter_add_card_filter_not _
      have hdisj : LP.card + NL.card + Fr.card ≤ 2 ^ 128 := by
        rw [← card_randomness, ← Finset.card_univ]
        have h1 : Disjoint LP NL := by
          refine Finset.disjoint_left.2 fun ρ h1 h2 => ?_
          obtain ⟨_, u0, hr, hl⟩ := Finset.mem_filter.1 h1
          obtain ⟨_, u1, hs, hnl⟩ := Finset.mem_filter.1 h2
          rcases hrel ρ with h | ⟨h, _⟩
          · rw [h, hr] at hs; cases hs; exact hnl hl
          · rw [h] at hr; cases hr
        have h2 : Disjoint (LP ∪ NL) Fr := by
          refine Finset.disjoint_left.2 fun ρ h1 h2 => ?_
          have hnone := (Finset.mem_filter.1 h2).2
          rcases Finset.mem_union.1 h1 with h1 | h1
          · obtain ⟨_, u0, hr, _⟩ := Finset.mem_filter.1 h1
            rcases hrel ρ with h | ⟨h, _⟩
            · rw [h, hr] at hnone; cases hnone
            · rw [h] at hr; cases hr
          · obtain ⟨_, u1, hs, _⟩ := Finset.mem_filter.1 h1
            rw [hs] at hnone; cases hnone
        rw [← Finset.card_union_of_disjoint h1, ← Finset.card_union_of_disjoint h2]
        exact Finset.card_le_univ _
      have hland1 : ForestPrice.landing ≤ 1 := ForestPrice.landing_le_one
      have hu2 : u * ((2 ^ 128 : ℕ) : ℝ≥0∞) = 1 := ENNReal.inv_mul_cancel (by simp) (by simp)
      have hnLP : n = (LP.card : ℝ≥0∞) := rfl
      have hnNF : n * u + u * (NL.card : ℝ≥0∞) + u * (Fr.card : ℝ≥0∞) ≤ 1 := by
        rw [hnLP, mul_comm _ u, ← mul_add, ← mul_add, ← hu2]
        gcongr
        exact_mod_cast hdisj
      have hu' : u ≤ e * (n * u + u * (Fr.card : ℝ≥0∞) * ForestPrice.landing) := by
        refine le_trans hu ?_
        gcongr
        rw [ENNReal.div_eq_inv_mul]
        gcongr
        exact_mod_cast (by omega : 2 ^ 128 - Cmax ≤ Fr.card)
      have hnt : n ≠ ⊤ := ENNReal.natCast_ne_top _
      have hut : u ≠ ⊤ := by simp [hudef]
      calc u * ∑ ρ, (state.cache (blk parameter data message ρ)).elim fresh
            (fun u0 => if Landed parameter (blockIndex u0) then poolValue parameter data message reference gp ρ
              else Bnd)
          ≤ u * (S + (NL.card : ℝ≥0∞) * Bnd + (Fr.card : ℝ≥0∞) * fresh) := mul_le_mul_right hsum u
        _ = u * S + (u * (NL.card : ℝ≥0∞)) * Bnd + (u * (Fr.card : ℝ≥0∞)) *
              (ForestPrice.landing * a + (1 - ForestPrice.landing) * Bnd) := by
            rw [hfreshEq]
            ring
        _ ≤ Bnd := loop_arith a S e u n _ _ ForestPrice.landing hafin hSfin he hnt hut hnNF hland1 hu'

/-- **Fair share of the grinding signer, signed pair only.** -/
theorem loop_bound
    (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (B : ℝ≥0∞) (hB : B ≠ ⊤) (hgf : ∀ v, gf v ≤ B) (hgp : ∀ ρ v, gp ρ v ≤ B)
    (e : ℝ≥0∞) (he : e ≠ ⊤) (Cmax : ℕ) (hC : Cmax ≤ 2 ^ 128)
    (hu : ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ ≤
      e * ((landedCount parameter data message reference : ℝ≥0∞) * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ +
        (((2 ^ 128 - Cmax : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞)) * ForestPrice.landing)) :
    ∀ attempts budget state, Related parameter data message reference state →
      cachedCount parameter data message state + attempts ≤ Cmax →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts) budget state] *
          outWeight parameter data message reference gf gp out ≤
        Domination.freshAvg Finset.univ gf + e * (∑ ρ, poolValue parameter data message reference gp ρ -
          (landedCount parameter data message reference : ℝ≥0∞) * Domination.freshAvg Finset.univ gf) :=
  loop_boundW tg initial model parameter data message hparse reference gf gp
    (fun r s' => outWeight parameter data message reference gf gp ((r, [], [], []), s')) (fun _ => rfl) (fun _ _ => rfl)
    (fun ρ s' u0 b _ _ out hout => outWeight_finish_le tg initial model parameter data message reference gf gp ρ b s'
      out hout) B hB hgf hgp e he Cmax hC hu


/-! ### Fresh pairs completed by a signing call -/

/-- Weight of the reference-fresh landed pairs that a non-aborted signing call cached. -/
noncomputable def freshNewWeight (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate) : ℝ≥0∞ :=
  if out.1.1.isSome then ∑ ρ : Randomness,
    (if reference.cache (blk parameter data message ρ) = none then
      (out.2.cache (blk parameter data message ρ)).elim 0 fun u0 =>
        if Landed parameter (blockIndex u0) then gf (viewOf u0) else 0
    else 0)
  else 0

/-- A final assembly from a cached block keeps every message-digest entry. -/
theorem finish_keeps_msg (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none) (ρ : Randomness)
    (b : ℕ) (s' : DebtState HashInput HashOutput Coordinate) (u0 : HashOutput)
    (hc0 : s'.cache (blk parameter data message ρ) = some u0)
    (out : Run HashInput Coordinate (Option Signature) × DebtState HashInput HashOutput Coordinate)
    (hout : out ∈ support (interp tg initial model (finishCostSource parameter data message ρ) b s')) :
    ∀ x, IsMsgInput x → out.2.cache x = s'.cache x := by
  rw [finishCostSource_eq, interp_ordinary] at hout
  split_ifs at hout with h1
  · rw [ordinaryStep, hparse ρ] at hout
    simp only at hout
    rw [readOutside_cached _ s' u0 hc0, pure_bind, support_map] at hout
    obtain ⟨o, ho, rfl⟩ := hout
    exact interp_avoids_cache tg initial model IsMsgInput _
      (avoids_finishRest parameter data message ρ (truncateMessageDigest u0)) _ s' o ho
  · rw [support_pure, Set.mem_singleton_iff] at hout
    rw [hout]
    exact fun _ _ => rfl

/-- **Fair share of the grinding signer, with the fresh pairs it completes.** -/
theorem loop_bound_comb
    (hparse : ∀ ρ, model.parse (blk parameter data message ρ) = none)
    (reference : DebtState HashInput HashOutput Coordinate)
    (gf : Lifetime.KeptDigestView → ℝ≥0∞) (gp : Randomness → Lifetime.KeptDigestView → ℝ≥0∞)
    (B : ℝ≥0∞) (hB : B ≠ ⊤) (hgf : ∀ v, gf v ≤ B) (hgp : ∀ ρ v, gp ρ v ≤ B)
    (e : ℝ≥0∞) (he : e ≠ ⊤) (Cmax : ℕ) (hC : Cmax ≤ 2 ^ 128)
    (hu : ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ ≤
      e * ((landedCount parameter data message reference : ℝ≥0∞) * ((2 ^ 128 : ℕ) : ℝ≥0∞)⁻¹ +
        (((2 ^ 128 - Cmax : ℕ) : ℝ≥0∞) / ((2 ^ 128 : ℕ) : ℝ≥0∞)) * ForestPrice.landing)) :
    ∀ attempts budget state, Related parameter data message reference state →
      cachedCount parameter data message state + attempts ≤ Cmax →
      ∑' out, Pr[= out | interp tg initial model (signCostSourceLoop parameter data message attempts) budget state] *
          (freshNewWeight parameter data message reference gf out + outWeight parameter data message reference 0 gp out) ≤
        Domination.freshAvg Finset.univ gf + e * (∑ ρ, poolValue parameter data message reference gp ρ -
          (landedCount parameter data message reference : ℝ≥0∞) * Domination.freshAvg Finset.univ gf) := by
  refine loop_boundW tg initial model parameter data message hparse reference gf gp
    (fun r s' => freshNewWeight parameter data message reference gf ((r, [], [], []), s') +
      outWeight parameter data message reference 0 gp ((r, [], [], []), s'))
    (fun _ => by simp [freshNewWeight, outWeight]) ?_ ?_ B hB hgf hgp e he Cmax hC hu
  · intro s' hrel
    simp only [freshNewWeight, outWeight, Option.isSome_some, if_true, add_zero]
    refine Finset.sum_eq_zero fun ρ _ => ?_
    split_ifs with hn
    · rcases hrel ρ with h | ⟨_, u, hu', hnl⟩
      · rw [h, hn]; rfl
      · simp only [hu', Option.elim, if_neg hnl]
    · rfl
  · intro ρ s' u0 b hoff hs0 out hout
    have hkeep := finish_keeps_msg tg initial model parameter data message hparse ρ b s' u0 hs0 out hout
    have hk : ∀ ρ', out.2.cache (blk parameter data message ρ') = s'.cache (blk parameter data message ρ') :=
      fun ρ' => hkeep _ (msgInput_digestInput parameter data.root message ρ')
    show freshNewWeight parameter data message reference gf ((out.1.1, [], [], []), out.2) +
      outWeight parameter data message reference 0 gp ((out.1.1, [], [], []), out.2) ≤ _
    by_cases hsome : out.1.1.isSome
    · rw [if_pos hsome, hk ρ, hs0]
      simp only [Option.elim]
      have hfresh : freshNewWeight parameter data message reference gf ((out.1.1, [], [], []), out.2) =
          if reference.cache (blk parameter data message ρ) = none then
            (if Landed parameter (blockIndex u0) then gf (viewOf u0) else 0) else 0 := by
        simp only [freshNewWeight, if_pos hsome]
        rw [Finset.sum_eq_single ρ]
        · simp only [hk ρ, hs0, Option.elim]
        · intro ρ' _ hne
          split_ifs with hn
          · rcases hoff ρ' hne with h | ⟨_, u, hu', hnl⟩
            · rw [hk ρ', h, hn]; rfl
            · simp only [hk ρ', hu', Option.elim, if_neg hnl]
          · rfl
        · intro h; exact absurd (Finset.mem_univ ρ) h
      rw [hfresh]
      have hout' : outWeight parameter data message reference 0 gp ((out.1.1, [], [], []), out.2) ≤
          if reference.cache (blk parameter data message ρ) = none then 0 else gp ρ (viewOf u0) := by
        have := outWeight_finish_le tg initial model parameter data message reference 0 gp ρ b s' out hout
        simp only [if_pos hsome, hk ρ, hs0, Option.elim, pairWeight] at this
        refine le_trans (le_of_eq ?_) (le_trans this (le_of_eq ?_))
        · rfl
        · split_ifs <;> rfl
      refine le_trans (add_le_add_right hout' _) (le_of_eq ?_)
      simp only [pairWeight]
      split_ifs <;> simp
    · rw [if_neg hsome]
      simp only [freshNewWeight, if_neg hsome, zero_add]
      unfold outWeight
      cases hr : out.1.1 with
      | none => rfl
      | some r => simp [hr] at hsome

end Loop

end LeanForest.Security.GraphView
